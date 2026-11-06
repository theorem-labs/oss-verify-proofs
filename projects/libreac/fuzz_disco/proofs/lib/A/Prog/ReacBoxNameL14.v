(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths, module names and numbers changed; 361 of its 413 lines of code are new or changed and 1226 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ReacBoxNameSeg1.v; 1462 of its 1513 lines of code are new or changed and 362 lines of the source are left out. *)
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
YC1g YC1h YC81 YC4b YC45 YC85 YCkd YC1i ACbf ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacBoxNameLoops.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac rl_pull HS H0 Hout :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ex _ _ =>
    lazymatch type of H0 with
    | ew _ ?q = ?v => assert (Hout : ew Ex q = v) by (cbn [ew ewset Nat.eqb]; exact H0)
    end
  end.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Lemma rl_shadow_apart : forall D n x, in_app D n -> 0 <= x -> x < 2 ^ 47 -> ~ (D <= SHADOW_OFF + x / 8 < D + n).
Proof.
intros D n x [H4096 Hc] Hx0 Hx Hbad.
assert (Hd : 0 <= x / 8 < 17592186044416)
  by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia | change (8 * 17592186044416) with (2 ^ 47); lia]]).
unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. ceil. destruct Hc as [HL | [HH1 HH2]]; lia.
Qed.
Lemma rl_not_shadow : forall D n a, in_app D n -> D <= a < D + n -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 17592186044416).
Proof.
intros D n a [H4096 Hc] Ha Hbad. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. ceil.
destruct Hc as [HL | [HH1 HH2]]; lia.
Qed.
Lemma rl_ra_kept : forall (H : word -> bool) (m m2 : word -> option byte) a len,
  (forall x, a <= x < a + len -> aview SEGS H m2 (SHADOW_OFF + x / 8) = aview SEGS H m (SHADOW_OFF + x / 8)) ->
  range_addressable (aview SEGS H m) SHADOW_OFF a len ->
  range_addressable (aview SEGS H m2) SHADOW_OFF a len.
Proof.
intros H m m2 a len He Hra x Hx. destruct (Hra x Hx) as (s & Hs & Hok).
exists s. split; [|exact Hok]. unfold shadow_of_addr in *. rewrite (He x Hx). exact Hs.
Qed.
Lemma rl_garr8_kept : forall (H : word -> bool) (m m' : word -> option byte) p L,
  (forall a, p <= a < p + Z.of_nat (length L) -> aview SEGS H m' a = aview SEGS H m a) ->
  garr8 SEGS (mrestrict H m) p L -> garr8 SEGS (mrestrict H m') p L.
Proof.
intros H m m' p L He Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_kept SEGS H H m m'); [|exact Hv].
intros q Hq. cbn [Z.of_nat] in Hq. apply He. lia.
Qed.
Definition EL (regs : bvmap 5 word) (x c : Z) : env := Eimg (Ereg regs [w64 x; w64 c]).
Lemma EL_img : forall regs x c, img_env VAL A_LIM (EL regs x c).
Proof. intros. unfold EL. apply Eimg_env. Qed.
Lemma EL_reg : forall regs x c n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew (EL regs x c) n = getr regs r.
Proof.
intros regs x c n r Hn Hr. unfold EL. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hr.
Qed.
Lemma EL_32 : forall regs x c, ew (EL regs x c) 32 = w64 x.
Proof. intros. unfold EL. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma EL_33 : forall regs x c, ew (EL regs x c) 33 = w64 c.
Proof. intros. unfold EL. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1). Qed.
Lemma EL_agree : forall regs x c, env_agree 32 (Ereg regs [w64 x; w64 c]) (EL regs x c).
Proof.
intros. split; [intros q Hq; unfold EL; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
Qed.
Lemma rl_afact : forall E q v lo hi, ew E q = w64 v -> 0 <= v < 2 ^ 64 -> lo <= v -> v <= hi -> afact_ok E q (mkAF lo hi 0).
Proof.
intros E q v lo hi He Hv Hlo Hhi. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite He. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r.
split; [lia|]. split; [reflexivity | lia].
Qed.
Lemma rl_keep_of : forall (regs regs2 : bvmap 5 word) (l : list (bv 5)) (cl : list Z),
  (forall r : bv 5, In r l -> getr regs2 r = getr regs r) ->
  getr regs2 (Z_to_bv 5 0) = getr regs (Z_to_bv 5 0) ->
  (forall z, 0 < z < 32 -> ~ In z cl -> In (Z_to_bv 5 z) l) ->
  rbn_keep_regs regs regs2 cl.
Proof.
intros regs regs2 l cl Hk H0 Hin z Hz Hnc.
destruct (Z.eq_dec z 0) as [-> | Hz0]; [exact H0 | apply Hk; apply Hin; [lia | exact Hnc]].
Qed.
Lemma rl_keep_trans : forall (regs r1 r2 : bvmap 5 word) cl,
  rbn_keep_regs regs r1 cl -> rbn_keep_regs r1 r2 cl -> rbn_keep_regs regs r2 cl.
Proof. intros regs r1 r2 cl H1 H2 z Hz Hn. rewrite (H2 z Hz Hn). exact (H1 z Hz Hn). Qed.
Definition rl_srcR : YP09.region := YP09.mkRegion (Some 13%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition rl_dstR : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 1 [].
Definition rl_Bx : sv := SOff 22 0.
Definition rl_SH : list shent := [mkSHE 32 0 1].
Definition KEPT1 : list (bv 5) := [1;2;3;4;6;7;8;9;12;14;18;19;20;21;22;23;25;26;27;28;29;31]%bv.
Definition KEPT4 : list (bv 5) := [1;2;3;4;6;7;8;9;14;18;19;20;21;22;23;24;25;26;27;28;29;30;31]%bv.
Definition rl_cmn : list (nat * afact) :=
  [(22%nat, mkAF SB SB 0); (15%nat, mkAF 1 255 0); (33%nat, mkAF 0 255 0);
   (10%nat, mkAF 1 (2 ^ 47 - 1) 0); (13%nat, mkAF 1 (2 ^ 47 - 1) 0)].
Definition l1_ff : facts := mkFacts
  ((24%nat, mkAF 0 22 0) :: (14%nat, mkAF 23 23 0) :: (30%nat, mkAF 0 1 0) ::
   (32%nat, mkAF 4096 (2 ^ 47 - 1) 0) :: rl_cmn) [] [(SAlu ALU_ADD (SOff 27 0) (SOff 24 0), SOff 32 0)].
Definition l1_ssf : sstate := mkSS (AF_reac_box_name + RBN_L1) sr_atoms [rl_dstR; rl_srcR] None l1_ff.
Definition l1_fo : facts := mkFacts
  ((24%nat, mkAF 23 23 0) :: (14%nat, mkAF 23 23 0) :: (30%nat, mkAF 0 1 0) :: rl_cmn) [] [].
Definition l1_sso : sstate := mkSS (AF_reac_box_name + RBN_L1) sr_atoms [rl_srcR] None l1_fo.
Definition l4_ff : facts := mkFacts
  ((11%nat, mkAF 0 46 0) :: (14%nat, mkAF 47 47 0) :: (12%nat, mkAF 0 1 0) ::
   (32%nat, mkAF 4096 (2 ^ 47 - 1) 0) :: rl_cmn) [] [(SAlu ALU_ADD (SOff 20 0) (SOff 11 0), SOff 32 0)].
Definition l4_ssf : sstate := mkSS (AF_reac_box_name + RBN_L4) sr_atoms [rl_dstR; rl_srcR] None l4_ff.
Definition l4_fo : facts := mkFacts
  ((11%nat, mkAF 47 47 0) :: (14%nat, mkAF 47 47 0) :: (12%nat, mkAF 0 1 0) :: rl_cmn) [] [].
Definition l4_sso : sstate := mkSS (AF_reac_box_name + RBN_L4) sr_atoms [rl_srcR] None l4_fo.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Lemma l1_entry_f : forall (fq : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (D n ov c c2 Q : Z),
  0 <= n <= 22 -> (ov = 0 \/ ov = 1) -> 0 < c < 256 -> 0 <= c2 < 256 ->
  4096 <= D -> D + n <= 2 ^ 47 - 1 -> 0 <= Q -> Q + 2 <= 2 ^ 47 ->
  (Q + 2 <= D + n \/ D + n + 1 <= Q + 1) ->
  getr regs 24 = w64 n -> getr regs 30 = w64 ov -> getr regs 15 = w64 c ->
  getr regs 13 = w64 (Q + 1) -> getr regs 10 = w64 (Q + 1) -> getr regs 14 = w64 23 ->
  getr regs 27 = w64 D -> getr regs 22 = w64 SHADOW_OFF ->
  apresent (w_H W) mem (D + n) ->
  val_mem SEGS (mrestrict (w_H W) mem) (Q + 1) 1 c2 ->
  st_ok_pi SEGS VAL (EL regs (D + n) c2) l1_ssf
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L1))) mem (seg_rom SEGS))).
Proof.
intros fq W regs mem D n ov c c2 Q Hn Hov Hc Hc2 HD4 HD47 HQ0 HQ47 Hdisj
  H24 H30 H15 H13 H10 H14 H27 H22 Hap Hmem.
assert (E32 : ew (EL regs (D + n) c2) 32 = w64 (D + n)) by apply EL_32.
assert (E33 : ew (EL regs (D + n) c2) 33 = w64 c2) by apply EL_33.
assert (E24 : ew (EL regs (D + n) c2) 24 = w64 n)
  by (rewrite (EL_reg regs _ _ 24%nat 24%bv) by (first [lia | vm_compute; reflexivity]); exact H24).
assert (E30 : ew (EL regs (D + n) c2) 30 = w64 ov)
  by (rewrite (EL_reg regs _ _ 30%nat 30%bv) by (first [lia | vm_compute; reflexivity]); exact H30).
assert (E15 : ew (EL regs (D + n) c2) 15 = w64 c)
  by (rewrite (EL_reg regs _ _ 15%nat 15%bv) by (first [lia | vm_compute; reflexivity]); exact H15).
assert (E13 : ew (EL regs (D + n) c2) 13 = w64 (Q + 1))
  by (rewrite (EL_reg regs _ _ 13%nat 13%bv) by (first [lia | vm_compute; reflexivity]); exact H13).
assert (E10 : ew (EL regs (D + n) c2) 10 = w64 (Q + 1))
  by (rewrite (EL_reg regs _ _ 10%nat 10%bv) by (first [lia | vm_compute; reflexivity]); exact H10).
assert (E14 : ew (EL regs (D + n) c2) 14 = w64 23)
  by (rewrite (EL_reg regs _ _ 14%nat 14%bv) by (first [lia | vm_compute; reflexivity]); exact H14).
assert (E27 : ew (EL regs (D + n) c2) 27 = w64 D)
  by (rewrite (EL_reg regs _ _ 27%nat 27%bv) by (first [lia | vm_compute; reflexivity]); exact H27).
assert (E22 : ew (EL regs (D + n) c2) 22 = w64 SHADOW_OFF)
  by (rewrite (EL_reg regs _ _ 22%nat 22%bv) by (first [lia | vm_compute; reflexivity]); exact H22).
assert (U32 : bv_unsigned (ew (EL regs (D + n) c2) 32) = D + n)
  by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
assert (U13 : bv_unsigned (ew (EL regs (D + n) c2) 13) = Q + 1)
  by (rewrite E13; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold l1_ssf, l1_ff, rl_cmn. apply pa_entry_st_ok_full.
- unfold EL. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold rl_dstR, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U32. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. assert (o = 0) by lia. subst o. rewrite Z.add_0_r.
    apply (apresent_writable SEGS). exact Hap.
  + unfold rl_srcR, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U13. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS _ _ (Q + 1) 0 1 (SOff 33 0) c2);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    change (N.to_nat 1) with 1%nat. rewrite Z.add_0_r. exact Hmem.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, rl_dstR, rl_srcR.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U32, U13. split; [|split; exact I]. split; [lia|exact I].
- split; [|split; [exact I|]].
  + cbn [f_atoms atoms_ok].
    split; [apply (rl_afact _ _ n); [exact E24 | lia | lia | lia]|].
    split; [apply (rl_afact _ _ 23); [exact E14 | lia | lia | lia]|].
    split; [apply (rl_afact _ _ ov); [exact E30 | lia | lia | lia]|].
    split; [apply (rl_afact _ _ (D + n)); [exact E32 | lia | lia | lia]|].
    split; [apply (rl_afact _ _ SHADOW_OFF); [exact E22 | unfold SHADOW_OFF; lia | unfold SB, SHADOW_OFF; lia | unfold SB, SHADOW_OFF; lia]|].
    split; [apply (rl_afact _ _ c); [exact E15 | lia | lia | lia]|].
    split; [apply (rl_afact _ _ c2); [exact E33 | lia | lia | lia]|].
    split; [apply (rl_afact _ _ (Q + 1)); [exact E10 | lia | lia | lia]|].
    split; [apply (rl_afact _ _ (Q + 1)); [exact E13 | lia | lia | lia]|]. exact I.
  + cbn [f_alias alias_ok]. split; [|exact I].
    apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
    rewrite (U_atom _ 27 D E27) by lia. rewrite (U_atom _ 24 n E24) by lia.
    rewrite (U_atom _ 32 (D + n) E32) by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma l1_entry_o : forall (fq : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (D ov c c2 Q : Z),
  (ov = 0 \/ ov = 1) -> 0 < c < 256 -> 0 <= c2 < 256 ->
  0 <= Q -> Q + 2 <= 2 ^ 47 ->
  getr regs 24 = w64 23 -> getr regs 30 = w64 ov -> getr regs 15 = w64 c ->
  getr regs 13 = w64 (Q + 1) -> getr regs 10 = w64 (Q + 1) -> getr regs 14 = w64 23 ->
  getr regs 22 = w64 SHADOW_OFF ->
  val_mem SEGS (mrestrict (w_H W) mem) (Q + 1) 1 c2 ->
  st_ok_pi SEGS VAL (EL regs (D + 23) c2) l1_sso
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L1))) mem (seg_rom SEGS))).
Proof.
intros fq W regs mem D ov c c2 Q Hov Hc Hc2 HQ0 HQ47 H24 H30 H15 H13 H10 H14 H22 Hmem.
assert (E33 : ew (EL regs (D + 23) c2) 33 = w64 c2) by apply EL_33.
assert (E24 : ew (EL regs (D + 23) c2) 24 = w64 23)
  by (rewrite (EL_reg regs _ _ 24%nat 24%bv) by (first [lia | vm_compute; reflexivity]); exact H24).
assert (E30 : ew (EL regs (D + 23) c2) 30 = w64 ov)
  by (rewrite (EL_reg regs _ _ 30%nat 30%bv) by (first [lia | vm_compute; reflexivity]); exact H30).
assert (E15 : ew (EL regs (D + 23) c2) 15 = w64 c)
  by (rewrite (EL_reg regs _ _ 15%nat 15%bv) by (first [lia | vm_compute; reflexivity]); exact H15).
assert (E13 : ew (EL regs (D + 23) c2) 13 = w64 (Q + 1))
  by (rewrite (EL_reg regs _ _ 13%nat 13%bv) by (first [lia | vm_compute; reflexivity]); exact H13).
assert (E10 : ew (EL regs (D + 23) c2) 10 = w64 (Q + 1))
  by (rewrite (EL_reg regs _ _ 10%nat 10%bv) by (first [lia | vm_compute; reflexivity]); exact H10).
assert (E14 : ew (EL regs (D + 23) c2) 14 = w64 23)
  by (rewrite (EL_reg regs _ _ 14%nat 14%bv) by (first [lia | vm_compute; reflexivity]); exact H14).
assert (E22 : ew (EL regs (D + 23) c2) 22 = w64 SHADOW_OFF)
  by (rewrite (EL_reg regs _ _ 22%nat 22%bv) by (first [lia | vm_compute; reflexivity]); exact H22).
assert (U13 : bv_unsigned (ew (EL regs (D + 23) c2) 13) = Q + 1)
  by (rewrite E13; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold l1_sso, l1_fo, rl_cmn. apply pa_entry_st_ok_full.
- unfold EL. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  unfold rl_srcR, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U13. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ (Q + 1) 0 1 (SOff 33 0) c2);
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
  change (N.to_nat 1) with 1%nat. rewrite Z.add_0_r. exact Hmem.
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- split; [|split; exact I].
  cbn [f_atoms atoms_ok].
  split; [apply (rl_afact _ _ 23); [exact E24 | lia | lia | lia]|].
  split; [apply (rl_afact _ _ 23); [exact E14 | lia | lia | lia]|].
  split; [apply (rl_afact _ _ ov); [exact E30 | lia | lia | lia]|].
  split; [apply (rl_afact _ _ SHADOW_OFF); [exact E22 | unfold SHADOW_OFF; lia | unfold SB, SHADOW_OFF; lia | unfold SB, SHADOW_OFF; lia]|].
  split; [apply (rl_afact _ _ c); [exact E15 | lia | lia | lia]|].
  split; [apply (rl_afact _ _ c2); [exact E33 | lia | lia | lia]|].
  split; [apply (rl_afact _ _ (Q + 1)); [exact E10 | lia | lia | lia]|].
  split; [apply (rl_afact _ _ (Q + 1)); [exact E13 | lia | lia | lia]|]. exact I.
Qed.
Lemma rbn_l1_core : forall (m : nat) (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc
  (W : world SEGS) (memc : word -> option byte) (k : Z) (regs : bvmap 5 word) (D n0 : Z)
  (Q : Z) (t : list Z) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model)
  (n ov : Z) (wr : list Z) (nF ovF : Z) (wrF : list Z),
  (length t <= m)%nat ->
  nF = Z.min (n + Z.of_nat (length t)) 23 ->
  ovF = (if n + Z.of_nat (length t) <=? 23 then ov else 1) ->
  wrF = wr ++ firstn (Z.to_nat (23 - n)) t ->
  t <> [] -> Forall (fun x => 0 < x < 256) t ->
  garr8 SEGS (mrestrict (w_H W) memc) Q (t ++ [0]) ->
  0 <= Q -> Q + Z.of_nat (length t) + 1 <= 2 ^ 47 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF Q (Z.of_nat (length t) + 1) ->
  rbn_lbuf B STK sp0 FP ly S own lyc Sc W memc D 24 ->
  (Q + Z.of_nat (length t) + 1 <= D \/ D + 24 <= Q) ->
  0 <= n0 -> n0 <= n -> n <= 23 -> (ov = 0 \/ ov = 1) ->
  Z.of_nat (length wr) = n - n0 ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
  mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) mem') ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (D + n0 <= a < D + n) -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a) ->
  garr8 SEGS (mrestrict (w_H W) mem') (D + n0) wr ->
  getr regs' 24 = w64 n -> getr regs' 30 = w64 ov -> getr regs' 15 = w64 (hd 0 t) ->
  getr regs' 13 = w64 (Q + 1) -> getr regs' 10 = w64 (Q + 1) -> getr regs' 14 = w64 23 ->
  getr regs' 27 = w64 D -> getr regs' 22 = w64 SHADOW_OFF ->
  rbn_keep_regs regs regs' [5; 10; 11; 13; 15; 16; 17; 24; 30] ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs' (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L1))) mem' (seg_rom SEGS)) md')
    (rbn_lpost B fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L1X
       [5; 10; 11; 13; 15; 16; 17; 24; 30] D n0 wrF [(24, nF); (30, ovF)]).
Proof.
intros m. induction m as [|m IH];
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs D n0 Q t regs' mem' md' n ov wr nF ovF wrF
  Hm HnF HovF HwrF Ht0 Htb Hga HQ0 HQ47 Hra Hbuf Hdis Hn00 Hn0n Hn23 Hov Hwrl HJ HMG HF1 Hgw
  H24 H30 H15 H13 H10 H14 H27 H22 HKP.
{ exfalso. destruct t as [|c t']; [exact (Ht0 eq_refl) | cbn [length] in Hm; lia]. }
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof (@paj_run fq _ _ _ _ _ B LAWS) as RUN.
pose proof (@paj_run_to fq _ _ _ _ _ B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (L := disco_listing) (PI := PI)) as BR.
destruct t as [|c t']; [exact (False_ind _ (Ht0 eq_refl))|].
pose proof Hbuf as (HD0 & HD63 & HDapp & HDra & HDbyte).
assert (H4096 : 4096 <= D) by (destruct HDapp as [HH _]; exact HH).
ceil.
assert (HD47 : D + 24 <= 2 ^ 47 - 1)
  by (destruct HDapp as [_ [HL | [HH1 HH2]]]; unfold kLowShadowBeg, kHighMemBeg in *; lia).
assert (HLn : Z.of_nat (length (c :: t')) = Z.of_nat (length t') + 1) by (cbn [length]; lia).
assert (Hcr : 0 < c < 256) by (inversion Htb; assumption).
assert (Htb' : Forall (fun x => 0 < x < 256) t') by (inversion Htb; assumption).
assert (Hidx : (1 < length ((c :: t') ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
destruct (Hga 1%nat Hidx) as [Hc2m0 Hc2r].
change (Z.of_nat 1) with 1 in Hc2m0.
set (c2 := nth 1 ((c :: t') ++ [0]) 0) in *.
assert (Hc2z : c2 = 0 -> t' = []).
{ unfold c2. destruct t' as [|x t'']; [reflexivity|]. cbn [app nth]. intros Hx. exfalso. inversion Htb'. lia. }
assert (Hc2nil : t' = [] -> c2 = 0) by (intros Hx; unfold c2; rewrite Hx; reflexivity).
assert (Hc2nz : t' <> [] -> c2 = hd 0 t').
{ unfold c2. destruct t' as [|x t'']; [intros HX; exfalso; exact (HX eq_refl)|]. cbn [app nth hd]. reflexivity. }
assert (HSEP : forall a, Q <= a <= Q + Z.of_nat (length t') + 1 -> ~ (D <= a < D + 24))
  by (intros a Ha; rewrite HLn in Hdis; lia).
assert (HQ2 : Q + 2 <= 2 ^ 47) by (rewrite HLn in HQ47; lia).
assert (Hc2m : val_mem SEGS (mrestrict (w_H W) mem') (Q + 1) 1 c2).
{ apply (val_mem_kept SEGS (w_H W) (w_H W) memc mem' (Q + 1) 1 c2); [|exact Hc2m0].
  intros j Hj. cbn [Z.of_nat] in Hj. assert (Hj0 : j = 0) by lia. subst j. rewrite Z.add_0_r.
  apply HF1; [lia|]. intros Hbad. apply (HSEP (Q + 1) ltac:(lia)). lia. }
assert (HRAQ : range_addressable (aview SEGS (w_H W) mem') SHADOW_OFF (Q + 1) 1).
{ apply (rl_ra_kept (w_H W) memc mem' (Q + 1) 1).
  - intros x Hx. apply HF1.
    + unfold SHADOW_OFF. assert (0 <= x / 8 < 2 ^ 47) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). lia.
    + intros Hbad. apply (rl_shadow_apart D 24 x HDapp ltac:(lia) ltac:(rewrite HLn in HQ47; lia)). lia.
  - apply (range_addressable_sub (aview SEGS (w_H W) memc) SHADOW_OFF Q (Z.of_nat (length (c :: t')) + 1));
    [exact Hra | lia | rewrite HLn; lia]. }
cbn [hd] in H15.
destruct (Z_le_gt_dec n 22) as [Hn22 | Hngt].
{
  assert (HDn : D <= D + n < D + 24) by lia.
  destruct (HDbyte (D + n) ltac:(lia)) as [Hawr Hap0].
  assert (Hap : apresent (w_H W) mem' (D + n))
    by (apply (apresent_grows (w_H W) memc mem'); [exact HMG | exact Hap0]).
  set (E := EL regs' (D + n) c2).
  assert (HEI : img_env VAL A_LIM E) by apply EL_img.
  assert (E32 : ew E 32 = w64 (D + n)) by apply EL_32.
  assert (E33 : ew E 33 = w64 c2) by apply EL_33.
  assert (E24 : ew E 24 = w64 n)
    by (unfold E; rewrite (EL_reg regs' _ _ 24%nat 24%bv) by (first [lia | vm_compute; reflexivity]); exact H24).
  assert (E30 : ew E 30 = w64 ov)
    by (unfold E; rewrite (EL_reg regs' _ _ 30%nat 30%bv) by (first [lia | vm_compute; reflexivity]); exact H30).
  assert (E15 : ew E 15 = w64 c)
    by (unfold E; rewrite (EL_reg regs' _ _ 15%nat 15%bv) by (first [lia | vm_compute; reflexivity]); exact H15).
  assert (E13 : ew E 13 = w64 (Q + 1))
    by (unfold E; rewrite (EL_reg regs' _ _ 13%nat 13%bv) by (first [lia | vm_compute; reflexivity]); exact H13).
  assert (E10 : ew E 10 = w64 (Q + 1))
    by (unfold E; rewrite (EL_reg regs' _ _ 10%nat 10%bv) by (first [lia | vm_compute; reflexivity]); exact H10).
  assert (E14 : ew E 14 = w64 23)
    by (unfold E; rewrite (EL_reg regs' _ _ 14%nat 14%bv) by (first [lia | vm_compute; reflexivity]); exact H14).
  assert (E27 : ew E 27 = w64 D)
    by (unfold E; rewrite (EL_reg regs' _ _ 27%nat 27%bv) by (first [lia | vm_compute; reflexivity]); exact H27).
  assert (E22 : ew E 22 = w64 SHADOW_OFF)
    by (unfold E; rewrite (EL_reg regs' _ _ 22%nat 22%bv) by (first [lia | vm_compute; reflexivity]); exact H22).
  assert (U32 : bv_unsigned (ew E 32) = D + n) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
  assert (U13 : bv_unsigned (ew E 13) = Q + 1) by (rewrite E13; unfold w64; apply unsigned_lit_small; lia).
  assert (HS : st_ok_pi SEGS VAL E l1_ssf
    (restrict (w_H W) (mkst (fx := fq) regs' (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L1))) mem' (seg_rom SEGS)))).
  { unfold E. apply (l1_entry_f fq W regs' mem' D n ov c c2 Q); try assumption; try lia. }
  pose proof HS as HSe.
  assert (SHOK : sh_ok SEGS rl_Bx rl_SH E (mrestrict (w_H W) mem')).
  { unfold sh_ok, rl_SH. apply Forall_cons; [|apply Forall_nil].
    unfold shent_ok, rl_Bx. cbn [she_m she_lo she_hi].
    rewrite (U_atom E 22 SHADOW_OFF E22) by (unfold SHADOW_OFF; lia).
    rewrite (U_atom E 32 (D + n) E32) by lia.
    split.
    - rewrite Z.add_0_r. rewrite <- (aview_rd_of SEGS). change (1 - 0) with 1.
      apply (rl_ra_kept (w_H W) memc mem' (D + n) 1).
      + intros x Hx. apply HF1.
        * unfold SHADOW_OFF. assert (0 <= x / 8 < 2 ^ 47) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). lia.
        * intros Hbad. apply (rl_shadow_apart D 24 x HDapp ltac:(lia) ltac:(lia)). lia.
      + apply (range_addressable_sub (aview SEGS (w_H W) memc) SHADOW_OFF D 24); [exact HDra | lia | lia].
    - unfold app_apart. cbn [she_m she_lo she_hi].
      intros a Ha.
      rewrite (U_atom E 32 (D + n) E32) in Ha by lia.
      rewrite (U_atom E 22 SHADOW_OFF E22) by (unfold SHADOW_OFF; lia).
      apply (rl_not_shadow D 24 a HDapp). lia. }
  paj_run_tok RUN HS HJ SHOK Bspan.
  { unfold rl_Bx. rewrite (U_atom E 22 SHADOW_OFF E22) by (unfold SHADOW_OFF; lia).
    rewrite (U_atom E 10 (Q + 1) E10) by lia.
    rewrite <- (aview_rd_of SEGS). exact HRAQ. }
  { eapply (awr_ok_cons_gen E rl_dstR _ _ _ _ _ _ _ _ 32%nat (D + n)); [reflexivity | exact U32 | | ].
    - intros a Ha. cbn [YP09.r_wlo YP09.r_whi rl_dstR] in Ha. exact (proj1 (HDbyte a ltac:(lia))).
    - apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi rl_srcR]; lia | apply awr_ok_nil]. }
  rename HF into HFa. rename HFr into HFra. rename HG into HGa.
  assert (U32a : bv_unsigned (ew _ 32) = D + n)
    by (rl_pull HS E32 Fa32; rewrite Fa32; unfold w64; apply unsigned_lit_small; lia).
  assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (D + n <= a < D + n + 1) ->
            aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem' a).
  { intros a Ha Hn. apply (aview_kept_out _ _ (w_H W) _ _ HFra a Ha).
    intros (r & Hin & Hr). cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [subst r|]); try destruct Hin;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val rl_dstR rl_srcR] in Hr; rewrite ?U32a in Hr; lia. }
  psrr_branch_tok RUN BR HS SHOK Bspan.
  {
    rl_pull HS E33 F33. rl_pull HS E32 F32. rl_pull HS E24 F24. rl_pull HS E30 F30.
    rl_pull HS E13 F13. rl_pull HS E10 F10. rl_pull HS E14 F14. rl_pull HS E27 F27. rl_pull HS E22 F22.
    match goal with H : branch_taken _ _ _ = _ |- _ => rename H into HB end.
    rewrite branch_ne_U in HB. rewrite (U_atom _ 33 c2 F33) in HB by lia. rewrite U_lit in HB by lia.
    apply negb_true_iff, Z.eqb_neq in HB.
    assert (Ht' : t' <> []) by (intros Hx; apply HB; apply Hc2nil; exact Hx).
    assert (U32' : bv_unsigned (ew _ 32) = D + n) by (rewrite F32; unfold w64; apply unsigned_lit_small; lia).
    paj_run_to_tok RUNTO HS HJ SHOK Bspan (AF_reac_box_name + RBN_L1).
    { eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32%nat (D + n)); [reflexivity | exact U32' | | ].
      - intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. exact (proj1 (HDbyte a ltac:(lia))).
      - apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil]. }
    rename HF into HFb. rename HFr into HFrb. rename HG into HGb.
    assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (D + n <= a < D + n + 1) ->
              aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) (ms_mem ms) a).
    { intros a Ha Hn. apply (aview_kept_out _ _ (w_H W) _ _ HFrb a Ha).
      intros (r & Hin & Hr). cbn [In] in Hin.
      repeat (destruct Hin as [Hin | Hin]; [subst r|]); try destruct Hin;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U32' in Hr; lia. }
    pose proof (st_ok_pi_region_nth _ _ _ 0%nat _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
    rl_pull HS E15 F15.
    pose proof (field_of_region _ (mrestrict (w_H W) (ms_mem ms0)) 32%nat (D + n) _ 0 1 0 1 0 1%N (SOff 15 0) c
      HR0 U32' ltac:(left; reflexivity)
      ltac:(cbn [sv_denot]; rewrite F15; unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
      ltac:(cbn; lia) ltac:(cbn; lia)) as HVAL.
    change (N.to_nat 1) with 1%nat in HVAL. rewrite Z.add_0_r in HVAL.
    pmkst HS.
    prreg HS (24%bv : bv 5) R24. prreg HS (30%bv : bv 5) R30. prreg HS (15%bv : bv 5) R15.
    prreg HS (13%bv : bv 5) R13. prreg HS (10%bv : bv 5) R10. prreg HS (14%bv : bv 5) R14.
    prreg HS (27%bv : bv 5) R27. prreg HS (22%bv : bv 5) R22.
    rewrite E24 in R24. rewrite E30 in R30. rewrite E33 in R15. rewrite E13 in R13.
    rewrite E10 in R10. rewrite E14 in R14. rewrite E27 in R27. rewrite E22 in R22.
    unfold w64 in R24, R30, R15, R13, R10, R14, R27, R22.
    rewrite unsigned_lit_small in R24 by lia. rewrite unsigned_lit_small in R13 by lia.
    rewrite unsigned_lit_small in R10 by lia.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs' [w64 (D + n); w64 c2] KEPT1 HS
      ltac:(env_agree_chain (EL_agree regs' (D + n) c2)) ltac:(vm_compute; reflexivity)) as HK2.
    cbn [ms_regs restrict] in HK2.
    pose proof (st_ok_pi_restrict_reg _ _ _ _ (Z_to_bv 5 0) HSe) as Z0a. cbn [ms_regs mkst] in Z0a.
    pose proof (st_ok_pi_restrict_reg _ _ _ _ (Z_to_bv 5 0) HS) as Z0b. cbn [ms_regs mkst] in Z0b.
    assert (HKP2 : rbn_keep_regs regs' (ms_regs ms0) [5; 10; 11; 13; 15; 16; 17; 24; 30]).
    { apply (rl_keep_of _ _ KEPT1); [exact HK2 | rewrite Z0a, Z0b; vm_compute; reflexivity |].
      intros z Hz Hnc. unfold KEPT1.
      assert (Hd : z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/ z = 5 \/ z = 6 \/ z = 7 \/ z = 8 \/ z = 9
        \/ z = 10 \/ z = 11 \/ z = 12 \/ z = 13 \/ z = 14 \/ z = 15 \/ z = 16 \/ z = 17 \/ z = 18 \/ z = 19
        \/ z = 20 \/ z = 21 \/ z = 22 \/ z = 23 \/ z = 24 \/ z = 25 \/ z = 26 \/ z = 27 \/ z = 28 \/ z = 29
        \/ z = 30 \/ z = 31) by lia.
      repeat (destruct Hd as [Hd | Hd]); subst z;
      solve [ exfalso; apply Hnc; cbn [In]; repeat (first [left; reflexivity | right])
            | cbn [In]; repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]) ]. }
    change 14808 with (AF_reac_box_name + RBN_L1).
    assert (HgaQ : garr8 SEGS (mrestrict (w_H W) memc) (Q + 1) (t' ++ [0])).
    { intros j Hj.
      assert (Hj2 : (Datatypes.S j < length ((c :: t') ++ [0%Z]))%nat).
      { change ((c :: t') ++ [0%Z]) with (c :: (t' ++ [0%Z])). cbn [length]. lia. }
      destruct (Hga (Datatypes.S j) Hj2) as [Hv Hr].
      split; [|exact Hr]. replace (Q + 1 + Z.of_nat j) with (Q + Z.of_nat (Datatypes.S j)) by lia. exact Hv. }
    eapply (IH fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs D n0 (Q + 1) t'
      (ms_regs ms0) (ms_mem ms0) _ (n + 1) ov (wr ++ [c]) nF ovF wrF).
    - cbn [length] in Hm. lia.
    - rewrite HnF, HLn. lia.
    - rewrite HLn in HovF. replace (n + 1 + Z.of_nat (length t')) with (n + (Z.of_nat (length t') + 1)) by lia. exact HovF.
    - rewrite HwrF, <- app_assoc. f_equal.
      replace (Z.to_nat (23 - n)) with (Datatypes.S (Z.to_nat (23 - (n + 1)))) by lia. reflexivity.
    - exact Ht'.
    - exact Htb'.
    - exact HgaQ.
    - lia.
    - rewrite HLn in HQ47. lia.
    - apply (range_addressable_sub (aview SEGS (w_H W) memc) SHADOW_OFF Q (Z.of_nat (length (c :: t')) + 1));
        [exact Hra | lia | rewrite HLn; lia].
    - exact Hbuf.
    - rewrite HLn in Hdis. lia.
    - lia.
    - lia.
    - lia.
    - exact Hov.
    - rewrite length_app. cbn [length]. lia.
    - exact HJ.
    - eapply mem_grows_trans; [exact HMG | eapply mem_grows_trans; [exact HGa | exact HGb]].
    - intros a Ha Hn1. rewrite (KEEP2 a Ha ltac:(lia)), (KEEP1 a Ha ltac:(lia)). apply HF1; lia.
    - apply (garr8_app1 SEGS (mrestrict (w_H W) mem') (mrestrict (w_H W) (ms_mem ms0)) (D + n0) wr c Hgw).
      + rewrite Hwrl. replace (D + n0 + (n - n0)) with (D + n) by lia. exact HVAL.
      + lia.
      + intros a Ha. rewrite Hwrl in Ha. apply (mbyte_of_aview SEGS (w_H W) (w_H W)).
        rewrite (KEEP2 a ltac:(lia) ltac:(lia)). apply (KEEP1 a); lia.
    - unfold w64. exact R24.
    - unfold w64. exact R30.
    - unfold w64. rewrite <- (Hc2nz Ht'). exact R15.
    - unfold w64. replace (Q + 1 + 1) with (Q + 1 + 1) by lia. exact R13.
    - unfold w64. exact R10.
    - unfold w64. exact R14.
    - unfold w64. exact R27.
    - unfold w64. exact R22.
    - apply (rl_keep_trans regs regs' (ms_regs ms0)); [exact HKP | exact HKP2]. }
  {
    match goal with H : branch_taken _ _ _ = _ |- _ => rename H into HB end.
    rl_pull HS E33 F33. rl_pull HS E32 F32.
    rewrite branch_ne_U in HB. rewrite (U_atom _ 33 c2 F33) in HB by lia. rewrite U_lit in HB by lia.
    apply negb_false_iff, Z.eqb_eq in HB.
    assert (Ht'nil : t' = []) by (apply Hc2z; exact HB).
    assert (HwrE : wrF = wr ++ [c]).
    { rewrite HwrF, Ht'nil. f_equal.
      replace (Z.to_nat (23 - n)) with (Datatypes.S (Z.to_nat (23 - n - 1))) by lia.
      cbn [firstn]. rewrite firstn_nil. reflexivity. }
    assert (U32' : bv_unsigned (ew _ 32) = D + n) by (rewrite F32; unfold w64; apply unsigned_lit_small; lia).
    paj_run_to_tok RUNTO HS HJ SHOK Bspan (AF_reac_box_name + RBN_L1X).
    { eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32%nat (D + n)); [reflexivity | exact U32' | | ].
      - intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. exact (proj1 (HDbyte a ltac:(lia))).
      - apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil]. }
    rename HF into HFb. rename HFr into HFrb. rename HG into HGb.
    assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (D + n <= a < D + n + 1) ->
              aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) (ms_mem ms) a).
    { intros a Ha Hn1. apply (aview_kept_out _ _ (w_H W) _ _ HFrb a Ha).
      intros (r & Hin & Hr). cbn [In] in Hin.
      repeat (destruct Hin as [Hin | Hin]; [subst r|]); try destruct Hin;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U32' in Hr; lia. }
    pose proof (st_ok_pi_region_nth _ _ _ 0%nat _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
    rl_pull HS E15 F15.
    pose proof (field_of_region _ (mrestrict (w_H W) (ms_mem ms0)) 32%nat (D + n) _ 0 1 0 1 0 1%N (SOff 15 0) c
      HR0 U32' ltac:(left; reflexivity)
      ltac:(cbn [sv_denot]; rewrite F15; unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
      ltac:(cbn; lia) ltac:(cbn; lia)) as HVAL.
    change (N.to_nat 1) with 1%nat in HVAL. rewrite Z.add_0_r in HVAL.
    pmkst HS.
    prreg HS (24%bv : bv 5) R24. prreg HS (30%bv : bv 5) R30.
    rewrite E24 in R24. rewrite E30 in R30. unfold w64 in R24, R30.
    rewrite unsigned_lit_small in R24 by lia.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs' [w64 (D + n); w64 c2] KEPT1 HS
      ltac:(env_agree_chain (EL_agree regs' (D + n) c2)) ltac:(vm_compute; reflexivity)) as HK2.
    cbn [ms_regs restrict] in HK2.
    pose proof (st_ok_pi_restrict_reg _ _ _ _ (Z_to_bv 5 0) HSe) as Z0a. cbn [ms_regs mkst] in Z0a.
    pose proof (st_ok_pi_restrict_reg _ _ _ _ (Z_to_bv 5 0) HS) as Z0b. cbn [ms_regs mkst] in Z0b.
    assert (HKP2 : rbn_keep_regs regs' (ms_regs ms0) [5; 10; 11; 13; 15; 16; 17; 24; 30]).
    { apply (rl_keep_of _ _ KEPT1); [exact HK2 | rewrite Z0a, Z0b; vm_compute; reflexivity |].
      intros z Hz Hnc. unfold KEPT1.
      assert (Hd : z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/ z = 5 \/ z = 6 \/ z = 7 \/ z = 8 \/ z = 9
        \/ z = 10 \/ z = 11 \/ z = 12 \/ z = 13 \/ z = 14 \/ z = 15 \/ z = 16 \/ z = 17 \/ z = 18 \/ z = 19
        \/ z = 20 \/ z = 21 \/ z = 22 \/ z = 23 \/ z = 24 \/ z = 25 \/ z = 26 \/ z = 27 \/ z = 28 \/ z = 29
        \/ z = 30 \/ z = 31) by lia.
      repeat (destruct Hd as [Hd | Hd]); subst z;
      solve [ exfalso; apply Hnc; cbn [In]; repeat (first [left; reflexivity | right])
            | cbn [In]; repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]) ]. }
    assert (HnFe : nF = n + 1) by (rewrite HnF, Ht'nil; cbn [length]; lia).
    assert (HovFe : ovF = ov).
    { rewrite HovF, Ht'nil. cbn [length].
      replace (n + Z.of_nat 1 <=? 23) with true by (symmetry; apply Z.leb_le; cbn [Z.of_nat]; lia).
      reflexivity. }
    apply SRr_ret. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst ?rg _ ?mm _) ?mdx] => exists rg, mm, mdx end.
    split.
    { unfold cfg_at, w64. rewrite <- Z.add_assoc. change (AF_reac_box_name + RBN_L1X) with 14916. reflexivity. }
    split; [exact HJ|].
    split; [apply (rl_keep_trans regs regs' (ms_regs ms0)); [exact HKP | exact HKP2]|].
    split.
    { apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
      - rewrite HnFe. unfold w64. exact R24.
      - rewrite HovFe. unfold w64. exact R30. }
    split.
    { intros a Ha Hn1.
      assert (HlenF : Z.of_nat (length wrF) = n + 1 - n0) by (rewrite HwrE, length_app; cbn [length]; lia).
      rewrite HlenF in Hn1.
      rewrite (KEEP2 a Ha ltac:(lia)), (KEEP1 a Ha ltac:(lia)). apply HF1; lia. }
    rewrite HwrE.
    apply (garr8_app1 SEGS (mrestrict (w_H W) mem') (mrestrict (w_H W) (ms_mem ms0)) (D + n0) wr c Hgw).
    - rewrite Hwrl. replace (D + n0 + (n - n0)) with (D + n) by lia. exact HVAL.
    - lia.
    - intros a Ha. rewrite Hwrl in Ha. apply (mbyte_of_aview SEGS (w_H W) (w_H W)).
      rewrite (KEEP2 a ltac:(lia) ltac:(lia)). apply (KEEP1 a); lia. } }
{
  assert (Hne : n = 23) by lia.
  assert (H24' : getr regs' 24 = w64 23) by (rewrite H24, Hne; reflexivity).
  set (E := EL regs' (D + 23) c2).
  assert (HEI : img_env VAL A_LIM E) by apply EL_img.
  assert (E33 : ew E 33 = w64 c2) by apply EL_33.
  assert (E24 : ew E 24 = w64 23)
    by (unfold E; rewrite (EL_reg regs' _ _ 24%nat 24%bv) by (first [lia | vm_compute; reflexivity]); exact H24').
  assert (E30 : ew E 30 = w64 ov)
    by (unfold E; rewrite (EL_reg regs' _ _ 30%nat 30%bv) by (first [lia | vm_compute; reflexivity]); exact H30).
  assert (E15 : ew E 15 = w64 c)
    by (unfold E; rewrite (EL_reg regs' _ _ 15%nat 15%bv) by (first [lia | vm_compute; reflexivity]); exact H15).
  assert (E13 : ew E 13 = w64 (Q + 1))
    by (unfold E; rewrite (EL_reg regs' _ _ 13%nat 13%bv) by (first [lia | vm_compute; reflexivity]); exact H13).
  assert (E10 : ew E 10 = w64 (Q + 1))
    by (unfold E; rewrite (EL_reg regs' _ _ 10%nat 10%bv) by (first [lia | vm_compute; reflexivity]); exact H10).
  assert (E14 : ew E 14 = w64 23)
    by (unfold E; rewrite (EL_reg regs' _ _ 14%nat 14%bv) by (first [lia | vm_compute; reflexivity]); exact H14).
  assert (E27 : ew E 27 = w64 D)
    by (unfold E; rewrite (EL_reg regs' _ _ 27%nat 27%bv) by (first [lia | vm_compute; reflexivity]); exact H27).
  assert (E22 : ew E 22 = w64 SHADOW_OFF)
    by (unfold E; rewrite (EL_reg regs' _ _ 22%nat 22%bv) by (first [lia | vm_compute; reflexivity]); exact H22).
  assert (HS : st_ok_pi SEGS VAL E l1_sso
    (restrict (w_H W) (mkst (fx := fq) regs' (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L1))) mem' (seg_rom SEGS)))).
  { unfold E. apply (l1_entry_o fq W regs' mem' D ov c c2 Q); try assumption; try lia. }
  pose proof HS as HSe.
  assert (SHOK : sh_ok SEGS rl_Bx (@nil shent) E (mrestrict (w_H W) mem')) by (apply Forall_nil).
  paj_run_tok RUN HS HJ SHOK Bspan.
  { unfold rl_Bx. rewrite (U_atom E 22 SHADOW_OFF E22) by (unfold SHADOW_OFF; lia).
    rewrite (U_atom E 10 (Q + 1) E10) by lia.
    rewrite <- (aview_rd_of SEGS). exact HRAQ. }
  { apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi rl_srcR]; lia | apply awr_ok_nil]. }
  rename HF into HFa. rename HFr into HFra. rename HG into HGa.
  assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem' a).
  { intros a Ha. apply (aview_kept_out _ _ (w_H W) _ _ HFra a Ha).
    intros (r & Hin & Hr). cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [subst r|]); try destruct Hin;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val rl_srcR] in Hr; lia. }
  psrr_branch_tok RUN BR HS SHOK Bspan.
  {
    match goal with H : branch_taken _ _ _ = _ |- _ => rename H into HB end.
    rl_pull HS E33 F33. rl_pull HS E24 F24. rl_pull HS E30 F30.
    rl_pull HS E13 F13. rl_pull HS E10 F10. rl_pull HS E14 F14. rl_pull HS E27 F27. rl_pull HS E22 F22.
    rewrite branch_ne_U in HB. rewrite (U_atom _ 33 c2 F33) in HB by lia. rewrite U_lit in HB by lia.
    apply negb_true_iff, Z.eqb_neq in HB.
    assert (Ht' : t' <> []) by (intros Hx; apply HB; apply Hc2nil; exact Hx).
    paj_run_to_tok RUNTO HS HJ SHOK Bspan (AF_reac_box_name + RBN_L1).
    { apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil]. }
    rename HF into HFb. rename HFr into HFrb. rename HG into HGb.
    assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) (ms_mem ms) a).
    { intros a Ha. apply (aview_kept_out _ _ (w_H W) _ _ HFrb a Ha).
      intros (r & Hin & Hr). cbn [In] in Hin.
      repeat (destruct Hin as [Hin | Hin]; [subst r|]); try destruct Hin;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia. }
    pmkst HS.
    prreg HS (24%bv : bv 5) R24. prreg HS (30%bv : bv 5) R30. prreg HS (15%bv : bv 5) R15.
    prreg HS (13%bv : bv 5) R13. prreg HS (10%bv : bv 5) R10. prreg HS (14%bv : bv 5) R14.
    prreg HS (27%bv : bv 5) R27. prreg HS (22%bv : bv 5) R22.
    rewrite E24 in R24. rewrite E33 in R15. rewrite E13 in R13.
    rewrite E10 in R10. rewrite E14 in R14. rewrite E27 in R27. rewrite E22 in R22.
    unfold w64 in R24, R30, R15, R13, R10, R14, R27, R22.
    rewrite unsigned_lit_small in R13 by lia. rewrite unsigned_lit_small in R10 by lia.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs' [w64 (D + 23); w64 c2] KEPT1 HS
      ltac:(env_agree_chain (EL_agree regs' (D + 23) c2)) ltac:(vm_compute; reflexivity)) as HK2.
    cbn [ms_regs restrict] in HK2.
    pose proof (st_ok_pi_restrict_reg _ _ _ _ (Z_to_bv 5 0) HSe) as Z0a. cbn [ms_regs mkst] in Z0a.
    pose proof (st_ok_pi_restrict_reg _ _ _ _ (Z_to_bv 5 0) HS) as Z0b. cbn [ms_regs mkst] in Z0b.
    assert (HKP2 : rbn_keep_regs regs' (ms_regs ms0) [5; 10; 11; 13; 15; 16; 17; 24; 30]).
    { apply (rl_keep_of _ _ KEPT1); [exact HK2 | rewrite Z0a, Z0b; vm_compute; reflexivity |].
      intros z Hz Hnc. unfold KEPT1.
      assert (Hd : z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/ z = 5 \/ z = 6 \/ z = 7 \/ z = 8 \/ z = 9
        \/ z = 10 \/ z = 11 \/ z = 12 \/ z = 13 \/ z = 14 \/ z = 15 \/ z = 16 \/ z = 17 \/ z = 18 \/ z = 19
        \/ z = 20 \/ z = 21 \/ z = 22 \/ z = 23 \/ z = 24 \/ z = 25 \/ z = 26 \/ z = 27 \/ z = 28 \/ z = 29
        \/ z = 30 \/ z = 31) by lia.
      repeat (destruct Hd as [Hd | Hd]); subst z;
      solve [ exfalso; apply Hnc; cbn [In]; repeat (first [left; reflexivity | right])
            | cbn [In]; repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]) ]. }
    change 14808 with (AF_reac_box_name + RBN_L1).
    assert (HgaQ : garr8 SEGS (mrestrict (w_H W) memc) (Q + 1) (t' ++ [0])).
    { intros j Hj.
      assert (Hj2 : (Datatypes.S j < length ((c :: t') ++ [0%Z]))%nat).
      { change ((c :: t') ++ [0%Z]) with (c :: (t' ++ [0%Z])). cbn [length]. lia. }
      destruct (Hga (Datatypes.S j) Hj2) as [Hv Hr].
      split; [|exact Hr]. replace (Q + 1 + Z.of_nat j) with (Q + Z.of_nat (Datatypes.S j)) by lia. exact Hv. }
    eapply (IH fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs D n0 (Q + 1) t'
      (ms_regs ms0) (ms_mem ms0) _ n 1 wr nF ovF wrF).
    - cbn [length] in Hm. lia.
    - rewrite HnF, HLn. lia.
    - rewrite HovF, HLn.
      replace (n + (Z.of_nat (length t') + 1) <=? 23) with false by (symmetry; apply Z.leb_gt; lia).
      destruct (n + Z.of_nat (length t') <=? 23); reflexivity.
    - rewrite HwrF. replace (Z.to_nat (23 - n)) with 0%nat by lia. reflexivity.
    - exact Ht'.
    - exact Htb'.
    - exact HgaQ.
    - lia.
    - rewrite HLn in HQ47. lia.
    - apply (range_addressable_sub (aview SEGS (w_H W) memc) SHADOW_OFF Q (Z.of_nat (length (c :: t')) + 1));
        [exact Hra | lia | rewrite HLn; lia].
    - exact Hbuf.
    - rewrite HLn in Hdis. lia.
    - lia.
    - lia.
    - lia.
    - right; reflexivity.
    - exact Hwrl.
    - exact HJ.
    - eapply mem_grows_trans; [exact HMG | eapply mem_grows_trans; [exact HGa | exact HGb]].
    - intros a Ha Hn1. rewrite (KEEP2 a Ha), (KEEP1 a Ha). apply HF1; lia.
    - apply (rl_garr8_kept (w_H W) mem' (ms_mem ms0) (D + n0) wr);
        [intros a Ha; rewrite (KEEP2 a ltac:(lia)); apply (KEEP1 a); lia | exact Hgw].
    - unfold w64. rewrite Hne. exact R24.
    - unfold w64. exact R30.
    - unfold w64. rewrite <- (Hc2nz Ht'). exact R15.
    - unfold w64. exact R13.
    - unfold w64. exact R10.
    - unfold w64. exact R14.
    - unfold w64. exact R27.
    - unfold w64. exact R22.
    - apply (rl_keep_trans regs regs' (ms_regs ms0)); [exact HKP | exact HKP2]. }
  {
    match goal with H : branch_taken _ _ _ = _ |- _ => rename H into HB end.
    rl_pull HS E33 F33.
    rewrite branch_ne_U in HB. rewrite (U_atom _ 33 c2 F33) in HB by lia. rewrite U_lit in HB by lia.
    apply negb_false_iff, Z.eqb_eq in HB.
    assert (Ht'nil : t' = []) by (apply Hc2z; exact HB).
    assert (HwrE : wrF = wr) by (rewrite HwrF; replace (Z.to_nat (23 - n)) with 0%nat by lia;
      cbn [firstn]; rewrite app_nil_r; reflexivity).
    paj_run_to_tok RUNTO HS HJ SHOK Bspan (AF_reac_box_name + RBN_L1X).
    { apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil]. }
    rename HF into HFb. rename HFr into HFrb. rename HG into HGb.
    assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) (ms_mem ms) a).
    { intros a Ha. apply (aview_kept_out _ _ (w_H W) _ _ HFrb a Ha).
      intros (r & Hin & Hr). cbn [In] in Hin.
      repeat (destruct Hin as [Hin | Hin]; [subst r|]); try destruct Hin;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia. }
    pmkst HS.
    prreg HS (24%bv : bv 5) R24. prreg HS (30%bv : bv 5) R30.
    rewrite E24 in R24. unfold w64 in R24, R30.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs' [w64 (D + 23); w64 c2] KEPT1 HS
      ltac:(env_agree_chain (EL_agree regs' (D + 23) c2)) ltac:(vm_compute; reflexivity)) as HK2.
    cbn [ms_regs restrict] in HK2.
    pose proof (st_ok_pi_restrict_reg _ _ _ _ (Z_to_bv 5 0) HSe) as Z0a. cbn [ms_regs mkst] in Z0a.
    pose proof (st_ok_pi_restrict_reg _ _ _ _ (Z_to_bv 5 0) HS) as Z0b. cbn [ms_regs mkst] in Z0b.
    assert (HKP2 : rbn_keep_regs regs' (ms_regs ms0) [5; 10; 11; 13; 15; 16; 17; 24; 30]).
    { apply (rl_keep_of _ _ KEPT1); [exact HK2 | rewrite Z0a, Z0b; vm_compute; reflexivity |].
      intros z Hz Hnc. unfold KEPT1.
      assert (Hd : z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/ z = 5 \/ z = 6 \/ z = 7 \/ z = 8 \/ z = 9
        \/ z = 10 \/ z = 11 \/ z = 12 \/ z = 13 \/ z = 14 \/ z = 15 \/ z = 16 \/ z = 17 \/ z = 18 \/ z = 19
        \/ z = 20 \/ z = 21 \/ z = 22 \/ z = 23 \/ z = 24 \/ z = 25 \/ z = 26 \/ z = 27 \/ z = 28 \/ z = 29
        \/ z = 30 \/ z = 31) by lia.
      repeat (destruct Hd as [Hd | Hd]); subst z;
      solve [ exfalso; apply Hnc; cbn [In]; repeat (first [left; reflexivity | right])
            | cbn [In]; repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]) ]. }
    assert (HnFe : nF = 23) by (rewrite HnF, HLn; lia).
    assert (HovFe : ovF = 1)
      by (rewrite HovF, HLn; replace (n + (Z.of_nat (length t') + 1) <=? 23) with false
            by (symmetry; apply Z.leb_gt; lia); reflexivity).
    apply SRr_ret. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst ?rg _ ?mm _) ?mdx] => exists rg, mm, mdx end.
    split.
    { unfold cfg_at, w64. rewrite <- Z.add_assoc. change (AF_reac_box_name + RBN_L1X) with 14916. reflexivity. }
    split; [exact HJ|].
    split; [apply (rl_keep_trans regs regs' (ms_regs ms0)); [exact HKP | exact HKP2]|].
    split.
    { apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
      - rewrite HnFe. unfold w64. exact R24.
      - rewrite HovFe. unfold w64. exact R30. }
    split.
    { intros a Ha Hn1. rewrite (KEEP2 a Ha), (KEEP1 a Ha). apply HF1; [lia|].
      rewrite HwrE in Hn1. lia. }
    rewrite HwrE.
    apply (rl_garr8_kept (w_H W) mem' (ms_mem ms0) (D + n0) wr);
      [intros a Ha; rewrite (KEEP2 a ltac:(lia)); apply (KEEP1 a); lia | exact Hgw]. } }
Qed.
Theorem rbn_l1_fits : rbn_L1_fits B.
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s Hlen.
unfold rbn_L1_run. intros HJ Hs0 Hsb Hsrc Hbuf Hdis Hn0 Hov H24 H30 H15 H13 H10 H14 H27 H22.
unfold rbn_lsrc in Hsrc.
pose proof (proj1 Hsrc) as Hga. pose proof (proj1 (proj2 Hsrc)) as HP0.
pose proof (proj1 (proj2 (proj2 Hsrc))) as HP63. pose proof (proj1 (proj2 (proj2 (proj2 Hsrc)))) as HP47.
pose proof (proj2 (proj2 (proj2 (proj2 Hsrc)))) as Hra.
rewrite length_app in HP63, HP47, Hra. cbn [length] in HP63, HP47, Hra.
replace (Z.of_nat (length s + 1)) with (Z.of_nat (length s) + 1) in HP63, HP47, Hra by lia.
change (cfg_at (fx := fq) SEGS (BASE + AF_reac_box_name + RBN_L1) regs memc mdc)
  with (mkCfg (mkst (fx := fq) regs (Z_to_bv 64 (BASE + AF_reac_box_name + RBN_L1)) memc (seg_rom SEGS)) mdc).
rewrite <- Z.add_assoc.
eapply (rbn_l1_core (length s) fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs D n0 P s regs memc mdc
  n0 ov0 [] (n0 + Z.of_nat (length s)) ov0 s).
- lia.
- lia.
- replace (n0 + Z.of_nat (length s) <=? 23) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
- cbn [app]. symmetry. apply firstn_all2. lia.
- exact Hs0.
- exact Hsb.
- exact Hga.
- exact HP0.
- lia.
- exact Hra.
- exact Hbuf.
- exact Hdis.
- lia.
- lia.
- lia.
- exact Hov.
- cbn [length]. lia.
- exact HJ.
- apply mem_grows_refl.
- intros a Ha Hn. reflexivity.
- apply garr8_nil.
- exact H24.
- exact H30.
- exact H15.
- exact H13.
- exact H10.
- exact H14.
- exact H27.
- exact H22.
- intros z Hz Hnc. reflexivity.
Qed.
Theorem rbn_l1_ovf : rbn_L1_ovf B.
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s Hlen.
unfold rbn_L1_run. intros HJ Hs0 Hsb Hsrc Hbuf Hdis Hn0 Hov H24 H30 H15 H13 H10 H14 H27 H22.
unfold rbn_lsrc in Hsrc.
pose proof (proj1 Hsrc) as Hga. pose proof (proj1 (proj2 Hsrc)) as HP0.
pose proof (proj1 (proj2 (proj2 Hsrc))) as HP63. pose proof (proj1 (proj2 (proj2 (proj2 Hsrc)))) as HP47.
pose proof (proj2 (proj2 (proj2 (proj2 Hsrc)))) as Hra.
rewrite length_app in HP63, HP47, Hra. cbn [length] in HP63, HP47, Hra.
replace (Z.of_nat (length s + 1)) with (Z.of_nat (length s) + 1) in HP63, HP47, Hra by lia.
change (cfg_at (fx := fq) SEGS (BASE + AF_reac_box_name + RBN_L1) regs memc mdc)
  with (mkCfg (mkst (fx := fq) regs (Z_to_bv 64 (BASE + AF_reac_box_name + RBN_L1)) memc (seg_rom SEGS)) mdc).
rewrite <- Z.add_assoc.
eapply (rbn_l1_core (length s) fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs D n0 P s regs memc mdc
  n0 ov0 [] 23 1 (firstn (Z.to_nat (23 - n0)) s)).
- lia.
- lia.
- replace (n0 + Z.of_nat (length s) <=? 23) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
- cbn [app]. reflexivity.
- exact Hs0.
- exact Hsb.
- exact Hga.
- exact HP0.
- lia.
- exact Hra.
- exact Hbuf.
- exact Hdis.
- lia.
- lia.
- lia.
- exact Hov.
- cbn [length]. lia.
- exact HJ.
- apply mem_grows_refl.
- intros a Ha Hn. reflexivity.
- apply garr8_nil.
- exact H24.
- exact H30.
- exact H15.
- exact H13.
- exact H10.
- exact H14.
- exact H27.
- exact H22.
- intros z Hz Hnc. reflexivity.
Qed.
Lemma l4_entry_f : forall (fq : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (D n ov c c2 Q : Z),
  0 <= n <= 46 -> (ov = 0 \/ ov = 1) -> 0 < c < 256 -> 0 <= c2 < 256 ->
  4096 <= D -> D + n <= 2 ^ 47 - 1 -> 0 <= Q -> Q + 2 <= 2 ^ 47 ->
  (Q + 2 <= D + n \/ D + n + 1 <= Q + 1) ->
  getr regs 11 = w64 n -> getr regs 12 = w64 ov -> getr regs 15 = w64 c ->
  getr regs 13 = w64 (Q + 1) -> getr regs 10 = w64 (Q + 1) -> getr regs 14 = w64 47 ->
  getr regs 20 = w64 D -> getr regs 22 = w64 SHADOW_OFF ->
  apresent (w_H W) mem (D + n) ->
  val_mem SEGS (mrestrict (w_H W) mem) (Q + 1) 1 c2 ->
  st_ok_pi SEGS VAL (EL regs (D + n) c2) l4_ssf
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L4))) mem (seg_rom SEGS))).
Proof.
intros fq W regs mem D n ov c c2 Q Hn Hov Hc Hc2 HD4 HD47 HQ0 HQ47 Hdisj
  H11 H12 H15 H13 H10 H14 H20 H22 Hap Hmem.
assert (E32 : ew (EL regs (D + n) c2) 32 = w64 (D + n)) by apply EL_32.
assert (E33 : ew (EL regs (D + n) c2) 33 = w64 c2) by apply EL_33.
assert (E11 : ew (EL regs (D + n) c2) 11 = w64 n)
  by (rewrite (EL_reg regs _ _ 11%nat 11%bv) by (first [lia | vm_compute; reflexivity]); exact H11).
assert (E12 : ew (EL regs (D + n) c2) 12 = w64 ov)
  by (rewrite (EL_reg regs _ _ 12%nat 12%bv) by (first [lia | vm_compute; reflexivity]); exact H12).
assert (E15 : ew (EL regs (D + n) c2) 15 = w64 c)
  by (rewrite (EL_reg regs _ _ 15%nat 15%bv) by (first [lia | vm_compute; reflexivity]); exact H15).
assert (E13 : ew (EL regs (D + n) c2) 13 = w64 (Q + 1))
  by (rewrite (EL_reg regs _ _ 13%nat 13%bv) by (first [lia | vm_compute; reflexivity]); exact H13).
assert (E10 : ew (EL regs (D + n) c2) 10 = w64 (Q + 1))
  by (rewrite (EL_reg regs _ _ 10%nat 10%bv) by (first [lia | vm_compute; reflexivity]); exact H10).
assert (E14 : ew (EL regs (D + n) c2) 14 = w64 47)
  by (rewrite (EL_reg regs _ _ 14%nat 14%bv) by (first [lia | vm_compute; reflexivity]); exact H14).
assert (E20 : ew (EL regs (D + n) c2) 20 = w64 D)
  by (rewrite (EL_reg regs _ _ 20%nat 20%bv) by (first [lia | vm_compute; reflexivity]); exact H20).
assert (E22 : ew (EL regs (D + n) c2) 22 = w64 SHADOW_OFF)
  by (rewrite (EL_reg regs _ _ 22%nat 22%bv) by (first [lia | vm_compute; reflexivity]); exact H22).
assert (U32 : bv_unsigned (ew (EL regs (D + n) c2) 32) = D + n)
  by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
assert (U13 : bv_unsigned (ew (EL regs (D + n) c2) 13) = Q + 1)
  by (rewrite E13; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold l4_ssf, l4_ff, rl_cmn. apply pa_entry_st_ok_full.
- unfold EL. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold rl_dstR, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U32. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. assert (o = 0) by lia. subst o. rewrite Z.add_0_r.
    apply (apresent_writable SEGS). exact Hap.
  + unfold rl_srcR, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U13. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS _ _ (Q + 1) 0 1 (SOff 33 0) c2);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    change (N.to_nat 1) with 1%nat. rewrite Z.add_0_r. exact Hmem.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, rl_dstR, rl_srcR.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U32, U13. split; [|split; exact I]. split; [lia|exact I].
- split; [|split; [exact I|]].
  + cbn [f_atoms atoms_ok].
    split; [apply (rl_afact _ _ n); [exact E11 | lia | lia | lia]|].
    split; [apply (rl_afact _ _ 47); [exact E14 | lia | lia | lia]|].
    split; [apply (rl_afact _ _ ov); [exact E12 | lia | lia | lia]|].
    split; [apply (rl_afact _ _ (D + n)); [exact E32 | lia | lia | lia]|].
    split; [apply (rl_afact _ _ SHADOW_OFF); [exact E22 | unfold SHADOW_OFF; lia | unfold SB, SHADOW_OFF; lia | unfold SB, SHADOW_OFF; lia]|].
    split; [apply (rl_afact _ _ c); [exact E15 | lia | lia | lia]|].
    split; [apply (rl_afact _ _ c2); [exact E33 | lia | lia | lia]|].
    split; [apply (rl_afact _ _ (Q + 1)); [exact E10 | lia | lia | lia]|].
    split; [apply (rl_afact _ _ (Q + 1)); [exact E13 | lia | lia | lia]|]. exact I.
  + cbn [f_alias alias_ok]. split; [|exact I].
    apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
    rewrite (U_atom _ 20 D E20) by lia. rewrite (U_atom _ 11 n E11) by lia.
    rewrite (U_atom _ 32 (D + n) E32) by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma l4_entry_o : forall (fq : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (D ov c c2 Q : Z),
  (ov = 0 \/ ov = 1) -> 0 < c < 256 -> 0 <= c2 < 256 ->
  0 <= Q -> Q + 2 <= 2 ^ 47 ->
  getr regs 11 = w64 47 -> getr regs 12 = w64 ov -> getr regs 15 = w64 c ->
  getr regs 13 = w64 (Q + 1) -> getr regs 10 = w64 (Q + 1) -> getr regs 14 = w64 47 ->
  getr regs 22 = w64 SHADOW_OFF ->
  val_mem SEGS (mrestrict (w_H W) mem) (Q + 1) 1 c2 ->
  st_ok_pi SEGS VAL (EL regs (D + 47) c2) l4_sso
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L4))) mem (seg_rom SEGS))).
Proof.
intros fq W regs mem D ov c c2 Q Hov Hc Hc2 HQ0 HQ47 H11 H12 H15 H13 H10 H14 H22 Hmem.
assert (E33 : ew (EL regs (D + 47) c2) 33 = w64 c2) by apply EL_33.
assert (E11 : ew (EL regs (D + 47) c2) 11 = w64 47)
  by (rewrite (EL_reg regs _ _ 11%nat 11%bv) by (first [lia | vm_compute; reflexivity]); exact H11).
assert (E12 : ew (EL regs (D + 47) c2) 12 = w64 ov)
  by (rewrite (EL_reg regs _ _ 12%nat 12%bv) by (first [lia | vm_compute; reflexivity]); exact H12).
assert (E15 : ew (EL regs (D + 47) c2) 15 = w64 c)
  by (rewrite (EL_reg regs _ _ 15%nat 15%bv) by (first [lia | vm_compute; reflexivity]); exact H15).
assert (E13 : ew (EL regs (D + 47) c2) 13 = w64 (Q + 1))
  by (rewrite (EL_reg regs _ _ 13%nat 13%bv) by (first [lia | vm_compute; reflexivity]); exact H13).
assert (E10 : ew (EL regs (D + 47) c2) 10 = w64 (Q + 1))
  by (rewrite (EL_reg regs _ _ 10%nat 10%bv) by (first [lia | vm_compute; reflexivity]); exact H10).
assert (E14 : ew (EL regs (D + 47) c2) 14 = w64 47)
  by (rewrite (EL_reg regs _ _ 14%nat 14%bv) by (first [lia | vm_compute; reflexivity]); exact H14).
assert (E22 : ew (EL regs (D + 47) c2) 22 = w64 SHADOW_OFF)
  by (rewrite (EL_reg regs _ _ 22%nat 22%bv) by (first [lia | vm_compute; reflexivity]); exact H22).
assert (U13 : bv_unsigned (ew (EL regs (D + 47) c2) 13) = Q + 1)
  by (rewrite E13; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold l4_sso, l4_fo, rl_cmn. apply pa_entry_st_ok_full.
- unfold EL. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  unfold rl_srcR, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U13. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ (Q + 1) 0 1 (SOff 33 0) c2);
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
  change (N.to_nat 1) with 1%nat. rewrite Z.add_0_r. exact Hmem.
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- split; [|split; exact I].
  cbn [f_atoms atoms_ok].
  split; [apply (rl_afact _ _ 47); [exact E11 | lia | lia | lia]|].
  split; [apply (rl_afact _ _ 47); [exact E14 | lia | lia | lia]|].
  split; [apply (rl_afact _ _ ov); [exact E12 | lia | lia | lia]|].
  split; [apply (rl_afact _ _ SHADOW_OFF); [exact E22 | unfold SHADOW_OFF; lia | unfold SB, SHADOW_OFF; lia | unfold SB, SHADOW_OFF; lia]|].
  split; [apply (rl_afact _ _ c); [exact E15 | lia | lia | lia]|].
  split; [apply (rl_afact _ _ c2); [exact E33 | lia | lia | lia]|].
  split; [apply (rl_afact _ _ (Q + 1)); [exact E10 | lia | lia | lia]|].
  split; [apply (rl_afact _ _ (Q + 1)); [exact E13 | lia | lia | lia]|]. exact I.
Qed.
Lemma rbn_l4_core : forall (m : nat) (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc
  (W : world SEGS) (memc : word -> option byte) (k : Z) (regs : bvmap 5 word) (D n0 : Z)
  (Q : Z) (t : list Z) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model)
  (n ov : Z) (wr : list Z) (nF ovF : Z) (wrF : list Z),
  (length t <= m)%nat ->
  nF = Z.min (n + Z.of_nat (length t)) 47 ->
  ovF = (if n + Z.of_nat (length t) <=? 47 then ov else 1) ->
  wrF = wr ++ firstn (Z.to_nat (47 - n)) t ->
  t <> [] -> Forall (fun x => 0 < x < 256) t ->
  garr8 SEGS (mrestrict (w_H W) memc) Q (t ++ [0]) ->
  0 <= Q -> Q + Z.of_nat (length t) + 1 <= 2 ^ 47 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF Q (Z.of_nat (length t) + 1) ->
  rbn_lbuf B STK sp0 FP ly S own lyc Sc W memc D 48 ->
  (Q + Z.of_nat (length t) + 1 <= D \/ D + 48 <= Q) ->
  0 <= n0 -> n0 <= n -> n <= 47 -> (ov = 0 \/ ov = 1) ->
  Z.of_nat (length wr) = n - n0 ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
  mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) mem') ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (D + n0 <= a < D + n) -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a) ->
  garr8 SEGS (mrestrict (w_H W) mem') (D + n0) wr ->
  getr regs' 11 = w64 n -> getr regs' 12 = w64 ov -> getr regs' 15 = w64 (hd 0 t) ->
  getr regs' 13 = w64 (Q + 1) -> getr regs' 10 = w64 (Q + 1) -> getr regs' 14 = w64 47 ->
  getr regs' 20 = w64 D -> getr regs' 22 = w64 SHADOW_OFF ->
  rbn_keep_regs regs regs' [5; 10; 11; 12; 13; 15; 16; 17] ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs' (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L4))) mem' (seg_rom SEGS)) md')
    (rbn_lpost B fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L4X
       [5; 10; 11; 12; 13; 15; 16; 17] D n0 wrF [(11, nF); (12, ovF)]).
Proof.
intros m. induction m as [|m IH];
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs D n0 Q t regs' mem' md' n ov wr nF ovF wrF
  Hm HnF HovF HwrF Ht0 Htb Hga HQ0 HQ47 Hra Hbuf Hdis Hn00 Hn0n Hn47 Hov Hwrl HJ HMG HF1 Hgw
  H11 H12 H15 H13 H10 H14 H20 H22 HKP.
{ exfalso. destruct t as [|c t']; [exact (Ht0 eq_refl) | cbn [length] in Hm; lia]. }
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof (@paj_run fq _ _ _ _ _ B LAWS) as RUN.
pose proof (@paj_run_to fq _ _ _ _ _ B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (L := disco_listing) (PI := PI)) as BR.
destruct t as [|c t']; [exact (False_ind _ (Ht0 eq_refl))|].
pose proof Hbuf as (HD0 & HD63 & HDapp & HDra & HDbyte).
assert (H4096 : 4096 <= D) by (destruct HDapp as [HH _]; exact HH).
ceil.
assert (HD47 : D + 48 <= 2 ^ 47 - 1)
  by (destruct HDapp as [_ [HL | [HH1 HH2]]]; unfold kLowShadowBeg, kHighMemBeg in *; lia).
assert (HLn : Z.of_nat (length (c :: t')) = Z.of_nat (length t') + 1) by (cbn [length]; lia).
assert (Hcr : 0 < c < 256) by (inversion Htb; assumption).
assert (Htb' : Forall (fun x => 0 < x < 256) t') by (inversion Htb; assumption).
assert (Hidx : (1 < length ((c :: t') ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
destruct (Hga 1%nat Hidx) as [Hc2m0 Hc2r].
change (Z.of_nat 1) with 1 in Hc2m0.
set (c2 := nth 1 ((c :: t') ++ [0]) 0) in *.
assert (Hc2z : c2 = 0 -> t' = []).
{ unfold c2. destruct t' as [|x t'']; [reflexivity|]. cbn [app nth]. intros Hx. exfalso. inversion Htb'. lia. }
assert (Hc2nil : t' = [] -> c2 = 0) by (intros Hx; unfold c2; rewrite Hx; reflexivity).
assert (Hc2nz : t' <> [] -> c2 = hd 0 t').
{ unfold c2. destruct t' as [|x t'']; [intros HX; exfalso; exact (HX eq_refl)|]. cbn [app nth hd]. reflexivity. }
assert (HSEP : forall a, Q <= a <= Q + Z.of_nat (length t') + 1 -> ~ (D <= a < D + 48))
  by (intros a Ha; rewrite HLn in Hdis; lia).
assert (HQ2 : Q + 2 <= 2 ^ 47) by (rewrite HLn in HQ47; lia).
assert (Hc2m : val_mem SEGS (mrestrict (w_H W) mem') (Q + 1) 1 c2).
{ apply (val_mem_kept SEGS (w_H W) (w_H W) memc mem' (Q + 1) 1 c2); [|exact Hc2m0].
  intros j Hj. cbn [Z.of_nat] in Hj. assert (Hj0 : j = 0) by lia. subst j. rewrite Z.add_0_r.
  apply HF1; [lia|]. intros Hbad. apply (HSEP (Q + 1) ltac:(lia)). lia. }
assert (HRAQ : range_addressable (aview SEGS (w_H W) mem') SHADOW_OFF (Q + 1) 1).
{ apply (rl_ra_kept (w_H W) memc mem' (Q + 1) 1).
  - intros x Hx. apply HF1.
    + unfold SHADOW_OFF. assert (0 <= x / 8 < 2 ^ 47) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). lia.
    + intros Hbad. apply (rl_shadow_apart D 48 x HDapp ltac:(lia) ltac:(rewrite HLn in HQ47; lia)). lia.
  - apply (range_addressable_sub (aview SEGS (w_H W) memc) SHADOW_OFF Q (Z.of_nat (length (c :: t')) + 1));
    [exact Hra | lia | rewrite HLn; lia]. }
cbn [hd] in H15.
destruct (Z_le_gt_dec n 46) as [Hn22 | Hngt].
{
  assert (HDn : D <= D + n < D + 48) by lia.
  destruct (HDbyte (D + n) ltac:(lia)) as [Hawr Hap0].
  assert (Hap : apresent (w_H W) mem' (D + n))
    by (apply (apresent_grows (w_H W) memc mem'); [exact HMG | exact Hap0]).
  set (E := EL regs' (D + n) c2).
  assert (HEI : img_env VAL A_LIM E) by apply EL_img.
  assert (E32 : ew E 32 = w64 (D + n)) by apply EL_32.
  assert (E33 : ew E 33 = w64 c2) by apply EL_33.
  assert (E11 : ew E 11 = w64 n)
    by (unfold E; rewrite (EL_reg regs' _ _ 11%nat 11%bv) by (first [lia | vm_compute; reflexivity]); exact H11).
  assert (E12 : ew E 12 = w64 ov)
    by (unfold E; rewrite (EL_reg regs' _ _ 12%nat 12%bv) by (first [lia | vm_compute; reflexivity]); exact H12).
  assert (E15 : ew E 15 = w64 c)
    by (unfold E; rewrite (EL_reg regs' _ _ 15%nat 15%bv) by (first [lia | vm_compute; reflexivity]); exact H15).
  assert (E13 : ew E 13 = w64 (Q + 1))
    by (unfold E; rewrite (EL_reg regs' _ _ 13%nat 13%bv) by (first [lia | vm_compute; reflexivity]); exact H13).
  assert (E10 : ew E 10 = w64 (Q + 1))
    by (unfold E; rewrite (EL_reg regs' _ _ 10%nat 10%bv) by (first [lia | vm_compute; reflexivity]); exact H10).
  assert (E14 : ew E 14 = w64 47)
    by (unfold E; rewrite (EL_reg regs' _ _ 14%nat 14%bv) by (first [lia | vm_compute; reflexivity]); exact H14).
  assert (E20 : ew E 20 = w64 D)
    by (unfold E; rewrite (EL_reg regs' _ _ 20%nat 20%bv) by (first [lia | vm_compute; reflexivity]); exact H20).
  assert (E22 : ew E 22 = w64 SHADOW_OFF)
    by (unfold E; rewrite (EL_reg regs' _ _ 22%nat 22%bv) by (first [lia | vm_compute; reflexivity]); exact H22).
  assert (U32 : bv_unsigned (ew E 32) = D + n) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
  assert (U13 : bv_unsigned (ew E 13) = Q + 1) by (rewrite E13; unfold w64; apply unsigned_lit_small; lia).
  assert (HS : st_ok_pi SEGS VAL E l4_ssf
    (restrict (w_H W) (mkst (fx := fq) regs' (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L4))) mem' (seg_rom SEGS)))).
  { unfold E. apply (l4_entry_f fq W regs' mem' D n ov c c2 Q); try assumption; try lia. }
  pose proof HS as HSe.
  assert (SHOK : sh_ok SEGS rl_Bx rl_SH E (mrestrict (w_H W) mem')).
  { unfold sh_ok, rl_SH. apply Forall_cons; [|apply Forall_nil].
    unfold shent_ok, rl_Bx. cbn [she_m she_lo she_hi].
    rewrite (U_atom E 22 SHADOW_OFF E22) by (unfold SHADOW_OFF; lia).
    rewrite (U_atom E 32 (D + n) E32) by lia.
    split.
    - rewrite Z.add_0_r. rewrite <- (aview_rd_of SEGS). change (1 - 0) with 1.
      apply (rl_ra_kept (w_H W) memc mem' (D + n) 1).
      + intros x Hx. apply HF1.
        * unfold SHADOW_OFF. assert (0 <= x / 8 < 2 ^ 47) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). lia.
        * intros Hbad. apply (rl_shadow_apart D 48 x HDapp ltac:(lia) ltac:(lia)). lia.
      + apply (range_addressable_sub (aview SEGS (w_H W) memc) SHADOW_OFF D 48); [exact HDra | lia | lia].
    - unfold app_apart. cbn [she_m she_lo she_hi].
      intros a Ha.
      rewrite (U_atom E 32 (D + n) E32) in Ha by lia.
      rewrite (U_atom E 22 SHADOW_OFF E22) by (unfold SHADOW_OFF; lia).
      apply (rl_not_shadow D 48 a HDapp). lia. }
  paj_run_tok RUN HS HJ SHOK Bspan.
  { unfold rl_Bx. rewrite (U_atom E 22 SHADOW_OFF E22) by (unfold SHADOW_OFF; lia).
    rewrite (U_atom E 10 (Q + 1) E10) by lia.
    rewrite <- (aview_rd_of SEGS). exact HRAQ. }
  { eapply (awr_ok_cons_gen E rl_dstR _ _ _ _ _ _ _ _ 32%nat (D + n)); [reflexivity | exact U32 | | ].
    - intros a Ha. cbn [YP09.r_wlo YP09.r_whi rl_dstR] in Ha. exact (proj1 (HDbyte a ltac:(lia))).
    - apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi rl_srcR]; lia | apply awr_ok_nil]. }
  rename HF into HFa. rename HFr into HFra. rename HG into HGa.
  assert (U32a : bv_unsigned (ew _ 32) = D + n)
    by (rl_pull HS E32 Fa32; rewrite Fa32; unfold w64; apply unsigned_lit_small; lia).
  assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (D + n <= a < D + n + 1) ->
            aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem' a).
  { intros a Ha Hn. apply (aview_kept_out _ _ (w_H W) _ _ HFra a Ha).
    intros (r & Hin & Hr). cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [subst r|]); try destruct Hin;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val rl_dstR rl_srcR] in Hr; rewrite ?U32a in Hr; lia. }
  psrr_branch_tok RUN BR HS SHOK Bspan.
  {
    rl_pull HS E33 F33. rl_pull HS E32 F32. rl_pull HS E11 F11. rl_pull HS E12 F12.
    rl_pull HS E13 F13. rl_pull HS E10 F10. rl_pull HS E14 F14. rl_pull HS E20 F20. rl_pull HS E22 F22.
    match goal with H : branch_taken _ _ _ = _ |- _ => rename H into HB end.
    rewrite branch_ne_U in HB. rewrite (U_atom _ 33 c2 F33) in HB by lia. rewrite U_lit in HB by lia.
    apply negb_true_iff, Z.eqb_neq in HB.
    assert (Ht' : t' <> []) by (intros Hx; apply HB; apply Hc2nil; exact Hx).
    assert (U32' : bv_unsigned (ew _ 32) = D + n) by (rewrite F32; unfold w64; apply unsigned_lit_small; lia).
    paj_run_to_tok RUNTO HS HJ SHOK Bspan (AF_reac_box_name + RBN_L4).
    { eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32%nat (D + n)); [reflexivity | exact U32' | | ].
      - intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. exact (proj1 (HDbyte a ltac:(lia))).
      - apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil]. }
    rename HF into HFb. rename HFr into HFrb. rename HG into HGb.
    assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (D + n <= a < D + n + 1) ->
              aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) (ms_mem ms) a).
    { intros a Ha Hn. apply (aview_kept_out _ _ (w_H W) _ _ HFrb a Ha).
      intros (r & Hin & Hr). cbn [In] in Hin.
      repeat (destruct Hin as [Hin | Hin]; [subst r|]); try destruct Hin;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U32' in Hr; lia. }
    pose proof (st_ok_pi_region_nth _ _ _ 0%nat _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
    rl_pull HS E15 F15.
    pose proof (field_of_region _ (mrestrict (w_H W) (ms_mem ms0)) 32%nat (D + n) _ 0 1 0 1 0 1%N (SOff 15 0) c
      HR0 U32' ltac:(left; reflexivity)
      ltac:(cbn [sv_denot]; rewrite F15; unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
      ltac:(cbn; lia) ltac:(cbn; lia)) as HVAL.
    change (N.to_nat 1) with 1%nat in HVAL. rewrite Z.add_0_r in HVAL.
    pmkst HS.
    prreg HS (11%bv : bv 5) Rv11. prreg HS (12%bv : bv 5) Rv12. prreg HS (15%bv : bv 5) Rv15.
    prreg HS (13%bv : bv 5) Rv13. prreg HS (10%bv : bv 5) Rv10. prreg HS (14%bv : bv 5) Rv14.
    prreg HS (20%bv : bv 5) Rv20. prreg HS (22%bv : bv 5) Rv22.
    rewrite E11 in Rv11. rewrite E12 in Rv12. rewrite E33 in Rv15. rewrite E13 in Rv13.
    rewrite E10 in Rv10. rewrite E14 in Rv14. rewrite E20 in Rv20. rewrite E22 in Rv22.
    unfold w64 in Rv11, Rv12, Rv15, Rv13, Rv10, Rv14, Rv20, Rv22.
    rewrite unsigned_lit_small in Rv11 by lia. rewrite unsigned_lit_small in Rv13 by lia.
    rewrite unsigned_lit_small in Rv10 by lia.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs' [w64 (D + n); w64 c2] KEPT4 HS
      ltac:(env_agree_chain (EL_agree regs' (D + n) c2)) ltac:(vm_compute; reflexivity)) as HK2.
    cbn [ms_regs restrict] in HK2.
    pose proof (st_ok_pi_restrict_reg _ _ _ _ (Z_to_bv 5 0) HSe) as Z0a. cbn [ms_regs mkst] in Z0a.
    pose proof (st_ok_pi_restrict_reg _ _ _ _ (Z_to_bv 5 0) HS) as Z0b. cbn [ms_regs mkst] in Z0b.
    assert (HKP2 : rbn_keep_regs regs' (ms_regs ms0) [5; 10; 11; 12; 13; 15; 16; 17]).
    { apply (rl_keep_of _ _ KEPT4); [exact HK2 | rewrite Z0a, Z0b; vm_compute; reflexivity |].
      intros z Hz Hnc. unfold KEPT4.
      assert (Hd : z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/ z = 5 \/ z = 6 \/ z = 7 \/ z = 8 \/ z = 9
        \/ z = 10 \/ z = 11 \/ z = 12 \/ z = 13 \/ z = 14 \/ z = 15 \/ z = 16 \/ z = 17 \/ z = 18 \/ z = 19
        \/ z = 20 \/ z = 21 \/ z = 22 \/ z = 23 \/ z = 24 \/ z = 25 \/ z = 26 \/ z = 27 \/ z = 28 \/ z = 29
        \/ z = 30 \/ z = 31) by lia.
      repeat (destruct Hd as [Hd | Hd]); subst z;
      solve [ exfalso; apply Hnc; cbn [In]; repeat (first [left; reflexivity | right])
            | cbn [In]; repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]) ]. }
    change 15536 with (AF_reac_box_name + RBN_L4).
    assert (HgaQ : garr8 SEGS (mrestrict (w_H W) memc) (Q + 1) (t' ++ [0])).
    { intros j Hj.
      assert (Hj2 : (Datatypes.S j < length ((c :: t') ++ [0%Z]))%nat).
      { change ((c :: t') ++ [0%Z]) with (c :: (t' ++ [0%Z])). cbn [length]. lia. }
      destruct (Hga (Datatypes.S j) Hj2) as [Hv Hr].
      split; [|exact Hr]. replace (Q + 1 + Z.of_nat j) with (Q + Z.of_nat (Datatypes.S j)) by lia. exact Hv. }
    eapply (IH fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs D n0 (Q + 1) t'
      (ms_regs ms0) (ms_mem ms0) _ (n + 1) ov (wr ++ [c]) nF ovF wrF).
    - cbn [length] in Hm. lia.
    - rewrite HnF, HLn. lia.
    - rewrite HLn in HovF. replace (n + 1 + Z.of_nat (length t')) with (n + (Z.of_nat (length t') + 1)) by lia. exact HovF.
    - rewrite HwrF, <- app_assoc. f_equal.
      replace (Z.to_nat (47 - n)) with (Datatypes.S (Z.to_nat (47 - (n + 1)))) by lia. reflexivity.
    - exact Ht'.
    - exact Htb'.
    - exact HgaQ.
    - lia.
    - rewrite HLn in HQ47. lia.
    - apply (range_addressable_sub (aview SEGS (w_H W) memc) SHADOW_OFF Q (Z.of_nat (length (c :: t')) + 1));
        [exact Hra | lia | rewrite HLn; lia].
    - exact Hbuf.
    - rewrite HLn in Hdis. lia.
    - lia.
    - lia.
    - lia.
    - exact Hov.
    - rewrite length_app. cbn [length]. lia.
    - exact HJ.
    - eapply mem_grows_trans; [exact HMG | eapply mem_grows_trans; [exact HGa | exact HGb]].
    - intros a Ha Hn1. rewrite (KEEP2 a Ha ltac:(lia)), (KEEP1 a Ha ltac:(lia)). apply HF1; lia.
    - apply (garr8_app1 SEGS (mrestrict (w_H W) mem') (mrestrict (w_H W) (ms_mem ms0)) (D + n0) wr c Hgw).
      + rewrite Hwrl. replace (D + n0 + (n - n0)) with (D + n) by lia. exact HVAL.
      + lia.
      + intros a Ha. rewrite Hwrl in Ha. apply (mbyte_of_aview SEGS (w_H W) (w_H W)).
        rewrite (KEEP2 a ltac:(lia) ltac:(lia)). apply (KEEP1 a); lia.
    - unfold w64. exact Rv11.
    - unfold w64. exact Rv12.
    - unfold w64. rewrite <- (Hc2nz Ht'). exact Rv15.
    - unfold w64. replace (Q + 1 + 1) with (Q + 1 + 1) by lia. exact Rv13.
    - unfold w64. exact Rv10.
    - unfold w64. exact Rv14.
    - unfold w64. exact Rv20.
    - unfold w64. exact Rv22.
    - apply (rl_keep_trans regs regs' (ms_regs ms0)); [exact HKP | exact HKP2]. }
  {
    match goal with H : branch_taken _ _ _ = _ |- _ => rename H into HB end.
    rl_pull HS E33 F33. rl_pull HS E32 F32.
    rewrite branch_ne_U in HB. rewrite (U_atom _ 33 c2 F33) in HB by lia. rewrite U_lit in HB by lia.
    apply negb_false_iff, Z.eqb_eq in HB.
    assert (Ht'nil : t' = []) by (apply Hc2z; exact HB).
    assert (HwrE : wrF = wr ++ [c]).
    { rewrite HwrF, Ht'nil. f_equal.
      replace (Z.to_nat (47 - n)) with (Datatypes.S (Z.to_nat (47 - n - 1))) by lia.
      cbn [firstn]. rewrite firstn_nil. reflexivity. }
    assert (U32' : bv_unsigned (ew _ 32) = D + n) by (rewrite F32; unfold w64; apply unsigned_lit_small; lia).
    paj_run_to_tok RUNTO HS HJ SHOK Bspan (AF_reac_box_name + RBN_L4X).
    { eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32%nat (D + n)); [reflexivity | exact U32' | | ].
      - intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. exact (proj1 (HDbyte a ltac:(lia))).
      - apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil]. }
    rename HF into HFb. rename HFr into HFrb. rename HG into HGb.
    assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (D + n <= a < D + n + 1) ->
              aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) (ms_mem ms) a).
    { intros a Ha Hn1. apply (aview_kept_out _ _ (w_H W) _ _ HFrb a Ha).
      intros (r & Hin & Hr). cbn [In] in Hin.
      repeat (destruct Hin as [Hin | Hin]; [subst r|]); try destruct Hin;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U32' in Hr; lia. }
    pose proof (st_ok_pi_region_nth _ _ _ 0%nat _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
    rl_pull HS E15 F15.
    pose proof (field_of_region _ (mrestrict (w_H W) (ms_mem ms0)) 32%nat (D + n) _ 0 1 0 1 0 1%N (SOff 15 0) c
      HR0 U32' ltac:(left; reflexivity)
      ltac:(cbn [sv_denot]; rewrite F15; unfold w64; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
      ltac:(cbn; lia) ltac:(cbn; lia)) as HVAL.
    change (N.to_nat 1) with 1%nat in HVAL. rewrite Z.add_0_r in HVAL.
    pmkst HS.
    prreg HS (11%bv : bv 5) Rv11. prreg HS (12%bv : bv 5) Rv12.
    rewrite E11 in Rv11. rewrite E12 in Rv12. unfold w64 in Rv11, Rv12.
    rewrite unsigned_lit_small in Rv11 by lia.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs' [w64 (D + n); w64 c2] KEPT4 HS
      ltac:(env_agree_chain (EL_agree regs' (D + n) c2)) ltac:(vm_compute; reflexivity)) as HK2.
    cbn [ms_regs restrict] in HK2.
    pose proof (st_ok_pi_restrict_reg _ _ _ _ (Z_to_bv 5 0) HSe) as Z0a. cbn [ms_regs mkst] in Z0a.
    pose proof (st_ok_pi_restrict_reg _ _ _ _ (Z_to_bv 5 0) HS) as Z0b. cbn [ms_regs mkst] in Z0b.
    assert (HKP2 : rbn_keep_regs regs' (ms_regs ms0) [5; 10; 11; 12; 13; 15; 16; 17]).
    { apply (rl_keep_of _ _ KEPT4); [exact HK2 | rewrite Z0a, Z0b; vm_compute; reflexivity |].
      intros z Hz Hnc. unfold KEPT4.
      assert (Hd : z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/ z = 5 \/ z = 6 \/ z = 7 \/ z = 8 \/ z = 9
        \/ z = 10 \/ z = 11 \/ z = 12 \/ z = 13 \/ z = 14 \/ z = 15 \/ z = 16 \/ z = 17 \/ z = 18 \/ z = 19
        \/ z = 20 \/ z = 21 \/ z = 22 \/ z = 23 \/ z = 24 \/ z = 25 \/ z = 26 \/ z = 27 \/ z = 28 \/ z = 29
        \/ z = 30 \/ z = 31) by lia.
      repeat (destruct Hd as [Hd | Hd]); subst z;
      solve [ exfalso; apply Hnc; cbn [In]; repeat (first [left; reflexivity | right])
            | cbn [In]; repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]) ]. }
    assert (HnFe : nF = n + 1) by (rewrite HnF, Ht'nil; cbn [length]; lia).
    assert (HovFe : ovF = ov).
    { rewrite HovF, Ht'nil. cbn [length].
      replace (n + Z.of_nat 1 <=? 47) with true by (symmetry; apply Z.leb_le; cbn [Z.of_nat]; lia).
      reflexivity. }
    apply SRr_ret. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst ?rg _ ?mm _) ?mdx] => exists rg, mm, mdx end.
    split.
    { unfold cfg_at, w64. rewrite <- Z.add_assoc. change (AF_reac_box_name + RBN_L4X) with 15644. reflexivity. }
    split; [exact HJ|].
    split; [apply (rl_keep_trans regs regs' (ms_regs ms0)); [exact HKP | exact HKP2]|].
    split.
    { apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
      - rewrite HnFe. unfold w64. exact Rv11.
      - rewrite HovFe. unfold w64. exact Rv12. }
    split.
    { intros a Ha Hn1.
      assert (HlenF : Z.of_nat (length wrF) = n + 1 - n0) by (rewrite HwrE, length_app; cbn [length]; lia).
      rewrite HlenF in Hn1.
      rewrite (KEEP2 a Ha ltac:(lia)), (KEEP1 a Ha ltac:(lia)). apply HF1; lia. }
    rewrite HwrE.
    apply (garr8_app1 SEGS (mrestrict (w_H W) mem') (mrestrict (w_H W) (ms_mem ms0)) (D + n0) wr c Hgw).
    - rewrite Hwrl. replace (D + n0 + (n - n0)) with (D + n) by lia. exact HVAL.
    - lia.
    - intros a Ha. rewrite Hwrl in Ha. apply (mbyte_of_aview SEGS (w_H W) (w_H W)).
      rewrite (KEEP2 a ltac:(lia) ltac:(lia)). apply (KEEP1 a); lia. } }
{
  assert (Hne : n = 47) by lia.
  assert (H11' : getr regs' 11 = w64 47) by (rewrite H11, Hne; reflexivity).
  set (E := EL regs' (D + 47) c2).
  assert (HEI : img_env VAL A_LIM E) by apply EL_img.
  assert (E33 : ew E 33 = w64 c2) by apply EL_33.
  assert (E11 : ew E 11 = w64 47)
    by (unfold E; rewrite (EL_reg regs' _ _ 11%nat 11%bv) by (first [lia | vm_compute; reflexivity]); exact H11').
  assert (E12 : ew E 12 = w64 ov)
    by (unfold E; rewrite (EL_reg regs' _ _ 12%nat 12%bv) by (first [lia | vm_compute; reflexivity]); exact H12).
  assert (E15 : ew E 15 = w64 c)
    by (unfold E; rewrite (EL_reg regs' _ _ 15%nat 15%bv) by (first [lia | vm_compute; reflexivity]); exact H15).
  assert (E13 : ew E 13 = w64 (Q + 1))
    by (unfold E; rewrite (EL_reg regs' _ _ 13%nat 13%bv) by (first [lia | vm_compute; reflexivity]); exact H13).
  assert (E10 : ew E 10 = w64 (Q + 1))
    by (unfold E; rewrite (EL_reg regs' _ _ 10%nat 10%bv) by (first [lia | vm_compute; reflexivity]); exact H10).
  assert (E14 : ew E 14 = w64 47)
    by (unfold E; rewrite (EL_reg regs' _ _ 14%nat 14%bv) by (first [lia | vm_compute; reflexivity]); exact H14).
  assert (E20 : ew E 20 = w64 D)
    by (unfold E; rewrite (EL_reg regs' _ _ 20%nat 20%bv) by (first [lia | vm_compute; reflexivity]); exact H20).
  assert (E22 : ew E 22 = w64 SHADOW_OFF)
    by (unfold E; rewrite (EL_reg regs' _ _ 22%nat 22%bv) by (first [lia | vm_compute; reflexivity]); exact H22).
  assert (HS : st_ok_pi SEGS VAL E l4_sso
    (restrict (w_H W) (mkst (fx := fq) regs' (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L4))) mem' (seg_rom SEGS)))).
  { unfold E. apply (l4_entry_o fq W regs' mem' D ov c c2 Q); try assumption; try lia. }
  pose proof HS as HSe.
  assert (SHOK : sh_ok SEGS rl_Bx (@nil shent) E (mrestrict (w_H W) mem')) by (apply Forall_nil).
  paj_run_tok RUN HS HJ SHOK Bspan.
  { unfold rl_Bx. rewrite (U_atom E 22 SHADOW_OFF E22) by (unfold SHADOW_OFF; lia).
    rewrite (U_atom E 10 (Q + 1) E10) by lia.
    rewrite <- (aview_rd_of SEGS). exact HRAQ. }
  { apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi rl_srcR]; lia | apply awr_ok_nil]. }
  rename HF into HFa. rename HFr into HFra. rename HG into HGa.
  assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem' a).
  { intros a Ha. apply (aview_kept_out _ _ (w_H W) _ _ HFra a Ha).
    intros (r & Hin & Hr). cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [subst r|]); try destruct Hin;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val rl_srcR] in Hr; lia. }
  psrr_branch_tok RUN BR HS SHOK Bspan.
  {
    match goal with H : branch_taken _ _ _ = _ |- _ => rename H into HB end.
    rl_pull HS E33 F33. rl_pull HS E11 F11. rl_pull HS E12 F12.
    rl_pull HS E13 F13. rl_pull HS E10 F10. rl_pull HS E14 F14. rl_pull HS E20 F20. rl_pull HS E22 F22.
    rewrite branch_ne_U in HB. rewrite (U_atom _ 33 c2 F33) in HB by lia. rewrite U_lit in HB by lia.
    apply negb_true_iff, Z.eqb_neq in HB.
    assert (Ht' : t' <> []) by (intros Hx; apply HB; apply Hc2nil; exact Hx).
    paj_run_to_tok RUNTO HS HJ SHOK Bspan (AF_reac_box_name + RBN_L4).
    { apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil]. }
    rename HF into HFb. rename HFr into HFrb. rename HG into HGb.
    assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) (ms_mem ms) a).
    { intros a Ha. apply (aview_kept_out _ _ (w_H W) _ _ HFrb a Ha).
      intros (r & Hin & Hr). cbn [In] in Hin.
      repeat (destruct Hin as [Hin | Hin]; [subst r|]); try destruct Hin;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia. }
    pmkst HS.
    prreg HS (11%bv : bv 5) Rv11. prreg HS (12%bv : bv 5) Rv12. prreg HS (15%bv : bv 5) Rv15.
    prreg HS (13%bv : bv 5) Rv13. prreg HS (10%bv : bv 5) Rv10. prreg HS (14%bv : bv 5) Rv14.
    prreg HS (20%bv : bv 5) Rv20. prreg HS (22%bv : bv 5) Rv22.
    rewrite E11 in Rv11. rewrite E33 in Rv15. rewrite E13 in Rv13.
    rewrite E10 in Rv10. rewrite E14 in Rv14. rewrite E20 in Rv20. rewrite E22 in Rv22.
    unfold w64 in Rv11, Rv12, Rv15, Rv13, Rv10, Rv14, Rv20, Rv22.
    rewrite unsigned_lit_small in Rv13 by lia. rewrite unsigned_lit_small in Rv10 by lia.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs' [w64 (D + 47); w64 c2] KEPT4 HS
      ltac:(env_agree_chain (EL_agree regs' (D + 47) c2)) ltac:(vm_compute; reflexivity)) as HK2.
    cbn [ms_regs restrict] in HK2.
    pose proof (st_ok_pi_restrict_reg _ _ _ _ (Z_to_bv 5 0) HSe) as Z0a. cbn [ms_regs mkst] in Z0a.
    pose proof (st_ok_pi_restrict_reg _ _ _ _ (Z_to_bv 5 0) HS) as Z0b. cbn [ms_regs mkst] in Z0b.
    assert (HKP2 : rbn_keep_regs regs' (ms_regs ms0) [5; 10; 11; 12; 13; 15; 16; 17]).
    { apply (rl_keep_of _ _ KEPT4); [exact HK2 | rewrite Z0a, Z0b; vm_compute; reflexivity |].
      intros z Hz Hnc. unfold KEPT4.
      assert (Hd : z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/ z = 5 \/ z = 6 \/ z = 7 \/ z = 8 \/ z = 9
        \/ z = 10 \/ z = 11 \/ z = 12 \/ z = 13 \/ z = 14 \/ z = 15 \/ z = 16 \/ z = 17 \/ z = 18 \/ z = 19
        \/ z = 20 \/ z = 21 \/ z = 22 \/ z = 23 \/ z = 24 \/ z = 25 \/ z = 26 \/ z = 27 \/ z = 28 \/ z = 29
        \/ z = 30 \/ z = 31) by lia.
      repeat (destruct Hd as [Hd | Hd]); subst z;
      solve [ exfalso; apply Hnc; cbn [In]; repeat (first [left; reflexivity | right])
            | cbn [In]; repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]) ]. }
    change 15536 with (AF_reac_box_name + RBN_L4).
    assert (HgaQ : garr8 SEGS (mrestrict (w_H W) memc) (Q + 1) (t' ++ [0])).
    { intros j Hj.
      assert (Hj2 : (Datatypes.S j < length ((c :: t') ++ [0%Z]))%nat).
      { change ((c :: t') ++ [0%Z]) with (c :: (t' ++ [0%Z])). cbn [length]. lia. }
      destruct (Hga (Datatypes.S j) Hj2) as [Hv Hr].
      split; [|exact Hr]. replace (Q + 1 + Z.of_nat j) with (Q + Z.of_nat (Datatypes.S j)) by lia. exact Hv. }
    eapply (IH fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs D n0 (Q + 1) t'
      (ms_regs ms0) (ms_mem ms0) _ n 1 wr nF ovF wrF).
    - cbn [length] in Hm. lia.
    - rewrite HnF, HLn. lia.
    - rewrite HovF, HLn.
      replace (n + (Z.of_nat (length t') + 1) <=? 47) with false by (symmetry; apply Z.leb_gt; lia).
      destruct (n + Z.of_nat (length t') <=? 47); reflexivity.
    - rewrite HwrF. replace (Z.to_nat (47 - n)) with 0%nat by lia. reflexivity.
    - exact Ht'.
    - exact Htb'.
    - exact HgaQ.
    - lia.
    - rewrite HLn in HQ47. lia.
    - apply (range_addressable_sub (aview SEGS (w_H W) memc) SHADOW_OFF Q (Z.of_nat (length (c :: t')) + 1));
        [exact Hra | lia | rewrite HLn; lia].
    - exact Hbuf.
    - rewrite HLn in Hdis. lia.
    - lia.
    - lia.
    - lia.
    - right; reflexivity.
    - exact Hwrl.
    - exact HJ.
    - eapply mem_grows_trans; [exact HMG | eapply mem_grows_trans; [exact HGa | exact HGb]].
    - intros a Ha Hn1. rewrite (KEEP2 a Ha), (KEEP1 a Ha). apply HF1; lia.
    - apply (rl_garr8_kept (w_H W) mem' (ms_mem ms0) (D + n0) wr);
        [intros a Ha; rewrite (KEEP2 a ltac:(lia)); apply (KEEP1 a); lia | exact Hgw].
    - unfold w64. rewrite Hne. exact Rv11.
    - unfold w64. exact Rv12.
    - unfold w64. rewrite <- (Hc2nz Ht'). exact Rv15.
    - unfold w64. exact Rv13.
    - unfold w64. exact Rv10.
    - unfold w64. exact Rv14.
    - unfold w64. exact Rv20.
    - unfold w64. exact Rv22.
    - apply (rl_keep_trans regs regs' (ms_regs ms0)); [exact HKP | exact HKP2]. }
  {
    match goal with H : branch_taken _ _ _ = _ |- _ => rename H into HB end.
    rl_pull HS E33 F33.
    rewrite branch_ne_U in HB. rewrite (U_atom _ 33 c2 F33) in HB by lia. rewrite U_lit in HB by lia.
    apply negb_false_iff, Z.eqb_eq in HB.
    assert (Ht'nil : t' = []) by (apply Hc2z; exact HB).
    assert (HwrE : wrF = wr) by (rewrite HwrF; replace (Z.to_nat (47 - n)) with 0%nat by lia;
      cbn [firstn]; rewrite app_nil_r; reflexivity).
    paj_run_to_tok RUNTO HS HJ SHOK Bspan (AF_reac_box_name + RBN_L4X).
    { apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil]. }
    rename HF into HFb. rename HFr into HFrb. rename HG into HGb.
    assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) (ms_mem ms) a).
    { intros a Ha. apply (aview_kept_out _ _ (w_H W) _ _ HFrb a Ha).
      intros (r & Hin & Hr). cbn [In] in Hin.
      repeat (destruct Hin as [Hin | Hin]; [subst r|]); try destruct Hin;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia. }
    pmkst HS.
    prreg HS (11%bv : bv 5) Rv11. prreg HS (12%bv : bv 5) Rv12.
    rewrite E11 in Rv11. unfold w64 in Rv11, Rv12.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs' [w64 (D + 47); w64 c2] KEPT4 HS
      ltac:(env_agree_chain (EL_agree regs' (D + 47) c2)) ltac:(vm_compute; reflexivity)) as HK2.
    cbn [ms_regs restrict] in HK2.
    pose proof (st_ok_pi_restrict_reg _ _ _ _ (Z_to_bv 5 0) HSe) as Z0a. cbn [ms_regs mkst] in Z0a.
    pose proof (st_ok_pi_restrict_reg _ _ _ _ (Z_to_bv 5 0) HS) as Z0b. cbn [ms_regs mkst] in Z0b.
    assert (HKP2 : rbn_keep_regs regs' (ms_regs ms0) [5; 10; 11; 12; 13; 15; 16; 17]).
    { apply (rl_keep_of _ _ KEPT4); [exact HK2 | rewrite Z0a, Z0b; vm_compute; reflexivity |].
      intros z Hz Hnc. unfold KEPT4.
      assert (Hd : z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/ z = 5 \/ z = 6 \/ z = 7 \/ z = 8 \/ z = 9
        \/ z = 10 \/ z = 11 \/ z = 12 \/ z = 13 \/ z = 14 \/ z = 15 \/ z = 16 \/ z = 17 \/ z = 18 \/ z = 19
        \/ z = 20 \/ z = 21 \/ z = 22 \/ z = 23 \/ z = 24 \/ z = 25 \/ z = 26 \/ z = 27 \/ z = 28 \/ z = 29
        \/ z = 30 \/ z = 31) by lia.
      repeat (destruct Hd as [Hd | Hd]); subst z;
      solve [ exfalso; apply Hnc; cbn [In]; repeat (first [left; reflexivity | right])
            | cbn [In]; repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]) ]. }
    assert (HnFe : nF = 47) by (rewrite HnF, HLn; lia).
    assert (HovFe : ovF = 1)
      by (rewrite HovF, HLn; replace (n + (Z.of_nat (length t') + 1) <=? 47) with false
            by (symmetry; apply Z.leb_gt; lia); reflexivity).
    apply SRr_ret. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst ?rg _ ?mm _) ?mdx] => exists rg, mm, mdx end.
    split.
    { unfold cfg_at, w64. rewrite <- Z.add_assoc. change (AF_reac_box_name + RBN_L4X) with 15644. reflexivity. }
    split; [exact HJ|].
    split; [apply (rl_keep_trans regs regs' (ms_regs ms0)); [exact HKP | exact HKP2]|].
    split.
    { apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
      - rewrite HnFe. unfold w64. exact Rv11.
      - rewrite HovFe. unfold w64. exact Rv12. }
    split.
    { intros a Ha Hn1. rewrite (KEEP2 a Ha), (KEEP1 a Ha). apply HF1; [lia|].
      rewrite HwrE in Hn1. lia. }
    rewrite HwrE.
    apply (rl_garr8_kept (w_H W) mem' (ms_mem ms0) (D + n0) wr);
      [intros a Ha; rewrite (KEEP2 a ltac:(lia)); apply (KEEP1 a); lia | exact Hgw]. } }
Qed.
Theorem rbn_l4_fits : rbn_L4_fits B.
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s Hlen.
unfold rbn_L4_run. intros HJ Hs0 Hsb Hsrc Hbuf Hdis Hn0 Hov H11 H12 H15 H13 H10 H14 H20 H22.
unfold rbn_lsrc in Hsrc.
pose proof (proj1 Hsrc) as Hga. pose proof (proj1 (proj2 Hsrc)) as HP0.
pose proof (proj1 (proj2 (proj2 Hsrc))) as HP63. pose proof (proj1 (proj2 (proj2 (proj2 Hsrc)))) as HP47.
pose proof (proj2 (proj2 (proj2 (proj2 Hsrc)))) as Hra.
rewrite length_app in HP63, HP47, Hra. cbn [length] in HP63, HP47, Hra.
replace (Z.of_nat (length s + 1)) with (Z.of_nat (length s) + 1) in HP63, HP47, Hra by lia.
change (cfg_at (fx := fq) SEGS (BASE + AF_reac_box_name + RBN_L4) regs memc mdc)
  with (mkCfg (mkst (fx := fq) regs (Z_to_bv 64 (BASE + AF_reac_box_name + RBN_L4)) memc (seg_rom SEGS)) mdc).
rewrite <- Z.add_assoc.
eapply (rbn_l4_core (length s) fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs D n0 P s regs memc mdc
  n0 ov0 [] (n0 + Z.of_nat (length s)) ov0 s).
- lia.
- lia.
- replace (n0 + Z.of_nat (length s) <=? 47) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
- cbn [app]. symmetry. apply firstn_all2. lia.
- exact Hs0.
- exact Hsb.
- exact Hga.
- exact HP0.
- lia.
- exact Hra.
- exact Hbuf.
- exact Hdis.
- lia.
- lia.
- lia.
- exact Hov.
- cbn [length]. lia.
- exact HJ.
- apply mem_grows_refl.
- intros a Ha Hn. reflexivity.
- apply garr8_nil.
- exact H11.
- exact H12.
- exact H15.
- exact H13.
- exact H10.
- exact H14.
- exact H20.
- exact H22.
- intros z Hz Hnc. reflexivity.
Qed.
Theorem rbn_l4_ovf : rbn_L4_ovf B.
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s Hlen.
unfold rbn_L4_run. intros HJ Hs0 Hsb Hsrc Hbuf Hdis Hn0 Hov H11 H12 H15 H13 H10 H14 H20 H22.
unfold rbn_lsrc in Hsrc.
pose proof (proj1 Hsrc) as Hga. pose proof (proj1 (proj2 Hsrc)) as HP0.
pose proof (proj1 (proj2 (proj2 Hsrc))) as HP63. pose proof (proj1 (proj2 (proj2 (proj2 Hsrc)))) as HP47.
pose proof (proj2 (proj2 (proj2 (proj2 Hsrc)))) as Hra.
rewrite length_app in HP63, HP47, Hra. cbn [length] in HP63, HP47, Hra.
replace (Z.of_nat (length s + 1)) with (Z.of_nat (length s) + 1) in HP63, HP47, Hra by lia.
change (cfg_at (fx := fq) SEGS (BASE + AF_reac_box_name + RBN_L4) regs memc mdc)
  with (mkCfg (mkst (fx := fq) regs (Z_to_bv 64 (BASE + AF_reac_box_name + RBN_L4)) memc (seg_rom SEGS)) mdc).
rewrite <- Z.add_assoc.
eapply (rbn_l4_core (length s) fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs D n0 P s regs memc mdc
  n0 ov0 [] 47 1 (firstn (Z.to_nat (47 - n0)) s)).
- lia.
- lia.
- replace (n0 + Z.of_nat (length s) <=? 47) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
- cbn [app]. reflexivity.
- exact Hs0.
- exact Hsb.
- exact Hga.
- exact HP0.
- lia.
- exact Hra.
- exact Hbuf.
- exact Hdis.
- lia.
- lia.
- lia.
- exact Hov.
- cbn [length]. lia.
- exact HJ.
- apply mem_grows_refl.
- intros a Ha Hn. reflexivity.
- apply garr8_nil.
- exact H11.
- exact H12.
- exact H15.
- exact H13.
- exact H10.
- exact H14.
- exact H20.
- exact H22.
- intros z Hz Hnc. reflexivity.
Qed.
End h.
End f.
End d.
