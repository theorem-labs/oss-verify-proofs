(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbd.v:102-108, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_L4.v, with its module paths, module names and numbers changed; 780 of its 858 lines of code are new or changed and 742 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC8i YC1f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q YG0s YC1g YC4b YC44.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YC81 YC85 YC88 YCjr YCj1 YXcalls YK0e.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import SbCh ReacBoxNameLoops.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac rl_pull HS H0 Hout :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ex _ _ =>
    lazymatch type of H0 with
    | ew _ ?q = ?v => assert (Hout : ew Ex q = v) by (cbn [ew ewset Nat.eqb]; exact H0)
    end
  | st_ok _ ?Ex _ _ =>
    lazymatch type of H0 with
    | ew _ ?q = ?v => assert (Hout : ew Ex q = v) by (cbn [ew ewset Nat.eqb]; exact H0)
    end
  end.
Ltac l1_ro_regs :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbn in Hr; repeat (destruct Hr as [<- | Hr]; [cbn; lia|]); try destruct Hr.
Open Scope bv_scope.
Open Scope Z_scope.
Definition l1_kept_regs : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 27]%bv.
Lemma l1_getr0 : forall (r1 r2 : bvmap 5 word), getr r2 (Z_to_bv 5 0) = getr r1 (Z_to_bv 5 0).
Proof.
intros r1 r2. assert (E : (Z_to_bv 5 0 : bv 5) = 0%bv) by (apply bv_eq; vm_compute; reflexivity).
rewrite E, !getr_zero. reflexivity.
Qed.
Lemma l1_keep_of : forall (r1 r2 : bvmap 5 word) (l : list (bv 5)) (cl : list Z),
  (forall r : bv 5, In r l -> getr r2 r = getr r1 r) ->
  (forall z, 0 < z < 32 -> ~ In z cl -> In (Z_to_bv 5 z) l) ->
  rbn_keep_regs r1 r2 cl.
Proof.
intros r1 r2 l cl Hk Hin z Hz Hnc.
destruct (Z.eq_dec z 0) as [-> | Hz0]; [apply l1_getr0 | apply Hk; apply Hin; [lia | exact Hnc]].
Qed.
Lemma l1_keep_trans : forall (r1 r2 r3 : bvmap 5 word) cl,
  rbn_keep_regs r1 r2 cl -> rbn_keep_regs r2 r3 cl -> rbn_keep_regs r1 r3 cl.
Proof. intros r1 r2 r3 cl H1 H2 z Hz Hn. rewrite (H2 z Hz Hn). exact (H1 z Hz Hn). Qed.
Lemma l1_keep_cl1 : forall (r1 r2 : bvmap 5 word),
  (forall r : bv 5, In r l1_kept_regs -> getr r2 r = getr r1 r) -> rbn_keep_regs r1 r2 rbn_cl1.
Proof.
intros r1 r2 Hk. apply (l1_keep_of r1 r2 l1_kept_regs); [exact Hk|].
intros z Hz Hnc. unfold rbn_cl1, rbn_clc in Hnc. cbn [app In] in Hnc. unfold l1_kept_regs.
assert (Hd : z = 2 \/ z = 3 \/ z = 4 \/ z = 8 \/ z = 9 \/ z = 18 \/ z = 19 \/ z = 20 \/ z = 22 \/ z = 23
  \/ z = 24 \/ z = 25 \/ z = 27) by lia.
repeat (destruct Hd as [Hd | Hd]); subst z; cbn [In];
repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]).
Qed.
Lemma l1_keep_pres : forall (r1 r2 : bvmap 5 word), aregs_preserved r1 r2 -> rbn_keep_regs r1 r2 rbn_cl1.
Proof.
intros r1 r2 HP z Hz Hnc. destruct (Z.eq_dec z 0) as [-> | H0]; [apply l1_getr0|].
apply HP. unfold rbn_cl1, rbn_clc in Hnc. cbn [app In] in Hnc. unfold acallee_saved. lia.
Qed.
Lemma l1_and255 : forall (x : word) c, x = w64 c -> 0 <= c < 256 -> alu64 ALU_AND x (Z_to_bv 64 255) = w64 c.
Proof.
intros x c -> Hc. apply bv_eq. rewrite AX2S.u_and64. unfold w64.
rewrite !unsigned_lit_small by lia. rewrite land255_small by lia. reflexivity.
Qed.
Lemma l1_soa : forall x, shadow_of_addr SHADOW_OFF x = shadow_addr x.
Proof. intros x. reflexivity. Qed.
Lemma l1_band : forall x, 0 <= x -> x < 2 ^ 47 -> SHADOW_OFF <= shadow_addr x < kHighMemBeg.
Proof.
intros x H0 H47. unfold shadow_addr, SHADOW_OFF, kHighMemBeg.
assert (x / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
assert (0 <= x / 8) by (apply Z.div_pos; lia). lia.
Qed.
Lemma l1_hull_rng : forall a n s, 0 <= a -> 0 < n -> a + n <= 2 ^ 47 - 1 ->
  shadow_addr a / 8 * 8 <= s < shadow_addr (a + n - 1) / 8 * 8 + 8 ->
  SHADOW_OFF - 4096 <= s < kHighMemBeg.
Proof.
intros a n s Ha Hn Han Hs.
destruct (l1_band a Ha ltac:(lia)) as [B1 B2].
destruct (l1_band (a + n - 1) ltac:(lia) ltac:(lia)) as [C1 C2].
unfold SHADOW_OFF, kHighMemBeg in *. lia.
Qed.
Lemma l1_hsub : forall (rd : reader) a n a' n',
  shadow_hull_vis rd a n -> a <= a' -> 0 < n' -> a' + n' <= a + n -> shadow_hull_vis rd a' n'.
Proof.
intros rd a n a' n' Hh Ha Hn' Hle s Hs. apply Hh.
pose proof (shadow_mono a a' Ha) as M1. pose proof (shadow_mono (a' + n' - 1) (a + n - 1) ltac:(lia)) as M2. lia.
Qed.
Lemma l1_rak : forall (rd rd' : reader) a n,
  (forall x, a <= x < a + n -> rd' (shadow_addr x) = rd (shadow_addr x)) ->
  range_addressable rd SHADOW_OFF a n -> range_addressable rd' SHADOW_OFF a n.
Proof.
intros rd rd' a n He Hra x Hx. destruct (Hra x Hx) as (sv & Hs & Hok).
exists sv. split; [|exact Hok]. rewrite l1_soa in *. rewrite (He x Hx). exact Hs.
Qed.
Lemma l1_hk : forall (rd rd' : reader) a n,
  (forall s, shadow_addr a / 8 * 8 <= s < shadow_addr (a + n - 1) / 8 * 8 + 8 -> rd' s = rd s) ->
  shadow_hull_vis rd a n -> shadow_hull_vis rd' a n.
Proof. intros rd rd' a n He Hh s Hs. rewrite (He s Hs). exact (Hh s Hs). Qed.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Lemma l1_avoid : forall R D n0 len sp s,
  alloc_ceiling <= R -> in_app D 24 -> alloc_ceiling <= sp - TSB_CH_STK ->
  0 <= n0 -> 0 <= len -> n0 + len <= 24 ->
  SHADOW_OFF - 4096 <= s < kHighMemBeg ->
  0 <= s < 2 ^ 64 /\ ~ (R + 16 <= s < R + 28) /\ ~ (D + n0 <= s < D + n0 + len) /\
  ~ (sp - TSB_CH_STK <= s < sp).
Proof.
intros R D n0 len sp s HR HD Hsp Hn0 Hlen Hnl Hs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HD as (HD4096 & HDc).
unfold SHADOW_OFF, kHighMemBeg, kLowShadowBeg, YG0f.ASAN_CEIL in *.
destruct HDc as [HL | [HH1 HH2]]; repeat split; lia.
Qed.
Lemma l1_vk : forall (H1 H2 : word -> bool) m1 m2 a (nn : nat) v,
  (forall x, a <= x < a + Z.of_nat nn -> aview SEGS H2 m2 x = aview SEGS H1 m1 x) ->
  val_mem SEGS (mrestrict H1 m1) a nn v -> val_mem SEGS (mrestrict H2 m2) a nn v.
Proof. intros H1 H2 m1 m2 a nn v He Hv. apply (val_mem_kept SEGS H1 H2 m1 m2 a nn v); [intros kk Hk; apply He; lia | exact Hv]. Qed.
Lemma l1_gk : forall (H1 H2 : word -> bool) m1 m2 p L,
  (forall x, p <= x < p + Z.of_nat (length L) -> aview SEGS H2 m2 x = aview SEGS H1 m1 x) ->
  garr8 SEGS (mrestrict H1 m1) p L -> garr8 SEGS (mrestrict H2 m2) p L.
Proof. intros H1 H2 m1 m2 p L He Hg. exact (garr8_aview_kept SEGS H1 H2 m1 m2 p L He Hg). Qed.
Definition EY (regs : bvmap 5 word) (xs : list Z) : env := Eimg (Ereg regs (map w64 xs)).
Lemma EY_img : forall regs xs, img_env VAL A_LIM (EY regs xs).
Proof. intros. unfold EY. apply Eimg_env. Qed.
Lemma EY_reg : forall regs xs n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew (EY regs xs) n = getr regs r.
Proof. intros regs xs n r Hn Hr. unfold EY. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hr. Qed.
Lemma EY_32 : forall regs x xs, ew (EY regs (x :: xs)) 32 = w64 x.
Proof. intros. unfold EY. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma EY_agree : forall regs xs, env_agree 32 (Ereg regs (map w64 xs)) (EY regs xs).
Proof. intros. split; [intros q Hq; unfold EY; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
Lemma l1_afact : forall E q v lo hi, ew E q = w64 v -> 0 <= v < 2 ^ 64 -> lo <= v -> v <= hi -> afact_ok E q (mkAF lo hi 0).
Proof.
intros E q v lo hi He Hv Hlo Hhi. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite He. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r.
split; [lia|]. split; [reflexivity | lia].
Qed.
Definition l1_ssA : sstate := mkSS (AF_both3_reac_box_name + RBN_L1) sr_atoms [] None (mkFacts [] [] []).
Definition l1_srcB : YP09.region := YP09.mkRegion (Some 21%nat) 1 2 0 0 [YP09.mkChunk 1 (CVal 1 (SOff 32 0))].
Definition l1_ffB : facts := mkFacts
  [(22%nat, mkAF SB SB 0); (21%nat, mkAF 0 (2 ^ 47 - 2) 0); (24%nat, mkAF (2 ^ 64 - 1) (2 ^ 64 - 1) 0);
   (32%nat, mkAF 0 255 0)] [] [].
Definition l1_ssB0 : sstate := mkSS (AF_both3_reac_box_name + 800) sr_atoms [l1_srcB] None l1_ffB.
Definition l1_ssB : sstate := mkSS (AF_both3_reac_box_name + 800) (sr_set sr_atoms 26%bv (SOff 21 1)) [l1_srcB] None l1_ffB.
Lemma l1_pre_entry : forall (fq : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) mem,
  st_ok_pi SEGS VAL (EY regs []) l1_ssA
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_L1))) mem (seg_rom SEGS))).
Proof.
intros fq W regs mem. rewrite restrict_mkst_fx. unfold l1_ssA. apply pa_entry_st_ok_full.
- unfold EY. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- cbn. exact I.
- split; [exact I | split; exact I].
Qed.
Lemma l1_post_entry : forall (fq : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) mem (Q c2 : Z),
  0 <= Q -> Q + 2 <= 2 ^ 47 -> 0 <= c2 < 256 ->
  getr regs 21 = w64 Q -> getr regs 26 = w64 (Q + 1) -> getr regs 24 = w64 (-1) -> getr regs 22 = w64 SHADOW_OFF ->
  val_mem SEGS (mrestrict (w_H W) mem) (Q + 1) 1 c2 ->
  st_ok_pi SEGS VAL (EY regs [c2]) l1_ssB
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + 800))) mem (seg_rom SEGS))).
Proof.
intros fq W regs mem Q c2 HQ0 HQ47 Hc2 H21 H26 H24 H22 Hmem.
assert (E32 : ew (EY regs [c2]) 32 = w64 c2) by apply EY_32.
assert (E21 : ew (EY regs [c2]) 21 = w64 Q) by (rewrite (EY_reg regs _ 21%nat 21%bv) by (first [lia | vm_compute; reflexivity]); exact H21).
assert (E24 : ew (EY regs [c2]) 24 = w64 (2 ^ 64 - 1))
  by (rewrite (EY_reg regs _ 24%nat 24%bv) by (first [lia | vm_compute; reflexivity]); rewrite H24; apply bv_eq; reflexivity).
assert (E22 : ew (EY regs [c2]) 22 = w64 SHADOW_OFF)
  by (rewrite (EY_reg regs _ 22%nat 22%bv) by (first [lia | vm_compute; reflexivity]); exact H22).
assert (U21 : bv_unsigned (ew (EY regs [c2]) 21) = Q) by (rewrite E21; unfold w64; apply unsigned_lit_small; lia).
assert (HS0 : st_ok_pi SEGS VAL (EY regs [c2]) l1_ssB0
  (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + 800))) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold l1_ssB0, l1_ffB. apply pa_entry_st_ok_full.
  - unfold EY. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold l1_srcB, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U21. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS _ _ Q 1 1 (SOff 32 0) c2);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    change (N.to_nat 1) with 1%nat. exact Hmem.
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - split; [|split; exact I].
    cbn [f_atoms atoms_ok].
    split; [apply (l1_afact _ _ SHADOW_OFF); [exact E22 | unfold SHADOW_OFF; lia | unfold SB, SHADOW_OFF; lia | unfold SB, SHADOW_OFF; lia]|].
    split; [apply (l1_afact _ _ Q); [exact E21 | lia | lia | lia]|].
    split; [apply (l1_afact _ _ (2 ^ 64 - 1)); [exact E24 | lia | lia | lia]|].
    split; [apply (l1_afact _ _ c2); [exact E32 | lia | lia | lia]|]. exact I. }
apply (ast_ok_pi_set_reg_fp _ _ _ 26%bv (SOff 21 1)) in HS0; [exact HS0 | reflexivity |].
cbn [sv_denot ms_regs restrict mkst]. rewrite E21. unfold w64. rewrite unsigned_lit_small by lia. rewrite H26. reflexivity.
Qed.
Lemma l1_lyF : forall nsecs ly ly1 ly2, layout_le nsecs ly ly1 -> layout_le nsecs ly ly2 ->
  forall c p, frame_addr ly1 c p = frame_addr ly2 c p.
Proof.
intros nsecs ly ly1 ly2 H1 H2 c p. unfold frame_addr.
destruct H1 as (_ & _ & _ & _ & _ & E1 & _). destruct H2 as (_ & _ & _ & _ & _ & E2 & _).
rewrite E1, E2. reflexivity.
Qed.
Lemma l1_awr_ly : forall STK sp0 FP bl0 blc blc' ly1 ly2 own a,
  blc' = blc -> (forall c p, frame_addr ly2 c p = frame_addr ly1 c p) ->
  awr_byte STK sp0 FP bl0 blc ly1 own a -> awr_byte STK sp0 FP bl0 blc' ly2 own a.
Proof.
intros STK sp0 FP bl0 blc blc' ly1 ly2 own a -> Hfa H.
unfold awr_byte, in_frames in *. destruct H as [H | [H | [H | H]]]; [left | right;left | right;right;left | right;right;right]; try exact H.
destruct H as (cid & pos & Hin & Hz). exists cid, pos. split; [exact Hin|]. rewrite !(Hfa cid pos). exact Hz.
Qed.
Lemma l1_callee1 : forall (r1 r2 : bvmap 5 word) (z : Z) (r : bv 5),
  aregs_preserved r1 r2 -> acallee_saved z -> Z_to_bv 5 z = r -> getr r2 r = getr r1 r.
Proof. intros r1 r2 z r HP Hc <-. exact (HP z Hc). Qed.
Lemma l1_aview_ro : forall E (H : word -> bool) (m m' : word -> option byte) rs,
  (forall r, In r rs -> YP09.r_whi r <= YP09.r_wlo r) ->
  frame_of E rs (mrestrict H m) (mrestrict H m') -> forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E H m m' rs Hro HF a. rewrite (aview_wrap H m' a), (aview_wrap H m a).
apply (aview_kept_frame E rs H m m' 0 HF ltac:(lia)); [| apply Z.mod_pos_bound; lia].
intros x Hx (r & Hin & Hr). pose proof (Hro r Hin) as Hq. lia.
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TSB : tsb_ch_spec B.
Lemma l1_kept_mono : forall lyc Sc W1 m1 W2 m2 sp (E E' : Z -> Prop),
  (forall a, E a -> E' a) -> tsb_ch_kept B lyc Sc W1 m1 W2 m2 sp E -> tsb_ch_kept B lyc Sc W1 m1 W2 m2 sp E'.
Proof.
intros lyc Sc W1 m1 W2 m2 sp E E' HE (K1 & K2 & K3 & K4 & K5 & K6).
split; [intros a Ha Hw He; exact (K1 a Ha Hw (fun x => He (HE a x)))|].
split; [intros b mm i Hb Hi He; exact (K2 b mm i Hb Hi (fun x => He (HE _ x)))|].
split; [exact K3|].
split; [intros cid pos a Hf Hz He; exact (K4 cid pos a Hf Hz (fun x => He (HE a x)))|].
split; [exact K5 | exact K6].
Qed.
Lemma l1_kept_run : forall lyc Sc W memc W1 m1 m2 sp E,
  tsb_ch_kept B lyc Sc W memc W1 m1 sp E ->
  (forall a, aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a) ->
  mem_grows (mrestrict (w_H W1) m1) (mrestrict (w_H W1) m2) ->
  tsb_ch_kept B lyc Sc W memc W1 m2 sp E.
Proof.
intros lyc Sc W memc W1 m1 m2 sp E (K1 & K2 & K3 & K4 & K5 & K6) Hv Hg.
split; [intros a Ha Hw He; rewrite Hv; exact (K1 a Ha Hw He)|].
split; [intros b mm i Hb Hi He; rewrite Hv; exact (K2 b mm i Hb Hi He)|].
split; [intros a Hi Ho Her; rewrite Hv; exact (K3 a Hi Ho Her)|].
split; [intros cid pos a Hf Hz He; rewrite Hv; exact (K4 cid pos a Hf Hz He)|].
split; [intros a Ha Hw Hp; exact (apresent_grows _ _ _ _ Hg (K5 a Ha Hw Hp))
       |intros a Ha; exact (apresent_grows _ _ _ _ Hg (K6 a Ha))].
Qed.
Lemma l1_kept_trans : forall lyc Sc lyc1 Sc1 W memc W1 m1 W2 m2 sp E1 E2,
  ablocks B lyc1 Sc1 = ablocks B lyc Sc -> frames Sc1 = frames Sc ->
  (forall c p, frame_addr lyc1 c p = frame_addr lyc c p) ->
  tsb_ch_kept B lyc Sc W memc W1 m1 sp E1 ->
  tsb_ch_kept B lyc1 Sc1 W1 m1 W2 m2 sp E2 ->
  tsb_ch_kept B lyc Sc W memc W2 m2 sp (fun a => E1 a \/ E2 a).
Proof.
intros lyc Sc lyc1 Sc1 W memc W1 m1 W2 m2 sp E1 E2 Hbl Hfr Hfa
  (K1 & K2 & K3 & K4 & K5 & K6) (L1 & L2 & L3 & L4 & L5 & L6).
split.
{ intros a Ha Hw He. rewrite (L1 a Ha Hw (fun x => He (or_intror x))). exact (K1 a Ha Hw (fun x => He (or_introl x))). }
split.
{ intros b mm i Hb Hi He.
  rewrite (L2 b mm i ltac:(rewrite Hbl; exact Hb) Hi (fun x => He (or_intror x))).
  exact (K2 b mm i Hb Hi (fun x => He (or_introl x))). }
split.
{ intros a Hi Ho Her. rewrite (L3 a Hi Ho Her). exact (K3 a Hi Ho Her). }
split.
{ intros cid pos a Hf Hz He.
  assert (Hz1 : in_zr a (frame_rng lyc1 (cid, pos)) \/
                in_zr a (shadow_addr (frame_addr lyc1 cid pos), fs_frame_bytes cid / 8)).
  { unfold frame_rng in *. cbn [fst snd] in *. rewrite (Hfa cid pos). exact Hz. }
  rewrite (L4 cid pos a ltac:(rewrite Hfr; exact Hf) Hz1 (fun x => He (or_intror x))).
  exact (K4 cid pos a Hf Hz (fun x => He (or_introl x))). }
split.
{ intros a Ha Hw Hp. exact (L5 a Ha Hw (K5 a Ha Hw Hp)). }
intros a Ha. exact (L6 a Ha).
Qed.
Lemma l1_rod : forall lyc Sc W1 m1 W2 m2 sp E,
  tsb_ch_kept B lyc Sc W1 m1 W2 m2 sp E ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W1) m1) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) m2).
Proof.
intros lyc Sc W1 m1 W2 m2 sp E (_ & _ & K3 & _) HRO a Hro Ho He.
assert (Hi : in_img SEGS a)
  by (destruct Hro as [(sg & Hs & _ & Hr) | Hr]; [exists sg; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hr)]).
rewrite (K3 a Hi Ho He). exact (HRO a Hro Ho He).
Qed.
Lemma l1_core : forall (m : nat) (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc
  (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (P D n0 ov0 : Z) (s : list Z)
  (lyc1 : alayout) (Sc1 : astate) (W1 : world SEGS) (mem1 : word -> option byte) (md1 : Model)
  (regs1 : bvmap 5 word) (Q : Z) (t : list Z) (n ov : Z) (wr : list Z) (nF ovF : Z) (wrF : list Z),
  rbn_lcx B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ->
  rbn_lrec B STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 152) D 24 n0 ov0 ->
  rbn_lbuf B STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 152) D 24 ->
  rbn_lsrc W memc P (s ++ [0]) ->
  rbn_lsep (spZ regs) (spZ regs + 152) D 24 P (Z.of_nat (length s) + 1) ->
  0 <= n0 <= 23 ->
  (length t <= m)%nat -> t <> [] -> Forall (fun c => 0 < c < 256) t ->
  P <= Q -> Q + Z.of_nat (length t) = P + Z.of_nat (length s) ->
  garr8 SEGS (mrestrict (w_H W) memc) Q (t ++ [0]) ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc1 Sc1 W1 mem1 md1 k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W1) mem1) ->
  ablocks B lyc1 Sc1 = ablocks B lyc Sc -> frames Sc1 = frames Sc ->
  tsb_ch_kept B lyc Sc W memc W1 mem1 (spZ regs)
    (fun a => spZ regs + 152 + 16 <= a < spZ regs + 152 + 28 \/
              D + n0 <= a < D + n0 + Z.of_nat (length wrF)) ->
  val_mem SEGS (mrestrict (w_H W1) mem1) (spZ regs + 152 + 16) 8 n ->
  val_mem SEGS (mrestrict (w_H W1) mem1) (spZ regs + 152 + 24) 4 ov ->
  garr8 SEGS (mrestrict (w_H W1) mem1) (D + n0) wr ->
  Z.of_nat (length wr) = n - n0 -> n0 <= n <= 23 -> (ov = 0 \/ ov = 1) ->
  getr regs1 1 = w64 (BASE + (AF_both3_reac_box_name + 800)) ->
  getr regs1 2 = getr regs 2 -> getr regs1 3 = w64 (as_gp B) -> getr regs1 4 = w64 (as_tp B) ->
  getr regs1 9 = getr regs 2 -> getr regs1 10 = w64 (spZ regs + 152) -> getr regs1 11 = w64 (hd 0 t) ->
  getr regs1 21 = w64 Q -> getr regs1 22 = w64 SHADOW_OFF -> getr regs1 24 = w64 (-1) ->
  getr regs1 26 = w64 (Q + 1) ->
  rbn_keep_regs regs regs1 rbn_cl1 ->
  nF = Z.min (n + Z.of_nat (length t)) 23 ->
  ovF = (if n + Z.of_nat (length t) <=? 23 then ov else 1) ->
  wrF = wr ++ firstn (Z.to_nat (23 - n)) t ->
  SRr SEGS W1 (cfg_at (fx := fq) SEGS (BASE + AF_both3_sb_ch) regs1 mem1 md1)
    (rbn_lpost B fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L1X rbn_cl1
       (spZ regs + 152) D n0 nF ovF wrF).
Proof.
intros m. induction m as [|m IH]; intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
  P D n0 ov0 s lyc1 Sc1 W1 mem1 md1 regs1 Q t n ov wr nF ovF wrF
  HCX HREC HBUF HSRC HSEP Hn0 Hm Ht0 Htb HPQ HQlen HgaQ HJ1 HRO1 Hbl Hfrs KEPT Vn Vov Vwr Hwrl Hn Hov
  G1 G2 G3 G4 G9 G10 G11 G21 G22 G24 G26 GK HnF HovF HwrF.
{ exfalso. destruct t as [|c t']; [exact (Ht0 eq_refl) | cbn [length] in Hm; lia]. }
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
pose proof pa_B_ok as (HB1 & HB2 & HB3). pose proof pa_base_lo as HBL. unfold YImgTop.IMG_LO in HBL.
pose proof HCX as (HJ0 & HRO0 & Hgp & Htp & H9 & H22 & Hal16 & Hwlo & Hwhi).
pose proof HREC as (HR0 & HR8 & HR63 & HRam & HRimg & HRside & HDr0 & HDrcap & HnA & HnB & HovA &
  VD & Vcap & Vn0m & Vov0m & HRra & HRhull & HRwr).
pose proof HBUF as (HD0 & HD63 & HDapp & HDam & HDimg & HDside & HDR & HDra & HDhull & HDwr).
pose proof HSRC as (HgaP & HP0 & HP63 & HP47 & HPra).
assert (HSL : Z.of_nat (length (s ++ [0])) = Z.of_nat (length s) + 1)
  by (rewrite length_app; cbn [length]; lia).
rewrite HSL in HP63, HP47, HPra.
pose proof HSEP as (HsepD & HsepR & Hsepsp).
pose proof HJ0 as (_ & Hly0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 &
  (Hsp0al & Hstk0 & Hceil0 & Hslo0 & Hshi0 & H47a & Hbot0 & Htop0 & Htop0b) & _).
assert (HTS : TSB_CH_STK = 4112) by reflexivity.
assert (Hceil : alloc_ceiling <= spZ regs - TSB_CH_STK) by lia.
assert (HR47 : spZ regs + 152 + 28 <= 2 ^ 47 - 1) by (unfold amem_range in HRam; lia).
assert (HD47 : D + 24 <= 2 ^ 47 - 1) by (unfold amem_range in HDam; lia).
assert (HlenF : Z.of_nat (length wrF) = nF - n0)
  by (subst wrF nF; rewrite length_app, length_firstn; lia).
assert (HnFr : n0 <= nF <= 23) by (subst nF; lia).
assert (Hfa : forall cc pp, frame_addr lyc1 cc pp = frame_addr lyc cc pp)
  by (intros cc pp; exact (l1_lyF _ ly lyc1 lyc (proj1 (proj2 HJ1)) (proj1 (proj2 HJ0)) cc pp)).
pose proof (fun a Ha => proj1 (awr_byte_present SEGS B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc1 Sc1
  W1 mem1 md1 k a HJ1 Ha)) as HAPR.
assert (HAWR : forall a, awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a ->
    awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc1 Sc1) lyc1 own a)
  by (intros a Ha; exact (l1_awr_ly STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) (ablocks B lyc1 Sc1)
       lyc lyc1 own a Hbl Hfa Ha)).
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TSB_CH_STK <= a < spZ regs) ->
    ~ (spZ regs + 152 + 16 <= a < spZ regs + 152 + 28) ->
    ~ (D + n0 <= a < D + n0 + Z.of_nat (length wrF)) ->
    aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) memc a).
{ intros a Ha Hw He1 He2. apply (proj1 KEPT a Ha Hw). intros [x | x]; [exact (He1 x) | exact (He2 x)]. }
assert (KEEPB : forall ss, SHADOW_OFF - 4096 <= ss < kHighMemBeg ->
    aview SEGS (w_H W1) mem1 ss = aview SEGS (w_H W) memc ss).
{ intros ss Hss. destruct (l1_avoid (spZ regs + 152) D n0 (Z.of_nat (length wrF)) (spZ regs) ss
    ltac:(lia) HDapp Hceil ltac:(lia) ltac:(lia) ltac:(lia) Hss) as (A1 & A2 & A3 & A4).
  apply KEEP1; assumption. }
assert (VD1 : val_mem SEGS (mrestrict (w_H W1) mem1) (spZ regs + 152) 8 D)
  by (apply (l1_vk (w_H W) (w_H W1) memc mem1); [intros x Hx; apply KEEP1; lia | exact VD]).
assert (Vcap1 : val_mem SEGS (mrestrict (w_H W1) mem1) (spZ regs + 152 + 8) 8 24)
  by (apply (l1_vk (w_H W) (w_H W1) memc mem1); [intros x Hx; apply KEEP1; lia | exact Vcap]).
assert (HRra1 : range_addressable (aview SEGS (w_H W1) mem1) SHADOW_OFF (spZ regs + 152) 28).
{ apply (l1_rak (aview SEGS (w_H W) memc) (aview SEGS (w_H W1) mem1) (spZ regs + 152) 28); [|exact HRra].
  intros x Hx. apply KEEPB. destruct (l1_band x ltac:(lia) ltac:(lia)) as [Hb1 Hb2]. lia. }
assert (HRh1 : shadow_hull_vis (aview SEGS (w_H W1) mem1) (spZ regs + 152) 28).
{ apply (l1_hk (aview SEGS (w_H W) memc) (aview SEGS (w_H W1) mem1) (spZ regs + 152) 28); [|exact HRhull].
  intros ss Hss. apply KEEPB.
  exact (l1_hull_rng (spZ regs + 152) 28 ss ltac:(lia) ltac:(lia) ltac:(lia) Hss). }
assert (HDnra : forall nn, 0 <= nn <= 23 ->
    range_addressable (aview SEGS (w_H W1) mem1) SHADOW_OFF (D + nn) 1).
{ intros nn Hnn. apply (l1_rak (aview SEGS (w_H W) memc) (aview SEGS (w_H W1) mem1) (D + nn) 1).
  - intros x Hx. apply KEEPB. destruct (l1_band x ltac:(lia) ltac:(lia)) as [Hb1 Hb2]. lia.
  - apply (range_addressable_sub (aview SEGS (w_H W) memc) SHADOW_OFF D 24); [exact HDra | lia | lia]. }
assert (HDnh : forall nn, 0 <= nn <= 23 -> shadow_hull_vis (aview SEGS (w_H W1) mem1) (D + nn) 1).
{ intros nn Hnn. apply (l1_hk (aview SEGS (w_H W) memc) (aview SEGS (w_H W1) mem1) (D + nn) 1).
  - intros ss Hss. apply KEEPB. exact (l1_hull_rng (D + nn) 1 ss ltac:(lia) ltac:(lia) ltac:(lia) Hss).
  - exact (l1_hsub (aview SEGS (w_H W) memc) D 24 (D + nn) 1 HDhull ltac:(lia) ltac:(lia) ltac:(lia)). }
assert (HraQ0 : range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF Q (Z.of_nat (length t) + 1))
  by (apply (range_addressable_sub (aview SEGS (w_H W) memc) SHADOW_OFF P (Z.of_nat (length s) + 1));
      [exact HPra | lia | lia]).
destruct t as [|c t']; [exact (False_ind _ (Ht0 eq_refl))|].
assert (Hc : 0 < c < 256) by (inversion Htb; assumption).
assert (Htb' : Forall (fun x => 0 < x < 256) t') by (inversion Htb; assumption).
cbn [hd] in G11.
assert (HLn : Z.of_nat (length (c :: t')) = Z.of_nat (length t') + 1) by (cbn [length]; lia).
assert (Hsp1 : spZ regs1 = spZ regs) by (unfold spZ; rewrite G2; reflexivity).
assert (Hidx : (1 < length ((c :: t') ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
destruct (HgaQ 1%nat Hidx) as [Hc2m0 Hc2r]. change (Z.of_nat 1) with 1 in Hc2m0.
set (c2 := nth 1 ((c :: t') ++ [0]) 0) in *.
assert (Hc2z : c2 = 0 -> t' = []).
{ unfold c2. destruct t' as [|x t'']; [reflexivity|]. cbn [app nth]. intros Hx. exfalso. inversion Htb'. lia. }
assert (Hc2nil : t' = [] -> c2 = 0) by (intros Hx; unfold c2; rewrite Hx; reflexivity).
assert (Hc2nz : t' <> [] -> c2 = hd 0 t').
{ unfold c2. destruct t' as [|x t'']; [intros HX; exfalso; exact (HX eq_refl)|]. cbn [app nth hd]. reflexivity. }
eapply SRr_bind.
{ apply (TSB fq STK sp0 FP ly S W0 mem0 md0 own lyc1 Sc1 W1 mem1 md1 k regs1
    (spZ regs + 152) c D 24 n []).
  - exact HJ1.
  - exact HRO1.
  - rewrite G1. unfold w64. apply ret_ok_codeptr_v;
    [unfold AF_both3_reac_box_name; lia | vm_compute; reflexivity].
  - unfold raZ. rewrite G1. unfold w64.
    rewrite unsigned_lit_small by (unfold AF_both3_reac_box_name; lia).
    unfold AF_both3_reac_box_name. lia.
  - exact G3.
  - exact G4.
  - exact G10.
  - exact G11.
  - apply achain_low. unfold s0Z. rewrite getr_same by reg_neq_tac.
    rewrite unsigned_lit_small by lia. lia.
  - rewrite Hsp1. exact Hal16.
  - rewrite Hsp1. exact Hwlo.
  - rewrite Hsp1. exact Hwhi.
  - lia.
  - exact HR0.
  - exact HR8.
  - exact HR63.
  - exact HRam.
  - rewrite Hsp1. exact HRside.
  - exact HRimg.
  - exact HDr0.
  - lia.
  - lia.
  - exact VD1.
  - exact Vcap1.
  - exact Vn.
  - exact HRra1.
  - exact HRh1.
  - intros a Ha. split; [apply HAWR; exact (proj1 (HRwr a Ha))
                        |apply HAPR; apply HAWR; exact (proj1 (HRwr a Ha))].
  - intros Hlt. split; [lia|]. split; [lia|]. split; [unfold amem_range in HDam |- *; lia|].
    split; [apply HDnra; lia|]. split; [apply HDnh; lia|].
    split; [rewrite Hsp1; lia|]. split; [unfold off_img in HDimg |- *; lia|].
    split; [lia|].
    split; [apply HAWR; exact (proj1 (HDwr (D + n) ltac:(lia)))
           |apply HAPR; apply HAWR; exact (proj1 (HDwr (D + n) ltac:(lia)))]. }
cbv beta. intros W2 cfg2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HPRES2 & Hfr2 & Hbl2 & Hcase).
assert (HSTEP : exists (n' ov' : Z) (wr' : list Z),
  n' = Z.min (n + 1) 23 /\ ov' = (if n + 1 <=? 23 then ov else 1) /\
  wr' = wr ++ firstn (Z.to_nat (23 - n)) [c] /\
  val_mem SEGS (mrestrict (w_H W2) mem2) (spZ regs + 152 + 16) 8 n' /\
  val_mem SEGS (mrestrict (w_H W2) mem2) (spZ regs + 152 + 24) 4 ov' /\
  garr8 SEGS (mrestrict (w_H W2) mem2) (D + n0) wr' /\
  tsb_ch_kept B lyc Sc W memc W2 mem2 (spZ regs)
    (fun a => spZ regs + 152 + 16 <= a < spZ regs + 152 + 28 \/
              D + n0 <= a < D + n0 + Z.of_nat (length wrF))).
{ destruct Hcase as [(Hcap & Vov2 & KC) | (Hcap & Vn2 & Vc2 & KC)]; rewrite Hsp1 in KC.
  - assert (Hn23 : n = 23) by lia.
    assert (KCm : tsb_ch_kept B lyc1 Sc1 W1 mem1 W2 mem2 (spZ regs)
      (fun a => spZ regs + 152 + 16 <= a < spZ regs + 152 + 28 \/
                D + n0 <= a < D + n0 + Z.of_nat (length wrF))).
    { eapply l1_kept_mono; [|exact KC]. intros a Ha. cbv beta in Ha |- *. left. lia. }
    assert (KEEPC : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TSB_CH_STK <= a < spZ regs) ->
        ~ (spZ regs + 152 + 24 <= a < spZ regs + 152 + 28) ->
        aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) mem1 a)
      by (intros a Ha Hw He; exact (proj1 KC a Ha Hw He)).
    exists 23, 1, wr.
    split; [lia|].
    split; [replace (n + 1 <=? 23) with false by (symmetry; apply Z.leb_gt; lia); reflexivity|].
    split; [rewrite Hn23; replace (Z.to_nat (23 - 23)) with 0%nat by lia; cbn [firstn];
            rewrite app_nil_r; reflexivity|].
    split.
    { apply (l1_vk (w_H W1) (w_H W2) mem1 mem2); [intros x Hx; apply KEEPC; lia|]. rewrite <- Hn23. exact Vn. }
    split; [exact Vov2|].
    split.
    { apply (l1_gk (w_H W1) (w_H W2) mem1 mem2); [intros x Hx; apply KEEPC; lia | exact Vwr]. }
    eapply l1_kept_mono;
    [|exact (l1_kept_trans lyc Sc lyc1 Sc1 W memc W1 mem1 W2 mem2 (spZ regs) _ _ Hbl Hfrs Hfa KEPT KCm)].
    intros a Hx. cbv beta in Hx |- *. destruct Hx as [x | x]; exact x.
  - assert (Hn22 : n <= 22) by lia.
    assert (KCm : tsb_ch_kept B lyc1 Sc1 W1 mem1 W2 mem2 (spZ regs)
      (fun a => spZ regs + 152 + 16 <= a < spZ regs + 152 + 28 \/
                D + n0 <= a < D + n0 + Z.of_nat (length wrF))).
    { eapply l1_kept_mono; [|exact KC]. intros a Hx. cbv beta in Hx |- *.
      destruct Hx as [Ha | Ha]; [left; lia | right; subst nF; rewrite HLn in *; lia]. }
    assert (KEEPC : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TSB_CH_STK <= a < spZ regs) ->
        ~ (spZ regs + 152 + 16 <= a < spZ regs + 152 + 24) -> a <> D + n ->
        aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) mem1 a).
    { intros a Ha Hw He1 He2. apply (proj1 KC a Ha Hw). intros [x | x]; [exact (He1 x) | exact (He2 x)]. }
    assert (Hcm : c mod 256 = c) by (apply Z.mod_small; lia).
    exists (n + 1), ov, (wr ++ [c]).
    split; [lia|].
    split; [replace (n + 1 <=? 23) with true by (symmetry; apply Z.leb_le; lia); reflexivity|].
    split; [replace (Z.to_nat (23 - n)) with (Datatypes.S (Z.to_nat (23 - n - 1))) by lia;
            cbn [firstn]; rewrite firstn_nil; reflexivity|].
    split; [exact Vn2|].
    split; [apply (l1_vk (w_H W1) (w_H W2) mem1 mem2); [intros x Hx; apply KEEPC; lia | exact Vov]|].
    split.
    { apply (garr8_app1 SEGS (mrestrict (w_H W1) mem1) (mrestrict (w_H W2) mem2) (D + n0) wr c Vwr).
      - rewrite Hwrl. replace (D + n0 + (n - n0)) with (D + n) by lia. rewrite <- Hcm. exact Vc2.
      - lia.
      - intros a Ha. rewrite Hwrl in Ha. apply (mbyte_of_aview SEGS (w_H W1) (w_H W2)). apply KEEPC; lia. }
    eapply l1_kept_mono;
    [|exact (l1_kept_trans lyc Sc lyc1 Sc1 W memc W1 mem1 W2 mem2 (spZ regs) _ _ Hbl Hfrs Hfa KEPT KCm)].
    intros a Hx. cbv beta in Hx |- *. destruct Hx as [x | x]; exact x. }
destruct HSTEP as (n' & ov' & wr' & Hn'e & Hov'e & Hwr'e & Vn' & Vov' & Vwr' & KEPT2).
assert (Hn'r : n0 <= n' <= 23) by lia.
assert (Hov'r : ov' = 0 \/ ov' = 1) by (subst ov'; destruct (n + 1 <=? 23); lia).
assert (Hwr'l : Z.of_nat (length wr') = n' - n0)
  by (subst wr' n'; rewrite length_app, length_firstn; cbn [length]; lia).
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TSB_CH_STK <= a < spZ regs) ->
    ~ (spZ regs + 152 + 16 <= a < spZ regs + 152 + 28) ->
    ~ (D + n0 <= a < D + n0 + Z.of_nat (length wrF)) ->
    aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a).
{ intros a Ha Hw He1 He2. apply (proj1 KEPT2 a Ha Hw). intros [x | x]; [exact (He1 x) | exact (He2 x)]. }
assert (KEEPB2 : forall ss, SHADOW_OFF - 4096 <= ss < kHighMemBeg ->
    aview SEGS (w_H W2) mem2 ss = aview SEGS (w_H W) memc ss).
{ intros ss Hss. destruct (l1_avoid (spZ regs + 152) D n0 (Z.of_nat (length wrF)) (spZ regs) ss
    ltac:(lia) HDapp Hceil ltac:(lia) ltac:(lia) ltac:(lia) Hss) as (A1 & A2 & A3 & A4).
  apply KEEP2; assumption. }
assert (Hc2m2 : val_mem SEGS (mrestrict (w_H W2) mem2) (Q + 1) 1 c2)
  by (apply (l1_vk (w_H W) (w_H W2) memc mem2); [intros x Hx; apply KEEP2; lia | exact Hc2m0]).
assert (HraQ2 : range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF Q (Z.of_nat (length (c :: t')) + 1)).
{ apply (l1_rak (aview SEGS (w_H W) memc) (aview SEGS (w_H W2) mem2) Q (Z.of_nat (length (c :: t')) + 1));
  [|exact HraQ0].
  intros x Hx. apply KEEPB2. destruct (l1_band x ltac:(lia) ltac:(lia)) as [Hb1 Hb2]. lia. }
assert (P21 : getr regs2 21 = w64 Q)
  by (rewrite (l1_callee1 regs1 regs2 21 21%bv HPRES2 ltac:(unfold acallee_saved; lia)
       ltac:(apply bv_eq; vm_compute; reflexivity)); exact G21).
assert (P26 : getr regs2 26 = w64 (Q + 1))
  by (rewrite (l1_callee1 regs1 regs2 26 26%bv HPRES2 ltac:(unfold acallee_saved; lia)
       ltac:(apply bv_eq; vm_compute; reflexivity)); exact G26).
assert (P24 : getr regs2 24 = w64 (-1))
  by (rewrite (l1_callee1 regs1 regs2 24 24%bv HPRES2 ltac:(unfold acallee_saved; lia)
       ltac:(apply bv_eq; vm_compute; reflexivity)); exact G24).
assert (P22 : getr regs2 22 = w64 SHADOW_OFF)
  by (rewrite (l1_callee1 regs1 regs2 22 22%bv HPRES2 ltac:(unfold acallee_saved; lia)
       ltac:(apply bv_eq; vm_compute; reflexivity)); exact G22).
assert (P2 : getr regs2 2 = getr regs 2)
  by (rewrite (l1_callee1 regs1 regs2 2 2%bv HPRES2 ltac:(unfold acallee_saved; lia)
       ltac:(apply bv_eq; vm_compute; reflexivity)); exact G2).
assert (P9 : getr regs2 9 = getr regs 2)
  by (rewrite (l1_callee1 regs1 regs2 9 9%bv HPRES2 ltac:(unfold acallee_saved; lia)
       ltac:(apply bv_eq; vm_compute; reflexivity)); exact G9).
assert (P3 : getr regs2 3 = w64 (as_gp B))
  by (rewrite (l1_callee1 regs1 regs2 3 3%bv HPRES2 ltac:(unfold acallee_saved; lia)
       ltac:(apply bv_eq; vm_compute; reflexivity)); exact G3).
assert (P4 : getr regs2 4 = w64 (as_tp B))
  by (rewrite (l1_callee1 regs1 regs2 4 4%bv HPRES2 ltac:(unfold acallee_saved; lia)
       ltac:(apply bv_eq; vm_compute; reflexivity)); exact G4).
pose proof (l1_post_entry fq W2 regs2 mem2 Q c2 ltac:(lia) ltac:(lia) ltac:(lia) P21 P26 P24 P22 Hc2m2) as HS.
pose proof (EY_img regs2 [c2]) as HEI.
assert (SHOK : sh_ok SEGS (SOff 22 0) [] (EY regs2 [c2]) (mrestrict (w_H W2) mem2)) by apply Forall_nil.
pose (RUN := paj_run (fx := fq) B LAWS). pose (BR := paj_branch (fx := fq) (PI := PI)).
assert (E22 : ew (EY regs2 [c2]) 22 = w64 SHADOW_OFF)
  by (rewrite (EY_reg regs2 _ 22%nat 22%bv) by (first [lia | vm_compute; reflexivity]); exact P22).
assert (E21 : ew (EY regs2 [c2]) 21 = w64 Q)
  by (rewrite (EY_reg regs2 _ 21%nat 21%bv) by (first [lia | vm_compute; reflexivity]); exact P21).
assert (E9 : ew (EY regs2 [c2]) 9 = getr regs 2)
  by (rewrite (EY_reg regs2 _ 9%nat 9%bv) by (first [lia | vm_compute; reflexivity]); exact P9).
assert (E32 : ew (EY regs2 [c2]) 32 = w64 c2) by apply EY_32.
rewrite G1. unfold w64 at 1.
paj_run_tok RUN HS HJ2 SHOK Bspan.
{ cbn [ms_mem mkst]. rewrite <- (aview_rd_of SEGS).
  rewrite (U_atom (EY regs2 [c2]) 22 SHADOW_OFF E22) by (unfold SHADOW_OFF; lia).
  rewrite (U_atom_off (EY regs2 [c2]) 21 Q 1 E21) by lia.
  apply (range_addressable_sub (aview SEGS (w_H W2) mem2) SHADOW_OFF Q (Z.of_nat (length (c :: t')) + 1));
  [exact HraQ2 | lia | lia]. }
{ awr_ok_tac. }
assert (KEEPR1 : forall a, aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
{ cbn [ms_mem mkst] in HFr. eapply l1_aview_ro; [|exact HFr]. l1_ro_regs. }
assert (HG1 : mem_grows (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) (ms_mem ms)))
  by (cbn [ms_mem mkst] in HG; exact HG).
assert (KEPT3 : tsb_ch_kept B lyc Sc W memc W2 (ms_mem ms) (spZ regs)
  (fun a => spZ regs + 152 + 16 <= a < spZ regs + 152 + 28 \/
            D + n0 <= a < D + n0 + Z.of_nat (length wrF)))
  by exact (l1_kept_run lyc Sc W memc W2 mem2 (ms_mem ms) (spZ regs) _ KEPT2 KEEPR1 HG1).
psrr_branch_tok RUN BR HS SHOK Bspan.
{ rl_pull HS E32 F32.
  rewrite branch_eq_U in Hc0. rewrite (U_atom _ 32 c2 F32) in Hc0 by lia.
  rewrite U_lit in Hc0 by lia. apply Z.eqb_eq in Hc0.
  assert (Ht'nil : t' = []) by (apply Hc2z; exact Hc0).
  clear HF HFr HG.
  paj_run_tok RUN HS HJ2 SHOK Bspan; [awr_ok_tac|].
  assert (KEEPR2 : forall a, aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) (ms_mem ms) a).
  { eapply l1_aview_ro; [|exact HFr]. l1_ro_regs. }
  assert (KEEPR : forall a, aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a)
    by (intros a; rewrite KEEPR2; apply KEEPR1).
  assert (KEPT4 : tsb_ch_kept B lyc Sc W memc W2 (ms_mem ms0) (spZ regs)
    (fun a => spZ regs + 152 + 16 <= a < spZ regs + 152 + 28 \/
              D + n0 <= a < D + n0 + Z.of_nat (length wrF)))
    by exact (l1_kept_run lyc Sc W memc W2 (ms_mem ms) (ms_mem ms0) (spZ regs) _ KEPT3 KEEPR2 HG).
  assert (HnFe : nF = n') by (subst nF n'; rewrite Ht'nil; cbn [length]; lia).
  assert (HovFe : ovF = ov') by (subst ovF ov'; rewrite Ht'nil; cbn [length];
    replace (n + Z.of_nat 1) with (n + 1) by lia; reflexivity).
  assert (HwrFe : wrF = wr') by (subst wrF wr'; rewrite Ht'nil; reflexivity).
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs2 (map w64 [c2]) l1_kept_regs HS
    ltac:(env_agree_chain (EY_agree regs2 [c2])) ltac:(vm_compute; reflexivity)) as HK3.
  cbn [ms_regs restrict] in HK3.
  apply SRr_ret. unfold rbn_lpost. pmkst HS.
  eexists ly2, S2, _, _, _.
  split.
  { unfold cfg_at, w64. rewrite <- Z.add_assoc.
    change (AF_both3_reac_box_name + RBN_L1X) with 14872. reflexivity. }
  split; [exact HJ2|].
  split; [rewrite Hfr2; exact Hfrs|].
  split; [rewrite Hbl2; exact Hbl|].
  split; [exact (l1_rod lyc Sc W memc W2 (ms_mem ms0) (spZ regs) _ KEPT4 HRO0)|].
  split.
  { apply (l1_keep_trans regs regs1 (ms_regs ms0)); [exact GK|].
    apply (l1_keep_trans regs1 regs2 (ms_regs ms0)); [exact (l1_keep_pres regs1 regs2 HPRES2)|].
    apply l1_keep_cl1. exact HK3. }
  split.
  { rewrite HnFe. apply (l1_vk (w_H W2) (w_H W2) mem2 (ms_mem ms0));
    [intros x Hx; apply KEEPR | exact Vn']. }
  split.
  { rewrite HovFe. apply (l1_vk (w_H W2) (w_H W2) mem2 (ms_mem ms0));
    [intros x Hx; apply KEEPR | exact Vov']. }
  split.
  { rewrite HwrFe. apply (l1_gk (w_H W2) (w_H W2) mem2 (ms_mem ms0));
    [intros x Hx; apply KEEPR | exact Vwr']. }
  exact KEPT4. }
{ rl_pull HS E32 F32.
  rewrite branch_eq_U in Hc0. rewrite (U_atom _ 32 c2 F32) in Hc0 by lia.
  rewrite U_lit in Hc0 by lia. apply Z.eqb_neq in Hc0.
  assert (Ht'ne : t' <> []) by (intros Hx; apply Hc0; apply Hc2nil; exact Hx).
  clear HF HFr HG.
  paj_run_tok RUN HS HJ2 SHOK Bspan; [awr_ok_tac|].
  assert (KEEPR2 : forall a, aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) (ms_mem ms) a).
  { eapply l1_aview_ro; [|exact HFr]. l1_ro_regs. }
  assert (KEEPR : forall a, aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a)
    by (intros a; rewrite KEEPR2; apply KEEPR1).
  assert (KEPT4 : tsb_ch_kept B lyc Sc W memc W2 (ms_mem ms0) (spZ regs)
    (fun a => spZ regs + 152 + 16 <= a < spZ regs + 152 + 28 \/
              D + n0 <= a < D + n0 + Z.of_nat (length wrF)))
    by exact (l1_kept_run lyc Sc W memc W2 (ms_mem ms) (ms_mem ms0) (spZ regs) _ KEPT3 KEEPR2 HG).
  pose proof (regs_kept_of_st_ok _ _ _ _ regs2 (map w64 [c2]) l1_kept_regs HS
    ltac:(env_agree_chain (EY_agree regs2 [c2])) ltac:(vm_compute; reflexivity)) as HK3.
  cbn [ms_regs restrict] in HK3.
  prreg HS (1%bv : bv 5) R1. prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11.
  prreg HS (21%bv : bv 5) R21. prreg HS (26%bv : bv 5) R26.
  pmkst HS. rewrite pa_sigma_sb_ch.
  apply (IH fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s
    ly2 S2 W2 (ms_mem ms0) _ (ms_regs ms0) (Q + 1) t' n' ov' wr' nF ovF wrF).
  - exact HCX.
  - exact HREC.
  - exact HBUF.
  - exact HSRC.
  - exact HSEP.
  - exact Hn0.
  - cbn [length] in Hm. lia.
  - exact Ht'ne.
  - exact Htb'.
  - lia.
  - rewrite HLn in HQlen. lia.
  - intros j Hj.
    assert (Hj2 : (Datatypes.S j < length ((c :: t') ++ [0%Z]))%nat)
      by (change ((c :: t') ++ [0%Z]) with (c :: (t' ++ [0%Z])); cbn [length]; lia).
    destruct (HgaQ (Datatypes.S j) Hj2) as [Hv Hr]. split; [|exact Hr].
    replace (Q + 1 + Z.of_nat j) with (Q + Z.of_nat (Datatypes.S j)) by lia. exact Hv.
  - exact HJ2.
  - exact (l1_rod lyc Sc W memc W2 (ms_mem ms0) (spZ regs) _ KEPT4 HRO0).
  - rewrite Hbl2. exact Hbl.
  - rewrite Hfr2. exact Hfrs.
  - exact KEPT4.
  - apply (l1_vk (w_H W2) (w_H W2) mem2 (ms_mem ms0)); [intros x Hx; apply KEEPR | exact Vn'].
  - apply (l1_vk (w_H W2) (w_H W2) mem2 (ms_mem ms0)); [intros x Hx; apply KEEPR | exact Vov'].
  - apply (l1_gk (w_H W2) (w_H W2) mem2 (ms_mem ms0)); [intros x Hx; apply KEEPR | exact Vwr'].
  - exact Hwr'l.
  - exact Hn'r.
  - exact Hov'r.
  - rewrite R1. unfold w64, AF_both3_reac_box_name. f_equal; lia.
  - rewrite (HK3 2%bv ltac:(unfold l1_kept_regs; cbn [In]; repeat (first [left; reflexivity | right]))).
    exact P2.
  - rewrite (HK3 3%bv ltac:(unfold l1_kept_regs; cbn [In]; repeat (first [left; reflexivity | right]))).
    exact P3.
  - rewrite (HK3 4%bv ltac:(unfold l1_kept_regs; cbn [In]; repeat (first [left; reflexivity | right]))).
    exact P4.
  - rewrite (HK3 9%bv ltac:(unfold l1_kept_regs; cbn [In]; repeat (first [left; reflexivity | right]))).
    exact P9.
  - rewrite R10. rewrite E9. unfold w64, spZ. reflexivity.
  - rewrite R11. rewrite (l1_and255 _ c2 E32 ltac:(lia)). rewrite (Hc2nz Ht'ne). reflexivity.
  - rewrite R21, E21. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  - rewrite (HK3 22%bv ltac:(unfold l1_kept_regs; cbn [In]; repeat (first [left; reflexivity | right]))).
    exact P22.
  - rewrite (HK3 24%bv ltac:(unfold l1_kept_regs; cbn [In]; repeat (first [left; reflexivity | right]))).
    exact P24.
  - rewrite R26, E21. unfold w64. rewrite unsigned_lit_small by lia. f_equal; lia.
  - apply (l1_keep_trans regs regs1 (ms_regs ms0)); [exact GK|].
    apply (l1_keep_trans regs1 regs2 (ms_regs ms0)); [exact (l1_keep_pres regs1 regs2 HPRES2)|].
    apply l1_keep_cl1. exact HK3.
  - subst nF n'. rewrite HLn. lia.
  - subst ovF ov' n'. rewrite HLn.
    destruct (Z.leb_spec (n + (Z.of_nat (length t') + 1)) 23) as [Ha | Ha];
    destruct (Z.leb_spec (n + 1) 23) as [Hb | Hb];
    destruct (Z.leb_spec (Z.min (n + 1) 23 + Z.of_nat (length t')) 23) as [Hd | Hd];
    try reflexivity; try lia.
  - subst wrF wr' n'. destruct (Z_le_gt_dec n 22) as [Hle | Hgt].
    + replace (Z.to_nat (23 - n)) with (Datatypes.S (Z.to_nat (23 - n - 1))) by lia. cbn [firstn].
      replace (Z.min (n + 1) 23) with (n + 1) by lia.
      replace (Z.to_nat (23 - (n + 1))) with (Z.to_nat (23 - n - 1)) by lia.
      rewrite firstn_nil, <- app_assoc. reflexivity.
    + replace (Z.to_nat (23 - n)) with 0%nat by lia. cbn [firstn].
      replace (Z.min (n + 1) 23) with 23 by lia.
      replace (Z.to_nat (23 - 23)) with 0%nat by lia. cbn [firstn].
      rewrite !app_nil_r. reflexivity. }
Qed.
Lemma l1_start : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc
  (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (P D n0 ov0 : Z) (s : list Z) (nF ovF : Z) (wrF : list Z),
  rbn_lcx B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ->
  rbn_lrec B STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 152) D 24 n0 ov0 ->
  rbn_lbuf B STK sp0 FP ly S own lyc Sc W memc (spZ regs) (spZ regs + 152) D 24 ->
  s <> [] -> Forall (fun c => 0 < c < 256) s -> rbn_lsrc W memc P (s ++ [0]) ->
  rbn_lsep (spZ regs) (spZ regs + 152) D 24 P (Z.of_nat (length s) + 1) ->
  0 <= n0 <= 23 -> (ov0 = 0 \/ ov0 = 1) ->
  getr regs 10 = w64 (hd 0 s) -> getr regs 21 = w64 P -> getr regs 26 = w64 (P + 1) ->
  getr regs 24 = w64 (-1) ->
  nF = Z.min (n0 + Z.of_nat (length s)) 23 ->
  ovF = (if n0 + Z.of_nat (length s) <=? 23 then ov0 else 1) ->
  wrF = firstn (Z.to_nat (23 - n0)) s ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + RBN_L1) regs memc mdc)
    (rbn_lpost B fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L1X rbn_cl1
       (spZ regs + 152) D n0 nF ovF wrF).
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s nF ovF wrF
  HCX HREC HBUF Hs0 Htb HSRC HSEP Hn0 Hov0 H10 H21 H26 H24 HnF HovF HwrF.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof HCX as (HJ0 & HRO0 & Hgp & Htp & H9 & H22 & Hal16 & Hwlo & Hwhi).
pose proof HREC as (HR0 & HR8 & HR63 & HRam & HRimg & HRside & HDr0 & HDrcap & HnA & HnB & HovA &
  VD & Vcap & Vn0m & Vov0m & HRra & HRhull & HRwr).
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 &
  (Hsp0al & Hstk0 & Hceil0 & Hslo0 & Hshi0 & H47a & Hbot0 & Htop0 & Htop0b) & _).
assert (HTS : TSB_CH_STK = 4112) by reflexivity.
assert (Hwin : forall a, spZ regs - TSB_CH_STK <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
assert (Hhd : 0 < hd 0 s < 256)
  by (destruct s as [|c0 s0]; [exfalso; exact (Hs0 eq_refl)|]; cbn [hd]; inversion Htb; assumption).
pose proof (l1_pre_entry fq W regs memc) as HS.
pose proof (EY_img regs []) as HEI.
assert (SHOK : sh_ok SEGS (SOff 22 0) [] (EY regs []) (mrestrict (w_H W) memc)) by apply Forall_nil.
pose (RUN := paj_run (fx := fq) B LAWS).
assert (E9 : ew (EY regs []) 9 = getr regs 2)
  by (rewrite (EY_reg regs _ 9%nat 9%bv) by (first [lia | vm_compute; reflexivity]); exact H9).
assert (E10 : ew (EY regs []) 10 = w64 (hd 0 s))
  by (rewrite (EY_reg regs _ 10%nat 10%bv) by (first [lia | vm_compute; reflexivity]); exact H10).
assert (E21 : ew (EY regs []) 21 = w64 P)
  by (rewrite (EY_reg regs _ 21%nat 21%bv) by (first [lia | vm_compute; reflexivity]); exact H21).
assert (E26 : ew (EY regs []) 26 = w64 (P + 1))
  by (rewrite (EY_reg regs _ 26%nat 26%bv) by (first [lia | vm_compute; reflexivity]); exact H26).
assert (E24 : ew (EY regs []) 24 = w64 (-1))
  by (rewrite (EY_reg regs _ 24%nat 24%bv) by (first [lia | vm_compute; reflexivity]); exact H24).
assert (E22 : ew (EY regs []) 22 = w64 SHADOW_OFF)
  by (rewrite (EY_reg regs _ 22%nat 22%bv) by (first [lia | vm_compute; reflexivity]); exact H22).
unfold cfg_at, w64. rewrite <- Z.add_assoc.
paj_run_tok RUN HS HJ0 SHOK Bspan.
{ awr_ok_tac. }
assert (KEEPR0 : forall a, aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memc a).
{ cbn [ms_mem mkst] in HFr. eapply l1_aview_ro; [|exact HFr]. l1_ro_regs. }
assert (KEPT0 : tsb_ch_kept B lyc Sc W memc W (ms_mem ms) (spZ regs)
  (fun a => spZ regs + 152 + 16 <= a < spZ regs + 152 + 28 \/
            D + n0 <= a < D + n0 + Z.of_nat (length wrF))).
{ apply (l1_kept_run lyc Sc W memc W memc (ms_mem ms) (spZ regs) _
    (tsb_ch_kept_refl B lyc Sc W memc (spZ regs) _ Hwin) KEEPR0).
  cbn [ms_mem mkst] in HG. exact HG. }
pose proof (regs_kept_of_st_ok _ _ _ _ regs (map w64 []) l1_kept_regs HS
  ltac:(env_agree_chain (EY_agree regs [])) ltac:(vm_compute; reflexivity)) as HK1.
cbn [ms_regs restrict] in HK1.
prreg HS (1%bv : bv 5) R1. prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11.
prreg HS (21%bv : bv 5) R21. prreg HS (26%bv : bv 5) R26.
prreg HS (22%bv : bv 5) R22. prreg HS (24%bv : bv 5) R24.
pmkst HS. rewrite pa_sigma_sb_ch.
apply (l1_core (length s) fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s
  lyc Sc W (ms_mem ms) _ (ms_regs ms) P s n0 ov0 [] nF ovF wrF).
- exact HCX.
- exact HREC.
- exact HBUF.
- exact HSRC.
- exact HSEP.
- exact Hn0.
- lia.
- exact Hs0.
- exact Htb.
- lia.
- lia.
- exact (proj1 HSRC).
- exact HJ0.
- exact (l1_rod lyc Sc W memc W (ms_mem ms) (spZ regs) _ KEPT0 HRO0).
- reflexivity.
- reflexivity.
- exact KEPT0.
- apply (l1_vk (w_H W) (w_H W) memc (ms_mem ms)); [intros x Hx; apply KEEPR0 | exact Vn0m].
- apply (l1_vk (w_H W) (w_H W) memc (ms_mem ms)); [intros x Hx; apply KEEPR0 | exact Vov0m].
- apply garr8_nil.
- cbn [length]. lia.
- lia.
- exact Hov0.
- rewrite R1. unfold w64, AF_both3_reac_box_name. f_equal; lia.
- rewrite (HK1 2%bv ltac:(unfold l1_kept_regs; cbn [In]; repeat (first [left; reflexivity | right]))).
  reflexivity.
- rewrite (HK1 3%bv ltac:(unfold l1_kept_regs; cbn [In]; repeat (first [left; reflexivity | right]))).
  exact Hgp.
- rewrite (HK1 4%bv ltac:(unfold l1_kept_regs; cbn [In]; repeat (first [left; reflexivity | right]))).
  exact Htp.
- rewrite (HK1 9%bv ltac:(unfold l1_kept_regs; cbn [In]; repeat (first [left; reflexivity | right]))).
  exact H9.
- rewrite R10, E9. unfold w64, spZ. reflexivity.
- rewrite R11. exact (l1_and255 _ (hd 0 s) E10 ltac:(lia)).
- rewrite R21. exact E21.
- rewrite R22. exact E22.
- rewrite R24. exact E24.
- rewrite R26. exact E26.
- apply l1_keep_cl1. exact HK1.
- exact HnF.
- exact HovF.
- rewrite HwrF. reflexivity.
Qed.
Theorem rbn_l1_fits : rbn_L1_fits B.
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s Hlen.
unfold rbn_L1_run. intros HCX HREC HBUF Hs0 Htb HSRC HSEP Hn0 Hov0 H10 H21 H26 H24.
apply (l1_start fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s
  (n0 + Z.of_nat (length s)) ov0 s HCX HREC HBUF Hs0 Htb HSRC HSEP Hn0 Hov0 H10 H21 H26 H24).
- symmetry. apply Z.min_l. lia.
- replace (n0 + Z.of_nat (length s) <=? 23) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
- symmetry. apply firstn_all2. lia.
Qed.
Theorem rbn_l1_ovf : rbn_L1_ovf B.
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s Hlen.
unfold rbn_L1_run. intros HCX HREC HBUF Hs0 Htb HSRC HSEP Hn0 Hov0 H10 H21 H26 H24.
apply (l1_start fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s
  23 1 (firstn (Z.to_nat (23 - n0)) s) HCX HREC HBUF Hs0 Htb HSRC HSEP Hn0 Hov0 H10 H21 H26 H24).
- symmetry. apply Z.min_r. lia.
- replace (n0 + Z.of_nat (length s) <=? 23) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
- reflexivity.
Qed.
End h.
End f.
End d.
