(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyImg_zone3.v (commit eb934de95d13, blob 7206be6e27d2) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AF0l AF0m AF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG08cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseAGS.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import AGif4. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AGImgSA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AGjm.

From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Local Lemma z3_aview_same : forall segs (H : word -> bool) (mem mem' : word -> option byte) a,
  mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a) -> aview segs H mem' a = aview segs H mem a.
Proof. intros segs H mem mem' a E. unfold aview, mbyte, mrestrict. rewrite E. reflexivity. Qed.

Local Lemma z3_bv64_small : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a.
Proof.
intros a Ha. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
apply Z.mod_small. exact Ha.
Qed.

Local Lemma z3_cell_holds_agree : forall B ly (rd rd' : reader) c,
  (forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> rd' (aeval B ly (c_at c) + k) = rd (aeval B ly (c_at c) + k)) ->
  cell_holds B ly rd c -> cell_holds B ly rd' c.
Proof.
intros B ly rd rd' c He Hc. unfold cell_holds in *. destruct (c_val c) as [e|m vv].
- intros k Hk. rewrite He by lia. exact (Hc k Hk).
- destruct Hc as (b & Hb & Hm). exists b. split; [|exact Hm].
  rewrite <- (Z.add_0_r (aeval B ly (c_at c))). rewrite He by lia. rewrite Z.add_0_r. exact Hb.
Qed.

Local Lemma z3_pw_ij {X : Type} (R : X -> X -> Prop) : forall l i j x y, pairwise R l ->
  nth_error l i = Some x -> nth_error l (i + S j) = Some y -> R x y.
Proof.
induction l as [|h t IH]; intros i j x y P Hx Hy; [destruct i; discriminate|].
destruct P as [F P]. destruct i as [|i]; cbn in Hx, Hy.
- injection Hx as <-. apply (proj1 (Forall_forall _ _) F). exact (nth_error_In _ _ Hy).
- exact (IH i j x y P Hx Hy).
Qed.

Local Lemma z3_pw_app {X : Type} (R : X -> X -> Prop) : forall l1 l2 x y, pairwise R (l1 ++ l2) ->
  In x l1 -> In y l2 -> R x y.
Proof.
induction l1 as [|h t IH]; intros l2 x y P Hx Hy; [destruct Hx|].
destruct P as [F P]. destruct Hx as [<-|Hx].
- apply (proj1 (Forall_forall _ _) F). apply in_or_app. right. exact Hy.
- exact (IH l2 x y P Hx Hy).
Qed.

Local Lemma z3_orb_le : forall a b c d, ((a <=? b) || (c <=? d))%bool = true -> a <= b \/ c <= d.
Proof. intros a b c d H. apply Bool.orb_prop in H as [H|H]; apply Z.leb_le in H; [left|right]; exact H. Qed.

Local Lemma z3_val0 : forall v, match v with AV (ANum 0) => true | _ => false end = true -> v = AV (ANum 0).
Proof.
intros v H. destruct v as [e|m w]; [|discriminate H]. destruct e; try discriminate H.
lazymatch goal with |- AV (ANum ?zz) = _ => destruct zz; try discriminate H; reflexivity end.
Qed.

Fixpoint z3_pwb (l : list (Z * Z)) : bool :=
  match l with
  | [] => true
  | x :: t => forallb (fun y => (fst x + snd x <=? fst y) || (fst y + snd y <=? fst x))%bool t && z3_pwb t
  end.
Local Lemma z3_pwb_ok : forall l, z3_pwb l = true -> pairwise zdisjoint l.
Proof.
induction l as [|x t IH]; intros H; cbn [z3_pwb pairwise] in *; [exact I|].
apply andb_prop in H as [H1 H2]. split; [|exact (IH H2)].
apply Forall_forall. intros y Hy. pose proof (proj1 (forallb_forall _ _) H1 y Hy) as Hb. cbv beta in Hb.
unfold zdisjoint. exact (z3_orb_le _ _ _ _ Hb).
Qed.

Definition z3_cells_at (w : nat) (v : Z) (l : list acell) : list Z :=
  flat_map (fun c => match c with
    | ACell (ANum a) w' (AV (ANum v')) => if (Nat.eqb w' w && Z.eqb v' v)%bool then [a] else []
    | _ => [] end) l.
Local Lemma z3_cells_at_In : forall w v l a, In (ACell (ANum a) w (AV (ANum v))) l -> In a (z3_cells_at w v l).
Proof.
intros w v l a H. unfold z3_cells_at. apply in_flat_map. exists (ACell (ANum a) w (AV (ANum v))).
split; [exact H|]. cbv beta iota. rewrite Nat.eqb_refl, Z.eqb_refl. cbn. left. reflexivity.
Qed.

Local Lemma z3_msv : forall n, 64513 <= n < 2 ^ 30 -> 73728 <= ImgBaseAGS.MSv n <= 262147 * 4096.
Proof.
intros n Hn. unfold ImgBaseAGS.MSv, ImgBaseAGS.NDv, ImgBaseAGS.R8v.
pose proof (Z.div_mod (n + 7) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)) as M1.
set (q := (n + 7) / 8) in *.
pose proof (Z.div_mod (q * 8 + 4096 + 4095) 4096 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (q * 8 + 4096 + 4095) 4096 ltac:(lia)) as M2.
set (p := (q * 8 + 4096 + 4095) / 4096) in *.
lia.
Qed.
Local Lemma z3_bsl_range : forall (regs0 : bvmap 5 word) n, 64513 <= n < 2 ^ 30 ->
  bv_unsigned (getr regs0 11) + 296 <= ImgBaseAGS.BSLv regs0 n /\
  ImgBaseAGS.BSLv regs0 n + 8 <= bv_unsigned (getr regs0 11) + 416.
Proof.
intros regs0 n Hn. pose proof (z3_msv n Hn) as M.
unfold ImgBaseAGS.BSLv, ImgBaseAGS.LGv. cbv zeta.
assert (Q : 18 <= ImgBaseAGS.MSv n / 4096 <= 262147)
  by (split; [apply Z.div_le_lower_bound | apply Z.div_le_upper_bound]; lia).
pose proof (Z.log2_le_mono (ImgBaseAGS.MSv n / 4096) 262147 ltac:(lia)) as L2.
rewrite (eq_refl : Z.log2 262147 = 18) in L2.
pose proof (Z.log2_le_mono 18 (ImgBaseAGS.MSv n / 4096) ltac:(lia)) as L1.
rewrite (eq_refl : Z.log2 18 = 4) in L1.
lia.
Qed.

Lemma areas_disj_A : forall B, @im_syms AImg_A B -> pairwise zdisjoint (asyms_areas B).
Proof.
intros B TS. change (TfibSyms B) in TS.

destruct (aso_const_law B (ts_ok B TS) (ALayout 0 0 0 0 0 0 0 0 0 0 0 0 [] [] 0 [] (0, 0) (fun _ => 0)))
  as (L1 & L2 & L3 & L4).
rewrite (ts_const B TS) in L1, L2, L3, L4. unfold Tfib_const, z8, z4, c8, c4 in L1, L2, L3, L4.
apply z3_cells_at_In in L1. apply z3_cells_at_In in L2. apply z3_cells_at_In in L3. apply z3_cells_at_In in L4.
unfold asyms_areas.
rewrite (ts_inst B TS), (ts_depot B TS), (ts_store B TS), (ts_ial_lo B TS), (ts_ial_hi B TS), (ts_ial_flag B TS),
  (ts_oom B TS), (ts_tp B TS).
revert L1 L2 L3 L4.
generalize (as_got_uar B) as gu. generalize (as_got_shadow B) as gs.
generalize (as_uar_cell B) as uc. generalize (as_shadow_cell B) as sc.
clear TS B. intros sc uc gs gu L1 L2 L3 L4.
lazymatch type of L1 with In _ ?l =>
  let l' := eval vm_compute in l in replace l with l' in L1 by (vm_compute; reflexivity) end.
cbn [In] in L1. destruct L1 as [<-|[]].
lazymatch type of L2 with In _ ?l =>
  let l' := eval vm_compute in l in replace l with l' in L2 by (vm_compute; reflexivity) end.
cbn [In] in L2. destruct L2 as [<-|[]].
lazymatch type of L3 with In _ ?l =>
  let l' := eval vm_compute in l in replace l with l' in L3 by (vm_compute; reflexivity) end.
cbn [In] in L3. destruct L3 as [<-|[]].
lazymatch type of L4 with In _ ?l =>
  let l' := eval vm_compute in l in replace l with l' in L4 by (vm_compute; reflexivity) end.
cbn [In] in L4. destruct L4 as [<-|[]].
apply z3_pwb_ok. vm_compute. reflexivity.
Qed.

Definition z3_nj_b (c : acell) : bool :=
match c_at c with
| ANum a => let e := a + Z.max 1 (Z.of_nat (c_w c)) in
  ((TFIB_IMG_LO <=? a) && (e <=? TFIB_IMG_END) &&
   ((e <=? TFIB_INST + o_sec_sorted) || (TFIB_INST + o_sec_sorted + 1 <=? a)) &&
   ((e <=? TFIB_INST + o_sec_stats) || (TFIB_INST + o_sec_stats + 32 <=? a)) &&
   ((e <=? TFIB_INST + 296) || (TFIB_INST + 416 <=? a)) &&
   ((e <=? TFIB_INST + o_comb_stats) || (TFIB_INST + o_comb_stats + 40 <=? a)) &&
   ((e <=? TFIB_OOM) || (TFIB_OOM + 1 <=? a)))
  || ((kLowShadowBeg <=? a) && (e <=? kHighMemBeg))
| _ => false
end.
Local Lemma z3_nj_abs : forallb z3_nj_b (Tfib_const_abs ++ Tfib_const_shadow) = true.
Proof. vm_compute. reflexivity. Qed.

Definition z3_nj_zone (ly : alayout) (a : Z) : Prop :=
  (TFIB_IMG_LO <= a < TFIB_IMG_END /\ (a < TFIB_INST + o_sec_sorted \/ TFIB_INST + o_sec_sorted + 1 <= a) /\
   (a < TFIB_INST + o_sec_stats \/ TFIB_INST + o_sec_stats + 32 <= a) /\ (a < TFIB_INST + 296 \/ TFIB_INST + 416 <= a) /\
   (a < TFIB_INST + o_comb_stats \/ TFIB_INST + o_comb_stats + 40 <= a) /\ a <> TFIB_OOM) \/
  (kLowShadowBeg <= a < kHighMemBeg) \/ (ly_T ly <= a < ly_T ly + 80) \/
  (ly_C ly <= a < ly_C ly + 256) \/ (ly_D ly <= a < ly_D ly + 4096).

Section rows. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams}.

Lemma zone3_A : forall ly x sz, @im_img_cover AImg_A ly -> 0 <= sz -> in_app x sz -> zdisjoint (x, sz) (ly_img ly) ->
  ims_zone3 (AImgS := AImgS_A) x sz.
Proof. intros ly x sz C Hs A D. exact (zone3_intro ly x sz C Hs A D). Qed.

Local Lemma z3_ext_zone3 : forall ly i e, layout_ok ly -> img_cover ly -> nth_error (owned_extents ly) i = Some e ->
  0 <= snd e -> zone3 (fst e) (snd e).
Proof.
intros ly i e LY IMG He SZ.
pose proof (proj1 (Forall_forall _ _) (lo_app ly LY) e (nth_error_In _ _ He)) as IA. cbv beta in IA.
assert (D : zdisjoint e (ly_img ly)).
{ refine (z3_pw_app zdisjoint (owned_extents ly) [(ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly); ly_img ly] e (ly_img ly)
    (lo_disj ly LY) (nth_error_In _ _ He) _).
  right. left. reflexivity. }
destruct e as [x sz]. exact (zone3_intro ly x sz IMG SZ IA D).
Qed.

Local Lemma z3_czs_img : forall ly inst x, 0x10000 <= x < ims_img_end (AImgS := AImgS_A) ->
  (x < inst + o_sec_reserved \/ inst + o_sec_sorted + 1 <= x) -> (x < inst + o_sec_stats \/ inst + o_sec_stats + 32 <= x) ->
  (x < inst + 296 \/ inst + 408 <= x) -> (x < inst + o_sec_mutex \/ inst + o_sec_mutex + 4 <= x) ->
  (x < inst + o_comb_stats \/ inst + o_comb_stats + 40 <= x) -> CZS (IM := AImg_A) (IMS := AImgS_A) ly inst x.
Proof.
intros ly inst x Hx H1 H2 H3 H4 H5. unfold CZS. left.
unfold o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, o_comb_stats in *.
destruct (Z_lt_le_dec x (inst + 112)) as [L|G1]; [left; clear - Hx L; lia|].
destruct H1 as [H1|H1]; [clear - G1 H1; lia|].
destruct (Z_lt_le_dec x (inst + 136)) as [L|G2]; [right; left; clear - H1 L; lia|].
destruct H2 as [H2|H2]; [clear - G2 H2; lia|].
destruct (Z_lt_le_dec x (inst + 296)) as [L|G3]; [do 2 right; left; clear - H2 L; lia|].
destruct H3 as [H3|H3]; [clear - G3 H3; lia|].
destruct (Z_lt_le_dec x (inst + 680)) as [L|G4]; [do 3 right; left; clear - H3 L; lia|].
destruct H4 as [H4|H4]; [clear - G4 H4; lia|].
destruct (Z_lt_le_dec x (inst + 688)) as [L|G5]; [do 4 right; left; clear - H4 L; lia|].
destruct H5 as [H5|H5]; [clear - G5 H5; lia|].
do 5 right. clear - Hx H5. lia.
Qed.

Definition z3_keep_b (c : acell) : bool :=
match c_at c with
| ANum a => let e := a + Z.max 1 (Z.of_nat (c_w c)) in
  ((0x10000 <=? a) && (e <=? ims_img_end (AImgS := AImgS_A)) &&
   ((e <=? TFIB_INST + o_sec_reserved) || (TFIB_INST + o_sec_sorted + 1 <=? a)) &&
   ((e <=? TFIB_INST + o_sec_stats) || (TFIB_INST + o_sec_stats + 32 <=? a)) &&
   ((e <=? TFIB_INST + 296) || (TFIB_INST + 408 <=? a)) &&
   ((e <=? TFIB_INST + o_sec_mutex) || (TFIB_INST + o_sec_mutex + 4 <=? a)) &&
   ((e <=? TFIB_INST + o_comb_stats) || (TFIB_INST + o_comb_stats + 40 <=? a)))
  || ((ims_shb (AImgS := AImgS_A) <=? a) && (e <=? ims_csh_end (AImgS := AImgS_A)))
  || ((TFIB_INST + o_sec_mutex + 1 <=? a) && (e <=? TFIB_INST + o_sec_mutex + 4) &&
      match c_val c with AV (ANum 0) => true | _ => false end)
| _ => false
end.
Local Lemma z3_keep_abs : forallb z3_keep_b (Tfib_const_abs ++ Tfib_const_shadow) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma const_keep_s_A : forall B, @im_syms AImg_A B ->
  forall ly (H : word -> bool) (mem0 mem : word -> option byte),
  layout_ok ly -> @im_img_cover AImg_A ly -> ly_tsd ly = as_tsd B ->
  Forall (cell_holds B ly (aview (@im_segs AImg_A) H mem0)) (as_const B ly) ->
  (forall x : word, ims_dzone (AImgS := AImgS_A) ly (bv_unsigned x) \/
     CZS (IM := AImg_A) (IMS := AImgS_A) ly (as_inst B) (bv_unsigned x) -> mem x = mem0 x) ->
  (forall k, 1 <= k < 4 -> aview (@im_segs AImg_A) H mem (as_inst B + o_sec_mutex + k) = Some 0) ->
  Forall (cell_holds B ly (aview (@im_segs AImg_A) H mem)) (as_const B ly).
Proof.
intros B TS ly H mem0 mem LY IMG HTSD HC KEEP MUT. change (TfibSyms B) in TS. change (img_cover ly) in IMG.
pose proof (ts_inst B TS) as EIN. pose proof (ts_tp B TS) as ETP. rewrite (ts_tsd B TS) in HTSD.
rewrite EIN in KEEP, MUT.
assert (KB : forall a, 0 <= a < 2 ^ 64 -> CZS (IM := AImg_A) (IMS := AImgS_A) ly TFIB_INST a ->
  aview (@im_segs AImg_A) H mem a = aview (@im_segs AImg_A) H mem0 a).
{ intros a Ra Ca. apply z3_aview_same. apply KEEP. right. rewrite (z3_bv64_small a Ra). exact Ca. }
pose proof (z3_ext_zone3 ly 2 (ly_T ly, kThreadObjSize) LY IMG eq_refl ltac:(cbn [snd]; unfold kThreadObjSize; lia)) as ZT.
pose proof (z3_ext_zone3 ly 6 (ly_C ly, 256) LY IMG eq_refl ltac:(cbn [snd]; lia)) as ZC.
pose proof (z3_ext_zone3 ly 7 (ly_D ly, 4096) LY IMG eq_refl ltac:(cbn [snd]; lia)) as ZD.
cbn [fst snd] in ZT, ZC, ZD.
destruct ZT as (ZT1 & ZT2 & _). destruct ZC as (ZC1 & ZC2 & _). destruct ZD as (ZD1 & ZD2 & _).
unfold kThreadObjSize in ZT2. pose proof (@ASAN_CEIL_range rc) as [CR _].
apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) HC c Hc) as HOLD.
rewrite (ts_const B TS ly) in Hc. unfold Tfib_const in Hc. apply in_app_iff in Hc as [Hc|Hc].
-
  clear KEEP MUT HC.
  apply (z3_cell_holds_agree B ly (aview (@im_segs AImg_A) H mem0)); [|exact HOLD]. clear HOLD.
  unfold Tfib_const_sym in Hc. cbn [In] in Hc.
  repeat match type of Hc with
  | _ \/ _ => destruct Hc as [<-|Hc];
    [intros k Hk; cbn [c_at c_w aeval z8 z4 z1 c8 c4 c1] in *; cbn in Hk; rewrite ?EIN, ?ETP, ?HTSD;
     apply KB;
     [ unfold TFIB_INST, TFIB_TP, TFIB_TSD, o_space, o_rinfo, o_sec_chunks in *; lia
     | unfold CZS; cbn [im_tsd ims_img_end AImg_A AImgS_A];
       unfold TFIB_INST, TFIB_TP, TFIB_TSD, o_space, o_rinfo, o_sec_chunks, o_sec_reserved, o_comb_stats in *;
       first [ right; right; left; lia | do 3 right; left; lia | do 4 right; left; lia | do 5 right; lia
             | left; left; lia | left; do 5 right; lia ] ]
    |]
  | False => destruct Hc
  end.
-
  pose proof (proj1 (forallb_forall _ _) z3_keep_abs c Hc) as Hb. unfold z3_keep_b in Hb.
  destruct (c_at c) eqn:Ea; try discriminate Hb. cbv zeta in Hb.
  apply Bool.orb_prop in Hb as [Hb|Hb]; [apply Bool.orb_prop in Hb as [Hb|Hb]|].
  + apply (z3_cell_holds_agree B ly (aview (@im_segs AImg_A) H mem0)); [|exact HOLD].
    rewrite Ea. cbn [aeval]. intros k Hk.
    apply andb_prop in Hb as [Hb W5]. apply andb_prop in Hb as [Hb W4]. apply andb_prop in Hb as [Hb W3].
    apply andb_prop in Hb as [Hb W2]. apply andb_prop in Hb as [Hb W1]. apply andb_prop in Hb as [Hb W0].
    apply Z.leb_le in Hb. apply Z.leb_le in W0.
    apply z3_orb_le in W1. apply z3_orb_le in W2. apply z3_orb_le in W3. apply z3_orb_le in W4. apply z3_orb_le in W5.
    apply KB.
    * pose proof W0 as W0'. cbn [ims_img_end AImgS_A] in W0'. lia.
    * apply z3_czs_img; [lia | | | | |].
      -- destruct W1 as [W|W]; [left|right]; lia.
      -- destruct W2 as [W|W]; [left|right]; lia.
      -- destruct W3 as [W|W]; [left|right]; lia.
      -- destruct W4 as [W|W]; [left|right]; lia.
      -- destruct W5 as [W|W]; [left|right]; lia.
  + apply (z3_cell_holds_agree B ly (aview (@im_segs AImg_A) H mem0)); [|exact HOLD].
    rewrite Ea. cbn [aeval]. intros k Hk.
    apply andb_prop in Hb as [S1 S2]. apply Z.leb_le in S1. apply Z.leb_le in S2.
    apply KB.
    * cbn [ims_shb ims_csh_end AImgS_A] in S1, S2. unfold AGjm.SHBv in S1. lia.
    * unfold CZS. right. left. lia.
  + apply andb_prop in Hb as [Hb V0]. apply andb_prop in Hb as [P1 P2]. apply Z.leb_le in P1. apply Z.leb_le in P2.
    apply z3_val0 in V0.
    unfold cell_holds. rewrite Ea, V0. cbn [aeval]. intros k Hk.
    replace (z + Z.of_nat k) with (TFIB_INST + o_sec_mutex + (z + Z.of_nat k - (TFIB_INST + o_sec_mutex))) by lia.
    rewrite MUT by (unfold o_sec_mutex in *; lia).
    f_equal. unfold YG0f.le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity.
Qed.

Lemma const_not_junk_A : forall B, @im_syms AImg_A B ->
  forall ly (regs0 : bvmap 5 word) n c k, layout_ok ly -> @im_img_cover AImg_A ly -> ly_tsd ly = as_tsd B ->
  bv_unsigned (getr regs0 11) = as_inst B -> 64513 <= n < cf_malloc_max ->
  In c (as_const B ly) -> 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
  ~ ((ly_T ly + 2768 <= aeval B ly (c_at c) + k < ly_T ly + 2824) \/
     (ly_T ly + 2872 <= aeval B ly (c_at c) + k < ly_T ly + 2888) \/
     (ly_T ly + 2904 <= aeval B ly (c_at c) + k < ly_T ly + 2912) \/
     (as_inst B + o_sec_sorted <= aeval B ly (c_at c) + k < as_inst B + o_sec_sorted + 1) \/
     (as_inst B + o_sec_stats <= aeval B ly (c_at c) + k < as_inst B + o_sec_stats + 32) \/
     (ImgBaseAGS.BSLv regs0 n <= aeval B ly (c_at c) + k < ImgBaseAGS.BSLv regs0 n + 8) \/
     (as_inst B + o_comb_stats <= aeval B ly (c_at c) + k < as_inst B + o_comb_stats + 40) \/
     aeval B ly (c_at c) + k = as_oom_byte B).
Proof.
intros B TS ly regs0 n c k LY IMG HTSD Hinst Hn Hc Hk. change (TfibSyms B) in TS. change (img_cover ly) in IMG.
pose proof (ts_inst B TS) as EIN. pose proof (ts_tp B TS) as ETP. pose proof (ts_oom B TS) as EOOM.
rewrite (ts_tsd B TS) in HTSD.
pose proof (@YG08cf.cf_malloc_max_bound cp) as CMB.
pose proof (z3_bsl_range regs0 n ltac:(lia)) as BS. rewrite Hinst, EIN in BS.
pose proof (z3_ext_zone3 ly 2 (ly_T ly, kThreadObjSize) LY IMG eq_refl ltac:(cbn [snd]; unfold kThreadObjSize; lia)) as ZT.
pose proof (z3_ext_zone3 ly 6 (ly_C ly, 256) LY IMG eq_refl ltac:(cbn [snd]; lia)) as ZC.
pose proof (z3_ext_zone3 ly 7 (ly_D ly, 4096) LY IMG eq_refl ltac:(cbn [snd]; lia)) as ZD.
cbn [fst snd] in ZT, ZC, ZD.
pose proof (z3_pw_ij zdisjoint (static_extents ly) 2 3 (ly_T ly, kThreadObjSize) (ly_C ly, 256) (lo_disj ly LY) eq_refl eq_refl)
  as DTC.
pose proof (z3_pw_ij zdisjoint (static_extents ly) 2 4 (ly_T ly, kThreadObjSize) (ly_D ly, 4096) (lo_disj ly LY) eq_refl eq_refl)
  as DTD.
unfold zdisjoint in DTC, DTD. cbn [fst snd] in DTC, DTD.
assert (ZN : z3_nj_zone ly (aeval B ly (c_at c) + k)).
{ rewrite (ts_const B TS ly) in Hc. unfold Tfib_const in Hc. apply in_app_iff in Hc as [Hc|Hc].
  - unfold Tfib_const_sym in Hc. cbn [In] in Hc.
    clear - Hc Hk EIN ETP HTSD.
    repeat match type of Hc with
    | _ \/ _ => destruct Hc as [<-|Hc];
      [cbn [c_at c_w aeval z8 z4 z1 c8 c4 c1] in *; cbn in Hk; rewrite ?EIN, ?ETP, ?HTSD;
       unfold z3_nj_zone, TFIB_IMG_LO, TFIB_IMG_END, TFIB_INST, TFIB_TP, TFIB_TSD, TFIB_OOM, o_space, o_rinfo,
         o_sec_chunks, o_sec_sorted, o_sec_stats, o_comb_stats;
       first [ do 2 right; left; lia | do 3 right; left; lia | do 4 right; lia | left; lia ]
      |]
    | False => destruct Hc
    end.
  - pose proof (proj1 (forallb_forall _ _) z3_nj_abs c Hc) as Hb. unfold z3_nj_b in Hb.
    destruct (c_at c) eqn:Ea; try discriminate Hb. cbv zeta in Hb. cbn [aeval].
    apply Bool.orb_prop in Hb as [Hb|Hb].
    + apply andb_prop in Hb as [Hb W5]. apply andb_prop in Hb as [Hb W4]. apply andb_prop in Hb as [Hb W3].
      apply andb_prop in Hb as [Hb W2]. apply andb_prop in Hb as [Hb W1]. apply andb_prop in Hb as [Hb W0].
      apply Z.leb_le in Hb. apply Z.leb_le in W0.
      apply z3_orb_le in W1. apply z3_orb_le in W2. apply z3_orb_le in W3. apply z3_orb_le in W4. apply z3_orb_le in W5.
      unfold z3_nj_zone. left.
      split; [lia|]. split; [destruct W1 as [W|W]; [left|right]; lia|].
      split; [destruct W2 as [W|W]; [left|right]; lia|]. split; [destruct W3 as [W|W]; [left|right]; lia|].
      split; [destruct W4 as [W|W]; [left|right]; lia|]. destruct W5 as [W|W]; lia.
    + apply andb_prop in Hb as [S1 S2]. apply Z.leb_le in S1. apply Z.leb_le in S2.
      unfold z3_nj_zone. right. left. lia. }
rewrite EIN, EOOM. set (a := aeval B ly (c_at c) + k) in *. clearbody a.
pose proof (zone3_apart_img _ _ a ZT) as TI. pose proof (zone3_apart_hsh _ _ a ZT) as TH.
pose proof (zone3_apart_img _ _ a ZC) as CI. pose proof (zone3_apart_img _ _ a ZD) as DI.
unfold z3_nj_zone in ZN.
clear - ZN TI TH CI DI DTC DTD BS.
unfold TFIB_IMG_LO, TFIB_IMG_END, TFIB_INST, TFIB_OOM, o_sec_sorted, o_sec_stats, o_comb_stats, kThreadObjSize,
  kLowShadowBeg, kHighMemBeg in *.
intros J.
destruct ZN as [(Z1 & Z2 & Z3 & Z4 & Z5 & Z6) | [Z1 | [Z1 | [Z1 | Z1]]]];
destruct J as [J|[J|[J|[J|[J|[J|[J|J]]]]]]]; lia.
Qed.

End rows.
