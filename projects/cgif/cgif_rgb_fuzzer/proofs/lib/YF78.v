(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0h YG10 YG0u YG0d YG0f YG0y YG0w.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF8t YE0v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YA00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF0g YF8y YF0f YF8m YF40.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF0k YF0q YF0o YF1a YF1w YF21 YF1z YF0n YF22 YF0m YF24 YF1m.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF6q YF6v YF6z YF7a YF79 YF6s YF6o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF07 YF68 YF67 YF6b YF6i YF6j YF6e YF6a YF6h YF6f YF6p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac img_facts ::= lazymatch goal with k : img |- _ => let F := fresh "IMGF" in pose proof (P_facts k) as F end.
Ltac img_lia ::=
first [ (img_goal_has_k; img_facts; lia)
| lia
| (img_inst; lia)
| (try img_inst;
first [ (img_local; img_local_unfold; img_unfold_all; lia)
| (img_arith_rel; first [ (img_facts; lia)
| (img_has_moddiv; img_case; img_unfold_all; lia)
| (first [ img_has_moddiv | img_has_match ]; img_concrete; img_unfold_all; lia) ]) ]) ].
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma aowned_s1 : forall B ly S a, aowned B ly (realloc_s1 S) a <-> aowned B ly S a.
Proof. intros B ly S a. unfold realloc_s1, aowned, aclient_byte, sec_extents, frames. cbn. tauto. Qed.
Lemma val_mem_slice {imgk : img} : forall (m : word -> option byte) a (w : nat) v (o w' : nat) v',
val_mem tfxsegs m a w v -> (o + w' <= w)%nat -> (forall j, (j < w')%nat -> YG0h.le_byte v' w' j = YG0h.le_byte v w (o + j)) ->
val_mem tfxsegs m (a + Z.of_nat o) w' v'.
Proof.
intros m a w v o w' v' Hv Hw Hle k Hk. replace (a + Z.of_nat o + Z.of_nat k) with (a + Z.of_nat (o + k)) by img_lia.
rewrite (Hv (o + k)%nat ltac:(img_lia)). do 2 f_equal. symmetry. img_exact (Hle k Hk).
Qed.
Lemma pairwise_app_last {imgk : img} : forall {X} (Rr : X -> X -> Prop) l x y, pairwise Rr (l ++ [y]) -> In x l -> Rr x y.
Proof.
intros X Rr l x y. induction l as [|z l IH]; intros HP Hin; [img_try (destruct Hin)|]. cbn [app pairwise] in HP. destruct HP as [HF HP].
destruct Hin as [<-|Hin]; [|img_try (img_exact (IH HP Hin))]. rewrite Forall_forall in HF. img_apply HF. img_apply in_or_app. right. left. img_refl.
Qed.
Lemma aview_rw_some {imgk : img} : forall (Hh : word -> bool) (m : word -> option byte) a, (0xa1000 + D_1000) <= a < (0x5ff000 + D_1000) -> aview tfxsegs Hh m a <> None.
Proof.
intros Hh m a Ha. unfold aview, mbyte. destruct (mrestrict Hh m (Z_to_bv 64 a)); cbn; [img_try (discriminate)|].
pose proof (YF07.tfx_rw_rom a Ha) as X. destruct (seg_rom tfxsegs (Z_to_bv 64 a)); [img_try (cbn; discriminate) | img_try (exfalso; img_exact (X eq_refl))].
Qed.
Lemma errno_not_owned {imgk : img} : forall B, TfxSyms B -> forall ly S (W : world tfxsegs) mem md a, AR tfxsegs B ly S W mem md -> TFX_ERRNO <= a < TFX_ERRNO + 4 -> ~ aowned B ly S a.
Proof.
intros B TS ly S W mem md a HAR Ha O.
assert (IMGa : in_img tfxsegs a).
{ unfold in_img. rewrite YF07.tfx_segs_eq. eexists. split; [img_try (do 3 right; left; img_refl)|]. img_case; cbn; unfold TFX_ERRNO in Ha; img_lia. }
apply (proj1 (AR_owned_image_law_ok tfxsegs B ly S W mem md a HAR IMGa)) in O.
rewrite (ts_owned B TS) in O. unfold Tfx_owned_static in O. apply Exists_exists in O as (r & Hr & [X1 X2]).
cbn [In] in Hr. unfold TFX_ERRNO in Ha.
repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr]; [img_try (cbn [fst snd] in X1, X2; img_lia)|] | False => destruct Hr end.
Qed.
Section h. Context {imgk : img}.
Variable B : asyms.
Hypothesis TB : TfxSyms B.
Variables (ly : alayout) (S : astate) (W : world tfxsegs) (R : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variable ch : list (Z * Z * Z).
Hypothesis PRE : acall_pre tfxsegs B ly S W R mem md ch.
Lemma pre_transport : forall (n0 : nat) ly2 S2 (W2 : world tfxsegs) (mem2 : word -> option byte) md2,
AR tfxsegs B ly2 S2 W2 mem2 md2 -> aregime S2   -> layout_le n0 ly ly2 ->
(forall a, spZ R - ASTACK <= a < spZ R -> apresent (w_H W2) mem2 a) ->
(forall a, spZ R <= a < ly_top ly -> aview tfxsegs (w_H W2) mem2 a = aview tfxsegs (w_H W) mem a) ->
qtight S2 -> acall_pre tfxsegs B ly2 S2 W2 R mem2 md2 ch.
Proof.
intros n0 ly2 S2 W2 mem2 md2 HAR2 Hev2 LLE HPR2 HCH2 HQT2.
destruct PRE as (HAR0 & Hev0 & Hra & Hal & Hlo & Hbot & Hhi & HPRES & Hgp & Htp & Hch & HQT).
destruct LLE as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
unfold acall_pre, ly_bot in *. rewrite ?Etop, ?Eslo, ?Eshi.
split; [img_try (img_exact HAR2)|]. split; [img_try (img_exact Hev2)|]. split; [img_try (img_exact Hra)|]. split; [img_try (img_exact Hal)|]. split; [img_try (img_exact Hlo)|]. split; [img_try (img_exact Hbot)|]. split; [img_try (img_exact Hhi)|].
split; [img_try (img_exact HPR2)|]. split; [img_try (img_exact Hgp)|]. split; [img_try (img_exact Htp)|]. split; [|img_try (img_exact HQT2)].
unfold chain_pre, frame0_ok in *. rewrite Etop. destruct Hch as [R4096 CH]. split; [img_try (img_exact R4096)|].
destruct (spZ R + 16 <? ly_top ly) eqn:Hf0; [|img_try (img_exact CH)].
destruct (bad_next (spZ R) (ly_top ly) (s0Z R)) eqn:Hb; [img_try (img_exact CH)|].
destruct CH as [H16 Hfp]. split; [img_try (img_exact H16)|].
apply Z.ltb_lt in Hf0. unfold bad_next in Hb. apply Bool.orb_false_iff in Hb as [Hb _]. apply Bool.orb_false_iff in Hb as [Hb1 Hb2].
apply Z.leb_gt in Hb1. apply Z.leb_gt in Hb2.
eapply fpchain_ext2; [img_try (img_exact Hfp) | img_lia |].
intros a va Ha1 Ha2 Hva. eapply rdword_ext; [|img_try (img_exact Hva)]. intros i Hi. img_apply HCH2. img_lia.
Qed.
Lemma pre_regs : forall ly2 S2 (W2 : world tfxsegs) (R' : bvmap 5 word) (mem2 : word -> option byte) md2,
acall_pre tfxsegs B ly2 S2 W2 R mem2 md2 ch ->
getr R' 1 = getr R 1 -> getr R' 2 = getr R 2 -> getr R' 3 = getr R 3 -> getr R' 4 = getr R 4 -> getr R' 8 = getr R 8 ->
acall_pre tfxsegs B ly2 S2 W2 R' mem2 md2 ch.
Proof.
intros ly2 S2 W2 R' mem2 md2 P E1 E2 E3 E4 E8. unfold acall_pre, spZ, chain_pre, frame0_ok, raZ, s0Z, spZ in *. rewrite E1, E2, E3, E4, E8. img_exact P.
Qed.
Variables (pp : sptr) (nold rn : Z).
Hypothesis HBLK : In (pp, nold) (blocks S).
Hypothesis HA0 : getr R 10 = w64 (sptr_addr B ly pp).
Hypothesis HA1 : getr R 11 = w64 rn.
Hypothesis Nrange : 64513 <= rn < MALLOC_MAX.
Hypothesis Hev : aregime3 S rn.
Let tr : list Z := call_trace ly (0x53640 + D_2c4) R ch.
Let s1 : astate := realloc_s1 S.
Hypothesis Htr : In tr (as_universe B).
Variables (U : bvmap 5 word) (memU : word -> option byte) (mdU : Model).
Hypothesis HIOU : same_io md mdU.
Hypothesis HFRU : forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly s1 a -> ~ ascratch B ASTACK R a ->
aview tfxsegs (w_H W) memU a = aview tfxsegs (w_H W) mem a.
Hypothesis HCHU : forall a, spZ R <= a < ly_top ly -> aview tfxsegs (w_H W) memU a = aview tfxsegs (w_H W) mem a.
Variables (q : sptr) (S2 : astate) (W2 : world tfxsegs) (ly2 : alayout) (regsM : bvmap 5 word) (memM : word -> option byte) (mdM : Model).
Hypothesis MP : exists ns, realloc_mpost (as_universe B) S rn ns (q, S2).
Hypothesis AR2 : AR tfxsegs B ly2 S2 W2 memM mdM.
Hypothesis LLE : layout_le (length (st_secs s1)) ly ly2.
Hypothesis WLE : wle W W2.
Hypothesis MST : MIDST_top (virt R U) (Z.of_nat (length tr)) (w_H W2) regsM memM.
Hypothesis SIO : same_io mdU mdM.
Hypothesis FRB : forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly s1 a -> ~ aowned B ly2 S2 a -> ~ ascratch B ASTACK (virt R U) a ->
~ (q <> PNull /\ sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size rn) ->
aview tfxsegs (w_H W2) memM a = aview tfxsegs (w_H W) memU a.
Hypothesis PRB : forall a, spZ (virt R U) - ASTACK <= a < spZ (virt R U) -> apresent (w_H W2) memM a.
Hypothesis A0M : getr regsM 10 = w64 (sptr_addr B ly2 q).
Hypothesis QT2 : qtight S2.
Hypothesis PBM : forall i, (i < length tr)%nat -> val_mem tfxsegs (mrestrict (w_H W2) memM) (spZ (virt R U) - 2120 + 8 * Z.of_nat i) 8 (nth i tr 0).
Hypothesis HARU : AR tfxsegs B ly s1 W memU mdU.
Lemma spV : spZ (virt R U) = spZ R.
Proof. unfold spZ. rewrite (virt_same R U 2%bv ltac:(img_try (cbn [In]; tauto))). img_refl. Qed.
Lemma mp_facts : Wf (as_universe B) S2 /\ st_nev S2 = st_nev S + 2 /\ frames S2 = frames S /\
match q with PNull => blocks S2 = blocks S | _ => blocks S2 = blocks S ++ [(q, rn)] /\ ~ In q (map fst (blocks S)) end /\ st_internal_inited S2 = true.
Proof.
destruct MP as (ns & (WF2 & NEV & _ & FRS & BL & _) & INI & _). cbn [snd] in INI.
unfold realloc_s1 in *. cbn in NEV, FRS, BL.
split; [img_try (img_exact WF2)|]. split; [img_lia|]. split; [img_try (img_exact FRS)|]. split; [img_try (img_exact BL) | img_try (img_exact INI)].
Qed.
Lemma stack_facts : forall a, spZ R <= a < ly_top ly ->
0 <= a < 2 ^ 64 /\ ~ aowned B ly S a /\ ~ aowned B ly s1 a /\ ~ aowned B ly2 S2 a /\ ~ ascratch B ASTACK R a /\ ASAN_CEIL <= a.
Proof.
intros a Ha. destruct PRE as (HAR0 & _ & _ & _ & Hlo & Hbot & Hhi & _).
pose proof (am_layout B ly S _ (proj1 HAR0)) as LY. pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof (lo_stk_ceil ly LY) as CE.
pose proof (proj1 ASAN_CEIL_range) as CR.
destruct LLE as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (ST : ly_stk_lo ly <= a < ly_stk_hi ly) by (img_try (unfold ASTACK in *; img_lia)).
split; [img_try (unfold kHighMemEnd in *; img_lia)|].
split; [img_try (img_exact (AR_stack_law_ok tfxsegs B ly S W mem md a HAR0 ST))|].
split; [img_try (img_exact (AR_stack_law_ok tfxsegs B ly s1 W memU mdU a HARU ST))|].
split; [img_try (img_apply (AR_stack_law_ok tfxsegs B ly2 S2 W2 memM mdM a AR2); rewrite Eslo, Eshi; img_exact ST)|].
split; [|img_try (unfold ASTACK in *; img_lia)].
unfold ascratch. rewrite (ts_errno B TB). unfold TFX_ERRNO, kHighMemBeg, ASTACK in *. img_lia.
Qed.
Lemma REG2 : aregime S2.
Proof.
destruct MP as (ns & MPn). destruct PRE as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
img_exact (aregime3_s2 (as_universe B) S rn ns q S2 (am_wf B ly S _ (proj1 HAR0)) ltac:(img_try (clear - Nrange; img_lia)) Hev HQT MPn).
Qed.
Lemma PRE_M : acall_pre tfxsegs B ly2 S2 W2 R memM mdM ch.
Proof.
pose proof mp_facts as (_ & NEV & _).
img_apply (pre_transport (length (st_secs s1)) ly2 S2 W2 memM mdM AR2 REG2 LLE); [img_try (intros a Ha; img_apply PRB; rewrite spV; img_exact Ha) | | img_try (img_exact QT2)].
intros a Ha. destruct (stack_facts a Ha) as (Ra & N0 & N1 & N2 & NS & CE).
rewrite (FRB a Ra N1 N2).
- img_exact (HCHU a Ha).
- unfold ascratch in NS |- *. rewrite spV. img_exact NS.
- intros [Hne Hq]. destruct (mp_facts) as (_ & _ & _ & BL & _). destruct q as [| | |]; [img_try (img_exact (Hne eq_refl)) | | |].
all: match type of BL with _ /\ _ => destruct BL as [BL _] end;
pose proof (AR_blocks_law_ok tfxsegs B ly2 S2 W2 memM mdM _ rn AR2 ltac:(img_try (unfold ablocks; img_apply in_map_iff; eexists (_, rn); split; [img_refl | img_try (rewrite BL; img_apply in_or_app; right; left; img_refl)]))) as (_ & _ & Hc & _);
cbn [fst snd] in Hc; unfold ASAN_CEIL in CE; img_lia.
Qed.
Lemma map_eq_In : forall {X Y} (f g : X -> Y) l x, map f l = map g l -> In x l -> f x = g x.
Proof.
intros X Y f g l x. induction l as [|y l IH]; intros E Hin; [img_try (destruct Hin)|].
cbn in E. injection E as E1 E2. destruct Hin as [<-|Hin]; [img_try (img_exact E1) | img_try (img_exact (IH E2 Hin))].
Qed.
Hypothesis HQ : q <> PNull.
Let pa : Z := sptr_addr B ly pp.
Let qa : Z := sptr_addr B ly2 q.
Let nn : Z := req_size nold.
Let len : Z := Z.min rn nn.
Let hb1 : Z := YF1w.hb1 B ly2 W2 memM pp.
Lemma BL2 : blocks S2 = blocks S ++ [(q, rn)].
Proof. destruct mp_facts as (_ & _ & _ & BL & _). destruct q; [img_try (img_exact (False_ind _ (HQ eq_refl))) | img_try (img_exact (proj1 BL)) | img_try (img_exact (proj1 BL)) | img_try (img_exact (proj1 BL))]. Qed.
Lemma HBLK2 : In (pp, nold) (blocks S2). Proof. rewrite BL2. img_apply in_or_app. left. img_exact HBLK. Qed.
Lemma HBQ2 : In (q, rn) (blocks S2). Proof. rewrite BL2. img_apply in_or_app. right. left. img_refl. Qed.
Lemma pa2 : sptr_addr B ly2 pp = pa.
Proof.
destruct (AR_layout_law_ok tfxsegs B ly s1 W memU mdU ly2 HARU LLE) as (EAB & _ & _). unfold ablocks in EAB.
img_change (blocks s1) with (blocks S) in EAB.
pose proof (map_eq_In (fun b => (sptr_addr B ly2 (fst b), snd b)) (fun b => (sptr_addr B ly (fst b), snd b)) (blocks S) (pp, nold) EAB HBLK) as E.
cbn [fst snd] in E. injection E as E. img_exact E.
Qed.
Lemma blkP : pa mod 16 = 0 /\ 4096 <= pa /\ pa + nn <= ASAN_CEIL /\
(forall a, pa <= a < pa + nn -> apresent (w_H W2) memM a /\ ~ aowned B ly2 S2 a) /\ 0 <= nold < MALLOC_MAX.
Proof.
assert (IN : In (pa, nold) (ablocks B ly2 S2)) by (img_try (unfold ablocks; img_apply in_map_iff; exists (pp, nold); split; [img_try (cbn [fst snd]; rewrite pa2; img_refl) | img_try (img_exact HBLK2)])).
destruct (AR_blocks_law_ok tfxsegs B ly2 S2 W2 memM mdM pa nold AR2 IN) as (P16 & P4096 & PC & _ & PP & _ & PN).
split; [img_try (img_exact P16)|]. split; [img_try (img_exact P4096)|]. split; [img_try (img_exact PC)|]. split; [img_try (img_exact PP) | img_try (img_exact PN)].
Qed.
Lemma blkQ : 4096 <= qa /\ qa + rn <= ASAN_CEIL /\ (forall a, qa <= a < qa + rn -> apresent (w_H W2) memM a /\ ~ aowned B ly2 S2 a) /\ in_app qa rn.
Proof.
assert (IN : In (qa, rn) (ablocks B ly2 S2)) by (img_try (unfold ablocks; img_apply in_map_iff; exists (q, rn); split; [img_refl | img_try (img_exact HBQ2)])).
destruct (AR_blocks_law_ok tfxsegs B ly2 S2 W2 memM mdM qa rn AR2 IN) as (_ & P4096 & PC & PA & PP & _ & _).
replace (req_size rn) with rn in PC, PP, PA by (img_try (unfold req_size; destruct (rn =? 0) eqn:E; [img_try (apply Z.eqb_eq in E; img_lia) | img_refl])).
split; [img_try (img_exact P4096)|]. split; [img_try (img_exact PC)|]. split; [img_try (img_exact PP) | img_try (img_exact PA)].
Qed.
Lemma blkDISJ : qa + rn <= pa \/ pa + nn <= qa.
Proof.
assert (IN : In (qa, rn) (ablocks B ly2 S2)) by (img_try (unfold ablocks; img_apply in_map_iff; exists (q, rn); split; [img_refl | img_try (img_exact HBQ2)])).
destruct (AR_blocks_law_ok tfxsegs B ly2 S2 W2 memM mdM qa rn AR2 IN) as (_ & _ & _ & _ & _ & PW & _).
unfold ablocks in PW. rewrite BL2, !map_app in PW. cbn [map fst snd] in PW.
pose proof (pairwise_app_last zdisjoint _ (pa, nn) _ PW) as D.
assert (INP : In (pa, nn) (map (fun b : Z * Z => (fst b, req_size (snd b))) (map (fun b : sptr * Z => (sptr_addr B ly2 (fst b), snd b)) (blocks S)))).
{ img_apply in_map_iff. exists (pa, nold). split; [img_refl|]. img_apply in_map_iff. exists (pp, nold). split; [img_try (cbn [fst snd]; rewrite pa2; img_refl) | img_try (img_exact HBLK)]. }
specialize (D INP). unfold zdisjoint in D. cbn [fst snd] in D. fold qa in D.
replace (req_size rn) with rn in D by (img_try (unfold req_size; destruct (rn =? 0) eqn:E; [img_try (apply Z.eqb_eq in E; img_lia) | img_refl])). img_lia.
Qed.
Lemma hdr_facts : 0 <= hb1 < 256 /\
val_mem tfxsegs (mrestrict (w_H W2) memM) (pa - 16) 1 2 /\ val_mem tfxsegs (mrestrict (w_H W2) memM) (pa - 15) 1 hb1 /\
val_mem tfxsegs (mrestrict (w_H W2) memM) (pa - 14) 2 0 /\ val_mem tfxsegs (mrestrict (w_H W2) memM) (pa - 12) 4 nn /\
val_mem tfxsegs (mrestrict (w_H W2) memM) (0xa2188 + D_10f0) 8 (0xa3ff8 + D_10f0) /\ val_mem tfxsegs (mrestrict (w_H W2) memM) (0xa3ff8 + D_10f0) 8 (0x9b490 + D_10ec) /\
(pa + nn <= TFX_IMG_LO \/ TFX_IMG_END + 16 <= pa).
Proof.
pose proof (YF1w.hw_val B ly2 S2 W2 R memM mdM pp nold ch PRE_M HBLK2) as [HW HN]. rewrite pa2 in HW, HN.
pose proof (YF1w.hb1_facts B ly2 S2 W2 R memM mdM pp nold ch PRE_M HBLK2) as (_ & HB & _). fold hb1 in HW, HB.
pose proof (YF1w.p_zone B ly2 S2 W2 R memM mdM pp nold ch PRE_M HBLK2) as (_ & _ & ZC). rewrite pa2 in ZC.
pose proof (YF1w.p_facts B ly2 S2 W2 R memM mdM pp nold ch PRE_M HBLK2) as (_ & _ & _ & _ & N8a & N8b & _). fold nn in N8b, ZC.
unfold YF2h.HWv in HW.
assert (LB : forall v (w j : nat), YG0h.le_byte v w j = (v mod 2 ^ (8 * Z.of_nat w)) / 2 ^ (8 * Z.of_nat j) mod 256).
{ intros v w j. unfold YG0h.le_byte. rewrite Z.shiftr_div_pow2 by img_lia. img_refl. }
split; [img_try (img_exact HB)|].
split. { replace (pa - 16) with (pa - 16 + Z.of_nat 0) by img_lia. img_apply (val_mem_slice _ _ 4 (2 + 256 * hb1) 0 1 2 HW ltac:(img_lia)).
intros j Hj. assert (j = 0%nat) by img_lia. (subst j; cbv beta). rewrite !LB. img_change (2 ^ (8 * Z.of_nat 1)) with 256. img_change (2 ^ (8 * Z.of_nat 4)) with 4294967296.
img_change (2 ^ (8 * Z.of_nat (0 + 0))) with 1. img_change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite !Z.div_1_r. Z.div_mod_to_equations. nia. }
split. { replace (pa - 15) with (pa - 16 + Z.of_nat 1) by img_lia. img_apply (val_mem_slice _ _ 4 (2 + 256 * hb1) 1 1 hb1 HW ltac:(img_lia)).
intros j Hj. assert (j = 0%nat) by img_lia. (subst j; cbv beta). rewrite !LB. img_change (2 ^ (8 * Z.of_nat 1)) with 256. img_change (2 ^ (8 * Z.of_nat 4)) with 4294967296.
img_change (2 ^ (8 * Z.of_nat (1 + 0))) with 256. img_change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite !Z.div_1_r. Z.div_mod_to_equations. nia. }
split. { replace (pa - 14) with (pa - 16 + Z.of_nat 2) by img_lia. img_apply (val_mem_slice _ _ 4 (2 + 256 * hb1) 2 2 0 HW ltac:(img_lia)).
intros j Hj. rewrite !LB. img_change (2 ^ (8 * Z.of_nat 2)) with 65536. img_change (2 ^ (8 * Z.of_nat 4)) with 4294967296.
destruct j as [|[|j]]; [| |img_lia].
- img_change (2 ^ (8 * Z.of_nat (2 + 0))) with 65536. img_change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite !Z.div_1_r. Z.div_mod_to_equations. nia.
- img_change (2 ^ (8 * Z.of_nat (2 + 1))) with 16777216. img_change (2 ^ (8 * Z.of_nat 1)) with 256. Z.div_mod_to_equations. nia. }
split; [img_try (img_exact HN)|].
split; [img_try (refine (YF1w.cell_lit B TB ly2 S2 W2 R memM mdM ch PRE_M (0xa2188 + D_10f0) 8 (0xa3ff8 + D_10f0) _); (img_case; vm_compute); img_refl)|].
split; [img_try (refine (YF1w.cell_lit B TB ly2 S2 W2 R memM mdM ch PRE_M (0xa3ff8 + D_10f0) 8 (0x9b490 + D_10ec) _); (img_case; vm_compute); img_refl)|].
unfold zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg in *. img_lia.
Qed.
Lemma mid_regs : getr regsM 9 = w64 pa /\ getr regsM 19 = w64 rn /\ getr regsM 18 = w64 TFX_INST /\
getr regsM 2 = Z_to_bv 64 (bv_unsigned (getr R 2) + (-2208)) /\ getr regsM 8 = Z_to_bv 64 (bv_unsigned (getr R 2) + (-2136)) /\
(forall r : bv 5, In r [3; 4; 23; 24; 25; 26; 27]%bv -> getr regsM r = getr R r).
Proof.
destruct MST as (CS & _ & MR & _). rewrite Forall_forall in MR.
assert (G : forall r e, In (r, e) MIDREGS -> getr regsM r = sv_denot (Ereg (virt R U) []) e) by (img_try (intros r e Hin; img_exact (MR (r, e) Hin))).
split. { rewrite (G 9%bv (SOff 11 0) ltac:(img_try (unfold MIDREGS; cbn [In]; tauto))). cbn [sv_denot]. rewrite (ew_Ereg_nat (virt R U) [] 11 11%bv eq_refl), virt_11, Z.add_0_r, Z_to_bv_bv_unsigned. img_exact HA0. }
split. { rewrite (G 19%bv (SOff 10 0) ltac:(img_try (unfold MIDREGS; cbn [In]; tauto))). cbn [sv_denot]. rewrite (ew_Ereg_nat (virt R U) [] 10 10%bv eq_refl), virt_10, Z.add_0_r, Z_to_bv_bv_unsigned. img_exact HA1. }
split. { rewrite (G 18%bv (SLit TFX_INST) ltac:(img_try (unfold MIDREGS; cbn [In]; tauto))). img_refl. }
split. { rewrite (G 2%bv (SOff 2 (-2208)) ltac:(img_try (unfold MIDREGS; cbn [In]; tauto))). cbn [sv_denot]. rewrite (ew_Ereg_nat (virt R U) [] 2 2%bv eq_refl), (virt_same R U 2%bv ltac:(img_try (cbn [In]; tauto))). img_refl. }
split. { rewrite (G 8%bv (SOff 2 (-2136)) ltac:(img_try (unfold MIDREGS; cbn [In]; tauto))). cbn [sv_denot]. rewrite (ew_Ereg_nat (virt R U) [] 2 2%bv eq_refl), (virt_same R U 2%bv ltac:(img_try (cbn [In]; tauto))). img_refl. }
intros r Hr. rewrite (CS r Hr). img_apply virt_same. cbn [In] in Hr |- *. tauto.
Qed.
Lemma c1_at_mid : SRr tfxsegs W2 (cfg_at tfxsegs (0x323bc + D_150) regsM memM mdM) (c1_postM W2 mdM regsM memM pa qa len).
Proof.
destruct hdr_facts as (HB & V0 & V1 & V2 & V4 & VC1 & VC2 & HPI). destruct mid_regs as (G9 & G19 & _).
destruct blkP as (_ & P4096 & PC & PP & PN). destruct blkQ as (Q4096 & QC & QP & _). pose proof blkDISJ as DJ.
pose proof (proj1 ASAN_CEIL_range) as CR.
assert (Hnn : 1 <= nn < 2 ^ 28) by (img_try (unfold nn, req_size, MALLOC_MAX in *; destruct (nold =? 0) eqn:E; [img_lia | img_try (apply Z.eqb_neq in E; img_lia)])).
unfold cfg_at. unfold len.
img_apply (c1_copy W2 mdM regsM memM pa qa rn nn hb1 G9 A0M G19); try assumption.
- img_lia.
- clear - HPI Hnn. img_lia.
- img_lia.
- unfold MALLOC_MAX in *. img_lia.
- img_lia.
- img_lia.
- img_lia.
- intros a Ha. img_apply PP. img_lia.
- intros a Ha. img_apply QP. img_lia.
Qed.
Lemma stack_view_M : forall a, spZ R <= a < ly_top ly -> aview tfxsegs (w_H W2) memM a = aview tfxsegs (w_H W) mem a.
Proof. destruct PRE_M as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
intros a Ha. destruct (stack_facts a Ha) as (Ra & N0 & N1 & N2 & NS & CE).
rewrite (FRB a Ra N1 N2).
- img_exact (HCHU a Ha).
- unfold ascratch in NS |- *. rewrite spV. img_exact NS.
- intros [_ Hq]. destruct blkQ as (_ & QC & _). fold qa in Hq. replace (req_size rn) with rn in Hq by (img_try (unfold req_size; destruct (rn =? 0) eqn:E; [img_try (apply Z.eqb_eq in E; img_lia) | img_refl])). img_lia.
Qed.
Variables (regsD : bvmap 5 word) (memD : word -> option byte) (matD : list word).
Let mdD : Model := with_vm_backing (m_vm_lazy mdM) matD mdM.
Hypothesis D1 : getr regsD 1 = w64 (0x32434 + D_150).
Hypothesis D10 : getr regsD 10 = getr regsM 18.
Hypothesis D11 : getr regsD 11 = w64 pa.
Hypothesis D12 : getr regsD 12 = w64 0.
Hypothesis D13 : getr regsD 13 = w64 0.
Hypothesis D14 : getr regsD 14 = getr regsM 8.
Hypothesis D15 : getr regsD 15 = w64 1.
Hypothesis D20 : getr regsD 20 = w64 qa.
Hypothesis DK : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 21; 22; 23; 24; 25; 26; 27; 29; 30; 31]%bv -> getr regsD r = getr regsM r.
Hypothesis DM : forall x : word, ~ (qa <= bv_unsigned x < qa + len) -> memD x = memM x.
Hypothesis DP : forall a, apresent (w_H W2) memM a -> apresent (w_H W2) memD a.
Let RF : bvmap 5 word := fvirt R regsD.
Lemma len_le : 0 <= len /\ len <= rn /\ len <= nn.
Proof. destruct blkP as (_ & _ & _ & _ & PN). unfold len, nn, req_size. destruct (nold =? 0); img_lia. Qed.
Lemma dcfacts : DCFACTS R regsD.
Proof.
destruct mid_regs as (G9 & G19 & G18 & G2 & G8 & GK). destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Htp & _). rewrite (ts_tp _ TB) in Htp.
unfold DCFACTS. repeat split.
- img_exact D1.
- rewrite (DK 2%bv ltac:(img_try (cbn [In]; tauto))). img_exact G2.
- rewrite (DK 3%bv ltac:(img_try (cbn [In]; tauto))). img_apply GK. cbn [In]. tauto.
- rewrite (DK 4%bv ltac:(img_try (cbn [In]; tauto))), (GK 4%bv ltac:(img_try (cbn [In]; tauto))). img_exact Htp.
- rewrite (DK 8%bv ltac:(img_try (cbn [In]; tauto))). img_exact G8.
- rewrite (DK 9%bv ltac:(img_try (cbn [In]; tauto))), G9. symmetry. img_exact HA0.
- rewrite D10. img_exact G18.
- rewrite D11. symmetry. img_exact HA0.
- img_exact D12.
- img_exact D13.
- rewrite D14. img_exact G8.
- img_exact D15.
- rewrite (DK 18%bv ltac:(img_try (cbn [In]; tauto))). img_exact G18.
- rewrite (DK 23%bv ltac:(img_try (cbn [In]; tauto))). img_apply GK. cbn [In]. tauto.
- rewrite (DK 24%bv ltac:(img_try (cbn [In]; tauto))). img_apply GK. cbn [In]. tauto.
- rewrite (DK 25%bv ltac:(img_try (cbn [In]; tauto))). img_apply GK. cbn [In]. tauto.
- rewrite (DK 26%bv ltac:(img_try (cbn [In]; tauto))). img_apply GK. cbn [In]. tauto.
- rewrite (DK 27%bv ltac:(img_try (cbn [In]; tauto))). img_apply GK. cbn [In]. tauto.
Qed.
Lemma AR_D : AR tfxsegs B ly2 S2 W2 memD mdD.
Proof.
destruct blkQ as (Q4096 & QC & QP & QA). pose proof len_le as (L0 & L1 & L2). pose proof (proj1 ASAN_CEIL_range) as CR.
assert (EQ : forall a, 0 <= a < 2 ^ 64 -> ~ (qa <= a < qa + len) -> aview tfxsegs (w_H W2) memD a = aview tfxsegs (w_H W2) memM a).
{ intros a Ra Na. img_apply aview_same. img_apply DM. rewrite unsigned_lit_small by img_exact Ra. img_exact Na. }
img_apply (AR_frame_law_ok tfxsegs B ly2 S2 W2 memM mdM memD mdD AR2).
- intros a Ra Ho. img_apply EQ; [img_try (img_exact Ra)|]. intros Hq. img_exact (proj2 (QP a ltac:(img_lia)) Ho).
- intros a Hv. rewrite (YE0v.aview_mod _ memD a). rewrite (YE0v.aview_mod _ memM a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (img_try (img_apply Z.mod_pos_bound; img_lia)). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' qa) as [L|L]; [img_try (rewrite EQ by img_lia; img_exact Hv)|]. destruct (Z_lt_le_dec a' (qa + len)) as [L'|L']; [|img_try (rewrite EQ by img_lia; img_exact Hv)].
img_apply YE0v.aview_some_of_apresent. img_apply DP. img_apply QP. img_lia.
- img_apply m_vmmaps_wvb.
- img_apply m_vm_lazy_wvb.
- img_apply eager_used_wvb.
- intros a Hb Hh. unfold YG0u.w64. img_apply DM. destruct QA as [_ QA].
unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *.
rewrite unsigned_lit_small by img_lia. img_lia.
Qed.
Lemma PRE_D : acall_pre tfxsegs B ly2 S2 W2 RF memD mdD ch.
Proof.
pose proof mp_facts as (_ & NEV & _). destruct blkQ as (Q4096 & QC & QP & QA). pose proof len_le as (L0 & L1 & L2).
img_apply (pre_regs ly2 S2 W2 RF memD mdD).
- img_apply (pre_transport (length (st_secs s1)) ly2 S2 W2 memD mdD AR_D REG2 LLE); [img_try (intros a Ha; apply DP, PRB; rewrite spV; img_exact Ha) | | img_try (img_exact QT2)].
intros a Ha. destruct (stack_facts a Ha) as (Ra & _ & _ & _ & _ & CE). rewrite <- (stack_view_M a Ha). img_apply aview_same. img_apply DM.
rewrite unsigned_lit_small by img_exact Ra. img_lia.
- img_apply fvirt_same. cbn [In]. tauto.
- img_apply fvirt_same. cbn [In]. tauto.
- img_apply fvirt_same. cbn [In]. tauto.
- img_apply fvirt_same. cbn [In]. tauto.
- img_apply fvirt_same. cbn [In]. tauto.
Qed.
Lemma tr_RF : forall pc0, call_trace ly2 pc0 RF ch = call_trace ly pc0 R ch.
Proof.
intros pc0. destruct LLE as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
unfold call_trace, frame0_ok, spZ, raZ, s0Z, RF. rewrite Etop.
rewrite (fvirt_same R regsD 2%bv ltac:(img_try (cbn [In]; tauto))), (fvirt_same R regsD 1%bv ltac:(img_try (cbn [In]; tauto))), (fvirt_same R regsD 8%bv ltac:(img_try (cbn [In]; tauto))). img_refl.
Qed.
Lemma tr_len : (1 <= length tr <= 30)%nat.
Proof.
unfold tr, call_trace. destruct (frame0_ok ly R); [|img_try (cbn [length]; img_lia)].
unfold unwind_of_chain, kUnwindMax. rewrite firstn_length. cbn [length]. img_lia.
Qed.
Lemma sp_geom : TFX_IMG_END + ASTACK <= spZ R /\ ASAN_CEIL + ASTACK <= spZ R /\ spZ R < 2 ^ 64.
Proof.
destruct PRE as (HAR0 & _ & _ & _ & Hlo & Hbot & Hhi & _).
pose proof (am_layout B ly S _ (proj1 HAR0)) as LY. pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof (lo_stk_ceil ly LY) as CE.
unfold TFX_IMG_END, kHighMemBeg, kHighMemEnd, ASTACK in *. img_lia.
Qed.
Lemma stack_D : forall a, spZ R - ASTACK <= a < spZ R -> memD (Z_to_bv 64 a) = memM (Z_to_bv 64 a).
Proof.
intros a Ha. destruct sp_geom as (_ & G & G'). destruct blkQ as (_ & QC & _). pose proof len_le as (L0 & L1 & _). pose proof (proj1 ASAN_CEIL_range) as CR.
img_apply DM. rewrite unsigned_lit_small by (img_try (unfold ASTACK in *; img_lia)). img_lia.
Qed.
Lemma cframes_D : CFRAMES_ok R (Z.of_nat (length tr)) (w_H W2) memD.
Proof. img_apply (CFRAMES_of_MID R U (Z.of_nat (length tr)) (w_H W2) regsM memM memD MST). intros a Ha. img_apply stack_D. unfold spZ, ASTACK. img_lia. Qed.
Lemma STKD_D : forall extra : list word, nth 4 extra (w64 0) = w64 (Z.of_nat (length (call_trace ly2 (0x53640 + D_2c4) RF ch))) ->
Forall (region_ok tfxsegs (Ereg RF extra) (mrestrict (w_H W2) memD)) [R_OBJ; R_SCR; R_TOP].
Proof.
intros extra Hx. rewrite tr_RF in Hx. fold tr in Hx. destruct sp_geom as (G1 & _). pose proof tr_len as TL.
img_apply (STKD_of R regsD (Z.of_nat (length tr)) (w_H W2) memD cframes_D ltac:(img_lia) G1); [|img_try (img_exact Hx)].
intros a Ha. apply DP, PRB. rewrite spV. img_exact Ha.
Qed.
Lemma HQ12_D : 4096 <= bv_unsigned (getr RF 12) <= 2 ^ 47.
Proof.
destruct blkQ as (Q4096 & QC & _). pose proof (proj1 ASAN_CEIL_range) as CR.
unfold RF. rewrite fvirt_12, D20. unfold w64. rewrite unsigned_lit_small by img_lia. img_lia.
Qed.
Lemma trace_D : forall i, (i < length tr)%nat -> val_mem tfxsegs (mrestrict (w_H W2) memD) (bv_unsigned (getr RF 2) - 2120 + 8 * Z.of_nat i) 8 (nth i tr 0).
Proof.
intros i Hi. pose proof tr_len as TL. unfold RF. rewrite (fvirt_same R regsD 2%bv ltac:(img_try (cbn [In]; tauto))).
eapply val_mem_frame; [|img_try (pose proof (PBM i Hi) as X; rewrite spV in X; img_exact X)].
intros k Hk. img_apply stack_D. unfold spZ, ASTACK. img_lia.
Qed.
Hypothesis HD : forall t, as_dhash B t = tfx_dhash t.
Lemma c2_arm : amreal tfxsegs (free pp tr S2) W2 (cfg_at tfxsegs (0x3244c + D_150) regsD memD mdD)
(fun r W' c' => (exists ns, realloc_fpost (as_universe B) S2 pp nold ns r) /\ rfree_leaf B ly2 S2 W2 RF memD mdD pp nold r W' c').
Proof.
pose proof mp_facts as (WF2 & NEV & _ & _ & INI).
eapply (amreal_atok _ true (realloc_fpost (as_universe B) S2 pp nold)).
{ img_exact (realloc_free_ok (as_universe B) S2 pp nold tr (ts_universe B TB) WF2 REG2 HBLK2 Htr). }
eapply amreal_mono; [img_try (intros r W' c' HL HP; split; [img_exact HP | img_exact HL])|].
pose proof PRE_D as PD. pose proof PD as ((M2 & _) & _).
assert (HTSD : ly_tsd ly2 = TFX_TSD) by (img_try (rewrite (am_tsd B ly2 S2 _ M2); img_apply (ts_tsd _ TB))).
assert (HA0D : getr RF 10 = w64 (sptr_addr B ly2 pp)) by (img_try (unfold RF; rewrite (fvirt_same R regsD 10%bv ltac:(cbn [In]; tauto)), pa2; img_exact HA0)).
assert (HUD : In (call_trace ly2 (0x53640 + D_2c4) RF ch) (as_universe B)) by (img_try (rewrite tr_RF; img_exact Htr)).
assert (REGSD : forall extra : list word, regs_ok (Ereg RF extra) REGS_DC regsD) by (img_try (intros extra; img_exact (REGSD_of R regsD extra dcfacts))).
assert (TRQ : YF6i.TRACEQ W2 ly2 RF ch memD).
{ unfold YF6i.TRACEQ, YF6m.tr. rewrite tr_RF. img_exact trace_D. }
assert (TRQM : YF6j.TRACEQ W2 ly2 RF ch memD).
{ unfold YF6j.TRACEQ, YF6n.tr. rewrite tr_RF. img_exact trace_D. }
pose proof (tfx_depot_ok B TB HD) as DEP. pose proof (tfx_refill_ok B TB) as R1.
assert (SEC : tfx_rchunk_sec_spec B) by (img_try (intros lyx X k cbp Wx regsx memx mdx r o PREx Hb; img_exact (tfx_rchunk_sec B TB lyx X k cbp Wx regsx memx mdx r o PREx Hb))).
assert (Q1 : forall nb, tfx_enqueue_spec_nb B nb) by (img_try (intros [|]; [img_try (img_exact (tfx_enqueue_nb B TB R1)) | img_try (img_exact (tfx_enqueue_room B TB))])).
assert (D0 : tfx_drain_spec B) by img_exact (tfx_drain_ok B TB (tfx_dorecycle_ok B TB (tfx_rchunk_of_arms B TB SEC))).
unfold tr. rewrite <- (tr_RF (0x53640 + D_2c4)).
set (qt := st_qthread S2) in *.
destruct (Z_le_gt_dec (qc_bytes qt + req_size nold + (if need_new_batch qt then kBatchBytes else 0)) kQuarantineCacheMax) as [ND|DR].
- destruct (need_new_batch qt) eqn:NB.
+ img_apply (YF6h.afree_mid B TB ly2 S2 W2 RF memD mdD pp nold ch PD HBLK2 HA0D HUD); [img_try ((subst qt; cbv beta); rewrite NB; img_exact ND) | img_try (img_exact tfx_ialloc_ok) | img_try (img_exact tfx_unwind_ok) | img_try (img_exact DEP) | img_try (img_apply Q1) | img_try (img_exact HTSD) | img_try (img_exact REGSD) | img_try (img_exact STKD_D) | img_try (img_exact HQ12_D) | img_try (img_exact INI) | img_try (img_exact TRQM)].
+ unfold need_new_batch in NB. destruct (rev (qc_list qt)) as [|lastb initr] eqn:ER; [img_try (discriminate)|]. apply Z.eqb_neq in NB.
assert (BL : Z.of_nat (length (b_items lastb)) < kBatchSlots).
{ pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wf_quarantine _ _ _ _ _ (am_wf B ly2 S2 _ M2))) lastb) as HH.
assert (IN : In lastb (all_batches S2)) by (img_try (unfold all_batches; img_apply in_app_iff; left; (subst qt; cbv beta); img_apply in_rev; rewrite ER; left; img_refl)).
specialize (HH IN). unfold kBatchSlots in *. img_lia. }
img_apply (YF6a.afree_common B TB ly2 S2 W2 RF memD mdD pp nold ch lastb initr PD HBLK2 HA0D HUD); [| img_try (img_exact tfx_ialloc_ok) | img_try (img_exact tfx_unwind_ok) | img_try (img_exact DEP) | img_try (img_exact HTSD) | img_try (img_exact REGSD) | img_try (img_exact STKD_D) | img_try (img_exact HQ12_D) | img_try (img_exact INI) | img_try (img_exact TRQ)].
(subst qt; cbv beta). split; [img_try (img_exact ER) | img_try (split; [img_exact BL | img_lia])].
- img_apply (YF6f.afree_drn B TB ly2 S2 W2 RF memD mdD pp nold ch PD HBLK2 HA0D HUD); [img_try ((subst qt; cbv beta); img_lia) | img_try (img_exact tfx_ialloc_ok) | img_try (img_exact tfx_unwind_ok) | img_try (img_exact DEP) | img_try (img_apply Q1) | img_try (img_exact D0) | img_try (img_exact HTSD) | img_try (img_exact REGSD) | img_try (img_exact STKD_D) | img_try (img_exact HQ12_D) | img_try (img_exact INI) | img_try (img_exact TRQM)].
Qed.
Hypothesis DC : forall i, 0 <= i < len -> aview tfxsegs (w_H W2) memD (qa + i) = aview tfxsegs (w_H W2) memM (pa + i).
Lemma succ_leaf : forall S3 (W4 : world tfxsegs) c4,
(exists ns, realloc_fpost (as_universe B) S2 pp nold ns (tt, S3)) -> rfree_leaf B ly2 S2 W2 RF memD mdD pp nold (tt, S3) W4 c4 ->
realloc_leaf tfxsegs B ly S W R mem md pp nold rn (q, S3) W4 c4.
Proof.
intros S3 W4 c4 FP ((ly' & regs' & mem' & md' & -> & AP & QT3) & (regs'' & mem'' & md'' & Ecfg & A0)).
destruct AP as (AR3 & LLE3 & WLE3 & CS3 & SIO3 & FR3 & PR3). cbn [snd] in AR3, QT3.
assert (ER : regs'' = regs') by (img_try (apply (f_equal (fun c => ms_regs (cfg_ms c))) in Ecfg; cbn in Ecfg; symmetry; img_exact Ecfg)). (subst regs''; cbv beta).
assert (E1 : raZ RF = raZ R) by (img_try (unfold raZ, RF; rewrite (fvirt_same R regsD 1%bv ltac:(cbn [In]; tauto)); img_refl)).
assert (E2 : spZ RF = spZ R) by (img_try (unfold spZ, RF; rewrite (fvirt_same R regsD 2%bv ltac:(cbn [In]; tauto)); img_refl)).
destruct blkP as (_ & P4096 & PC & PP & PN). destruct blkQ as (Q4096 & QC & QP & QA). pose proof blkDISJ as DJ. pose proof len_le as (L0 & L1 & L2).
destruct sp_geom as (G1 & G2 & G3). pose proof (proj1 ASAN_CEIL_range) as CR.
assert (RQ : req_size rn = rn) by (img_try (unfold req_size; destruct (rn =? 0) eqn:E; [img_try (apply Z.eqb_eq in E; img_lia) | img_refl])).
assert (Hnn : nold <= nn) by (img_try (unfold nn, req_size; destruct (nold =? 0) eqn:E; [img_try (apply Z.eqb_eq in E; img_lia) | img_lia])).
assert (QA' : sptr_addr B ly' q = qa).
{ destruct (AR_layout_law_ok tfxsegs B ly2 S2 W2 memD mdD ly' AR_D LLE3) as (EAB & _ & _). unfold ablocks in EAB.
pose proof (map_eq_In (fun b => (sptr_addr B ly' (fst b), snd b)) (fun b => (sptr_addr B ly2 (fst b), snd b)) (blocks S2) (q, rn) EAB HBQ2) as E.
cbn [fst snd] in E. injection E as E. img_exact E. }
exists ly', regs', mem', md'. cbn [fst snd].
split; [img_try (rewrite <- E1; img_refl)|].
split.
{ intros r Hr. rewrite (CS3 r Hr). unfold acallee_saved in Hr. unfold RF.
assert (RR : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by img_lia.
clear Hr. repeat match type of RR with _ \/ _ => destruct RR as [->|RR] | _ = _ => subst r end;
img_apply fvirt_same; cbn [In]; repeat (first [left; img_apply bv_eq; (img_case; vm_compute); img_refl | right]). }
split. { rewrite A0, QA'. unfold RF. rewrite fvirt_12. img_exact D20. }
split; [img_try (img_exact QT3)|].
assert (MAIN : exists ly2' S2' (W2' : world tfxsegs) mem2' md2',
astage tfxsegs B ASTACK ly S W R mem md (fun a => sptr_addr B ly2' q <= a < sptr_addr B ly2' q + req_size rn) ly2' S2' W2' mem2' md2' /\
(exists ns, realloc_mpost (as_universe B) S rn ns (q, S2')) /\ qtight S2' /\
(forall i, 0 <= i < Z.min nold rn -> aview tfxsegs (w_H W2') mem2' (sptr_addr B ly2' q + i) = aview tfxsegs (w_H W) mem (sptr_addr B ly pp + i)) /\
astage tfxsegs B ASTACK ly2' S2' W2' R mem2' md2' (fun a => sptr_addr B ly pp <= a < sptr_addr B ly pp + req_size nold) ly' S3 W4 mem' md' /\
(exists ns, realloc_fpost (as_universe B) S2' pp nold ns (tt, S3))).
{ exists ly2, S2, W2, memD, mdD. fold qa pa nn. rewrite RQ.
assert (V1 : forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly2 S2 a -> ~ ascratch B ASTACK R a -> ~ (qa <= a < qa + rn) ->
aview tfxsegs (w_H W2) memM a = aview tfxsegs (w_H W) mem a).
{ intros a Ra NO NO2 NS NE.
assert (N1 : ~ aowned B ly s1 a) by (img_try (intros O; img_apply NO; img_exact (proj1 (aowned_s1 B ly S a) O))).
rewrite (FRB a Ra N1 NO2); [img_exact (HFRU a Ra NO N1 NS) | unfold ascratch in NS |- *; rewrite spV; img_exact NS |].
intros [_ Hq]. fold qa in Hq. rewrite RQ in Hq. img_exact (NE Hq). }
split.
{ split; [img_try (img_exact AR_D)|]. split; [img_try (img_exact LLE)|]. split; [img_try (img_exact WLE)|].
split; [img_try (img_exact (same_io_trans _ _ _ (same_io_trans _ _ _ HIOU SIO) (same_io_wvb mdM matD)))|].
split.
- intros a Ra NO NO2 NS NE. rewrite <- (V1 a Ra NO NO2 NS NE). img_apply aview_same. img_apply DM. rewrite unsigned_lit_small by img_exact Ra. img_lia.
- intros a Ha. apply DP, PRB. rewrite spV. img_exact Ha. }
split; [img_try (img_exact MP)|]. split; [img_try (img_exact QT2)|].
split.
{ intros i Hi. rewrite (DC i ltac:(img_lia)).
destruct PRE as (HAR0 & _).
assert (IN0 : In (pa, nold) (ablocks B ly S)) by (img_try (unfold ablocks; img_apply in_map_iff; exists (pp, nold); split; [img_refl | img_try (img_exact HBLK)])).
destruct (AR_blocks_law_ok tfxsegs B ly S W mem md pa nold HAR0 IN0) as (_ & _ & _ & _ & PP0 & _). fold nn in PP0.
destruct hdr_facts as (_ & _ & _ & _ & _ & _ & _ & HPI).
img_apply V1; [img_lia | img_try (img_exact (proj2 (PP0 (pa + i) ltac:(img_lia)))) | img_try (img_exact (proj2 (PP (pa + i) ltac:(img_lia)))) | | img_lia].
unfold ascratch. rewrite (ts_errno B TB). unfold TFX_ERRNO, TFX_IMG_LO, TFX_IMG_END, ASTACK in *. img_lia. }
split; [|img_try (img_exact FP)].
split; [img_try (img_exact AR3)|]. split; [img_try (img_exact LLE3)|]. split; [img_try (img_exact WLE3)|]. split; [img_try (img_exact SIO3)|].
split.
- intros a Ra NO NO3 NS NE. img_apply (FR3 a Ra NO NO3); [unfold ascratch in NS |- *; rewrite E2; img_exact NS|].
intros [_ Hp]. rewrite pa2 in Hp. img_exact (NE Hp).
- intros a Ha. img_apply PR3. rewrite E2. img_exact Ha. }
destruct q as [| | |]; [img_try (img_exact (False_ind _ (HQ eq_refl))) | img_try (img_exact MAIN) | img_try (img_exact MAIN) | img_try (img_exact MAIN)].
Qed.
Lemma null_arm : q = PNull -> SRr tfxsegs W2 (cfg_at tfxsegs (0x323bc + D_150) regsM memM mdM) (realloc_leaf tfxsegs B ly S W R mem md pp nold rn (PNull, S2)).
Proof.
intros EQ. pose proof A0M as A0'. rewrite EQ in A0'. cbn [sptr_addr sptr_exp aeval] in A0'.
destruct mid_regs as (_ & _ & _ & G2 & _ & GK). destruct sp_geom as (G1 & G2' & G3). pose proof (proj1 ASAN_CEIL_range) as CR.
pose proof PRE as (HAR0 & _ & Hra & _ & Hlo & _ & Hhi & _ & _ & Htp & _). rewrite (ts_tp _ TB) in Htp.
pose proof LLE as LLE0. destruct LLE as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (F4 : getr regsM 4 = w64 TFX_TP) by (img_try (rewrite (GK 4%bv ltac:(cbn [In]; tauto)); img_exact Htp)).
assert (CF : CFRAMES_ok R (Z.of_nat (length tr)) (w_H W2) memM) by (img_try (img_apply (CFRAMES_of_MID R U (Z.of_nat (length tr)) (w_H W2) regsM memM memM MST); intros; img_refl)).
unfold cfg_at. eapply SRr_mono.
{ img_apply (c_null W2 mdM R regsM memM (Z.of_nat (length tr)) G2 F4 A0'); [intros r Hr; img_apply GK; cbn [In] in Hr |- *; tauto | img_exact Htp | img_exact Hra | img_exact CF | img_exact G1 |].
intros a Ha. img_apply PRB. rewrite spV. img_exact Ha. }
intros W' c' _ (-> & regs' & mem' & mat & -> & CS & A10 & FRN & PRN).
set (md' := with_vm_backing (m_vm_lazy mdM) mat mdM).
assert (NSC : forall a, 0 <= a < 2 ^ 64 -> ~ ascratch B ASTACK R a -> aview tfxsegs (w_H W2) mem' a = aview tfxsegs (w_H W2) memM a).
{ intros a Ra NS. img_apply aview_same. unfold ascratch in NS. rewrite (ts_errno B TB) in NS. img_apply FRN; rewrite unsigned_lit_small by img_exact Ra; intros X; img_apply NS; [img_try (left) | img_try (right)]; img_exact X. }
exists ly2, regs', mem', md'. cbn [fst snd].
split. { unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. img_refl. }
split.
{ intros r Hr. unfold acallee_saved in Hr.
assert (RR : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by img_lia.
clear Hr. repeat match type of RR with _ \/ _ => destruct RR as [->|RR] | _ = _ => subst r end;
img_apply CS; cbn [In]; repeat (first [left; img_apply bv_eq; (img_case; vm_compute); img_refl | right]). }
split; [img_try (img_exact A10)|]. split; [img_try (img_exact QT2)|].
split; [|img_try (rewrite <- EQ; img_exact MP)].
split.
{
img_apply (AR_frame_law_ok tfxsegs B ly2 S2 W2 memM mdM mem' md' AR2).
- intros a Ra Ho. img_apply NSC; [img_try (img_exact Ra)|]. unfold ascratch. rewrite (ts_errno B TB). intros [X|X].
+ img_apply (AR_stack_law_ok tfxsegs B ly2 S2 W2 memM mdM a AR2); [img_try (rewrite Eslo, Eshi; unfold spZ, ASTACK in *; img_lia) | img_try (img_exact Ho)].
+ img_exact (errno_not_owned B TB ly2 S2 W2 memM mdM a AR2 X Ho).
- intros a Hv. rewrite (YE0v.aview_mod _ mem' a). rewrite (YE0v.aview_mod _ memM a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (img_try (img_apply Z.mod_pos_bound; img_lia)). set (a' := a mod 2 ^ 64) in *.
destruct (Z_le_gt_dec (spZ R - ASTACK) a') as [L1|L1]; [img_try (destruct (Z_lt_le_dec a' (spZ R)) as [L2|L2])|].
{ img_apply YE0v.aview_some_of_apresent. img_apply PRN. unfold spZ in *. img_lia. }
all: destruct (Z_le_gt_dec TFX_ERRNO a') as [L3|L3]; [img_try (destruct (Z_lt_le_dec a' (TFX_ERRNO + 4)) as [L4|L4]; [img_apply aview_rw_some; unfold TFX_ERRNO in *; img_lia|])|].
all: rewrite NSC; [img_try (img_exact Hv) | img_try (img_exact Hr) | img_try (unfold ascratch; rewrite (ts_errno B TB); img_lia)].
- img_apply m_vmmaps_wvb.
- img_apply m_vm_lazy_wvb.
- img_apply eager_used_wvb.
- intros a Hb Hh. unfold YG0u.w64. img_apply FRN;
unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, TFX_ERRNO, TFX_IMG_END, ASTACK, spZ in *;
rewrite unsigned_lit_small by img_lia; img_lia. }
split; [img_try (img_exact LLE0)|]. split; [img_try (img_exact WLE)|].
split; [img_try (img_exact (same_io_trans _ _ _ (same_io_trans _ _ _ HIOU SIO) (same_io_wvb mdM mat)))|].
split.
- intros a Ra NO NO2 NS _. rewrite (NSC a Ra NS).
assert (N1 : ~ aowned B ly s1 a) by (img_try (intros O; img_apply NO; img_exact (proj1 (aowned_s1 B ly S a) O))).
rewrite (FRB a Ra N1 NO2); [img_exact (HFRU a Ra NO N1 NS) | unfold ascratch in NS |- *; rewrite spV; img_exact NS |].
intros [Hne _]. img_exact (Hne EQ).
- intros a Ha. img_apply PRN. img_exact Ha.
Qed.
End h.
Lemma sptr_null_dec : forall p : sptr, {p = PNull} + {p <> PNull}.
Proof. intros p. destruct p; [img_try (left; img_refl) | img_try (right; discriminate) | img_try (right; discriminate) | img_try (right; discriminate)]. Qed.
Theorem tfx_arealloc {imgk : img} : forall B, TfxSyms B -> (forall t, as_dhash B t = tfx_dhash t) ->
arealloc_realizes tfxsegs B (0x53108 + D_2c4) (0x53640 + D_2c4).
Proof.
intros B TB HD ly S W R mem md pp nold rn ch PRE Hev HBLK HA0 HA1 Nrange Hlive Htr.
set (tr := call_trace ly (0x53640 + D_2c4) R ch) in *. set (s1 := realloc_s1 S).
pose proof PRE as PRE'. destruct PRE' as (HAR0 & Hev0 & Hra & Hal & Hlo & Hbot & Hhi & HPRES & Hgp & Htp & Hch & HQT).
pose proof (proj1 HAR0) as M0.
assert (HTSD : ly_tsd ly = TFX_TSD) by (img_try (rewrite (am_tsd B ly S _ M0); img_apply (ts_tsd _ TB))).
assert (TJ2 : forall a, ly_T ly + t_stats <= a -> a + 8 <= ly_T ly + t_unwinding -> exists w, val_mem tfxsegs (mrestrict (w_H W) mem) a 8 w).
{ intros a Ha1 Ha2. img_apply (YF79.junk_at B ly S W R mem md ch PRE (AT t_stats) (t_unwinding - t_stats) a); [| img_try (cbn [aeval]; img_lia) | img_try (cbn [aeval]; img_lia)].
unfold ajunk. right; right. do 5 (img_apply in_or_app; right). img_apply in_or_app; left. unfold thread_junk. cbn. tauto. }
destruct (TJ2 (ly_T ly + 2856)) as [jr1 Hjr1]; [img_try (unfold t_stats; img_lia) | img_try (unfold t_unwinding; img_lia) |].
destruct (TJ2 (ly_T ly + 2864)) as [jr2 Hjr2]; [img_try (unfold t_stats; img_lia) | img_try (unfold t_unwinding; img_lia) |].
unfold realloc_tree.
eapply amreal_mbind.
- img_exact (pa_arm B TB ly S W R mem md pp nold rn ch PRE HBLK HA0 HA1 ltac:(img_try (unfold MALLOC_MAX in *; img_lia)) jr1 jr2 Hjr1 Hjr2 tfx_ialloc_ok tfx_unwind_ok HTSD).
- intros [] s' W' c' (Es & EW & U & memU & mdU & -> & (HARU & _ & HIOU & HFRU & HPRU) & HPA & HPB & HCHU & HQT'). cbn [snd] in Es, HARU, HQT', HFRU. (subst s' W'; cbv beta).
fold tr in HPA, HPB. fold s1 in HARU, HQT', HFRU. img_change (set_internal_inited true (set_nev (st_nev S + 1) S)) with s1 in *.
assert (HL : 1 <= Z.of_nat (length tr) <= 30).
{ pose proof (YF7f.unwind_of_chain_length (0x53640 + D_2c4) ((spZ R, raZ R, s0Z R) :: ch)) as LEN. unfold tr, call_trace. destruct (frame0_ok ly R); cbn [length]; img_lia. }
assert (HH : kHighMemBeg <= ly_stk_lo ly).
{ pose proof (lo_top ly (am_layout B ly S _ M0)) as (_ & _ & _ & _ & _ & _ & T7). img_exact T7. }
assert (E2 : getr (virt R U) 2 = getr R 2) by (img_try (img_apply virt_same; cbn [In]; tauto)).
assert (E1 : getr (virt R U) 1 = getr R 1) by (img_try (img_apply virt_same; cbn [In]; tauto)).
assert (E8 : getr (virt R U) 8 = getr R 8) by (img_try (img_apply virt_same; cbn [In]; tauto)).
assert (PREv : acall_pre tfxsegs B ly s1 W (virt R U) memU mdU ch).
{ img_apply (pre_regs B R ch ly s1 W (virt R U) memU mdU); [| img_try (img_exact E1) | img_try (img_exact E2) | img_try (img_apply virt_same; cbn [In]; tauto) | img_try (img_apply virt_same; cbn [In]; tauto) | img_try (img_exact E8)].
img_apply (pre_transport B ly S W R mem md ch PRE 0%nat ly s1 W memU mdU HARU (aregime3_s1 (as_universe B) S rn (am_wf B ly S _ M0) ltac:(img_try (clear - Nrange; img_lia)) Hev) (layout_le_refl _ _) HPRU HCHU HQT'). }
assert (PBUF0 : YF7a.PBUF W ly (virt R U) ch memU).
{ unfold YF7a.PBUF, YF7f.tr. rewrite call_trace_virt. fold tr. intros i Hi. rewrite E2.
replace (bv_unsigned (getr R 2) - IFRAME + 16 + 8 * Z.of_nat i) with (spZ R - 2120 + 8 * Z.of_nat i) by (img_try (unfold IFRAME, spZ; img_lia)). img_exact (HPB i Hi). }
pose proof (malloc_sec B TB (tfx_depot_ok B TB HD) ly s1 W (virt R U) memU mdU rn ch PREv ltac:(img_try (rewrite virt_10; img_exact HA1)) Nrange) as MS.
rewrite call_trace_virt in MS. fold tr in MS.
assert (SPH : TFX_IMG_END + ASTACK <= bv_unsigned (getr R 2)) by (img_try (clear - Hlo HH; unfold spZ, kHighMemBeg, TFX_IMG_END, ASTACK in *; img_lia)).
specialize (MS Htr ltac:(img_try (unfold s1, realloc_s1; img_exact Hlive)) U (REGSU_of R U (Z.of_nat (length tr)) (w_H W) memU HPA)
(STKU_of R U (Z.of_nat (length tr)) (w_H W) memU HPA ltac:(img_try (clear - HL; img_lia)) SPH HPRU) PBUF0).
eapply amreal_mbind with (P := fun r W2 c2 => (exists ns, realloc_mpost (as_universe B) S rn ns r) /\ mid_leaf B ly s1 W (virt R U) memU mdU rn tr r W2 c2).
+ eapply (amreal_atok _ true (realloc_mpost (as_universe B) S rn)).
{ img_exact (realloc_malloc_ok (as_universe B) S rn tr (ts_universe B TB) (am_wf B ly S _ M0) Hev Nrange Hlive Htr). }
eapply amreal_mono; [|img_try (img_exact MS)]. intros r W2 c2 HM HP. split; [img_try (img_exact HP) | img_try (img_exact HM)].
+ intros q S2 W2 c2 (MP & (ly2 & regsM & memM & mdM & -> & PBM & (AR2 & LLE & WLE & MST & SIO & FRB & PRB) & A0M & QT2)). cbn [fst snd] in *.
destruct (sptr_null_dec q) as [EQ | HQ].
*
rewrite EQ. cbn [YG00.ret amreal].
img_exact (null_arm B TB ly S W R mem md ch PRE pp nold rn HA0 HA1 Nrange U memU mdU HIOU HFRU q S2 W2 ly2 regsM memM mdM MP AR2 LLE WLE MST SIO FRB PRB A0M QT2 EQ).
*
assert (SUCC : amreal tfxsegs (YG00.bind (free pp tr) (fun _ => YG00.ret q) S2) W2 (cfg_at tfxsegs (0x323bc + D_150) regsM memM mdM)
(realloc_leaf tfxsegs B ly S W R mem md pp nold rn)).
{ eapply amreal_SRr_pre.
{ img_exact (c1_at_mid B TB ly S W R mem md ch PRE pp nold rn HBLK HA0 HA1 Nrange Hev U memU mdU HCHU q S2 W2 ly2 regsM memM mdM MP AR2 LLE MST FRB PRB A0M QT2 HARU HQ). }
intros W3 c3 _ (-> & regsD & memD & matD & -> & D1 & D10 & D11 & D12 & D13 & D14 & D15 & D19 & D20 & DK & DM & DC & DP).
eapply amreal_mbind.
{ img_exact (c2_arm B TB ly S W R mem md ch PRE pp nold rn HBLK HA0 HA1 Nrange Hev Htr U memU mdU HCHU q S2 W2 ly2 regsM memM mdM MP AR2 LLE MST FRB PRB A0M QT2 PBM HARU HQ
regsD memD matD D1 D10 D11 D12 D13 D14 D15 D20 DK DM DP HD). }
intros [] S3 W4 c4 (FP & RL). img_apply amreal_ret.
img_exact (succ_leaf B TB ly S W R mem md ch PRE pp nold rn HBLK Nrange Hev U memU mdU HIOU HFRU HCHU q S2 W2 ly2 regsM memM mdM MP AR2 LLE WLE SIO FRB PRB A0M QT2 HARU HQ
regsD memD matD D20 DM DP DC S3 W4 c4 FP RL). }
destruct q; [img_try (img_exact (False_ind _ (HQ eq_refl))) | img_try (img_exact SUCC) | img_try (img_exact SUCC) | img_try (img_exact SUCC)].
Qed.
End d.
