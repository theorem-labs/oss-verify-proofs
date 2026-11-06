(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI03 YI04 YI06 YCfy.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YF9i YCeb YCe8 YCfq YCdv YCe5 YCe9 YCfx YCex YCev YCf8 YCfa.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition FBAND : Z := 8192.
Definition A_bcmp_icpt : Z := 0x4239c.
Section WF.
Variable B : asyms.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ABCMP : abcmp_realizes trbsegs B A_bcmp_icpt.
Definition wkeptF (lyc : alayout) (Sc : astate) (W : world trbsegs) (sp1 : Z) (memc m : word -> option byte) : Prop :=
acall_kept trbsegs B lyc Sc W memc W m (sp1 - FBAND) (sp1 + 232) (fun _ => False) /\
(forall a, sp1 <= a < sp1 + 232 -> ~ wscr sp1 a -> aview trbsegs (w_H W) m a = aview trbsegs (w_H W) memc a).
Lemma wkeptF_trans : forall lyc Sc W sp1 m0 m1 m2, wkeptF lyc Sc W sp1 m0 m1 -> wkeptF lyc Sc W sp1 m1 m2 -> wkeptF lyc Sc W sp1 m0 m2.
Proof.
intros lyc Sc W sp1 m0 m1 m2 [K1 X1] [K2 X2]. split; [exact (acall_kept_trans B _ _ _ _ _ _ _ _ _ K1 K2)|].
intros a Ha Hs. rewrite (X2 a Ha Hs). exact (X1 a Ha Hs).
Qed.
Lemma wkeptF_refl : forall lyc Sc W sp1 m, (forall a, sp1 - FBAND <= a < sp1 + 232 -> apresent (w_H W) m a) -> wkeptF lyc Sc W sp1 m m.
Proof.
intros lyc Sc W sp1 m Hp. split; [|intros; reflexivity].
split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
split; [intros a _ _ H; exact H | exact Hp].
Qed.

Lemma wkeptF_of_run : forall E rs lyc Sc W (m m' : word -> option byte) md sp1,
AR trbsegs B lyc Sc W m md ->
frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
(forall a, in_wrange E rs a -> wscr sp1 a) -> alloc_ceiling <= sp1 - FBAND -> sp1 + 232 <= 2 ^ 64 ->
(forall a, sp1 - FBAND <= a < sp1 + 232 -> apresent (w_H W) m a) ->
wkeptF lyc Sc W sp1 m m'.
Proof.
intros E rs lyc Sc W m m' md sp1 HAR HFr HG Hw Hceil Hhi Hp. unfold wkeptF. unfold FBAND in *. split.
- apply (acall_kept_of_run B LAWS E rs lyc Sc W m m' md _ _ (fun _ => False) HAR HFr HG); [| intros a [] | exact Hceil | exact Hp].
intros a Ha. right. pose proof (Hw a Ha) as Hs. unfold wscr in Hs. lia.
- intros a Ha Hs. apply (aview_kept_out E rs _ m m' HFr a); [|intros Hin; exact (Hs (Hw a Hin))].
pose proof asan_consts as (C1 & _). lia.
Qed.
Lemma val_mem_wkeptF : forall lyc Sc W sp1 (m m' : word -> option byte) off v,
wkeptF lyc Sc W sp1 m m' -> 0 <= sp1 -> sp1 + 280 <= 2 ^ 64 -> alloc_ceiling <= sp1 ->
0 <= off -> off + 8 <= 280 -> (forall k, 0 <= k < 8 -> ~ wscr sp1 (sp1 + off + k)) ->
val_mem trbsegs (mrestrict (w_H W) m) (sp1 + off) 8 v -> val_mem trbsegs (mrestrict (w_H W) m') (sp1 + off) 8 v.
Proof.
intros lyc Sc W sp1 m m' off v [K X] H0 H64 Hc Ho1 Ho2 Hns Hv kk Hkk. rewrite <- (Hv kk Hkk). apply (mbyte_of_aview trbsegs).
cbn [Z.of_nat] in Hkk.
destruct (Z_lt_le_dec (off + Z.of_nat kk) 232).
- apply X; [lia | replace (sp1 + off + Z.of_nat kk) with (sp1 + off + Z.of_nat kk) by lia; apply Hns; lia].
- pose proof K as (K1 & _). apply K1; lia.
Qed.
Lemma wimg_byteF : forall lyc Sc W sp1 (memc m : word -> option byte) md b n p,
wkeptF lyc Sc W sp1 memc m -> AR trbsegs B lyc Sc W m md -> In (b, n) (ablocks B lyc Sc) -> 0 <= p < n ->
val_mem trbsegs (mrestrict (w_H W) m) (b + p) 1 (bval (aview trbsegs (w_H W) memc) (b + p)) /\
0 <= bval (aview trbsegs (w_H W) memc) (b + p) < 256 /\
aview trbsegs (w_H W) m (b + p) = aview trbsegs (w_H W) memc (b + p) /\
aview trbsegs (w_H W) memc (b + p) = Some (bval (aview trbsegs (w_H W) memc) (b + p)).
Proof.
intros lyc Sc W sp1 memc m md b n p [K _] HAR Hin Hp.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR Hin) as (_ & _ & _ & _ & Hpres & _). pose proof (req_size_pos' n ltac:(lia)) as [_ Hrn].
destruct (val_mem_byte1 (w_H W) m (b + p) (proj1 (Hpres (b + p) ltac:(lia)))) as (v & Rv & Vv).
pose proof K as (_ & K2 & _). pose proof (K2 b n p Hin ltac:(lia) (fun H : False => H)) as Eq.
assert (Hb : aview trbsegs (w_H W) memc (b + p) = Some v).
{ rewrite <- Eq. unfold aview. pose proof (Vv 0%nat ltac:(lia)) as V0. cbn [Z.of_nat] in V0. rewrite Z.add_0_r in V0. rewrite V0. cbn. f_equal.
rewrite Z_to_bv_unsigned. unfold YP0g.le_byte, bv_wrap. change (8 * Z.of_nat 0) with 0. change (2 ^ (8 * Z.of_nat 1)) with 256. change (bv_modulus 8) with 256.
rewrite Z.shiftr_0_r. rewrite (Z.mod_small v 256) by lia. rewrite (Z.mod_small v 256) by lia. apply Z.mod_small. lia. }
unfold bval. rewrite Hb. split; [exact Vv|]. split; [exact Rv|]. split; [rewrite Eq; exact Hb | reflexivity].
Qed.
Section d.
Variables (W : world trbsegs) (regs : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (sp0 sp1 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (W0 : world trbsegs) (mem0 : word -> option byte) (md0 : Model) (lyc : alayout) (Sc : astate) (k : Z) (fpos : Z)
(ch1 : list (Z * Z * Z)) (fimg bimg Nb g cfp bfp : Z) (gvals cvals bvals : list Z) (gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx : Z).
Hypothesis HC : wctx B W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx.
Ltac wctx_names :=
pose proof HC as (HJc & Hfi & Hbi & HNb & Dfb & Hg & Hcf & Hbf & Hcb & Og & Ogpal & Ongp & Oc & Ocpal & Ocattr & Ocnlp & Octidx
& Ob & Obpal & Obattr & Obnlp & Obtidx & HLc & HLb & HGp & Hsp & Hsp1 & Hsp1al & H9 & Hgp & Htp & Hch & Hs0 & Vsb & Vbfp).
Definition BD (p : Z) : Prop := aview trbsegs (w_H W) memc (fimg + p) <> aview trbsegs (w_H W) memc (bimg + p).
Lemma bcmp_callW : forall (regsT : bvmap 5 word) memT mdT (x n : Z) (raw : word),
ajournal trbsegs B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(1, fpos)] lyc Sc W memT mdT k -> wkeptF lyc Sc W sp1 memc memT ->
0 <= x -> 0 <= n -> x + n <= Nb ->
spZ regsT = sp1 -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 10 = Z_to_bv 64 (fimg + x) -> getr regsT 11 = Z_to_bv 64 (bimg + x) -> getr regsT 12 = Z_to_bv 64 n ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
SRr trbsegs W (mkCfg (mkst regsT (Z_to_bv 64 A_bcmp_icpt) memT (seg_rom trbsegs)) mdT)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : word),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom trbsegs)) md2 /\
ajournal trbsegs B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(1, fpos)] lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = v /\ (v = w64 0 <-> forall i, 0 <= i < n -> ~ BD (x + i)) /\
wkeptF lyc Sc W sp1 memc mem2 /\
acall_kept trbsegs B lyc Sc W memT W mem2 (sp1 - FBAND) sp1 (fun _ => False) /\ lkept W sp1 memT mem2).
Proof.
intros regsT memT mdT x n raw HJT WK Hx Hn Hxn Qsp Qgp Qtp Q10 Q11 Q12 Qra Hraw. wctx_names.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof trb_segs_low as Hsegs.
pose proof HJT as (HART & HLY & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSpresT & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (FFS : TFLUSH_STK = 17440) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity. assert (HFB : FBAND = 8192) by reflexivity.
pose proof Hslo as Hslo'. rewrite FFS in Hslo'.
destruct (al_blocks _ _ LAWS _ _ _ _ _ fimg Nb HART Hfi) as (_ & Hf4096 & Hfceil & Hfh_ia & Hfpres & _). pose proof (proj1 Hfh_ia) as Hfh.
pose proof (blk_off_img _ _ _ _ _ _ fimg Nb HART Hfi) as Hfh_img.
destruct (al_blocks _ _ LAWS _ _ _ _ _ bimg Nb HART Hbi) as (_ & Hb4096 & Hbceil & Hbh_ia & Hbpres & _). pose proof (proj1 Hbh_ia) as Hbh.
pose proof (blk_off_img _ _ _ _ _ _ bimg Nb HART Hbi) as Hbh_img.
pose proof (req_size_pos' Nb ltac:(lia)) as [_ HrNb].
assert (Usp : spZ regsT = sp0 + (sp1 - sp0)) by lia.
eapply SRr_mono.
{ eapply (aj_bcmp_at trbsegs B LAWS Hsegs A_bcmp_icpt ABCMP W regsT memT TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(1, fpos)]
lyc Sc mdT k (fimg + x) (bimg + x) n (sp1 - sp0) raw HJT).
- rewrite Q10; reflexivity. - rewrite Q11; reflexivity. - rewrite Q12; reflexivity.
- lia. - lia. - lia. - lia. - lia.
- exact Usp. - rewrite Zminus_mod, Hsp1al, Hal16; reflexivity. - lia. - rewrite Hes, FFS; lia.
- exact Qgp. - exact Qtp. - exact Qra. - exact Hraw.
- intros a Ha. split; [apply (aview_some_of_apresent trbsegs); apply (fun Hq => proj1 (Hfpres a Hq)); lia | rewrite Qsp, Hes; lia].
- intros a Ha. split; [apply (aview_some_of_apresent trbsegs); apply (fun Hq => proj1 (Hbpres a Hq)); lia | rewrite Qsp, Hes; lia].
- intros a Ha. rewrite Hes. lia. - intros a Ha. rewrite Hes. lia.
- apply (amem_range_of_block trbsegs B LAWS lyc Sc _ _ _ fimg Nb _ _ HART Hfi); lia.
- apply (amem_range_of_block trbsegs B LAWS lyc Sc _ _ _ bimg Nb _ _ HART Hbi); lia.
- apply (range_addressable_of_block trbsegs B LAWS lyc Sc _ _ _ fimg Nb _ _ HART Hfi); lia.
- intros Hn0. apply (shadow_hull_vis_of_block trbsegs B LAWS lyc Sc _ _ _ fimg Nb _ _ HART Hfi); lia.
- apply (range_addressable_of_block trbsegs B LAWS lyc Sc _ _ _ bimg Nb _ _ HART Hbi); lia.
- intros Hn0. apply (shadow_hull_vis_of_block trbsegs B LAWS lyc Sc _ _ _ bimg Nb _ _ HART Hbi); lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr & Hpr2).
split; [reflexivity|]. exists regs2, mem2, md2, v. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact Hv|].
replace (sp0 + (sp1 - sp0)) with sp1 in Hfr by lia. rewrite Hes in Hfr.
assert (Kc : acall_kept trbsegs B lyc Sc W memT W mem2 (sp1 - FBAND) sp1 (fun _ => False)).
{ rewrite HFB. split; [intros a Ha Hna; apply Hfr; lia|].
split; [intros b m i Hbm Hi _; destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HART Hbm) as (_ & Hb40 & Hbc & _); pose proof (req_size_pos' m ltac:(destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HART Hbm) as (_ & _ & _ & _ & _ & _ & Hm0 & _); lia)) as [_ Hrm]; apply Hfr; lia|].
split; [intros a Hia _ _; apply Hfr; [pose proof (Hsegs a Hia); lia | pose proof (Hsegs a Hia); lia]|].
split.
{ intros cid pos a Hin Hrng _. destruct (frames_bounds trbsegs B LAWS _ _ _ _ _ cid pos HART Hin) as (Hf40 & Hfc & Hfhi).
pose proof (fs_frame_bytes_nonneg cid) as Hfb.
pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)) as D1.
assert (D2 : frame_addr lyc cid pos / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
pose proof (Z.div_pos (fs_frame_bytes cid) 8 ltac:(lia) ltac:(lia)) as D3.
assert (D4 : fs_frame_bytes cid / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
apply Hfr; destruct Hrng as [Hr | Hr]; unfold in_zr, frame_rng, shadow_addr in Hr; cbn [fst snd] in Hr; unfold SHADOW_OFF in *; lia. }
split; [intros a Ha Hna Hp; apply Hpr2; exact Hp|].
intros a Ha. apply Hpr2. apply HSpresT. rewrite FFS. lia. }
assert (WK2 : wkeptF lyc Sc W sp1 memT mem2).
{ split.
- apply (acall_kept_band B _ _ _ _ _ _ _ _ _ _ Kc); [lia | lia |]. intros a Ha. apply Hpr2. apply HSpresT. rewrite HFB in Ha. rewrite FFS. lia.
- intros a Ha Hs. apply Hfr; [lia | lia]. }
split.
{ rewrite Hcmp. split; intros X i Hi.
- intros D. apply D. pose proof WK as [K0 _]. pose proof K0 as (_ & K02 & _).
rewrite <- (K02 fimg Nb (x + i) Hfi ltac:(lia) (fun H : False => H)), <- (K02 bimg Nb (x + i) Hbi ltac:(lia) (fun H : False => H)).
replace (fimg + (x + i)) with (fimg + x + i) by lia. replace (bimg + (x + i)) with (bimg + x + i) by lia. exact (X i Hi).
- pose proof WK as [K0 _]. pose proof K0 as (_ & K02 & _).
rewrite (K02 fimg Nb (x + i) Hfi ltac:(lia) (fun H : False => H)) || replace (fimg + x + i) with (fimg + (x + i)) by lia.
replace (fimg + x + i) with (fimg + (x + i)) by lia. replace (bimg + x + i) with (bimg + (x + i)) by lia.
rewrite (K02 fimg Nb (x + i) Hfi ltac:(lia) (fun H : False => H)), (K02 bimg Nb (x + i) Hbi ltac:(lia) (fun H : False => H)).
destruct (Classical_Prop.classic (aview trbsegs (w_H W) memc (fimg + (x + i)) = aview trbsegs (w_H W) memc (bimg + (x + i)))) as [Y|Y]; [exact Y | exfalso; exact (X i Hi Y)]. }
split; [exact (wkeptF_trans _ _ _ _ _ _ _ WK WK2)|]. split; [exact Kc|].
intros a Ha. apply Hfr; [lia | lia].
Qed.
End d.
End WF.
End c.
