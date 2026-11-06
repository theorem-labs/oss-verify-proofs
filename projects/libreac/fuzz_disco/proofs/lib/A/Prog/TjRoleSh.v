(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: relocated from the walk of the same function of libreac's fuzz_grant (the two are the same code at other addresses); the context, the cut specifications and the tactics are restated on fuzz_disco's contract, treac_ctrl_parse_spec. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/CtrlParseCut.v, with its module paths, module names and numbers changed; 927 of its 964 lines of code are new or changed and 446 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YCkd.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaRun PaShadow PaStep DiscoSyms DiscoList DiscoAddr DiscoPa.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaJournal DiscoPaLib YC1g YC1h YC81 YC4b DiscoFrame YC45 YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoBase YC1i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import TjSpec TjBase DiscoRo TjCuts TjLoopCuts TjSnSh.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnShared PfFacts SnprintfDef SnprintfDefR.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_json_text.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require tj_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_json_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import AmemBlock8.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma tjr_sub : forall c l z, zcanon z = 2 ^ 64 - 1 -> 0 <= l <= c -> c < 2 ^ 63 -> zcanon (c + zcanon (l * zcanon z)) = c - l.
Proof.
intros c l z Hz Hl Hc. rewrite Hz. unfold zcanon, M64.
destruct (Z.eq_dec l 0) as [->|Hl0].
- rewrite Z.mul_0_l, Zmod_0_l, Z.add_0_r, Z.sub_0_r. apply Z.mod_small. lia.
- replace (l * (2 ^ 64 - 1)) with ((2 ^ 64 - l) + (l - 1) * 2 ^ 64) by ring.
rewrite Z_mod_plus_full, (Z.mod_small (2 ^ 64 - l)) by lia.
replace (c + (2 ^ 64 - l)) with ((c - l) + 1 * 2 ^ 64) by ring.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Ltac notw AG :=
let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg; lia|]);
destruct Hin.
Local Ltac notwG AG Ha HG :=
let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG;
clear - Ha HG; unbox; intros Hrg; lia|]);
destruct Hin.
Local Ltac glia := first [match goal with HG : boxed _ |- _ => clear - HG; unbox; lia end | clear; lia | lia].
Ltac fa2 tac := apply Forall_cons; [tac | apply Forall_cons; [tac | apply Forall_nil]].
Ltac tjr_hd AG HSK :=
lazymatch goal with
| |- awr_ok _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | evalE AG | clear - HSK; cbn; lia | clear; cbn; lia |]
| |- awr_ok _ (YP09.mkRegion (Some 60%nat) _ _ _ _ _ :: _) _ ?sp0 _ _ _ _ _ =>
lazymatch goal with Hsp1 : sp0 - _ <= ?sp1 <= sp0 - _ |- _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (sp1 - sp0)); [reflexivity | evalE AG | clear - Hsp1 HSK; cbn; lia | clear - Hsp1; cbn; lia |] end
end.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
Context {RO : ro_below_ofl (@pa_segs _ disco_listing PI) (@pa_relro_lo _ disco_listing PI) (@pa_relro_hi _ disco_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Lemma tjr_vm4 : forall (m : word -> option byte) p (T : list byte) k,
garr8 SEGS m p (map bv_unsigned T) -> 0 <= k -> k + 4 <= Z.of_nat (length T) ->
val_mem SEGS m (p + k) 4 (disco_table_c.s32_at T k).
Proof.
intros m p T k HG Hk Hlen j Hj.
unfold disco_table_c.s32_at, disco_table_c.u_at, disco_table_c.sub.
set (bs := firstn 4 (skipn (Z.to_nat k) T)).
assert (Hbs : length bs = 4%nat) by (unfold bs; rewrite length_firstn, length_skipn; lia).
pose proof (bytes_le_to_Z_nonneg bs) as Hu0. pose proof (bytes_le_to_Z_bound bs) as Hu1. rewrite Hbs in Hu1.
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Hu1.
assert (Hsw : bv_swrap 32 (bytes_le_to_Z bs) mod 2 ^ 32 = bytes_le_to_Z bs).
{ unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
rewrite Zminus_mod, Z.mod_mod by lia. rewrite <- Zminus_mod.
replace (bytes_le_to_Z bs + 2 ^ 31 - 2 ^ 31) with (bytes_le_to_Z bs) by ring. apply Z.mod_small. lia. }
assert (Hle : YO0f.le_byte (bv_swrap 32 (bytes_le_to_Z bs)) 4 j = bv_unsigned (nth j bs (Z_to_bv 8 0))).
{ rewrite <- (YK0w.zb_of_bytes bs j ltac:(lia)). unfold YO0f.le_byte, YK0w.HZ.zb.
change (8 * Z.of_nat 4) with 32. rewrite Hsw. rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
rewrite Hle.
assert (Hn : nth j bs (Z_to_bv 8 0) = nth (Z.to_nat k + j) T (Z_to_bv 8 0)).
{ unfold bs. rewrite nth_firstn. destruct (Nat.ltb_spec j 4) as [_|]; [|lia]. cbn [andb]. rewrite nth_skipn. reflexivity. }
rewrite Hn.
assert (Hj2 : (Z.to_nat k + j < length (map bv_unsigned T))%nat) by (rewrite length_map; lia).
destruct (HG _ Hj2) as [Hv Hr].
pose proof (Hv 0%nat ltac:(lia)) as Hv0.
change (bv_unsigned (Z_to_bv 8 0)) with 0 in *.
rewrite (map_nth bv_unsigned T (Z_to_bv 8 0)) in Hv0, Hr.
rewrite le_byte_1_0 in Hv0 by exact Hr.
replace (p + k + Z.of_nat j) with (p + Z.of_nat (Z.to_nat k + j) + Z.of_nat 0) by lia.
exact Hv0.
Qed.
Section h.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Variables SNPC GC GV IMGLO IMGHI : Z.
Variable CR : list (Z * Z).
Hypothesis HSNPC : pa_sigma DS___interceptor_trampoline_snprintf = SNPC.
Hypothesis ASNP : forall fq : YK11.FPState,
SnprintfDefR.asnprintf_realizesR (fx := fq) SEGS B pa_relro_lo pa_relro_hi GC GV IMGLO IMGHI disco_fmt_lo disco_fmt_hi CR SNPC.
Hypothesis tj_snp_consts : forall (W : world SEGS) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> consts_view SEGS W mem CR.
Hypothesis tj_snp_cr : Forall (fun r => IMG_LO <= fst r /\ 0 <= snd r /\ fst r + snd r <= IMG_TOP) CR.
Hypothesis tj_snp_canary : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
exists cval, rdword (aview SEGS (w_H W) mem) GC = Some GV /\ rdword (aview SEGS (w_H W) mem) GV = Some cval.
Hypothesis tj_snp_gcgv : IMG_LO <= GC /\ GC + 8 <= IMG_TOP /\ IMG_LO <= GV /\ GV + 8 <= IMG_TOP.
Hypothesis tj_snp_img : IMG_LO <= IMGLO /\ IMGHI <= IMG_TOP.
Hypothesis DRO : disco_ro_unowned B.
Hypothesis GM : globs_marked SEGS B disco_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Hypothesis TJS : tj_strs.
Hypothesis tj_pad : forall k s, tj_ro_at k s -> forall x, VAL (A_OBJ k) + Z.of_nat (length s) < x < str_end (VAL (A_OBJ k)) s -> seg_rom SEGS (Z_to_bv 64 x) <> None.
Variables STK EV EVB : Z.
Variable IMG : world SEGS -> (word -> option byte) -> Prop.
Hypothesis HSTK : TJ_FRAME + SNPRINTF_STK <= STK.
Hypothesis HEVB : 0 <= EVB.
Hypothesis HEV : 8 * EVB <= EV.
Lemma tjr_keep : forall cx ly' S' W' mem' md' k',
tj_baseX B STK EV IMG cx ->
ajournal SEGS B STK (spZ (c_regs cx)) (tj_fp (c_buf cx) (c_cap cx)) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(2, c_fpos cx)] ly' S' W' mem' md' k' ->
tj_keep B cx W' mem'.
Proof.
intros cx ly' S' W' mem' md' k' HB HJ.
destruct cx as [fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0].
unfold tj_baseX in HB. unfold tj_keep.
cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0] in *.
destruct HB as (HPRE & Hfrm0 & Hroom & HROD & HIM & H10 & H11 & H12 & H13 & Hnow & Hcap & Hobj & Harr & HlenT & Hok
& Hbuf & Hev & Hsp1b & HE0 & HE032 & HE02).
pose proof HPRE as (HAR & _).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct Hobj as ((cid & pos & Hin & Hcid & Hal & Hlo & Hhi) & Ht8 & Hra).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hin) as (HT4096 & HTceil & HTapp).
assert (HnF : forall x, t <= x < t + 400 -> ~ inFP (tj_fp buf cap) x).
{ intros x Hx (r & Hr & Hrx). unfold tj_fp in Hr. destruct (Z.ltb_spec cap 3) as [_|Hc3]; [destruct Hr|].
destruct Hr as [<- | []]. cbn [fst snd] in Hrx.
destruct (Hbuf Hc3) as (Hinb & Hcb).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ buf Nb cid pos HAR Hinb Hin) as Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. lia. }
split; [exact (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROD)|].
split.
- intros j Hj. destruct (Harr j Hj) as [Hv Hr]. split; [|exact Hr].
rewrite length_map, HlenT in Hj.
eapply (val_mem_entry_frame SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cid pos); [exact HJ | exact Hin | lia | cbn [Z.of_nat]; lia | | exact Hv].
intros x Hx. apply HnF. cbn [Z.of_nat] in Hx. lia.
- split; [exists cid, pos; repeat split; assumption|]. split; [exact Ht8|].
eapply (range_addressable_entry_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cid pos); [exact HJ | exact Hin | exact Hcid | lia | lia | exact Hal | | exact HAR | exact Hra].
intros x (r & Hr & Hrx). unfold tj_fp in Hr. destruct (Z.ltb_spec cap 3) as [_|Hc3]; [destruct Hr|].
destruct Hr as [<- | []]. cbn [fst snd] in Hrx.
destruct (Hbuf Hc3) as (Hinb & Hcb).
destruct (al_blocks _ _ LAWS _ _ _ _ _ buf Nb HAR Hinb) as (_ & _ & _ & Hbapp & _).
unfold in_app, kLowShadowBeg, kHighMemBeg in *. rewrite C2. lia.
Qed.
Lemma tjr_garr : forall (m : word -> option byte) (H : word -> bool) d (q : list Z),
(forall i, 0 <= i < Z.of_nat (length q) -> aview SEGS H m (d + i) = Some (nth (Z.to_nat i) q 0)) ->
aview SEGS H m (d + Z.of_nat (length q)) = Some 0 ->
garr8 SEGS (mrestrict H m) d (q ++ [0]).
Proof.
intros m H d q Hd Hz j Hj. rewrite length_app in Hj. cbn [length] in Hj.
destruct (Nat.ltb_spec j (length q)) as [Hlt|Hge].
- rewrite app_nth1 by exact Hlt.
pose proof (Hd (Z.of_nat j) ltac:(lia)) as Hq. rewrite Nat2Z.id in Hq.
exact (val_mem1_of_aview SEGS H m (d + Z.of_nat j) _ Hq).
- assert (Hje : j = length q) by lia. subst j.
rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
exact (val_mem1_of_aview SEGS H m (d + Z.of_nat (length q)) 0 Hz).
Qed.
Lemma tjr_str : forall kk s ly S (W : world SEGS) mem md sp d n,
AR SEGS B ly S W mem md ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
tj_ro_at kk s ->
IMG_TOP + 8 <= sp - SNPRINTF_STK ->
(d + n <= IMG_LO \/ IMG_TOP <= d) ->
pf_arg_asan (aview SEGS (w_H W) mem) (snp_out SNPRINTF_STK sp d n) (VAL (A_OBJ kk)) (APtr s) /\
fmt_at (aview SEGS (w_H W) mem) (snp_out SNPRINTF_STK sp d n) (VAL (A_OBJ kk)) s.
Proof.
intros kk s ly S W mem md sp d n HAR HROD Hro Hsp Hdn.
pose proof Hro as (Hg & Hrr & Hlo & Hhi & Hc & Hb).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (HIL : 0 < IMG_LO) by (unfold IMG_LO; lia).
assert (HIT : IMG_TOP + 64 < kLowMemEnd) by (rewrite C5; unfold IMG_TOP; lia).
set (w := VAL (A_OBJ kk)) in *. set (L := Z.of_nat (length s)) in *.
pose proof (Z.mod_pos_bound (w + L) 8 ltac:(lia)) as Hm.
assert (Hse : str_end w s <= w + L + 8 /\ w + L < str_end w s) by (unfold str_end; fold L; lia).
destruct (ro_read_ok_glob SEGS B disco_globs ly S W mem md w (L + 1) w (L + 1) GM Hg HV HAR ltac:(lia) ltac:(lia) ltac:(lia) Hlo ltac:(lia)) as [Hra Hhull].
assert (Hbytes : forall i, 0 <= i <= L -> aview SEGS (w_H W) mem (w + i) = Some (nth (Z.to_nat i) (s ++ [0]) 0)).
{ intros i Hi. rewrite (ro_bytes SEGS pa_relro_lo pa_relro_hi B _ w (L + 1) (w + i) HROD (Hrr (w + i) ltac:(lia))
(disco_ro_unowned_at B _ _ DRO ltac:(unfold disco_ro_ranges; apply in_or_app; left; exact Hg)) ltac:(lia)).
pose proof (Hb (Z.to_nat i) ltac:(rewrite length_app; cbn [length]; lia)) as Hq. rewrite Z2Nat.id in Hq by lia. exact Hq. }
assert (Hdj : forall q, q <= L + 8 -> Forall (zdisjoint (w, q)) (snp_out SNPRINTF_STK sp d n)).
{ intros q Hq. unfold snp_out. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
split.
- unfold pf_arg_asan. split; [exact Hc|]. split; [lia|]. split; [lia|]. split; [exact Hbytes|]. split.
{ intros x Hx. pose proof (tj_pad kk s Hro x Hx) as Hp. unfold aview, mbyte.
destruct (mrestrict (w_H W) mem (Z_to_bv 64 x)); [discriminate|].
destruct (seg_rom SEGS (Z_to_bv 64 x)); [discriminate | contradiction]. }
split; [apply Hdj; lia|]. split; [unfold amem_range; left; lia|]. split; assumption.
- unfold fmt_at. split; [lia|]. split; [exact Hbytes|]. split; [apply Hdj; lia|].
split; [unfold amem_range; left; lia|]. split; assumption.
Qed.
Theorem pb_tj_seg_role_sh : tj_seg_role B STK EV EVB IMG.
Proof.
unfold tj_seg_role. intros i FX FR.
unfold tj_fromM, tj_from0.
intros cx E k ly3 S3 W3 ms3 md3 HBASE HEX HJ HFR HINV HS.
pose proof (tjr_keep cx _ _ _ _ _ _ HBASE HJ) as HKEEP0.
destruct cx as [fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0].
pose proof HBASE as HB0. pose proof HEX as HX0. unfold tj_baseX in HB0. unfold tj_EX, tj_F, tj_FL in HX0.
cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0 tj_F tj_FL]
in HB0, HX0, HINV, HJ, HFR, HS, HKEEP0.
pose proof HB0 as (HPRE & Hfrm0 & Hroom & HROD & HIM & H10 & H11 & H12 & H13 & Hnow & Hcap & Hobj & Harr & HlenT & Hok
& Hbuf & Hev & Hsp1b & HE0 & HE032 & HE02).
pose proof HX0 as (AG & E60 & E516 & E528 & E529 & HEI).
unfold INV_tjM, tj_lbody, tj_split, tj_wrote, tj_keep, tj_after1, tj_after2, tj_after4, tj_e, tj_age in HINV.
cbn [c_cap c_T c_now c_buf c_ly c_S c_t] in HINV.
destruct HINV as (Hk0 & (Hperm & HKEEP & Hcap3 & Hi & E721 & E722 & E723 & E734 & E740 & E741) & acc & (o1 & o2 & E733 & E764 & Ho1 & Ho2 & Ho12) & Hacc & Htxt & Hgarr).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity. assert (HSNP : SNPRINTF_STK = 11776) by reflexivity.
assert (HSK : 11776 + 640 <= STK) by (unfold TJ_FRAME in HSTK; glia).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBOK. pose proof pa_base_lo as HBLO.
destruct (sp1_facts (spZ regs + -288) ltac:(clear - Hceil Hslo Hstk0 HSK C1; lia)
ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
rewrite <- Hsp1b in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 304 <= sp1 <= spZ regs - 288) by (clear - Hsp1r; lia). clear Hsp1r.
pose (RUN := paj_run (fx := fq) B LAWS). pose (RUNTO := paj_run_to (fx := fq) B LAWS).
pose (BR := paj_branch (fx := fq) (PI := PI)).
pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & Hfrs3 & Hnev3 & Hk3 & _ & _ & _ & _ & _ & Hpres3 & _ & _ & HQT3).
destruct (al_layout _ _ LAWS ly S W mem md ly3 HAR Hly3) as (Eab3 & EFA & Eown3).
assert (EFA0 : forall c p, frame_addr ly3 c p = frame_addr ly c p) by exact EFA.
set (F := frame_addr ly 2 fpos) in *. set (FLg := flag_addr ly 2 fpos) in *.
assert (Hfin : In (2, fpos) (frames S3)) by (rewrite HFR; left; reflexivity).
assert (E1 : ew E 1 = getr regs 1) by (rewrite (AG 1%nat ltac:(glia)); exact (HE0 1%nat 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite (AG 2%nat ltac:(glia)); exact (HE0 2%nat 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite (AG 3%nat ltac:(glia)); exact (HE0 3%nat 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite (AG 4%nat ltac:(glia)); exact (HE0 4%nat 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 t) by (rewrite (AG 10%nat ltac:(glia)); rewrite (HE0 10%nat 10%bv eq_refl); exact H10).
assert (E12 : ew E 12 = Z_to_bv 64 buf) by (rewrite (AG 12%nat ltac:(glia)); rewrite (HE0 12%nat 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 cap) by (rewrite (AG 13%nat ltac:(glia)); rewrite (HE0 13%nat 13%bv eq_refl); exact H13).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat ltac:(glia)); exact HE032).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat ltac:(glia)); exact HE02).
img_factsF E.
pose proof (pa_obj_img 1 ltac:(unfold disco_nobj; glia)) as Hob242. pose proof (pa_obj_img 0 ltac:(unfold disco_nobj; glia)) as Hob241.
pose proof (pa_obj_img 66 ltac:(unfold disco_nobj; glia)) as Hob307. pose proof (pa_obj_img 67 ltac:(unfold disco_nobj; glia)) as Hob308.
cbv [A_OBJ Nat.add] in Hob241, Hob242, Hob307, Hob308.
pose proof (palf_uar_img B TL) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
unfold IMG_LO, IMG_TOP in Hob241, Hob242, Hob307, Hob308, Huar.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR3 Hfin) as (HFal & [HFhi _] & HFpres & HFSpres).
rewrite EFA in HFal, HFhi, HFpres, HFSpres. fold F in HFal, HFhi, HFpres, HFSpres.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 2 fpos HAR3 Hfin) as (HF4096 & HFceil & HFhigh).
rewrite EFA in HF4096, HFceil, HFhigh. fold F in HF4096, HFceil, HFhigh.
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR3 Hfin) as HFhigh_img. rewrite EFA in HFhigh_img. fold F in HFhigh_img.
change (fs_frame_bytes 2) with 256 in *.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(glia)); glia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by glia; rewrite Z.div_mul by glia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; glia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; glia).
assert (HF8hi2 : F / 8 <= 17592184995808) by (clear - HFq HF8 HFceil C1; lia).
pose (RUNP := SRr_run_pi_AJ (fx := fq) B LAWS). pose (RUNTOP := SRr_run_to_pi_AJ (fx := fq) B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fq) B LAWS).
pose proof HKEEP as (HRODk & Harrk & ((cidT & posT & HinT & HcidT & HTal & HTlo & HThi) & Ht8 & HraT)).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cidT posT HAR HinT) as (HT4096 & HTceil & HTapp).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR HinT) as HTimg.
destruct (in_split _ _ HinT) as (l2 & l3 & Hspl).
pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (2, fpos) (cidT, posT) [] l2 l3 HAR3 ltac:(rewrite HFR, Hspl; reflexivity)) as HdFT.
unfold zdisjoint, frame_rng in HdFT. cbn [fst snd] in HdFT. rewrite !EFA0 in HdFT. fold F in HdFT. change (fs_frame_bytes 2) with 256 in HdFT.
set (TF := frame_addr ly cidT posT) in *. set (TN := fs_frame_bytes cidT) in *.
unfold in_app, kLowShadowBeg, kHighMemBeg in HTapp. unfold off_img, IMG_LO, IMG_TOP in HTimg.
pose proof Hok as (HT1 & HT2 & HT3 & HT4). unfold disco_table_c.tbl_T1 in HT1.
unfold w64 in E740.
assert (Hinb0 : In (buf, Nb) (ablocks B ly S)) by exact (proj1 (Hbuf Hcap3)).
assert (Hcapb : cap <= req_size Nb) by exact (proj2 (Hbuf Hcap3)).
assert (Hinb : In (buf, Nb) (ablocks B ly3 S3))
by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hinb0]).
pose proof tj_snp_gcgv as (Hgc1 & Hgc2 & Hgv1 & Hgv2); unfold IMG_LO, IMG_TOP in Hgc1, Hgc2, Hgv1, Hgv2.
destruct (al_blocks _ _ LAWS _ _ _ _ _ buf Nb HAR3 Hinb) as (Hb16 & Hb4096 & Hbceil & Hbapp & _ & _ & HNb).
pose proof (blk_off_imgP _ _ _ _ _ _ buf Nb HAR3 Hinb) as Hbimg.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ buf Nb 2 fpos HAR3 Hinb Hfin) as Hbsep.
rewrite EFA0 in Hbsep; fold F in Hbsep; change (fs_frame_bytes 2) with 256 in Hbsep;
unfold zdisjoint in Hbsep; cbn [fst snd] in Hbsep.
unfold in_app, kLowShadowBeg, kHighMemBeg in Hbapp; unfold off_img, IMG_LO, IMG_TOP in Hbimg.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ buf Nb cidT posT HAR3 Hinb ltac:(rewrite HFR; right; rewrite Hspl; apply in_or_app; right; left; reflexivity)) as HbT.
rewrite EFA0 in HbT; unfold zdisjoint in HbT; cbn [fst snd] in HbT; fold TF TN in HbT.
unfold w64 in E733, E764.
assert (HGEO : boxed (
4096 <= buf /\ buf + cap <= alloc_ceiling /\
(buf + cap <= 2147450880 \/ 17594333495296 <= buf) /\
(buf + cap <= 65536 \/ 6283264 <= buf) /\
(buf + cap <= TF \/ TF + TN <= buf) /\
TF <= t /\ t + 400 <= TF + TN /\ 4096 <= TF /\ TF + TN <= alloc_ceiling /\
(buf + cap <= F \/ F + 256 <= buf) /\ 4096 <= F /\ F + 256 <= alloc_ceiling /\
512 <= F / 8 /\ F / 8 <= 17592184995808 /\
cap < 2 ^ 31 /\ 0 <= i /\ i <= 7 /\ 0 <= o1 /\ 0 <= o2 /\ o1 + o2 < cap /\ 3 <= cap /\
alloc_ceiling + 12416 <= spZ regs /\ spZ regs - 304 <= sp1 /\ sp1 <= spZ regs - 288 /\
spZ regs < 2 ^ 63 /\ 140735332483072 <= alloc_ceiling /\ alloc_ceiling <= 140737479966720 /\
65536 <= VAL 241 /\ VAL 241 + 8 <= 6283264 /\
65536 <= VAL 242 /\ VAL 242 + 8 <= 6283264 /\
65536 <= VAL 307 /\ VAL 307 + 8 <= 6283264 /\
65536 <= VAL 308 /\ VAL 308 + 8 <= 6283264 /\
SNPRINTF_STK = 11776 /\ ESTACK = 4096 /\ 11776 + 640 <= STK /\
65536 <= GC /\ GC + 8 <= 6283264 /\ 65536 <= GV /\ GV + 8 <= 6283264 /\ cap <= req_size Nb))
by (unbox; repeat split; clear - Hb4096 Hbceil Hcapb Hbapp Hbimg HbT HTlo HThi HT4096 HTceil Hbsep HF4096 HFceil HF8lo HF8hi2
Hi HT1 Hceil Hsp1 HSK Hstk0 Hshi Hslo H47 Hbot Htop Htop2 Hacc Ho1 Ho2 Ho12 Hcap3 Hcap C1 C2 C3 C4 C5
Hob241 Hob242 Hob307 Hob308 HSNP Hes Hgc1 Hgc2 Hgv1 Hgv2; lia).
clear HbT Hbsep Hbapp Hbimg Hb16.
assert (HV4 : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms3)) (t + 48 * i + 8) 4 (disco_table_c.role_of_e T i)).
{ replace (t + 48 * i + 8) with (t + (48 * i + 8)) by glia. unfold disco_table_c.role_of_e. apply tjr_vm4; [exact Harrk | glia | rewrite HlenT; glia]. }
fs_roF HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_fact Ev ssx msx 740 (HPTR 3) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E740, unsigned_lit_small by glia; change (2 ^ 3) with 8;
split; [glia|]; split; [|glia]; replace (t + 48 * i) with (t + (6 * i) * 8) by ring; rewrite Z_mod_plus_full; exact Ht8)) as HS1;
clear HS; rename HS1 into HS end.
norm_ss HS.
destruct (HT2 i Hi) as [Hr | [Hr | Hr]].
all: lazymatch goal with Hrr : disco_table_c.role_of_e _ _ = ?r |- _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_region Ev ssx msx (YP09.mkRegion (Some 740%nat) 8 12 0 0 [YP09.mkChunk 8 (CVal 4 (SLit r))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E740, unsigned_lit_small by glia; split; [glia|]; split; [glia|]; split; [intros o Ho; glia|];
apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS Ev _ (t + 48 * i) 8 4 (SLit r) r); [reflexivity | cbn; glia | cbn; glia | rewrite <- Hrr; exact HV4])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 HSK C1 C2 C3 C5 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi HF8hi2 Hob241 Hob242 Hob307 Hob308 Huar
HT4096 HTceil HTapp HTimg HdFT HTlo HThi HT1 Hi; unfold SB in *; repeat split; lia)) as HS1;
clear HS; rename HS1 into HS end end.
all: norm_ss HS.
all: shok_auto SHOK (SOff 32 0) E (mrestrict (w_H W3) (ms_mem ms3)).
all: hei_havoc HS; paj_run_tok RUN HS HJ SHOK Bspan.
all: try (lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 740 ?cc)) ?len =>
rewrite (U_atom_off Ex 740 (t + 48 * i) cc E740) by glia;
eapply (obl_of_range SEGS _ _ Ex (SOff 32 0) _ len t 400 HraT); [rewrite (U_atom Ex 32 SB E32); [reflexivity | unfold SB; glia] | glia | glia] end).
all: try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => awrFL_with ltac:(idtac; tjr_hd AG HSK) AG fpos F EFA0 end).
all: pose proof (proj1 HJ) as HARc.
all: pose proof (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROD) as HRODc.
all: destruct (tj_snp_canary _ _ _ _ _ HARc) as (cval & HG1 & HG2).
all: lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (HK1 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a);
[intros a Ha; eapply aview_kept_out; [exact HFr | clear - Ha HGEO; unbox; lia | notwG AG Ha HGEO] | ] end.
all: clear HF HFr HG.
all: rebaseE HS AG HEv; clear HEv.
all: lazymatch type of HS with st_ok _ ?Ec _ _ =>
assert (G12 : ew Ec 12 = Z_to_bv 64 buf) by (rewrite (AG 12%nat) by glia; rewrite (HE0 12%nat 12%bv eq_refl); exact H12);
assert (G13 : ew Ec 13 = Z_to_bv 64 cap) by (rewrite (AG 13%nat) by glia; rewrite (HE0 13%nat 13%bv eq_refl); exact H13);
assert (G3 : ew Ec 3 = getr regs 3) by (rewrite (AG 3%nat) by glia; exact (HE0 3%nat 3%bv eq_refl));
assert (G4 : ew Ec 4 = getr regs 4) by (rewrite (AG 4%nat) by glia; exact (HE0 4%nat 4%bv eq_refl));
assert (G32 : ew Ec 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat) by glia; exact HE032);
let HEIc := rnHEI Ec in
pose proof (img_env_atomP Ec 287 HEIc ltac:(unfold A_TEXT, A_LIM; glia)) as E287;
pose proof (img_env_atomP Ec 284 HEIc ltac:(unfold A_TEXT, A_LIM; glia)) as E284;
pose proof (img_env_atomP Ec 285 HEIc ltac:(unfold A_TEXT, A_LIM; glia)) as E285;
pose proof (img_env_atomP Ec 286 HEIc ltac:(unfold A_TEXT, A_LIM; glia)) as E286 end.
all: pose proof (pa_val_range 287) as Hv287; pose proof (pa_val_range 284) as Hv284;
pose proof (pa_val_range 285) as Hv285; pose proof (pa_val_range 286) as Hv286.
all: rregU HS (10%bv : bv 5) (buf + (o1 + o2))
ltac:(rewrite !U_SAlu; cbn [zalu_raw];
lazymatch goal with |- zcanon (zcanon (U ?Ec (SOff 12 0) + _) + _) = _ =>
rewrite (U_atom Ec 12 buf G12), (U_atom Ec 733 o1 E733), (U_atom Ec 764 o2 E764) by glia end;
rewrite (zcanon_id (buf + o1)) by (unfold M64; glia);
replace (buf + o1 + o2) with (buf + (o1 + o2)) by ring; apply zcanon_id; unfold M64; glia) Ra0.
all: rregU HS (11%bv : bv 5) (cap - (o1 + o2))
ltac:(rewrite !U_SAlu; cbn [zalu_raw]; rewrite !U_SMd; cbn [zmd_raw];
lazymatch goal with |- zcanon (zcanon (U ?Ec (SOff 13 0) + _) + _) = _ =>
rewrite (U_atom Ec 13 cap G13), (U_atom Ec 733 o1 E733), (U_atom Ec 764 o2 E764), !U_SLit by glia end;
lazymatch goal with |- zcanon (zcanon (?c + zcanon (?l1 * zcanon ?z1)) + zcanon (?l2 * zcanon ?z2)) = _ =>
rewrite (tjr_sub c l1 z1 ltac:(vm_compute; reflexivity) ltac:(glia) ltac:(glia)),
(tjr_sub (c - l1) l2 z2 ltac:(vm_compute; reflexivity) ltac:(glia) ltac:(glia)) end; glia) Ra1.
all: prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
prreg HS (1%bv : bv 5) Qra; prreg HS (12%bv : bv 5) Qa2; prreg HS (13%bv : bv 5) Qa3.
all: pose proof TJS as (_ & _ & _ & Hro46 & _ & _ & _ & _ & _ & _ & _ & _ & Hro45 & Hro44 & Hro43 & _).
all: destruct (tjr_str 46 tj_f_role _ _ _ _ _ sp1 (buf + (o1 + o2)) (cap - (o1 + o2)) HARc HRODc Hro46
ltac:(unfold IMG_TOP; glia) ltac:(unfold IMG_LO, IMG_TOP; clear - HGEO; unbox; lia)) as [_ Hfmt].
all: set (ei := reac_disco_table_json_c.tj_entry T i) in *.
all: pmkst HS; rewrite HSNPC.
1: {
destruct (tjr_str 43 s_unknown _ _ _ _ _ sp1 (buf + (o1 + o2)) (cap - (o1 + o2)) HARc HRODc Hro43
ltac:(unfold IMG_TOP; glia) ltac:(unfold IMG_LO, IMG_TOP; clear - HGEO; unbox; lia)) as [Hptr _].
assert (HP2 : P2 ei = [44; 34; 114; 111; 108; 101; 34; 58; 34] ++ s_unknown ++ [34])
by (unfold ei, P2, key, qstr, k_role, rolename, reac_disco_table_json_c.tj_entry; cbn [e_role]; rewrite Hr; reflexivity).
assert (HL2 : Z.of_nat (length (P2 ei)) = 17) by (rewrite HP2; reflexivity).
eapply (aj_sh_snprintf_at B LAWS pa_segs_low STK fq GC GV IMGLO IMGHI CR SNPC (ASNP fq) W3 (ms_regs ms) (ms_mem ms) (spZ regs)
(tj_fp buf cap) ly S W mem md [(2, fpos)] ly3 S3 _ k (buf + (o1 + o2)) (cap - (o1 + o2)) (VAL 287)
tj_f_role [PLit 44; PLit 34; PLit 114; PLit 111; PLit 108; PLit 101; PLit 34; PLit 58; PLit 34; Ps; PLit 34]
[] (map (argZ (ms_regs ms)) [3; 4; 5; 6; 7] ++ []) [APtr s_unknown] (P2 ei) cval (sp1 - spZ regs)
(Z_to_bv 64 (BASE + 24144)) _ HJ HRODc).
{ unfold spZ at 1. rewrite Qsp, E60, unsigned_lit_small by glia. glia. }
{ rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity. }
{ glia. }
{ glia. }
{ rewrite Qgp, G3. exact Hgp. }
{ rewrite Qtp, G4. exact Htp. }
{ exact Qra. }
{ apply ret_ok_codeptr_v; [glia | reflexivity]. }
{ exact Ra0. }
{ exact Ra1. }
{ rewrite Qa2, E287. reflexivity. }
{ exact (tj_snp_consts _ _ HRODc). }
{ eapply Forall_impl; [|exact tj_snp_cr]. intros r0 Hr0. cbv beta in *. unfold IMG_LO, IMG_TOP in Hr0. clear - Hr0; lia. }
{ eapply Forall_impl; [|exact tj_snp_cr]. intros r0 Hr0. cbv beta in *. unfold IMG_LO, IMG_TOP in Hr0.
unfold snp_out. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; clear - Hr0 HGEO; unbox; lia). }
{ exact HG1. }
{ exact HG2. }
{ glia. }
{ glia. }
{ glia. }
{ glia. }
{ unfold snp_out. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; glia). }
{ unfold snp_out. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; glia). }
{ replace (spZ regs + (sp1 - spZ regs)) with sp1 by glia. exact Hfmt. }
{ exact (tj_ro_fmt_rng 46 tj_f_role Hro46 ltac:(cbv; glia)). }
{ unfold tj_f_role; discriminate. }
{ reflexivity. }
{ repeat (apply Forall_cons; [exact I|]). apply Forall_nil. }
{ split; [reflexivity | intros q Hq; cbn in Hq; clear - Hq; lia]. }
{ cbn [length Z.of_nat]. glia. }
{ unfold snp_out. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; glia). }
{ cbn [map app pf_args_asan]. split; [|exact I].
replace (spZ regs + (sp1 - spZ regs)) with sp1 by glia.
replace (argZ (ms_regs ms) 3) with (VAL 284); [exact Hptr|].
unfold argZ. lazymatch type of Qa3 with getr _ ?r = _ => replace (Z_to_bv 5 (10 + 3)) with r by (apply bv_eq; vm_compute; reflexivity) end.
rewrite Qa3, E284. rewrite unsigned_lit_small by glia. reflexivity. }
{ cbn [map app SnFF.pf_args_amem]. split; [|exact I].
replace (argZ (ms_regs ms) 3) with (VAL 284); [exact (tj_ro_amem8 43 s_unknown Hro43)|].
unfold argZ. lazymatch type of Qa3 with getr _ ?r = _ => replace (Z_to_bv 5 (10 + 3)) with r by (apply bv_eq; vm_compute; reflexivity) end.
rewrite Qa3, E284. rewrite unsigned_lit_small by glia. reflexivity. }
{ rewrite HP2. vm_compute. reflexivity. }
{ glia. }
{ rewrite HL2. glia. }
{ glia. }
{ glia. }
{ unfold snp_out. cbn [pairwise]. split;
[apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; glia | apply Forall_nil] | split; [apply Forall_nil | exact I]]. }
{ intros a Ha. split; [|clear - Ha HGEO; unbox; lia]. right. left. split.
+ exists (buf, buf + cap). split; [unfold tj_fp; rewrite (proj2 (Z.ltb_ge cap 3) Hcap3); left; reflexivity | cbn [fst snd]; clear - Ha HGEO; unbox; lia].
+ exists buf, Nb. split; [exact Hinb | clear - Ha HGEO; unbox; lia]. }
{ apply (amem_range_of_block8 SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); glia. }
{ apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); glia. }
{ apply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); glia. }
{ eapply tj_dest_off_globals; [exact (proj1 tj_snp_img) | exact (proj2 tj_snp_img) | exact HARc | exact Hinb | glia | glia]. }
{ exact Hfrm0. }
intros fx' regs2 mem2 md2 Hf1 Hf2 HJ2 HP2x Ha0' Hwr Hnul Hfr Hpres2 Hsame.
rewrite HL2 in Ha0', Hwr, Hnul.
replace (spZ regs + (sp1 - spZ regs)) with sp1 in Hfr by glia. rewrite HSNP in Hfr.
assert (HOUT : forall a, 0 <= a < 2 ^ 64 -> ~ (buf <= a < buf + cap) -> ~ (sp1 - 11776 <= a < sp1) ->
aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms) a).
{ intros a Ha H1 H2. apply Hfr; [exact Ha | | exact H2].
intros Hd. apply H1.
pose proof (Z.le_min_r (Z.of_nat (length (P2 ei))) (cap - (o1 + o2) - 1)) as Hm.
clear - Hd Hm Ho1 Ho2; lia. }
reseat HS HJ2 HP2x [0; 1; 2; 3; 4; 5; 6; 7; 8]%nat AG
ltac:(idtac; eapply region_kept_aview;
[evalE AG | intros a Ha; apply HOUT; clear - Ha HGEO; unbox; lia | exact Hpres2]).
apply (st_ok_pi_restrict_fx fq fx') in HS.
clear RUNP RUNTOP RUNC BR.
pose (BR := paj_branch (fx := fx') (PI := PI)).
pose (RUNP := SRr_run_pi_AJ (fx := fx') B LAWS). pose (RUNTOP := SRr_run_to_pi_AJ (fx := fx') B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fx') B LAWS).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (F13 : ew Ev 13 = Z_to_bv 64 cap) by (rewrite (AG 13%nat) by glia; rewrite (HE0 13%nat 13%bv eq_refl); exact H13) end.
prreg HS (10%bv : bv 5) Qr0. cbn [ms_regs] in Qr0. rewrite Ha0' in Qr0. symmetry in Qr0. unfold w64 in Qr0.
lazymatch type of Qr0 with ew ?Ev ?nn = _ => assert (U0 : U Ev (SOff nn 0) = 17) by (apply U_atom; [exact Qr0 | glia]) end.
psrr_branch_pi RUNP BR HS.
{ exfalso. lazymatch type of Hc with branch_taken _ (sv_denot ?Ev ?a) (sv_denot _ ?b) = _ =>
rewrite (denot_lit_U Ev a), (denot_lit_U Ev b), U0, U_SLit in Hc end.
vm_compute in Hc. discriminate Hc. }
clear Hc.
paj_run_shc RUNP RUNC HS HJ2. { awrFL_with ltac:(idtac; tjr_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (HK2 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a)
by (intros a Ha; eapply aview_kept_out; [exact HFr | clear - Ha HGEO; unbox; lia | notwG AG Ha HGEO]) end.
clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (U4 : U Ev (SAlu ALU_ADD (SAlu ALU_ADD (SOff 13 0) (SMd M_MUL (SOff 733 0) (SLit (-1)))) (SMd M_MUL (SOff 764 0) (SLit (-1)))) = cap - (o1 + o2))
by (rewrite !U_SAlu; cbn [zalu_raw]; rewrite !U_SMd; cbn [zmd_raw];
rewrite (U_atom Ev 13 cap F13), (U_atom Ev 733 o1 E733), (U_atom Ev 764 o2 E764), !U_SLit by (clear - HGEO; unbox; lia);
rewrite (tjr_sub cap o1 (-1) ltac:(vm_compute; reflexivity) ltac:(clear - HGEO; unbox; lia) ltac:(clear - HGEO; unbox; lia)),
(tjr_sub (cap - o1) o2 (-1) ltac:(vm_compute; reflexivity) ltac:(clear - HGEO; unbox; lia) ltac:(clear - HGEO; unbox; lia)); lia) end.
psrr_branch_pi RUNP BR HS.
- rewrite branch_geu_U, U0, U4 in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
paj_run_to_shc RUNTOP HS HJ2 0x621c. { awrFL_with ltac:(idtac; tjr_hd AG HSK) AG fpos F EFA0. }
clear HF HFr HG.
pose proof (proj1 HJ2) as HARy.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HARy Hfin) as (_ & _ & _ & HFSy).
rewrite EFA0 in HFSy. fold F in HFSy. change (fs_frame_bytes 2 / 8) with 32 in HFSy.
fs_rwF HS E529 HFSy.
prreg HS (21%bv : bv 5) R21.
ra_join HS ss_tjX 640%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 20; 21; 23; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join_val HS 640%nat 13%nat R21 E653.
hei_havoc HS. rebaseE HS AG HEv. clear HEv.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (tj_from0_at_fx B STK EV IMG _ _ FX (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx' Ev k ly3 S3 Wg msF mdF Hf1 Hf2) end end.
+ exact HBASE.
+ unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
split; [exact AG|]. split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529 | assumption].
+ cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos c_buf c_cap]. exact HJ2.
+ cbn [c_S c_fpos]. exact HFR.
+ unfold INV_tjX. cbn [c_cap c_T c_now c_buf c_ly c_S].
assert (Htl : o1 + o2 + 17 <= tj_len T now)
by (unfold tj_len; rewrite Htxt, !length_app, !Nat2Z.inj_add, HL2; clear - Ho12; lia).
split; [clear - Hk0 Hi HT1 HEV HEVB; nia|]. split; [exact Hperm|]. exists (-1). split.
{ rewrite E653. apply bv_eq. unfold w64. rewrite !Z_to_bv_unsigned. vm_compute. reflexivity. }
split; [intros _; reflexivity|].
split; [intros _ Hlt; exfalso; clear - Htl Hlt Hc; lia | intros _ _; reflexivity].
+ exact HS.
- rewrite branch_geu_U, U0, U4 in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
paj_run_to_shc RUNTOP HS HJ2 0x5e58. { awrFL_with ltac:(idtac; tjr_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (HK3 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a)
by (intros a Ha; eapply aview_kept_out; [exact HFr | clear - Ha HGEO; unbox; lia | notwG AG Ha HGEO]) end.
clear HF HFr HG.
pose proof (proj1 HJ2) as HARz.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HARz Hfin) as (_ & _ & _ & HFSz).
rewrite EFA0 in HFSz. fold F in HFSz. change (fs_frame_bytes 2 / 8) with 32 in HFSz.
fs_rwF HS E529 HFSz.
rregU HS (26%bv : bv 5) (o1 + o2)
ltac:(rewrite U_SAlu; cbn [zalu_raw];
lazymatch goal with |- zcanon (U ?Ev _ + _) = _ => rewrite (U_atom Ev 733 o1 E733), (U_atom Ev 764 o2 E764) by (clear - HGEO; unbox; lia) end;
apply zcanon_id; unfold M64; clear - HGEO; unbox; lia) R26.
rregU HS (10%bv : bv 5) 17 ltac:(exact U0) R10.
ra_join HS ss_tjR 1000%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
hei_havoc HS.
ra_join HS ss_tjR 780%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join_val HS 780%nat 4%nat R10 E784.
ra_join_val HS 780%nat 13%nat R26 E793.
hei_havoc HS. rebaseE HS AG HEv. clear HEv.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (tj_from0_at_fx B STK EV IMG _ _ FR (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx' Ev k ly3 S3 Wg msF mdF Hf1 Hf2) end end.
+ exact HBASE.
+ unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
split; [exact AG|]. split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529 | assumption].
+ cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos c_buf c_cap]. exact HJ2.
+ cbn [c_S c_fpos]. exact HFR.
+ unfold INV_tjR, tj_lbody, tj_split, tj_wrote, tj_after2, tj_after4, tj_e, tj_age.
cbn [c_cap c_T c_now c_buf c_ly c_S c_t]. fold ei.
split; [clear - Hk0 Hi HT1 HEV HEVB; nia|].
split.
{ split; [exact Hperm|]. split; [pose proof (tjr_keep _ _ _ _ _ _ _ HBASE HJ2) as HKq; unfold tj_keep in HKq |- *; cbn [c_t c_T c_ly c_S] in HKq |- *; exact HKq|].
split; [clear - HGEO; unbox; lia|]. split; [clear - Hi; lia|].
split; [exact E721|]. split; [exact E722|]. split; [exact E723|]. split; [exact E734|].
split; [exact E740 | exact E741]. }
exists (acc ++ P2 ei). split.
{ exists (o1 + o2), 17. split; [exact E793|]. split; [exact E784|].
split; [clear - HGEO; unbox; lia|]. split; [clear; lia|].
rewrite length_app, Nat2Z.inj_add, HL2. clear - Ho12; lia. }
split; [rewrite length_app, Nat2Z.inj_add, HL2; clear - Ho12 Hc; lia|].
split; [rewrite Htxt, <- app_assoc; reflexivity|].
rewrite <- app_assoc.
apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) mem2 _ buf).
{ intros a Ha. rewrite !length_app, !Nat2Z.inj_add, HL2 in Ha. cbn [length Z.of_nat] in Ha.
rewrite HK3 by (clear - Ha Ho12 Hc HGEO; unbox; lia). apply HK2. clear - Ha Ho12 Hc HGEO; unbox; lia. }
apply (proj2 (garr8_app SEGS _ _ _ _)). split.
{ apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) (ms_mem ms3) mem2 buf acc).
- intros a Ha. rewrite Hfr by (clear - Ha Ho12 Hc HGEO; unbox; lia). apply HK1. clear - Ha Ho12 Hc HGEO; unbox; lia.
- exact (proj1 (proj1 (garr8_app SEGS _ _ _ _) Hgarr)). }
rewrite Z.min_l in Hwr, Hnul by (clear - Hc; lia).
replace (buf + Z.of_nat (length acc)) with (buf + (o1 + o2)) by (clear - Ho12; lia).
apply (tjr_garr mem2 (w_H W3) (buf + (o1 + o2)) (P2 ei)).
{ intros q Hq. rewrite HL2 in Hq. exact (Hwr q Hq). }
{ rewrite HL2. exact Hnul. }
+ exact HS.
}
1: {
destruct (tjr_str 45 s_box _ _ _ _ _ sp1 (buf + (o1 + o2)) (cap - (o1 + o2)) HARc HRODc Hro45
ltac:(unfold IMG_TOP; glia) ltac:(unfold IMG_LO, IMG_TOP; clear - HGEO; unbox; lia)) as [Hptr _].
assert (HP2 : P2 ei = [44; 34; 114; 111; 108; 101; 34; 58; 34] ++ s_box ++ [34])
by (unfold ei, P2, key, qstr, k_role, rolename, reac_disco_table_json_c.tj_entry; cbn [e_role]; rewrite Hr; reflexivity).
assert (HL2 : Z.of_nat (length (P2 ei)) = 13) by (rewrite HP2; reflexivity).
eapply (aj_sh_snprintf_at B LAWS pa_segs_low STK fq GC GV IMGLO IMGHI CR SNPC (ASNP fq) W3 (ms_regs ms) (ms_mem ms) (spZ regs)
(tj_fp buf cap) ly S W mem md [(2, fpos)] ly3 S3 _ k (buf + (o1 + o2)) (cap - (o1 + o2)) (VAL 287)
tj_f_role [PLit 44; PLit 34; PLit 114; PLit 111; PLit 108; PLit 101; PLit 34; PLit 58; PLit 34; Ps; PLit 34]
[] (map (argZ (ms_regs ms)) [3; 4; 5; 6; 7] ++ []) [APtr s_box] (P2 ei) cval (sp1 - spZ regs)
(Z_to_bv 64 (BASE + 24144)) _ HJ HRODc).
{ unfold spZ at 1. rewrite Qsp, E60, unsigned_lit_small by glia. glia. }
{ rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity. }
{ glia. }
{ glia. }
{ rewrite Qgp, G3. exact Hgp. }
{ rewrite Qtp, G4. exact Htp. }
{ exact Qra. }
{ apply ret_ok_codeptr_v; [glia | reflexivity]. }
{ exact Ra0. }
{ exact Ra1. }
{ rewrite Qa2, E287. reflexivity. }
{ exact (tj_snp_consts _ _ HRODc). }
{ eapply Forall_impl; [|exact tj_snp_cr]. intros r0 Hr0. cbv beta in *. unfold IMG_LO, IMG_TOP in Hr0. clear - Hr0; lia. }
{ eapply Forall_impl; [|exact tj_snp_cr]. intros r0 Hr0. cbv beta in *. unfold IMG_LO, IMG_TOP in Hr0.
unfold snp_out. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; clear - Hr0 HGEO; unbox; lia). }
{ exact HG1. }
{ exact HG2. }
{ glia. }
{ glia. }
{ glia. }
{ glia. }
{ unfold snp_out. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; glia). }
{ unfold snp_out. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; glia). }
{ replace (spZ regs + (sp1 - spZ regs)) with sp1 by glia. exact Hfmt. }
{ exact (tj_ro_fmt_rng 46 tj_f_role Hro46 ltac:(cbv; glia)). }
{ unfold tj_f_role; discriminate. }
{ reflexivity. }
{ repeat (apply Forall_cons; [exact I|]). apply Forall_nil. }
{ split; [reflexivity | intros q Hq; cbn in Hq; clear - Hq; lia]. }
{ cbn [length Z.of_nat]. glia. }
{ unfold snp_out. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; glia). }
{ cbn [map app pf_args_asan]. split; [|exact I].
replace (spZ regs + (sp1 - spZ regs)) with sp1 by glia.
replace (argZ (ms_regs ms) 3) with (VAL 286); [exact Hptr|].
unfold argZ. lazymatch type of Qa3 with getr _ ?r = _ => replace (Z_to_bv 5 (10 + 3)) with r by (apply bv_eq; vm_compute; reflexivity) end.
rewrite Qa3, E286. rewrite unsigned_lit_small by glia. reflexivity. }
{ cbn [map app SnFF.pf_args_amem]. split; [|exact I].
replace (argZ (ms_regs ms) 3) with (VAL 286); [exact (tj_ro_amem8 45 s_box Hro45)|].
unfold argZ. lazymatch type of Qa3 with getr _ ?r = _ => replace (Z_to_bv 5 (10 + 3)) with r by (apply bv_eq; vm_compute; reflexivity) end.
rewrite Qa3, E286. rewrite unsigned_lit_small by glia. reflexivity. }
{ rewrite HP2. vm_compute. reflexivity. }
{ glia. }
{ rewrite HL2. glia. }
{ glia. }
{ glia. }
{ unfold snp_out. cbn [pairwise]. split;
[apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; glia | apply Forall_nil] | split; [apply Forall_nil | exact I]]. }
{ intros a Ha. split; [|clear - Ha HGEO; unbox; lia]. right. left. split.
+ exists (buf, buf + cap). split; [unfold tj_fp; rewrite (proj2 (Z.ltb_ge cap 3) Hcap3); left; reflexivity | cbn [fst snd]; clear - Ha HGEO; unbox; lia].
+ exists buf, Nb. split; [exact Hinb | clear - Ha HGEO; unbox; lia]. }
{ apply (amem_range_of_block8 SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); glia. }
{ apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); glia. }
{ apply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); glia. }
{ eapply tj_dest_off_globals; [exact (proj1 tj_snp_img) | exact (proj2 tj_snp_img) | exact HARc | exact Hinb | glia | glia]. }
{ exact Hfrm0. }
intros fx' regs2 mem2 md2 Hf1 Hf2 HJ2 HP2x Ha0' Hwr Hnul Hfr Hpres2 Hsame.
rewrite HL2 in Ha0', Hwr, Hnul.
replace (spZ regs + (sp1 - spZ regs)) with sp1 in Hfr by glia. rewrite HSNP in Hfr.
assert (HOUT : forall a, 0 <= a < 2 ^ 64 -> ~ (buf <= a < buf + cap) -> ~ (sp1 - 11776 <= a < sp1) ->
aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms) a).
{ intros a Ha H1 H2. apply Hfr; [exact Ha | | exact H2].
intros Hd. apply H1.
pose proof (Z.le_min_r (Z.of_nat (length (P2 ei))) (cap - (o1 + o2) - 1)) as Hm.
clear - Hd Hm Ho1 Ho2; lia. }
reseat HS HJ2 HP2x [0; 1; 2; 3; 4; 5; 6; 7; 8]%nat AG
ltac:(idtac; eapply region_kept_aview;
[evalE AG | intros a Ha; apply HOUT; clear - Ha HGEO; unbox; lia | exact Hpres2]).
apply (st_ok_pi_restrict_fx fq fx') in HS.
clear RUNP RUNTOP RUNC BR.
pose (BR := paj_branch (fx := fx') (PI := PI)).
pose (RUNP := SRr_run_pi_AJ (fx := fx') B LAWS). pose (RUNTOP := SRr_run_to_pi_AJ (fx := fx') B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fx') B LAWS).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (F13 : ew Ev 13 = Z_to_bv 64 cap) by (rewrite (AG 13%nat) by glia; rewrite (HE0 13%nat 13%bv eq_refl); exact H13) end.
prreg HS (10%bv : bv 5) Qr0. cbn [ms_regs] in Qr0. rewrite Ha0' in Qr0. symmetry in Qr0. unfold w64 in Qr0.
lazymatch type of Qr0 with ew ?Ev ?nn = _ => assert (U0 : U Ev (SOff nn 0) = 13) by (apply U_atom; [exact Qr0 | glia]) end.
psrr_branch_pi RUNP BR HS.
{ exfalso. lazymatch type of Hc with branch_taken _ (sv_denot ?Ev ?a) (sv_denot _ ?b) = _ =>
rewrite (denot_lit_U Ev a), (denot_lit_U Ev b), U0, U_SLit in Hc end.
vm_compute in Hc. discriminate Hc. }
clear Hc.
paj_run_shc RUNP RUNC HS HJ2. { awrFL_with ltac:(idtac; tjr_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (HK2 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a)
by (intros a Ha; eapply aview_kept_out; [exact HFr | clear - Ha HGEO; unbox; lia | notwG AG Ha HGEO]) end.
clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (U4 : U Ev (SAlu ALU_ADD (SAlu ALU_ADD (SOff 13 0) (SMd M_MUL (SOff 733 0) (SLit (-1)))) (SMd M_MUL (SOff 764 0) (SLit (-1)))) = cap - (o1 + o2))
by (rewrite !U_SAlu; cbn [zalu_raw]; rewrite !U_SMd; cbn [zmd_raw];
rewrite (U_atom Ev 13 cap F13), (U_atom Ev 733 o1 E733), (U_atom Ev 764 o2 E764), !U_SLit by (clear - HGEO; unbox; lia);
rewrite (tjr_sub cap o1 (-1) ltac:(vm_compute; reflexivity) ltac:(clear - HGEO; unbox; lia) ltac:(clear - HGEO; unbox; lia)),
(tjr_sub (cap - o1) o2 (-1) ltac:(vm_compute; reflexivity) ltac:(clear - HGEO; unbox; lia) ltac:(clear - HGEO; unbox; lia)); lia) end.
psrr_branch_pi RUNP BR HS.
- rewrite branch_geu_U, U0, U4 in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
paj_run_to_shc RUNTOP HS HJ2 0x621c. { awrFL_with ltac:(idtac; tjr_hd AG HSK) AG fpos F EFA0. }
clear HF HFr HG.
pose proof (proj1 HJ2) as HARy.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HARy Hfin) as (_ & _ & _ & HFSy).
rewrite EFA0 in HFSy. fold F in HFSy. change (fs_frame_bytes 2 / 8) with 32 in HFSy.
fs_rwF HS E529 HFSy.
prreg HS (21%bv : bv 5) R21.
ra_join HS ss_tjX 640%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 20; 21; 23; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join_val HS 640%nat 13%nat R21 E653.
hei_havoc HS. rebaseE HS AG HEv. clear HEv.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (tj_from0_at_fx B STK EV IMG _ _ FX (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx' Ev k ly3 S3 Wg msF mdF Hf1 Hf2) end end.
+ exact HBASE.
+ unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
split; [exact AG|]. split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529 | assumption].
+ cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos c_buf c_cap]. exact HJ2.
+ cbn [c_S c_fpos]. exact HFR.
+ unfold INV_tjX. cbn [c_cap c_T c_now c_buf c_ly c_S].
assert (Htl : o1 + o2 + 13 <= tj_len T now)
by (unfold tj_len; rewrite Htxt, !length_app, !Nat2Z.inj_add, HL2; clear - Ho12; lia).
split; [clear - Hk0 Hi HT1 HEV HEVB; nia|]. split; [exact Hperm|]. exists (-1). split.
{ rewrite E653. apply bv_eq. unfold w64. rewrite !Z_to_bv_unsigned. vm_compute. reflexivity. }
split; [intros _; reflexivity|].
split; [intros _ Hlt; exfalso; clear - Htl Hlt Hc; lia | intros _ _; reflexivity].
+ exact HS.
- rewrite branch_geu_U, U0, U4 in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
paj_run_to_shc RUNTOP HS HJ2 0x5e58. { awrFL_with ltac:(idtac; tjr_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (HK3 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a)
by (intros a Ha; eapply aview_kept_out; [exact HFr | clear - Ha HGEO; unbox; lia | notwG AG Ha HGEO]) end.
clear HF HFr HG.
pose proof (proj1 HJ2) as HARz.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HARz Hfin) as (_ & _ & _ & HFSz).
rewrite EFA0 in HFSz. fold F in HFSz. change (fs_frame_bytes 2 / 8) with 32 in HFSz.
fs_rwF HS E529 HFSz.
rregU HS (26%bv : bv 5) (o1 + o2)
ltac:(rewrite U_SAlu; cbn [zalu_raw];
lazymatch goal with |- zcanon (U ?Ev _ + _) = _ => rewrite (U_atom Ev 733 o1 E733), (U_atom Ev 764 o2 E764) by (clear - HGEO; unbox; lia) end;
apply zcanon_id; unfold M64; clear - HGEO; unbox; lia) R26.
rregU HS (10%bv : bv 5) 13 ltac:(exact U0) R10.
ra_join HS ss_tjR 1000%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
hei_havoc HS.
ra_join HS ss_tjR 780%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join_val HS 780%nat 4%nat R10 E784.
ra_join_val HS 780%nat 13%nat R26 E793.
hei_havoc HS. rebaseE HS AG HEv. clear HEv.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (tj_from0_at_fx B STK EV IMG _ _ FR (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx' Ev k ly3 S3 Wg msF mdF Hf1 Hf2) end end.
+ exact HBASE.
+ unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
split; [exact AG|]. split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529 | assumption].
+ cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos c_buf c_cap]. exact HJ2.
+ cbn [c_S c_fpos]. exact HFR.
+ unfold INV_tjR, tj_lbody, tj_split, tj_wrote, tj_after2, tj_after4, tj_e, tj_age.
cbn [c_cap c_T c_now c_buf c_ly c_S c_t]. fold ei.
split; [clear - Hk0 Hi HT1 HEV HEVB; nia|].
split.
{ split; [exact Hperm|]. split; [pose proof (tjr_keep _ _ _ _ _ _ _ HBASE HJ2) as HKq; unfold tj_keep in HKq |- *; cbn [c_t c_T c_ly c_S] in HKq |- *; exact HKq|].
split; [clear - HGEO; unbox; lia|]. split; [clear - Hi; lia|].
split; [exact E721|]. split; [exact E722|]. split; [exact E723|]. split; [exact E734|].
split; [exact E740 | exact E741]. }
exists (acc ++ P2 ei). split.
{ exists (o1 + o2), 13. split; [exact E793|]. split; [exact E784|].
split; [clear - HGEO; unbox; lia|]. split; [clear; lia|].
rewrite length_app, Nat2Z.inj_add, HL2. clear - Ho12; lia. }
split; [rewrite length_app, Nat2Z.inj_add, HL2; clear - Ho12 Hc; lia|].
split; [rewrite Htxt, <- app_assoc; reflexivity|].
rewrite <- app_assoc.
apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) mem2 _ buf).
{ intros a Ha. rewrite !length_app, !Nat2Z.inj_add, HL2 in Ha. cbn [length Z.of_nat] in Ha.
rewrite HK3 by (clear - Ha Ho12 Hc HGEO; unbox; lia). apply HK2. clear - Ha Ho12 Hc HGEO; unbox; lia. }
apply (proj2 (garr8_app SEGS _ _ _ _)). split.
{ apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) (ms_mem ms3) mem2 buf acc).
- intros a Ha. rewrite Hfr by (clear - Ha Ho12 Hc HGEO; unbox; lia). apply HK1. clear - Ha Ho12 Hc HGEO; unbox; lia.
- exact (proj1 (proj1 (garr8_app SEGS _ _ _ _) Hgarr)). }
rewrite Z.min_l in Hwr, Hnul by (clear - Hc; lia).
replace (buf + Z.of_nat (length acc)) with (buf + (o1 + o2)) by (clear - Ho12; lia).
apply (tjr_garr mem2 (w_H W3) (buf + (o1 + o2)) (P2 ei)).
{ intros q Hq. rewrite HL2 in Hq. exact (Hwr q Hq). }
{ rewrite HL2. exact Hnul. }
+ exact HS.
}
1: {
destruct (tjr_str 44 s_master _ _ _ _ _ sp1 (buf + (o1 + o2)) (cap - (o1 + o2)) HARc HRODc Hro44
ltac:(unfold IMG_TOP; glia) ltac:(unfold IMG_LO, IMG_TOP; clear - HGEO; unbox; lia)) as [Hptr _].
assert (HP2 : P2 ei = [44; 34; 114; 111; 108; 101; 34; 58; 34] ++ s_master ++ [34])
by (unfold ei, P2, key, qstr, k_role, rolename, reac_disco_table_json_c.tj_entry; cbn [e_role]; rewrite Hr; reflexivity).
assert (HL2 : Z.of_nat (length (P2 ei)) = 16) by (rewrite HP2; reflexivity).
eapply (aj_sh_snprintf_at B LAWS pa_segs_low STK fq GC GV IMGLO IMGHI CR SNPC (ASNP fq) W3 (ms_regs ms) (ms_mem ms) (spZ regs)
(tj_fp buf cap) ly S W mem md [(2, fpos)] ly3 S3 _ k (buf + (o1 + o2)) (cap - (o1 + o2)) (VAL 287)
tj_f_role [PLit 44; PLit 34; PLit 114; PLit 111; PLit 108; PLit 101; PLit 34; PLit 58; PLit 34; Ps; PLit 34]
[] (map (argZ (ms_regs ms)) [3; 4; 5; 6; 7] ++ []) [APtr s_master] (P2 ei) cval (sp1 - spZ regs)
(Z_to_bv 64 (BASE + 24144)) _ HJ HRODc).
{ unfold spZ at 1. rewrite Qsp, E60, unsigned_lit_small by glia. glia. }
{ rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity. }
{ glia. }
{ glia. }
{ rewrite Qgp, G3. exact Hgp. }
{ rewrite Qtp, G4. exact Htp. }
{ exact Qra. }
{ apply ret_ok_codeptr_v; [glia | reflexivity]. }
{ exact Ra0. }
{ exact Ra1. }
{ rewrite Qa2, E287. reflexivity. }
{ exact (tj_snp_consts _ _ HRODc). }
{ eapply Forall_impl; [|exact tj_snp_cr]. intros r0 Hr0. cbv beta in *. unfold IMG_LO, IMG_TOP in Hr0. clear - Hr0; lia. }
{ eapply Forall_impl; [|exact tj_snp_cr]. intros r0 Hr0. cbv beta in *. unfold IMG_LO, IMG_TOP in Hr0.
unfold snp_out. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; clear - Hr0 HGEO; unbox; lia). }
{ exact HG1. }
{ exact HG2. }
{ glia. }
{ glia. }
{ glia. }
{ glia. }
{ unfold snp_out. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; glia). }
{ unfold snp_out. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; glia). }
{ replace (spZ regs + (sp1 - spZ regs)) with sp1 by glia. exact Hfmt. }
{ exact (tj_ro_fmt_rng 46 tj_f_role Hro46 ltac:(cbv; glia)). }
{ unfold tj_f_role; discriminate. }
{ reflexivity. }
{ repeat (apply Forall_cons; [exact I|]). apply Forall_nil. }
{ split; [reflexivity | intros q Hq; cbn in Hq; clear - Hq; lia]. }
{ cbn [length Z.of_nat]. glia. }
{ unfold snp_out. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; glia). }
{ cbn [map app pf_args_asan]. split; [|exact I].
replace (spZ regs + (sp1 - spZ regs)) with sp1 by glia.
replace (argZ (ms_regs ms) 3) with (VAL 285); [exact Hptr|].
unfold argZ. lazymatch type of Qa3 with getr _ ?r = _ => replace (Z_to_bv 5 (10 + 3)) with r by (apply bv_eq; vm_compute; reflexivity) end.
rewrite Qa3, E285. rewrite unsigned_lit_small by glia. reflexivity. }
{ cbn [map app SnFF.pf_args_amem]. split; [|exact I].
replace (argZ (ms_regs ms) 3) with (VAL 285); [exact (tj_ro_amem8 44 s_master Hro44)|].
unfold argZ. lazymatch type of Qa3 with getr _ ?r = _ => replace (Z_to_bv 5 (10 + 3)) with r by (apply bv_eq; vm_compute; reflexivity) end.
rewrite Qa3, E285. rewrite unsigned_lit_small by glia. reflexivity. }
{ rewrite HP2. vm_compute. reflexivity. }
{ glia. }
{ rewrite HL2. glia. }
{ glia. }
{ glia. }
{ unfold snp_out. cbn [pairwise]. split;
[apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; glia | apply Forall_nil] | split; [apply Forall_nil | exact I]]. }
{ intros a Ha. split; [|clear - Ha HGEO; unbox; lia]. right. left. split.
+ exists (buf, buf + cap). split; [unfold tj_fp; rewrite (proj2 (Z.ltb_ge cap 3) Hcap3); left; reflexivity | cbn [fst snd]; clear - Ha HGEO; unbox; lia].
+ exists buf, Nb. split; [exact Hinb | clear - Ha HGEO; unbox; lia]. }
{ apply (amem_range_of_block8 SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); glia. }
{ apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); glia. }
{ apply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); glia. }
{ eapply tj_dest_off_globals; [exact (proj1 tj_snp_img) | exact (proj2 tj_snp_img) | exact HARc | exact Hinb | glia | glia]. }
{ exact Hfrm0. }
intros fx' regs2 mem2 md2 Hf1 Hf2 HJ2 HP2x Ha0' Hwr Hnul Hfr Hpres2 Hsame.
rewrite HL2 in Ha0', Hwr, Hnul.
replace (spZ regs + (sp1 - spZ regs)) with sp1 in Hfr by glia. rewrite HSNP in Hfr.
assert (HOUT : forall a, 0 <= a < 2 ^ 64 -> ~ (buf <= a < buf + cap) -> ~ (sp1 - 11776 <= a < sp1) ->
aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms) a).
{ intros a Ha H1 H2. apply Hfr; [exact Ha | | exact H2].
intros Hd. apply H1.
pose proof (Z.le_min_r (Z.of_nat (length (P2 ei))) (cap - (o1 + o2) - 1)) as Hm.
clear - Hd Hm Ho1 Ho2; lia. }
reseat HS HJ2 HP2x [0; 1; 2; 3; 4; 5; 6; 7; 8]%nat AG
ltac:(idtac; eapply region_kept_aview;
[evalE AG | intros a Ha; apply HOUT; clear - Ha HGEO; unbox; lia | exact Hpres2]).
apply (st_ok_pi_restrict_fx fq fx') in HS.
clear RUNP RUNTOP RUNC BR.
pose (BR := paj_branch (fx := fx') (PI := PI)).
pose (RUNP := SRr_run_pi_AJ (fx := fx') B LAWS). pose (RUNTOP := SRr_run_to_pi_AJ (fx := fx') B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fx') B LAWS).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (F13 : ew Ev 13 = Z_to_bv 64 cap) by (rewrite (AG 13%nat) by glia; rewrite (HE0 13%nat 13%bv eq_refl); exact H13) end.
prreg HS (10%bv : bv 5) Qr0. cbn [ms_regs] in Qr0. rewrite Ha0' in Qr0. symmetry in Qr0. unfold w64 in Qr0.
lazymatch type of Qr0 with ew ?Ev ?nn = _ => assert (U0 : U Ev (SOff nn 0) = 16) by (apply U_atom; [exact Qr0 | glia]) end.
psrr_branch_pi RUNP BR HS.
{ exfalso. lazymatch type of Hc with branch_taken _ (sv_denot ?Ev ?a) (sv_denot _ ?b) = _ =>
rewrite (denot_lit_U Ev a), (denot_lit_U Ev b), U0, U_SLit in Hc end.
vm_compute in Hc. discriminate Hc. }
clear Hc.
paj_run_shc RUNP RUNC HS HJ2. { awrFL_with ltac:(idtac; tjr_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (HK2 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a)
by (intros a Ha; eapply aview_kept_out; [exact HFr | clear - Ha HGEO; unbox; lia | notwG AG Ha HGEO]) end.
clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (U4 : U Ev (SAlu ALU_ADD (SAlu ALU_ADD (SOff 13 0) (SMd M_MUL (SOff 733 0) (SLit (-1)))) (SMd M_MUL (SOff 764 0) (SLit (-1)))) = cap - (o1 + o2))
by (rewrite !U_SAlu; cbn [zalu_raw]; rewrite !U_SMd; cbn [zmd_raw];
rewrite (U_atom Ev 13 cap F13), (U_atom Ev 733 o1 E733), (U_atom Ev 764 o2 E764), !U_SLit by (clear - HGEO; unbox; lia);
rewrite (tjr_sub cap o1 (-1) ltac:(vm_compute; reflexivity) ltac:(clear - HGEO; unbox; lia) ltac:(clear - HGEO; unbox; lia)),
(tjr_sub (cap - o1) o2 (-1) ltac:(vm_compute; reflexivity) ltac:(clear - HGEO; unbox; lia) ltac:(clear - HGEO; unbox; lia)); lia) end.
psrr_branch_pi RUNP BR HS.
- rewrite branch_geu_U, U0, U4 in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
paj_run_to_shc RUNTOP HS HJ2 0x621c. { awrFL_with ltac:(idtac; tjr_hd AG HSK) AG fpos F EFA0. }
clear HF HFr HG.
pose proof (proj1 HJ2) as HARy.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HARy Hfin) as (_ & _ & _ & HFSy).
rewrite EFA0 in HFSy. fold F in HFSy. change (fs_frame_bytes 2 / 8) with 32 in HFSy.
fs_rwF HS E529 HFSy.
prreg HS (21%bv : bv 5) R21.
ra_join HS ss_tjX 640%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 20; 21; 23; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join_val HS 640%nat 13%nat R21 E653.
hei_havoc HS. rebaseE HS AG HEv. clear HEv.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (tj_from0_at_fx B STK EV IMG _ _ FX (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx' Ev k ly3 S3 Wg msF mdF Hf1 Hf2) end end.
+ exact HBASE.
+ unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
split; [exact AG|]. split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529 | assumption].
+ cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos c_buf c_cap]. exact HJ2.
+ cbn [c_S c_fpos]. exact HFR.
+ unfold INV_tjX. cbn [c_cap c_T c_now c_buf c_ly c_S].
assert (Htl : o1 + o2 + 16 <= tj_len T now)
by (unfold tj_len; rewrite Htxt, !length_app, !Nat2Z.inj_add, HL2; clear - Ho12; lia).
split; [clear - Hk0 Hi HT1 HEV HEVB; nia|]. split; [exact Hperm|]. exists (-1). split.
{ rewrite E653. apply bv_eq. unfold w64. rewrite !Z_to_bv_unsigned. vm_compute. reflexivity. }
split; [intros _; reflexivity|].
split; [intros _ Hlt; exfalso; clear - Htl Hlt Hc; lia | intros _ _; reflexivity].
+ exact HS.
- rewrite branch_geu_U, U0, U4 in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
paj_run_to_shc RUNTOP HS HJ2 0x5e58. { awrFL_with ltac:(idtac; tjr_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (HK3 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a)
by (intros a Ha; eapply aview_kept_out; [exact HFr | clear - Ha HGEO; unbox; lia | notwG AG Ha HGEO]) end.
clear HF HFr HG.
pose proof (proj1 HJ2) as HARz.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HARz Hfin) as (_ & _ & _ & HFSz).
rewrite EFA0 in HFSz. fold F in HFSz. change (fs_frame_bytes 2 / 8) with 32 in HFSz.
fs_rwF HS E529 HFSz.
rregU HS (26%bv : bv 5) (o1 + o2)
ltac:(rewrite U_SAlu; cbn [zalu_raw];
lazymatch goal with |- zcanon (U ?Ev _ + _) = _ => rewrite (U_atom Ev 733 o1 E733), (U_atom Ev 764 o2 E764) by (clear - HGEO; unbox; lia) end;
apply zcanon_id; unfold M64; clear - HGEO; unbox; lia) R26.
rregU HS (10%bv : bv 5) 16 ltac:(exact U0) R10.
ra_join HS ss_tjR 1000%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
hei_havoc HS.
ra_join HS ss_tjR 780%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join_val HS 780%nat 4%nat R10 E784.
ra_join_val HS 780%nat 13%nat R26 E793.
hei_havoc HS. rebaseE HS AG HEv. clear HEv.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (tj_from0_at_fx B STK EV IMG _ _ FR (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx' Ev k ly3 S3 Wg msF mdF Hf1 Hf2) end end.
+ exact HBASE.
+ unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
split; [exact AG|]. split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529 | assumption].
+ cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos c_buf c_cap]. exact HJ2.
+ cbn [c_S c_fpos]. exact HFR.
+ unfold INV_tjR, tj_lbody, tj_split, tj_wrote, tj_after2, tj_after4, tj_e, tj_age.
cbn [c_cap c_T c_now c_buf c_ly c_S c_t]. fold ei.
split; [clear - Hk0 Hi HT1 HEV HEVB; nia|].
split.
{ split; [exact Hperm|]. split; [pose proof (tjr_keep _ _ _ _ _ _ _ HBASE HJ2) as HKq; unfold tj_keep in HKq |- *; cbn [c_t c_T c_ly c_S] in HKq |- *; exact HKq|].
split; [clear - HGEO; unbox; lia|]. split; [clear - Hi; lia|].
split; [exact E721|]. split; [exact E722|]. split; [exact E723|]. split; [exact E734|].
split; [exact E740 | exact E741]. }
exists (acc ++ P2 ei). split.
{ exists (o1 + o2), 16. split; [exact E793|]. split; [exact E784|].
split; [clear - HGEO; unbox; lia|]. split; [clear; lia|].
rewrite length_app, Nat2Z.inj_add, HL2. clear - Ho12; lia. }
split; [rewrite length_app, Nat2Z.inj_add, HL2; clear - Ho12 Hc; lia|].
split; [rewrite Htxt, <- app_assoc; reflexivity|].
rewrite <- app_assoc.
apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) mem2 _ buf).
{ intros a Ha. rewrite !length_app, !Nat2Z.inj_add, HL2 in Ha. cbn [length Z.of_nat] in Ha.
rewrite HK3 by (clear - Ha Ho12 Hc HGEO; unbox; lia). apply HK2. clear - Ha Ho12 Hc HGEO; unbox; lia. }
apply (proj2 (garr8_app SEGS _ _ _ _)). split.
{ apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) (ms_mem ms3) mem2 buf acc).
- intros a Ha. rewrite Hfr by (clear - Ha Ho12 Hc HGEO; unbox; lia). apply HK1. clear - Ha Ho12 Hc HGEO; unbox; lia.
- exact (proj1 (proj1 (garr8_app SEGS _ _ _ _) Hgarr)). }
rewrite Z.min_l in Hwr, Hnul by (clear - Hc; lia).
replace (buf + Z.of_nat (length acc)) with (buf + (o1 + o2)) by (clear - Ho12; lia).
apply (tjr_garr mem2 (w_H W3) (buf + (o1 + o2)) (P2 ei)).
{ intros q Hq. rewrite HL2 in Hq. exact (Hwr q Hq). }
{ rewrite HL2. exact Hnul. }
+ exact HS.
}
Qed.
End h.
End f.
End d.
