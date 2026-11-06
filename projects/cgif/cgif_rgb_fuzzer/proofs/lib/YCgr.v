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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI03 YI04 YI1i YI20.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCfr YCfu YCe9 YCgu YCgv.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma val_mem_zero4 : forall H (m : word -> option byte) a,
(forall i, 0 <= i < 4 -> aview trbsegs H m (a + i) = Some 0) -> val_mem trbsegs (mrestrict H m) a 4 0.
Proof.
intros H m a Hz j Hj. destruct (aview_byte trbsegs H m (a + Z.of_nat j) 0 (Hz (Z.of_nat j) ltac:(lia))) as (b & Hb & Hv & _).
rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold YP0g.le_byte, bv_wrap.
repeat (rewrite Z.shiftr_0_l || rewrite Z.mod_0_l by (vm_compute; discriminate)). lia.
Qed.
Section d.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes trbsegs B.
Hypothesis AFREE : afree_realizes trbsegs B.
Hypothesis AMEMSET : aintrin_realizes trbsegs B OSet A_asan_memset.
Hypothesis AMEMCPY : aintrin_realizes trbsegs B OCpy A_asan_memcpy.
Hypothesis ASF : astack_free_law trbsegs B.
Hypothesis FFL : frame_flag_lawP trbsegs B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.
Local Notation code := (as_code B).
Lemma ng_M : NG_K_stmt B -> NG_M_stmt B.
Proof.
intros NGK ly S W regs mem md ch cfgp pal0 pala attr gen Wd Hd ngp loops rest cid pos E0 E W3 ly3 S3 ms3 md3 k fpos g HCTX HCFG HE0 HE Rg HNOW HW0 HH0 HS.
ng_facts HCTX HCFG HE0 HE.
destruct HNOW as (HJ3 & Hk3 & Hfrs3 & Eab3 & Hg4096 & Tg & Ag).
ng_frame HJ3 Hfrs3.
assert (Hg_in : In (g, 96) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_app_iff; right; left; reflexivity).
assert (Hing : forall x, In x (ablocks B ly S) -> In x (ablocks B ly3 S3)) by (intros x Hx; rewrite Eab3; apply in_app_iff; left; exact Hx).
destruct (al_blocks _ _ LAWS _ _ _ _ _ g 96 HAR3 Hg_in) as (Hg16 & _ & Hgceil & Hgh_ia & Hgpres3 & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_img _ _ _ _ _ _ g 96 HAR3 Hg_in) as Hgh_img.
change (req_size 96) with 96 in Hgceil, Hgpres3, Hgh_img.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ g 96 1 fpos HAR3 Hg_in Hfin3) as HdGF.
unfold zdisjoint in HdGF. cbn [fst snd] in HdGF. change (req_size 96) with 96 in HdGF. change (fs_frame_bytes 1) with 128 in HdGF. rewrite EFA3 in HdGF. fold F in HdGF.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ g 96 cid pos HAR3 Hg_in HfinS3) as HdGC.
unfold zdisjoint in HdGC. cbn [fst snd] in HdGC. change (req_size 96) with 96 in HdGC. rewrite EFA3 in HdGC.
nbox HdFC.
aconsts HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
assert (E10' : ew E 10 = Z_to_bv 64 cfgp) by (rewrite (AG 10%nat) by lia; exact E10).
reshok_bx HS 35%nat.
aj_run_tok trbtbl_lib_ok HS HJ3 SHOK NBspan.
{ awrR AG fpos F EFA3. }
clear_frames.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 337168) with (Z_to_bv 64 A_asan_memset).
clear Kgot3 Kcell3 Kguar3 Kuar3 Vgr3. aconsts HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_at trbsegs B LAWS Hsegs OSet A_asan_memset AMEMSET _ (ms_regs msX) (ms_mem msX) TNEWGIF_STK (spZ regs) [] ly S W mem md [(1, fpos)]
ly3 S3 _ _ g 0 96 (-192) (Z_to_bv 64 0x85e78) HJ3) end.
- rewrite Ra0. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite Rg. reflexivity.
- exact Ra1.
- exact Ra2.
- lia. - lia. - lia.
- unfold spZ at 1. rewrite Rsp. evalE AG.
- reflexivity. - lia. - rewrite FFS. unfold ESTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- intros a Ha. split; [replace a with (g + (a - g)) by lia; apply Ag; [exact Hg_in | lia] | unfold ESTACK; lia].
- apply (amem_range_of_block trbsegs B LAWS ly3 S3 _ _ _ g 96 _ _ (proj1 HJ3) Hg_in); change (req_size 96) with 96; lia.
- apply (range_addressable_of_block trbsegs B LAWS ly3 S3 _ _ _ g 96 _ _ (proj1 HJ3) Hg_in); change (req_size 96) with 96; lia.
- intros _. apply (shadow_hull_vis_of_block trbsegs B LAWS ly3 S3 _ _ _ g 96 _ _ (proj1 HJ3) Hg_in); change (req_size 96) with 96; lia.
- exact I. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Heff & Hfr4 & Hpres4).
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp.
aconsts HROD HJ4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos (proj1 HJ4) Hfin3) as (_ & _ & HFpres4 & HFSpres4). change (fs_frame_bytes 1) with 128 in HFpres4, HFSpres4.
change (128 / 8) with 16 in HFSpres4. rewrite !EFA3 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
destruct (al_blocks _ _ LAWS _ _ _ _ _ g 96 (proj1 HJ4) Hg_in) as (_ & _ & _ & _ & Hgpres4 & _). change (req_size 96) with 96 in Hgpres4.
reseat HS HJ4 HP4 [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11]%nat AG
ltac:(idtac; first [ keptI Hfr4 Hpres4 AG Kgot3 Kgot4 Kcell3 Kcell4 Kguar3 Kguar4 Kuar3 Kuar4 Vgr3 Vgr4
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
assert (Z8 : forall off, 0 <= off -> off + 8 <= 96 -> val_mem trbsegs (mrestrict (w_H W3) mem4) (g + off) 8 0).
{ intros off Ho1 Ho2. apply val_mem_zero8. intros i Hi. replace (g + off + i) with (g + (off + i)) by lia. rewrite (Heff (off + i)) by lia. reflexivity. }
assert (Z4 : forall off, 0 <= off -> off + 4 <= 96 -> val_mem trbsegs (mrestrict (w_H W3) mem4) (g + off) 4 0).
{ intros off Ho1 Ho2. apply val_mem_zero4. intros i Hi. replace (g + off + i) with (g + (off + i)) by lia. rewrite (Heff (off + i)) by lia. reflexivity. }
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region trbsegs Ev _ _
(YQ0b.mkRegion (Some 79%nat) 0 96 0 96
[YQ0b.mkChunk 0 (CVal 8 (SLit 0)); YQ0b.mkChunk 8 (CVal 8 (SLit 0)); YQ0b.mkChunk 16 (CVal 8 (SLit 0));
YQ0b.mkChunk 72 (CVal 8 (SLit 0)); YQ0b.mkChunk 80 (CVal 8 (SLit 0)); YQ0b.mkChunk 88 (CVal 4 (SLit 0)); YQ0b.mkChunk 92 (CVal 4 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Rg, unsigned_lit_small by lia;
split; [lia|]; split; [lia|]; split; [intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (Hgpres4 (g + o) ltac:(lia)))|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ g 0 8 _ 0); [reflexivity | zside | zside | apply Z8; lia]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ g 8 8 _ 0); [reflexivity | zside | zside | apply Z8; lia]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ g 16 8 _ 0); [reflexivity | zside | zside | apply Z8; lia]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ g 72 8 _ 0); [reflexivity | zside | zside | apply Z8; lia]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ g 80 8 _ 0); [reflexivity | zside | zside | apply Z8; lia]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ g 88 4 _ 0); [reflexivity | zside | zside | apply Z4; lia]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ g 92 4 _ 0); [reflexivity | zside | zside | apply Z4; lia]|];
apply Forall_nil)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite Rg; change (fs_frame_bytes 1) with 128; change (fs_frame_bytes 1 / 8) with 16; evalE AG;
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_newgif; nunbox HdGF; nunbox HdGC; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. reshok_bx HS 35%nat. clear_frames.
nbox HdGF. nbox HdGC.
aj_run_tok trbtbl_lib_ok HS HJ4 SHOK NBspan.
all: try (slim; obl_blk HJ4 Rg E35 Hg_in).
all: try (slim; awrR AG fpos F EFA3).
clear_frames.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) 0 _ HS eq_refl) as HRg; cbn [ms_mem restrict] in HRg;
lazymatch type of HRg with region_ok _ _ _ (YQ0b.mkRegion (Some 79%nat) ?lo ?hi ?wlo ?whi ?cs) =>
let gf off w v V := pose proof (field_of_region Ex _ 79 g cs lo hi wlo whi off w (SLit v) v HRg
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Rg; apply unsigned_lit_small; lia)
ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V in
gf 0 8%N 0 U0; gf 8 8%N 0 U8; gf 16 8%N 0 U16; gf 72 8%N 0 U72; gf 80 8%N 0 U80; gf 88 4%N 0 U88; gf 92 4%N 1 U92 end;
clear HRg end.
cbn [N.to_nat] in U0, U8, U16, U72, U80, U88, U92.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 335988) with (Z_to_bv 64 A_asan_memcpy).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos (proj1 HJ4) HfinS3) as (_ & _ & HCpres4 & _). rewrite EFA3 in HCpres4.
assert (Qcs : cfgp + 48 <= spZ regs - 192 - ESTACK) by (unfold ESTACK; lia).
clear Kgot3 Kcell3 Kguar3 Kuar3 Vgr3 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4. aconsts HROD HJ4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_at trbsegs B LAWS Hsegs OCpy A_asan_memcpy AMEMCPY _ (ms_regs msX) (ms_mem msX) TNEWGIF_STK (spZ regs) [] ly S W mem md [(1, fpos)]
ly3 S3 _ _ (g + 24) cfgp 48 (-192) (Z_to_bv 64 0x85ed0) HJ4) end.
- rewrite Ra0. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite Rg. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
- rewrite Ra1. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 10%nat) by lia. rewrite E10. reflexivity.
- exact Ra2.
- lia. - lia. - lia.
- unfold spZ at 1. rewrite Rsp. evalE AG.
- reflexivity. - lia. - rewrite FFS. unfold ESTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- intros a Ha. split; [replace a with (g + (a - g)) by lia; apply Ag; [exact Hg_in | lia] | unfold ESTACK; lia].
- apply (amem_range_of_block trbsegs B LAWS ly3 S3 _ _ _ g 96 _ _ (proj1 HJ4) Hg_in); change (req_size 96) with 96; lia.
- apply (range_addressable_of_block trbsegs B LAWS ly3 S3 _ _ _ g 96 _ _ (proj1 HJ4) Hg_in); change (req_size 96) with 96; lia.
- intros _. apply (shadow_hull_vis_of_block trbsegs B LAWS ly3 S3 _ _ _ g 96 _ _ (proj1 HJ4) Hg_in); change (req_size 96) with 96; lia.
- split; [lia|]. split; [lia|]. split.
{ intros a Ha. split; [| unfold spZ; rewrite Rsp; evalE AG].
apply (aview_some_of_apresent trbsegs). apply (proj1 (HCpres4 a ltac:(lia))). }
split; [nunbox HdGC; clear - HdGC Hflo Hfhi; lia|]. split; [apply amem_range_high; zone_lia|]. split.
+ eapply (range_addressable_entry_frame trbsegs B LAWS); [exact HJ4 | exact Hfin | exact Hcid0 | exact Hflo | exact Hfhi | exact Hfal
| intros x Hx; exfalso; exact (inFP_nil x Hx) | exact HAR | exact HRA].
+ intros _. eapply (shadow_hull_vis_of_frame trbsegs B LAWS ly3 S3 _ _ _ cid pos cfgp 48 (proj1 HJ4) HfinS3); [rewrite EFA3; exact Hflo | rewrite EFA3; exact Hfhi | lia]. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Ha05 & Heff5 & Hfr5 & Hpres5).
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp.
lazymatch type of Heff5 with forall i, _ -> aview _ _ _ _ = aview _ _ ?memT _ =>
let cmove off w v V Vr :=
pose proof (val_mem_moved trbsegs (w_H W3) (w_H W3) memT mem5 (cfgp + off) (g + 24 + off) w v
ltac:(intros kk Hk; replace (g + 24 + off + kk) with (g + 24 + (off + kk)) by lia; replace (cfgp + off + kk) with (cfgp + (off + kk)) by lia;
apply Heff5; cbn [Z.of_nat Pos.to_nat Pos.iter_op Nat.add] in Hk; lia)
(val_mem_entry_frame trbsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cid pos (cfgp + off) w v HJ4 Hfin
ltac:(lia) ltac:(cbn [Z.of_nat Pos.to_nat Pos.iter_op Nat.add]; lia) ltac:(intros x Hx HF; exact (inFP_nil x HF)) V)) as Vr in
cmove 0 8%nat pal0 CV0 W0; cmove 8 8%nat 0 CV8 W8; cmove 16 4%nat attr CV16 W16; cmove 20 4%nat gen CV20 W20;
cmove 24 2%nat Wd CV24 W24; cmove 26 2%nat Hd CV26 W26; cmove 28 2%nat ngp CV28 W28; cmove 30 2%nat loops CV30 W30;
cmove 32 8%nat A_writecb CV32 W32; cmove 40 8%nat 0 CV40 W40 end.
lazymatch type of Heff5 with forall i, _ -> aview _ _ _ _ = aview _ _ ?memT _ =>
let keep off w v U Ur :=
pose proof (val_mem_moved trbsegs (w_H W3) (w_H W3) memT mem5 (g + off) (g + off) w v
ltac:(intros kk Hk; apply Hfr5; [lia | cbn [Z.of_nat Pos.to_nat Pos.iter_op Nat.add] in Hk; lia | unfold ESTACK; lia]) U) as Ur in
keep 0 8%nat 0 U0 X0; keep 8 8%nat 0 U8 X8; keep 16 8%nat 0 U16 X16; keep 72 8%nat 0 U72 X72; keep 80 8%nat 0 U80 X80; keep 88 4%nat 0 U88 X88; keep 92 4%nat 1 U92 X92 end.
clear U0 U8 U16 U72 U80 U88 U92.
nunbox HdGF. nunbox HdGC.
aconsts HROD HJ5 Kgot5 Kcell5 Kguar5 Kuar5 Vgr5.
destruct (al_blocks _ _ LAWS _ _ _ _ _ g 96 (proj1 HJ5) Hg_in) as (_ & _ & _ & _ & Hgpres5 & _). change (req_size 96) with 96 in Hgpres5.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos (proj1 HJ5) Hfin3) as (_ & _ & HFpres5 & HFSpres5). change (fs_frame_bytes 1) with 128 in HFpres5, HFSpres5.
change (128 / 8) with 16 in HFSpres5. rewrite !EFA3 in HFpres5, HFSpres5. fold F in HFpres5, HFSpres5.
reseat HS HJ5 HP5 [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11]%nat AG
ltac:(idtac; first [ keptI Hfr5 Hpres5 AG Kgot4 Kgot5 Kcell4 Kcell5 Kguar4 Kguar5 Kuar4 Kuar5 Vgr4 Vgr5
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
let ckv HE := cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
try rewrite (AG 32%nat) by lia; rewrite HE; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity in
pose proof (ast_ok_add_region trbsegs Ev _ _
(YQ0b.mkRegion (Some 79%nat) 0 96 0 96
[YQ0b.mkChunk 0 (CVal 8 (SLit 0)); YQ0b.mkChunk 8 (CVal 8 (SLit 0)); YQ0b.mkChunk 16 (CVal 8 (SLit 0));
YQ0b.mkChunk 24 (CVal 8 (SOff 32 0)); YQ0b.mkChunk 32 (CVal 8 (SLit 0)); YQ0b.mkChunk 40 (CVal 4 (SOff 33 0)); YQ0b.mkChunk 44 (CVal 4 (SOff 34 0));
YQ0b.mkChunk 48 (CVal 2 (SOff 36 0)); YQ0b.mkChunk 50 (CVal 2 (SOff 37 0)); YQ0b.mkChunk 52 (CVal 2 (SOff 38 0)); YQ0b.mkChunk 54 (CVal 2 (SOff 39 0));
YQ0b.mkChunk 56 (CVal 8 (SLit A_writecb)); YQ0b.mkChunk 64 (CVal 8 (SLit 0)); YQ0b.mkChunk 72 (CVal 8 (SLit 0)); YQ0b.mkChunk 80 (CVal 8 (SLit 0));
YQ0b.mkChunk 88 (CVal 4 (SLit 0)); YQ0b.mkChunk 92 (CVal 4 (SLit 1))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Rg, unsigned_lit_small by lia;
split; [lia|]; split; [lia|]; split; [intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (Hgpres5 (g + o) ltac:(lia)))|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ g 0 8 _ 0); [reflexivity | zside | zside | exact X0]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ g 8 8 _ 0); [reflexivity | zside | zside | exact X8]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ g 16 8 _ 0); [reflexivity | zside | zside | exact X16]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ g 24 8 _ pal0); [ckv E32 | zside | zside | replace (g + 24) with (g + 24 + 0) by lia; exact W0]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ g 32 8 _ 0); [reflexivity | zside | zside | replace (g + 32) with (g + 24 + 8) by lia; exact W8]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ g 40 4 _ attr); [ckv E33 | zside | zside | replace (g + 40) with (g + 24 + 16) by lia; exact W16]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ g 44 4 _ gen); [ckv E34 | zside | zside | replace (g + 44) with (g + 24 + 20) by lia; exact W20]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ g 48 2 _ Wd); [ckv E36 | zside | zside | replace (g + 48) with (g + 24 + 24) by lia; exact W24]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ g 50 2 _ Hd); [ckv E37 | zside | zside | replace (g + 50) with (g + 24 + 26) by lia; exact W26]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ g 52 2 _ ngp); [ckv E38 | zside | zside | replace (g + 52) with (g + 24 + 28) by lia; exact W28]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ g 54 2 _ loops); [ckv E39 | zside | zside | replace (g + 54) with (g + 24 + 30) by lia; exact W30]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ g 56 8 _ A_writecb); [reflexivity | unfold A_writecb; zside | zside | replace (g + 56) with (g + 24 + 32) by lia; exact W32]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ g 64 8 _ 0); [reflexivity | zside | zside | replace (g + 64) with (g + 24 + 40) by lia; exact W40]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ g 72 8 _ 0); [reflexivity | zside | zside | exact X72]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ g 80 8 _ 0); [reflexivity | zside | zside | exact X80]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ g 88 4 _ 0); [reflexivity | zside | zside | exact X88]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ g 92 4 _ 1); [reflexivity | zside | zside | exact X92]|];
apply Forall_nil)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite Rg; change (fs_frame_bytes 1) with 128; change (fs_frame_bytes 1 / 8) with 16; evalE AG;
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_newgif; nunbox HdGF; nunbox HdGC; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. clear W0 W8 W16 W20 W24 W26 W28 W30 W32 W40 X0 X8 X16 X72 X80 X88 X92 Heff5. nbox HdGF. nbox HdGC.
lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msv) =>
change ssx with ss_NK in HS;
eapply (NGK ly S W regs mem md ch cfgp pal0 pala attr gen Wd Hd ngp loops rest cid pos E0 Ev W3 ly3 S3 msv _ k fpos g);
[ split; [exact HPRE | split; [exact Hal32 | split; [| split; [exact Hroom | split; [exact Htop32 | split; [exact HROD | split; [exact Hcfg | split; [exact HWH | split; [exact Hpala | split; [exact HPerm | split; [exact Hev | exact Hlive]]]]]]]]]]]
| split; [exact Hfin | split; [exact Hcid0 | split; [exact Hfal | split; [exact Hflo | split; [exact Hfhi | split; [exact Hcal | exact HRA]]]]]]
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| split; [exact AG | repeat (split; [eassumption|]); eassumption]
| exact Rg
| split; [exact HJ5 | split; [exact Hk3 | split; [exact Hfrs3 | split; [exact Eab3 | split; [exact Hg4096 | split; [exact Tg | exact Ag]]]]]]
| exact HW0 | exact HH0
| exact HS ] end.
rewrite <- Hra88. destruct Hspine as [Hs | Hs]; rewrite Hs; cbn; tauto.
Qed.
End d. End c.
