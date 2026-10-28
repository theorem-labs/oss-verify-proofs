(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI0m YI0n YI5w YI5z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a YC80 YC1f YC1g YC1h YC81 YC4b YC20 YC44 YC45.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8h AC8a ACjr ACk4 ACk5.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YC5d YC7z YC7x YC21 YC85 YC86 YC88.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI17 YE02 YC5n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACk0 ACk2 ACk3.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Context {NP : ng_params}.
#[local] Notation hw := (@ngp_hw NP).
#[local] Notation CTX := (@ngp_ctx NP).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Lemma val_mem_zero4 : forall H (m : word -> option byte) a,
(forall i, 0 <= i < 4 -> aview SEGS H m (a + i) = Some 0) -> val_mem SEGS (mrestrict H m) a 4 0.
Proof.
intros H m a Hz j Hj. destruct (aview_byte SEGS H m (a + Z.of_nat j) 0 (Hz (Z.of_nat j) ltac:(lia))) as (b & Hb & Hv & _).
rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
repeat (rewrite Z.shiftr_0_l || rewrite Z.mod_0_l by ((first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate]))). lia.
Qed.
Section f.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes SEGS B.
Hypothesis AFREE : afree_realizes SEGS B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA AS_asan_memset).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA AS_asan_memcpy).
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_0 PI.
Hypothesis TLF : PALibF B.
Hypothesis Rhw : 0 <= hw < 2 ^ 64.
Hypothesis HGOT3 : forall (H : word -> bool) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
val_mem SEGS (mrestrict H mem) (VAL (A_OBJ 3)) 8 (BASE + 0).
Hypothesis HU : forall c t, In c CTX -> In t (ng_traces B c) -> In t (as_universe B).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Local Notation code := (as_code B).
Variable K : asink_syms.
Hypothesis AIL : asink_img_laws SEGS B K.
Variable MT : ameter_ops.
Hypothesis MLAW : ameter_laws MT.
Hypothesis MLAWF : ameter_fs_laws MT.
Hypothesis AMALLOC4 : amalloc04_rule SEGS B MT.
Variable XN : xnums.
Hypothesis HXN : forall ngp, 0 <= ngp <= 65535 -> ng_msum MT ngp <= xn_newgif XN ngp.
Hypothesis HXM : forall ngp, 0 <= ngp <= 65535 -> ng_msum MT ngp <= xm_newgif XN ngp.
Lemma ng_MX : NG_K_stmtX B K MT XN -> NG_M_stmtX B K MT XN.
Proof.
intros NGK ly S W regs mem md ch cfgp pal0 pala attr gen Wd Hd ngp loops aM rest GPAL cid pos E0 E W3 ly3 S3 ms3 md3 k fpos pf g HCTX HXE HCFG HE0 HEX E52 Rg HNOW HW0 HH0 HS.
destruct HEX as [HE E42].
ng_facts HCTX HCFG HE0 HE.
destruct HNOW as (HJ3 & Hk3 & Hfrs3 & Eab3 & Hg4096 & Hpf4096 & Tg & Ag & Tpf & Apf & HSINK & MLE3).
ng_frame HJ3 Hfrs3.
assert (Rngp : 0 <= ngp <= 65535) by (clear - CR28; lia).
assert (Rpath : 0x10000 <= ak_path K < 0x5fb000).
{ apply (pa_img_range (ak_path K)). apply (proj1 (ail_env _ _ _ AIL (ak_path K) ltac:(unfold aenv_addr; right; right; right; left; lia))). }
assert (Hpf_in : In (pf, FILE_BLOCK) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_app_iff; left; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pf FILE_BLOCK HAR3 Hpf_in) as (Hpf16 & _ & Hpfceil & Hp_ia & _ & _).
pose proof (blk_off_imgP _ _ _ _ _ _ pf FILE_BLOCK HAR3 Hpf_in) as Hph_img. change (req_size FILE_BLOCK) with 1264 in Hpfceil, Hph_img, Hp_ia. unfold off_img in Hph_img.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 _ _ _ pf FILE_BLOCK 1 fpos HAR3 Hpf_in Hfin3) as HdPF.
unfold zdisjoint in HdPF. cbn [fst snd] in HdPF. change (req_size FILE_BLOCK) with 1264 in HdPF. change (fs_frame_bytes 1) with 128 in HdPF. rewrite ?EFA3 in HdPF. fold F in HdPF.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 _ _ _ pf FILE_BLOCK cid pos HAR3 Hpf_in HfinS3) as HdPC.
unfold zdisjoint in HdPC. cbn [fst snd] in HdPC. change (req_size FILE_BLOCK) with 1264 in HdPC. rewrite ?EFA3 in HdPC.
pose proof HFhigh_img as HFoffX. unfold off_img in HFoffX.
assert (XF : xfacts ((alloc_ceiling + TNEWGIFX_STK <= spZ regs /\ TNEWGIFX_STK = 18816 /\ 140735332483072 <= alloc_ceiling <= 140737479966720 /\
(F + 128 <= 65536 \/ 6270976 <= F) /\ 4096 <= F /\ F + 128 <= alloc_ceiling /\ 512 <= F / 8) /\
pf + 1264 <= alloc_ceiling /\ 4096 <= pf /\ (pf + 1264 <= 65536 \/ 6270976 <= pf) /\
(pf + 1264 <= cfgp \/ cfgp + 48 <= pf) /\ 4096 <= cfgp /\ (pf + 1264 <= F \/ F + 128 <= pf)))
by (apply xfacts_i; clear - Hceil Hslo FFS C1 HFoffX HF4096 HFceil HF8lo Hpfceil Hpf4096 Hph_img HdPC HdPF Hflo Hfhi Hf4096; lia).
clear HdPC HdPF Hph_img HFoffX. change (in_app pf 1264) with (xfacts (in_app pf 1264)) in Hp_ia.
assert (Hg_in : In (g, 96) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_app_iff; right; left; reflexivity).
assert (Hing : forall x, In x (ablocks B ly S) -> In x (ablocks B ly3 S3)) by (intros x Hx; rewrite Eab3; apply in_app_iff; left; apply in_app_iff; left; exact Hx).
destruct (al_blocks _ _ LAWS _ _ _ _ _ g 96 HAR3 Hg_in) as (Hg16 & _ & Hgceil & Hgh_ia & Hgpres3 & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g 96 HAR3 Hg_in) as Hgh_img.
change (req_size 96) with 96 in Hgceil, Hgpres3, Hgh_img.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 _ _ _ g 96 1 fpos HAR3 Hg_in Hfin3) as HdGF.
unfold zdisjoint in HdGF. cbn [fst snd] in HdGF. change (req_size 96) with 96 in HdGF. change (fs_frame_bytes 1) with 128 in HdGF. rewrite EFA3 in HdGF. fold F in HdGF.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 _ _ _ g 96 cid pos HAR3 Hg_in HfinS3) as HdGC.
unfold zdisjoint in HdGC. cbn [fst snd] in HdGC. change (req_size 96) with 96 in HdGC. rewrite EFA3 in HdGC.
pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ pf FILE_BLOCK g 96 HAR3 Hpf_in Hg_in ltac:(unfold FILE_BLOCK; intros X; injection X; lia)) as HdXG.
unfold zdisjoint in HdXG. cbn [fst snd] in HdXG. change (req_size FILE_BLOCK) with 1264 in HdXG.
change (req_size 96) with 96 in HdXG. pose proof Hgh_img as HGoffX. unfold off_img in HGoffX.
lazymatch type of XF with xfacts ?P =>
assert (XF2 : xfacts (P /\ (pf + 1264 <= g \/ g + 96 <= pf) /\ 4096 <= g /\ g + 96 <= alloc_ceiling /\ (g + 96 <= 65536 \/ 6270976 <= g)))
by (apply xfacts_i; split; [exact XF | clear - HdXG Hg4096 Hgceil HGoffX; lia]); clear XF HGoffX HdXG; rename XF2 into XF end.
nbox HdFC.
aconsts HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
assert (E10' : ew E 10 = Z_to_bv 64 cfgp) by (rewrite (AG 10%nat) by lia; exact E10).
reshok_bx HS 35%nat.
hei_havoc HS; paj_run_tok RUN HS HJ3 SHOK NBspan.
all: try (awrR AG fpos F EFA3).
xsink_stretch HFr HSINK. clear_frames.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
pmkst HS.
idtac.
clear Kgot3 Kcell3 Kguar3 Kuar3 Vgr3. aconsts HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_atS SEGS B LAWS Hsegs OSet (SIGMA AS_asan_memset) AMEMSET _ (ms_regs msX) (ms_mem msX) TNEWGIFX_STK (spZ regs) [sink_token] ly S W mem md [(1, fpos)]
ly3 S3 _ _ g 0 96 (-192) (Z_to_bv 64 (BASE + 0x1d8)) HJ3) end.
- rewrite Ra0. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite Rg. reflexivity.
- exact Ra1.
- exact Ra2.
- lia. - lia. - lia.
- unfold spZ at 1. rewrite Rsp. evalE AG.
- reflexivity. - lia. - rewrite FFS. unfold ESTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity].
- intros a Ha. split; [replace a with (g + (a - g)) by lia; apply Ag; [exact Hg_in | lia] | unfold ESTACK; lia].
- apply (amem_range_of_block SEGS B LAWS ly3 S3 _ _ _ g 96 _ _ (proj1 HJ3) Hg_in); change (req_size 96) with 96; lia.
- apply (range_addressable_of_block SEGS B LAWS ly3 S3 _ _ _ g 96 _ _ (proj1 HJ3) Hg_in); change (req_size 96) with 96; lia.
- intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 _ _ _ g 96 _ _ (proj1 HJ3) Hg_in); change (req_size 96) with 96; lia.
- exact I. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Heff & Hfr4 & Hpres4 & HSM4).
xsink_intrin Hfr4 HSM4 HSINK. clear HSM4.
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp.
aconsts HROD HJ4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos (proj1 HJ4) Hfin3) as (_ & _ & HFpres4 & HFSpres4). change (fs_frame_bytes 1) with 128 in HFpres4, HFSpres4.
change (128 / 8) with 16 in HFSpres4. rewrite !EFA3 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
destruct (al_blocks _ _ LAWS _ _ _ _ _ g 96 (proj1 HJ4) Hg_in) as (_ & _ & _ & _ & Hgpres4 & _). change (req_size 96) with 96 in Hgpres4.
reseat HS HJ4 HP4 [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11]%nat AG
ltac:(idtac; first [ keptI Hfr4 Hpres4 AG Kgot3 Kgot4 Kcell3 Kcell4 Kguar3 Kguar4 Kuar3 Kuar4 Vgr3 Vgr4
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
assert (Z8 : forall off, 0 <= off -> off + 8 <= 96 -> val_mem SEGS (mrestrict (w_H W3) mem4) (g + off) 8 0).
{ intros off Ho1 Ho2. apply val_mem_zero8. intros i Hi. replace (g + off + i) with (g + (off + i)) by lia. rewrite (Heff (off + i)) by lia. reflexivity. }
assert (Z4 : forall off, 0 <= off -> off + 4 <= 96 -> val_mem SEGS (mrestrict (w_H W3) mem4) (g + off) 4 0).
{ intros off Ho1 Ho2. apply val_mem_zero4. intros i Hi. replace (g + off + i) with (g + (off + i)) by lia. rewrite (Heff (off + i)) by lia. reflexivity. }
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _
(YP09.mkRegion (Some 550%nat) 0 96 0 96
[YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0)); YP09.mkChunk 16 (CVal 8 (SLit 0));
YP09.mkChunk 72 (CVal 8 (SLit 0)); YP09.mkChunk 80 (CVal 8 (SLit 0)); YP09.mkChunk 88 (CVal 4 (SLit 0)); YP09.mkChunk 92 (CVal 4 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Rg, unsigned_lit_small by lia;
split; [lia|]; split; [lia|]; split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Hgpres4 (g + o) ltac:(lia)))|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 0 8 _ 0); [reflexivity | zside | zside | apply Z8; lia]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 8 8 _ 0); [reflexivity | zside | zside | apply Z8; lia]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 16 8 _ 0); [reflexivity | zside | zside | apply Z8; lia]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 72 8 _ 0); [reflexivity | zside | zside | apply Z8; lia]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 80 8 _ 0); [reflexivity | zside | zside | apply Z8; lia]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 88 4 _ 0); [reflexivity | zside | zside | apply Z4; lia]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 92 4 _ 0); [reflexivity | zside | zside | apply Z4; lia]|];
apply Forall_nil)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Rg; change (fs_frame_bytes 1) with 128; change (fs_frame_bytes 1 / 8) with 16; evalE AG;
nunbox HdGF; nunbox HdGC; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region SEGS Ev _ _
(YP09.mkRegion (Some 550%nat) 0 96 0 96
[YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0)); YP09.mkChunk 16 (CVal 8 (SLit 0));
YP09.mkChunk 72 (CVal 8 (SLit 0)); YP09.mkChunk 80 (CVal 8 (SLit 0)); YP09.mkChunk 88 (CVal 4 (SLit 0)); YP09.mkChunk 92 (CVal 4 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Rg, unsigned_lit_small by lia;
split; [lia|]; split; [lia|]; split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Hgpres4 (g + o) ltac:(lia)))|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 0 8 _ 0); [reflexivity | zside | zside | apply Z8; lia]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 8 8 _ 0); [reflexivity | zside | zside | apply Z8; lia]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 16 8 _ 0); [reflexivity | zside | zside | apply Z8; lia]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 72 8 _ 0); [reflexivity | zside | zside | apply Z8; lia]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 80 8 _ 0); [reflexivity | zside | zside | apply Z8; lia]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 88 4 _ 0); [reflexivity | zside | zside | apply Z4; lia]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 92 4 _ 0); [reflexivity | zside | zside | apply Z4; lia]|];
apply Forall_nil)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Rg; change (fs_frame_bytes 1) with 128; change (fs_frame_bytes 1 / 8) with 16; evalE AG;
nunbox HdGF; nunbox HdGC; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS. reshok_bx HS 35%nat. clear_frames.
nbox HdGF. nbox HdGC.
hei_havoc HS; paj_run_tok RUN HS HJ4 SHOK NBspan.
all: try (slim; obl_blk HJ4 Rg E35 Hg_in).
all: try (slim; awrR AG fpos F EFA3).
xsink_stretch HFr HSINK. clear_frames.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) 0 _ HS eq_refl) as HRg; cbn [ms_mem restrict] in HRg;
lazymatch type of HRg with region_ok _ _ _ (YP09.mkRegion (Some 550%nat) ?lo ?hi ?wlo ?whi ?cs) =>
let gf off w v V := pose proof (field_of_region Ex _ 550 g cs lo hi wlo whi off w (SLit v) v HRg
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Rg; apply unsigned_lit_small; lia)
ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V in
let gfa off w n v HE V := pose proof (field_of_region Ex _ 550 g cs lo hi wlo whi off w (SOff n 0) v HRg
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Rg; apply unsigned_lit_small; lia)
ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact HE)
ltac:(cbn; clear - Hpf4096 Hpfceil C1; lia) ltac:(cbn; lia)) as V in
gf 0 8%N 0 U0; gf 8 8%N 0 U8; gf 16 8%N 0 U16; gf 72 8%N 0 U72; gfa 80 8%N 52%nat pf E52 U80; gf 88 4%N 0 U88; gf 92 4%N 1 U92 end;
clear HRg | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) 0 _ HS eq_refl) as HRg; cbn [ms_mem restrict] in HRg;
lazymatch type of HRg with region_ok _ _ _ (YP09.mkRegion (Some 550%nat) ?lo ?hi ?wlo ?whi ?cs) =>
let gf off w v V := pose proof (field_of_region Ex _ 550 g cs lo hi wlo whi off w (SLit v) v HRg
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Rg; apply unsigned_lit_small; lia)
ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V in
let gfa off w n v HE V := pose proof (field_of_region Ex _ 550 g cs lo hi wlo whi off w (SOff n 0) v HRg
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Rg; apply unsigned_lit_small; lia)
ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact HE)
ltac:(cbn; clear - Hpf4096 Hpfceil C1; lia) ltac:(cbn; lia)) as V in
gf 0 8%N 0 U0; gf 8 8%N 0 U8; gf 16 8%N 0 U16; gf 72 8%N 0 U72; gfa 80 8%N 52%nat pf E52 U80; gf 88 4%N 0 U88; gf 92 4%N 1 U92 end;
clear HRg  end.
cbn [N.to_nat] in U0, U8, U16, U72, U80, U88, U92.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
pmkst HS.
change (Z_to_bv 64 333176) with (Z_to_bv 64 (SIGMA AS_asan_memcpy)).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos (proj1 HJ4) HfinS3) as (_ & _ & HCpres4 & _). rewrite EFA3 in HCpres4.
assert (Qcs : cfgp + 48 <= spZ regs - 192 - ESTACK) by (unfold ESTACK; lia).
clear Kgot3 Kcell3 Kguar3 Kuar3 Vgr3 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4. aconsts HROD HJ4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_atS SEGS B LAWS Hsegs OCpy (SIGMA AS_asan_memcpy) AMEMCPY _ (ms_regs msX) (ms_mem msX) TNEWGIFX_STK (spZ regs) [sink_token] ly S W mem md [(1, fpos)]
ly3 S3 _ _ (g + 24) cfgp 48 (-192) (Z_to_bv 64 (BASE + 0x228)) HJ4) end.
- rewrite Ra0. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite Rg. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
- rewrite Ra1. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 10%nat) by lia. rewrite E10. reflexivity.
- exact Ra2.
- lia. - lia. - lia.
- unfold spZ at 1. rewrite Rsp. evalE AG.
- reflexivity. - lia. - rewrite FFS. unfold ESTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity].
- intros a Ha. split; [replace a with (g + (a - g)) by lia; apply Ag; [exact Hg_in | lia] | unfold ESTACK; lia].
- apply (amem_range_of_block SEGS B LAWS ly3 S3 _ _ _ g 96 _ _ (proj1 HJ4) Hg_in); change (req_size 96) with 96; lia.
- apply (range_addressable_of_block SEGS B LAWS ly3 S3 _ _ _ g 96 _ _ (proj1 HJ4) Hg_in); change (req_size 96) with 96; lia.
- intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 _ _ _ g 96 _ _ (proj1 HJ4) Hg_in); change (req_size 96) with 96; lia.
- split; [lia|]. split; [lia|]. split.
{ intros a Ha. split; [| unfold spZ; rewrite Rsp; evalE AG].
apply (aview_some_of_apresent SEGS). apply (proj1 (HCpres4 a ltac:(lia))). }
split; [nunbox HdGC; clear - HdGC Hflo Hfhi; lia|]. split; [apply amem_range_high; zone_lia|]. split.
+ eapply (range_addressable_entry_frame SEGS B LAWS); [exact HJ4 | exact Hfin | exact Hcid0 | exact Hflo | exact Hfhi | exact Hfal
| fptokS | exact HAR | exact HRA].
+ intros _. eapply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 _ _ _ cid pos cfgp 48 (proj1 HJ4) HfinS3); [rewrite EFA3; exact Hflo | rewrite EFA3; exact Hfhi | lia]. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Ha05 & Heff5 & Hfr5 & Hpres5 & HSM5).
xsink_intrin Hfr5 HSM5 HSINK. clear HSM5.
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp.
lazymatch type of Heff5 with forall i, _ -> aview _ _ _ _ = aview _ _ ?memT _ =>
let cmove off w v V Vr :=
pose proof (val_mem_moved SEGS (w_H W3) (w_H W3) memT mem5 (cfgp + off) (g + 24 + off) w v
ltac:(intros kk Hk; replace (g + 24 + off + kk) with (g + 24 + (off + kk)) by lia; replace (cfgp + off + kk) with (cfgp + (off + kk)) by lia;
apply Heff5; cbn [Z.of_nat Pos.to_nat Pos.iter_op Nat.add] in Hk; lia)
(val_mem_entry_frame SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cid pos (cfgp + off) w v HJ4 Hfin
ltac:(lia) ltac:(cbn [Z.of_nat Pos.to_nat Pos.iter_op Nat.add]; lia) ltac:(intros x Hx HF; apply inFP_token in HF; clear - HF Hx Hflo Hf4096; lia) V)) as Vr in
cmove 0 8%nat pal0 CV0 W0; cmove 8 8%nat (ak_path K) CV8 W8; cmove 16 4%nat attr CV16 W16; cmove 20 4%nat gen CV20 W20;
cmove 24 2%nat Wd CV24 W24; cmove 26 2%nat Hd CV26 W26; cmove 28 2%nat ngp CV28 W28; cmove 30 2%nat loops CV30 W30;
cmove 32 8%nat (@ngp_hw NP) CV32 W32; cmove 40 8%nat 0 CV40 W40 end.
lazymatch type of Heff5 with forall i, _ -> aview _ _ _ _ = aview _ _ ?memT _ =>
let keep off w v U Ur :=
pose proof (val_mem_moved SEGS (w_H W3) (w_H W3) memT mem5 (g + off) (g + off) w v
ltac:(intros kk Hk; apply Hfr5; [lia | cbn [Z.of_nat Pos.to_nat Pos.iter_op Nat.add] in Hk; lia | unfold ESTACK; lia]) U) as Ur in
keep 0 8%nat 0 U0 X0; keep 8 8%nat 0 U8 X8; keep 16 8%nat 0 U16 X16; keep 72 8%nat 0 U72 X72; keep 80 8%nat pf U80 X80; keep 88 4%nat 0 U88 X88; keep 92 4%nat 1 U92 X92 end.
clear U0 U8 U16 U72 U80 U88 U92.
nunbox HdGF. nunbox HdGC.
aconsts HROD HJ5 Kgot5 Kcell5 Kguar5 Kuar5 Vgr5.
destruct (al_blocks _ _ LAWS _ _ _ _ _ g 96 (proj1 HJ5) Hg_in) as (_ & _ & _ & _ & Hgpres5 & _). change (req_size 96) with 96 in Hgpres5.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos (proj1 HJ5) Hfin3) as (_ & _ & HFpres5 & HFSpres5). change (fs_frame_bytes 1) with 128 in HFpres5, HFSpres5.
change (128 / 8) with 16 in HFSpres5. rewrite !EFA3 in HFpres5, HFSpres5. fold F in HFpres5, HFSpres5.
reseat HS HJ5 HP5 [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11]%nat AG
ltac:(idtac; first [ keptI Hfr5 Hpres5 AG Kgot4 Kgot5 Kcell4 Kcell5 Kguar4 Kguar5 Kuar4 Kuar5 Vgr4 Vgr5
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
let ckv HE := cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
try rewrite (AG 32%nat) by lia; rewrite HE; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity in
pose proof (st_ok_pi_add_region Ev _ _
(YP09.mkRegion (Some 550%nat) 0 96 0 96
[YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0)); YP09.mkChunk 16 (CVal 8 (SLit 0));
YP09.mkChunk 24 (CVal 8 (SOff 32 0)); YP09.mkChunk 32 (CVal 8 (SOff 42 0)); YP09.mkChunk 40 (CVal 4 (SOff 33 0)); YP09.mkChunk 44 (CVal 4 (SOff 34 0));
YP09.mkChunk 48 (CVal 2 (SOff 36 0)); YP09.mkChunk 50 (CVal 2 (SOff 37 0)); YP09.mkChunk 52 (CVal 2 (SOff 38 0)); YP09.mkChunk 54 (CVal 2 (SOff 39 0));
YP09.mkChunk 56 (CVal 8 (SLit hw)); YP09.mkChunk 64 (CVal 8 (SLit 0)); YP09.mkChunk 72 (CVal 8 (SLit 0)); YP09.mkChunk 80 (CVal 8 (SOff 52 0));
YP09.mkChunk 88 (CVal 4 (SLit 0)); YP09.mkChunk 92 (CVal 4 (SLit 1))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Rg, unsigned_lit_small by lia;
split; [lia|]; split; [lia|]; split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Hgpres5 (g + o) ltac:(lia)))|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 0 8 _ 0); [reflexivity | zside | zside | exact X0]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 8 8 _ 0); [reflexivity | zside | zside | exact X8]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 16 8 _ 0); [reflexivity | zside | zside | exact X16]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 24 8 _ pal0); [ckv E32 | zside | zside | replace (g + 24) with (g + 24 + 0) by lia; exact W0]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 32 8 _ (ak_path K)); [ckv E42 | clear - Rpath; zside | zside | replace (g + 32) with (g + 24 + 8) by lia; exact W8]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 40 4 _ attr); [ckv E33 | zside | zside | replace (g + 40) with (g + 24 + 16) by lia; exact W16]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 44 4 _ gen); [ckv E34 | zside | zside | replace (g + 44) with (g + 24 + 20) by lia; exact W20]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 48 2 _ Wd); [ckv E36 | zside | zside | replace (g + 48) with (g + 24 + 24) by lia; exact W24]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 50 2 _ Hd); [ckv E37 | zside | zside | replace (g + 50) with (g + 24 + 26) by lia; exact W26]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 52 2 _ ngp); [ckv E38 | zside | zside | replace (g + 52) with (g + 24 + 28) by lia; exact W28]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 54 2 _ loops); [ckv E39 | zside | zside | replace (g + 54) with (g + 24 + 30) by lia; exact W30]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 56 8 _ hw); [reflexivity | clear - Rhw; zside | zside | replace (g + 56) with (g + 24 + 32) by lia; exact W32]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 64 8 _ 0); [reflexivity | zside | zside | replace (g + 64) with (g + 24 + 40) by lia; exact W40]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 72 8 _ 0); [reflexivity | zside | zside | exact X72]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 80 8 _ pf); [ckv E52 | clear - Hpf4096 Hpfceil C1; zside | zside | exact X80]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 88 4 _ 0); [reflexivity | zside | zside | exact X88]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 92 4 _ 1); [reflexivity | zside | zside | exact X92]|];
apply Forall_nil)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Rg; change (fs_frame_bytes 1) with 128; change (fs_frame_bytes 1 / 8) with 16; evalE AG;
nunbox HdGF; nunbox HdGC; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ev _ _ =>
let ckv HE := cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
try rewrite (AG 32%nat) by lia; rewrite HE; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity in
pose proof (ast_ok_add_region SEGS Ev _ _
(YP09.mkRegion (Some 550%nat) 0 96 0 96
[YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0)); YP09.mkChunk 16 (CVal 8 (SLit 0));
YP09.mkChunk 24 (CVal 8 (SOff 32 0)); YP09.mkChunk 32 (CVal 8 (SOff 42 0)); YP09.mkChunk 40 (CVal 4 (SOff 33 0)); YP09.mkChunk 44 (CVal 4 (SOff 34 0));
YP09.mkChunk 48 (CVal 2 (SOff 36 0)); YP09.mkChunk 50 (CVal 2 (SOff 37 0)); YP09.mkChunk 52 (CVal 2 (SOff 38 0)); YP09.mkChunk 54 (CVal 2 (SOff 39 0));
YP09.mkChunk 56 (CVal 8 (SLit hw)); YP09.mkChunk 64 (CVal 8 (SLit 0)); YP09.mkChunk 72 (CVal 8 (SLit 0)); YP09.mkChunk 80 (CVal 8 (SOff 52 0));
YP09.mkChunk 88 (CVal 4 (SLit 0)); YP09.mkChunk 92 (CVal 4 (SLit 1))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Rg, unsigned_lit_small by lia;
split; [lia|]; split; [lia|]; split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Hgpres5 (g + o) ltac:(lia)))|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 0 8 _ 0); [reflexivity | zside | zside | exact X0]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 8 8 _ 0); [reflexivity | zside | zside | exact X8]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 16 8 _ 0); [reflexivity | zside | zside | exact X16]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 24 8 _ pal0); [ckv E32 | zside | zside | replace (g + 24) with (g + 24 + 0) by lia; exact W0]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 32 8 _ (ak_path K)); [ckv E42 | clear - Rpath; zside | zside | replace (g + 32) with (g + 24 + 8) by lia; exact W8]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 40 4 _ attr); [ckv E33 | zside | zside | replace (g + 40) with (g + 24 + 16) by lia; exact W16]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 44 4 _ gen); [ckv E34 | zside | zside | replace (g + 44) with (g + 24 + 20) by lia; exact W20]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 48 2 _ Wd); [ckv E36 | zside | zside | replace (g + 48) with (g + 24 + 24) by lia; exact W24]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 50 2 _ Hd); [ckv E37 | zside | zside | replace (g + 50) with (g + 24 + 26) by lia; exact W26]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 52 2 _ ngp); [ckv E38 | zside | zside | replace (g + 52) with (g + 24 + 28) by lia; exact W28]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 54 2 _ loops); [ckv E39 | zside | zside | replace (g + 54) with (g + 24 + 30) by lia; exact W30]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 56 8 _ hw); [reflexivity | clear - Rhw; zside | zside | replace (g + 56) with (g + 24 + 32) by lia; exact W32]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 64 8 _ 0); [reflexivity | zside | zside | replace (g + 64) with (g + 24 + 40) by lia; exact W40]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 72 8 _ 0); [reflexivity | zside | zside | exact X72]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 80 8 _ pf); [ckv E52 | clear - Hpf4096 Hpfceil C1; zside | zside | exact X80]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 88 4 _ 0); [reflexivity | zside | zside | exact X88]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ g 92 4 _ 1); [reflexivity | zside | zside | exact X92]|];
apply Forall_nil)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Rg; change (fs_frame_bytes 1) with 128; change (fs_frame_bytes 1 / 8) with 16; evalE AG;
nunbox HdGF; nunbox HdGC; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS. clear W0 W8 W16 W20 W24 W26 W28 W30 W32 W40 X0 X8 X16 X72 X80 X88 X92 Heff5. nbox HdGF. nbox HdGC.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msv) =>
change ssx with ss_NKX in HS;
eapply (NGK ly S W regs mem md ch cfgp pal0 pala attr gen Wd Hd ngp loops aM rest GPAL cid pos E0 Ev W3 ly3 S3 msv _ k fpos pf g);
[ split; [exact HPRE | split; [exact Hal32 | split; [| split; [exact Hroom | split; [exact Htop32 | split; [exact HROD | split; [exact Hcfg | split; [exact HWH | split; [exact Hpala | split; [exact HPerm | split; [exact Hev | exact Hlive]]]]]]]]]]]
| exact HXE
| split; [exact Hfin | split; [exact Hcid0 | split; [exact Hfal | split; [exact Hflo | split; [exact Hfhi | split; [exact Hcal | exact HRA]]]]]]
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| split; [split; [exact AG | repeat (split; [eassumption|]); eassumption] | exact E42]
| exact E52
| exact Rg
| split; [exact HJ5 | split; [exact Hk3 | split; [exact Hfrs3 | split; [exact Eab3 | split; [exact Hg4096 | split; [exact Hpf4096 | split; [exact Tg | split; [exact Ag | split; [exact Tpf | split; [exact Apf | split; [exact HSINK | exact MLE3]]]]]]]]]]]
| exact HW0 | exact HH0
| exact HS ] | st_ok _ ?Ev ?ssx (restrict _ ?msv) =>
change ssx with ss_NKX in HS;
eapply (NGK ly S W regs mem md ch cfgp pal0 pala attr gen Wd Hd ngp loops aM rest GPAL cid pos E0 Ev W3 ly3 S3 msv _ k fpos pf g);
[ split; [exact HPRE | split; [exact Hal32 | split; [| split; [exact Hroom | split; [exact Htop32 | split; [exact HROD | split; [exact Hcfg | split; [exact HWH | split; [exact Hpala | split; [exact HPerm | split; [exact Hev | exact Hlive]]]]]]]]]]]
| exact HXE
| split; [exact Hfin | split; [exact Hcid0 | split; [exact Hfal | split; [exact Hflo | split; [exact Hfhi | split; [exact Hcal | exact HRA]]]]]]
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| split; [split; [exact AG | repeat (split; [eassumption|]); eassumption] | exact E42]
| exact E52
| exact Rg
| split; [exact HJ5 | split; [exact Hk3 | split; [exact Hfrs3 | split; [exact Eab3 | split; [exact Hg4096 | split; [exact Hpf4096 | split; [exact Tg | split; [exact Ag | split; [exact Tpf | split; [exact Apf | split; [exact HSINK | exact MLE3]]]]]]]]]]]
| exact HW0 | exact HH0
| exact HS ]  end.
exact Hctx.
Qed.
End f. End e.
End d.
