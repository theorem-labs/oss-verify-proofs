(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI08 YI0t YI0m YI0n YI0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0s YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCbw.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC81 YC4b YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a AC8f AC8c AC93 AC9g AC95.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac obl_blk HJ Hin Rn E32 AG :=
let L := getLAWS in
lazymatch goal with |- range_addressable _ (U ?Ex (SOff ?bx 0)) (U _ (SOff ?n ?c)) ?len =>
first [ rewrite (U_atom_off Ex n _ c) by (first [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?AG by lia; exact Rn | lia])
| rewrite (U_atom Ex n _) by (first [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?AG by lia; exact Rn | lia]) ];
lazymatch type of Hin with In (?p, ?m) _ =>
eapply (obl_of_block _ _ L _ _ _ _ _ Ex (SOff bx 0) _ len p m (proj1 HJ) Hin);
[ rewrite (U_atom Ex bx SB) by (first [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?AG by lia; exact E32 | unfold SB; lia]); reflexivity
| lia | lia ] end end.
Ltac kept_ctx_e HKw HJ2 Hc2 Hc1 Rctx AG Hres :=
let L := getLAWS in eapply (region_kept_block_ajw _ L _ _ _ _ _ _ _ _ _ _ 8%nat 0 72 _ _ 72);
[ exact HKw | exact (proj1 HJ2) | exact Hc2
| cbn [ew ewset Nat.eqb]; rewrite ?(AG 8%nat) by lia; rewrite Rctx; apply unsigned_lit_small; lia
| exact Hc1 | lia | change (req_size 72) with 72; lia
| let l1 := fresh "l1" in let l2 := fresh "l2" in let El := fresh "El" in let Hd := fresh "Hd" in
let Hnz := fresh "Hnz" in let Hra := fresh "Hra" in let Ebl := fresh "Ebl" in
intros a Ha [Hnz Hra]; destruct Hres as [(? & _ & _) | (_ & Ebl & _)]; [lia|];
destruct (in_split _ _ Hc1) as (l1 & l2 & El);
lazymatch type of Ebl with ablocks _ ?ly2 ?S2 = _ ++ [?nb] =>
pose proof (sep_blocks_pos _ _ L ly2 S2 _ _ _ (_, 72) nb l1 l2 [] (proj1 HJ2)
ltac:(rewrite Ebl, El, <- app_assoc; reflexivity)) as Hd end;
unfold zdisjoint, block_rng in Hd; cbn [fst snd] in Hd; change (req_size 72) with 72 in Hd; lia ].
Ltac awr2e Actx Hc AG Rctx Usp :=
lazymatch type of Rctx with _ = w64 ?ctxv =>
lazymatch type of Usp with _ = ?spv =>
lazymatch goal with |- awr_ok _ _ ?STK ?sp0 _ _ _ _ _ =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ _ ctxv); [reflexivity | cbn [ew ewset Nat.eqb]; rewrite ?(AG 8%nat) by lia; rewrite Rctx; apply unsigned_lit_small; lia
| cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; replace a with (ctxv + (a - ctxv)) by lia; apply Actx; [exact Hc | lia] |];
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - sp0));
[reflexivity | cbn [ew ewset Nat.eqb]; rewrite ?(AG 2%nat) by lia; rewrite Usp; lia | cbn; lia | cbn; lia | awr_ok_tac] end end end.
Ltac malloc_site_e HS HJ nval a0tac AG Usp Rctx Hom HSZ :=
let Bv := getB in let L := getLAWS in let T := getTL in let M := getML in let AM := getAM in
let HUL := getHUL in let ENV := getENV in
let Rra := fresh "Rra" in let Rsp := fresh "Rsp" in let Rgp := fresh "Rgp" in let Rtp := fresh "Rtp" in let Rs0 := fresh "Rs0" in
prreg HS (1%bv : bv 5) Rra; prreg HS (2%bv : bv 5) Rsp; prreg HS (3%bv : bv 5) Rgp; prreg HS (4%bv : bv 5) Rtp; prreg HS (8%bv : bv 5) Rs0;
pmkst HS; ppcs;
ppcs;
lazymatch type of Usp with _ = ?spv =>
lazymatch type of Rctx with _ = w64 ?ctxv =>
lazymatch type of HJ with ajournal _ _ ?STK ?sp0 ?FP ?ly ?S ?W0 ?mem0 ?md0 ?own ?lyc ?Sc ?Wc (ms_mem ?msX) ?mdc ?kk =>
lazymatch type of Rra with _ = Z_to_bv 64 ?ra =>
let Hnev := fresh "Hnev" in pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _);
eapply SRr_bind;
[ eapply (aj_malloc_at _ Bv L pa_segs_low ENV M AM Wc (ms_regs msX) (ms_mem msX) STK sp0 FP ly S W0 mem0 md0 own
lyc Sc mdc kk nval (spv - 320 - sp0) (Z_to_bv 64 ra) [] HJ);
[ first [ a0tac | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ exact (proj1 HSZ) | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ exact (proj2 HSZ) | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ unfold spZ; rewrite Rsp, ?(AG 2%nat) by lia; rewrite Usp, unsigned_lit_small by lia; lia | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ exact Hom | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ lia | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ lia | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ rewrite Rgp, ?(AG 3%nat) by lia; lazymatch goal with H : ew _ 3%nat = Z_to_bv 64 (as_gp _) |- _ => rewrite H; reflexivity end | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ rewrite Rtp, ?(AG 4%nat) by lia; lazymatch goal with H : ew _ 4%nat = Z_to_bv 64 (as_tp _) |- _ => rewrite H; reflexivity end | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ exact Rra | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity] | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ match goal with H1 : st_nev ?Sb + LZW_EV <= EV_MAX, H2 : LZW_EV = 19 |- _ => clear - Hnev H1 H2; lia end | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ apply (achain_chain_pre lyc _ (spv - 320) ctxv [] _ (achain_low lyc _ (spv - 320) ctxv ltac:(lia)));
[ unfold spZ; rewrite Rsp, ?(AG 2%nat) by lia; rewrite Usp, unsigned_lit_small by lia; lia
| unfold s0Z; rewrite Rs0, ?(AG 8%nat) by lia; rewrite Rctx; apply unsigned_lit_small; lia
| unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia ] | match goal with |- ?g => idtac "MSFAIL" g end ]
| first [ rewrite call_trace_nil; unfold raZ; rewrite Rra, unsigned_lit_small by lia; try rewrite (proj2 (Z.eqb_neq _ _)) by (pose proof (pal_rt_below Bv T); lia);
hul_tac | match goal with |- ?g => idtac "MSFAIL" g end ] ]
| clear Rra Rsp Rgp Rtp Rs0 Hnev ] end end end end.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition lzw_rodata_ok (H : word -> bool) (m : word -> option byte) : Prop := val_mem SEGS (mrestrict H m) (VAL (A_OBJ 10)) 8 MAGIC_0101.
Lemma alu64_add0 : forall x : word, alu64 ALU_ADD x (Z_to_bv 64 0) = x.
Proof.
intros x. unfold alu64, alu. apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned.
pose proof (bv_unsigned_in_range 64 x) as Hr.
change (bv_wrap 64 0) with 0. rewrite Z.add_0_r. apply bv_wrap_small. exact Hr.
Qed.
Ltac ctx_field_n n HS idx Rctx AG :=
lazymatch goal with |- val_mem _ _ (?ctxv + ?off) ?nn ?v =>
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let w := eval vm_compute in (N.of_nat nn) in
eapply (field_of_region Ex _ n ctxv _ _ _ _ _ off w _ v);
[ eapply (st_ok_pi_region_nth Ex ssx msx idx); [exact HS | reflexivity]
| cbn [ew ewset Nat.eqb]; rewrite ?(AG n) by lia; rewrite Rctx; apply unsigned_lit_small; lia
| cbn; repeat (first [left; reflexivity | right])
| cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [reflexivity | rewrite ?AG by lia; assumption | match goal with |- ?g => idtac "FIELDVAL" g end]
| cbn; lia | cbn; lia ] | st_ok _ ?Ex ?ssx ?msx =>
let w := eval vm_compute in (N.of_nat nn) in
eapply (field_of_region Ex _ n ctxv _ _ _ _ _ off w _ v);
[ eapply (st_ok_region_nth Ex ssx msx idx); [exact HS | reflexivity]
| cbn [ew ewset Nat.eqb]; rewrite ?(AG n) by lia; rewrite Rctx; apply unsigned_lit_small; lia
| cbn; repeat (first [left; reflexivity | right])
| cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [reflexivity | rewrite ?AG by lia; assumption | match goal with |- ?g => idtac "FIELDVAL" g end]
| cbn; lia | cbn; lia ]  end
| |- val_mem _ _ ?ctxv _ ?v =>
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
rewrite <- (Z.add_0_r ctxv) at 1;
eapply (field_of_region Ex _ n ctxv _ _ _ _ _ 0 8%N _ v);
[ eapply (st_ok_pi_region_nth Ex ssx msx idx); [exact HS | reflexivity]
| cbn [ew ewset Nat.eqb]; rewrite ?(AG n) by lia; rewrite Rctx; apply unsigned_lit_small; lia
| cbn; repeat (first [left; reflexivity | right])
| cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [reflexivity | rewrite ?AG by lia; assumption | match goal with |- ?g => idtac "FIELDVAL" g end]
| cbn; lia | cbn; lia ] | st_ok _ ?Ex ?ssx ?msx =>
rewrite <- (Z.add_0_r ctxv) at 1;
eapply (field_of_region Ex _ n ctxv _ _ _ _ _ 0 8%N _ v);
[ eapply (st_ok_region_nth Ex ssx msx idx); [exact HS | reflexivity]
| cbn [ew ewset Nat.eqb]; rewrite ?(AG n) by lia; rewrite Rctx; apply unsigned_lit_small; lia
| cbn; repeat (first [left; reflexivity | right])
| cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [reflexivity | rewrite ?AG by lia; assumption | match goal with |- ?g => idtac "FIELDVAL" g end]
| cbn; lia | cbn; lia ]  end end.
Ltac frame_tac_e HS idx AG :=
lazymatch type of HS with st_ok_pi _ _ ?E1 ?ss1 ?ms1 =>
eapply (tlzw_frame_of_region E1);
[ eapply (st_ok_pi_region_nth E1 ss1 ms1 idx); [exact HS | reflexivity]
| cbn [ew ewset Nat.eqb]; rewrite ?(AG 2%nat) by lia; assumption
| let od := fresh "od" in let r := fresh "r" in let Hin := fresh "Hin" in
intros od r Hin; cbv [TSAVED In] in Hin;
repeat (destruct Hin as [Hin | Hin];
[ apply pair_equal_spec in Hin as [<- <-]; eexists; split;
[ cbv; tauto
| cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; rewrite ?AG by lia; assumption ] | ]);
destruct Hin ] | st_ok _ ?E1 ?ss1 ?ms1 =>
eapply (tlzw_frame_of_region E1);
[ eapply (st_ok_region_nth E1 ss1 ms1 idx); [exact HS | reflexivity]
| cbn [ew ewset Nat.eqb]; rewrite ?(AG 2%nat) by lia; assumption
| let od := fresh "od" in let r := fresh "r" in let Hin := fresh "Hin" in
intros od r Hin; cbv [TSAVED In] in Hin;
repeat (destruct Hin as [Hin | Hin];
[ apply pair_equal_spec in Hin as [<- <-]; eexists; split;
[ cbv; tauto
| cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; rewrite ?AG by lia; assumption ] | ]);
destruct Hin ]  end.
Lemma frm_off_imgP : forall B ly S (W : world SEGS) mem md cid pos,
AR SEGS B ly S W mem md -> In (cid, pos) (frames S) -> off_img (frame_addr ly cid pos) (fs_frame_bytes cid).
Proof.
intros B ly S W mem md cid pos (M & LG & _) Hin. unfold off_img. pose proof (pa_img_cover ly S md LG) as [C1 C2].
pose proof (frame_facts B ly S _ cid pos M Hin) as (Fc & Fp & _ & _ & _ & _ & _ & _ & F64 & _).
destruct (Z.le_gt_cases (frame_addr ly cid pos + fs_frame_bytes cid) 0x10000) as [|H1]; [left; lia|].
destruct (Z.le_gt_cases 0x5fb000 (frame_addr ly cid pos)) as [|H2]; [right; lia|]. exfalso.
apply (client_byte_not_img B ly S _ (Z.max (frame_addr ly cid pos) 0x10000) M).
- right. exists (cid, pos). split; [exact Hin|]. left. unfold in_zr. cbn [fst snd]. lia.
- unfold in_zr. lia.
Qed.
Lemma st_ok_pi_submem : forall E ss ms rs,
st_ok_pi SEGS VAL E ss ms -> submem rs (ss_mem ss) -> regions_wf rs = true ->
st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (ss_regs ss) rs (ss_resv ss) (ss_facts ss)) ms.
Proof. intros E ss ms rs HS Hs Hwf. destruct ss as [pc0 sr0 fr0 sm0 rv0 fs0]. exact (st_ok_submem SEGS E _ ms rs HS Hs Hwf). Qed.
Lemma st_ok_conds_nil0 : forall E ss ms,
st_ok SEGS E ss ms ->
st_ok SEGS E (mkSST (ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss)
(mkFacts (f_atoms (ss_facts ss)) [] (f_alias (ss_facts ss)))) ms.
Proof.
intros E ss ms (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & (Ha & Hc & Hl)).
cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts f_atoms f_conds f_alias]. repeat (split; [assumption|]). split; [exact I | exact Hl].
Qed.
Lemma st_ok_conds_nil : forall E ss ms,
st_ok_pi SEGS VAL E ss ms ->
st_ok_pi SEGS VAL E (mkSST (ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss)
(mkFacts (f_atoms (ss_facts ss)) [] (f_alias (ss_facts ss)))) ms.
Proof.
intros E ss ms HS. destruct ss as [pc0 sr0 fr0 sm0 rv0 fs0]. exact (st_ok_conds_nil0 E _ ms HS).
Qed.
Lemma shadow_cells_in_frame : forall fa pR bytes j,
fa mod 32 = 0 -> bytes mod 64 = 0 -> 0 <= bytes -> pR mod 8 = 0 -> fa <= pR -> pR + 16 <= fa + bytes -> 0 <= j < 2 ->
fa / 8 <= pR / 8 + j < fa / 8 + bytes / 8.
Proof.
intros fa pR bytes j Hfa Hb Hb0 HpR H1 H2 Hj.
pose proof (Z.div_mod fa 32 ltac:(lia)) as A. pose proof (Z.div_mod pR 8 ltac:(lia)) as Bq. pose proof (Z.div_mod bytes 64 ltac:(lia)) as C.
rewrite Hfa, Z.add_0_r in A. rewrite HpR, Z.add_0_r in Bq. rewrite Hb, Z.add_0_r in C.
set (q := fa / 32) in *. set (r := pR / 8) in *. set (m := bytes / 64) in *. clearbody q r m. subst fa pR bytes.
replace (32 * q) with (4 * q * 8) by lia. replace (64 * m) with (8 * m * 8) by lia. rewrite !Z.div_mul by lia. lia.
Qed.
Lemma stack_cells : forall lo hi pR, lo mod 4096 = 0 -> hi mod 4096 = 0 -> lo <= pR -> pR + 16 <= hi ->
lo mod 8 = 0 /\ (hi - lo) mod 8 = 0.
Proof.
intros lo hi pR Hlo Hhi H1 H2.
pose proof (Z.div_mod lo 4096 ltac:(lia)) as A. pose proof (Z.div_mod hi 4096 ltac:(lia)) as C.
rewrite Hlo, Z.add_0_r in A. rewrite Hhi, Z.add_0_r in C.
split.
- rewrite A. replace (4096 * (lo / 4096)) with ((512 * (lo / 4096)) * 8) by lia. apply Z_mod_mult.
- rewrite A, C. replace (4096 * (hi / 4096) - 4096 * (lo / 4096)) with ((512 * (hi / 4096) - 512 * (lo / 4096)) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma awr_byte_ly : forall STK sp0 FP bl0 blc ly ly' own a,
(forall cid pos, frame_addr ly' cid pos = frame_addr ly cid pos) ->
awr_byte STK sp0 FP bl0 blc ly own a -> awr_byte STK sp0 FP bl0 blc ly' own a.
Proof.
intros STK sp0 FP bl0 blc ly ly' own a Efa [H | [H | [H | (cid & pos & Hin & H)]]]; [left; exact H | right; left; exact H | right; right; left; exact H |].
right. right. right. exists cid, pos. split; [exact Hin|]. rewrite !Efa. exact H.
Qed.
Lemma in_tnz_nz : forall (p n : Z) l, p <> 0 -> In (p, n) l -> In (p, n) (tnz l).
Proof.
intros p n l Hp Hin. unfold tnz. apply filter_In. split; [exact Hin|]. cbn [fst].
replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hp). reflexivity.
Qed.
Lemma in_tnz_tl : forall (b x : Z * Z) l, In b (tnz l) -> In b (tnz (x :: l)).
Proof. intros b [p n] l Hb. rewrite tnz_cons. apply in_app_iff. right. exact Hb. Qed.
Section f.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes SEGS B.
Hypothesis AFREE : afree_realizes SEGS B.
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA AS_asan_memcpy).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_1) (PI := PI).
Hypothesis HUL : forall t, In t (lzw_traces (as_code B) BASE) -> In t (as_universe B).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_1 PI.
Definition sr_epi : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 1%bv (SOff 8 40)) 9%bv (SOff 8 32)) 18%bv (SOff 8 24)) 19%bv (SOff 8 16)) 20%bv (SOff 8 8))
22%bv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 0) (SLit 3)) (SOff 27 0))) 30%bv (SOff 8 60)) 2%bv (SOff 2 (-320)).
Definition ctx_region_epi : YP09.region :=
YP09.mkRegion (Some 8%nat) 0 72 0 72
[YP09.mkChunk 0 (CVal 8 (SOff 37 0)); YP09.mkChunk 8 (CVal 8 (SOff 38 0)); YP09.mkChunk 16 (CVal 8 (SOff 39 0));
YP09.mkChunk 24 (CVal 8 (SOff 40 0)); YP09.mkChunk 32 (CVal 8 (SOff 41 0)); YP09.mkChunk 40 (CVal 8 (SOff 32 0));
YP09.mkChunk 60 (CVal 4 (SOff 33 0))].
Definition stk_region_epi : YP09.region :=
YP09.mkRegion (Some 2%nat) (-320) 0 0 0
[YP09.mkChunk (-216) (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 60) (SLit 3)) (SOff 27 0)));
YP09.mkChunk (-192) (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 40) (SLit 3)) (SOff 27 0)));
YP09.mkChunk (-168) (CVal 8 (SOff 34 0)); YP09.mkChunk (-144) (CVal 8 (SOff 35 0)); YP09.mkChunk (-112) (CVal 8 (SOff 8 40));
YP09.mkChunk (-8) (CVal 8 (SOff 42 0)); YP09.mkChunk (-16) (CVal 8 (SOff 43 0)); YP09.mkChunk (-24) (CVal 8 (SOff 44 0));
YP09.mkChunk (-32) (CVal 8 (SOff 45 0)); YP09.mkChunk (-40) (CVal 8 (SOff 46 0)); YP09.mkChunk (-48) (CVal 8 (SOff 47 0));
YP09.mkChunk (-56) (CVal 8 (SOff 48 0)); YP09.mkChunk (-64) (CVal 8 (SOff 49 0)); YP09.mkChunk (-72) (CVal 8 (SOff 50 0));
YP09.mkChunk (-80) (CVal 8 (SOff 51 0)); YP09.mkChunk (-88) (CVal 8 (SOff 52 0)); YP09.mkChunk (-96) (CVal 8 (SOff 53 0));
YP09.mkChunk (-104) (CVal 8 (SOff 54 0))].
Definition end_region_epi : YP09.region := YP09.mkRegion (Some 36%nat) 0 2 0 2 [].
Definition rodata_region_epi : YP09.region :=
YP09.mkRegion (Some (A_OBJ 10)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit MAGIC_0101))].
Definition facts_epi : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (8%nat, PTR 4); (27%nat, mkAF SB SB 0); (25%nat, mkAF 2 256 0);
(32%nat, PTR 4); (33%nat, mkAF 0 (2^27 - 2) 0); (34%nat, mkAF 0 (2^63 - 16) 3); (35%nat, mkAF 0 12 0); (36%nat, PTR 1) ]
[] [ (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SLL (SOff 33 0) (SLit 1)), SOff 36 0) ].
Definition facts_epiA : facts :=
mkFacts (f_atoms facts_epi) [ mkAC BC_GEU (SOff 36 0) (SOff 32 0) ] (f_alias facts_epi).
Definition ss_epi : sstate := mkSS PC_EPI sr_epi [ctx_region_epi; stk_region_epi; end_region_epi; rodata_region_epi] None facts_epi.
Definition ss_epi_c : sstate := Eval vm_compute in ss_epi.
Lemma tfree_anyo : forall W regsT memT STK1 sp1 FP1 own lyb Sb W0 memb mdb lyc Sc mdc k p n (o : Z) raw v0,
ajournal SEGS B STK1 sp1 FP1 lyb Sb W0 memb mdb own lyc Sc W memT mdc k ->
(p = 0 \/ (In (p, n) (ablocks B lyc Sc) /\ aftok FP1 (ablocks B lyb Sb) (p, n))) ->
getr regsT 10 = w64 p -> spZ regsT = sp1 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK1 ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
s0Z regsT = v0 -> v0 < alloc_ceiling ->
st_nev Sc < EV_MAX ->
bv_unsigned raw <> pc_free_ra0 (as_code B) -> In [pc_free_ra0 (as_code B); bv_unsigned raw] (as_universe B) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free (as_code B))) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK1 sp1 FP1 lyb Sb W0 memb mdb own ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\ frames S2 = frames Sc /\
((p = 0 /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc)) \/
(p <> 0 /\ exists l1 l2, ablocks B lyc Sc = l1 ++ (p, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2)) /\
acall_kept SEGS B lyc Sc W memT W2 mem2 (sp1 + o - ASTACK) (sp1 + o) (fun a => p <> 0 /\ p <= a < p + req_size n)).
Proof.
intros W regsT memT STK1 sp1 FP1 own lyb Sb W0 memb mdb lyc Sc mdc k p n o raw v0
HJ Hcase Ha0 Hsp Ho16 Ho0 Hstk Hgp Htp Hra Hraw Hra4 Hs0 Hv0 Hev Hrane Htr.
pose proof pa_segs_low as Hsegs.
assert (Hch : chain_pre lyc (aview SEGS (w_H W) memT) regsT []).
{ eapply (achain_chain_pre lyc _ (sp1 + o) v0 []); [apply achain_low; exact Hv0 | | exact Hs0 | unfold raZ; rewrite Hra; exact Hra4].
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hstk0 & Hceil & Hslo & _) & _). pose proof asan_consts as (C1 & _).
assert (ASTACK = 16384) as Has by reflexivity. rewrite Hsp. clear - Hstk0 Hceil Hslo Hstk Ho0 C1 Has. lia. }
assert (Htr' : In (call_trace0 (pc_free_ra0 (as_code B)) regsT []) (as_universe B)).
{ rewrite call_trace_nil. unfold raZ. rewrite Hra. replace (bv_unsigned raw =? pc_free_ra0 (as_code B)) with false; [exact Htr|].
symmetry. apply Z.eqb_neq. exact Hrane. }
destruct Hcase as [-> | [Hin Htok]].
- eapply SRr_mono.
{ eapply (aj_free_null_at SEGS B LAWS Hsegs errno_low ML AFREE W regsT memT STK1 sp1 FP1 lyb Sb W0 memb mdb own lyc Sc mdc k o raw []
HJ Ha0); try eassumption; try lia. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP & HPerm & Hfrs & HK).
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP|]. split; [exact Hfrs|].
split; [left; split; [reflexivity | exact HPerm]|].
eapply acall_kept_mono_E; [exact HK|]. intros a [].
- eapply SRr_mono.
{ eapply (aj_free_at SEGS B LAWS Hsegs errno_low ML AFREE W regsT memT STK1 sp1 FP1 lyb Sb W0 memb mdb own lyc Sc mdc k p n o raw []
HJ Hin Ha0); try eassumption; try lia; try reflexivity.
all: try (intros H0 i Hi; exact (Htok H0 i Hi)).
all: match goal with |- ?g => idtac "FREELEFT" g end. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP & Hl & Hfrs & HK).
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP|]. split; [exact Hfrs|].
assert (Hp0 : p <> 0).
{ destruct (al_blocks _ _ LAWS _ _ _ _ _ p n (proj1 HJ) Hin) as (_ & H4096 & _). lia. }
split; [right; split; [exact Hp0 | exact Hl]|].
eapply acall_kept_mono_E; [exact HK|]. intros a Ha. split; [exact Hp0 | exact Ha].
Qed.
Lemma tlzw_kept_of_journal : forall sp lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k2 pR (Ex : Z -> Prop),
ajournal SEGS B LZW_TSTK sp [] lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k2 ->
(forall b, In b (ablocks B lyc Sc) -> In b (ablocks B ly2 S2)) ->
tlzw_kept SEGS B lyc Sc W memc W2 mem2 sp pR Ex.
Proof.
intros sp lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k2 pR Ex HJ Hlive.
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & F3 & F4 & _ & Hpres & (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof pa_segs_low as Hsegs.
split; [intros a Ha Hn _; apply F1; [exact Ha | exact Hn]|].
split; [intros b m i Hb Hi _; apply (F2 b m i Hb (Hlive _ Hb) Hi); intros (r & Hr & _); exact Hr|].
split; [intros a Hi Hn He; exact (F3 a Hi Hn He (fp_spares_closed [] a sink_closed_nil))|].
split; [intros cid pos a Hf Ha _; apply (F4 cid pos a Hf Ha); intros (r & Hr & _); exact Hr|].
split; [|exact Hpres].
intros a Ha Hn Hp. eapply (apresent_transfer SEGS); [lia | | apply F1; [exact Ha | exact Hn] | exact Hp].
intros Himg. pose proof (Hsegs a Himg). lia.
Qed.
Lemma tlzw_pR_kept_of_journal : forall sp lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k2 pR a,
ajournal SEGS B LZW_TSTK sp [] lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k2 ->
tlzw_pR_ok SEGS lyc Sc W memc pR -> (sp <= pR \/ pR + 16 <= sp - LZW_TSTK) -> pR + 16 <= 2 ^ 63 ->
pR <= a < pR + 16 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a.
Proof.
intros sp lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k2 pR a HJ HpR Hside H63 Ha.
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & F3 & F4 & _ & Hpres & (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HpR as [(cid & pos & Hf & Hin & _) | Hstk].
- apply (F4 cid pos a Hf); [left; apply Hin; lia | intros (r & Hr & _); exact Hr].
- apply F1; lia.
Qed.
Lemma tlzw_fail_post : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP idl icl ly2 S2 W2 regs2 mem2 md2 k2 res,
tlzw_caller B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP idl icl ->
ajournal SEGS B LZW_TSTK (spZ regs) [] lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k2 -> k2 <= LZW_EV ->
aregs_preserved regs regs2 -> getr regs2 10 = w64 res -> (res = 2 \/ res = 5) -> frames S2 = frames Sc ->
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
tlzw_post SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs pR W2 (mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP idl icl ly2 S2 W2 regs2 mem2 md2 k2 res
(HJc & Hra0 & Hgp & Htp & Hal16 & Hwlo & Hwhi & HpR8 & HpRside & HpR0 & HpR63 & HpRw & HpRok & HnP & Hidl & Hicl & Hev & Hlive)
HJ2 Hk2 HP Ha0 Hres Hfrs HPerm.
pose proof pa_segs_low as Hsegs. assert (HEV : LZW_EV = 19) by reflexivity.
exists ly2, S2, regs2, mem2, md2, res. split; [reflexivity|].
split.
{ eapply ajournal_mono_k.
{ change own with ([] ++ own). eapply (ajournal_sub SEGS B LAWS Hsegs); [exact HJc | exact HJ2 | exact Hwlo | exact Hwhi |].
intros a (r & Hr & _). destruct Hr. }
rewrite HEV. lia. }
split; [exact HP|]. split; [exact Ha0|]. split; [exact Hfrs|].
right. split; [exact Hres|]. split; [exact HPerm|].
split; [eapply tlzw_kept_of_journal; [exact HJ2 | intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Hb]]|].
intros a Ha. eapply tlzw_pR_kept_of_journal; [exact HJ2 | exact HpRok | exact HpRside | exact HpR63 | lia].
Qed.
Lemma tlzw_pR_high : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP idl icl,
tlzw_caller B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP idl icl ->
4096 <= pR /\ (pR + 16 <= 0x10000 \/ 0x5fb000 <= pR) /\ (pR + 16 <= kLowShadowBeg \/ kHighMemBeg <= pR).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP idl icl HC.
pose proof HC as (HJc & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpR63 & _ & HpRok & _).
pose proof HJc as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HpRok as [(cid & pos & Hf & Hin & _) | Hstk].
- destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hf) as (_ & _ & Hh).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR Hf) as Hh_img.
pose proof (Hin pR ltac:(lia)) as [H1 _]. pose proof (Hin (pR + 15) ltac:(lia)) as [_ H2]. unfold frame_rng in H1, H2. cbn [fst snd] in H1, H2.
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
- pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & _ & _ & Hh). unfold kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
Lemma tlzw_pR_bound : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP idl icl,
tlzw_caller B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP idl icl -> pR + 16 <= 2 ^ 47.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP idl icl
(HJc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpRok & _).
pose proof HJc as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & _ & _ & H47 & _) & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HpRok as [(cid & pos & Hf & Hin & _) | Hstk]; [|lia].
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hf) as (_ & Hc & _). pose proof (Hin (pR + 15) ltac:(lia)) as [_ H2].
unfold frame_rng in H2. cbn [fst snd] in H2. lia.
Qed.
Lemma tlzw_pR_present : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP idl icl ly2 S2 W2 mem2 md2 k2 a,
tlzw_caller B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP idl icl ->
ajournal SEGS B LZW_TSTK (spZ regs) [] lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k2 ->
pR <= a < pR + 16 -> apresent (w_H W2) mem2 a.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP idl icl ly2 S2 W2 mem2 md2 k2 a HC HJ2 Ha.
pose proof HC as (HJc & Hra0 & Hgp & Htp & Hal16 & Hwlo & Hwhi & HpR8 & HpRside & HpR0 & HpR63 & HpRw & HpRok & _).
pose proof (tlzw_pR_high _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC) as (Hh & Hh_img & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof pa_segs_low as Hsegs.
eapply (apresent_transfer SEGS); [lia | intros Hi; pose proof (pa_img_range a Hi); lia | | exact (proj2 (HpRw a Ha))].
eapply tlzw_pR_kept_of_journal; [exact HJ2 | exact HpRok | exact HpRside | exact HpR63 | exact Ha].
Qed.
Lemma tlzw_pR_addressable : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP idl icl ly2 S2 W2 mem2 md2 k2,
tlzw_caller B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP idl icl ->
ajournal SEGS B LZW_TSTK (spZ regs) [] lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k2 ->
range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF pR 16.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP idl icl ly2 S2 W2 mem2 md2 k2 HC HJ2.
pose proof HC as (HJc & Hra0 & Hgp & Htp & Hal16 & Hwlo & Hwhi & HpR8 & HpRside & HpR0 & HpR63 & HpRw & HpRok & _).
pose proof HJc as (HAR & _). pose proof HJ2 as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & F1 & F2 & F3 & F4 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HpRok as [(cid & pos & Hf & Hin & Hz0 & Hz1) | Hstk].
- destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hf) as (Hal32 & _).
pose proof (Hin pR ltac:(lia)) as [H1 _]. pose proof (Hin (pR + 15) ltac:(lia)) as [_ H2]. unfold frame_rng in H1, H2. cbn [fst snd] in H1, H2.
destruct (frame_facts B lyc Sc _ cid pos (proj1 HAR) Hf) as (_ & _ & _ & _ & _ & _ & _ & _ & Hb64 & Hbm64 & _).
assert (Hsh : forall j, 0 <= j < 2 -> in_zr (shadow_addr pR + j) (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)).
{ intros j Hj. unfold in_zr, shadow_addr. cbn [fst snd].
pose proof (shadow_cells_in_frame (frame_addr lyc cid pos) pR (fs_frame_bytes cid) j Hal32 Hbm64 ltac:(lia) HpR8 H1 ltac:(lia) Hj). lia. }
apply zero_shadow_range; [exact HpR8 | reflexivity |].
intros j Hj. change (16 / 8) with 2 in Hj. unfold shadow_of_addr. change (SHADOW_OFF + pR / 8) with (shadow_addr pR).
destruct (Z.eq_dec j 0) as [-> | Hj1].
+ rewrite Z.add_0_r. rewrite <- Hz0. apply (F4 cid pos _ Hf); [right; rewrite <- (Z.add_0_r (shadow_addr pR)); apply Hsh; lia | intros (r & Hr & _); exact Hr].
+ replace j with 1 by lia. rewrite <- Hz1. apply (F4 cid pos _ Hf); [right; apply Hsh; lia | intros (r & Hr & _); exact Hr].
- pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR2))) as (_ & _ & _ & _ & Hpal & Hpah & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
pose proof (al_zshadow _ _ LAWS _ _ _ _ _ (ly_stk_lo ly2, ly_stk_hi ly2 - ly_stk_lo ly2) HAR2 ltac:(left; reflexivity)) as Hz. cbn [fst snd] in Hz.
rewrite Elo, Ehi in *. unfold page_aligned in Hpal, Hpah.
destruct (stack_cells _ _ pR Hpal Hpah ltac:(lia) ltac:(lia)) as [Hm1 Hm2].
eapply range_addressable_sub; [apply zero_shadow_range; [exact Hm1 | exact Hm2 | exact Hz] | lia | lia].
Qed.
Lemma tlzw_kept_success :
forall sp lyc Sc W memc mdc W12 mem12 (memr : word -> option byte) W13 mem13 ly12 S12 md12r pR (Ebb E13 : Z -> Prop),
AR SEGS B lyc Sc W memc mdc ->
tlzw_kept SEGS B lyc Sc W memc W12 mem12 sp pR Ebb ->
(forall x : word, ~ (pR <= bv_unsigned x < pR + 12) -> memr x = mem12 x) ->
mem_grows (mrestrict (w_H W12) mem12) (mrestrict (w_H W12) memr) ->
acall_kept SEGS B ly12 S12 W12 memr W13 mem13 (sp - 320 - ASTACK) (sp - 320) E13 ->
AR SEGS B ly12 S12 W12 memr md12r ->
(forall b, In b (ablocks B lyc Sc) -> In b (ablocks B ly12 S12)) ->
frames S12 = frames Sc -> (forall cid pos, frame_addr ly12 cid pos = frame_addr lyc cid pos) ->
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ (pR <= b + i < pR + 12) /\ ~ E13 (b + i)) ->
(forall cid pos a, In (cid, pos) (frames Sc) ->
in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8) -> ~ E13 a) ->
(pR + 16 <= 0x10000 \/ 0x5fb000 <= pR) -> alloc_ceiling <= sp - LZW_TSTK -> sp <= 2 ^ 63 ->
tlzw_kept SEGS B lyc Sc W memc W13 mem13 sp pR Ebb.
Proof.
intros sp lyc Sc W memc mdc W12 mem12 memr W13 mem13 ly12 S12 md12r pR Ebb E13
HARc (T1 & T2 & T3 & T4 & T5 & T6) Hrun Hgr (K1 & K2 & K3 & K4 & K5 & K6) HAR12 Hlive Hfrs Efa Hsep Hsepf HpRh Hceil H63.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof pa_segs_low as Hsegs.
assert (HTS : LZW_TSTK = 336 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (RUNr : forall a, 0 <= a < 2 ^ 64 -> ~ (pR <= a < pR + 12) -> aview SEGS (w_H W12) memr a = aview SEGS (w_H W12) mem12 a).
{ intros a Ha Hp. apply (aview_eq_of SEGS). unfold mrestrict. rewrite (Hrun (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by exact Ha. exact Hp. }
split.
{ intros a Ha Hn Hp. rewrite (K1 a Ha) by lia. rewrite (RUNr a ltac:(lia) Hp). exact (T1 a Ha Hn Hp). }
split.
{ intros b m i Hb Hi HnE. destruct (Hsep b m i Hb Hi) as [Hp HnE13].
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HARc Hb) as (_ & H4096 & Hbceil & _).
rewrite (K2 b m i (Hlive _ Hb) Hi HnE13). rewrite (RUNr (b + i) ltac:(lia) Hp). exact (T2 b m i Hb Hi HnE). }
split.
{ intros a Hi Ho He. pose proof (Hsegs a Hi) as Ha. pose proof (pa_img_range a Hi) as Ha'. rewrite (K3 a Hi Ho He). rewrite (RUNr a ltac:(lia) ltac:(lia)). exact (T3 a Hi Ho He). }
split.
{ intros cid pos a Hf Hzr Hp.
assert (Ha : 0 <= a < 2 ^ 64).
{ destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HARc Hf) as (Hf0 & Hfc & Hfh).
destruct Hzr as [H | H]; unfold in_zr, frame_rng in H; cbn [fst snd] in H; [lia|].
destruct (frame_facts B lyc Sc _ cid pos (proj1 HARc) Hf) as (_ & _ & _ & _ & _ & _ & _ & _ & Hb64 & _).
pose proof (YCbq.shadow_addr_bounds (frame_addr lyc cid pos) ltac:(clear - Hf0 Hfc Hb64 C1 C4; lia)) as [Hs0 Hs1].
assert (0 <= fs_frame_bytes cid / 8) by (apply Z.div_pos; lia).
pose proof (shadow_range_below (frame_addr lyc cid pos) (fs_frame_bytes cid) ltac:(lia) ltac:(lia) ltac:(clear - Hfc Hf0 Hb64 C1 C4; lia)).
clear - H Hs0 Hs1 H0 H1 C1 C2 C3 C4 C5. unfold kLowMemEnd in Hs0. lia. }
rewrite (K4 cid pos a ltac:(rewrite Hfrs; exact Hf) ltac:(unfold frame_rng; cbn [fst snd]; rewrite !Efa; unfold frame_rng in Hzr; cbn [fst snd] in Hzr; exact Hzr) (Hsepf cid pos a Hf Hzr)).
rewrite (RUNr a Ha Hp). exact (T4 cid pos a Hf Hzr Hp). }
split.
{ intros a Ha Hn Hpres. apply (K5 a Ha ltac:(lia)). eapply apresent_grows; [exact Hgr|]. exact (T5 a Ha Hn Hpres). }
intros a Ha. destruct (Z_lt_le_dec a (sp - 320)) as [Hlo | Hhi].
- destruct (Z_lt_le_dec a (sp - 320 - ASTACK)) as [Hlo2 | Hhi2].
+
apply (K5 a ltac:(lia) ltac:(lia)). eapply apresent_grows; [exact Hgr|]. apply T6. exact Ha.
+ apply K6. lia.
- apply (K5 a ltac:(lia) ltac:(lia)). eapply apresent_grows; [exact Hgr|]. apply T6. exact Ha.
Qed.
Lemma sep_head_ctx : forall ly1 S1 W1 mem1 md1 p n rest ctx C,
AR SEGS B ly1 S1 W1 mem1 md1 -> Permutation (ablocks B ly1 S1) (tnz ((p, n) :: rest) ++ (ctx, 72) :: C) ->
forall a, ctx <= a < ctx + 72 -> ~ (p <> 0 /\ p <= a < p + req_size n).
Proof.
intros ly1 S1 W1 mem1 md1 p n rest ctx C HAR HB a Ha [Hp Hpa].
rewrite tnz_cons_nz in HB by exact Hp. cbn [app] in HB.
pose proof (sep_blocks_perm SEGS B LAWS _ _ _ _ _ (p, n) (ctx, 72) (tnz rest ++ C) HAR
ltac:(eapply Permutation_trans; [exact HB | apply Permutation_cons; [reflexivity|]; apply Permutation_sym; apply Permutation_middle])) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. change (req_size 72) with 72 in Hd. lia.
Qed.
Definition sr_e2 : list sv :=
[SLit 0; SOff 71 0; SOff 2 (-320); SOff 3 0; SOff 4 0; SOff 72 0; SOff 73 0; SOff 74 0; SOff 8 0; SOff 8 32; SOff 75 0; SOff 76 0; SOff 77 0; SOff 78 0;
SOff 79 0; SOff 80 0; SOff 81 0; SOff 82 0; SOff 8 24; SOff 8 16; SOff 8 8; SOff 21 0; SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 0) (SLit 3)) (SOff 27 0);
SAlu ALU_ADD (SMd M_MULHU (SAlu ALU_ADD (SMd M_MUL (SOff 33 0) (SLit 384)) (SLit 384)) (SLit 72340172838076674)) (SLit 4); SOff 33 1; SOff 25 0;
SOff 59 0; SOff 27 0; SOff 83 0; SOff 84 0; SOff 85 0; SOff 86 0].
Definition ctx_region_e2 : YP09.region :=
YP09.mkRegion (Some 8%nat) 0 72 0 0
[YP09.mkChunk 60 (CVal 4 (SOff 33 1)); YP09.mkChunk 0 (CVal 8 (SOff 37 0)); YP09.mkChunk 8 (CVal 8 (SOff 38 0));
YP09.mkChunk 16 (CVal 8 (SOff 39 0)); YP09.mkChunk 24 (CVal 8 (SOff 40 0)); YP09.mkChunk 32 (CVal 8 (SOff 41 0));
YP09.mkChunk 40 (CVal 8 (SOff 32 0))].
Definition ss_e2 : sstate := mkSS 0x2098 sr_e2 [ctx_region_e2; stk_region_epi] None facts_epi.
Definition ss_e2_c : sstate := Eval vm_compute in ss_e2.
Definition ss_f : sstate := mkSS 0x2124 (sr_set sr_e2 23%bv (SOff 75 0)) [ctx_region_e2; stk_region_epi] None facts_epi.
Definition ss_f_c : sstate := Eval vm_compute in ss_f.
Definition tepi2_inv (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (mdc : Model)
(regs : bvmap 5 word) (pR nP idl icl : Z)
(E : env) (W9 : world SEGS) (ly9 : alayout) (S9 : astate) (mem9 : word -> option byte) (md9 : Model)
(ctx ti lm lc li tm ld lp bl bb Lby Lbb : Z) : Prop :=
ajournal SEGS B LZW_TSTK (spZ regs) [] lyc Sc W memc mdc [] ly9 S9 W9 mem9 md9 9 /\
bv_unsigned (ew E 2) = spZ regs /\ ew E 3 = getr regs 3 /\ ew E 4 = getr regs 4 /\
ew E 8 = w64 ctx /\ ew E 27 = w64 SB /\ ew E 25 = w64 idl /\ ew E 32 = w64 ld /\ ew E 21 = w64 2 /\
ew E 33 = w64 lp /\ ew E 34 = w64 pR /\ ew E 35 = w64 icl /\
ew E 37 = w64 ti /\ ew E 38 = w64 lm /\ ew E 39 = w64 lc /\ ew E 40 = w64 li /\ ew E 41 = w64 tm /\
(forall j, (j < 13)%nat -> ew E (42 + j)%nat = nth j (tsaved_vals regs) (Z_to_bv 64 0)) /\
ew E 59 = w64 bl /\ ew E 75 = w64 bb /\
0 <= lp /\ lp + 1 <= lzw_MR nP idl + nP + 2 /\ Lby = 12 * (lp + 1) / 8 + 3 /\ Lbb = 384 * (lp + 1) / 255 + 4 /\
Permutation (ablocks B ly9 S9) (tnz ((bl, Lby) :: (bb, Lbb) :: lzw_tabs ti lm lc li tm ld nP idl) ++ (ctx, 72) :: ablocks B lyc Sc) /\
tok_inv LZW_TSTK (spZ regs) [] (ablocks B lyc Sc) [] ((ctx, 72) :: tnz ((bl, Lby) :: (bb, Lbb) :: lzw_tabs ti lm lc li tm ld nP idl)) /\
Forall (fun b => fst b <> 0) (lzw_tabs ti lm lc li tm ld nP idl) /\
frames S9 = frames Sc.
Local Ltac saved_facts HSV :=
pose proof (HSV 0%nat ltac:(lia)) as V42; pose proof (HSV 1%nat ltac:(lia)) as V43; pose proof (HSV 2%nat ltac:(lia)) as V44;
pose proof (HSV 3%nat ltac:(lia)) as V45; pose proof (HSV 4%nat ltac:(lia)) as V46; pose proof (HSV 5%nat ltac:(lia)) as V47;
pose proof (HSV 6%nat ltac:(lia)) as V48; pose proof (HSV 7%nat ltac:(lia)) as V49; pose proof (HSV 8%nat ltac:(lia)) as V50;
pose proof (HSV 9%nat ltac:(lia)) as V51; pose proof (HSV 10%nat ltac:(lia)) as V52; pose proof (HSV 11%nat ltac:(lia)) as V53;
pose proof (HSV 12%nat ltac:(lia)) as V54;
cbn [Nat.add nth tsaved_vals map snd TSAVED] in V42, V43, V44, V45, V46, V47, V48, V49, V50, V51, V52, V53, V54.
Local Ltac call_free_g HS HJ9 n casetac Ep AG Usp Egp Etp Rctx Hcceil Hev :=
let Bv := getB in let T := getTL in
let Ra0 := fresh "Ra0" in let Rra := fresh "Rra" in let Rsp := fresh "Rsp" in let Rgp := fresh "Rgp" in
let Rtp := fresh "Rtp" in let Rs0 := fresh "Rs0" in
prreg HS (10%bv : bv 5) Ra0; prreg HS (1%bv : bv 5) Rra; prreg HS (2%bv : bv 5) Rsp; prreg HS (3%bv : bv 5) Rgp;
prreg HS (4%bv : bv 5) Rtp; prreg HS (8%bv : bv 5) Rs0;
pmkst HS; ppcs;
lazymatch type of HJ9 with ajournal _ _ ?STK1 ?sp1 ?FP1 ?lyb ?Sb ?W0 ?memb ?mdb [] ?lyc ?Sc ?Wc (ms_mem ?msX) ?mdc ?kk =>
lazymatch type of Rra with _ = Z_to_bv 64 ?ra =>
lazymatch type of Ep with ew _ ?na = w64 ?p =>
lazymatch type of Rctx with ew _ 8%nat = w64 ?ctxv =>
let Hnev := fresh "Hnev" in pose proof HJ9 as (_ & _ & _ & _ & _ & _ & Hnev & _);
eapply SRr_bind;
[ eapply (tfree_anyo Wc (ms_regs msX) (ms_mem msX) STK1 sp1 FP1 [] lyb Sb W0 memb mdb lyc Sc mdc kk p n (-320) (Z_to_bv 64 ra) ctxv HJ9);
[ first [ casetac | idtac "CF1" ]
| first [ rewrite Ra0, ?(AG na) by lia; rewrite Ep; reflexivity | idtac "CF2" ]
| first [ unfold spZ; rewrite Rsp, ?(AG 2%nat) by lia; rewrite Usp, unsigned_lit_small by lia; lia | idtac "CF3" ]
| first [ reflexivity | idtac "CF4" ]
| first [ lia | idtac "CF5" ]
| first [ unfold LZW_TSTK; lia | idtac "CF6" ]
| first [ rewrite Rgp, ?(AG 3%nat) by lia; exact Egp | idtac "CF7" ]
| first [ rewrite Rtp, ?(AG 4%nat) by lia; exact Etp | idtac "CF8" ]
| first [ exact Rra | idtac "CF9" ]
| first [ apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity] | idtac "CF10" ]
| first [ rewrite unsigned_lit_small by lia; lia | idtac "CF11" ]
| first [ unfold s0Z; rewrite Rs0, ?(AG 8%nat) by lia; rewrite Rctx; apply unsigned_lit_small; lia | idtac "CF12" ]
| first [ clear - Hcceil; lia | idtac "CF13" ]
| first [ match goal with H2 : LZW_EV = 19 |- _ => clear - Hnev Hev H2; lia end | idtac "CF14" ]
| first [ rewrite unsigned_lit_small by lia; pose proof (proj1 (pal_rt_below B TL)); lia | idtac "CF15" ]
| first [ rewrite unsigned_lit_small by lia; hul_tac | idtac "CF16" ] ]
| clear Ra0 Rra Rsp Rgp Rtp Rs0 Hnev ] end end end end.
Local Ltac call_free_e HS HJ9 HB TOK Ep AG Usp Egp Etp Rctx Hcceil Hev :=
lazymatch type of HB with Permutation _ (tnz ((_, ?n) :: _) ++ _) =>
call_free_g HS HJ9 n
ltac:(eapply tfree_pre_case; [exact HB|]; intros b Hb; refine (proj1 (proj2 (proj2 (TOK b _)))); right; repeat (first [exact Hb | apply in_tnz_tl]))
Ep AG Usp Egp Etp Rctx Hcceil Hev end.
Lemma tepi_fail : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP idl icl
E W9 (regs9 : bvmap 5 word) mem9 md9 ly9 S9 ctx ti lm lc li tm ld lp bl bb Lby Lbb,
tlzw_caller B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP idl icl ->
st_ok_pi SEGS VAL E ss_f_c (restrict (w_H W9) (mkst regs9 (Z_to_bv 64 (BASE + 0x2124)) mem9 (seg_rom SEGS))) -> img_env VAL A_LIM E ->
tepi2_inv lyc Sc W memc mdc regs pR nP idl icl E W9 ly9 S9 mem9 md9 ctx ti lm lc li tm ld lp bl bb Lby Lbb ->
(bl = 0 \/ bb = 0) ->
SRr SEGS W9 (mkCfg (mkst regs9 (Z_to_bv 64 (BASE + 0x2124)) mem9 (seg_rom SEGS)) md9)
(tlzw_post SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs pR).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP idl icl E W9 regs9 mem9 md9 ly9 S9 ctx ti lm lc li tm ld lp bl bb Lby Lbb
HC HS HEI (HJ9 & Usp & E3 & E4 & Rctx & E20 & E25 & Rld & E21 & Rlp & RpR & Ricl & Rti & Rlm & Rlc & Rli & Rtm & HSV & Rbl & Rbb &
Hlp0 & Hlpcap & HLby & HLbb & HB9 & TOK9 & Hnz & Hfrs9) Hnull.
pose proof HC as (HJc & Hra0 & Hgp & Htp & Hal16 & Hwlo & Hwhi & HpR8 & HpRside & HpR0 & HpR63 & HpRw & HpRok & HnP & Hidl & Hicl & Hev & Hlive).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (Egp : ew E 3 = Z_to_bv 64 (as_gp B)) by (rewrite E3; exact Hgp). assert (Etp : ew E 4 = Z_to_bv 64 (as_tp B)) by (rewrite E4; exact Htp).
saved_facts HSV. clear HSV.
pose proof HJ9 as (HAR9 & Hly9 & _ & _ & _ & _ & Hnev9 & _ & _ & _ & _ & _ & _ & Hpres9 & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : LZW_TSTK = 336 + ASTACK) by reflexivity.
assert (ASTACK = 16384) as Has by reflexivity. assert (HEV : LZW_EV = 19) by reflexivity.
set (sp := spZ regs) in *.
assert (Hctx9 : In (ctx, 72) (ablocks B ly9 S9)) by (eapply in_cfin; [exact HB9 | left; reflexivity]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ ctx 72 HAR9 Hctx9) as (Hc16 & Hc4096 & Hcceil & Hchigh_ia & Hcpres & _). pose proof (proj1 Hchigh_ia) as Hchigh. change (req_size 72) with 72 in Hcceil, Hcpres.
pose proof (blk_off_imgP _ _ _ _ _ _ ctx 72 HAR9 Hctx9) as Hchigh_img.
assert (Actx : forall blc lyq i, In (ctx, 72) blc -> 0 <= i < 72 -> awr_byte LZW_TSTK sp [] (ablocks B lyc Sc) blc lyq [] (ctx + i)).
{ intros blc lyq i Hb Hi. apply (TOK9 (ctx, 72) ltac:(left; reflexivity)); [exact Hb | cbn [snd]; change (req_size 72) with 72; lia]. }
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
reshok_bx HS 27%nat.
paj_run_tok RUN HS HJ9 SHOK Bspan; [awr_ok_tac |]. clear HF HFr HG.
call_free_e HS HJ9 HB9 TOK9 Rbl AG Usp Egp Etp Rctx Hcceil Hev.
cbv beta. intros W10 c10 Hwle10 (ly10 & S10 & regs10 & mem10 & md10 & -> & HJ10 & HP10 & Hfrs10 & Hpost10 & HK10).
pose proof (tfree_post_step _ _ _ _ _ _ HB9 Hpost10) as HB10.
assert (Hctx10 : In (ctx, 72) (ablocks B ly10 S10)) by (eapply in_cfin; [exact HB10 | left; reflexivity]).
pose proof (sep_head_ctx _ _ _ _ _ _ _ _ _ _ HAR9 HB9) as Hsep9.
reseat HS HJ10 HP10 [0%nat; 1%nat] AG
ltac:(first [ eapply (region_kept_block_aj SEGS B _ _ _ _ _ _ _ _ _ _ 8%nat 0 72 0 0 _ _ 72);
[ exact HK10 | cbn [ew ewset Nat.eqb]; rewrite ?(AG 8%nat) by lia; rewrite Rctx; apply unsigned_lit_small; lia
| exact Hctx9 | lia | change (req_size 72) with 72; lia | lia | intros a Ha; apply Hsep9; lia ]
| eapply (region_kept_high_aj B _ _ _ _ _ _ _ _ _ _ 2%nat); [exact HK10 | cbn [ew ewset Nat.eqb]; rewrite ?(AG 2%nat) by lia; exact Usp | lia | lia | lia]
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
reshok_bx HS 27%nat.
paj_run_tok RUN HS HJ10 SHOK Bspan; [awr_ok_tac |]. clear HF HFr HG.
pose proof HJ10 as (HAR10 & _).
call_free_e HS HJ10 HB10 TOK9 Rbb AG Usp Egp Etp Rctx Hcceil Hev.
cbv beta. intros W11 c11 Hwle11 (ly11 & S11 & regs11 & mem11 & md11 & -> & HJ11 & HP11 & Hfrs11 & Hpost11 & HK11).
pose proof (tfree_post_step _ _ _ _ _ _ HB10 Hpost11) as HB11. pose proof HJ11 as (_ & _ & _ & _ & _ & _ & Hnev11 & _).
assert (Hctx11 : In (ctx, 72) (ablocks B ly11 S11)) by (eapply in_cfin; [exact HB11 | left; reflexivity]).
pose proof (sep_head_ctx _ _ _ _ _ _ _ _ _ _ HAR10 HB10) as Hsep10.
reseat HS HJ11 HP11 [0%nat; 1%nat] AG
ltac:(first [ eapply (region_kept_block_aj SEGS B _ _ _ _ _ _ _ _ _ _ 8%nat 0 72 0 0 _ _ 72);
[ exact HK11 | cbn [ew ewset Nat.eqb]; rewrite ?(AG 8%nat) by lia; rewrite Rctx; apply unsigned_lit_small; lia
| exact Hctx10 | lia | change (req_size 72) with 72; lia | lia | intros a Ha; apply Hsep10; lia ]
| eapply (region_kept_high_aj B _ _ _ _ _ _ _ _ _ _ 2%nat); [exact HK11 | cbn [ew ewset Nat.eqb]; rewrite ?(AG 2%nat) by lia; exact Usp | lia | lia | lia]
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
reshok_bx HS 27%nat.
paj_run_to_tok RUNTO HS HJ11 SHOK Bspan 0x2138; [awr_ok_tac |]. clear HF HFr HG.
prreg HS (2%bv : bv 5) R2; prreg HS (3%bv : bv 5) R3; prreg HS (4%bv : bv 5) R4; prreg HS (8%bv : bv 5) R8; prreg HS (9%bv : bv 5) R9;
prreg HS (18%bv : bv 5) R18; prreg HS (19%bv : bv 5) R19; prreg HS (20%bv : bv 5) R20; prreg HS (21%bv : bv 5) R21;
prreg HS (22%bv : bv 5) R22; prreg HS (1%bv : bv 5) R1; prreg HS (27%bv : bv 5) R27;
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict (w_H ?Wx) ?msx) =>
assert (HFR : tlzw_frame (mrestrict (w_H Wx) (ms_mem msx)) sp regs) by (frame_tac_e HS 1%nat AG) | st_ok _ _ _ (restrict (w_H ?Wx) ?msx) =>
assert (HFR : tlzw_frame (mrestrict (w_H Wx) (ms_mem msx)) sp regs) by (frame_tac_e HS 1%nat AG)  end.
assert (Hrng : forall b, In b (lzw_tabs ti lm lc li tm ld nP idl) -> 0 <= fst b < 2 ^ 64).
{ intros [bp bn] Hb.
assert (Hb' : In (bp, bn) (ablocks B ly11 S11)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB11|]. apply in_app_iff. left. rewrite (tnz_id _ Hnz). exact Hb. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ bp bn (proj1 HJ11) Hb') as (_ & H4096 & Hbc & _ & _ & _ & Hbn).
pose proof (req_size_pos bn ltac:(lia)). cbn [fst]. lia. }
assert (Gti : 0 <= ti < 2 ^ 64) by (apply (Hrng (ti, 2 * idl * idl)); cbv [lzw_tabs In]; tauto).
assert (Glm : 0 <= lm < 2 ^ 64) by (apply (Hrng (lm, 8192)); cbv [lzw_tabs In]; tauto).
assert (Glc : 0 <= lc < 2 ^ 64) by (apply (Hrng (lc, 4096)); cbv [lzw_tabs In]; tauto).
assert (Gli : 0 <= li < 2 ^ 64) by (apply (Hrng (li, 8192)); cbv [lzw_tabs In]; tauto).
assert (Gtm : 0 <= tm < 2 ^ 64) by (apply (Hrng (tm, 4098 * idl)); cbv [lzw_tabs In]; tauto).
assert (Gld : 0 <= ld < 2 ^ 64) by (apply (Hrng (ld, 2 * (lzw_MR nP idl + nP + 2))); cbv [lzw_tabs In]; tauto).
unfold lzw_tabs in HB11, Hrng.
rewrite (st_ok_restrict_mkst SEGS _ _ _ _ HS eq_refl); cbn [ss_pc].
lazymatch type of HJ11 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?msX) ?md11' _ =>
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ _ _) ?mdX) _ =>
eapply SRr_mono;
[ eapply (tlzw_clean B TL LAWS ML AFREE ltac:(pHUL) W11 (ms_regs msX) (ms_mem msX) mdX regs LZW_TSTK sp [] lyc Sc W memc mdc [] ly11 S11 11
ctx ti _ lm _ lc _ li _ tm _ ld _ (ablocks B lyc Sc) 2 HJ11 HB11);
[ first [ intros b Hb; refine (proj1 (proj2 (proj2 (TOK9 b _)))); destruct Hb as [Hb | Hb]; [left; exact Hb | right; apply in_tnz_tl; apply in_tnz_tl; exact Hb] | idtac "BR0" ]
| first [ exact Hrng | idtac "BR1" ]
| first [ ctx_field_n 8%nat HS 0%nat Rctx AG | idtac "BR2" ]
| first [ ctx_field_n 8%nat HS 0%nat Rctx AG | idtac "BR3" ]
| first [ ctx_field_n 8%nat HS 0%nat Rctx AG | idtac "BR4" ]
| first [ ctx_field_n 8%nat HS 0%nat Rctx AG | idtac "BR5" ]
| first [ ctx_field_n 8%nat HS 0%nat Rctx AG | idtac "BR6" ]
| first [ ctx_field_n 8%nat HS 0%nat Rctx AG | idtac "BR7" ]
| first [ exact Hra0 | idtac "BR8" ]
| first [ exact Hal16 | idtac "BR9" ]
| first [ clear - Hwlo; subst sp; lia | idtac "BR10" ]
| first [ lia | idtac "BR11" ]
| first [ exact Hgp | idtac "BR12" ]
| first [ exact Htp | idtac "BR13" ]
| first [ fold sp; unfold spZ; rewrite R2, ?(AG 2%nat) by lia; rewrite Usp, unsigned_lit_small by lia; lia | idtac "BR14" ]
| first [ rewrite R3, ?(AG 3%nat) by lia; exact E3 | idtac "BR15" ]
| first [ rewrite R4, ?(AG 4%nat) by lia; exact E4 | idtac "BR16" ]
| first [ rewrite R8, ?(AG 8%nat) by lia; exact Rctx | idtac "BR17" ]
| first [ rewrite R27, ?(AG 27%nat) by lia; exact E20 | idtac "BR18" ]
| first [ rewrite R21, ?(AG 21%nat) by lia; exact E21 | idtac "BR19" ]
| first [ lia | idtac "BR20" ]
| first [ rewrite R22, ?(AG 8%nat), ?(AG 27%nat) by lia; rewrite Rctx, E20, ?alu64_add0, ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity | match goal with |- ?g => idtac "BR21" g end ]
| first [ rewrite R20, ?(AG 8%nat) by lia; rewrite Rctx, unsigned_lit_small by lia; reflexivity | match goal with |- ?g => idtac "BR22" g end ]
| first [ rewrite R19, ?(AG 8%nat) by lia; rewrite Rctx, unsigned_lit_small by lia; reflexivity | match goal with |- ?g => idtac "BR23" g end ]
| first [ rewrite R18, ?(AG 8%nat) by lia; rewrite Rctx, unsigned_lit_small by lia; reflexivity | match goal with |- ?g => idtac "BR24" g end ]
| first [ rewrite R9, ?(AG 8%nat) by lia; rewrite Rctx, unsigned_lit_small by lia; reflexivity | match goal with |- ?g => idtac "BR25" g end ]
| first [ rewrite R1, ?(AG 8%nat) by lia; rewrite Rctx, unsigned_lit_small by lia; reflexivity | match goal with |- ?g => idtac "BR26" g end ]
| first [ exact HFR | idtac "BR27" ]
| first [ clear - Hnev11 Hev HEV; lia | idtac "BR28" ] ]
| ] end end.
cbv beta. intros W12 c12 _ (ly12 & S12 & regs12 & mem12 & md12 & -> & HJ12 & HP12 & Ha12 & Hfrs12 & HPerm12 & _).
eapply (tlzw_fail_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP idl icl); [exact HC | exact HJ12 | rewrite HEV; lia | exact HP12 | exact Ha12 | left; reflexivity | | exact HPerm12].
rewrite Hfrs12, Hfrs11, Hfrs10. exact Hfrs9.
Qed.
Definition sr_d : list sv :=
[SLit 0; SOff 119 0; SOff 2 (-320); SOff 3 0; SOff 4 0; SOff 120 0; SOff 121 0; SOff 122 0; SOff 8 0; SOff 8 32; SOff 123 0; SOff 124 0; SOff 125 0;
SOff 126 0; SOff 127 0; SOff 128 0; SOff 129 0; SOff 130 0; SOff 8 24; SOff 8 16; SOff 8 8; SOff 107 0;
SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 0) (SLit 3)) (SOff 27 0); SOff 75 0; SOff 33 1; SOff 25 0; SOff 59 0; SOff 27 0; SOff 131 0; SOff 132 0;
SOff 133 0; SOff 134 0].
Definition facts_d : facts :=
mkFacts ((91%nat, mkAF 0 (2^28) 0) :: f_atoms facts_epi) [] (f_alias facts_epi).
Definition ss_d : sstate := mkSS 0x20e8 sr_d [ctx_region_e2; stk_region_epi] None facts_d.
Definition ss_d_c : sstate := Eval vm_compute in ss_d.
Definition tepi4_inv (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (mdc : Model)
(regs : bvmap 5 word) (pR nP idl icl : Z)
(E : env) (W12 : world SEGS) (ly12 : alayout) (S12 : astate) (mem12 : word -> option byte) (md12 : Model)
(ctx ti lm lc li tm ld lp bb Lbb M : Z) : Prop :=
ajournal SEGS B LZW_TSTK (spZ regs) [] lyc Sc W memc mdc [] ly12 S12 W12 mem12 md12 10 /\
bv_unsigned (ew E 2) = spZ regs /\ ew E 3 = getr regs 3 /\ ew E 4 = getr regs 4 /\
ew E 8 = w64 ctx /\ ew E 27 = w64 SB /\ ew E 25 = w64 idl /\ ew E 32 = w64 ld /\
ew E 33 = w64 lp /\ ew E 34 = w64 pR /\ ew E 35 = w64 icl /\
ew E 37 = w64 ti /\ ew E 38 = w64 lm /\ ew E 39 = w64 lc /\ ew E 40 = w64 li /\ ew E 41 = w64 tm /\
(forall j, (j < 13)%nat -> ew E (42 + j)%nat = nth j (tsaved_vals regs) (Z_to_bv 64 0)) /\
ew E 75 = w64 bb /\ ew E 107 = w64 (M - 1) /\
0 <= lp /\ lp + 1 <= lzw_MR nP idl + nP + 2 /\ 1 <= M <= Lbb /\ 4096 <= bb /\
Permutation (ablocks B ly12 S12)
((ld, 2 * (lzw_MR nP idl + nP + 2)) :: (bb, Lbb) :: (ti, 2 * idl * idl) :: (lm, 8192) :: (lc, 4096) :: (li, 8192) :: (tm, 4098 * idl) :: (ctx, 72) :: ablocks B lyc Sc) /\
(forall b, In b ((bb, Lbb) :: (ctx, 72) :: lzw_tabs ti lm lc li tm ld nP idl) -> ~ In b (ablocks B lyc Sc)) /\
Forall (fun b => fst b <> 0) (lzw_tabs ti lm lc li tm ld nP idl) /\
frames S12 = frames Sc.
Lemma tepi_ok : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP idl icl
E W12 (regs12 : bvmap 5 word) mem12 md12 ly12 S12 ctx ti lm lc li tm ld lp bb Lbb M,
tlzw_caller B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP idl icl ->
st_ok_pi SEGS VAL E ss_d_c (restrict (w_H W12) (mkst regs12 (Z_to_bv 64 (BASE + 0x20e8)) mem12 (seg_rom SEGS))) -> img_env VAL A_LIM E ->
tepi4_inv lyc Sc W memc mdc regs pR nP idl icl E W12 ly12 S12 mem12 md12 ctx ti lm lc li tm ld lp bb Lbb M ->
SRr SEGS W12 (mkCfg (mkst regs12 (Z_to_bv 64 (BASE + 0x20e8)) mem12 (seg_rom SEGS)) md12)
(tlzw_post SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs pR).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP idl icl E W12 regs12 mem12 md12 ly12 S12 ctx ti lm lc li tm ld lp bb Lbb M
HC HS HEI (HJ12 & Usp & E3 & E4 & Rctx & E20 & E25 & Rld & Rlp & RpR & Ricl & Rti & Rlm & Rlc & Rli & Rtm & HSV & Rbb & RM &
Hlp0 & Hlpcap & HM & Hbb4096 & HB12 & Hnin & Hnz & Hfrs12).
pose proof HC as (HJc & Hra0 & Hgp & Htp & Hal16 & Hwlo & Hwhi & HpR8 & HpRside & HpR0 & HpR63 & HpRw & HpRok & HnP & Hidl & Hicl & Hev & Hlive).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (Egp : ew E 3 = Z_to_bv 64 (as_gp B)) by (rewrite E3; exact Hgp). assert (Etp : ew E 4 = Z_to_bv 64 (as_tp B)) by (rewrite E4; exact Htp).
saved_facts HSV. clear HSV.
pose proof HJ12 as (HAR12 & Hly12 & _ & _ & _ & _ & Hnev12 & _ & _ & _ & _ & _ & _ & Hpres12 & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof HJc as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgonec & _ & (Hsp0al' & HstkC0 & HceilC & HsloC & HshiC & H47C & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : LZW_TSTK = 336 + ASTACK) by reflexivity.
assert (ASTACK = 16384) as Has by reflexivity. assert (HEV : LZW_EV = 19) by reflexivity.
set (sp := spZ regs) in *.
pose proof (tlzw_pR_high _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC) as HpRh.
assert (Hin12 : forall b, In b ((ld, 2 * (lzw_MR nP idl + nP + 2)) :: (bb, Lbb) :: (ti, 2 * idl * idl) :: (lm, 8192) :: (lc, 4096) :: (li, 8192) :: (tm, 4098 * idl) :: (ctx, 72) :: ablocks B lyc Sc) -> In b (ablocks B ly12 S12))
by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact HB12 | exact Hb]).
assert (Hctx12 : In (ctx, 72) (ablocks B ly12 S12)) by (apply Hin12; do 7 right; left; reflexivity).
assert (Hbb12 : In (bb, Lbb) (ablocks B ly12 S12)) by (apply Hin12; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ ctx 72 HAR12 Hctx12) as (Hc16 & Hc4096 & Hcceil & Hchigh_ia & Hcpres & _). pose proof (proj1 Hchigh_ia) as Hchigh. change (req_size 72) with 72 in Hcceil, Hcpres.
pose proof (blk_off_imgP _ _ _ _ _ _ ctx 72 HAR12 Hctx12) as Hchigh_img.
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb Lbb HAR12 Hbb12) as (Hbb16 & _ & Hbbceil & Hbbhigh_ia & Hbbpres & _ & HLbb0). pose proof (proj1 Hbbhigh_ia) as Hbbhigh.
pose proof (blk_off_imgP _ _ _ _ _ _ bb Lbb HAR12 Hbb12) as Hbbhigh_img.
assert (HMM : MALLOC_MAX = 2 ^ 28) by reflexivity. rewrite HMM in HLbb0.
pose proof (req_size_pos Lbb ltac:(lia)) as HrLbb.
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
pose proof (tlzw_pR_addressable _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC HJ12) as HRA.
assert (HPRS : forall a, pR <= a < pR + 16 -> apresent (w_H W12) mem12 a) by (intros a Ha; exact (tlzw_pR_present _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HC HJ12 Ha)).
assert (HJc12 : ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly12 S12 W12 mem12 md12 (k + 10)).
{ change own with ([] ++ own). eapply (ajournal_sub SEGS B LAWS Hsegs); [exact HJc | exact HJ12 | exact Hwlo | exact Hwhi |].
intros a (r & Hr & _). destruct Hr. }
lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?msX) =>
pose proof (st_ok_pi_add_region E ss (restrict (w_H W12) msX) (YP09.mkRegion (Some 34%nat) 0 16 0 12 []) HS eq_refl) as HS2 | st_ok _ _ ?ss (restrict _ ?msX) =>
pose proof (st_ok_pi_add_region E ss (restrict (w_H W12) msX) (YP09.mkRegion (Some 34%nat) 0 16 0 12 []) HS eq_refl) as HS2  end.
match type of HS2 with ?P -> ?Q -> _ => assert (HP : P); [|assert (HQ : Q); [|specialize (HS2 HP HQ); clear HP HQ]] end.
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict].
rewrite RpR. unfold w64. rewrite unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply HPRS. lia. }
{ unfold ss_d_c. cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite RpR, Rctx, Usp. unfold w64. rewrite !unsigned_lit_small by lia.
split; [|split; [|exact I]].
-
destruct HpRok as [(cid & pos & Hf & HinF & _) | Hstk]; [|lia].
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ ctx 72 cid pos HAR12 Hctx12 ltac:(rewrite Hfrs12; exact Hf)) as Hd.
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. change (req_size 72) with 72 in Hd.
pose proof (HinF pR ltac:(lia)) as [H1 _]. pose proof (HinF (pR + 15) ltac:(lia)) as [_ H2]. unfold frame_rng in H1, H2. cbn [fst snd] in H1, H2.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly12 HARc Hly12) as (_ & Efa & _). rewrite Efa in Hd. lia.
- clear - HpRside HTS Has. lia. }
clear HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2. rename HS2 into HS.
reshok_bx HS 27%nat.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly12 HARc Hly12) as (Eab12 & Efa12 & _).
assert (ApR : forall a, pR <= a < pR + 16 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B ly12 S12) ly12 own a).
{ intros a Ha. apply (awr_byte_ly _ _ _ _ _ lyc ly12 own a Efa12). eapply awr_byte_mono; [exact (proj1 (HpRw a Ha))|].
intros b n Hb _. apply Hin12. do 8 right. exact Hb. }
pose proof (tlzw_pR_bound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC) as HpR47.
pose proof (st_ok_pi_add_fact E _ _ 34%nat (mkAF 4096 (2 ^ 47 - 16) 3) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite RpR; unfold w64; rewrite unsigned_lit_small by lia;
change (2 ^ 3) with 8; split; [lia | split; [exact HpR8 | lia]])) as HS3.
clear HS. rename HS3 into HS. norm_ss HS. reshok_bx HS 27%nat.
paj_run_to_tok RUNTO HS HJc12 SHOK Bspan 0x2138;
[ lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 34 ?c)) ?len =>
first [rewrite (U_atom_off Ex 34 pR c) by (first [eatom AG RpR | lia]) | rewrite (U_atom Ex 34 pR) by (first [eatom AG RpR | lia])];
eapply (obl_of_range SEGS _ _ Ex _ _ len pR 16 HRA); [rewrite (U_atom Ex 27 SB) by (first [eatom AG E20 | unfold SB; lia]); reflexivity | lia | lia] end
| lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 34 ?c)) ?len =>
first [rewrite (U_atom_off Ex 34 pR c) by (first [eatom AG RpR | lia]) | rewrite (U_atom Ex 34 pR) by (first [eatom AG RpR | lia])];
eapply (obl_of_range SEGS _ _ Ex _ _ len pR 16 HRA); [rewrite (U_atom Ex 27 SB) by (first [eatom AG E20 | unfold SB; lia]); reflexivity | lia | lia] end
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat pR);
[ reflexivity | cbn [ew ewset Nat.eqb]; rewrite RpR; apply unsigned_lit_small; lia
| cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply ApR; lia | awr_ok_tac ]
| ].
prreg HS (2%bv : bv 5) R2; prreg HS (3%bv : bv 5) R3; prreg HS (4%bv : bv 5) R4; prreg HS (8%bv : bv 5) R8; prreg HS (9%bv : bv 5) R9;
prreg HS (18%bv : bv 5) R18; prreg HS (19%bv : bv 5) R19; prreg HS (20%bv : bv 5) R20; prreg HS (21%bv : bv 5) R21;
prreg HS (22%bv : bv 5) R22; prreg HS (1%bv : bv 5) R1; prreg HS (27%bv : bv 5) R27;
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict (w_H ?Wx) ?msx) =>
assert (HFR : tlzw_frame (mrestrict (w_H Wx) (ms_mem msx)) sp regs) by (frame_tac_e HS 2%nat AG) | st_ok _ _ _ (restrict (w_H ?Wx) ?msx) =>
assert (HFR : tlzw_frame (mrestrict (w_H Wx) (ms_mem msx)) sp regs) by (frame_tac_e HS 2%nat AG)  end.
assert (Hrng : forall b, In b (lzw_tabs ti lm lc li tm ld nP idl) -> 0 <= fst b < 2 ^ 64).
{ intros [bp bn] Hb.
assert (Hb' : In (bp, bn) (ablocks B ly12 S12)).
{ apply Hin12. cbv [lzw_tabs In] in Hb.
repeat (destruct Hb as [Hb | Hb]; [apply pair_equal_spec in Hb as [<- <-]; cbv [In]; tauto|]). destruct Hb. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ bp bn HAR12 Hb') as (_ & H4096 & Hbc & _ & _ & _ & Hbn).
pose proof (req_size_pos bn ltac:(lia)). cbn [fst]. lia. }
assert (Gti : 0 <= ti < 2 ^ 64) by (apply (Hrng (ti, 2 * idl * idl)); cbv [lzw_tabs In]; tauto).
assert (Glm : 0 <= lm < 2 ^ 64) by (apply (Hrng (lm, 8192)); cbv [lzw_tabs In]; tauto).
assert (Glc : 0 <= lc < 2 ^ 64) by (apply (Hrng (lc, 4096)); cbv [lzw_tabs In]; tauto).
assert (Gli : 0 <= li < 2 ^ 64) by (apply (Hrng (li, 8192)); cbv [lzw_tabs In]; tauto).
assert (Gtm : 0 <= tm < 2 ^ 64) by (apply (Hrng (tm, 4098 * idl)); cbv [lzw_tabs In]; tauto).
assert (Gld : 0 <= ld < 2 ^ 64) by (apply (Hrng (ld, 2 * (lzw_MR nP idl + nP + 2))); cbv [lzw_tabs In]; tauto).
assert (HBc : Permutation (ablocks B ly12 S12) (tnz (lzw_tabs ti lm lc li tm ld nP idl) ++ (ctx, 72) :: (bb, Lbb) :: ablocks B lyc Sc)).
{ rewrite (tnz_id _ Hnz). unfold lzw_tabs. cbn [app]. eapply Permutation_trans; [exact HB12|].
apply perm_skip. apply (@Permutation_cons_app _ _ [(ti, 2 * idl * idl); (lm, 8192); (lc, 4096); (li, 8192); (tm, 4098 * idl); (ctx, 72)] (ablocks B lyc Sc)). apply Permutation_refl. }
unfold lzw_tabs in HBc, Hrng, Hnz.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
assert (VpR : val_mem SEGS (ms_mem msx) (pR + 0) (N.to_nat 8) bb /\ val_mem SEGS (ms_mem msx) (pR + 8) (N.to_nat 4) M);
[ pose proof (st_ok_pi_region_nth Ex ssx msx 0%nat _ HS eq_refl) as HR0; split;
[ eapply (field_of_region Ex _ 34%nat pR _ _ _ _ _ 0 8%N _ bb HR0);
[ cbn [ew ewset Nat.eqb]; rewrite RpR; apply unsigned_lit_small; lia | cbn; repeat (first [left; reflexivity | right])
| cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; first [exact Rbb | match goal with |- ?g => idtac "VPR1" g end]
| cbn; lia | cbn; lia ]
| eapply (field_of_region Ex _ 34%nat pR _ _ _ _ _ 8 4%N _ M HR0);
[ cbn [ew ewset Nat.eqb]; rewrite RpR; apply unsigned_lit_small; lia | cbn; repeat (first [left; reflexivity | right])
| cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?Z_to_bv_bv_unsigned; first [rewrite RM; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia | match goal with |- ?g => idtac "VPR2" g end]
| cbn; lia | cbn; lia ] ]
| ] | st_ok _ ?Ex ?ssx ?msx =>
assert (VpR : val_mem SEGS (ms_mem msx) (pR + 0) (N.to_nat 8) bb /\ val_mem SEGS (ms_mem msx) (pR + 8) (N.to_nat 4) M);
[ pose proof (st_ok_region_nth Ex ssx msx 0%nat _ HS eq_refl) as HR0; split;
[ eapply (field_of_region Ex _ 34%nat pR _ _ _ _ _ 0 8%N _ bb HR0);
[ cbn [ew ewset Nat.eqb]; rewrite RpR; apply unsigned_lit_small; lia | cbn; repeat (first [left; reflexivity | right])
| cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; first [exact Rbb | match goal with |- ?g => idtac "VPR1" g end]
| cbn; lia | cbn; lia ]
| eapply (field_of_region Ex _ 34%nat pR _ _ _ _ _ 8 4%N _ M HR0);
[ cbn [ew ewset Nat.eqb]; rewrite RpR; apply unsigned_lit_small; lia | cbn; repeat (first [left; reflexivity | right])
| cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?Z_to_bv_bv_unsigned; first [rewrite RM; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia | match goal with |- ?g => idtac "VPR2" g end]
| cbn; lia | cbn; lia ] ]
| ]  end.
destruct VpR as [VpR1 VpR2]. rewrite Z.add_0_r in VpR1. change (N.to_nat 8) with 8%nat in VpR1. change (N.to_nat 4) with 4%nat in VpR2.
rewrite (st_ok_restrict_mkst SEGS _ _ _ _ HS eq_refl); cbn [ss_pc].
lazymatch type of HJc12 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?msX) ?mdq _ =>
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ _ _) ?mdX) _ =>
pose proof HJc12 as (_ & _ & _ & _ & _ & _ & Hnevc12 & _);
eapply SRr_mono;
[ eapply (tlzw_clean B TL LAWS ML AFREE ltac:(pHUL) W12 (ms_regs msX) (ms_mem msX) mdX regs STK sp0 FP ly S W0 mem0 md0 own ly12 S12 (k + 10)
ctx ti _ lm _ lc _ li _ tm _ ld _ ((bb, Lbb) :: ablocks B lyc Sc) 0 HJc12 HBc);
[ first [ intros b Hb Hin0 i Hi; destruct b as [bp bn]; cbn [fst snd]; apply (Hgonec bp bn i Hin0); [|exact Hi];
apply Hnin; destruct Hb as [Hb | Hb]; [right; left; exact Hb | right; right; unfold lzw_tabs; unfold tnz in Hb; apply filter_In in Hb; exact (proj1 Hb)] | idtac "BR0" ]
| first [ exact Hrng | idtac "BR1" ]
| first [ ctx_field_n 8%nat HS 1%nat Rctx AG | idtac "BR2" ]
| first [ ctx_field_n 8%nat HS 1%nat Rctx AG | idtac "BR3" ]
| first [ ctx_field_n 8%nat HS 1%nat Rctx AG | idtac "BR4" ]
| first [ ctx_field_n 8%nat HS 1%nat Rctx AG | idtac "BR5" ]
| first [ ctx_field_n 8%nat HS 1%nat Rctx AG | idtac "BR6" ]
| first [ ctx_field_n 8%nat HS 1%nat Rctx AG | idtac "BR7" ]
| first [ exact Hra0 | idtac "BR8" ]
| first [ exact Hal16 | idtac "BR9" ]
| first [ exact Hwlo | idtac "BR10" ]
| first [ exact Hwhi | idtac "BR11" ]
| first [ exact Hgp | idtac "BR12" ]
| first [ exact Htp | idtac "BR13" ]
| first [ fold sp; unfold spZ; rewrite R2, ?(AG 2%nat) by lia; rewrite Usp, unsigned_lit_small by lia; lia | idtac "BR14" ]
| first [ rewrite R3, ?(AG 3%nat) by lia; exact E3 | idtac "BR15" ]
| first [ rewrite R4, ?(AG 4%nat) by lia; exact E4 | idtac "BR16" ]
| first [ rewrite R8, ?(AG 8%nat) by lia; exact Rctx | idtac "BR17" ]
| first [ rewrite R27, ?(AG 27%nat) by lia; exact E20 | idtac "BR18" ]
| first [ rewrite R21; reflexivity | match goal with |- ?g => idtac "BR19" g end ]
| first [ lia | idtac "BR20" ]
| first [ rewrite R22, ?(AG 8%nat), ?(AG 27%nat) by lia; rewrite Rctx, E20, ?alu64_add0, ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity | match goal with |- ?g => idtac "BR21" g end ]
| first [ rewrite R20, ?(AG 8%nat) by lia; rewrite Rctx, unsigned_lit_small by lia; reflexivity | match goal with |- ?g => idtac "BR22" g end ]
| first [ rewrite R19, ?(AG 8%nat) by lia; rewrite Rctx, unsigned_lit_small by lia; reflexivity | match goal with |- ?g => idtac "BR23" g end ]
| first [ rewrite R18, ?(AG 8%nat) by lia; rewrite Rctx, unsigned_lit_small by lia; reflexivity | match goal with |- ?g => idtac "BR24" g end ]
| first [ rewrite R9, ?(AG 8%nat) by lia; rewrite Rctx, unsigned_lit_small by lia; reflexivity | match goal with |- ?g => idtac "BR25" g end ]
| first [ rewrite R1, ?(AG 8%nat) by lia; rewrite Rctx, unsigned_lit_small by lia; reflexivity | match goal with |- ?g => idtac "BR26" g end ]
| first [ exact HFR | idtac "BR27" ]
| first [ clear - Hnevc12 Hnev12 Hev HEV; lia | idtac "BR28" ] ]
| ] end end.
cbv beta. intros W13 c13 _ (ly13 & S13 & regs13 & mem13 & md13 & -> & HJ13 & HP13 & Ha13 & Hfrs13 & HPerm13 & HK13).
assert (HT : forall t, In t ((ctx, 72) :: tnz [(ld, 2 * (lzw_MR nP idl + nP + 2)); (ti, 2 * idl * idl); (lm, 8192); (lc, 4096); (li, 8192); (tm, 4098 * idl)]) ->
In t (ablocks B ly12 S12) /\ (4096 <= fst t /\ (fst t + req_size (snd t) <= 65536 \/ 6270976 <= fst t) /\ (fst t + req_size (snd t) <= 2147446784 \/ 17594333495296 <= fst t)) /\ ~ In t (ablocks B lyc Sc)).
{ intros t Ht.
assert (Ht12 : In t (ablocks B ly12 S12)).
{ eapply Permutation_in; [apply Permutation_sym; exact HBc|]. apply in_app_iff. destruct Ht as [<- | Ht]; [right; left; reflexivity | left; exact Ht]. }
split; [exact Ht12|]. destruct t as [tp tn].
destruct (al_blocks _ _ LAWS _ _ _ _ _ tp tn HAR12 Ht12) as (_ & _ & _ & [Hth Htapp] & _).
pose proof (blk_off_imgP _ _ _ _ _ _ tp tn HAR12 Ht12) as Hth_img.
split; [cbn [fst snd]; unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Htapp, Hth_img; clear - Hth Htapp Hth_img; lia|].
apply Hnin. destruct Ht as [Ht | Ht]; [right; left; exact Ht | right; right; unfold lzw_tabs; unfold tnz in Ht; apply filter_In in Ht; exact (proj1 Ht)]. }
set (E13 := fun a : Z => exists b : Z * Z, In b ((ctx, 72) :: tnz [(ld, 2 * (lzw_MR nP idl + nP + 2)); (ti, 2 * idl * idl); (lm, 8192); (lc, 4096); (li, 8192); (tm, 4098 * idl)]) /\
fst b <= a < fst b + req_size (snd b)) in HK13.
assert (HsepE : forall y i, In y (ablocks B lyc Sc) -> 0 <= i < req_size (snd y) -> ~ E13 (fst y + i)).
{ intros [yp yn] i Hy Hi (t & Ht & Hta). destruct (HT t Ht) as (Ht12 & _ & Htn). destruct t as [tp tn]. cbn [fst snd] in *.
pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ tp tn yp yn HAR12 Ht12 (Hin12 _ ltac:(do 8 right; exact Hy)) ltac:(intros Ety; rewrite Ety in Htn; exact (Htn Hy))) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
assert (HsepF : forall cid pos a, In (cid, pos) (frames Sc) ->
in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8) -> ~ E13 a).
{ intros cid pos a Hf Hzr (t & Ht & Hta). destruct (HT t Ht) as (Ht12 & Hth & _). destruct t as [tp tn]. cbn [fst snd] in *.
destruct Hzr as [Hzr | Hzr].
- pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ tp tn cid pos HAR12 Ht12 ltac:(rewrite Hfrs12; exact Hf)) as Hd.
rewrite Efa12 in Hd. unfold zdisjoint, frame_rng, in_zr in *. cbn [fst snd] in *. lia.
- destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HARc Hf) as (Hf0 & Hfc & Hfh).
destruct (frame_facts B lyc Sc _ cid pos (proj1 HARc) Hf) as (_ & _ & _ & _ & _ & _ & _ & _ & Hb64 & _).
pose proof (shadow_range_below (frame_addr lyc cid pos) (fs_frame_bytes cid) ltac:(lia) ltac:(lia) ltac:(clear - Hfc Hf0 Hb64 C1 C4; lia)).
pose proof (YCbq.shadow_addr_bounds (frame_addr lyc cid pos) ltac:(clear - Hf0 Hfc Hb64 C1 C4; lia)) as [Hs0 Hs1]. unfold kLowMemEnd in Hs0.
unfold in_zr in Hzr. cbn [fst snd] in Hzr. clear - Hzr Hs0 H Hth Hta C3. lia. }
assert (KpR : forall a, pR <= a < pR + 16 -> aview SEGS (w_H W13) mem13 a = aview SEGS (w_H W12) (ms_mem ms) a).
{ intros a Ha. destruct HK13 as (K1 & K2 & K3 & K4 & K5 & K6).
destruct HpRok as [(cid & pos & Hf & HinF & _) | Hstk].
- apply (K4 cid pos a); [rewrite Hfrs12; exact Hf | left; unfold frame_rng; cbn [fst snd]; rewrite Efa12; exact (HinF a Ha) |].
apply (HsepF cid pos a Hf). left. exact (HinF a Ha).
- apply K1; [| clear - Ha HpRside HTS Has; subst sp; lia]. clear - Ha Hstk Hceil HpR47. lia. }
exists ly13, S13, regs13, mem13, md13, 0. split; [reflexivity|].
split; [eapply ajournal_mono_k; [exact HJ13 | rewrite HEV; lia]|].
split; [exact HP13|]. split; [exact Ha13|]. split; [rewrite Hfrs13; exact Hfrs12|].
left. split; [reflexivity|]. exists bb, Lbb, M.
split; [exact HPerm13|]. split; [exact Hbb4096|]. split; [exact HM|].
split.
{ intros blc i Hblc Hi.
destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (bb, Lbb) (ablocks B ly S)) as [Hin0 | Hn0].
- right. left. split; [apply (Hgonec bb Lbb i Hin0); [apply Hnin; left; reflexivity | lia] | exists bb, Lbb; split; [exact Hblc | lia]].
- right. right. left. exists bb, Lbb. split; [exact Hblc|]. split; [exact Hn0 | lia]. }
split; [intros Hin0 i Hi; cbn [fst snd] in Hi |- *; apply (Hgonec bb Lbb i Hin0); [apply Hnin; left; reflexivity | exact Hi]|].
split; [eapply (val_mem_kept SEGS); [intros j Hj; apply KpR; cbn in Hj; lia | exact VpR1]|].
split; [eapply (val_mem_kept SEGS); [intros j Hj; apply KpR; cbn in Hj; lia | exact VpR2]|].
eapply (tlzw_kept_success sp lyc Sc W memc mdc W12 mem12 (ms_mem ms) W13 mem13 ly12 S12 _ pR _ E13 HARc).
- eapply tlzw_kept_of_journal; [exact HJ12 | intros b Hb; apply Hin12; do 8 right; exact Hb].
- intros x Hx. apply HF. intros (rg & Hrg & Hra). cbn in Hrg.
destruct Hrg as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hra; [|lia|lia].
rewrite RpR in Hra. unfold w64 in Hra. rewrite unsigned_lit_small in Hra by lia. apply Hx. lia.
- exact HG.
- subst sp. exact HK13.
- exact (proj1 HJc12).
- intros b Hb. apply Hin12. do 8 right. exact Hb.
- exact Hfrs12.
- exact Efa12.
- intros b m i Hb Hi. split; [| exact (HsepE (b, m) i Hb Hi)].
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HARc Hb) as (_ & _ & Hbceil & _).
destruct HpRok as [(cid & pos & Hf & HinF & _) | Hstk].
+ pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b m cid pos HARc Hb Hf) as Hd.
pose proof (HinF pR ltac:(lia)) as [H1 _]. pose proof (HinF (pR + 15) ltac:(lia)) as [_ H2].
unfold zdisjoint, frame_rng, in_zr in *. cbn [fst snd] in *. lia.
+ lia.
- exact HsepF.
- exact (proj1 (proj2 HpRh)).
- clear - Hceil Hslo. subst sp. lia.
- clear - Hshi H47. subst sp. lia.
Qed.
Local Ltac mem_eq_ro HF :=
lazymatch type of HF with frame_of _ _ ?m0 (ms_mem ?msx) =>
let EQM := fresh "EQM" in
assert (EQM : ms_mem msx = m0)
by (apply functional_extensionality; intros x; apply HF; intros (rg & Hin & Hrg); cbn in Hin;
repeat (destruct Hin as [<-|Hin]; [cbn in Hrg; lia|]); destruct Hin);
rewrite <- EQM in *; clear EQM HF end.
Lemma tlzw_epi2 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP idl icl
E W9 (regs9 : bvmap 5 word) mem9 md9 ly9 S9 ctx ti lm lc li tm ld lp bl bb Lby Lbb,
tlzw_caller B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP idl icl ->
st_ok_pi SEGS VAL E ss_e2_c (restrict (w_H W9) (mkst regs9 (Z_to_bv 64 (BASE + 0x2098)) mem9 (seg_rom SEGS))) -> img_env VAL A_LIM E ->
tepi2_inv lyc Sc W memc mdc regs pR nP idl icl E W9 ly9 S9 mem9 md9 ctx ti lm lc li tm ld lp bl bb Lby Lbb ->
SRr SEGS W9 (mkCfg (mkst regs9 (Z_to_bv 64 (BASE + 0x2098)) mem9 (seg_rom SEGS)) md9)
(tlzw_post SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs pR).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP idl icl E W9 regs9 mem9 md9 ly9 S9 ctx ti lm lc li tm ld lp bl bb Lby Lbb
HC HS HEI HINV.
pose proof HINV as (HJ9 & Usp & E3 & E4 & Rctx & E20 & E25 & Rld & E21 & Rlp & RpR & Ricl & Rti & Rlm & Rlc & Rli & Rtm & HSV & Rbl & Rbb &
Hlp0 & Hlpcap & HLby & HLbb & HB9 & TOK9 & Hnz & Hfrs9).
pose proof HC as (HJc & Hra0 & Hgp & Htp & Hal16 & Hwlo & Hwhi & HpR8 & HpRside & HpR0 & HpR63 & HpRw & HpRok & HnP & Hidl & Hicl & Hev & Hlive).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (Egp : ew E 3 = Z_to_bv 64 (as_gp B)) by (rewrite E3; exact Hgp). assert (Etp : ew E 4 = Z_to_bv 64 (as_tp B)) by (rewrite E4; exact Htp).
saved_facts HSV.
pose proof HJ9 as (HAR9 & Hly9 & _ & _ & _ & _ & Hnev9 & _ & _ & _ & _ & _ & _ & Hpres9 & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : LZW_TSTK = 336 + ASTACK) by reflexivity.
assert (ASTACK = 16384) as Has by reflexivity. assert (HEV : LZW_EV = 19) by reflexivity.
set (sp := spZ regs) in *.
pose proof (maxres_bounds idl nP Hidl ltac:(lia)) as [HMR1 HMR2].
assert (HMRle : 0 <= lzw_MR nP idl <= nP) by (clear - HMR1 HMR2 Hidl HnP; unfold lzw_MR in *; nia).
assert (HMRb : 3838 * lzw_MR nP idl <= nP) by (clear - HMR1 HMR2 Hidl HnP; unfold lzw_MR in *; nia).
assert (Hlp27 : lp + 1 <= 2 ^ 27) by (clear - Hlp0 Hlpcap HMRb HMRle HnP; lia).
assert (Hctx9 : In (ctx, 72) (ablocks B ly9 S9)) by (eapply in_cfin; [exact HB9 | left; reflexivity]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ ctx 72 HAR9 Hctx9) as (Hc16 & Hc4096 & Hcceil & Hchigh_ia & Hcpres & _). pose proof (proj1 Hchigh_ia) as Hchigh. change (req_size 72) with 72 in Hcceil, Hcpres.
pose proof (blk_off_imgP _ _ _ _ _ _ ctx 72 HAR9 Hctx9) as Hchigh_img.
assert (Actx : forall blc lyq i, In (ctx, 72) blc -> 0 <= i < 72 -> awr_byte LZW_TSTK sp [] (ablocks B lyc Sc) blc lyq [] (ctx + i)).
{ intros blc lyq i Hb Hi. apply (TOK9 (ctx, 72) ltac:(left; reflexivity)); [exact Hb | cbn [snd]; change (req_size 72) with 72; lia]. }
assert (Hlive9 : forall p n, p <> 0 -> In (p, n) ((bl, Lby) :: (bb, Lbb) :: lzw_tabs ti lm lc li tm ld nP idl) -> In (p, n) (ablocks B ly9 S9)).
{ intros p n Hp Hin. eapply Permutation_in; [apply Permutation_sym; exact HB9|]. apply in_app_iff. left. apply in_tnz_nz; [exact Hp | exact Hin]. }
assert (Rgbl : 0 <= bl < 2 ^ 64).
{ destruct (Z.eq_dec bl 0) as [-> | Hp]; [lia|].
destruct (al_blocks _ _ LAWS _ _ _ _ _ bl Lby HAR9 (Hlive9 bl Lby Hp ltac:(left; reflexivity))) as (_ & H4096 & Hbc & _ & _ & _ & Hbn).
pose proof (req_size_pos Lby ltac:(lia)). lia. }
assert (Rgbb : 0 <= bb < 2 ^ 64).
{ destruct (Z.eq_dec bb 0) as [-> | Hp]; [lia|].
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb Lbb HAR9 (Hlive9 bb Lbb Hp ltac:(right; left; reflexivity))) as (_ & H4096 & Hbc & _ & _ & _ & Hbn).
pose proof (req_size_pos Lbb ltac:(lia)). lia. }
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
reshok_bx HS 27%nat.
paj_run_tok RUN HS HJ9 SHOK Bspan; [awr_ok_tac |]. mem_eq_ro HF. clear HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
{
paj_run_to_tok RUNTO HS HJ9 SHOK Bspan 0x2124; [awr_ok_tac |]. mem_eq_ro HF. clear HFr HG.
apply st_ok_conds_nil in HS. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts f_atoms f_alias] in HS.
pose proof (st_ok_restrict_mkst SEGS _ _ _ _ HS eq_refl) as Ems. cbn [ss_pc] in Ems. rewrite Ems in HS. rewrite Ems. clear Ems.
rewrite branch_eq_U, (U_atom _ 59 bl), U_SLit in Hc by (first [eatom AG Rbl | lia]). change (zcanon 0) with 0 in Hc.
eapply (tepi_fail STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP idl icl E);
[exact HC | first [exact HS | match type of HS with ?t => idtac "HSMISMATCH" t end] | assumption | unfold tepi2_inv; repeat (split; [eassumption|]); first [eassumption | match goal with |- ?g => idtac "INVLEFT" g end] | left; apply Z.eqb_eq; exact Hc]. }
rewrite branch_eq_U, (U_atom _ 59 bl), U_SLit in Hc by (first [eatom AG Rbl | lia]). change (zcanon 0) with 0 in Hc.
assert (Hbl1 : bl <> 0) by (destruct (Z.eqb_spec bl 0); [discriminate | assumption]). clear Hc.
paj_run_tok RUN HS HJ9 SHOK Bspan; [awr_ok_tac |]. mem_eq_ro HF. clear HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
{
paj_run_to_tok RUNTO HS HJ9 SHOK Bspan 0x2124; [awr_ok_tac |]. mem_eq_ro HF. clear HFr HG.
apply st_ok_conds_nil in HS. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts f_atoms f_alias] in HS.
pose proof (st_ok_restrict_mkst SEGS _ _ _ _ HS eq_refl) as Ems. cbn [ss_pc] in Ems. rewrite Ems in HS. rewrite Ems. clear Ems.
rewrite branch_eq_U, (U_atom _ 75 bb), U_SLit in Hc by (first [eatom AG Rbb | lia]). change (zcanon 0) with 0 in Hc.
eapply (tepi_fail STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP idl icl E);
[exact HC | first [exact HS | match type of HS with ?t => idtac "HSMISMATCH" t end] | assumption | unfold tepi2_inv; repeat (split; [eassumption|]); eassumption | right; apply Z.eqb_eq; exact Hc]. }
rewrite branch_eq_U, (U_atom _ 75 bb), U_SLit in Hc by (first [eatom AG Rbb | lia]). change (zcanon 0) with 0 in Hc.
assert (Hbb1 : bb <> 0) by (destruct (Z.eqb_spec bb 0); [discriminate | assumption]). clear Hc.
pose proof HB9 as HBl. rewrite (tnz_id ((bl, Lby) :: (bb, Lbb) :: lzw_tabs ti lm lc li tm ld nP idl) ltac:(constructor; [exact Hbl1 | constructor; [exact Hbb1 | exact Hnz]])) in HBl.
unfold lzw_tabs in HBl. cbn [app] in HBl.
assert (HBl' : Permutation (ablocks B ly9 S9)
((bl, Lby) :: (ld, 2 * (lzw_MR nP idl + nP + 2)) :: (bb, Lbb) :: (ti, 2 * idl * idl) :: (lm, 8192) :: (lc, 4096) :: (li, 8192) :: (tm, 4098 * idl) :: (ctx, 72) :: ablocks B lyc Sc)).
{ eapply Permutation_trans; [exact HBl|]. apply perm_skip. apply perm_swap. }
assert (Hbl9 : In (bl, Lby) (ablocks B ly9 S9)) by (apply (Hlive9 bl Lby Hbl1); left; reflexivity).
assert (Hbb9 : In (bb, Lbb) (ablocks B ly9 S9)) by (apply (Hlive9 bb Lbb Hbb1); right; left; reflexivity).
assert (Hldb9 : In (ld, 2 * (lzw_MR nP idl + nP + 2)) (ablocks B ly9 S9)) by (eapply in_cfin; [exact HBl' | left; reflexivity] || (eapply Permutation_in; [apply Permutation_sym; exact HBl' | right; left; reflexivity])).
assert (Hnbl : ~ In (bl, Lby) (ablocks B lyc Sc)).
{ intros Hin. destruct (proj1 (proj2 (proj2 (TOK9 (bl, Lby) ltac:(right; apply in_tnz_nz; [exact Hbl1 | left; reflexivity])))) Hin 0) as (r & Hr & _);
[cbn [snd]; pose proof (req_size_pos Lby ltac:(lia)); lia | exact Hr]. }
assert (Hnbb : ~ In (bb, Lbb) (ablocks B lyc Sc)).
{ intros Hin. destruct (proj1 (proj2 (proj2 (TOK9 (bb, Lbb) ltac:(right; apply in_tnz_tl; apply in_tnz_nz; [exact Hbb1 | left; reflexivity])))) Hin 0) as (r & Hr & _);
[cbn [snd]; pose proof (req_size_pos Lbb ltac:(lia)); lia | exact Hr]. }
pose proof (sep_blocks_perm SEGS B LAWS _ _ _ _ _ (bl, Lby) (ctx, 72) _ HAR9
ltac:(eapply Permutation_trans; [exact HBl' | apply perm_skip; apply Permutation_sym;
apply (@Permutation_middle _ [(ld, 2 * (lzw_MR nP idl + nP + 2)); (bb, Lbb); (ti, 2 * idl * idl); (lm, 8192); (lc, 4096); (li, 8192); (tm, 4098 * idl)]
(ablocks B lyc Sc) (ctx, 72))])) as Hsep_bl_ctx.
unfold zdisjoint, block_rng in Hsep_bl_ctx. cbn [fst snd] in Hsep_bl_ctx. change (req_size 72) with 72 in Hsep_bl_ctx.
destruct (al_blocks _ _ LAWS _ _ _ _ _ bl Lby HAR9 Hbl9) as (Hbl16 & Hbl4096 & Hblceil & Hblhigh_ia & Hblpres & _). pose proof (proj1 Hblhigh_ia) as Hblhigh.
pose proof (blk_off_imgP _ _ _ _ _ _ bl Lby HAR9 Hbl9) as Hblhigh_img.
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb Lbb HAR9 Hbb9) as (Hbb16 & Hbb4096 & Hbbceil & Hbbhigh_ia & Hbbpres & _). pose proof (proj1 Hbbhigh_ia) as Hbbhigh.
pose proof (blk_off_imgP _ _ _ _ _ _ bb Lbb HAR9 Hbb9) as Hbbhigh_img.
pose proof (req_size_pos Lby ltac:(lia)) as HrLby. pose proof (req_size_pos Lbb ltac:(lia)) as HrLbb.
paj_run_to_tok RUNTO HS HJ9 SHOK Bspan 0x25ec; try (obl_ctx HJ9 Hctx9 AG Rctx E20); [awr_ok_tac |]. mem_eq_ro HF. clear HFr HG.
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (12%bv : bv 5) Ra2; prreg HS (13%bv : bv 5) Ra3; prreg HS (14%bv : bv 5) Ra4.
prreg HS (1%bv : bv 5) Rra; prreg HS (2%bv : bv 5) Rsp; prreg HS (3%bv : bv 5) Rgp; prreg HS (4%bv : bv 5) Rtp; prreg HS (8%bv : bv 5) Rs0.
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssX _ =>
eapply SRr_bind;
[ eapply (aj_call SEGS B LAWS Hsegs W9 Ex (abs_ss VAL ssX) msX LZW_TSTK sp [] lyc Sc W memc mdc [] ly9 S9 mdX 9 TCBL_STK (ablocks_fp [(bl, Lby)]) 0 (-320)
(ew Ex 2) (Z_to_bv 64 (BASE + 0x20cc)) []
(fun ly2 S2 W2 regs2 mem2 md2 => ly2 = ly9 /\ S2 = S9 /\ W2 = W9 /\ exists ret, getr regs2 10 = w64 ret /\ 0 <= ret /\ 8 * ret <= 12 * (lp + 1)) HS eq_refl HJ9);
[ first [ rewrite Rsp; cbn [sv_denot]; rewrite ?(AG 2%nat) by lia; reflexivity | match goal with |- ?g => idtac "AJ1" g end ]
| first [ reflexivity | idtac "AJ2" ]
| first [ rewrite ?(AG 2%nat) by lia; exact Usp | idtac "AJ3" ]
| first [ reflexivity | idtac "AJ4" ]
| first [ lia | idtac "AJ5" ]
| first [ unfold TCBL_STK; lia | idtac "AJ6" ]
| first [ unfold TCBL_STK; rewrite HTS; lia | idtac "AJ7" ]
| first [ rewrite Rgp, ?(AG 3%nat) by lia; exact Egp | idtac "AJ8" ]
| first [ rewrite Rtp, ?(AG 4%nat) by lia; exact Etp | idtac "AJ9" ]
| first [ exact Rra | idtac "AJ10" ]
| first [ apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity] | idtac "AJ11" ]
| first [ rewrite unsigned_lit_small by lia; lia | idtac "AJ12" ]
| first [ apply achain_low; unfold s0Z; rewrite Rs0, ?(AG 8%nat) by lia; rewrite Rctx, unsigned_lit_small by lia; lia | match goal with |- ?g => idtac "AJ13" g end ]
| first [ intros HPRE; eapply SRr_mono;
[ eapply (pb_cbl B LAWS TL W9 ly9 S9 (ms_regs msX) (ms_mem msX) mdX [] bl Lby ld (2 * (lzw_MR nP idl + nP + 2)) (lp + 1) idl icl
((bb, Lbb) :: (ti, 2 * idl * idl) :: (lm, 8192) :: (lc, 4096) :: (li, 8192) :: (tm, 4098 * idl) :: (ctx, 72) :: ablocks B lyc Sc) HPRE);
[ first [ rewrite Ra0, ?(AG 59%nat) by lia; exact Rbl | idtac "CB1" ]
| first [ rewrite Ra1; unfold w64; f_equal; rewrite Rlp; unfold w64; rewrite unsigned_lit_small by lia; reflexivity | match goal with |- ?g => idtac "CB2" g end ]
| first [ rewrite Ra2, ?(AG 32%nat) by lia; exact Rld | idtac "CB3" ]
| first [ rewrite Ra3, ?(AG 25%nat) by lia; exact E25 | match goal with |- ?g => idtac "CB4" g end ]
| first [ rewrite Ra4; exact Ricl | match goal with |- ?g => idtac "CB5" g end ]
| first [ clear - Hlp0 Hlp27; lia | idtac "CB6" ]
| first [ lia | idtac "CB7" ]
| first [ lia | idtac "CB8" ]
| first [ rewrite HLby; lia | idtac "CB9" ]
| first [ lia | idtac "CB10" ]
| first [ exact HBl' | idtac "CB11" ] ]
| ]
| idtac "AJ14" ]
| first [ intros a (r & Hr & Ha); right; exists bl, Lby; split; [exact Hbl9 | split; [exact Hnbl|]];
cbv [ablocks_fp map fst snd In] in Hr; destruct Hr as [<- | []]; cbn [fst snd] in Ha; exact Ha | match goal with |- ?g => idtac "AJ15" g end ] ]
| ] | st_ok _ ?Ex ?ssX _ =>
eapply SRr_bind;
[ eapply (aj_call SEGS B LAWS Hsegs W9 Ex ssX msX LZW_TSTK sp [] lyc Sc W memc mdc [] ly9 S9 mdX 9 TCBL_STK (ablocks_fp [(bl, Lby)]) 0 (-320)
(ew Ex 2) (Z_to_bv 64 (BASE + 0x20cc)) []
(fun ly2 S2 W2 regs2 mem2 md2 => ly2 = ly9 /\ S2 = S9 /\ W2 = W9 /\ exists ret, getr regs2 10 = w64 ret /\ 0 <= ret /\ 8 * ret <= 12 * (lp + 1)) HS eq_refl HJ9);
[ first [ rewrite Rsp; cbn [sv_denot]; rewrite ?(AG 2%nat) by lia; reflexivity | match goal with |- ?g => idtac "AJ1" g end ]
| first [ reflexivity | idtac "AJ2" ]
| first [ rewrite ?(AG 2%nat) by lia; exact Usp | idtac "AJ3" ]
| first [ reflexivity | idtac "AJ4" ]
| first [ lia | idtac "AJ5" ]
| first [ unfold TCBL_STK; lia | idtac "AJ6" ]
| first [ unfold TCBL_STK; rewrite HTS; lia | idtac "AJ7" ]
| first [ rewrite Rgp, ?(AG 3%nat) by lia; exact Egp | idtac "AJ8" ]
| first [ rewrite Rtp, ?(AG 4%nat) by lia; exact Etp | idtac "AJ9" ]
| first [ exact Rra | idtac "AJ10" ]
| first [ apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity] | idtac "AJ11" ]
| first [ rewrite unsigned_lit_small by lia; lia | idtac "AJ12" ]
| first [ apply achain_low; unfold s0Z; rewrite Rs0, ?(AG 8%nat) by lia; rewrite Rctx, unsigned_lit_small by lia; lia | match goal with |- ?g => idtac "AJ13" g end ]
| first [ intros HPRE; eapply SRr_mono;
[ eapply (pb_cbl B LAWS TL W9 ly9 S9 (ms_regs msX) (ms_mem msX) mdX [] bl Lby ld (2 * (lzw_MR nP idl + nP + 2)) (lp + 1) idl icl
((bb, Lbb) :: (ti, 2 * idl * idl) :: (lm, 8192) :: (lc, 4096) :: (li, 8192) :: (tm, 4098 * idl) :: (ctx, 72) :: ablocks B lyc Sc) HPRE);
[ first [ rewrite Ra0, ?(AG 59%nat) by lia; exact Rbl | idtac "CB1" ]
| first [ rewrite Ra1; unfold w64; f_equal; rewrite Rlp; unfold w64; rewrite unsigned_lit_small by lia; reflexivity | match goal with |- ?g => idtac "CB2" g end ]
| first [ rewrite Ra2, ?(AG 32%nat) by lia; exact Rld | idtac "CB3" ]
| first [ rewrite Ra3, ?(AG 25%nat) by lia; exact E25 | match goal with |- ?g => idtac "CB4" g end ]
| first [ rewrite Ra4; exact Ricl | match goal with |- ?g => idtac "CB5" g end ]
| first [ clear - Hlp0 Hlp27; lia | idtac "CB6" ]
| first [ lia | idtac "CB7" ]
| first [ lia | idtac "CB8" ]
| first [ rewrite HLby; lia | idtac "CB9" ]
| first [ lia | idtac "CB10" ]
| first [ exact HBl' | idtac "CB11" ] ]
| ]
| idtac "AJ14" ]
| first [ intros a (r & Hr & Ha); right; exists bl, Lby; split; [exact Hbl9 | split; [exact Hnbl|]];
cbv [ablocks_fp map fst snd In] in Hr; destruct Hr as [<- | []]; cbn [fst snd] in Ha; exact Ha | match goal with |- ?g => idtac "AJ15" g end ] ]
| ]  end end.
{ cbv beta. intros W10 c10 _ (-> & regs10 & mem10 & md10 & ret & -> & HJcb & HPcb & Hret & Hret0 & Hret1).
exists ly9, S9, regs10, mem10, md10. split; [rewrite Rra; reflexivity|]. split; [exact HJcb|]. split; [exact HPcb|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exists ret. split; [exact Hret | split; [exact Hret0 | exact Hret1]]. }
cbv beta. intros W10 c10 Hwle10 (ly10 & S10 & regs10 & mem10 & md10 & -> & HJ10 & HJcb & HP10 & -> & -> & -> & ret & Hret & Hret0 & Hret1).
clear Ra0 Ra1 Ra2 Ra3 Ra4 Rra Rsp Rgp Rtp Rs0.
reseat HS HJ10 HP10 [0%nat; 1%nat] AG
ltac:(first [ eapply (region_kept_block_sub SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 8%nat 0 72 0 0 _ _ 72);
[ exact HJcb | cbn [ew ewset Nat.eqb]; rewrite ?(AG 8%nat) by lia; rewrite Rctx; apply unsigned_lit_small; lia
| exact Hctx9 | exact Hctx9 | lia | change (req_size 72) with 72; lia | lia
| intros a Ha (r & Hr & Hra); cbv [ablocks_fp map fst snd In] in Hr; destruct Hr as [<- | []]; cbn [fst snd] in Hra; lia ]
| eapply (region_kept_stack_sub SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2%nat);
[ exact HJcb | exact HJ10 | cbn [ew ewset Nat.eqb]; rewrite ?(AG 2%nat) by lia; exact Usp | lia | rewrite HTS; lia | lia | lia | lia ]
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
prreg HS (10%bv : bv 5) Rret. rewrite Hret in Rret. symmetry in Rret.
lazymatch type of Rret with ew ?Ex ?nx = _ =>
pose proof (st_ok_pi_add_fact Ex _ _ nx (mkAF 0 (2 ^ 28) 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Rret; unfold w64; rewrite unsigned_lit_small by lia;
change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. reshok_bx HS 27%nat.
paj_run_to_tok RUNTO HS HJ10 SHOK Bspan 0x28b4; [awr_ok_tac |]. mem_eq_ro HF. clear HFr HG.
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (12%bv : bv 5) Ra2.
prreg HS (1%bv : bv 5) Rra; prreg HS (2%bv : bv 5) Rsp; prreg HS (3%bv : bv 5) Rgp; prreg HS (4%bv : bv 5) Rtp; prreg HS (8%bv : bv 5) Rs0.
pose proof (cbb_len_bounds (ret + 1) ltac:(lia)) as Hcbb1.
pose proof (blb_size_ok (lp + 1) (ret + 1) ltac:(lia) ltac:(lia) ltac:(lia)) as Hcbb2.
assert (HnLby : ret + 1 <= Lby) by (rewrite HLby; pose proof (Z.div_le_lower_bound (12 * (lp + 1)) 8 ret ltac:(lia) ltac:(lia)); lia).
pose proof (sep_blocks_perm SEGS B LAWS _ _ _ _ _ (bb, Lbb) (ctx, 72) _ HAR9
ltac:(eapply Permutation_trans; [exact HBl' | apply Permutation_sym;
apply (@Permutation_cons_app _ _ [(bl, Lby); (ld, 2 * (lzw_MR nP idl + nP + 2))]
((ti, 2 * idl * idl) :: (lm, 8192) :: (lc, 4096) :: (li, 8192) :: (tm, 4098 * idl) :: (ctx, 72) :: ablocks B lyc Sc));
apply (@Permutation_cons_app _ _ [(bl, Lby); (ld, 2 * (lzw_MR nP idl + nP + 2)); (ti, 2 * idl * idl); (lm, 8192); (lc, 4096); (li, 8192); (tm, 4098 * idl)]
(ablocks B lyc Sc)); apply Permutation_refl])) as Hsep_bb_ctx.
unfold zdisjoint, block_rng in Hsep_bb_ctx. cbn [fst snd] in Hsep_bb_ctx. change (req_size 72) with 72 in Hsep_bb_ctx.
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssX _ =>
eapply SRr_bind;
[ eapply (aj_call SEGS B LAWS Hsegs W9 Ex (abs_ss VAL ssX) msX LZW_TSTK sp [] lyc Sc W memc mdc [] ly9 S9 mdX 9 CBB_STK (ablocks_fp [(bb, Lbb)]) 0 (-320)
(ew Ex 2) (Z_to_bv 64 (BASE + 0x20dc)) []
(fun ly2 S2 W2 regs2 mem2 md2 => ly2 = ly9 /\ S2 = S9 /\ W2 = W9 /\ getr regs2 10 = w64 (cbb_len (ret + 1) - 1)) HS eq_refl HJ10);
[ first [ rewrite Rsp; cbn [sv_denot]; rewrite ?(AG 2%nat) by lia; reflexivity | match goal with |- ?g => idtac "AJ1" g end ]
| first [ reflexivity | idtac "AJ2" ]
| first [ rewrite ?(AG 2%nat) by lia; exact Usp | idtac "AJ3" ]
| first [ reflexivity | idtac "AJ4" ]
| first [ lia | idtac "AJ5" ]
| first [ unfold CBB_STK, ESTACK; lia | idtac "AJ6" ]
| first [ unfold CBB_STK, ESTACK; rewrite HTS; lia | idtac "AJ7" ]
| first [ rewrite Rgp, ?(AG 3%nat) by lia; exact Egp | idtac "AJ8" ]
| first [ rewrite Rtp, ?(AG 4%nat) by lia; exact Etp | idtac "AJ9" ]
| first [ exact Rra | idtac "AJ10" ]
| first [ apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity] | idtac "AJ11" ]
| first [ rewrite unsigned_lit_small by lia; lia | idtac "AJ12" ]
| first [ apply achain_low; unfold s0Z; rewrite Rs0, ?(AG 8%nat) by lia; rewrite Rctx, unsigned_lit_small by lia; lia | match goal with |- ?g => idtac "AJ13" g end ]
| first [ intros HPRE; eapply SRr_mono;
[ eapply (pb_cbb B LAWS TL AMEMCPY W9 ly9 S9 (ms_regs msX) (ms_mem msX) mdX [] bl Lby bb Lbb (ret + 1)
((ld, 2 * (lzw_MR nP idl + nP + 2)) :: (ti, 2 * idl * idl) :: (lm, 8192) :: (lc, 4096) :: (li, 8192) :: (tm, 4098 * idl) :: (ctx, 72) :: ablocks B lyc Sc) HPRE);
[ first [ rewrite Ra0, ?(AG 59%nat) by lia; exact Rbl | idtac "CC1" ]
| first [ rewrite Ra1, ?(AG 75%nat) by lia; exact Rbb | idtac "CC2" ]
| first [ rewrite Ra2; unfold w64; f_equal; rewrite Rret; unfold w64; rewrite unsigned_lit_small by lia; reflexivity | match goal with |- ?g => idtac "CC3" g end ]
| first [ lia | idtac "CC4" ]
| first [ exact HnLby | idtac "CC5" ]
| first [ lia | idtac "CC6" ]
| first [ exact HBl | idtac "CC7" ] ]
| ]
| idtac "AJ14" ]
| first [ intros a (r & Hr & Ha); right; exists bb, Lbb; split; [exact Hbb9 | split; [exact Hnbb|]];
cbv [ablocks_fp map fst snd In] in Hr; destruct Hr as [<- | []]; cbn [fst snd] in Ha; exact Ha | match goal with |- ?g => idtac "AJ15" g end ] ]
| ] | st_ok _ ?Ex ?ssX _ =>
eapply SRr_bind;
[ eapply (aj_call SEGS B LAWS Hsegs W9 Ex ssX msX LZW_TSTK sp [] lyc Sc W memc mdc [] ly9 S9 mdX 9 CBB_STK (ablocks_fp [(bb, Lbb)]) 0 (-320)
(ew Ex 2) (Z_to_bv 64 (BASE + 0x20dc)) []
(fun ly2 S2 W2 regs2 mem2 md2 => ly2 = ly9 /\ S2 = S9 /\ W2 = W9 /\ getr regs2 10 = w64 (cbb_len (ret + 1) - 1)) HS eq_refl HJ10);
[ first [ rewrite Rsp; cbn [sv_denot]; rewrite ?(AG 2%nat) by lia; reflexivity | match goal with |- ?g => idtac "AJ1" g end ]
| first [ reflexivity | idtac "AJ2" ]
| first [ rewrite ?(AG 2%nat) by lia; exact Usp | idtac "AJ3" ]
| first [ reflexivity | idtac "AJ4" ]
| first [ lia | idtac "AJ5" ]
| first [ unfold CBB_STK, ESTACK; lia | idtac "AJ6" ]
| first [ unfold CBB_STK, ESTACK; rewrite HTS; lia | idtac "AJ7" ]
| first [ rewrite Rgp, ?(AG 3%nat) by lia; exact Egp | idtac "AJ8" ]
| first [ rewrite Rtp, ?(AG 4%nat) by lia; exact Etp | idtac "AJ9" ]
| first [ exact Rra | idtac "AJ10" ]
| first [ apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity] | idtac "AJ11" ]
| first [ rewrite unsigned_lit_small by lia; lia | idtac "AJ12" ]
| first [ apply achain_low; unfold s0Z; rewrite Rs0, ?(AG 8%nat) by lia; rewrite Rctx, unsigned_lit_small by lia; lia | match goal with |- ?g => idtac "AJ13" g end ]
| first [ intros HPRE; eapply SRr_mono;
[ eapply (pb_cbb B LAWS TL AMEMCPY W9 ly9 S9 (ms_regs msX) (ms_mem msX) mdX [] bl Lby bb Lbb (ret + 1)
((ld, 2 * (lzw_MR nP idl + nP + 2)) :: (ti, 2 * idl * idl) :: (lm, 8192) :: (lc, 4096) :: (li, 8192) :: (tm, 4098 * idl) :: (ctx, 72) :: ablocks B lyc Sc) HPRE);
[ first [ rewrite Ra0, ?(AG 59%nat) by lia; exact Rbl | idtac "CC1" ]
| first [ rewrite Ra1, ?(AG 75%nat) by lia; exact Rbb | idtac "CC2" ]
| first [ rewrite Ra2; unfold w64; f_equal; rewrite Rret; unfold w64; rewrite unsigned_lit_small by lia; reflexivity | match goal with |- ?g => idtac "CC3" g end ]
| first [ lia | idtac "CC4" ]
| first [ exact HnLby | idtac "CC5" ]
| first [ lia | idtac "CC6" ]
| first [ exact HBl | idtac "CC7" ] ]
| ]
| idtac "AJ14" ]
| first [ intros a (r & Hr & Ha); right; exists bb, Lbb; split; [exact Hbb9 | split; [exact Hnbb|]];
cbv [ablocks_fp map fst snd In] in Hr; destruct Hr as [<- | []]; cbn [fst snd] in Ha; exact Ha | match goal with |- ?g => idtac "AJ15" g end ] ]
| ]  end end.
{ cbv beta. intros W11 c11 _ (-> & regs11 & mem11 & md11 & -> & HJcc & HPcc & Ha0).
exists ly9, S9, regs11, mem11, md11. split; [rewrite Rra; reflexivity|]. split; [exact HJcc|]. split; [exact HPcc|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity | exact Ha0]. }
cbv beta. intros W11 c11 Hwle11 (ly11 & S11 & regs11 & mem11 & md11 & -> & HJ11 & HJcc & HP11 & -> & -> & -> & Ha011).
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp Rs0.
reseat HS HJ11 HP11 [0%nat; 1%nat] AG
ltac:(first [ eapply (region_kept_block_sub SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 8%nat 0 72 0 0 _ _ 72);
[ exact HJcc | cbn [ew ewset Nat.eqb]; rewrite ?(AG 8%nat) by lia; rewrite Rctx; apply unsigned_lit_small; lia
| exact Hctx9 | exact Hctx9 | lia | change (req_size 72) with 72; lia | lia
| intros a Ha (r & Hr & Hra); cbv [ablocks_fp map fst snd In] in Hr; destruct Hr as [<- | []]; cbn [fst snd] in Hra; lia ]
| eapply (region_kept_stack_sub SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2%nat);
[ exact HJcc | exact HJ11 | cbn [ew ewset Nat.eqb]; rewrite ?(AG 2%nat) by lia; exact Usp | lia | rewrite HTS; lia | lia | lia | lia ]
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
prreg HS (10%bv : bv 5) RM. rewrite Ha011 in RM. symmetry in RM.
reshok_bx HS 27%nat.
paj_run_tok RUN HS HJ11 SHOK Bspan; [awr_ok_tac |]. mem_eq_ro HF. clear HFr HG.
pose proof HJ11 as (HAR11 & _).
call_free_g HS HJ11 Lby ltac:(right; split; [exact Hbl9 | intros Hin i Hi; exfalso; exact (Hnbl Hin)]) Rbl AG Usp Egp Etp Rctx Hcceil Hev.
cbv beta. intros W12 c12 Hwle12 (ly12 & S12 & regs12 & mem12 & md12 & -> & HJ12 & HP12 & Hfrs12 & Hpost12 & HK12).
destruct Hpost12 as [[Hbl0 _] | (_ & l1 & l2 & El1 & El2)]; [exfalso; exact (Hbl1 Hbl0)|].
assert (HB12 : Permutation (ablocks B ly12 S12)
((ld, 2 * (lzw_MR nP idl + nP + 2)) :: (bb, Lbb) :: (ti, 2 * idl * idl) :: (lm, 8192) :: (lc, 4096) :: (li, 8192) :: (tm, 4098 * idl) :: (ctx, 72) :: ablocks B lyc Sc)).
{ rewrite El2. apply Permutation_sym. apply (@Permutation_cons_app_inv _ _ l1 l2 (bl, Lby)). rewrite <- El1. apply Permutation_sym. exact HBl'. }
assert (Hctx12 : In (ctx, 72) (ablocks B ly12 S12)) by (eapply Permutation_in; [apply Permutation_sym; exact HB12|]; do 7 right; left; reflexivity).
reseat HS HJ12 HP12 [0%nat; 1%nat] AG
ltac:(first [ eapply (region_kept_block_aj SEGS B _ _ _ _ _ _ _ _ _ _ 8%nat 0 72 0 0 _ _ 72);
[ exact HK12 | cbn [ew ewset Nat.eqb]; rewrite ?(AG 8%nat) by lia; rewrite Rctx; apply unsigned_lit_small; lia
| exact Hctx9 | lia | change (req_size 72) with 72; lia | lia | intros a Ha [_ Hba]; lia ]
| eapply (region_kept_high_aj B _ _ _ _ _ _ _ _ _ _ 2%nat); [exact HK12 | cbn [ew ewset Nat.eqb]; rewrite ?(AG 2%nat) by lia; exact Usp | lia | lia | lia]
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
assert (Hnin : forall b, In b ((bb, Lbb) :: (ctx, 72) :: lzw_tabs ti lm lc li tm ld nP idl) -> ~ In b (ablocks B lyc Sc)).
{ intros b Hb Hin.
assert (Hb' : In b ((ctx, 72) :: tnz ((bl, Lby) :: (bb, Lbb) :: lzw_tabs ti lm lc li tm ld nP idl))).
{ destruct Hb as [<- | [<- | Hb]]; [right; apply in_tnz_tl; apply in_tnz_nz; [exact Hbb1 | left; reflexivity] | left; reflexivity |].
right. apply in_tnz_tl. apply in_tnz_tl. destruct b as [bp bn]. apply in_tnz_nz; [| exact Hb].
exact (proj1 (Forall_forall _ _) Hnz _ Hb). }
destruct (TOK9 b Hb') as (_ & Hn0 & Htk & _). destruct (Htk Hin 0 ltac:(pose proof (req_size_pos (snd b) Hn0); lia)) as (r & Hr & _). exact Hr. }
assert (Hfrs12' : frames S12 = frames Sc) by (rewrite Hfrs12; exact Hfrs9).
apply st_ok_conds_nil in HS. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts f_atoms f_alias] in HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
eapply (tepi_ok STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP idl icl Ex _ _ _ _ _ _ ctx ti lm lc li tm ld lp bb Lbb (cbb_len (ret + 1)));
[ exact HC | first [exact HS | match type of HS with ?t => idtac "HSMISMATCH" t end] | assumption
| unfold tepi4_inv;
repeat (split; [ first [ eassumption | rewrite AG by lia; eassumption | lia
| intros j Hj; do 13 (destruct j as [|j]; [cbn [Nat.add nth tsaved_vals map snd TSAVED]; assumption|]); lia
| match goal with |- ?g => idtac "INVLEFT" g end ] |]);
first [ eassumption | match goal with |- ?g => idtac "INVLEFT" g end ] ] | st_ok _ ?Ex _ _ =>
eapply (tepi_ok STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP idl icl Ex _ _ _ _ _ _ ctx ti lm lc li tm ld lp bb Lbb (cbb_len (ret + 1)));
[ exact HC | first [exact HS | match type of HS with ?t => idtac "HSMISMATCH" t end] | assumption
| unfold tepi4_inv;
repeat (split; [ first [ eassumption | rewrite AG by lia; eassumption | lia
| intros j Hj; do 13 (destruct j as [|j]; [cbn [Nat.add nth tsaved_vals map snd TSAVED]; assumption|]); lia
| match goal with |- ?g => idtac "INVLEFT" g end ] |]);
first [ eassumption | match goal with |- ?g => idtac "INVLEFT" g end ] ]  end.
Qed.
Definition tepi_pre (STK sp0 : Z) (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (mdc : Model)
(regs : bvmap 5 word) (pR nP idl icl : Z)
(WE : world SEGS) (lyE : alayout) (SE : astate) (regsE : bvmap 5 word) (memE : word -> option byte) (mdE : Model)
(E : env) (ctx ti lm lc li tm ld lp : Z) : Prop :=
ajournal SEGS B LZW_TSTK (spZ regs) [] lyc Sc W memc mdc [] lyE SE WE memE mdE 7 /\
st_ok_pi SEGS VAL E ss_epi_c (restrict (w_H WE) (mkst regsE (Z_to_bv 64 (BASE + PC_EPI)) memE (seg_rom SEGS))) /\ img_env VAL A_LIM E /\
bv_unsigned (ew E 2) = spZ regs /\ ew E 3 = getr regs 3 /\ ew E 4 = getr regs 4 /\
ew E 8 = w64 ctx /\ ew E 27 = w64 SB /\ ew E 25 = w64 idl /\ ew E 32 = w64 ld /\ ew E 21 = w64 2 /\
ew E 33 = w64 lp /\ ew E 34 = w64 pR /\ ew E 35 = w64 icl /\ ew E 36 = w64 (ld + 2 * lp) /\
ew E 37 = w64 ti /\ ew E 38 = w64 lm /\ ew E 39 = w64 lc /\ ew E 40 = w64 li /\ ew E 41 = w64 tm /\
(forall j, (j < 13)%nat -> ew E (42 + j)%nat = nth j (tsaved_vals regs) (Z_to_bv 64 0)) /\ lzw_rodata_ok (w_H WE) memE /\
0 <= lp /\ lp + 1 <= lzw_MR nP idl + nP + 2 /\
Permutation (ablocks B lyE SE) (lzw_tabs ti lm lc li tm ld nP idl ++ (ctx, 72) :: ablocks B lyc Sc) /\
tok_inv LZW_TSTK (spZ regs) [] (ablocks B lyc Sc) [] ((ctx, 72) :: lzw_tabs ti lm lc li tm ld nP idl) /\
frames SE = frames Sc /\
blocks_bytes SE <= blocks_bytes Sc + (72 + 2 * idl * idl + 8192 + 4096 + 8192 + 4098 * idl + 2 * (lzw_MR nP idl + nP + 2)).
Lemma tlzw_epi : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (pR nP img idl icl bi Li : Z)
WE lyE SE (regsE : bvmap 5 word) memE mdE (E : env) (ctx ti lm lc li tm ld lp : Z),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
YK0s.ret_ok (getr regs 1) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - LZW_TSTK -> spZ regs <= sp0 ->
pR mod 8 = 0 -> (spZ regs <= pR \/ pR + 16 <= spZ regs - LZW_TSTK) -> 0 <= pR -> pR + 16 <= 2 ^ 63 ->
(forall a, pR <= a < pR + 16 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a) ->
tlzw_pR_ok SEGS lyc Sc W memc pR ->
1 <= nP <= 100000000 -> 2 <= idl <= 256 -> 0 <= icl <= 12 ->
st_nev Sc + LZW_EV <= EV_MAX -> blocks_bytes Sc + 2 ^ 29 <= LIVE_MAX ->
tepi_pre STK sp0 lyc Sc W memc mdc regs pR nP idl icl WE lyE SE regsE memE mdE E ctx ti lm lc li tm ld lp ->
SRr SEGS WE (mkCfg (mkst regsE (Z_to_bv 64 (BASE + PC_EPI)) memE (seg_rom SEGS)) mdE)
(tlzw_post SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs pR).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP img idl icl bi Li WE lyE SE regsE memE mdE E ctx ti lm lc li tm ld lp
HJc Hra0 Hgp Htp Hal16 Hwlo Hwhi HpR8 HpRside HpR0 HpR63 HpRw HpRok HnP Hidl Hicl Hev Hlive
(HJ & HS & HEI & Usp & E3 & E4 & Rctx & E32 & E25 & Rld & E21 & Rlp & RpR & Ricl & Rend & Rti & Rlm & Rlc & Rli & Rtm &
HSV & Hrod & Hlp0 & Hlpcap & HB & TOK & Hfrs & HBB).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (HSV 0%nat ltac:(lia)) as V42. pose proof (HSV 1%nat ltac:(lia)) as V43. pose proof (HSV 2%nat ltac:(lia)) as V44.
pose proof (HSV 3%nat ltac:(lia)) as V45. pose proof (HSV 4%nat ltac:(lia)) as V46. pose proof (HSV 5%nat ltac:(lia)) as V47.
pose proof (HSV 6%nat ltac:(lia)) as V48. pose proof (HSV 7%nat ltac:(lia)) as V49. pose proof (HSV 8%nat ltac:(lia)) as V50.
pose proof (HSV 9%nat ltac:(lia)) as V51. pose proof (HSV 10%nat ltac:(lia)) as V52. pose proof (HSV 11%nat ltac:(lia)) as V53.
pose proof (HSV 12%nat ltac:(lia)) as V54.
cbn [Nat.add nth tsaved_vals map snd TSAVED] in V42, V43, V44, V45, V46, V47, V48, V49, V50, V51, V52, V53, V54. clear HSV.
assert (Egp : ew E 3 = Z_to_bv 64 (as_gp B)) by (rewrite E3; exact Hgp). assert (Etp : ew E 4 = Z_to_bv 64 (as_tp B)) by (rewrite E4; exact Htp).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & Hnev & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : LZW_TSTK = 336 + ASTACK) by reflexivity.
assert (ASTACK = 16384) as Has by reflexivity. assert (HEV : LZW_EV = 19) by reflexivity. assert (HMM : MALLOC_MAX = 2 ^ 28) by reflexivity.
pose proof (maxres_bounds idl nP Hidl ltac:(lia)) as [HMR1 HMR2].
assert (HMRle : 0 <= lzw_MR nP idl <= nP) by (clear - HMR1 HMR2 Hidl HnP; unfold lzw_MR in *; nia).
assert (HMRb : 3838 * lzw_MR nP idl <= nP) by (clear - HMR1 HMR2 Hidl HnP; unfold lzw_MR in *; nia).
assert (Htisz : 8 <= 2 * idl * idl <= 131072) by (clear - Hidl; nia).
set (sp := spZ regs) in *.
assert (Hom : (sp - 320 - sp) mod 16 = 0) by (replace (sp - 320 - sp) with ((-20) * 16) by lia; apply Z_mod_mult).
assert (Hin : forall b, In b (lzw_tabs ti lm lc li tm ld nP idl ++ (ctx, 72) :: ablocks B lyc Sc) -> In b (ablocks B lyE SE))
by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact HB | exact Hb]).
assert (Hctx : In (ctx, 72) (ablocks B lyE SE)) by (apply Hin; apply in_app_iff; right; left; reflexivity).
assert (Hldb : In (ld, 2 * (lzw_MR nP idl + nP + 2)) (ablocks B lyE SE)) by (apply Hin; apply in_app_iff; left; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ ctx 72 HAR Hctx) as (Hc16 & Hc4096 & Hcceil & Hchigh_ia & Hcpres & _). pose proof (proj1 Hchigh_ia) as Hchigh. change (req_size 72) with 72 in Hcceil, Hcpres.
pose proof (blk_off_imgP _ _ _ _ _ _ ctx 72 HAR Hctx) as Hchigh_img.
destruct (al_blocks _ _ LAWS _ _ _ _ _ ld _ HAR Hldb) as (Hld16 & Hld4096 & Hldceil & Hldhigh_ia & Hldpres & _). pose proof (proj1 Hldhigh_ia) as Hldhigh.
pose proof (blk_off_imgP _ _ _ _ _ _ ld _ HAR Hldb) as Hldhigh_img.
pose proof (req_size_pos' (2 * (lzw_MR nP idl + nP + 2)) ltac:(lia)) as Hrqld.
assert (Actx : forall blc lyq i, In (ctx, 72) blc -> 0 <= i < 72 -> awr_byte LZW_TSTK sp [] (ablocks B lyc Sc) blc lyq [] (ctx + i)).
{ intros blc lyq i Hb Hi. apply (TOK (ctx, 72) ltac:(left; reflexivity)); [exact Hb | cbn [snd]; change (req_size 72) with 72; lia]. }
assert (Ald : forall blc lyq i, In (ld, 2 * (lzw_MR nP idl + nP + 2)) blc -> 0 <= i < req_size (2 * (lzw_MR nP idl + nP + 2)) ->
awr_byte LZW_TSTK sp [] (ablocks B lyc Sc) blc lyq [] (ld + i)).
{ intros blc lyq i Hb Hi. apply (TOK (ld, _) ltac:(right; left; reflexivity)); [exact Hb | exact Hi]. }
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
reshok_bx HS 27%nat.
Local Ltac awr_epi Actx Hctx Ald Hldb Rctx Rend AG Usp :=
lazymatch type of Rctx with _ = w64 ?ctxv => lazymatch type of Rend with _ = w64 (?ldv + ?o2) =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ _ ctxv); [reflexivity | cbn [ew ewset Nat.eqb]; rewrite Rctx; apply unsigned_lit_small; lia
| cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; replace a with (ctxv + (a - ctxv)) by lia; apply Actx; [exact Hctx | lia] |];
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0);
[reflexivity | cbn [ew ewset Nat.eqb]; rewrite ?(AG 2%nat) by lia; rewrite Usp; lia | cbn; lia | cbn; lia |];
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ _ (ldv + o2)); [reflexivity | cbn [ew ewset Nat.eqb]; rewrite Rend; apply unsigned_lit_small; lia
| cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; replace a with (ldv + (a - ldv)) by lia; apply Ald; [exact Hldb | lia] |];
awr_ok_tac end end.
paj_run_tok RUN HS HJ SHOK Bspan; try (obl_blk HJ Hldb Rend E32 AG); try (obl_ctx HJ Hctx AG Rctx E32); [awr_epi Actx Hctx Ald Hldb Rctx Rend AG Usp |].
clear HF HFr HG.
set (Lby := 12 * (lp + 1) / 8 + 3) in *. set (Lbb := 384 * (lp + 1) / 255 + 4) in *.
assert (HLby : 0 <= 12 * (lp + 1) / 8 /\ 8 * (12 * (lp + 1) / 8) <= 12 * (lp + 1)) by (clear - Hlp0; split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
assert (HLbb : 0 <= 384 * (lp + 1) / 255 /\ 255 * (384 * (lp + 1) / 255) <= 384 * (lp + 1)) by (clear - Hlp0; split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
assert (Hlp27 : lp + 1 <= 2 ^ 27) by (clear - Hlp0 Hlpcap HMRb HMRle HnP; lia).
rregU HS (10%bv : bv 5) Lby ltac:(unfold Lby; apply (U_blB _ 33 lp); [eatom AG Rlp | exact Hlp0 | exact Hlp27]) Ra0.
assert (HSZ : (0 <= Lby < MALLOC_MAX /\ blocks_bytes SE + Lby <= LIVE_MAX) /\ (0 <= Lbb < MALLOC_MAX /\ blocks_bytes SE + Lby + Lbb <= LIVE_MAX))
by (clear - HMM HBB Hlive Htisz Hidl HnP HMRb HMRle HLby HLbb Hlp0 Hlpcap; subst Lby Lbb; rewrite HMM; unfold LIVE_MAX in *; lia).
destruct HSZ as [HSZ8 HSZ9].
malloc_site_e HS HJ Lby ltac:(exact Ra0) AG Usp Rctx Hom HSZ8. clear Ra0.
cbv beta. intros W8 c8 Hwle8 (ly8 & S8 & regs8 & mem8 & md8 & bl & -> & HJ8 & HP8 & Ha08 & Hfrs8 & Hres8).
assert (HBB8 : blocks_bytes S8 <= blocks_bytes SE + Lby) by (exact (blocks_bytes_after_malloc B _ _ _ _ _ _ _ _ Hres8 ltac:(lia))).
destruct (mres_kept B _ _ _ _ _ _ _ _ _ _ _ _ Hres8) as (HK8 & Hsub8 & Hbl_in).
pose proof (mres_range B LAWS _ _ _ _ _ _ _ _ _ _ _ (proj1 HJ8) Hres8) as Hrr8.
assert (Hctx8 : In (ctx, 72) (ablocks B ly8 S8)) by (apply Hsub8; exact Hctx).
assert (Hldb8 : In (ld, 2 * (lzw_MR nP idl + nP + 2)) (ablocks B ly8 S8)) by (apply Hsub8; exact Hldb).
assert (Tbl : bl <> 0 -> aftok [] (ablocks B lyc Sc) (bl, Lby) /\
forall blc lyq i, In (bl, Lby) blc -> 0 <= i < req_size Lby -> awr_byte LZW_TSTK sp [] (ablocks B lyc Sc) blc lyq [] (bl + i)).
{ intros Hnz. destruct Hres8 as [(Hz0 & _ & _) | (_ & Ebl & _)]; [lia|].
split; [exact (aftok_new_block SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bl _ HJ (proj1 HJ8) Ebl ltac:(lia))|].
intros blc lyq i Hb Hi. exact (awr_new_block SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bl _ blc i lyq HJ (proj1 HJ8) Ebl ltac:(lia) Hb Hi). }
reseat HS HJ8 HP8 [0%nat; 1%nat] AG ltac:(first [ kept_malloc HK8 HJ8 AG Usp | kept_ctx_e HK8 HJ8 Hctx8 Hctx Rctx AG Hres8 ]).
prreg HS (10%bv : bv 5) Rbl. rewrite Ha08 in Rbl. symmetry in Rbl.
reshok_bx HS 27%nat.
paj_run_tok RUN HS HJ8 SHOK Bspan; [awr2e Actx Hctx8 AG Rctx Usp |]. clear HF HFr HG.
rregU HS (10%bv : bv 5) Lbb ltac:(unfold Lbb; rewrite U_add0; apply (U_bbB _ 33 lp); [eatom AG Rlp | exact Hlp0 | exact Hlp27]) Ra0.
assert (HSZ9' : 0 <= Lbb < MALLOC_MAX /\ blocks_bytes S8 + Lbb <= LIVE_MAX) by (clear - HSZ9 HBB8; lia).
malloc_site_e HS HJ8 Lbb ltac:(exact Ra0) AG Usp Rctx Hom HSZ9'. clear Ra0.
cbv beta. intros W9 c9 Hwle9 (ly9 & S9 & regs9 & mem9 & md9 & bb & -> & HJ9 & HP9 & Ha09 & Hfrs9 & Hres9).
assert (HBB9 : blocks_bytes S9 <= blocks_bytes S8 + Lbb) by (exact (blocks_bytes_after_malloc B _ _ _ _ _ _ _ _ Hres9 ltac:(lia))).
destruct (mres_kept B _ _ _ _ _ _ _ _ _ _ _ _ Hres9) as (HK9 & Hsub9 & Hbb_in).
pose proof (mres_range B LAWS _ _ _ _ _ _ _ _ _ _ _ (proj1 HJ9) Hres9) as Hrr9.
assert (Hctx9 : In (ctx, 72) (ablocks B ly9 S9)) by (apply Hsub9; exact Hctx8).
assert (Hldb9 : In (ld, 2 * (lzw_MR nP idl + nP + 2)) (ablocks B ly9 S9)) by (apply Hsub9; exact Hldb8).
assert (Tbb : bb <> 0 -> aftok [] (ablocks B lyc Sc) (bb, Lbb) /\
forall blc lyq i, In (bb, Lbb) blc -> 0 <= i < req_size Lbb -> awr_byte LZW_TSTK sp [] (ablocks B lyc Sc) blc lyq [] (bb + i)).
{ intros Hnz. destruct Hres9 as [(Hz0 & _ & _) | (_ & Ebl & _)]; [lia|].
split; [exact (aftok_new_block SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bb _ HJ8 (proj1 HJ9) Ebl ltac:(lia))|].
intros blc lyq i Hb Hi. exact (awr_new_block SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bb _ blc i lyq HJ8 (proj1 HJ9) Ebl ltac:(lia) Hb Hi). }
reseat HS HJ9 HP9 [0%nat; 1%nat] AG ltac:(first [ kept_malloc HK9 HJ9 AG Usp | kept_ctx_e HK9 HJ9 Hctx9 Hctx8 Rctx AG Hres9 ]).
prreg HS (10%bv : bv 5) Rbb. rewrite Ha09 in Rbb. symmetry in Rbb.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ss ?msx =>
pose proof (st_ok_pi_submem Ex ss msx [ctx_region_e2; stk_region_epi] HS
ltac:(apply submem_keep; [| apply submem_keep; [apply subregion_refl | apply submem_nil]];
unfold subregion; cbn; split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [left; lia | intros c Hc; exact Hc])
ltac:(vm_compute; reflexivity)) as HS3 | st_ok _ ?Ex ?ss ?msx =>
pose proof (st_ok_submem SEGS Ex ss msx [ctx_region_e2; stk_region_epi] HS
ltac:(apply submem_keep; [| apply submem_keep; [apply subregion_refl | apply submem_nil]];
unfold subregion; cbn; split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [left; lia | intros c Hc; exact Hc])
ltac:(vm_compute; reflexivity)) as HS3  end.
clear HS. rename HS3 into HS.
assert (Hnz : Forall (fun b => fst b <> 0) (lzw_tabs ti lm lc li tm ld nP idl)).
{ unfold lzw_tabs. repeat (constructor; [cbn [fst];
lazymatch goal with |- ?p <> 0 =>
let Hb := fresh in
assert (Hb : exists n, In (p, n) (ablocks B lyE SE)) by (eexists; apply Hin; apply in_app_iff; left; cbv [lzw_tabs In]; tauto);
destruct Hb as [nb Hb]; destruct (al_blocks _ _ LAWS _ _ _ _ _ p nb HAR Hb) as (_ & H4096' & _); lia end |]). constructor. }
assert (HB0 : Permutation (ablocks B lyE SE) (tnz ([] ++ (0, Lby) :: (0, Lbb) :: lzw_tabs ti lm lc li tm ld nP idl) ++ (ctx, 72) :: ablocks B lyc Sc)).
{ cbn [app]. rewrite !tnz_cons0, (tnz_id _ Hnz). exact HB. }
pose proof (perm_tab_update _ _ _ [] _ bl Lby _ _ HB0 Hres8) as HB8.
pose proof (perm_tab_update _ _ _ [(bl, Lby)] _ bb Lbb _ _ HB8 Hres9) as HB9. cbn [app] in HB9.
assert (TOK9 : tok_inv LZW_TSTK sp [] (ablocks B lyc Sc) [] ((ctx, 72) :: tnz ((bl, Lby) :: (bb, Lbb) :: lzw_tabs ti lm lc li tm ld nP idl))).
{ intros b [<- | Hb]; [apply TOK; left; reflexivity|].
rewrite tnz_cons in Hb. apply in_app_iff in Hb as [Hb | Hb].
{ unfold optb in Hb. destruct (Z.eqb_spec bl 0) as [Hz | Hz]; [destruct Hb|]. destruct Hb as [<- | []]. cbn [fst snd].
destruct (Tbl Hz) as [T1 T2]. destruct Hrr8 as [H0 | (H4096b & _)]; [lia|]. split; [exact H4096b|]. split; [lia|]. split; [exact T1 | exact T2]. }
rewrite tnz_cons in Hb. apply in_app_iff in Hb as [Hb | Hb].
{ unfold optb in Hb. destruct (Z.eqb_spec bb 0) as [Hz | Hz]; [destruct Hb|]. destruct Hb as [<- | []]. cbn [fst snd].
destruct (Tbb Hz) as [T1 T2]. destruct Hrr9 as [H0 | (H4096b & _)]; [lia|]. split; [exact H4096b|]. split; [lia|]. split; [exact T1 | exact T2]. }
apply TOK. right. rewrite (tnz_id _ Hnz) in Hb. exact Hb. }
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
eapply (tlzw_epi2 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP idl icl Ex _ _ _ _ _ _ ctx ti lm lc li tm ld lp bl bb Lby Lbb);
[ red; repeat (split; [assumption|]); assumption
| first [exact HS | match type of HS with ?t => idtac "HSMISMATCH" t end] | assumption
| unfold tepi2_inv;
repeat (split; [ first [ eassumption | rewrite AG by lia; eassumption | lia | subst Lby; reflexivity | subst Lbb; reflexivity
| intros j Hj; do 13 (destruct j as [|j]; [cbn [Nat.add nth tsaved_vals map snd TSAVED]; assumption|]); lia
| match goal with |- ?g => idtac "INVLEFT" g end ] |]);
first [ eassumption | rewrite Hfrs9, Hfrs8; exact Hfrs | match goal with |- ?g => idtac "INVLEFT" g end ] ] | st_ok _ ?Ex _ _ =>
eapply (tlzw_epi2 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP idl icl Ex _ _ _ _ _ _ ctx ti lm lc li tm ld lp bl bb Lby Lbb);
[ red; repeat (split; [assumption|]); assumption
| first [exact HS | match type of HS with ?t => idtac "HSMISMATCH" t end] | assumption
| unfold tepi2_inv;
repeat (split; [ first [ eassumption | rewrite AG by lia; eassumption | lia | subst Lby; reflexivity | subst Lbb; reflexivity
| intros j Hj; do 13 (destruct j as [|j]; [cbn [Nat.add nth tsaved_vals map snd TSAVED]; assumption|]); lia
| match goal with |- ?g => idtac "INVLEFT" g end ] |]);
first [ eassumption | rewrite Hfrs9, Hfrs8; exact Hfrs | match goal with |- ?g => idtac "INVLEFT" g end ] ]  end.
Qed.
End f.
End e.
End d.
