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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCbw.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC81 YC4b.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a AC93 AC9g AC95 AC91.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition PC_EMITC : Z := 0x1b08.
Definition PC_TIMISS : Z := 0x198c.
Definition PC_ISET : Z := 0x1820.
Definition PC_INNER : Z := 0x1848.
Definition acx_blk (bl : list (Z * Z)) (cx : lzw_acx) : Prop :=
In (z_ctx cx, 72) bl /\ In (z_bi cx, z_Li cx) bl /\ forall b, In b (acx_tabs cx) -> In b bl.
Definition afix_shape (sr : list sv) : bool :=
sv_eqb (sr_get sr 2%bv) (SOff 2 0) && sv_eqb (sr_get sr 8%bv) (SOff 8 0) && sv_eqb (sr_get sr 9%bv) (SOff 8 32) &&
sv_eqb (sr_get sr 18%bv) (SOff 8 24) && sv_eqb (sr_get sr 19%bv) (SOff 8 16) && sv_eqb (sr_get sr 20%bv) (SOff 8 8) &&
sv_eqb (sr_get sr 21%bv) (SOff 21 0) && sv_eqb (sr_get sr 22%bv) (shx 0) && sv_eqb (sr_get sr 25%bv) (SOff 25 0) &&
sv_eqb (sr_get sr 26%bv) (shx 8) && sv_eqb (sr_get sr 27%bv) (SOff 27 0) && sv_eqb (sr_get sr 1%bv) (SOff 8 40) &&
sv_eqb (sr_get sr 3%bv) (SOff 3 0) && sv_eqb (sr_get sr 4%bv) (SOff 4 0).
Lemma alzw_regs_fix_after : forall E E' ss ms regs ext cx,
st_ok_pi SEGS VAL E' ss ms -> afix_shape (ss_regs ss) = true ->
(forall n, (n < 32)%nat -> ew E' n = ew E n) -> E = Eimg (Ereg regs ext) ->
alzw_regs_core regs cx -> 0 <= z_ctx cx -> z_ctx cx + 72 <= 2 ^ 64 ->
alzw_regs_fix (ms_regs ms) cx.
Proof.
intros E E' ss ms regs ext cx HS Hsh AG HE HF Hc0 Hc1.
unfold afix_shape in Hsh. repeat (apply andb_prop in Hsh as [Hsh ?]).
pose proof HF as (Gsp & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G25 & G26 & G27 & G1 & G3 & G4).
assert (R : forall (r : bv 5) e, sv_eqb (sr_get (ss_regs ss) r) e = true -> getr (ms_regs ms) r = sv_denot E' e).
{ intros r e Hr. rewrite (st_ok_pi_reg E' ss ms r HS). apply sv_eqb_denot. exact Hr. }
assert (A : forall (r : bv 5) n, Z.of_nat n = bv_unsigned r -> (n < 32)%nat -> sv_denot E' (SOff n 0) = getr regs r).
{ intros r n Hn Hlt. cbn [sv_denot]. rewrite (AG n Hlt), HE, Z.add_0_r, Z_to_bv_bv_unsigned. apply ew_Eimg_Ereg_nat. exact Hn. }
assert (E8 : ew E' 8 = w64 (z_ctx cx)) by (rewrite (AG 8%nat) by lia; rewrite HE, Eimg_low, (ew_Ereg_nat regs ext 8 8%bv eq_refl) by (unfold A_TEXT; lia); exact G8).
assert (E27 : ew E' 27 = w64 SB) by (rewrite (AG 27%nat) by lia; rewrite HE, Eimg_low, (ew_Ereg_nat regs ext 27 27%bv eq_refl) by (unfold A_TEXT; lia); exact G27).
unfold alzw_regs_fix, spZ.
repeat match goal with |- _ /\ _ => split end;
lazymatch goal with
| |- bv_unsigned (getr _ ?r) = _ => let n := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
rewrite (R r _ ltac:(eassumption)), (A r n eq_refl ltac:(lia)); exact Gsp
| |- getr _ 22%bv = _ => rewrite (R 22%bv _ ltac:(eassumption)); unfold shx; cbn [sv_denot]; rewrite E8, E27; unfold w64;
rewrite !unsigned_lit_small by (unfold SB; lia); rewrite !Z.add_0_r; exact eq_refl
| |- getr _ 26%bv = _ => rewrite (R 26%bv _ ltac:(eassumption)); unfold shx; cbn [sv_denot]; rewrite E8, E27; unfold w64;
rewrite !unsigned_lit_small by (unfold SB; lia); exact eq_refl
| |- getr _ ?r = w64 (z_ctx _ + _) => rewrite (R r _ ltac:(eassumption)); cbn [sv_denot]; rewrite E8; unfold w64; rewrite unsigned_lit_small by lia; reflexivity
| |- getr _ ?r = _ => let n := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
rewrite (R r _ ltac:(eassumption)), (A r n eq_refl ltac:(lia)); assumption
end.
Qed.
Inductive thead_out := THO_eidx | THO_emitc (q : Z) | THO_timiss (c1 c2 : Z) | THO_inner (q : Z).
Definition tho_pc (o : thead_out) : Z :=
match o with THO_eidx => PC_EIDX | THO_emitc _ => PC_EMITC | THO_timiss _ _ => PC_TIMISS | THO_inner _ => PC_ISET end.
Definition tho_post (cx : lzw_acx) (X : lzw_abs) (m : word -> option byte) (regs' : bvmap 5 word) (o : thead_out) : Prop :=
let nP := z_nP cx in let idl := z_idl cx in let s := la_s X in
match o with
| THO_eidx => True
| THO_emitc q => getr regs' 23 = w64 (nP - 1) /\ getr regs' 15 = w64 q /\ 0 <= q < 4096 /\ getr regs' 30 = w64 (z_ctx cx + 60)
| THO_timiss c1 c2 => getr regs' 23 = w64 (s + 1) /\ getr regs' 15 = w64 c1 /\ getr regs' 17 = w64 (c1 * idl) /\
getr regs' 11 = w64 (z_img cx + s + 1) /\
getr regs' 14 = alu64 ALU_ADD (alu64 ALU_SRL (w64 (z_img cx + s + 1)) (w64 3)) (w64 SB) /\
getr regs' 7 = w64 (z_ti cx) /\ getr regs' 30 = w64 (z_ctx cx + 60) /\
0 <= c1 < idl /\ 0 <= c2 < idl /\ nth (Z.to_nat (c1 * idl + c2)) (la_TI X) 0 = 0 /\ s + 1 < nP /\
val_mem SEGS m (z_img cx + s + 1) 1 c2
| THO_inner q => getr regs' 23 = w64 (s + 1) /\ getr regs' 15 = w64 q /\ getr regs' 7 = w64 (z_ti cx) /\
getr regs' 13 = w64 (z_img cx) /\ getr regs' 16 = w64 (nP - 1) /\
0 < q < 4096 /\ s + 1 < nP - 1
end.
Lemma U_tgrd0 : forall E q k s nimg,
ew E q = Z_to_bv 64 s -> ew E k = Z_to_bv 64 nimg -> 0 <= s -> 2 ^ 63 <= nimg < 2 ^ 64 -> s + 1 < 2 ^ 62 ->
U E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff q 0) (SLit (-1))) (SLit (-1))) (SOff k 0)) = nimg - (s + 1).
Proof.
intros E q k s nimg Hq Hk Hs Hn Hs1.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite !U_SLit.
rewrite (U_atom E q s Hq), (U_atom E k nimg Hk) by lia.
change (zcanon (-1)) with (2 ^ 64 - 1). unfold zcanon. rewrite M64_val.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition thead_facts (two ti : bool) : list (nat * afact) :=
[ (23%nat, mkAF 0 100000000 0); (60%nat, APTR 0); (61%nat, mkAF 0 255 0) ]
++ (if two then [ (62%nat, mkAF 0 255 0) ] else [])
++ (if ti then [ (63%nat, mkAF 0 65535 0); (64%nat, APTR 1); (65%nat, mkAF 0 4095 0) ] else []).
Definition thead_alias (ti : bool) : list (sv * sv) :=
[ (SAlu ALU_ADD (SOff 32 0) (SOff 23 0), SOff 60 0) ]
++ (if ti then [ (SAlu ALU_ADD (SMd M_MUL (SOff 61 0) (SOff 25 0)) (SOff 62 0), SOff 63 0);
(SAlu ALU_ADD (SOff 53 0) (SAlu ALU_SLL (SOff 63 0) (SLit 1)), SOff 64 0) ] else []).
Definition thead_conds (two ti : bool) : list acond :=
[ mkAC BC_LTU (SOff 23 0) (SOff 59 0); mkAC (if two then BC_LTU else BC_GEU) (SOff 23 0) (SOff 59 (-1)) ]
++ (if ti then [ mkAC BC_LTU (SOff 61 0) (SOff 25 0); mkAC BC_LTU (SOff 62 0) (SOff 25 0) ] else []).
Definition timg_region (two : bool) : YP09.region :=
YP09.mkRegion (Some 60%nat) 0 (if two then 2 else 1) 0 0
(YP09.mkChunk 0 (CVal 1 (SOff 61%nat 0)) :: (if two then [YP09.mkChunk 1 (CVal 1 (SOff 62%nat 0))] else [])).
Definition thead_regions (two ti : bool) : smem := timg_region two :: (if ti then [reg16 64 65 false] else []).
Definition ss_thead (two ti : bool) : sstate :=
alzw_ss PC_HEAD asr_head false false (thead_regions two ti) (thead_facts two ti) (thead_conds two ti) (thead_alias ti).
Ltac mem_eq_ro HF :=
lazymatch type of HF with frame_of _ _ ?m0 (ms_mem ?msx) =>
let EQM := fresh "EQM" in
assert (EQM : ms_mem msx = m0)
by (apply functional_extensionality; intros x; apply HF; intros (rg & Hin & Hrg); cbn in Hin;
repeat (destruct Hin as [<-|Hin]; [cbn in Hrg; lia|]); destruct Hin);
rewrite <- EQM in *; clear EQM HF end.
Ltac aleaf HS HJ HE0 HF o :=
pmkst HS; ppcs;
apply SRr_ret; split; [reflexivity|];
lazymatch goal with |- exists regs' md' oo, mkCfg (mkst ?rg _ _ _) ?mdx = _ /\ _ =>
exists rg, mdx, o end;
split; [reflexivity|]; split; [exact HJ|];
split; [ lazymatch type of HS with st_ok_pi _ _ ?E1 ?ss1 ?ms1 =>
eapply (alzw_regs_fix_after _ E1 ss1 ms1 _ _ _ HS); [vm_compute; reflexivity | intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | exact HE0 | first [exact HF | exact (alzw_regs_core_of_fix _ _ HF)] | lia | lia] | st_ok _ ?E1 ?ss1 ?ms1 =>
eapply (alzw_regs_fix_after _ E1 ss1 ms1 _ _ _ HS); [vm_compute; reflexivity | intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | exact HE0 | first [exact HF | exact (alzw_regs_core_of_fix _ _ HF)] | lia | lia]  end
| unfold tho_post; cbn [la_s la_TI] ].
Ltac aregv HS r :=
let R := fresh "R" in
prreg HS r R; rewrite R; clear R; cbn [ew ewset Nat.eqb];
rewrite ?ew_ewset_other by lia;
repeat match goal with H : ew ?E ?n = Z_to_bv 64 _ |- context [ew ?E ?n] => rewrite H end;
unfold w64; rewrite ?unsigned_lit_small by lia; rewrite ?Z.add_0_r;
first [ reflexivity | f_equal; lia | match goal with |- ?g => idtac "AREGV" g end ].
Section S.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_1) (PI := PI).
Hypothesis HUL : forall t, In t (lzw_traces (as_code B) BASE) -> In t (as_universe B).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_1 PI.
Lemma thead_seg : forall cx lyc Sc W memc mdc ly7 S7 W7 (regs : bvmap 5 word) memT mdT (regs0 : bvmap 5 word) X,
acx_ok cx -> acx_ranges cx -> acx_seps cx -> acx_blk (ablocks B ly7 S7) cx ->
ajournal SEGS B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 memT mdT 7 ->
alzw_regs_head regs cx -> agen_at (mrestrict (w_H W7) memT) cx (la_lp X) (la_dp X) (la_mp X) ->
alzw_slots (mrestrict (w_H W7) memT) cx -> alzw_sslots (mrestrict (w_H W7) memT) cx -> tlzw_frame (mrestrict (w_H W7) memT) (z_sp cx) regs0 ->
atables_at (mrestrict (w_H W7) memT) cx X -> lzw_inv (z_idl cx) (z_nP cx) X ->
getr regs 23 = w64 (la_s X) -> la_s X < z_nP cx ->
SRr SEGS W7 (mkCfg (mkst regs (Z_to_bv 64 (BASE + PC_HEAD)) memT (seg_rom SEGS)) mdT)
(fun W' c' => W' = W7 /\ exists regs' md' o,
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + tho_pc o)) memT (seg_rom SEGS)) md' /\
ajournal SEGS B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 memT md' 7 /\
alzw_regs_fix regs' cx /\ tho_post cx X (mrestrict (w_H W7) memT) regs' o).
Proof.
intros cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 X HCX HRG HSEP (HBg & HBi & HBt) HJ HFH HG HSL HSS HFR HT HI H24 Hs.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HJ as (HAR & _). pose proof HFH as (HFX & H30 & H16). pose proof (alzw_regs_core_of_fix _ _ HFX) as HFC.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : LZW_TSTK = 336 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
pose proof HCX as (Hidl & HnP & HMR & HMR0 & Hicl & Hal16 & Hsplo & Hsphi & HpR0 & HpR47 & HpR8 & Hgp & Htp & EMR).
assert (HBld : In (z_ld cx, 2 * (lzw_MR (z_nP cx) (z_idl cx) + z_nP cx + 2)) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; left; reflexivity).
assert (HBti : In (z_ti cx, 2 * z_idl cx * z_idl cx) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; right; left; reflexivity).
assert (HBlm : In (z_lm cx, 8192) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; do 2 right; left; reflexivity).
assert (HBlc : In (z_lc cx, 4096) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; do 3 right; left; reflexivity).
assert (HBli : In (z_li cx, 8192) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; do 4 right; left; reflexivity).
assert (HBtm : In (z_tm cx, 4098 * z_idl cx) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; do 5 right; left; reflexivity).
pose proof HRG as (HR & Hbi0 & Hbi1 & Hbi2 & Hbi3). cbn [ranges acx_tabs lzw_tabs app] in HR.
destruct HR as ((Rld1 & Rld2 & Rld3 & Rld4) & (Rti1 & Rti2 & Rti3 & Rti4) & (Rlm1 & Rlm2 & Rlm3 & _) & (Rlc1 & Rlc2 & Rlc3 & _) & (Rli1 & Rli2 & Rli3 & _) &
(Rtm1 & Rtm2 & Rtm3 & Rtm4) & (Rg1 & Rg2 & Rg3 & _) & _).
pose proof (req_size_pos (z_Li cx)) as HrLi.
assert (Htisz : 8 <= z_tisz cx <= 131072) by (unfold z_tisz; clear - Hidl; nia).
rewrite ?C1, ?C2, ?C3, ?C4, ?HTS, ?Has in *. clear C2 C3 C4 HTS Has.
destruct X as [TI LM LI TM s lp dp mp Cn R]. cbn [la_TI la_LM la_LI la_TM la_s la_lp la_dp la_mp] in *.
pose proof HI as (LenTI & LenLM & LenLI & LenTM & BTI & BLI & BLM & UTM & ATMrows & Hdp & Hmp & HA & HR0 & HRC & HCn & Hlp & Hs0).
pose proof (countA_nonneg LI LM) as HA0.
assert (HMRle : z_MR cx <= 26055).
{ assert (z_MR cx * 3838 <= z_MR cx * (4094 - z_idl cx)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
pose proof (lp_head_bound (z_idl cx) (z_nP cx) (z_MR cx) (mkLA TI LM LI TM s lp dp mp Cn R) ltac:(unfold lzw_par; lia) HI ltac:(cbn [la_s]; lia)) as Hlpb.
cbn [la_lp] in Hlpb. unfold cap in Hlpb.
set (m := mrestrict (w_H W7) memT) in *.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (z_bi cx) (z_Li cx) HAR HBi) as (_ & _ & _ & _ & Hbipres & _).
assert (Pimg : forall i, 0 <= i < z_nP cx -> YO0d.present m (z_img cx + i)).
{ intros i Hi. destruct (Hbipres (z_img cx + i) ltac:(lia)) as [[Hh [bb0 Hb0]] _]. exists bb0. subst m. unfold mrestrict. rewrite Hh. exact Hb0. }
destruct (val_mem1 SEGS m (z_img cx + s)) as (C1v & HC1r & HC1); [apply Pimg; lia|]. change (2 ^ 8) with 256 in HC1r.
remember (s <? z_nP cx - 1) as two eqn:Htwo.
assert (HC2ex : exists C2v, 0 <= C2v < 256 /\ (two = true -> val_mem SEGS m (z_img cx + s + 1) 1 C2v)).
{ destruct two.
- symmetry in Htwo. apply Z.ltb_lt in Htwo.
destruct (val_mem1 SEGS m (z_img cx + s + 1)) as (C2v & HC2r & HC2); [replace (z_img cx + s + 1) with (z_img cx + (s + 1)) by lia; apply Pimg; lia|].
exists C2v. change (2 ^ 8) with 256 in HC2r. split; [exact HC2r | intros _; exact HC2].
- exists 0. split; [lia | intros X0; discriminate X0]. }
destruct HC2ex as (C2v & HC2r & HC2).
remember (two && (C1v <? z_idl cx) && (C2v <? z_idl cx)) as ti eqn:Hti.
assert (HtiT : ti = true -> two = true /\ C1v < z_idl cx /\ C2v < z_idl cx).
{ intros ->. symmetry in Hti. apply andb_prop in Hti as [B1 B3]. apply andb_prop in B1 as [B1 B2]. apply Z.ltb_lt in B2. apply Z.ltb_lt in B3. auto. }
assert (HtwoT : two = true -> s < z_nP cx - 1) by (intros ->; symmetry in Htwo; apply Z.ltb_lt in Htwo; exact Htwo).
assert (HtwoF : two = false -> s = z_nP cx - 1) by (intros ->; symmetry in Htwo; apply Z.ltb_ge in Htwo; lia).
remember (C1v * z_idl cx + C2v) as K eqn:HK0.
assert (HKr : 0 <= K <= 255 * 256 + 255).
{ subst K. split; [apply Z.add_nonneg_nonneg; [apply Z.mul_nonneg_nonneg; lia | lia]|].
assert (C1v * z_idl cx <= 255 * 256) by (apply Z.mul_le_mono_nonneg; lia). lia. }
assert (HTIj : ti = true -> (Z.to_nat K < length TI)%nat /\ 0 <= nth (Z.to_nat K) TI 0 < 4096).
{ intros Ht. destruct (HtiT Ht) as (_ & HC1i & HC2i).
destruct (TI_read (z_idl cx) (z_nP cx) (mkLA TI LM LI TM s lp dp mp Cn R) C1v C2v ltac:(lia) HI ltac:(lia) ltac:(lia)) as [T1 T2].
cbn [la_TI] in T1, T2. subst K. exact (conj T1 T2). }
remember (nth (Z.to_nat K) TI 0) as vTI eqn:HvTI.
destruct HT as (ATI & ALM & ALI & ATM).
assert (VTI : ti = true -> val_mem SEGS m (z_ti cx + 2 * K) 2 vTI).
{ intros Ht. destruct (HTIj Ht) as [T1 _]. rewrite HvTI. exact (proj1 (arr16_nthZ SEGS m (z_ti cx) TI K ATI ltac:(lia) T1)). }
assert (HKsz : ti = true -> 2 * K + 2 <= z_tisz cx).
{ intros Ht. destruct (HTIj Ht) as [T1 _]. rewrite LenTI in T1. unfold z_tisz. rewrite <- Z.mul_assoc.
pose proof (Z.mul_nonneg_nonneg (z_idl cx) (z_idl cx) ltac:(lia) ltac:(lia)) as Hii.
assert (K < z_idl cx * z_idl cx) by (apply Z2Nat.inj_lt; [lia | exact Hii | exact T1]). lia. }
remember [Z_to_bv 64 (z_img cx + s); Z_to_bv 64 C1v; Z_to_bv 64 C2v; Z_to_bv 64 K; Z_to_bv 64 (z_ti cx + 2 * K); Z_to_bv 64 vTI] as more eqn:Hmore.
remember (Eimg (Ereg regs (acx_extra cx lp dp mp regs0 ++ more))) as E eqn:HE0. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HE60 : ew E 60 = Z_to_bv 64 (z_img cx + s)) by (rewrite HE0, <- (Nat.add_0_r 60), (AE_more regs _ _ _ _ _ more 0 ltac:(unfold A_TEXT; lia)), Hmore; reflexivity).
assert (HE61 : ew E 61 = Z_to_bv 64 C1v) by (rewrite HE0; change 61%nat with (60 + 1)%nat; rewrite (AE_more regs _ _ _ _ _ more 1 ltac:(unfold A_TEXT; lia)), Hmore; reflexivity).
assert (HE62 : ew E 62 = Z_to_bv 64 C2v) by (rewrite HE0; change 62%nat with (60 + 2)%nat; rewrite (AE_more regs _ _ _ _ _ more 2 ltac:(unfold A_TEXT; lia)), Hmore; reflexivity).
assert (HE63 : ew E 63 = Z_to_bv 64 K) by (rewrite HE0; change 63%nat with (60 + 3)%nat; rewrite (AE_more regs _ _ _ _ _ more 3 ltac:(unfold A_TEXT; lia)), Hmore; reflexivity).
assert (HE64 : ew E 64 = Z_to_bv 64 (z_ti cx + 2 * K)) by (rewrite HE0; change 64%nat with (60 + 4)%nat; rewrite (AE_more regs _ _ _ _ _ more 4 ltac:(unfold A_TEXT; lia)), Hmore; reflexivity).
assert (HE65 : ew E 65 = Z_to_bv 64 vTI) by (rewrite HE0; change 65%nat with (60 + 5)%nat; rewrite (AE_more regs _ _ _ _ _ more 5 ltac:(unfold A_TEXT; lia)), Hmore; reflexivity).
pose proof (AE_sp regs cx lp dp mp regs0 more HFC) as HE2. pose proof (AE_ctx regs cx lp dp mp regs0 more HFC) as HE8.
pose proof (AE_SB regs cx lp dp mp regs0 more HFC) as HE20. pose proof (AE_idl regs cx lp dp mp regs0 more HFC) as HE25.
pose proof (AE_ti regs cx lp dp mp regs0 more) as HE22. pose proof (AE_nP regs cx lp dp mp regs0 more) as HE29.
pose proof (AE_img regs cx lp dp mp regs0 more) as HE32.
rewrite <- HE0 in HE2, HE8, HE20, HE25, HE22, HE29, HE32.
assert (HE24 : ew E 23 = Z_to_bv 64 s) by (rewrite HE0, (AE_reg regs _ _ _ _ _ more 23%bv 23) by reflexivity; exact H24).
Local Ltac septac HSEP i j :=
let Hs := fresh "Hs" in
pose proof (acx_sep _ HSEP i j ltac:(lia) ltac:(lia)) as Hs;
cbv [nth app acx_objs fst snd zz_disj z_tisz z_tmsz z_cap cap] in Hs; lia.
assert (HS : st_ok_pi SEGS VAL E (ss_thead two ti) (restrict (w_H W7) (mkst regs (Z_to_bv 64 (BASE + PC_HEAD)) memT (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_thead. rewrite HE0.
apply (alzw_st_ok cx regs regs0 lp dp mp more m PC_HEAD asr_head false false); rewrite <- ?HE0.
- exact HCX. - exact HRG. - exact HFC. - exact HG. - exact HSL. - exact HSS. - exact HFR.
- intros X0; discriminate X0. - intros X0; discriminate X0.
- lia. - lia. - lia.
- rewrite HE0. apply (regs_ok_head regs cx); [exact HFH | lia | lia | lia].
- destruct two, ti; vm_compute; reflexivity.
- unfold thead_regions. apply Forall_cons.
+ unfold region_ok, timg_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite HE60, unsigned_lit_small by lia. split; [lia|]. split; [destruct two; lia|]. split; [intros o Ho; lia|].
apply Forall_cons.
{ eapply chunk_ok_val; [| | cbn; lia | rewrite Z.add_0_r; exact HC1]; [|change (2 ^ (8 * Z.of_N 1)) with 256; lia].
cbn [sv_denot]. rewrite HE61, Z.add_0_r, unsigned_lit_small by lia. reflexivity. }
destruct two; [|apply Forall_nil]. apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [| | cbn; lia | exact (HC2 eq_refl)]; [|change (2 ^ (8 * Z.of_N 1)) with 256; lia].
cbn [sv_denot]. rewrite HE62, Z.add_0_r, unsigned_lit_small by lia. reflexivity.
+ destruct ti; [|apply Forall_nil]. destruct (HtiT eq_refl) as (Htw & HC1i & HC2i). specialize (HKsz eq_refl).
apply Forall_cons; [|apply Forall_nil].
apply (region_ok_reg16 _ E m 64 65 false (z_ti cx + 2 * K) vTI HE64 HE65); [lia | lia | | exact (VTI eq_refl) | intros X0; discriminate X0].
destruct (HTIj eq_refl) as [_ T2]. lia.
-
unfold thead_regions. destruct ti.
+ destruct (HtiT eq_refl) as (Htw & HC1i & HC2i). specialize (HKsz eq_refl).
cbn [all_disjoint app]; unfold extent_disjoint, timg_region, reg16, actx_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val app].
rewrite HE8, HE60, HE64, !unsigned_lit_small by lia.
split; [destruct two; septac HSEP 6%nat 7%nat|]. split; [septac HSEP 1%nat 6%nat | exact I].
+ cbn [all_disjoint app]; unfold extent_disjoint, timg_region, actx_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val app].
rewrite HE8, HE60, !unsigned_lit_small by lia. split; [destruct two; septac HSEP 6%nat 7%nat | exact I].
-
unfold thead_regions. destruct ti.
+ destruct (HtiT eq_refl) as (Htw & HC1i & HC2i). specialize (HKsz eq_refl).
cbn [all_disjoint app]; unfold extent_disjoint, timg_region, reg16, astk_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val app].
rewrite HE2, HE60, HE64, !unsigned_lit_small by lia. split; [destruct two; lia|]. split; [lia | exact I].
+ cbn [all_disjoint app]; unfold extent_disjoint, timg_region, astk_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val app].
rewrite HE2, HE60, !unsigned_lit_small by lia. split; [destruct two; lia | exact I].
- unfold thead_regions. destruct ti; [|cbn [pairwise_disjoint all_disjoint app]; repeat split].
destruct (HtiT eq_refl) as (Htw & HC1i & HC2i). specialize (HKsz eq_refl). destruct two; [|discriminate Htw]. specialize (HtwoT eq_refl).
cbn [pairwise_disjoint all_disjoint app]; unfold extent_disjoint, timg_region, reg16; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite HE60, HE64, !unsigned_lit_small by lia. split; [split; [septac HSEP 1%nat 7%nat | exact I] | split; exact I].
- unfold thead_facts. apply atoms_ok_app; [|apply atoms_ok_app].
+ cbn [atoms_ok]. unfold afact_ok, APTR. cbn [af_lo af_hi af_al2].
rewrite HE24, HE60, HE61, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
+ destruct two; [|exact I]. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE62, !unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
+ destruct ti; [|exact I]. destruct (HTIj eq_refl) as [_ T2]. specialize (HKsz eq_refl).
cbn [atoms_ok]. unfold afact_ok, APTR. cbn [af_lo af_hi af_al2].
rewrite HE63, HE64, HE65, !unsigned_lit_small by lia. change (2 ^ 0) with 1. change (2 ^ 1) with 2. rewrite !Z.mod_1_r.
repeat split; try lia.
apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists K; lia].
apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rti3].
- unfold thead_conds. cbn [conds_ok app]. split; [|split].
+ apply (cond_ltu E 23 0 59 0 s (z_nP cx) HE24 HE29); lia.
+ destruct two.
* specialize (HtwoT eq_refl). apply (cond_ltu E 23 0 59 (-1) s (z_nP cx) HE24 HE29); lia.
* specialize (HtwoF eq_refl). apply (cond_geu E 23 0 59 (-1) s (z_nP cx) HE24 HE29); lia.
+ destruct ti; [|exact I]. destruct (HtiT eq_refl) as (Htw & HC1i & HC2i). cbn [conds_ok].
split; [apply (cond_ltu E 61 0 25 0 C1v (z_idl cx) HE61 HE25); lia|].
split; [apply (cond_ltu E 62 0 25 0 C2v (z_idl cx) HE62 HE25); lia | exact I].
- unfold thead_alias. cbn [alias_ok app]. split.
+ rewrite (alias_add E 32 23 60 (z_img cx) s HE32 HE24 HE60); [reflexivity | lia | lia | lia].
+ destruct ti; [|exact I]. destruct (HtiT eq_refl) as (Htw & HC1i & HC2i). specialize (HKsz eq_refl). cbn [alias_ok].
split; [rewrite HK0 in HE63; apply (alias_mul_add E 61 25 62 63 C1v (z_idl cx) C2v HE61 HE25 HE62 HE63); lia|].
split; [apply (alias_b2i' E 53 63 64 (z_ti cx) K HE22 HE63 HE64); lia | exact I]. }
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
assert (SHOK : sh_ok SEGS (SOff 27 0) [] E (mrestrict (w_H W7) (ms_mem (mkst regs (Z_to_bv 64 (BASE + PC_HEAD)) memT (seg_rom SEGS))))) by (unfold sh_ok; apply Forall_nil).
change memT with (ms_mem (mkst regs (Z_to_bv 64 (BASE + PC_HEAD)) memT (seg_rom SEGS))) in HJ.
Local Ltac hobl HJ HBi HBt HBg HE60 HE64 HE20 HE8 vimg vti vctx :=
let L := getLAWS in
match goal with
| |- range_addressable _ (U ?Ex _) (U _ (SOff 60 ?c)) ?len =>
rewrite (U_atom_off Ex 60 vimg c); [| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact HE60 | lia | lia];
eapply (obl_of_block SEGS _ L _ _ _ _ _ Ex (SOff 27 0) _ len _ _ (proj1 HJ) HBi);
[rewrite (U_atom Ex 27 SB); [reflexivity | cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact HE20 | unfold SB; lia] | lia | lia]
| |- range_addressable _ (U ?Ex _) (U _ (SOff 64 0)) ?len =>
rewrite (U_atom Ex 64 vti); [| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact HE64 | lia];
eapply (obl_of_block SEGS _ L _ _ _ _ _ Ex (SOff 27 0) _ len _ _ (proj1 HJ) HBt);
[rewrite (U_atom Ex 27 SB); [reflexivity | cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact HE20 | unfold SB; lia]
| lia | unfold z_tisz in *; match goal with |- _ <= _ + req_size ?n => pose proof (req_size_pos n ltac:(lia)) end; lia]
| |- range_addressable _ (U ?Ex _) (U _ (SOff 8 ?c)) ?len =>
first [ rewrite (U_atom_off Ex 8 vctx c); [| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact HE8 | lia | lia]
| rewrite (U_atom Ex 8 vctx); [| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact HE8 | lia] ];
eapply (obl_of_block SEGS _ L _ _ _ _ _ Ex (SOff 27 0) _ len _ _ (proj1 HJ) HBg);
[rewrite (U_atom Ex 27 SB); [reflexivity | cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact HE20 | unfold SB; lia] | lia | change (req_size 72) with 72; lia]
| |- _ => idtac
end.
destruct ti.
-
destruct (HtiT eq_refl) as (Htw & HC1i & HC2i). destruct two; [|discriminate Htw]. specialize (HtwoT eq_refl). destruct (HTIj eq_refl) as [T1 T2]. specialize (HKsz eq_refl).
paj_run_tok RUN HS HJ SHOK Bspan; try hobl HJ HBi HBti HBg HE60 HE64 HE20 HE8 (z_img cx + s) (z_ti cx + 2 * K) (z_ctx cx); [awr_ok_tac|].
mem_eq_ro HF. clear HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
+
paj_run_to_tok RUNTO HS HJ SHOK Bspan PC_TIMISS; try hobl HJ HBi HBti HBg HE60 HE64 HE20 HE8 (z_img cx + s) (z_ti cx + 2 * K) (z_ctx cx); [awr_ok_tac|]. mem_eq_ro HF. clear HFr HG.
rewrite branch_eq_U, (U_atom _ 65 vTI), U_SLit in Hc by (first [cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact HE65 | lia]). change (zcanon 0) with 0 in Hc.
apply Z.eqb_eq in Hc.
aleaf HS HJ HE0 HFX (THO_timiss C1v C2v). subst K.
split; [aregv HS (23%bv : bv 5)|]. split; [aregv HS (15%bv : bv 5)|].
split; [rregU HS (17%bv : bv 5) (C1v * z_idl cx)
ltac:(apply (U_mul_atoms _ 61 25 C1v (z_idl cx)); [cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact HE61 | cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact HE25 | lia | lia]) R17; exact R17|].
split; [aregv HS (11%bv : bv 5)|]. split; [aregv HS (14%bv : bv 5)|].
split; [aregv HS (7%bv : bv 5)|]. split; [aregv HS (30%bv : bv 5)|].
split; [lia|]. split; [lia|]. split; [rewrite <- HvTI; exact Hc|]. split; [lia|]. exact (HC2 eq_refl).
+ rewrite branch_eq_U, (U_atom _ 65 vTI), U_SLit in Hc by (first [cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact HE65 | lia]). change (zcanon 0) with 0 in Hc.
assert (HvTInz : vTI <> 0) by (destruct (Z.eqb_spec vTI 0); [discriminate | assumption]). clear Hc.
paj_run_tok RUN HS HJ SHOK Bspan; try hobl HJ HBi HBti HBg HE60 HE64 HE20 HE8 (z_img cx + s) (z_ti cx + 2 * K) (z_ctx cx); [awr_ok_tac|]. mem_eq_ro HF. clear HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
*
paj_run_to_tok RUNTO HS HJ SHOK Bspan PC_EMITC; try hobl HJ HBi HBti HBg HE60 HE64 HE20 HE8 (z_img cx + s) (z_ti cx + 2 * K) (z_ctx cx); [awr_ok_tac|]. mem_eq_ro HF. clear HFr HG.
rewrite branch_geu_U, (U_atom_off _ 23 s 1), (U_atom_off _ 59 (z_nP cx) (-1)) in Hc
by (first [cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; first [exact HE24 | exact HE29] | lia]).
assert (Hs1 : s + 1 = z_nP cx - 1) by (destruct (Z.ltb_spec (s + 1) (z_nP cx + -1)); [discriminate | lia]). clear Hc.
aleaf HS HJ HE0 HFX (THO_emitc vTI).
split; [aregv HS (23%bv : bv 5)|]. split; [aregv HS (15%bv : bv 5)|]. split; [lia|]. aregv HS (30%bv : bv 5).
* paj_run_to_tok RUNTO HS HJ SHOK Bspan PC_ISET; try hobl HJ HBi HBti HBg HE60 HE64 HE20 HE8 (z_img cx + s) (z_ti cx + 2 * K) (z_ctx cx); [awr_ok_tac|]. mem_eq_ro HF. clear HFr HG.
rewrite branch_geu_U, (U_atom_off _ 23 s 1), (U_atom_off _ 59 (z_nP cx) (-1)) in Hc
by (first [cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; first [exact HE24 | exact HE29] | lia]).
assert (Hs1 : s + 1 < z_nP cx - 1) by (destruct (Z.ltb_spec (s + 1) (z_nP cx + -1)); [lia | discriminate]). clear Hc.
aleaf HS HJ HE0 HFX (THO_inner vTI).
split; [aregv HS (23%bv : bv 5)|]. split; [aregv HS (15%bv : bv 5)|]. split; [aregv HS (7%bv : bv 5)|]. split; [aregv HS (13%bv : bv 5)|].
split; [aregv HS (16%bv : bv 5) | lia].
- destruct two.
+
specialize (HtwoT eq_refl).
paj_run_tok RUN HS HJ SHOK Bspan; try hobl HJ HBi HBti HBg HE60 HE64 HE20 HE8 (z_img cx + s) (z_ti cx + 2 * K) (z_ctx cx); [awr_ok_tac|].
mem_eq_ro HF. clear HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
* paj_run_to_tok RUNTO HS HJ SHOK Bspan PC_EIDX; try hobl HJ HBi HBti HBg HE60 HE64 HE20 HE8 (z_img cx + s) (z_ti cx + 2 * K) (z_ctx cx); [awr_ok_tac|]. mem_eq_ro HF. clear HFr HG.
aleaf HS HJ HE0 HFX THO_eidx. exact I.
* rewrite branch_geu_U, (U_atom _ 61 C1v), (U_atom _ 25 (z_idl cx)) in Hc
by (first [cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; first [exact HE61 | exact HE25] | lia]).
assert (HC1i : C1v < z_idl cx) by (destruct (Z.ltb_spec C1v (z_idl cx)); [lia | discriminate]). clear Hc.
paj_run_tok RUN HS HJ SHOK Bspan; try hobl HJ HBi HBti HBg HE60 HE64 HE20 HE8 (z_img cx + s) (z_ti cx + 2 * K) (z_ctx cx); [awr_ok_tac|].
mem_eq_ro HF. clear HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
-- paj_run_to_tok RUNTO HS HJ SHOK Bspan PC_EIDX; try hobl HJ HBi HBti HBg HE60 HE64 HE20 HE8 (z_img cx + s) (z_ti cx + 2 * K) (z_ctx cx); [awr_ok_tac|]. mem_eq_ro HF. clear HFr HG.
aleaf HS HJ HE0 HFX THO_eidx. exact I.
-- rewrite branch_geu_U, (U_atom _ 62 C2v), (U_atom _ 25 (z_idl cx)) in Hc
by (first [cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; first [exact HE62 | exact HE25] | lia]).
exfalso. destruct (Z.ltb_spec C2v (z_idl cx)); [|discriminate].
assert (X1 : (C1v <? z_idl cx) = true) by (apply Z.ltb_lt; lia).
rewrite X1 in Hti. cbn in Hti. try (rewrite (proj2 (Z.ltb_lt C2v (z_idl cx))) in Hti by lia). discriminate Hti.
+
specialize (HtwoF eq_refl).
paj_run_tok RUN HS HJ SHOK Bspan; try hobl HJ HBi HBti HBg HE60 HE64 HE20 HE8 (z_img cx + s) (z_ti cx + 2 * K) (z_ctx cx); [awr_ok_tac|].
mem_eq_ro HF. clear HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
* paj_run_to_tok RUNTO HS HJ SHOK Bspan PC_EIDX; try hobl HJ HBi HBti HBg HE60 HE64 HE20 HE8 (z_img cx + s) (z_ti cx + 2 * K) (z_ctx cx); [awr_ok_tac|]. mem_eq_ro HF. clear HFr HG.
aleaf HS HJ HE0 HFX THO_eidx. exact I.
* rewrite branch_geu_U, (U_atom _ 61 C1v), (U_atom _ 25 (z_idl cx)) in Hc
by (first [cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; first [exact HE61 | exact HE25] | lia]).
assert (HC1i : C1v < z_idl cx) by (destruct (Z.ltb_spec C1v (z_idl cx)); [lia | discriminate]). clear Hc.
paj_run_to_tok RUNTO HS HJ SHOK Bspan PC_EMITC; try hobl HJ HBi HBti HBg HE60 HE64 HE20 HE8 (z_img cx + s) (z_ti cx + 2 * K) (z_ctx cx); [awr_ok_tac|]. mem_eq_ro HF. clear HFr HG.
aleaf HS HJ HE0 HFX (THO_emitc C1v).
split; [aregv HS (23%bv : bv 5)|]. split; [aregv HS (15%bv : bv 5)|]. split; [lia|]. aregv HS (30%bv : bv 5).
Qed.
End S.
End d.
End a.
