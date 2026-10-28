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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI08 YI0t YI0m YI0n YI0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC81 YC4b.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a AC93 AC9g.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Lemma st_ok_pi_reg : forall E ss ms r, st_ok_pi SEGS VAL E ss ms -> getr (ms_regs ms) r = sv_denot E (sr_get (ss_regs ss) r).
Proof. intros E ss ms r HS. destruct ss. exact (st_ok_reg SEGS E _ ms r HS). Qed.
Definition PC_HEAD : Z := 0x177c.
Definition PC_EPI : Z := 0x2014.
Definition PC_EIDX : Z := 0x200c.
Definition PC_TAIL : Z := 0x1dd0.
Record lzw_acx := mkACX {
z_sp : Z;
z_ctx : Z;
z_ti : Z; z_lm : Z; z_lc : Z; z_li : Z; z_tm : Z; z_ld : Z;
z_img : Z; z_nP : Z; z_idl : Z; z_icl : Z; z_pR : Z;
z_MR : Z; z_bi : Z; z_Li : Z; z_gp : Z; z_tp : Z }.
Definition z_cap (cx : lzw_acx) : Z := cap (z_nP cx) (z_MR cx).
Definition z_tisz (cx : lzw_acx) : Z := 2 * z_idl cx * z_idl cx.
Definition z_tmsz (cx : lzw_acx) : Z := 4098 * z_idl cx.
Definition acx_ok (cx : lzw_acx) : Prop :=
2 <= z_idl cx <= 256 /\ 1 <= z_nP cx <= 100000000 /\
z_MR cx * (4094 - z_idl cx) <= z_nP cx < (z_MR cx + 1) * (4094 - z_idl cx) /\ 0 <= z_MR cx /\
0 <= z_icl cx <= 12 /\
z_sp cx mod 16 = 0 /\ alloc_ceiling + LZW_TSTK <= z_sp cx /\ z_sp cx <= 2 ^ 47 /\
0 <= z_pR cx /\ z_pR cx + 16 <= 2 ^ 47 /\ z_pR cx mod 8 = 0 /\
0 <= z_gp cx < 2 ^ 64 /\ 0 <= z_tp cx < 2 ^ 64 /\ z_MR cx = lzw_MR (z_nP cx) (z_idl cx).
Definition acx_tabs (cx : lzw_acx) : list (Z * Z) :=
lzw_tabs (z_ti cx) (z_lm cx) (z_lc cx) (z_li cx) (z_tm cx) (z_ld cx) (z_nP cx) (z_idl cx).
Definition acx_objs (cx : lzw_acx) : list (Z * Z) :=
[ (z_ld cx, 2 * z_cap cx); (z_ti cx, z_tisz cx); (z_lm cx, 8192); (z_lc cx, 4096); (z_li cx, 8192); (z_tm cx, z_tmsz cx);
(z_ctx cx, 72); (z_img cx, z_nP cx) ].
Fixpoint seps_from (b : Z * Z) (l : list (Z * Z)) : Prop :=
match l with
| [] => True
| c :: r => (fst b + snd b <= fst c \/ fst c + snd c <= fst b) /\ seps_from b r
end.
Fixpoint seps (l : list (Z * Z)) : Prop :=
match l with [] => True | b :: r => seps_from b r /\ seps r end.
Definition zz_disj (b c : Z * Z) : Prop := fst b + snd b <= fst c \/ fst c + snd c <= fst b.
Lemma seps_from_nth : forall b l j d, seps_from b l -> (j < length l)%nat -> zz_disj b (nth j l d).
Proof.
intros b l. induction l as [|c r IH]; intros j d H Hj; cbn in Hj; [lia|].
destruct H as [H1 H2]. destruct j as [|j]; cbn [nth]; [exact H1|]. apply IH; [exact H2 | lia].
Qed.
Lemma seps_nth : forall l i j d, seps l -> (i < j)%nat -> (j < length l)%nat -> zz_disj (nth i l d) (nth j l d).
Proof.
induction l as [|b r IH]; intros i j d H Hij Hj; cbn in Hj; [lia|].
destruct H as [H1 H2]. destruct i as [|i].
- destruct j as [|j]; [lia|]. cbn [nth]. apply seps_from_nth; [exact H1 | lia].
- destruct j as [|j]; [lia|]. cbn [nth]. apply IH; [exact H2 | lia | lia].
Qed.
Definition acx_seps (cx : lzw_acx) : Prop := seps (acx_objs cx).
Lemma acx_sep : forall cx, acx_seps cx -> forall i j, (i < j)%nat -> (j < 8)%nat ->
zz_disj (nth i (acx_objs cx) (0, 0)) (nth j (acx_objs cx) (0, 0)).
Proof. intros cx H i j Hij Hj. apply seps_nth; [exact H | exact Hij | cbn; lia]. Qed.
Fixpoint ranges (l : list (Z * Z)) : Prop :=
match l with [] => True | (a, n) :: r => ((4096 <= a /\ zone2 a n) /\ a + n <= alloc_ceiling /\ a mod 16 = 0 /\ 0 < n) /\ ranges r end.
Definition acx_ranges (cx : lzw_acx) : Prop :=
ranges (acx_tabs cx ++ [(z_ctx cx, 72)]) /\
(4096 <= z_bi cx /\ zone2 (z_bi cx) (req_size (z_Li cx))) /\
z_bi cx <= z_img cx /\ z_img cx + z_nP cx <= z_bi cx + req_size (z_Li cx) /\ z_bi cx + req_size (z_Li cx) <= alloc_ceiling.
Definition alzw_regs_fix (regs : bvmap 5 word) (cx : lzw_acx) : Prop :=
spZ regs = z_sp cx - 320 /\ getr regs 8 = w64 (z_ctx cx) /\
getr regs 9 = w64 (z_ctx cx + 32) /\ getr regs 18 = w64 (z_ctx cx + 24) /\ getr regs 19 = w64 (z_ctx cx + 16) /\ getr regs 20 = w64 (z_ctx cx + 8) /\
getr regs 21 = w64 2 /\
getr regs 22 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (z_ctx cx)) (Z_to_bv 64 3)) (Z_to_bv 64 SB) /\
getr regs 25 = w64 (z_idl cx) /\
getr regs 26 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (z_ctx cx + 8)) (Z_to_bv 64 3)) (Z_to_bv 64 SB) /\
getr regs 27 = w64 SB /\ getr regs 1 = w64 (z_ctx cx + 40) /\
getr regs 3 = w64 (z_gp cx) /\ getr regs 4 = w64 (z_tp cx).
Definition alzw_regs_head (regs : bvmap 5 word) (cx : lzw_acx) : Prop :=
alzw_regs_fix regs cx /\ getr regs 30 = w64 (z_ctx cx + 60) /\ getr regs 16 = w64 (z_nP cx).
Definition AREGS_FIXL : list (bv 5) := [2; 8; 9; 18; 19; 20; 21; 22; 25; 26; 27; 1; 3; 4]%bv.
Lemma alzw_regs_fix_kept : forall regs regs' cx,
alzw_regs_fix regs cx -> (forall r, In r AREGS_FIXL -> getr regs' r = getr regs r) -> alzw_regs_fix regs' cx.
Proof.
intros regs regs' cx H HK. unfold alzw_regs_fix, spZ in *. rewrite !HK by (cbv; tauto). exact H.
Qed.
Definition alzw_slots (m : word -> option byte) (cx : lzw_acx) : Prop :=
let sp := z_sp cx - 320 in let ctx := z_ctx cx in
val_mem SEGS m (sp + 56) 8 (z_idl cx + 2) /\
val_mem SEGS m (sp + 72) 8 (ctx + 66) /\ val_mem SEGS m (sp + 88) 8 (ctx + 60) /\ val_mem SEGS m (sp + 96) 8 (ctx + 64) /\
val_mem SEGS m (sp + 120) 8 (ctx + 48) /\ val_mem SEGS m (sp + 144) 8 (ctx + 56) /\ val_mem SEGS m (sp + 152) 8 (z_pR cx) /\
val_mem SEGS m (sp + 168) 8 (2 * z_idl cx) /\ val_mem SEGS m (sp + 176) 8 (z_icl cx) /\ val_mem SEGS m (sp + 184) 8 (z_tisz cx) /\
val_mem SEGS m (sp + 208) 8 (ctx + 40).
Definition alzw_sslots (m : word -> option byte) (cx : lzw_acx) : Prop :=
let sp := z_sp cx - 320 in let ctx := z_ctx cx in
val_mem SEGS m (sp + 64) 8 (shadow_word (ctx + 66)) /\ val_mem SEGS m (sp + 80) 8 (shadow_word (ctx + 64)) /\
val_mem SEGS m (sp + 104) 8 (shadow_word (ctx + 60)) /\ val_mem SEGS m (sp + 112) 8 (shadow_word (ctx + 48)) /\
val_mem SEGS m (sp + 128) 8 (shadow_word (ctx + 40)) /\ val_mem SEGS m (sp + 136) 8 (shadow_word (ctx + 56)) /\
val_mem SEGS m (sp + 160) 8 (shadow_word (ctx + 32)) /\ val_mem SEGS m (sp + 192) 8 (shadow_word (ctx + 24)) /\
val_mem SEGS m (sp + 200) 8 (shadow_word (ctx + 16)).
Definition agen_at (m : word -> option byte) (cx : lzw_acx) (lp dp mp : Z) : Prop :=
let g := z_ctx cx in
val_mem SEGS m g 8 (z_ti cx) /\ val_mem SEGS m (g + 8) 8 (z_lm cx) /\
val_mem SEGS m (g + 16) 8 (z_lc cx) /\ val_mem SEGS m (g + 24) 8 (z_li cx) /\
val_mem SEGS m (g + 32) 8 (z_tm cx) /\ val_mem SEGS m (g + 40) 8 (z_ld cx) /\
val_mem SEGS m (g + 48) 8 (z_img cx) /\ val_mem SEGS m (g + 56) 4 (z_nP cx) /\
val_mem SEGS m (g + 60) 4 lp /\ val_mem SEGS m (g + 64) 2 dp /\ val_mem SEGS m (g + 66) 2 mp.
Definition atables_at (m : word -> option byte) (cx : lzw_acx) (X : lzw_abs) : Prop :=
arr16 SEGS m (z_ti cx) (la_TI X) /\ arr16 SEGS m (z_lm cx) (la_LM X) /\
arr16 SEGS m (z_li cx) (la_LI X) /\ arr16 SEGS m (z_tm cx) (la_TM X).
Lemma agen_at_frame : forall m m' cx lp dp mp,
agen_at m cx lp dp mp -> (forall a, z_ctx cx <= a < z_ctx cx + 72 -> mbyte SEGS m' a = mbyte SEGS m a) ->
agen_at m' cx lp dp mp.
Proof.
intros m m' cx lp dp mp (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11) Hfr.
repeat split; intros k Hk; (rewrite Hfr; [first [apply H1 | apply H2 | apply H3 | apply H4 | apply H5 | apply H6 | apply H7 | apply H8 | apply H9 | apply H10 | apply H11]; exact Hk | cbn in Hk; lia]).
Qed.
Definition tlzw_caller (B : asyms) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
(lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z)
(regs : bvmap 5 word) (pR nP idl icl : Z) : Prop :=
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
YK0s.ret_ok (getr regs 1) /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - LZW_TSTK /\ spZ regs <= sp0 /\
pR mod 8 = 0 /\ (spZ regs <= pR \/ pR + 16 <= spZ regs - LZW_TSTK) /\ 0 <= pR /\ pR + 16 <= 2 ^ 63 /\
(forall a, pR <= a < pR + 16 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a) /\
tlzw_pR_ok SEGS lyc Sc W memc pR /\
1 <= nP <= 100000000 /\ 2 <= idl <= 256 /\ 0 <= icl <= 12 /\
st_nev Sc + LZW_EV <= EV_MAX /\ blocks_bytes Sc + 2 ^ 29 <= LIVE_MAX.
Definition optb (p n : Z) : list (Z * Z) := if p =? 0 then [] else [(p, n)].
Lemma tnz_cons : forall p n l, tnz ((p, n) :: l) = optb p n ++ tnz l.
Proof. intros p n l. unfold tnz, optb. cbn [List.filter fst]. destruct (p =? 0); reflexivity. Qed.
Lemma tnz_id : forall l : list (Z * Z), Forall (fun b => fst b <> 0) l -> tnz l = l.
Proof.
intros l H. induction H as [|b l Hb H IH]; [reflexivity|]. destruct b as [p n]. cbn [fst] in Hb.
unfold tnz in *. cbn [List.filter fst]. replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hb). cbn [negb]. f_equal. exact IH.
Qed.
End f.
End e.
