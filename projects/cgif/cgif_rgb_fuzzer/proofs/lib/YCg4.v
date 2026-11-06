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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI01 YI07 YI03 YI04 YI06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YF9i YCeb YCe8 YCdv YCgl YCg2 YCgi.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section e. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition PC_HEAD : Z := 0x8a6e8.
Definition PC_EPI : Z := 0x8b084.
Definition PC_EIDX : Z := 0x8b07c.
Definition PC_TAIL : Z := 0x8ae40.
Definition PC_CLEAN2 : Z := 0x8b1ec.
Definition PC_CLEAN1 : Z := 0x8b1f0.
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
spZ regs = z_sp cx - 304 /\ getr regs 8 = w64 (z_ctx cx) /\
getr regs 21 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (z_ctx cx)) (Z_to_bv 64 3)) (Z_to_bv 64 SB) /\
getr regs 18 = w64 (z_ctx cx + 24) /\ getr regs 19 = w64 (z_ctx cx + 16) /\ getr regs 20 = w64 (z_ctx cx + 8) /\
getr regs 23 = w64 SB /\ getr regs 22 = w64 2 /\
getr regs 26 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (z_ctx cx + 8)) (Z_to_bv 64 3)) (Z_to_bv 64 SB) /\
getr regs 25 = w64 (z_idl cx) /\
getr regs 3 = w64 (z_gp cx) /\ getr regs 4 = w64 (z_tp cx).
Definition alzw_regs_head (regs : bvmap 5 word) (cx : lzw_acx) : Prop :=
alzw_regs_fix regs cx /\ getr regs 15 = w64 (z_nP cx).
Definition AREGS_FIXL : list (bv 5) := [2; 8; 21; 18; 19; 20; 23; 22; 26; 25; 3; 4]%bv.

Definition alzw_slots (m : word -> option byte) (cx : lzw_acx) : Prop :=
let sp := z_sp cx - 304 in let ctx := z_ctx cx in
val_mem trbsegs m (sp + 40) 8 1 /\ val_mem trbsegs m (sp + 48) 8 7 /\
val_mem trbsegs m (sp + 56) 8 (ctx + 66) /\ val_mem trbsegs m (sp + 72) 8 (ctx + 64) /\ val_mem trbsegs m (sp + 88) 8 (ctx + 48) /\
val_mem trbsegs m (sp + 112) 8 (ctx + 56) /\ val_mem trbsegs m (sp + 128) 8 (ctx + 60) /\
val_mem trbsegs m (sp + 152) 8 (2 * z_idl cx) /\ val_mem trbsegs m (sp + 160) 8 (z_icl cx) /\ val_mem trbsegs m (sp + 136) 8 (z_pR cx) /\
val_mem trbsegs m (sp + 184) 8 (ctx + 40) /\ val_mem trbsegs m (sp + 192) 8 (ctx + 32).
Definition alzw_sslots (m : word -> option byte) (cx : lzw_acx) : Prop :=
let sp := z_sp cx - 304 in let ctx := z_ctx cx in
val_mem trbsegs m (sp + 64) 8 (shadow_word (ctx + 64)) /\ val_mem trbsegs m (sp + 80) 8 (shadow_word (ctx + 48)) /\
val_mem trbsegs m (sp + 96) 8 (shadow_word (ctx + 40)) /\ val_mem trbsegs m (sp + 104) 8 (shadow_word (ctx + 56)) /\
val_mem trbsegs m (sp + 120) 8 (shadow_word (ctx + 60)) /\ val_mem trbsegs m (sp + 176) 8 (shadow_word (ctx + 16)) /\
val_mem trbsegs m (sp + 144) 8 (shadow_word (ctx + 32)) /\ val_mem trbsegs m (sp + 168) 8 (shadow_word (ctx + 24)).
Definition agen_at (m : word -> option byte) (cx : lzw_acx) (lp dp mp : Z) : Prop :=
let g := z_ctx cx in
val_mem trbsegs m g 8 (z_ti cx) /\ val_mem trbsegs m (g + 8) 8 (z_lm cx) /\
val_mem trbsegs m (g + 16) 8 (z_lc cx) /\ val_mem trbsegs m (g + 24) 8 (z_li cx) /\
val_mem trbsegs m (g + 32) 8 (z_tm cx) /\ val_mem trbsegs m (g + 40) 8 (z_ld cx) /\
val_mem trbsegs m (g + 48) 8 (z_img cx) /\ val_mem trbsegs m (g + 56) 4 (z_nP cx) /\
val_mem trbsegs m (g + 60) 4 lp /\ val_mem trbsegs m (g + 64) 2 dp /\ val_mem trbsegs m (g + 66) 2 mp.
Definition atables_at (m : word -> option byte) (cx : lzw_acx) (X : lzw_abs) : Prop :=
arr16 trbsegs m (z_ti cx) (la_TI X) /\ arr16 trbsegs m (z_lm cx) (la_LM X) /\
arr16 trbsegs m (z_li cx) (la_LI X) /\ arr16 trbsegs m (z_tm cx) (la_TM X).
Lemma agen_at_frame : forall m m' cx lp dp mp,
agen_at m cx lp dp mp -> (forall a, z_ctx cx <= a < z_ctx cx + 72 -> mbyte trbsegs m' a = mbyte trbsegs m a) ->
agen_at m' cx lp dp mp.
Proof.
intros m m' cx lp dp mp (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11) Hfr.
repeat split; intros k Hk; (rewrite Hfr; [first [apply H1 | apply H2 | apply H3 | apply H4 | apply H5 | apply H6 | apply H7 | apply H8 | apply H9 | apply H10 | apply H11]; exact Hk | cbn in Hk; lia]).
Qed.
Definition tlzw_caller (B : asyms) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trbsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
(lyc : alayout) (Sc : astate) (W : world trbsegs) (memc : word -> option byte) (mdc : Model) (k : Z)
(regs : bvmap 5 word) (pR nP idl icl : Z) : Prop :=
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
YK0s.ret_ok (getr regs 1) /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - LZW_TSTK /\ spZ regs <= sp0 /\
pR mod 8 = 0 /\ (spZ regs <= pR \/ pR + 16 <= spZ regs - LZW_TSTK) /\ 0 <= pR /\ pR + 16 <= 2 ^ 63 /\
(forall a, pR <= a < pR + 16 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a) /\
tlzw_pR_ok lyc Sc W memc pR /\
1 <= nP <= 100000000 /\ 2 <= idl <= 256 /\ 0 <= icl <= 12 /\
vev Sc + LZW_EV <= VEV_MAX /\ blocks_bytes Sc + 2 ^ 29 <= LIVE_MAX.
Definition optb (p n : Z) : list (Z * Z) := if p =? 0 then [] else [(p, n)].
Lemma tnz_cons : forall p n l, tnz ((p, n) :: l) = optb p n ++ tnz l.
Proof. intros p n l. unfold tnz, optb. cbn [List.filter fst]. destruct (p =? 0); reflexivity. Qed.
Lemma tnz_id : forall l : list (Z * Z), Forall (fun b => fst b <> 0) l -> tnz l = l.
Proof.
intros l H. induction H as [|b l Hb H IH]; [reflexivity|]. destruct b as [p n]. cbn [fst] in Hb.
unfold tnz in *. cbn [List.filter fst]. replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hb). cbn [negb]. f_equal. exact IH.
Qed.
End e.
