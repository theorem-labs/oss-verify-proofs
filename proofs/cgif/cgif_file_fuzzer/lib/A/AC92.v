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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a AC93 AC9g AC95 AC91 AC99.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition aabove_eq (cx : lzw_acx) (m m' : word -> option byte) : Prop :=
forall a, z_sp cx - 264 <= a < 2 ^ 64 -> mbyte SEGS m' a = mbyte SEGS m a.
Lemma aabove_eq_refl : forall cx m, aabove_eq cx m m.
Proof. intros cx m a _. reflexivity. Qed.
Lemma aabove_eq_trans : forall cx m1 m2 m3, aabove_eq cx m1 m2 -> aabove_eq cx m2 m3 -> aabove_eq cx m1 m3.
Proof. intros cx m1 m2 m3 H1 H2 a Ha. rewrite (H2 a Ha). apply H1. exact Ha. Qed.
Lemma aabove_eq_of_eq : forall cx (m m' : word -> option byte), (forall x, m' x = m x) -> aabove_eq cx m m'.
Proof. intros cx m m' H a _. unfold mbyte. rewrite H. reflexivity. Qed.
Lemma alzw_slots_kept : forall m m' cx, alzw_slots m cx -> aabove_eq cx m m' -> z_sp cx <= 2 ^ 47 -> alzw_slots m' cx.
Proof.
intros m m' cx H HA Hsp. unfold alzw_slots in *.
repeat match goal with |- _ /\ _ => split end;
lazymatch goal with |- val_mem _ _ ?a _ _ =>
intros k Hk; rewrite HA; [| cbn in Hk; lia];
repeat match type of H with _ /\ _ => first [apply (proj1 H); exact Hk | apply proj2 in H] end; apply H; exact Hk end.
Qed.
Lemma alzw_sslots_kept : forall m m' cx, alzw_sslots m cx -> aabove_eq cx m m' -> z_sp cx <= 2 ^ 47 -> alzw_sslots m' cx.
Proof.
intros m m' cx (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HA Hsp. unfold alzw_sslots.
repeat split; intros k Hk; (rewrite HA; [| cbn in Hk; lia]); [apply H1 | apply H2 | apply H3 | apply H4 | apply H5 | apply H6 | apply H7 | apply H8 | apply H9]; exact Hk.
Qed.
Lemma tlzw_frame_keptA : forall m m' cx regs0, tlzw_frame m (z_sp cx) regs0 -> aabove_eq cx m m' -> z_sp cx <= 2 ^ 47 -> tlzw_frame m' (z_sp cx) regs0.
Proof. intros m m' cx regs0 H HA Hsp. eapply tlzw_frame_agree; [exact H|]. intros a Ha. apply HA. lia. Qed.
Lemma ambyte_eq_of1 : forall (m m' : word -> option byte) a,
m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> mbyte SEGS m' a = mbyte SEGS m a.
Proof. intros m m' a H. unfold mbyte. rewrite H. reflexivity. Qed.
Lemma aframe_mbyte : forall E rs (m m' : word -> option byte) a,
frame_of E rs m m' -> 0 <= a < 2 ^ 64 ->
(forall r, In r rs -> ~ (base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r)) ->
mbyte SEGS m' a = mbyte SEGS m a.
Proof.
intros E rs m m' a HF Ha Hout. apply ambyte_eq_of1. apply HF.
rewrite unsigned_lit_small by exact Ha. intros (r & Hin & Hr). exact (Hout r Hin Hr).
Qed.
Fixpoint outsideA (l : list (Z * Z)) (a : Z) : Prop :=
match l with [] => True | (lo, hi) :: r => ~ (lo <= a < hi) /\ outsideA r a end.
Lemma aframe_mbyte_list : forall E rs (m m' : word -> option byte) (ws : list (Z * Z)) a,
frame_of E rs m m' -> 0 <= a < 2 ^ 64 ->
Forall2 (fun r w => YP09.r_whi r <= YP09.r_wlo r \/
(fst w <= base_val E (YP09.r_base r) + YP09.r_wlo r /\ base_val E (YP09.r_base r) + YP09.r_whi r <= snd w)) rs ws ->
outsideA ws a ->
mbyte SEGS m' a = mbyte SEGS m a.
Proof.
intros E rs m m' ws a HF Ha Hrw Hout. apply (aframe_mbyte E rs m m' a HF Ha). clear HF.
intros r Hin Hr. induction Hrw as [|r0 w0 rs0 ws0 Hr0 Hrw IH]; [destruct Hin|].
destruct w0 as [lo hi]. cbn [fst snd] in Hr0. destruct Hout as [Hn0 Hout].
destruct Hin as [<-|Hin]; [|exact (IH Hout Hin)]. lia.
Qed.
Lemma atables_at_frame : forall mem mem' cx X (Wr : Z -> Prop),
atables_at mem cx X -> lzw_inv (z_idl cx) (z_nP cx) X -> 0 <= z_idl cx -> acx_ranges cx ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> mbyte SEGS mem' a = mbyte SEGS mem a) ->
(forall a, z_ti cx <= a < z_ti cx + z_tisz cx -> ~ Wr a) ->
(forall a, z_lm cx <= a < z_lm cx + 8192 -> ~ Wr a) ->
(forall a, z_li cx <= a < z_li cx + 8192 -> ~ Wr a) ->
(forall a, z_tm cx <= a < z_tm cx + z_tmsz cx -> ~ Wr a) ->
atables_at mem' cx X.
Proof.
intros mem mem' cx [TI LM LI TM s lp dp mp Cn R] Wr (ATI & ALM & ALI & ATM) HI Hidl HRG Hfr Wti Wlm Wli Wtm.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HRG as (HR & _). cbn [ranges acx_tabs lzw_tabs app] in HR.
destruct HR as ((Rld1 & Rld2 & Rld3 & Rld4) & (Rti1 & Rti2 & Rti3 & Rti4) & (Rlm1 & Rlm2 & Rlm3 & _) & (Rlc1 & Rlc2 & Rlc3 & _) & (Rli1 & Rli2 & Rli3 & _) &
(Rtm1 & Rtm2 & Rtm3 & Rtm4) & _).
rewrite ?C1, ?C2, ?C3, ?C4 in *. clear C2 C3 C4 C5.
unfold z_tisz, z_tmsz in *.
destruct HI as (LenTI & LenLM & LenLI & LenTM & _).
split; [|split; [|split]]; (eapply arr16_frame; [eassumption|]); intros a Ha; cbn [la_TI la_LM la_LI la_TM] in Ha.
- rewrite LenTI, Z2Nat.id in Ha by nia. apply Hfr; [nia|]. apply Wti. lia.
- rewrite LenLM in Ha. cbn in Ha. apply Hfr; [lia|]. apply Wlm. lia.
- rewrite LenLI in Ha. cbn in Ha. apply Hfr; [lia|]. apply Wli. lia.
- rewrite LenTM, Z2Nat.id in Ha by nia. apply Hfr; [nia|]. apply Wtm. lia.
Qed.
Lemma agen_at_upd : forall m m' cx lp dp mp lp' dp' mp',
agen_at m cx lp dp mp ->
(forall a, z_ctx cx <= a < z_ctx cx + 60 -> mbyte SEGS m' a = mbyte SEGS m a) ->
val_mem SEGS m' (z_ctx cx + 60) 4 lp' -> val_mem SEGS m' (z_ctx cx + 64) 2 dp' -> val_mem SEGS m' (z_ctx cx + 66) 2 mp' ->
agen_at m' cx lp' dp' mp'.
Proof.
intros m m' cx lp dp mp lp' dp' mp' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _) Hfr Vlp Vdp Vmp.
unfold agen_at. repeat split; try assumption;
intros k Hk; (rewrite Hfr; [| cbn in Hk; lia]); first [apply H1 | apply H2 | apply H3 | apply H4 | apply H5 | apply H6 | apply H7 | apply H8]; exact Hk.
Qed.
Lemma val_mem_keptA : forall (m m' : word -> option byte) a n v,
val_mem SEGS m a n v -> (forall b, a <= b < a + Z.of_nat n -> mbyte SEGS m' b = mbyte SEGS m b) -> val_mem SEGS m' a n v.
Proof. intros m m' a n v H Hfr k Hk. rewrite Hfr by lia. apply H. exact Hk. Qed.
Lemma ast_ok_set_reg : forall E ss ms (r : bv 5) e,
st_ok_pi SEGS VAL E ss ms -> bv_eqb r 0 = false -> sv_denot E e = getr (ms_regs ms) r ->
st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r e HS Hr0 He. apply (st_ok_pi_set_reg E ss ms r e HS).
- intros X. rewrite X in Hr0. cbv in Hr0. discriminate Hr0.
- symmetry. exact He.
Qed.
Definition acx_tok (cx : lzw_acx) (bl0 : list (Z * Z)) : Prop :=
tok_inv LZW_TSTK (z_sp cx) [] bl0 [] ((z_ctx cx, 72) :: acx_tabs cx).
Definition atail_pc (cx : lzw_acx) (X' : lzw_abs) : Z := if la_s X' <? z_nP cx then PC_HEAD else PC_EPI.
Definition atail_post (cx : lzw_acx) (X : lzw_abs) (regs' : bvmap 5 word) (m' : word -> option byte) (X' : lzw_abs) : Prop :=
alzw_regs_head regs' cx /\ agen_at m' cx (la_lp X') (la_dp X') (la_mp X') /\ atables_at m' cx X' /\
lzw_inv (z_idl cx) (z_nP cx) X' /\ getr regs' 23 = w64 (la_s X') /\ la_s X < la_s X' <= z_nP cx.
Definition PC_RST1 : Z := 0x1ba4.
Definition PC_RST2 : Z := 0x1c64.
Definition arst_pre (full1 : bool) (cx : lzw_acx) (X : lzw_abs) (s' : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
alzw_regs_fix regs cx /\ getr regs 30 = w64 (z_ctx cx + 60) /\
getr regs (if full1 then 13%bv else 16%bv) = w64 (la_lp X) /\ getr regs (if full1 then 7%bv else 15%bv) = w64 (z_ti cx) /\
agen_at m cx (la_lp X + 1) (z_idl cx + 2) 1 /\ atables_at m cx X /\
lzw_inv (z_idl cx) (z_nP cx) X /\ la_dp X = 4096 /\
getr regs 23 = w64 s' /\ la_s X < s' < z_nP cx.
Definition ld4 (p k0 k1 : nat) : YP09.region :=
YP09.mkRegion (Some p) 0 4 0 4 [YP09.mkChunk 0 (CVal 2 (SOff k0 0)); YP09.mkChunk 2 (CVal 2 (SOff k1 0))].
Lemma region_ok_ld4 : forall E mem p k0 k1 a v0 v1,
ew E p = Z_to_bv 64 a -> ew E k0 = Z_to_bv 64 v0 -> ew E k1 = Z_to_bv 64 v1 -> 0 <= a -> a + 4 <= 2 ^ 64 ->
0 <= v0 < 65536 -> 0 <= v1 < 65536 ->
val_mem SEGS mem a 2 v0 -> val_mem SEGS mem (a + 2) 2 v1 -> (forall o, 0 <= o < 4 -> writable_at SEGS mem (a + o)) ->
region_ok SEGS E mem (ld4 p k0 k1).
Proof.
intros E mem p k0 k1 a v0 v1 Hp Hk0 Hk1 Ha Ha4 Hv0 Hv1 Hval0 Hval1 Hw. unfold region_ok, ld4.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite Hp, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hw; lia|].
constructor; [|constructor; [|constructor]].
- eapply chunk_ok_val; [| | cbn; lia | rewrite Z.add_0_r; exact Hval0]; [| change (2 ^ (8 * Z.of_N 2)) with 65536; lia].
cbn [sv_denot]. rewrite Hk0, Z.add_0_r, unsigned_lit_small by lia. reflexivity.
- eapply chunk_ok_val; [| | cbn; lia | exact Hval1]; [| change (2 ^ (8 * Z.of_N 2)) with 65536; lia].
cbn [sv_denot]. rewrite Hk1, Z.add_0_r, unsigned_lit_small by lia. reflexivity.
Qed.
Lemma cond_eq_U : forall E a b, U E a = U E b -> acond_ok E (mkAC BC_EQ a b).
Proof. intros E a b H. unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U. apply Z.eqb_eq. exact H. Qed.
Lemma cond_ne_U : forall E a b, U E a <> U E b -> acond_ok E (mkAC BC_NE a b).
Proof. intros E a b H. unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_ne_U. apply Bool.negb_true_iff. apply Z.eqb_neq. exact H. Qed.
Lemma U_dpfull12 : forall E nd dp,
ew E nd = Z_to_bv 64 dp -> 0 <= dp <= 4096 ->
U E (SAlu ALU_SRL (SOff nd 0) (SLit 12)) = (if dp =? 4096 then 1 else 0).
Proof.
intros E nd dp Hd Hr. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (Z.land (zcanon 12) 63) with 12.
rewrite (U_atom E nd dp Hd) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 12) with 4096.
destruct (Z.eqb_spec dp 4096) as [->|Hne]; [reflexivity|]. rewrite Z.div_small by lia. reflexivity.
Qed.
End f.
End d.
Ltac mem_eq_ro HF :=
lazymatch type of HF with frame_of _ _ ?m0 (ms_mem ?msx) =>
let EQM := fresh "EQM" in
assert (EQM : ms_mem msx = m0)
by (apply functional_extensionality; intros x; apply HF; intros (rg & Hin & Hrg); cbn in Hin;
repeat (destruct Hin as [<-|Hin]; [cbn in Hrg; lia|]); destruct Hin);
rewrite <- EQM in *; clear EQM HF end.
Ltac aregv HS r :=
let R := fresh "R" in
prreg HS r R; rewrite R; clear R; cbn [ew ewset Nat.eqb];
rewrite ?ew_ewset_other by lia;
repeat match goal with H : ew ?E ?n = Z_to_bv 64 _ |- context [ew ?E ?n] => rewrite H end;
unfold w64; rewrite ?unsigned_lit_small by lia; rewrite ?Z.add_0_r;
first [ reflexivity | f_equal; lia | match goal with |- ?g => idtac "AREGV" g end ].
Ltac septac HSEP i j :=
let Hs := fresh "Hs" in
pose proof (acx_sep _ HSEP i j ltac:(lia) ltac:(lia)) as Hs;
cbv [nth app acx_objs fst snd zz_disj z_tisz z_tmsz z_cap cap] in Hs.
Ltac oblk HJ HB HEn HE20 v :=
let L := getLAWS in
lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff ?n ?c)) ?len =>
first [ rewrite (U_atom_off Ex n v c); [| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact HEn | lia | lia]
| rewrite (U_atom Ex n v); [| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact HEn | lia] ];
eapply (obl_of_block _ _ L _ _ _ _ _ Ex (SOff 27 0) _ len _ _ (proj1 HJ) HB);
[ rewrite (U_atom Ex 27 SB); [reflexivity | cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact HE20 | unfold SB; lia]
| lia
| try change (req_size 72) with 72;
first [ lia | match goal with |- _ <= _ + req_size ?nn => pose proof (req_size_pos nn ltac:(lia)); lia end ] ]
end.
Ltac awr_tmp n b HEn Atmp HB :=
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ n b);
[ reflexivity
| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite HEn; apply unsigned_lit_small; lia
| cbn [YP09.r_wlo YP09.r_whi actx_region astk_region reg16 reg8 ld4 negb]; intros a Ha;
lazymatch type of Atmp with forall blc lyq i, In (?b0, _) blc -> _ -> _ =>
replace a with (b0 + (a - b0)) by lia; apply Atmp; [exact HB | lia] end
| ].
Ltac aUcond Hc :=
first [ rewrite branch_eq_U in Hc | rewrite branch_ne_U in Hc | rewrite branch_ltu_U in Hc | rewrite branch_geu_U in Hc ];
rewrite ?U_SOff, ?U_SLit in Hc; cbn [ew ewset Nat.eqb] in Hc; rewrite ?ew_ewset_other in Hc by lia;
repeat match goal with H : ew ?E ?n = Z_to_bv 64 _ |- _ => rewrite H in Hc end;
rewrite ?unsigned_lit_small in Hc by lia;
rewrite ?zcanon_id in Hc by (unfold M64; lia);
first [ apply Z.eqb_eq in Hc | apply Z.eqb_neq in Hc | apply Z.ltb_lt in Hc | apply Z.ltb_ge in Hc
| apply (proj1 (Bool.negb_true_iff _)) in Hc; first [apply Z.ltb_ge in Hc | apply Z.eqb_neq in Hc]
| apply (proj1 (Bool.negb_false_iff _)) in Hc; first [apply Z.ltb_lt in Hc | apply Z.eqb_eq in Hc] ].
