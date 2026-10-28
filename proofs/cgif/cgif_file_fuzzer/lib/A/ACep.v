(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0n YI0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v ACef AF0l ACej ACeh ACei.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Definition A_asan_memset : Z := 0x51a78.
Lemma st_ok_region_nth : forall E ss ms i r,
st_ok tfibsegs E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok tfibsegs E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. destruct (st_ok_mem_ok tfibsegs E ss ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma field_of_region : forall E m n b cs lo hi wlo whi od (w : N) e v,
region_ok tfibsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
val_mem tfibsegs m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok tfibsegs E m b od w e v Hck He Hv Hw).
Qed.
Section f.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Lemma awr_ok_cons_gen : forall E r rs STK sp0 FP bl0 blc ly own n b,
YP09.r_base r = Some n -> bv_unsigned (ew E n) = b ->
(forall a, b + YP09.r_wlo r <= a < b + YP09.r_whi r -> awr_byte STK sp0 FP bl0 blc ly own a) ->
awr_ok E rs STK sp0 FP bl0 blc ly own -> awr_ok E (r :: rs) STK sp0 FP bl0 blc ly own.
Proof.
intros E r rs STK sp0 FP bl0 blc ly own n b Hb Hn Hw H a (r' & [<-|Hin] & Ha).
- rewrite Hb in Ha. cbn [base_val] in Ha. rewrite Hn in Ha. apply Hw. exact Ha.
- apply H. exists r'. auto.
Qed.
Lemma aview_kept_frame : forall E rs H (m m' : word -> option byte) lo,
frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= lo ->
(forall a, lo <= a < 2 ^ 64 -> ~ in_wrange E rs a) ->
forall a, lo <= a < 2 ^ 64 -> aview tfibsegs H m' a = aview tfibsegs H m a.
Proof.
intros E rs H m m' lo HF Hlo Hno a Ha. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia. apply Hno. exact Ha.
Qed.
Lemma writable_kept : forall H (m m2 : word -> option byte) a,
(apresent H m a -> apresent H m2 a) -> writable_at tfibsegs (mrestrict H m) a -> writable_at tfibsegs (mrestrict H m2) a.
Proof.
intros H m m2 a Hp Hw. unfold writable_at, wview, mrestrict in *. revert Hw.
destruct (H (Z_to_bv 64 a)) eqn:EH; intros Hw; [exact Hw|].
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
- destruct (Hp (conj EH (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
- destruct (m2 (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
Lemma region_kept_aview : forall E H (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview tfibsegs H m2 a = aview tfibsegs H m a) ->
(forall a, apresent H m a -> apresent H m2 a) ->
region_kept tfibsegs E (mrestrict H m) (mrestrict H m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview tfibsegs). apply Hav. exact Ha.
- apply writable_kept. apply Hp.
Qed.
Lemma val_mem_zero8 : forall H (m : word -> option byte) a,
(forall i, 0 <= i < 8 -> aview tfibsegs H m (a + i) = Some 0) -> val_mem tfibsegs (mrestrict H m) a 8 0.
Proof.
intros H m a Hz j Hj. destruct (aview_byte tfibsegs H m (a + Z.of_nat j) 0 (Hz (Z.of_nat j) ltac:(lia))) as (b & Hb & Hv & _).
rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
repeat (rewrite Z.shiftr_0_l || rewrite Z.mod_0_l by ((first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate]))). lia.
Qed.
End f.
End d.
Ltac reseat HS HJ2 HP2 keep AG kept_tac :=
let K := lazymatch type of HS with st_ok _ _ ?ss _ => eval vm_compute in (run_K 0 (SOff 32 0) [] ss) end in
let HS2 := fresh "HS2" in
lazymatch type of HJ2 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?W2 ?mem2 _ _ =>
lazymatch type of HP2 with aregs_preserved _ ?regs2 =>
jafter_call_keep HS K regs2 (mrestrict (w_H W2) mem2) HP2 keep HS2 end end;
match type of HS2 with ?Q -> _ =>
let HQ := fresh "HQ" in
assert (HQ : Q); [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil; kept_tac | specialize (HS2 HQ); clear HQ ] end;
clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS;
let AG2 := fresh "AG" in let Ev := fresh "E" in let HEv := fresh "HE" in
lazymatch type of AG with forall n, _ -> _ = ew ?E0 n =>
lazymatch type of HS with st_ok _ ?Enew _ _ =>
remember Enew as Ev eqn:HEv in HS;
assert (AG2 : forall n, (n < 33)%nat -> ew Ev n = ew E0 n)
by (intros nn Hnn; rewrite HEv; rewrite ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; apply AG; exact Hnn);
repeat match goal with H : ew ?Eo ?n = ?v |- _ =>
lazymatch Eo with
| Ev => fail
| _ => lazymatch (eval cbv in (Nat.leb 33 n)) with
| true => let H2 := fresh H in
assert (H2 : ew Ev n = v) by (rewrite HEv; rewrite ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; exact H);
clear H; rename H2 into H
end end end;
clear HEv AG; rename AG2 into AG end end.
Ltac reshok_bx HS bx :=
try match goal with H : sh_ok _ _ _ _ _ |- _ => clear H end;
lazymatch type of HS with st_ok _ ?Ex _ (restrict (w_H ?Wx) ?msx) =>
let SH := fresh "SHOK" in
shok_auto SH (SOff bx 0) Ex (mrestrict (w_H Wx) (ms_mem msx)) end.
Ltac norm_ss HS := lazymatch type of HS with st_ok _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
Lemma low_byte_mod : forall u n k, 0 <= u -> (k < n)%nat ->
Z_to_bv 8 (Z.shiftr (u mod 2 ^ (8 * Z.of_nat n)) (8 * Z.of_nat k)) = Z_to_bv 8 (Z.shiftr u (8 * Z.of_nat k)).
Proof.
intros u n k Hu Hk. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with (2 ^ 8).
apply Z.bits_inj'. intros i Hi.
destruct (Z_lt_le_dec i 8) as [Hl|Hge].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma val_of_chunk_any : forall segs E mem base off (n : N) (e : sv),
YP09.chunk_ok segs E mem base (YP09.mkChunk off (CVal n e)) -> (Z.of_N n <= 8) ->
val_mem segs mem (base + off) (N.to_nat n) (bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N n)).
Proof.
intros segs E mem base off n e H Hn k Hk. unfold YP09.chunk_ok in H. cbn [YP09.c_off YP09.c_val c_len cv_len] in H.
pose proof (N_nat_Z n) as Hnn.
destruct (H (Z.of_nat k) ltac:(lia)) as (b & Hb1 & Hb2). cbn [cbyte] in Hb1. unfold YP09.byte_of_word in Hb1.
injection Hb1 as <-. rewrite Hb2. f_equal.
pose proof (bv_unsigned_in_range 64 (sv_denot E e)) as Hu. change (bv_modulus 64) with (2 ^ 64) in Hu.
set (u := bv_unsigned (sv_denot E e)) in *.
assert (Hm : 0 <= u mod 2 ^ (8 * Z.of_N n) < 2 ^ (8 * Z.of_nat (N.to_nat n))).
{ rewrite Hnn. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. }
rewrite (le_byte_small _ _ _ Hm Hk). rewrite <- Hnn. symmetry. apply low_byte_mod; [lia | exact Hk].
Qed.
Lemma field_of_region_any : forall E m n b cs lo hi wlo whi od (w : N) e,
region_ok tfibsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> (Z.of_N w <= 8) ->
val_mem tfibsegs m (b + od) (N.to_nat w) (bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N w)).
Proof.
intros E m n b cs lo hi wlo whi od w e (_ & _ & _ & Hcs) Hn Hc Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_any tfibsegs E m b od w e Hck Hw).
Qed.
Section g.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Variable B : asyms.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Lemma region_kept_frame_sub : forall E STK1 sp1 FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 n b lo hi wlo whi cs cid pos,
ajournal tfibsegs B STK1 sp1 FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
bv_unsigned (ew E n) = b -> In (cid, pos) (frames Sc) ->
frame_addr lyc cid pos <= b + lo -> b + hi <= frame_addr lyc cid pos + fs_frame_bytes cid ->
(forall a, b + lo <= a < b + hi -> ~ inFP FP1 a) ->
(forall a, b + wlo <= a < b + whi -> apresent (w_H W2) mem2 a) ->
region_kept tfibsegs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E STK1 sp1 FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 n b lo hi wlo whi cs cid pos HJ1 Hn Hin Hlo Hhi HnF Hp2.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K4 & _).
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview tfibsegs). apply (K4 cid pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | apply HnF; exact Ha].
- intros _. apply (apresent_writable tfibsegs). apply Hp2. lia.
Qed.
Lemma region_kept_fshadow_sub : forall E STK1 sp1 FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 n b lo hi wlo whi cs cid pos,
ajournal tfibsegs B STK1 sp1 FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
bv_unsigned (ew E n) = b -> In (cid, pos) (frames Sc) ->
shadow_addr (frame_addr lyc cid pos) <= b + lo -> b + hi <= shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8 ->
(forall a, b + lo <= a < b + hi -> ~ inFP FP1 a) ->
(forall a, b + wlo <= a < b + whi -> apresent (w_H W2) mem2 a) ->
region_kept tfibsegs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E STK1 sp1 FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 n b lo hi wlo whi cs cid pos HJ1 Hn Hin Hlo Hhi HnF Hp2.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K4 & _).
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview tfibsegs). apply (K4 cid pos a Hin); [right; unfold in_zr; cbn [fst snd]; lia | apply HnF; exact Ha].
- intros _. apply (apresent_writable tfibsegs). apply Hp2. lia.
Qed.
End h.
End g.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Definition A_asan_memcpy : Z := 0x515dc.
Section l.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma denot_shx : forall E n m c v sb, ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 sb -> 0 <= v -> 0 <= c -> v + c < 2 ^ 63 -> 0 <= sb < 2 ^ 32 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff m 0)) = Z_to_bv 64 (sb + (v + c) / 8).
Proof.
intros E n m c v sb Hn Hm Hv Hc0 Hc Hsb.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff m 0)))). f_equal.
change (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff m 0)) = sb + (v + c) / 8).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, Hn, Hm. rewrite !unsigned_lit_small by lia. rewrite Z.add_0_r.
change (Z.land (U E (SLit 3)) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos (v + c) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (v + c) 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
rewrite (zcanon_small (v + c)) by lia. rewrite (zcanon_small ((v + c) / 8)) by lia. rewrite (zcanon_small sb) by lia. rewrite zcanon_small by lia. lia.
Qed.
Section o.
Variable B : asyms.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Let HBgot := tl_got_shadow B TL.
Let HBcell := tl_shadow_cell B TL.
Lemma kept_of_frame : forall E rs H (m m' : word -> option byte) (Zs : Z -> Prop),
frame_of E rs (mrestrict H m) (mrestrict H m') ->
(forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> Zs a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview tfibsegs H m' a = aview tfibsegs H m a.
Proof.
intros E rs H m m' Zs HFR Hw a Ha Hn. apply (aview_eq_of tfibsegs). apply HFR. rewrite unsigned_lit_small by lia.
intros Hin. destruct (in_wrange_windows E rs a Hin) as (b & wlo & whi & Hi & Hr). exact (Hn (Hw b wlo whi a Hi Hr)).
Qed.
End o.
End l.
