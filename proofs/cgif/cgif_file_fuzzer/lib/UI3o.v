(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YN32 YK0w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3b UN3c
YI06 UI5b YI09 YI08 YI0t YI0r YI0o UI3n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition tabove_eq (cx : lzw_tcx) (m m' : word -> option byte) : Prop :=
forall a, y_sp cx + 8 <= a < 2 ^ 64 -> mbyte ubs0segs m' a = mbyte ubs0segs m a.
Lemma tabove_eq_refl : forall cx m, tabove_eq cx m m.
Proof using. intros cx m a _. reflexivity. Qed.
Lemma tabove_eq_trans : forall cx m1 m2 m3, tabove_eq cx m1 m2 -> tabove_eq cx m2 m3 -> tabove_eq cx m1 m3.
Proof using. intros cx m1 m2 m3 H1 H2 a Ha. rewrite (H2 a Ha). apply H1. exact Ha. Qed.
Lemma tabove_eq_of_eq : forall cx (m m' : word -> option byte), (forall x, m' x = m x) -> tabove_eq cx m m'.
Proof using. intros cx m m' H a _. unfold mbyte. rewrite H. reflexivity. Qed.
Lemma gen_at_eq : forall m m' cx lp dp mp, gen_at m cx lp dp mp -> (forall x, m' x = m x) -> gen_at m' cx lp dp mp.
Proof using. intros m m' cx lp dp mp H Heq. eapply gen_at_frame; [exact H|]. intros a _. unfold mbyte. rewrite Heq. reflexivity. Qed.
Lemma ttables_at_eq : forall m m' cx X, ttables_at m cx X -> (forall x, m' x = m x) -> ttables_at m' cx X.
Proof using.
intros m m' cx X (H1 & H2 & H3 & H4) Heq.
split; [|split; [|split]]; (eapply arr16_frame; [eassumption|]); intros a _; unfold mbyte; rewrite Heq; reflexivity.
Qed.
Lemma ttables_at_frame : forall mem mem' cx X (W : Z -> Prop),
ttables_at mem cx X -> lzw_inv (y_idl cx) (y_nP cx) X -> 0 <= y_idl cx -> tcx_ranges cx ->
(forall a, 0 <= a < 2 ^ 64 -> ~ W a -> mbyte ubs0segs mem' a = mbyte ubs0segs mem a) ->
(forall a, y_ti cx <= a < y_ti cx + y_tisz cx -> ~ W a) ->
(forall a, y_lm cx <= a < y_lm cx + 8192 -> ~ W a) ->
(forall a, y_li cx <= a < y_li cx + 8192 -> ~ W a) ->
(forall a, y_tm cx <= a < y_tm cx + y_tmsz cx -> ~ W a) ->
ttables_at mem' cx X.
Proof using.
intros mem mem' cx [TI LM LI TM s lp dp mp Cn R] W (ATI & ALM & ALI & ATM) HI Hidl HRG Hfr Wti Wlm Wli Wtm.
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof HRG as ((Rti1 & Rti2 & Rti3 & Rti4) & (Rlm1 & Rlm2 & Rlm3 & _) & (Rlc1 & Rlc2 & Rlc3 & _) & (Rli1 & Rli2 & Rli3 & _) &
(Rtm1 & Rtm2 & Rtm3 & Rtm4) & (Rld1 & Rld2 & Rld3 & Rld4) & _).
unfold y_tisz, y_tmsz in *. cbn [fst snd] in Rti1, Rti2, Rti3, Rti4, Rtm1, Rtm2, Rtm3, Rtm4.
destruct HI as (LenTI & LenLM & LenLI & LenTM & _).
split; [|split; [|split]]; (eapply arr16_frame; [eassumption|]); intros a Ha; cbn [la_TI la_LM la_LI la_TM] in Ha.
- rewrite LenTI, Z2Nat.id in Ha by nia. apply Hfr; [lia|]. apply Wti. lia.
- rewrite LenLM in Ha. cbn in Ha. apply Hfr; [lia|]. apply Wlm. lia.
- rewrite LenLI in Ha. cbn in Ha. apply Hfr; [lia|]. apply Wli. lia.
- rewrite LenTM, Z2Nat.id in Ha by nia. apply Hfr; [lia|]. apply Wtm. lia.
Qed.
Lemma tst_ok_region_nth : forall E ss ms i r,
st_ok ubs0segs E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok ubs0segs E (ms_mem ms) r.
Proof using.
intros E ss ms i r HS Hi. destruct (st_ok_mem_ok ubs0segs E ss ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma tval_mem_of_chunk : forall E mem r p a off (n : BinNums.N) e v,
region_ok ubs0segs E mem r -> r_base r = Some p -> In (mkChunk off (CVal n e)) (r_chunks r) ->
bv_unsigned (ew E p) = a -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
val_mem ubs0segs mem (a + off) (N.to_nat n) v.
Proof using.
intros E mem r p a off n e v HR Hb Hin Hp He Hv Hn.
destruct HR as (_ & _ & _ & Hcs). pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc.
rewrite Hb in Hc. cbn [base_val] in Hc. rewrite Hp in Hc.
eapply val_of_chunk_ok; [exact Hc | exact He | exact Hv | exact Hn].
Qed.
Fixpoint outside (l : list (Z * Z)) (a : Z) : Prop :=
match l with [] => True | (lo, hi) :: r => ~ (lo <= a < hi) /\ outside r a end.
Lemma tframe_mbyte_list : forall E rs (m m' : word -> option byte) (ws : list (Z * Z)) a,
frame_of E rs m m' -> 0 <= a < 2 ^ 64 ->
Forall2 (fun r w => r_whi r <= r_wlo r \/ (fst w <= base_val E (r_base r) + r_wlo r /\ base_val E (r_base r) + r_whi r <= snd w)) rs ws ->
outside ws a ->
mbyte ubs0segs m' a = mbyte ubs0segs m a.
Proof using.
intros E rs m m' ws a HF Ha Hrw Hout. apply (tframe_mbyte E rs m m' a HF Ha). clear HF.
intros r Hin Hr. induction Hrw as [|r0 w0 rs0 ws0 Hr0 Hrw IH]; [destruct Hin|].
destruct w0 as [lo hi]. cbn [fst snd] in Hr0. destruct Hout as [Hn0 Hout].
destruct Hin as [<-|Hin]; [|exact (IH Hout Hin)]. lia.
Qed.
Lemma U_dpfull12 : forall E nd dp,
ew E nd = Z_to_bv 64 dp -> 0 <= dp <= 4096 ->
U E (SAlu ALU_SRL (SOff nd 0) (SLit 12)) = (if dp =? 4096 then 1 else 0).
Proof using.
intros E nd dp Hd Hr. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (Z.land (zcanon 12) 63) with 12.
rewrite (U_atom E nd dp Hd) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 12) with 4096.
destruct (Z.eqb_spec dp 4096) as [->|Hne]; [reflexivity|]. rewrite Z.div_small by lia. reflexivity.
Qed.
Definition ttail_post (cx : lzw_tcx) (X : lzw_abs) (regs' : bvmap 5 word) (mem' : word -> option byte) (X' : lzw_abs) : Prop :=
tlzw_regs_fix regs' cx /\ gen_at mem' cx (la_lp X') (la_dp X') (la_mp X') /\ ttables_at mem' cx X' /\
lzw_inv (y_idl cx) (y_nP cx) X' /\ getr regs' 22 = Z_to_bv 64 (la_s X') /\ la_s X < la_s X' <= y_nP cx.
Definition trst_pre (cx : lzw_tcx) (X : lzw_abs) (s' : Z) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
tlzw_regs_fix regs cx /\ gen_at mem cx (la_lp X + 1) (la_dp X) (la_mp X) /\ ttables_at mem cx X /\
lzw_inv (y_idl cx) (y_nP cx) X /\ la_dp X = 4096 /\
getr regs 22 = Z_to_bv 64 s' /\ la_s X < s' <= y_nP cx.
End b.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
