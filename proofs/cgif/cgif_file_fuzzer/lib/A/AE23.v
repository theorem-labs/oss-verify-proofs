(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v YO0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AE34 AF0l AF0m AE3e AE3f AE3g AE6g AE2p AE3i AE3h AE3m AE22 AF0x AE20 AE2y AE7f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Notation tfibtbl_x := tfibmusl_tbl (only parsing).
Notation tfibtbl_x_ok := tfibmusl_tbl_ok (only parsing).
Definition A_exit : Z := 0x8d604.
Definition TFIB_TPX : Z := 0x5d8f90.
Definition F_STDIN : Z := 0xa2758.
Definition X1_PC : Z := 0x6fa50.  Definition X1_RA : Z := 0x8d4a0.  Definition OSP_X1 : Z := -64.
Definition X2_PC : Z := 0x813d4. Definition X3_PC : Z := 0x30398.   Definition X23_RA : Z := 0x8d5e8. Definition OSP_X23 : Z := -48.
Definition XW1 (a : Z) : Prop := False.
Definition XW2 (a : Z) : Prop := (0xa2940 <= a < 0xa2948) \/ (0xa38b0 <= a < 0xa38b8) \/
(0x7fffc1c0 <= a < 0x7fffc1c4) \/ (0x7fffc1cc <= a < 0x7fffc1d0) \/ (0x7fffc1d4 <= a < 0x7fffc1d8) \/ (0x8000c50e <= a < 0x8000c526).
Definition XW3 (a : Z) : Prop := a = 0xa2990.
Definition XTRUE (W : world tfibsegs) (m : word -> option byte) : Prop := True.
Definition X3PRE (W : world tfibsegs) (m : word -> option byte) : Prop :=
val_mem tfibsegs (mrestrict (w_H W) m) 0x9df68 8 0x8d4e8 /\ val_mem tfibsegs (mrestrict (w_H W) m) 0x9df70 8 0.
Definition ex_consts : list (Z * N * Z) :=
[(0x9ec68, 8%N, 0x9da30); (0x9ec70, 8%N, 0x9da20); (0x9da20, 8%N, 0x813d4); (0x9da28, 8%N, 0x30398);
(0x9df68, 8%N, 0x8d4e8); (0x9df70, 8%N, 0);
(0xa2660, 8%N, F_STDERR); (0xa2750, 8%N, F_STDOUT); (0xa2840, 8%N, F_STDIN);
(0x5f8fe0, 1%N, 0); (0x5f8fe4, 4%N, 0); (0x5f8fe8, 4%N, 2); (0x5f8ff0, 8%N, 0x5f8ff8); (0x5f8ff8, 8%N, 0);
(0x5f9000, 8%N, 0x8d5b0); (0x5f9008, 8%N, 0x8d5b0); (0x5f9100, 8%N, 0x6fa50); (0x5f9108, 8%N, 0x80418); (0x5d8654, 1%N, 0);
(0x5f9200, 4%N, 0); (0x5f9223, 1%N, 0); (0x5f9680, 4%N, 0); (0x5f9688, 8%N, 0);
(F_STDIN + 8, 8%N, 0); (F_STDIN + 16, 8%N, 0); (F_STDIN + 40, 8%N, 0); (F_STDIN + 56, 8%N, 0); (F_STDIN + 140, 4%N, 0xffffffff);
(F_STDERR + 8, 8%N, 0); (F_STDERR + 16, 8%N, 0); (F_STDERR + 140, 4%N, 0xffffffff)].
Definition ex_consts1 : list (Z * N * Z) :=
[(0x9ec68, 8%N, 0x9da30); (0x9ec70, 8%N, 0x9da20); (0x9da20, 8%N, 0x813d4); (0x9da28, 8%N, 0x30398);
(0x9df68, 8%N, 0x8d4e8); (0x9df70, 8%N, 0);
(0xa2660, 8%N, F_STDERR); (0xa2750, 8%N, F_STDOUT); (0xa2840, 8%N, F_STDIN);
(0x5f8fe0, 1%N, 0); (0x5f8fe4, 4%N, 0); (0x5f8fe8, 4%N, 1); (0x5f8ff0, 8%N, 0x5f8ff8); (0x5f8ff8, 8%N, 0);
(0x5f9000, 8%N, 0x8d5b0); (0x5f9100, 8%N, 0x6fa50); (0x5d8654, 1%N, 0);
(0x5f9200, 4%N, 0); (0x5f9223, 1%N, 0); (0x5f9680, 4%N, 0); (0x5f9688, 8%N, 0);
(F_STDIN + 8, 8%N, 0); (F_STDIN + 16, 8%N, 0); (F_STDIN + 40, 8%N, 0); (F_STDIN + 56, 8%N, 0); (F_STDIN + 140, 4%N, 0xffffffff);
(F_STDERR + 8, 8%N, 0); (F_STDERR + 16, 8%N, 0); (F_STDERR + 140, 4%N, 0xffffffff)].
Definition cells_are (l : list (Z * N * Z)) (m : word -> option byte) : Prop :=
Forall (fun f => match f with (a, n, v) => val_mem tfibsegs m a (N.to_nat n) v end) l.
Definition ex_cell_range (tp a : Z) : Prop :=
vo_file a \/ vf_file a \/ (F_STDIN <= a < F_STDIN + FILE_SZ) \/
(A_canary <= a < A_canary + 8) \/ (0x9ec68 <= a < 0x9ec78) \/ (0x9da20 <= a < 0x9da30) \/ (0x9df68 <= a < 0x9df78) \/
(0xa2660 <= a < 0xa2668) \/ (0xa2750 <= a < 0xa2758) \/ (0xa2840 <= a < 0xa2848) \/
(0x5f8fe0 <= a < 0x5f9110) \/ (0x5d8654 <= a < 0x5d8655) \/ (0x5f9200 <= a < 0x5f9204) \/ (0x5f9223 <= a < 0x5f9224) \/ (0x5f9680 <= a < 0x5f9690) \/
(tp - 168 <= a < tp - 164).
Definition cellr (a : Z) (n : N) (v : sv) (w : bool) : YP09.region :=
YP09.mkRegion None a (a + Z.of_N n) a (if w then a + Z.of_N n else a) [YP09.mkChunk a (CVal n v)].
Definition ex_regions (fo : list YP09.chunk) : smem :=
[ YP09.mkRegion (Some 2%nat) (- VF_STK) 0 (- VF_STK) 0 [];
YP09.mkRegion None F_STDOUT (F_STDOUT + FILE_SZ) F_STDOUT (F_STDOUT + FILE_SZ) fo;
YP09.mkRegion None F_STDERR (F_STDERR + FILE_SZ) F_STDERR (F_STDERR + FILE_SZ)
[YP09.mkChunk (F_STDERR + 8) (CVal 8 (SLit 0)); YP09.mkChunk (F_STDERR + 16) (CVal 8 (SLit 0));
YP09.mkChunk (F_STDERR + 40) (CVal 8 (SOff 35 0)); YP09.mkChunk (F_STDERR + 56) (CVal 8 (SOff 35 0));
YP09.mkChunk (F_STDERR + 140) (CVal 4 (SLit 0xffffffff))];
YP09.mkRegion None F_STDIN (F_STDIN + FILE_SZ) F_STDIN F_STDIN
[YP09.mkChunk (F_STDIN + 8) (CVal 8 (SLit 0)); YP09.mkChunk (F_STDIN + 16) (CVal 8 (SLit 0));
YP09.mkChunk (F_STDIN + 40) (CVal 8 (SLit 0)); YP09.mkChunk (F_STDIN + 56) (CVal 8 (SLit 0));
YP09.mkChunk (F_STDIN + 140) (CVal 4 (SLit 0xffffffff))];
cellr A_GOT_canary 8 (SLit A_canary) false;
cellr A_canary 8 (SOff 33 0) false;
YP09.mkRegion None 0x9ec68 0x9ec78 0x9ec68 0x9ec68 [YP09.mkChunk 0x9ec68 (CVal 8 (SLit 0x9da30)); YP09.mkChunk 0x9ec70 (CVal 8 (SLit 0x9da20))];
YP09.mkRegion None 0x9da20 0x9da30 0x9da20 0x9da20 [YP09.mkChunk 0x9da20 (CVal 8 (SLit 0x813d4)); YP09.mkChunk 0x9da28 (CVal 8 (SLit 0x30398))];
YP09.mkRegion None 0x9df68 0x9df78 0x9df68 0x9df68 [YP09.mkChunk 0x9df68 (CVal 8 (SLit 0x8d4e8)); YP09.mkChunk 0x9df70 (CVal 8 (SLit 0))];
cellr 0xa2660 8 (SLit F_STDERR) false;
cellr 0xa2750 8 (SLit F_STDOUT) false;
cellr 0xa2840 8 (SLit F_STDIN) false;
YP09.mkRegion None 0x5f8fe0 0x5f9110 0x5f8fe0 0x5f9110
[YP09.mkChunk 0x5f8fe0 (CVal 1 (SLit 0)); YP09.mkChunk 0x5f8fe4 (CVal 4 (SLit 0)); YP09.mkChunk 0x5f8fe8 (CVal 4 (SLit 2));
YP09.mkChunk 0x5f8ff0 (CVal 8 (SLit 0x5f8ff8)); YP09.mkChunk 0x5f8ff8 (CVal 8 (SLit 0));
YP09.mkChunk 0x5f9000 (CVal 8 (SLit 0x8d5b0)); YP09.mkChunk 0x5f9008 (CVal 8 (SLit 0x8d5b0));
YP09.mkChunk 0x5f9100 (CVal 8 (SLit 0x6fa50)); YP09.mkChunk 0x5f9108 (CVal 8 (SLit 0x80418))];
cellr 0x5f9200 4 (SLit 0) true;
cellr 0x5f9223 1 (SLit 0) false;
cellr 0x5d8654 1 (SLit 0) false;
YP09.mkRegion None 0x5f9680 0x5f9690 0x5f9680 0x5f9680 [YP09.mkChunk 0x5f9680 (CVal 4 (SLit 0)); YP09.mkChunk 0x5f9688 (CVal 8 (SLit 0))];
YP09.mkRegion (Some 4%nat) (-168) (-164) (-168) (-168) [YP09.mkChunk (-168) (CVal 4 (SOff 32 0))] ].
Definition ex_regions1 (fo : list YP09.chunk) : smem :=
[ YP09.mkRegion (Some 2%nat) (- VF_STK) 0 (- VF_STK) 0 [];
YP09.mkRegion None F_STDOUT (F_STDOUT + FILE_SZ) F_STDOUT (F_STDOUT + FILE_SZ) fo;
YP09.mkRegion None F_STDERR (F_STDERR + FILE_SZ) F_STDERR (F_STDERR + FILE_SZ)
[YP09.mkChunk (F_STDERR + 8) (CVal 8 (SLit 0)); YP09.mkChunk (F_STDERR + 16) (CVal 8 (SLit 0));
YP09.mkChunk (F_STDERR + 40) (CVal 8 (SOff 35 0)); YP09.mkChunk (F_STDERR + 56) (CVal 8 (SOff 35 0));
YP09.mkChunk (F_STDERR + 140) (CVal 4 (SLit 0xffffffff))];
YP09.mkRegion None F_STDIN (F_STDIN + FILE_SZ) F_STDIN F_STDIN
[YP09.mkChunk (F_STDIN + 8) (CVal 8 (SLit 0)); YP09.mkChunk (F_STDIN + 16) (CVal 8 (SLit 0));
YP09.mkChunk (F_STDIN + 40) (CVal 8 (SLit 0)); YP09.mkChunk (F_STDIN + 56) (CVal 8 (SLit 0));
YP09.mkChunk (F_STDIN + 140) (CVal 4 (SLit 0xffffffff))];
cellr A_GOT_canary 8 (SLit A_canary) false;
cellr A_canary 8 (SOff 33 0) false;
YP09.mkRegion None 0x9ec68 0x9ec78 0x9ec68 0x9ec68 [YP09.mkChunk 0x9ec68 (CVal 8 (SLit 0x9da30)); YP09.mkChunk 0x9ec70 (CVal 8 (SLit 0x9da20))];
YP09.mkRegion None 0x9da20 0x9da30 0x9da20 0x9da20 [YP09.mkChunk 0x9da20 (CVal 8 (SLit 0x813d4)); YP09.mkChunk 0x9da28 (CVal 8 (SLit 0x30398))];
YP09.mkRegion None 0x9df68 0x9df78 0x9df68 0x9df68 [YP09.mkChunk 0x9df68 (CVal 8 (SLit 0x8d4e8)); YP09.mkChunk 0x9df70 (CVal 8 (SLit 0))];
cellr 0xa2660 8 (SLit F_STDERR) false;
cellr 0xa2750 8 (SLit F_STDOUT) false;
cellr 0xa2840 8 (SLit F_STDIN) false;
YP09.mkRegion None 0x5f8fe0 0x5f9110 0x5f8fe0 0x5f9110
[YP09.mkChunk 0x5f8fe0 (CVal 1 (SLit 0)); YP09.mkChunk 0x5f8fe4 (CVal 4 (SLit 0)); YP09.mkChunk 0x5f8fe8 (CVal 4 (SLit 1));
YP09.mkChunk 0x5f8ff0 (CVal 8 (SLit 0x5f8ff8)); YP09.mkChunk 0x5f8ff8 (CVal 8 (SLit 0));
YP09.mkChunk 0x5f9000 (CVal 8 (SLit 0x8d5b0));
YP09.mkChunk 0x5f9100 (CVal 8 (SLit 0x6fa50))];
cellr 0x5f9200 4 (SLit 0) true;
cellr 0x5f9223 1 (SLit 0) false;
cellr 0x5d8654 1 (SLit 0) false;
YP09.mkRegion None 0x5f9680 0x5f9690 0x5f9680 0x5f9680 [YP09.mkChunk 0x5f9680 (CVal 4 (SLit 0)); YP09.mkChunk 0x5f9688 (CVal 8 (SLit 0))];
YP09.mkRegion (Some 4%nat) (-168) (-164) (-168) (-168) [YP09.mkChunk (-168) (CVal 4 (SOff 32 0))] ].
Definition ex_facts0 : facts := mkFacts [ (2%nat, mkAF (2 ^ 44) (2 ^ 47) 4) ] [] [].
Definition ex_factsF : facts := mkFacts [ (2%nat, mkAF (2 ^ 44) (2 ^ 47) 4); (34%nat, mkAF (STDOUT_BUFA + 1) (STDOUT_BUFA + STDOUT_BSZ) 0) ] [] [].
Definition ss_exP : sstate := mkSS A_exit sr_atoms (ex_regions (fo_chunks stdout_fields0)) None ex_facts0.
Definition ss_exP1 : sstate := mkSS A_exit sr_atoms (ex_regions1 (fo_chunks stdout_fields0)) None ex_facts0.
Definition ss_exE : sstate := mkSS A_exit sr_atoms (ex_regions (YP09.mkChunk (F_STDOUT + 40) (CVal 8 (SLit STDOUT_BUFA)) :: fo_chunks stdout_fields1)) None ex_facts0.
Definition ss_exF : sstate := mkSS A_exit sr_atoms (ex_regions (YP09.mkChunk (F_STDOUT + 40) (CVal 8 (SOff 34 0)) :: fo_chunks stdout_fields1)) None ex_factsF.
Definition exm (a : Z) : Prop := vo_file a \/ vf_file a \/ (0x5f8fe0 <= a < 0x5f9110) \/ (0x5f9200 <= a < 0x5f9204).
Lemma exm_img_bytes_ok1 : zallb (img_byte_ok tfibsegs) 0x5f8fe0 (Z.to_nat 0x130) = true. Proof. vm_compute. reflexivity. Qed.
Lemma exm_img_bytes_ok2 : zallb (img_byte_ok tfibsegs) 0x5f9200 4%nat = true. Proof. vm_compute. reflexivity. Qed.
Lemma exm_img : forall a, exm a -> img_byte_ok tfibsegs a = true.
Proof.
intros a [H|[H|[H|H]]].
- unfold vo_file in H. exact (zallb_sound _ _ _ a stdout_img_bytes_ok ltac:(unfold FILE_SZ in *; lia)).
- unfold vf_file in H. exact (zallb_sound _ _ _ a stderr_img_bytes_ok ltac:(unfold FILE_SZ in *; lia)).
- exact (zallb_sound _ _ _ a exm_img_bytes_ok1 ltac:(lia)).
- exact (zallb_sound _ _ _ a exm_img_bytes_ok2 ltac:(lia)).
Qed.
Lemma exm_dec : forall a, exm a \/ ~ exm a.
Proof. intros a. unfold exm, vo_file, vf_file. lia. Qed.
Definition exw_ok (t : option nat * Z * Z) : bool :=
band_winb t || win_eqb t (None, F_STDOUT, F_STDOUT + FILE_SZ) || win_eqb t (None, F_STDERR, F_STDERR + FILE_SZ)
|| win_eqb t (None, 0x5f8fe0, 0x5f9110) || win_eqb t (None, 0x5f9200, 0x5f9204) || (snd t <=? snd (fst t)).
Definition ex_windows_ok (ss : sstate) : bool := forallb exw_ok (windows (ss_mem ss)).
Lemma ex_windows_sound : forall E ss sp0 a,
ex_windows_ok ss = true -> bv_unsigned (ew E 2) = sp0 ->
in_wrange E (ss_mem ss) a -> vf_band sp0 a \/ exm a.
Proof.
intros E ss sp0 a Hb Hsp Hin.
destruct (in_wrange_windows E _ a Hin) as (b & lo & hi & Ht & Hr).
unfold ex_windows_ok in Hb. rewrite forallb_forall in Hb. specialize (Hb _ Ht). unfold exw_ok in Hb.
repeat (apply orb_prop in Hb as [Hb|Hb]).
- unfold band_winb in Hb. destruct b as [[|[|[|n]]]|]; try discriminate Hb.
apply andb_prop in Hb as [H1 H2]. apply Z.eqb_eq in H1. apply Z.leb_le in H2. subst lo.
cbn [base_val] in Hr. rewrite Hsp in Hr. left. unfold vf_band. lia.
- apply win_eqb_eq in Hb. injection Hb as -> -> ->. cbn [base_val] in Hr. right. unfold exm, vo_file. lia.
- apply win_eqb_eq in Hb. injection Hb as -> -> ->. cbn [base_val] in Hr. right. unfold exm, vf_file. lia.
- apply win_eqb_eq in Hb. injection Hb as -> -> ->. cbn [base_val] in Hr. right. unfold exm. lia.
- apply win_eqb_eq in Hb. injection Hb as -> -> ->. cbn [base_val] in Hr. right. unfold exm. lia.
- cbn [fst snd] in Hb. apply Z.leb_le in Hb. lia.
Qed.
Section VX.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (sp0 : Z) (mem0 : word -> option byte) (md0 : Model).
Variable mut : Z -> Prop.
Hypothesis Hmut_img : forall a, mut a -> img_byte_ok tfibsegs a = true.
Hypothesis Hmut_dec : forall a, mut a \/ ~ mut a.
Hypothesis HFown : forall a, mut a -> ~ aowned B ly S a.
Variable xs : Z -> Prop.
Hypothesis Hstk : ly_stk_lo ly + VF_STK <= sp0.
Hypothesis Htop : sp0 <= ly_stk_hi ly.
Definition VX (mem : word -> option byte) (md : Model) : Prop :=
AR tfibsegs B ly S W mem md /\ same_but_materialized md0 md /\
(forall a, vf_band sp0 a -> apresent (w_H W) mem a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_band sp0 a -> ~ mut a -> ~ xs a -> aview tfibsegs (w_H W) mem a = aview tfibsegs (w_H W) mem0 a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ mut a -> ~ xs a -> apresent (w_H W) mem0 a -> apresent (w_H W) mem a).
Lemma VX_init : AR tfibsegs B ly S W mem0 md0 -> (forall a, vf_band sp0 a -> apresent (w_H W) mem0 a) -> VX mem0 md0.
Proof.
intros HAR Hp. split; [exact HAR|]. split; [apply same_but_materialized_refl|]. split; [exact Hp|].
split; [intros; reflexivity | intros a _ _ _ Ha; exact Ha].
Qed.
Lemma VX_run : forall mem md memB mat,
VX mem md ->
(forall x : word, ~ vf_band sp0 (bv_unsigned x) -> ~ mut (bv_unsigned x) -> memB x = mem x) ->
(forall x : word, ~ vf_band sp0 (bv_unsigned x) -> ~ mut (bv_unsigned x) -> mrestrict (w_H W) memB x = mrestrict (w_H W) mem x) ->
(forall a, vf_band sp0 a -> apresent (w_H W) memB a) ->
VX memB (with_vm_backing (m_vm_lazy md) mat md).
Proof.
intros mem md memB mat (HAR & Hsbm & Hpb & Hfr & Hpm) HF HFr HpbB.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
assert (HVF : VF_STK = 9104) by reflexivity.
assert (AVB : forall a, 0 <= a < 2 ^ 64 -> ~ vf_band sp0 a -> ~ mut a -> aview tfibsegs (w_H W) memB a = aview tfibsegs (w_H W) mem a).
{ intros a Hr H1 H2. apply aview_eq_of. apply HFr; rewrite unsigned_lit_small by lia; assumption. }
pose proof (same_but_materialized_frame md _ (with_vm_backing_same md mat)) as MF.
split; [|split; [|split; [exact HpbB | split]]].
- apply (al_frame _ _ LAWS ly S W mem md memB _ HAR).
+ intros a Hr Hown. apply AVB; [exact Hr | |].
* intros Hb. exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(unfold vf_band in Hb; lia) Hown).
* intros Hf. exact (HFown a Hf Hown).
+ assert (PV : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) mem a <> None -> aview tfibsegs (w_H W) memB a <> None).
{ intros a Hr Hv.
assert (CASE : vf_band sp0 a \/ mut a \/ (~ vf_band sp0 a /\ ~ mut a)).
{ destruct (Hmut_dec a) as [Hm|Hm]; [right; left; exact Hm|]. assert (D : vf_band sp0 a \/ ~ vf_band sp0 a) by (unfold vf_band; lia). tauto. }
destruct CASE as [Hin | [Hin | [Ho1 Ho2]]].
* apply aview_some_of_apresent. apply HpbB. exact Hin.
* unfold aview, mbyte. destruct (mrestrict (w_H W) memB (Z_to_bv 64 a)) as [b|]; [cbn; discriminate|].
pose proof (Hmut_img a Hin) as Hb.
unfold img_byte_ok, img_byte in Hb. destruct (seg_rom tfibsegs (Z_to_bv 64 a)); [cbn; discriminate | discriminate Hb].
* rewrite AVB; assumption. }
intros a Hv. rewrite (aview_mod _ memB a). apply PV; [apply Z.mod_pos_bound; lia | rewrite <- aview_mod; exact Hv].
+ apply MF. + apply MF. + apply MF.
+ intros a Ha Hh. unfold YG0d.w64 in Hh. unfold YG0d.w64.     destruct (Hmut_dec a) as [Hmt|Hmt].
* exfalso. pose proof (Hmut_img a Hmt) as Hb. unfold img_byte_ok, img_byte in Hb. rewrite (seg_rom_none_band a Ha) in Hb. discriminate Hb.
* assert (CASE : vf_band sp0 a \/ ~ vf_band sp0 a) by (unfold vf_band; lia).
destruct CASE as [Hin|Hout]; [exfalso; destruct (Hpb a Hin) as [Hf _]; rewrite Hf in Hh; discriminate Hh|].
rewrite HF; [reflexivity | |]; rewrite unsigned_lit_small by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; lia); assumption.
- eapply same_but_materialized_trans; [exact Hsbm | apply with_vm_backing_same].
- intros a Hr H1 H2 H3. rewrite AVB by assumption. apply Hfr; assumption.
- intros a Hr Hf Hx Hp.
assert (CASE : vf_band sp0 a \/ ~ vf_band sp0 a) by (unfold vf_band; lia).
destruct CASE as [Hin | Hout]; [apply HpbB; exact Hin|].
destruct (Hpm a Hr Hf Hx Hp) as [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite HF; [exact Hb| |]; rewrite unsigned_lit_small by lia; assumption.
Qed.
Lemma VX_splice : forall mem md memB mdB (Sx : Z -> Prop),
VX mem md ->
AR tfibsegs B ly S W memB mdB -> same_but_materialized md mdB ->
(forall a, Sx a -> vf_band sp0 a \/ mut a \/ xs a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Sx a -> aview tfibsegs (w_H W) memB a = aview tfibsegs (w_H W) mem a) ->
(forall a, 0 <= a < 2 ^ 64 -> (vf_band sp0 a \/ ~ Sx a) -> apresent (w_H W) mem a -> apresent (w_H W) memB a) ->
VX memB mdB.
Proof.
intros mem md memB mdB Sx (HAR & Hsbm & Hpb & Hfr & Hpm) HARB HsbmB HSx HfrB HpmB.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HVF : VF_STK = 9104) by reflexivity.
split; [exact HARB|]. split; [eapply same_but_materialized_trans; [exact Hsbm | exact HsbmB]|].
split; [intros a Ha; apply HpmB; [unfold vf_band in Ha; lia | left; exact Ha | apply Hpb; exact Ha]|]. split.
- intros a Hr H1 H2 H3. rewrite HfrB; [apply Hfr; assumption | exact Hr | intros Hs; destruct (HSx a Hs) as [Hb|[Hm|Hx]]; [exact (H1 Hb) | exact (H2 Hm) | exact (H3 Hx)]].
- intros a Hr Hf Hx Hp. apply HpmB; [exact Hr | | apply Hpm; assumption].
assert (CASE : vf_band sp0 a \/ ~ vf_band sp0 a) by (unfold vf_band; lia).
destruct CASE as [Hin | Hout]; [left; exact Hin | right]. intros Hs. destruct (HSx a Hs) as [Hb|[Hm|Hx']]; tauto.
Qed.
End VX.
Definition ex_rest : smem := Eval vm_compute in (tl (ex_regions [])).
Lemma ex_rest_ok : forall E (rest : smem) tp,
skeleton rest = skeleton ex_rest -> bv_unsigned (ew E 4) = tp -> 168 <= tp -> tp <= 2 ^ 43 ->
forall r, In r rest -> exists bz, base_val E (YP09.r_base r) = bz /\ 0 <= bz + YP09.r_lo r /\ bz + YP09.r_hi r <= 2 ^ 43.
Proof.
intros E rest tp Hsk H4 Htp1 Htp2 r Hr. pose proof (In_skel rest r Hr) as Hin. rewrite Hsk in Hin.
unfold ex_rest, skeleton in Hin. cbn in Hin. destruct r as [b lo hi wlo whi cs]. unfold skel in Hin. cbn in Hin.
cbn [YP09.r_base YP09.r_lo YP09.r_hi].
repeat (destruct Hin as [Hq|Hin]; [symmetry in Hq; injection Hq; intros; subst; cbn [base_val]; rewrite ?H4; eexists; split; [reflexivity|];
unfold F_STDOUT, F_STDERR, F_STDIN, FILE_SZ, A_GOT_canary, A_canary in *; lia |]).
destruct Hin.
Qed.
Lemma wseg_writable : forall (m : word -> option byte) lo n a,
wseg_ok tfibsegs (Z_to_bv 64 lo) (Z.to_nat n) = true -> 0 <= lo -> lo + n <= 2 ^ 47 -> 0 <= n -> lo <= a < lo + n -> writable_at tfibsegs m a.
Proof.
intros m lo n a Hz Hlo Hhi Hn Ha. unfold writable_at.
apply (store_ok_all tfibsegs m (Z.to_nat n) (Z_to_bv 64 lo));
[rewrite unsigned_lit_small by lia; rewrite Z2Nat.id by lia; lia
| apply store_ok_wseg; exact Hz
| rewrite !unsigned_lit_small by lia; rewrite Z2Nat.id by lia; lia].
Qed.
Lemma wz_stdout : wseg_ok tfibsegs (Z_to_bv 64 F_STDOUT) (Z.to_nat FILE_SZ) = true. Proof. vm_compute. reflexivity. Qed.
Lemma wz_stderr : wseg_ok tfibsegs (Z_to_bv 64 F_STDERR) (Z.to_nat FILE_SZ) = true. Proof. vm_compute. reflexivity. Qed.
Lemma wz_atexit : wseg_ok tfibsegs (Z_to_bv 64 0x5f8fe0) (Z.to_nat 0x130) = true. Proof. vm_compute. reflexivity. Qed.
Lemma wz_exitlock : wseg_ok tfibsegs (Z_to_bv 64 0x5f9200) (Z.to_nat 4) = true. Proof. vm_compute. reflexivity. Qed.
Lemma ex_rest_w : forall E (rest : smem), skeleton rest = skeleton ex_rest ->
forall r a (m : word -> option byte), In r rest ->
base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r -> writable_at tfibsegs m a.
Proof.
intros E rest Hsk r a m Hr Ha. pose proof (In_skel rest r Hr) as Hin. rewrite Hsk in Hin.
unfold ex_rest, skeleton in Hin. cbn in Hin. destruct r as [b lo hi wlo whi cs]. unfold skel in Hin. cbn in Hin.
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
repeat (destruct Hin as [Hq|Hin]; [symmetry in Hq; injection Hq; intros; subst; cbn [base_val] in Ha;
first [ apply (wseg_writable m F_STDOUT FILE_SZ a wz_stdout); unfold F_STDOUT, FILE_SZ in *; lia
| apply (wseg_writable m F_STDERR FILE_SZ a wz_stderr); unfold F_STDERR, FILE_SZ in *; lia
| apply (wseg_writable m 0x5f8fe0 0x130 a wz_atexit); lia
| apply (wseg_writable m 0x5f9200 4 a wz_exitlock); lia
| exfalso; unfold F_STDIN, FILE_SZ, A_GOT_canary, A_canary in *; lia ] |]).
destruct Hin.
Qed.
Lemma ex_rest_range : forall E (rest : smem) tp,
skeleton rest = skeleton ex_rest -> bv_unsigned (ew E 4) = tp ->
forall r a, In r rest -> base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
(is_canary_region r = true /\ A_GOT_canary <= a < A_GOT_canary + 8) \/ ex_cell_range tp a.
Proof.
intros E rest tp Hsk H4 r a Hr Ha. pose proof (In_skel rest r Hr) as Hin. rewrite Hsk in Hin.
unfold ex_rest, skeleton in Hin. cbn in Hin. destruct r as [b lo hi wlo whi cs]. unfold skel in Hin. cbn in Hin.
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha. unfold ex_cell_range, vo_file, vf_file.
repeat (destruct Hin as [Hq|Hin]; [symmetry in Hq; injection Hq; intros; subst; cbn [base_val] in Ha; rewrite ?H4 in Ha;
unfold F_STDOUT, F_STDERR, F_STDIN, FILE_SZ, A_GOT_canary, A_canary in *;
first [ left; split; [vm_compute; reflexivity | lia] | right; lia ] |]).
destruct Hin.
Qed.
Lemma ex_phase : forall (W : world tfibsegs) E ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) ->
sym_runN tfibsegs tfibtbl_x FUEL ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1)
| _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfibsegs tfibtbl_x tfibtbl_x_ok Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
Lemma srz_sym_exit : forall (W : world tfibsegs) E ss ms model (c : word),
AI tfibsegs (w_H W) (w_A W) model ->
st_ok_ecall tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
sr_get (ss_regs ss) 17 = SLit 94 -> sv_denot E (sr_get (ss_regs ss) 10) = c -> bv_unsigned c < 256 ->
srealizes tfibsegs (mkCfg ms model) (t_exit c (m_fs model)).
Proof.
intros W E ss ms model c HAI HS Hrv H17 H10 Hc.
destruct (st_ok_ecall_shape_r tfibsegs (w_H W) E ss ms HS Hrv) as (regs & mem & -> & Hregs & Hmem & HG).
apply (srz_exit_small_lazy tfibsegs regs _ mem (seg_rom tfibsegs) model c (AI_halted _ _ _ _ HAI)).
- rewrite (Hregs 17%bv), H17. right. reflexivity.
- rewrite (Hregs 10%bv). exact H10.
- exact Hc.
Qed.
Lemma m_fs_wvb : forall l mat md, m_fs (with_vm_backing l mat md) = m_fs md.
Proof. intros l mat md. destruct md; reflexivity. Qed.
Lemma rdn_of_aview : forall (H : word -> bool) (m : word -> option byte) a (bs : list byte),
(forall i, (i < length bs)%nat -> aview tfibsegs H m (a + Z.of_nat i) = Some (bv_unsigned (nth i bs 0%bv))) ->
rdn tfibsegs (mrestrict H m) (Z_to_bv 64 a) (length bs) = Some bs.
Proof.
intros H m a bs Hb. apply (proj2 (rdn_mbytes tfibsegs _ (length bs) a bs)). split; [reflexivity|].
intros i Hi. destruct (aview_mbyte H m _ _ (Hb i Hi)) as (b & Hmb & Hbv). rewrite Hmb.
symmetry. rewrite (nth_error_nth' bs 0%bv Hi). f_equal. apply bv_eq. symmetry. exact Hbv.
Qed.
Lemma beq0_sext32_false : forall E n v, bv_unsigned (ew E n) = v -> 0 < v < 2 ^ 31 ->
branch_taken BC_EQ (sv_denot E (SLit 0)) (sv_denot E (SExt true 32 (SOff n 0))) = false.
Proof.
intros E n v Hv Hr. rewrite branch_eq_U, U_SLit, U_SExt, U_off by (rewrite Hv; unfold M64; lia).
rewrite Hv, Z.add_0_r. change (zcanon 0) with 0.
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small v) by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32).
replace ((v + 2 ^ 32 ÷ 2) mod 2 ^ 32 - 2 ^ 32 ÷ 2) with v.
2:{ change (2 ^ 32 ÷ 2) with (2 ^ 31). rewrite Z.mod_small; lia. }
rewrite zcanon_id by (unfold M64; lia). apply Z.eqb_neq. lia.
Qed.
Local Ltac WSEG := first
[ apply (wseg_writable _ 665192 232); [exact wz_stdout | lia | lia | lia | lia]
| apply (wseg_writable _ 664952 232); [exact wz_stderr | lia | lia | lia | lia]
| apply (wseg_writable _ 0x5f8fe0 0x130); [exact wz_atexit | lia | lia | lia | lia]
| apply (wseg_writable _ 0x5f9200 4); [exact wz_exitlock | lia | lia | lia | lia] ].
Local Ltac CELL := (eapply (chunk_ok_val tfibsegs _ _ 0); [reflexivity | zside | zside | rewrite Z.add_0_l; assumption]).
Definition xP_st1 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibtbl_x FUEL ss_exP).
Definition xP_st1c : sstate := Eval vm_compute in YP06.add_cond xP_st1 (mkAC BC_NE (SLit 0) (SExt true 32 (SOff 32 0))).
Definition xP_st2 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibtbl_x FUEL xP_st1c).
Definition xP_af2 : sstate := Eval vm_compute in vf_after_icpt 36 xP_st2 X1_RA OSP_X1 0 [].
Definition xP_st3 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibtbl_x FUEL xP_af2).
Definition xP_af3 : sstate := Eval vm_compute in vf_after_icpt 52 xP_st3 X23_RA OSP_X23 0 [].
Definition xP_st4 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibtbl_x FUEL xP_af3).
Definition xP_af4 : sstate := Eval vm_compute in vf_after_icpt 68 xP_st4 X23_RA OSP_X23 0 [].
Definition xP_st5 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibtbl_x FUEL xP_af4).
Definition xP_r02 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem xP_st2).
Definition xP_rest2 : smem := Eval vm_compute in tl (ss_mem xP_st2).
Definition xP_r03 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem xP_st3).
Definition xP_rest3 : smem := Eval vm_compute in tl (ss_mem xP_st3).
Definition xP_r04 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem xP_st4).
Definition xP_rest4 : smem := Eval vm_compute in tl (ss_mem xP_st4).
Lemma xP_run1 : sym_runN tfibsegs tfibtbl_x FUEL ss_exP = (xP_st1, RS_stopped (SR_branch BC_EQ (SLit 0) (SExt true 32 (SOff 32 0)))). Proof. vm_compute. reflexivity. Qed.
Lemma xP_run2 : sym_runN tfibsegs tfibtbl_x FUEL xP_st1c = (xP_st2, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma xP_run3 : sym_runN tfibsegs tfibtbl_x FUEL xP_af2 = (xP_st3, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma xP_run4 : sym_runN tfibsegs tfibtbl_x FUEL xP_af3 = (xP_st4, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma xP_run5 : sym_runN tfibsegs tfibtbl_x FUEL xP_af4 = (xP_st5, RS_ecall). Proof. vm_compute. reflexivity. Qed.
Definition xP1_st1 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibtbl_x FUEL ss_exP1).
Definition xP1_st1c : sstate := Eval vm_compute in YP06.add_cond xP1_st1 (mkAC BC_NE (SLit 0) (SExt true 32 (SOff 32 0))).
Definition xP1_st2 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibtbl_x FUEL xP1_st1c).
Definition xP1_af2 : sstate := Eval vm_compute in vf_after_icpt 36 xP1_st2 X1_RA OSP_X1 0 [].
Definition xP1_st3 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibtbl_x FUEL xP1_af2).
Definition xP1_af3 : sstate := Eval vm_compute in vf_after_icpt 52 xP1_st3 X23_RA OSP_X23 0 [].
Definition xP1_st4 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibtbl_x FUEL xP1_af3).
Definition xP1_af4 : sstate := Eval vm_compute in vf_after_icpt 68 xP1_st4 X23_RA OSP_X23 0 [].
Definition xP1_st5 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibtbl_x FUEL xP1_af4).
Definition xP1_r02 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem xP1_st2).
Definition xP1_rest2 : smem := Eval vm_compute in tl (ss_mem xP1_st2).
Definition xP1_r03 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem xP1_st3).
Definition xP1_rest3 : smem := Eval vm_compute in tl (ss_mem xP1_st3).
Definition xP1_r04 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem xP1_st4).
Definition xP1_rest4 : smem := Eval vm_compute in tl (ss_mem xP1_st4).
Lemma xP1_run1 : sym_runN tfibsegs tfibtbl_x FUEL ss_exP1 = (xP1_st1, RS_stopped (SR_branch BC_EQ (SLit 0) (SExt true 32 (SOff 32 0)))). Proof. vm_compute. reflexivity. Qed.
Lemma xP1_run2 : sym_runN tfibsegs tfibtbl_x FUEL xP1_st1c = (xP1_st2, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma xP1_run3 : sym_runN tfibsegs tfibtbl_x FUEL xP1_af2 = (xP1_st3, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma xP1_run4 : sym_runN tfibsegs tfibtbl_x FUEL xP1_af3 = (xP1_st4, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma xP1_run5 : sym_runN tfibsegs tfibtbl_x FUEL xP1_af4 = (xP1_st5, RS_ecall). Proof. vm_compute. reflexivity. Qed.
Definition xE_st1 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibtbl_x FUEL ss_exE).
Definition xE_st1c : sstate := Eval vm_compute in YP06.add_cond xE_st1 (mkAC BC_NE (SLit 0) (SExt true 32 (SOff 32 0))).
Definition xE_st2 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibtbl_x FUEL xE_st1c).
Definition xE_af2 : sstate := Eval vm_compute in vf_after_icpt 36 xE_st2 X1_RA OSP_X1 0 [].
Definition xE_st3 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibtbl_x FUEL xE_af2).
Definition xE_af3 : sstate := Eval vm_compute in vf_after_icpt 52 xE_st3 X23_RA OSP_X23 0 [].
Definition xE_st4 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibtbl_x FUEL xE_af3).
Definition xE_af4 : sstate := Eval vm_compute in vf_after_icpt 68 xE_st4 X23_RA OSP_X23 0 [].
Definition xE_st5 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibtbl_x FUEL xE_af4).
Definition xE_r02 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem xE_st2).
Definition xE_rest2 : smem := Eval vm_compute in tl (ss_mem xE_st2).
Definition xE_r03 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem xE_st3).
Definition xE_rest3 : smem := Eval vm_compute in tl (ss_mem xE_st3).
Definition xE_r04 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem xE_st4).
Definition xE_rest4 : smem := Eval vm_compute in tl (ss_mem xE_st4).
Lemma xE_run1 : sym_runN tfibsegs tfibtbl_x FUEL ss_exE = (xE_st1, RS_stopped (SR_branch BC_EQ (SLit 0) (SExt true 32 (SOff 32 0)))). Proof. vm_compute. reflexivity. Qed.
Lemma xE_run2 : sym_runN tfibsegs tfibtbl_x FUEL xE_st1c = (xE_st2, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma xE_run3 : sym_runN tfibsegs tfibtbl_x FUEL xE_af2 = (xE_st3, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma xE_run4 : sym_runN tfibsegs tfibtbl_x FUEL xE_af3 = (xE_st4, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma xE_run5 : sym_runN tfibsegs tfibtbl_x FUEL xE_af4 = (xE_st5, RS_ecall). Proof. vm_compute. reflexivity. Qed.
Definition xF_st1 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibtbl_x FUEL ss_exF).
Definition xF_st1c : sstate := Eval vm_compute in YP06.add_cond xF_st1 (mkAC BC_NE (SLit 0) (SExt true 32 (SOff 32 0))).
Definition xF_st2 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibtbl_x FUEL xF_st1c).
Definition xF_af2 : sstate := Eval vm_compute in vf_after_icpt 36 xF_st2 X1_RA OSP_X1 0 [].
Definition xF_st3 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibtbl_x FUEL xF_af2).
Definition xF_af3 : sstate := Eval vm_compute in vf_after_icpt 52 xF_st3 X23_RA OSP_X23 0 [].
Definition xF_st4 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibtbl_x FUEL xF_af3).
Definition xF_af4 : sstate := Eval vm_compute in vf_after_icpt 68 xF_st4 X23_RA OSP_X23 0 [].
Definition xF_st5 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibtbl_x FUEL xF_af4).
Definition xF_r02 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem xF_st2).
Definition xF_rest2 : smem := Eval vm_compute in tl (ss_mem xF_st2).
Definition xF_r03 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem xF_st3).
Definition xF_rest3 : smem := Eval vm_compute in tl (ss_mem xF_st3).
Definition xF_r04 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem xF_st4).
Definition xF_rest4 : smem := Eval vm_compute in tl (ss_mem xF_st4).
Lemma xF_run1 : sym_runN tfibsegs tfibtbl_x FUEL ss_exF = (xF_st1, RS_stopped (SR_branch BC_EQ (SLit 0) (SExt true 32 (SOff 32 0)))). Proof. vm_compute. reflexivity. Qed.
Lemma xF_run2 : sym_runN tfibsegs tfibtbl_x FUEL xF_st1c = (xF_st2, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma xF_run3 : sym_runN tfibsegs tfibtbl_x FUEL xF_af2 = (xF_st3, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma xF_run4 : sym_runN tfibsegs tfibtbl_x FUEL xF_af3 = (xF_st4, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma xF_run5 : sym_runN tfibsegs tfibtbl_x FUEL xF_af4 = (xF_st5, RS_ecall). Proof. vm_compute. reflexivity. Qed.
Definition xF_af5 : sstate := Eval vm_compute in wl_after xF_st5 0 (-144) 84.
Definition xF_st6 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibtbl_x FUEL xF_af5).
Lemma xF_run6 : sym_runN tfibsegs tfibtbl_x FUEL xF_af5 = (xF_st6, RS_ecall). Proof. vm_compute. reflexivity. Qed.
Local Ltac GEO := unfold STDOUT_BUFA, STDOUT_BSZ, F_STDOUT, F_STDERR, F_STDIN, FILE_SZ, A_GOT_canary, A_canary, OSP_X1, OSP_X23, XW1, XW2, XW3, TFIB_TPX in *; lia.
Section S.
Variable B : asyms.
Hypothesis TL : TfibSyms B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis HB : TfibSyms B.
Hypothesis X1 : xret_realizes tfibsegs B X1_PC XW1 XTRUE.
Hypothesis X2 : xret_realizes_noar tfibsegs B X2_PC XW2 XTRUE.
Hypothesis X3 : xret_realizes tfibsegs B X3_PC XW3 X3PRE.
Lemma ex_entryP : forall (W : world tfibsegs) regs mem tid cval sew,
2 ^ 44 <= spZ regs -> spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
(forall a, spZ regs - VF_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 4 = w64 (as_tp B) -> as_tp B = TFIB_TPX ->
cells_are ex_consts (mrestrict (w_H W) mem) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (as_tp B - 168) 4 tid -> 0 < tid < 2 ^ 31 ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (F_STDERR + 40) 8 sew -> val_mem tfibsegs (mrestrict (w_H W) mem) (F_STDERR + 56) 8 sew -> 0 <= sew < 2 ^ 64 ->
stdout_pristine (mrestrict (w_H W) mem) ->
st_ok tfibsegs (Ereg regs [Z_to_bv 64 tid; Z_to_bv 64 cval; Z_to_bv 64 STDOUT_BUFA; Z_to_bv 64 sew]) ss_exP
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_exit) mem (seg_rom tfibsegs))).
Proof.
intros W regs mem tid cval sew Hsp1 Hsp2 Hal Hpres H4 HTP HC Htid Htidr Hgot Hcan Hcv Hew1 Hew2 Hewr HF.
rewrite restrict_mkst_fx. unfold ss_exP.
assert (HVF : VF_STK = 9104) by reflexivity.
unfold cells_are, ex_consts in HC.
repeat match type of HC with Forall _ (_ :: _) =>
let h := fresh "HCc" in pose proof (Forall_inv HC) as h; cbn beta iota in h; apply Forall_inv_tail in HC end.
unfold stdout_pristine, ofile_is, stdout_fields0 in HF.
repeat match type of HF with Forall _ (_ :: _) =>
let h := fresh "HFf" in pose proof (Forall_inv HF) as h; cbn beta iota in h; apply Forall_inv_tail in HF end.
unfold F_STDOUT, F_STDERR, F_STDIN, STDOUT_BUFA, STDOUT_BSZ, A_GOT_canary, A_canary in *. rewrite HTP in Htid. unfold TFIB_TPX in Htid.
set (E := Ereg regs [Z_to_bv 64 tid; Z_to_bv 64 cval; Z_to_bv 64 6264480; Z_to_bv 64 sew]).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E4 : bv_unsigned (ew E 4) = TFIB_TPX) by (subst E; rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl), H4, HTP; apply unsigned_lit_small; unfold TFIB_TPX; lia). unfold TFIB_TPX in E4.
assert (E32 : ew E 32 = Z_to_bv 64 tid) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 cval) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 6264480) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 sew) by (subst E; exact (ew_Ereg_extra regs _ 3)).
apply (entry_st_ok_full tfibsegs); change (Ereg regs [Z_to_bv 64 tid; Z_to_bv 64 cval; Z_to_bv 64 6264480; Z_to_bv 64 sew]) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold ex_regions. unfold F_STDOUT, F_STDERR, F_STDIN, FILE_SZ, A_GOT_canary, A_canary.
repeat apply Forall_cons; try apply Forall_nil.
+ apply (region_ok_stack tfibsegs E _ 2 (spZ regs) (- VF_STK)); [exact E2 | lia | lia |].
intros a Ha. apply apresent_writable. apply Hpres. lia.
+   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; WSEG |].
unfold fo_chunks, stdout_fields0. unfold F_STDOUT, STDOUT_BUFA, STDOUT_BSZ. cbn [map Z.add].
repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; WSEG |].
repeat apply Forall_cons; try apply Forall_nil;
first [ CELL | eapply (chunk_ok_val tfibsegs E _ 0 _ 8 _ sew); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_l; assumption] ].
+   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia |].
repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ 0); [reflexivity | zside | zside | rewrite Z.add_0_l; exact Hgot].
+   unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ 0 _ 8 _ cval); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_l; exact Hcan].
+   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; WSEG |]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; WSEG |]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E4. split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ 6131600 (-168) 4 _ tid); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
exact Htid.
- apply pairwise_disjoint_of_extents. unfold ex_regions, cellr, img_ro_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E4.
unfold F_STDOUT, F_STDERR, F_STDIN, FILE_SZ, A_GOT_canary, A_canary.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I].
cbn [ex_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
change (2 ^ 4) with 16. repeat split; lia.
Qed.
Lemma ex_entryP1 : forall (W : world tfibsegs) regs mem tid cval sew,
2 ^ 44 <= spZ regs -> spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
(forall a, spZ regs - VF_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 4 = w64 (as_tp B) -> as_tp B = TFIB_TPX ->
cells_are ex_consts1 (mrestrict (w_H W) mem) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (as_tp B - 168) 4 tid -> 0 < tid < 2 ^ 31 ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (F_STDERR + 40) 8 sew -> val_mem tfibsegs (mrestrict (w_H W) mem) (F_STDERR + 56) 8 sew -> 0 <= sew < 2 ^ 64 ->
stdout_pristine (mrestrict (w_H W) mem) ->
st_ok tfibsegs (Ereg regs [Z_to_bv 64 tid; Z_to_bv 64 cval; Z_to_bv 64 STDOUT_BUFA; Z_to_bv 64 sew]) ss_exP1
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_exit) mem (seg_rom tfibsegs))).
Proof.
intros W regs mem tid cval sew Hsp1 Hsp2 Hal Hpres H4 HTP HC Htid Htidr Hgot Hcan Hcv Hew1 Hew2 Hewr HF.
rewrite restrict_mkst_fx. unfold ss_exP1.
assert (HVF : VF_STK = 9104) by reflexivity.
unfold cells_are, ex_consts1 in HC.
repeat match type of HC with Forall _ (_ :: _) =>
let h := fresh "HCc" in pose proof (Forall_inv HC) as h; cbn beta iota in h; apply Forall_inv_tail in HC end.
unfold stdout_pristine, ofile_is, stdout_fields0 in HF.
repeat match type of HF with Forall _ (_ :: _) =>
let h := fresh "HFf" in pose proof (Forall_inv HF) as h; cbn beta iota in h; apply Forall_inv_tail in HF end.
unfold F_STDOUT, F_STDERR, F_STDIN, STDOUT_BUFA, STDOUT_BSZ, A_GOT_canary, A_canary in *. rewrite HTP in Htid. unfold TFIB_TPX in Htid.
set (E := Ereg regs [Z_to_bv 64 tid; Z_to_bv 64 cval; Z_to_bv 64 6264480; Z_to_bv 64 sew]).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E4 : bv_unsigned (ew E 4) = TFIB_TPX) by (subst E; rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl), H4, HTP; apply unsigned_lit_small; unfold TFIB_TPX; lia). unfold TFIB_TPX in E4.
assert (E32 : ew E 32 = Z_to_bv 64 tid) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 cval) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 6264480) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 sew) by (subst E; exact (ew_Ereg_extra regs _ 3)).
apply (entry_st_ok_full tfibsegs); change (Ereg regs [Z_to_bv 64 tid; Z_to_bv 64 cval; Z_to_bv 64 6264480; Z_to_bv 64 sew]) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold ex_regions1. unfold F_STDOUT, F_STDERR, F_STDIN, FILE_SZ, A_GOT_canary, A_canary.
repeat apply Forall_cons; try apply Forall_nil.
+ apply (region_ok_stack tfibsegs E _ 2 (spZ regs) (- VF_STK)); [exact E2 | lia | lia |].
intros a Ha. apply apresent_writable. apply Hpres. lia.
+   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; WSEG |].
unfold fo_chunks, stdout_fields0. unfold F_STDOUT, STDOUT_BUFA, STDOUT_BSZ. cbn [map Z.add].
repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; WSEG |].
repeat apply Forall_cons; try apply Forall_nil;
first [ CELL | eapply (chunk_ok_val tfibsegs E _ 0 _ 8 _ sew); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_l; assumption] ].
+   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia |].
repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ 0); [reflexivity | zside | zside | rewrite Z.add_0_l; exact Hgot].
+   unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ 0 _ 8 _ cval); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_l; exact Hcan].
+   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; WSEG |]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; WSEG |]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E4. split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ 6131600 (-168) 4 _ tid); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
exact Htid.
- apply pairwise_disjoint_of_extents. unfold ex_regions1, cellr, img_ro_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E4.
unfold F_STDOUT, F_STDERR, F_STDIN, FILE_SZ, A_GOT_canary, A_canary.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I].
cbn [ex_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
change (2 ^ 4) with 16. repeat split; lia.
Qed.
Lemma ex_entryE : forall (W : world tfibsegs) regs mem tid cval sew,
2 ^ 44 <= spZ regs -> spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
(forall a, spZ regs - VF_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 4 = w64 (as_tp B) -> as_tp B = TFIB_TPX ->
cells_are ex_consts (mrestrict (w_H W) mem) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (as_tp B - 168) 4 tid -> 0 < tid < 2 ^ 31 ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (F_STDERR + 40) 8 sew -> val_mem tfibsegs (mrestrict (w_H W) mem) (F_STDERR + 56) 8 sew -> 0 <= sew < 2 ^ 64 ->
stdout_mid STDOUT_BUFA (mrestrict (w_H W) mem) ->
st_ok tfibsegs (Ereg regs [Z_to_bv 64 tid; Z_to_bv 64 cval; Z_to_bv 64 STDOUT_BUFA; Z_to_bv 64 sew]) ss_exE
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_exit) mem (seg_rom tfibsegs))).
Proof.
intros W regs mem tid cval sew Hsp1 Hsp2 Hal Hpres H4 HTP HC Htid Htidr Hgot Hcan Hcv Hew1 Hew2 Hewr [HF Hwp].
rewrite restrict_mkst_fx. unfold ss_exE.
assert (HVF : VF_STK = 9104) by reflexivity.
unfold cells_are, ex_consts in HC.
repeat match type of HC with Forall _ (_ :: _) =>
let h := fresh "HCc" in pose proof (Forall_inv HC) as h; cbn beta iota in h; apply Forall_inv_tail in HC end.
unfold ofile_is, stdout_fields1 in HF.
repeat match type of HF with Forall _ (_ :: _) =>
let h := fresh "HFf" in pose proof (Forall_inv HF) as h; cbn beta iota in h; apply Forall_inv_tail in HF end.
unfold F_STDOUT, F_STDERR, F_STDIN, STDOUT_BUFA, STDOUT_BSZ, A_GOT_canary, A_canary in *. rewrite HTP in Htid. unfold TFIB_TPX in Htid.
set (E := Ereg regs [Z_to_bv 64 tid; Z_to_bv 64 cval; Z_to_bv 64 6264480; Z_to_bv 64 sew]).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E4 : bv_unsigned (ew E 4) = TFIB_TPX) by (subst E; rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl), H4, HTP; apply unsigned_lit_small; unfold TFIB_TPX; lia). unfold TFIB_TPX in E4.
assert (E32 : ew E 32 = Z_to_bv 64 tid) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 cval) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 6264480) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 sew) by (subst E; exact (ew_Ereg_extra regs _ 3)).
apply (entry_st_ok_full tfibsegs); change (Ereg regs [Z_to_bv 64 tid; Z_to_bv 64 cval; Z_to_bv 64 6264480; Z_to_bv 64 sew]) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold ex_regions. unfold F_STDOUT, F_STDERR, F_STDIN, FILE_SZ, A_GOT_canary, A_canary.
repeat apply Forall_cons; try apply Forall_nil.
+ apply (region_ok_stack tfibsegs E _ 2 (spZ regs) (- VF_STK)); [exact E2 | lia | lia |].
intros a Ha. apply apresent_writable. apply Hpres. lia.
+   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; WSEG |].
unfold fo_chunks, stdout_fields1. unfold F_STDOUT, STDOUT_BUFA, STDOUT_BSZ. cbn [map Z.add].
apply Forall_cons.
{ eapply (chunk_ok_val tfibsegs E _ 0 _ 8 _ 6264480); [reflexivity | zside | zside | rewrite Z.add_0_l; exact Hwp]. }
repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; WSEG |].
repeat apply Forall_cons; try apply Forall_nil;
first [ CELL | eapply (chunk_ok_val tfibsegs E _ 0 _ 8 _ sew); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_l; assumption] ].
+   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia |].
repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ 0); [reflexivity | zside | zside | rewrite Z.add_0_l; exact Hgot].
+   unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ 0 _ 8 _ cval); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_l; exact Hcan].
+   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; WSEG |]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; WSEG |]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E4. split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ 6131600 (-168) 4 _ tid); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
exact Htid.
- apply pairwise_disjoint_of_extents. unfold ex_regions, cellr, img_ro_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E4.
unfold F_STDOUT, F_STDERR, F_STDIN, FILE_SZ, A_GOT_canary, A_canary.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I].
cbn [ex_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
change (2 ^ 4) with 16. repeat split; lia.
Qed.
Lemma ex_entryF : forall (W : world tfibsegs) regs mem tid cval sew wp,
2 ^ 44 <= spZ regs -> spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
(forall a, spZ regs - VF_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 4 = w64 (as_tp B) -> as_tp B = TFIB_TPX ->
cells_are ex_consts (mrestrict (w_H W) mem) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (as_tp B - 168) 4 tid -> 0 < tid < 2 ^ 31 ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (F_STDERR + 40) 8 sew -> val_mem tfibsegs (mrestrict (w_H W) mem) (F_STDERR + 56) 8 sew -> 0 <= sew < 2 ^ 64 ->
stdout_mid wp (mrestrict (w_H W) mem) -> STDOUT_BUFA + 1 <= wp <= STDOUT_BUFA + STDOUT_BSZ ->
st_ok tfibsegs (Ereg regs [Z_to_bv 64 tid; Z_to_bv 64 cval; Z_to_bv 64 wp; Z_to_bv 64 sew]) ss_exF
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_exit) mem (seg_rom tfibsegs))).
Proof.
intros W regs mem tid cval sew wp Hsp1 Hsp2 Hal Hpres H4 HTP HC Htid Htidr Hgot Hcan Hcv Hew1 Hew2 Hewr [HF Hwp] Hwpr.
rewrite restrict_mkst_fx. unfold ss_exF.
assert (HVF : VF_STK = 9104) by reflexivity.
unfold cells_are, ex_consts in HC.
repeat match type of HC with Forall _ (_ :: _) =>
let h := fresh "HCc" in pose proof (Forall_inv HC) as h; cbn beta iota in h; apply Forall_inv_tail in HC end.
unfold ofile_is, stdout_fields1 in HF.
repeat match type of HF with Forall _ (_ :: _) =>
let h := fresh "HFf" in pose proof (Forall_inv HF) as h; cbn beta iota in h; apply Forall_inv_tail in HF end.
unfold F_STDOUT, F_STDERR, F_STDIN, STDOUT_BUFA, STDOUT_BSZ, A_GOT_canary, A_canary in *. rewrite HTP in Htid. unfold TFIB_TPX in Htid.
set (E := Ereg regs [Z_to_bv 64 tid; Z_to_bv 64 cval; Z_to_bv 64 wp; Z_to_bv 64 sew]).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E4 : bv_unsigned (ew E 4) = TFIB_TPX) by (subst E; rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl), H4, HTP; apply unsigned_lit_small; unfold TFIB_TPX; lia). unfold TFIB_TPX in E4.
assert (E32 : ew E 32 = Z_to_bv 64 tid) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 cval) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 wp) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 sew) by (subst E; exact (ew_Ereg_extra regs _ 3)).
apply (entry_st_ok_full tfibsegs); change (Ereg regs [Z_to_bv 64 tid; Z_to_bv 64 cval; Z_to_bv 64 wp; Z_to_bv 64 sew]) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold ex_regions. unfold F_STDOUT, F_STDERR, F_STDIN, FILE_SZ, A_GOT_canary, A_canary.
repeat apply Forall_cons; try apply Forall_nil.
+ apply (region_ok_stack tfibsegs E _ 2 (spZ regs) (- VF_STK)); [exact E2 | lia | lia |].
intros a Ha. apply apresent_writable. apply Hpres. lia.
+   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; WSEG |].
unfold fo_chunks, stdout_fields1. unfold F_STDOUT, STDOUT_BUFA, STDOUT_BSZ. cbn [map Z.add].
apply Forall_cons.
{ eapply (chunk_ok_val tfibsegs E _ 0 _ 8 _ wp); [| zside | zside | rewrite Z.add_0_l; exact Hwp].
cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; WSEG |].
repeat apply Forall_cons; try apply Forall_nil;
first [ CELL | eapply (chunk_ok_val tfibsegs E _ 0 _ 8 _ sew); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_l; assumption] ].
+   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia |].
repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ 0); [reflexivity | zside | zside | rewrite Z.add_0_l; exact Hgot].
+   unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ 0 _ 8 _ cval); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_l; exact Hcan].
+   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; WSEG |]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; WSEG |]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. repeat apply Forall_cons; try apply Forall_nil; CELL.
+   unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E4. split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ 6131600 (-168) 4 _ tid); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
exact Htid.
- apply pairwise_disjoint_of_extents. unfold ex_regions, cellr, img_ro_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E4.
unfold F_STDOUT, F_STDERR, F_STDIN, FILE_SZ, A_GOT_canary, A_canary.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I].
cbn [ex_factsF f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2, E34, (unsigned_lit_small wp) by lia.
change (2 ^ 4) with 16. rewrite Z.pow_0_r, Z.mod_1_r. unfold STDOUT_BUFA, STDOUT_BSZ in *. repeat split; lia.
Qed.
Theorem tfib_exit_pristine : forall ly S (W : world tfibsegs) regs mem md code tid cval sew,
ecall_pre tfibsegs B ly S W regs mem md ->
2 ^ 44 <= spZ regs -> ly_stk_lo ly + VF_STK <= spZ regs ->
(forall a, vf_band (spZ regs) a -> apresent (w_H W) mem a) ->
getr regs 10 = w64 code -> 0 <= code < 256 ->
as_tp B = TFIB_TPX ->
cells_are ex_consts (mrestrict (w_H W) mem) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (as_tp B - 168) 4 tid -> 0 < tid < 2 ^ 31 ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (F_STDERR + 40) 8 sew -> val_mem tfibsegs (mrestrict (w_H W) mem) (F_STDERR + 56) 8 sew -> 0 <= sew < 2 ^ 64 ->
stdout_pristine (mrestrict (w_H W) mem) ->
(forall a, ex_cell_range (as_tp B) a -> ~ aowned B ly S a) ->
(forall a, STDOUT_BUFA <= a < STDOUT_BUFA + STDOUT_BSZ -> ~ aowned B ly S a) ->
AI tfibsegs (w_H W) (w_A W) md ->
srealizes tfibsegs (cfg_at tfibsegs A_exit regs mem md) (t_exit (Z_to_bv 64 code) (m_fs md)).
Proof.
intros ly S W regs mem md code tid cval sew HPRE Hsp44 Hstk Hpres Ha0 Hcode HTP HC Htid Htidr Hgot Hcan Hcv Hew1 Hew2 Hewr HFO HXown HBown HAI0.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity. assert (HVF : VF_STK = 9104) by reflexivity.
assert (HFF : F_STDOUT = 665192) by reflexivity. assert (HFS : FILE_SZ = 232) by reflexivity. assert (HFE : F_STDERR = 664952) by reflexivity.
assert (HBF : STDOUT_BUFA = 6264480) by reflexivity. assert (HBS : STDOUT_BSZ = 1024) by reflexivity. assert (HFI : F_STDIN = 665432) by reflexivity.
assert (HGC : A_GOT_canary = 650296) by reflexivity. assert (HCA : A_canary = 6262736) by reflexivity.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hsp47 : sp0 <= 2 ^ 47) by lia.
set (XS := fun a => aowned B ly S a \/ XW1 a \/ XW2 a \/ XW3 a).
assert (HFownM : forall a, exm a -> ~ aowned B ly S a).
{ intros a Ha. apply HXown. unfold exm in Ha. unfold ex_cell_range. destruct Ha as [H|[H|[H|H]]]; [left; exact H | right; left; exact H | lia | lia]. }
unfold cfg_at. change (w64 A_exit) with (Z_to_bv 64 A_exit).
pose proof (ex_entryP W regs mem tid cval sew Hsp44 Hsp47 Hal16 ltac:(intros a Ha; apply Hpres; exact Ha) Htp HTP HC Htid Htidr Hgot Hcan Hcv Hew1 Hew2 Hewr HFO) as HS0.
set (EL := [Z_to_bv 64 tid; Z_to_bv 64 cval; Z_to_bv 64 STDOUT_BUFA; Z_to_bv 64 sew]) in *.
remember (Ereg regs EL) as E0 eqn:HE0.
assert (EE : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E0 i = getr regs r)
by (intros i r Hi; rewrite HE0; exact (ew_Ereg_nat regs _ i r Hi)).
assert (Usp0 : bv_unsigned (ew E0 2) = sp0) by (rewrite (EE 2%nat (2%bv : bv 5) eq_refl); reflexivity).
assert (G3_0 : ew E0 3 = w64 (as_gp B)) by (rewrite (EE 3%nat (3%bv : bv 5) eq_refl); exact Hgp).
assert (G4_0 : ew E0 4 = w64 (as_tp B)) by (rewrite (EE 4%nat (4%bv : bv 5) eq_refl); exact Htp).
assert (U4_0 : bv_unsigned (ew E0 4) = as_tp B) by (rewrite G4_0; apply unsigned_lit_small; rewrite HTP; unfold TFIB_TPX; lia).
assert (A10_0 : ew E0 10 = Z_to_bv 64 code) by (rewrite (EE 10%nat (10%bv : bv 5) eq_refl); exact Ha0).
assert (A32_0 : bv_unsigned (ew E0 32) = tid) by (rewrite HE0; pose proof (ew_Ereg_extra regs EL 0) as X; cbn [nth Nat.add EL] in X; rewrite X; apply unsigned_lit_small; lia).
pose (wp := STDOUT_BUFA). assert (A34_0 : bv_unsigned (ew E0 34) = wp) by (rewrite HE0; pose proof (ew_Ereg_extra regs EL 2) as X; cbn [nth Nat.add EL] in X; rewrite X; apply unsigned_lit_small; unfold wp; GEO).
clear HE0 EE.
pose proof (VX_init B ly S W sp0 mem md exm XS HAR Hpres) as VX0.
eapply (SRr_srealizes tfibsegs W _ _ _ (ex_phase W E0 ss_exP xP_st1 _ _ _ HS0 xP_run1) HAI0).
intros W1 c1 _ HAI1 (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). cbn [cfg_model] in HAI1. clear HS0.
rewrite ?wvb_wvb in HAI1 |- *.
assert (VX1 : VX B ly S W sp0 mem md exm XS (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat1 md)).
{ pose proof (VX_run B LAWS ly S W sp0 mem md exm exm_img exm_dec HFownM XS Hstk Htop _ _ (ms_mem ms1) mat1 VX0) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF1. intros Hin. destruct (ex_windows_sound E0 ss_exP sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 Hw)].
- intros x Hx1 Hx2. apply HFr1. intros Hin. destruct (ex_windows_sound E0 ss_exP sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 Hw)].
- apply (vf_band_present W E0 xP_st1 ms1 sp0 HS1 ltac:(vm_compute; reflexivity) Usp0 ltac:(lia)). }
clear VX0 HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs E0 xP_st1 _ BC_EQ (SLit 0) (SExt true 32 (SOff 32 0)) HS1
ltac:(apply (beq0_sext32_false E0 32 tid A32_0); lia)) as HS1c.
change (YP06.add_cond xP_st1 (mkAC (neg_bc BC_EQ) (SLit 0) (SExt true 32 (SOff 32 0)))) with xP_st1c in HS1c. clear HS1.
eapply (SRr_srealizes tfibsegs W _ _ _ (ex_phase W E0 xP_st1c xP_st2 _ _ _ HS1c xP_run2) HAI1).
intros W2 c2 _ HAI2 (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). cbn [cfg_model] in HAI2. clear HS1c.
rewrite ?wvb_wvb in HAI2 |- *.
assert (VX2 : VX B ly S W sp0 mem md exm XS (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md)).
{ pose proof (VX_run B LAWS ly S W sp0 mem md exm exm_img exm_dec HFownM XS Hstk Htop _ _ (ms_mem ms2) mat2 VX1) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF2. intros Hin. destruct (ex_windows_sound E0 xP_st1c sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 Hw)].
- intros x Hx1 Hx2. apply HFr2. intros Hin. destruct (ex_windows_sound E0 xP_st1c sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 Hw)].
- apply (vf_band_present W E0 xP_st2 ms2 sp0 HS2 ltac:(vm_compute; reflexivity) Usp0 ltac:(lia)). }
clear VX1 HF2 HFr2.
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_xcall B LAWS HB X1_PC XW1 XTRUE X1 W E0 xP_st2 ms2 _ ly S sp0 xP_r02 xP_rest2 36 X1_RA OSP_X1
HS2 eq_refl eq_refl Usp0 G3_0 G4_0 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_X1; lia) ltac:(unfold OSP_X1; lia) ltac:(unfold X1_RA; lia) ltac:(reflexivity)
(ex_rest_ok E0 xP_rest2 (as_tp B) ltac:(vm_compute; reflexivity) U4_0 ltac:(rewrite HTP; unfold TFIB_TPX; lia) ltac:(rewrite HTP; unfold TFIB_TPX; lia))
ltac:(intros r a Hr Ha; destruct (ex_rest_range E0 xP_rest2 (as_tp B) ltac:(vm_compute; reflexivity) U4_0 r a Hr Ha) as [[HcanR Hcr]|Hcr];
[ split; [left; exact HcanR | unfold XW1; unfold A_GOT_canary in Hcr; GEO]
| split; [right; apply HXown; exact Hcr | unfold XW1; unfold ex_cell_range, vo_file, vf_file in Hcr; GEO] ])
ltac:(intros a Hx; unfold XW1 in Hx; unfold vf_band; GEO)
(ex_rest_w E0 xP_rest2 ltac:(vm_compute; reflexivity))
(proj1 VX2) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VX2))) ltac:(exact I)) HAI2).
intros W2' c2' _ HAI2' (-> & ms2' & mat2' & -> & HS2' & HAR2' & HP2' & Hfr2' & Hpm2'). cbn [cfg_model] in HAI2'.
rewrite wvb_wvb in HAI2', HAR2' |- *.
change (vf_after_icpt 36 xP_st2 X1_RA OSP_X1 0 []) with xP_af2 in HS2'.
assert (VX2' : VX B ly S W sp0 mem md exm XS (ms_mem ms2') (with_vm_backing (m_vm_lazy md) mat2' md)).
{ eapply (VX_splice B ly S W sp0 mem md exm XS Hstk Htop (ms_mem ms2) _ (ms_mem ms2') _
(fun a => (sp0 + OSP_X1 - ESTACK <= a < sp0 + OSP_X1) \/ aowned B ly S a \/ XW1 a)).
- exact VX2.
- exact HAR2'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat2' mat2 md). apply with_vm_backing_same.
- intros a [Ha|[Ha|Ha]]; [left; unfold vf_band, OSP_X1 in *; lia | right; right; unfold XS; tauto | right; right; unfold XS; tauto].
- intros a Hr Hna. apply Hfr2'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; left; exact H' | intros H'; apply Hna; right; right; exact H'].
- intros a Hr Hba. apply Hpm2'; [exact Hr|]. destruct Hba as [Hb|Hns]; [intros Hx; unfold XW1 in Hx; unfold vf_band in Hb; GEO | intros Hx; apply Hns; right; right; exact Hx]. }
remember (havoc E0 36 (map (getr (ms_regs ms2')) CLOB)) as E1 eqn:HE1.
assert (OLD1 : forall j, (j < 36)%nat -> ew E1 j = ew E0 j) by (intros j Hj; rewrite HE1; apply ew_havoc_old; exact Hj).
assert (Usp1 : bv_unsigned (ew E1 2) = sp0) by (rewrite OLD1 by (cbv; lia); exact Usp0).
assert (G3_1 : ew E1 3 = w64 (as_gp B)) by (rewrite OLD1 by (cbv; lia); exact G3_0).
assert (G4_1 : ew E1 4 = w64 (as_tp B)) by (rewrite OLD1 by (cbv; lia); exact G4_0).
assert (U4_1 : bv_unsigned (ew E1 4) = as_tp B) by (rewrite OLD1 by (cbv; lia); exact U4_0).
assert (A10_1 : ew E1 10 = Z_to_bv 64 code) by (rewrite OLD1 by (cbv; lia); exact A10_0).
assert (A34_1 : bv_unsigned (ew E1 34) = wp) by (rewrite OLD1 by (cbv; lia); exact A34_0).
clear HE1 HS2 VX2.
eapply (SRr_srealizes tfibsegs W _ _ _ (ex_phase W E1 xP_af2 xP_st3 _ _ _ HS2' xP_run3) HAI2').
intros W3 c3 _ HAI3 (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). cbn [cfg_model] in HAI3. clear HS2'.
rewrite ?wvb_wvb in HAI3 |- *.
assert (VX3 : VX B ly S W sp0 mem md exm XS (ms_mem ms3) (with_vm_backing (m_vm_lazy md) mat3 md)).
{ pose proof (VX_run B LAWS ly S W sp0 mem md exm exm_img exm_dec HFownM XS Hstk Htop _ _ (ms_mem ms3) mat3 VX2') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF3. intros Hin. destruct (ex_windows_sound E1 xP_af2 sp0 _ ltac:(vm_compute; reflexivity) Usp1 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 Hw)].
- intros x Hx1 Hx2. apply HFr3. intros Hin. destruct (ex_windows_sound E1 xP_af2 sp0 _ ltac:(vm_compute; reflexivity) Usp1 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 Hw)].
- apply (vf_band_present W E1 xP_st3 ms3 sp0 HS3 ltac:(vm_compute; reflexivity) Usp1 ltac:(lia)). }
clear VX2' HF3 HFr3.
pose proof HS3 as HSc3. destruct HSc3 as (_ & _ & _ & _ & _ & _ & _ & Hmem3 & _). cbn [restrict ms_mem] in Hmem3.
assert (X3P : X3PRE W (ms_mem ms3)).
{ split; (eapply (val_mem_of_lit E1 (mrestrict (w_H W) (ms_mem ms3)) (ss_mem xP_st3) _ _ _ Hmem3); vm_compute; reflexivity). }
clear Hmem3.
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_xcall B LAWS HB X3_PC XW3 X3PRE X3 W E1 xP_st3 ms3 _ ly S sp0 xP_r03 xP_rest3 52 X23_RA OSP_X23
HS3 eq_refl eq_refl Usp1 G3_1 G4_1 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_X23; lia) ltac:(unfold OSP_X23; lia) ltac:(unfold X23_RA; lia) ltac:(reflexivity)
(ex_rest_ok E1 xP_rest3 (as_tp B) ltac:(vm_compute; reflexivity) U4_1 ltac:(rewrite HTP; unfold TFIB_TPX; lia) ltac:(rewrite HTP; unfold TFIB_TPX; lia))
ltac:(intros r a Hr Ha; destruct (ex_rest_range E1 xP_rest3 (as_tp B) ltac:(vm_compute; reflexivity) U4_1 r a Hr Ha) as [[HcanR Hcr]|Hcr];
[ split; [left; exact HcanR | unfold XW3; unfold A_GOT_canary in Hcr; GEO]
| split; [right; apply HXown; exact Hcr | unfold XW3; unfold ex_cell_range, vo_file, vf_file in Hcr; GEO] ])
ltac:(intros a Hx; unfold XW3 in Hx; unfold vf_band; GEO)
(ex_rest_w E1 xP_rest3 ltac:(vm_compute; reflexivity))
(proj1 VX3) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VX3))) ltac:(exact X3P)) HAI3).
intros W3' c3' _ HAI3' (-> & ms3' & mat3' & -> & HS3' & HAR3' & HP3' & Hfr3' & Hpm3'). cbn [cfg_model] in HAI3'.
rewrite wvb_wvb in HAI3', HAR3' |- *.
change (vf_after_icpt 52 xP_st3 X23_RA OSP_X23 0 []) with xP_af3 in HS3'.
assert (VX3' : VX B ly S W sp0 mem md exm XS (ms_mem ms3') (with_vm_backing (m_vm_lazy md) mat3' md)).
{ eapply (VX_splice B ly S W sp0 mem md exm XS Hstk Htop (ms_mem ms3) _ (ms_mem ms3') _
(fun a => (sp0 + OSP_X23 - ESTACK <= a < sp0 + OSP_X23) \/ aowned B ly S a \/ XW3 a)).
- exact VX3.
- exact HAR3'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat3' mat3 md). apply with_vm_backing_same.
- intros a [Ha|[Ha|Ha]]; [left; unfold vf_band, OSP_X23 in *; lia | right; right; unfold XS; tauto | right; right; unfold XS; tauto].
- intros a Hr Hna. apply Hfr3'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; left; exact H' | intros H'; apply Hna; right; right; exact H'].
- intros a Hr Hba. apply Hpm3'; [exact Hr|]. destruct Hba as [Hb|Hns]; [intros Hx; unfold XW3 in Hx; unfold vf_band in Hb; GEO | intros Hx; apply Hns; right; right; exact Hx]. }
remember (havoc E1 52 (map (getr (ms_regs ms3')) CLOB)) as E2 eqn:HE2.
assert (OLD2 : forall j, (j < 52)%nat -> ew E2 j = ew E1 j) by (intros j Hj; rewrite HE2; apply ew_havoc_old; exact Hj).
assert (Usp2 : bv_unsigned (ew E2 2) = sp0) by (rewrite OLD2 by (cbv; lia); exact Usp1).
assert (G3_2 : ew E2 3 = w64 (as_gp B)) by (rewrite OLD2 by (cbv; lia); exact G3_1).
assert (G4_2 : ew E2 4 = w64 (as_tp B)) by (rewrite OLD2 by (cbv; lia); exact G4_1).
assert (U4_2 : bv_unsigned (ew E2 4) = as_tp B) by (rewrite OLD2 by (cbv; lia); exact U4_1).
assert (A10_2 : ew E2 10 = Z_to_bv 64 code) by (rewrite OLD2 by (cbv; lia); exact A10_1).
assert (A34_2 : bv_unsigned (ew E2 34) = wp) by (rewrite OLD2 by (cbv; lia); exact A34_1).
clear HE2 HS3 VX3.
eapply (SRr_srealizes tfibsegs W _ _ _ (ex_phase W E2 xP_af3 xP_st4 _ _ _ HS3' xP_run4) HAI3').
intros W4 c4 _ HAI4 (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). cbn [cfg_model] in HAI4. clear HS3'.
rewrite ?wvb_wvb in HAI4 |- *.
assert (VX4 : VX B ly S W sp0 mem md exm XS (ms_mem ms4) (with_vm_backing (m_vm_lazy md) mat4 md)).
{ pose proof (VX_run B LAWS ly S W sp0 mem md exm exm_img exm_dec HFownM XS Hstk Htop _ _ (ms_mem ms4) mat4 VX3') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF4. intros Hin. destruct (ex_windows_sound E2 xP_af3 sp0 _ ltac:(vm_compute; reflexivity) Usp2 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 Hw)].
- intros x Hx1 Hx2. apply HFr4. intros Hin. destruct (ex_windows_sound E2 xP_af3 sp0 _ ltac:(vm_compute; reflexivity) Usp2 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 Hw)].
- apply (vf_band_present W E2 xP_st4 ms4 sp0 HS4 ltac:(vm_compute; reflexivity) Usp2 ltac:(lia)). }
clear VX3' HF4 HFr4.
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_xcall_noar B X2_PC XW2 XTRUE X2 W E2 xP_st4 ms4 _ ly S sp0 xP_r04 xP_rest4 68 X23_RA OSP_X23
HS4 eq_refl eq_refl Usp2 G3_2 G4_2 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_X23; lia) ltac:(unfold OSP_X23; lia) ltac:(unfold X23_RA; lia) ltac:(reflexivity)
(ex_rest_ok E2 xP_rest4 (as_tp B) ltac:(vm_compute; reflexivity) U4_2 ltac:(rewrite HTP; unfold TFIB_TPX; lia) ltac:(rewrite HTP; unfold TFIB_TPX; lia))
ltac:(intros r a Hr Ha; destruct (ex_rest_range E2 xP_rest4 (as_tp B) ltac:(vm_compute; reflexivity) U4_2 r a Hr Ha) as [[HcanR Hcr]|Hcr];
[ split; [left; exact HcanR | unfold XW2; unfold A_GOT_canary in Hcr; GEO]
| split; [right; apply HXown; exact Hcr | unfold XW2; unfold ex_cell_range, vo_file, vf_file in Hcr; GEO] ])
ltac:(intros a Hx; unfold XW2 in Hx; unfold vf_band; GEO)
(ex_rest_w E2 xP_rest4 ltac:(vm_compute; reflexivity))
(proj1 VX4) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VX4))) ltac:(exact I)) HAI4).
intros W4' c4' _ HAI4' (-> & ms4' & mat4' & -> & HS4' & HP4' & Hfr4' & Hpm4'). cbn [cfg_model] in HAI4'.
rewrite wvb_wvb in HAI4' |- *.
change (vf_after_icpt 68 xP_st4 X23_RA OSP_X23 0 []) with xP_af4 in HS4'.
remember (havoc E2 68 (map (getr (ms_regs ms4')) CLOB)) as E3 eqn:HE3.
assert (OLD3 : forall j, (j < 68)%nat -> ew E3 j = ew E2 j) by (intros j Hj; rewrite HE3; apply ew_havoc_old; exact Hj).
assert (Usp3 : bv_unsigned (ew E3 2) = sp0) by (rewrite OLD3 by (cbv; lia); exact Usp2).
assert (G3_3 : ew E3 3 = w64 (as_gp B)) by (rewrite OLD3 by (cbv; lia); exact G3_2).
assert (G4_3 : ew E3 4 = w64 (as_tp B)) by (rewrite OLD3 by (cbv; lia); exact G4_2).
assert (U4_3 : bv_unsigned (ew E3 4) = as_tp B) by (rewrite OLD3 by (cbv; lia); exact U4_2).
assert (A10_3 : ew E3 10 = Z_to_bv 64 code) by (rewrite OLD3 by (cbv; lia); exact A10_2).
assert (A34_3 : bv_unsigned (ew E3 34) = wp) by (rewrite OLD3 by (cbv; lia); exact A34_2).
clear HE3 HS4 VX4.
eapply (SRr_srealizes tfibsegs W _ _ _ (ex_phase W E3 xP_af4 xP_st5 _ _ _ HS4' xP_run5) HAI4').
intros W5 c5 _ HAI5 (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). cbn [cfg_model] in HAI5. clear HS4'.
rewrite ?wvb_wvb in HAI5 |- *.
clear HF5 HFr5.
rewrite <- (m_fs_wvb (m_vm_lazy md) mat5 md).
apply (srz_sym_exit W E3 xP_st5 ms5 _ (Z_to_bv 64 code) HAI5 HS5 eq_refl eq_refl); [| rewrite unsigned_lit_small by lia; lia].
match goal with |- sv_denot _ ?x = _ => let x' := eval vm_compute in x in change x with x' end.
cbn [sv_denot]. rewrite Z.add_0_r, A10_3, unsigned_lit_small by lia. reflexivity.
Qed.
Theorem tfib_exit_pristine1 : forall ly S (W : world tfibsegs) regs mem md code tid cval sew,
ecall_pre tfibsegs B ly S W regs mem md ->
2 ^ 44 <= spZ regs -> ly_stk_lo ly + VF_STK <= spZ regs ->
(forall a, vf_band (spZ regs) a -> apresent (w_H W) mem a) ->
getr regs 10 = w64 code -> 0 <= code < 256 ->
as_tp B = TFIB_TPX ->
cells_are ex_consts1 (mrestrict (w_H W) mem) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (as_tp B - 168) 4 tid -> 0 < tid < 2 ^ 31 ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (F_STDERR + 40) 8 sew -> val_mem tfibsegs (mrestrict (w_H W) mem) (F_STDERR + 56) 8 sew -> 0 <= sew < 2 ^ 64 ->
stdout_pristine (mrestrict (w_H W) mem) ->
(forall a, ex_cell_range (as_tp B) a -> ~ aowned B ly S a) ->
(forall a, STDOUT_BUFA <= a < STDOUT_BUFA + STDOUT_BSZ -> ~ aowned B ly S a) ->
AI tfibsegs (w_H W) (w_A W) md ->
srealizes tfibsegs (cfg_at tfibsegs A_exit regs mem md) (t_exit (Z_to_bv 64 code) (m_fs md)).
Proof.
intros ly S W regs mem md code tid cval sew HPRE Hsp44 Hstk Hpres Ha0 Hcode HTP HC Htid Htidr Hgot Hcan Hcv Hew1 Hew2 Hewr HFO HXown HBown HAI0.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity. assert (HVF : VF_STK = 9104) by reflexivity.
assert (HFF : F_STDOUT = 665192) by reflexivity. assert (HFS : FILE_SZ = 232) by reflexivity. assert (HFE : F_STDERR = 664952) by reflexivity.
assert (HBF : STDOUT_BUFA = 6264480) by reflexivity. assert (HBS : STDOUT_BSZ = 1024) by reflexivity. assert (HFI : F_STDIN = 665432) by reflexivity.
assert (HGC : A_GOT_canary = 650296) by reflexivity. assert (HCA : A_canary = 6262736) by reflexivity.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hsp47 : sp0 <= 2 ^ 47) by lia.
set (XS := fun a => aowned B ly S a \/ XW1 a \/ XW2 a \/ XW3 a).
assert (HFownM : forall a, exm a -> ~ aowned B ly S a).
{ intros a Ha. apply HXown. unfold exm in Ha. unfold ex_cell_range. destruct Ha as [H|[H|[H|H]]]; [left; exact H | right; left; exact H | lia | lia]. }
unfold cfg_at. change (w64 A_exit) with (Z_to_bv 64 A_exit).
pose proof (ex_entryP1 W regs mem tid cval sew Hsp44 Hsp47 Hal16 ltac:(intros a Ha; apply Hpres; exact Ha) Htp HTP HC Htid Htidr Hgot Hcan Hcv Hew1 Hew2 Hewr HFO) as HS0.
set (EL := [Z_to_bv 64 tid; Z_to_bv 64 cval; Z_to_bv 64 STDOUT_BUFA; Z_to_bv 64 sew]) in *.
remember (Ereg regs EL) as E0 eqn:HE0.
assert (EE : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E0 i = getr regs r)
by (intros i r Hi; rewrite HE0; exact (ew_Ereg_nat regs _ i r Hi)).
assert (Usp0 : bv_unsigned (ew E0 2) = sp0) by (rewrite (EE 2%nat (2%bv : bv 5) eq_refl); reflexivity).
assert (G3_0 : ew E0 3 = w64 (as_gp B)) by (rewrite (EE 3%nat (3%bv : bv 5) eq_refl); exact Hgp).
assert (G4_0 : ew E0 4 = w64 (as_tp B)) by (rewrite (EE 4%nat (4%bv : bv 5) eq_refl); exact Htp).
assert (U4_0 : bv_unsigned (ew E0 4) = as_tp B) by (rewrite G4_0; apply unsigned_lit_small; rewrite HTP; unfold TFIB_TPX; lia).
assert (A10_0 : ew E0 10 = Z_to_bv 64 code) by (rewrite (EE 10%nat (10%bv : bv 5) eq_refl); exact Ha0).
assert (A32_0 : bv_unsigned (ew E0 32) = tid) by (rewrite HE0; pose proof (ew_Ereg_extra regs EL 0) as X; cbn [nth Nat.add EL] in X; rewrite X; apply unsigned_lit_small; lia).
pose (wp := STDOUT_BUFA). assert (A34_0 : bv_unsigned (ew E0 34) = wp) by (rewrite HE0; pose proof (ew_Ereg_extra regs EL 2) as X; cbn [nth Nat.add EL] in X; rewrite X; apply unsigned_lit_small; unfold wp; GEO).
clear HE0 EE.
pose proof (VX_init B ly S W sp0 mem md exm XS HAR Hpres) as VX0.
eapply (SRr_srealizes tfibsegs W _ _ _ (ex_phase W E0 ss_exP1 xP1_st1 _ _ _ HS0 xP1_run1) HAI0).
intros W1 c1 _ HAI1 (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). cbn [cfg_model] in HAI1. clear HS0.
rewrite ?wvb_wvb in HAI1 |- *.
assert (VX1 : VX B ly S W sp0 mem md exm XS (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat1 md)).
{ pose proof (VX_run B LAWS ly S W sp0 mem md exm exm_img exm_dec HFownM XS Hstk Htop _ _ (ms_mem ms1) mat1 VX0) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF1. intros Hin. destruct (ex_windows_sound E0 ss_exP1 sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 Hw)].
- intros x Hx1 Hx2. apply HFr1. intros Hin. destruct (ex_windows_sound E0 ss_exP1 sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 Hw)].
- apply (vf_band_present W E0 xP1_st1 ms1 sp0 HS1 ltac:(vm_compute; reflexivity) Usp0 ltac:(lia)). }
clear VX0 HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs E0 xP1_st1 _ BC_EQ (SLit 0) (SExt true 32 (SOff 32 0)) HS1
ltac:(apply (beq0_sext32_false E0 32 tid A32_0); lia)) as HS1c.
change (YP06.add_cond xP1_st1 (mkAC (neg_bc BC_EQ) (SLit 0) (SExt true 32 (SOff 32 0)))) with xP1_st1c in HS1c. clear HS1.
eapply (SRr_srealizes tfibsegs W _ _ _ (ex_phase W E0 xP1_st1c xP1_st2 _ _ _ HS1c xP1_run2) HAI1).
intros W2 c2 _ HAI2 (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). cbn [cfg_model] in HAI2. clear HS1c.
rewrite ?wvb_wvb in HAI2 |- *.
assert (VX2 : VX B ly S W sp0 mem md exm XS (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md)).
{ pose proof (VX_run B LAWS ly S W sp0 mem md exm exm_img exm_dec HFownM XS Hstk Htop _ _ (ms_mem ms2) mat2 VX1) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF2. intros Hin. destruct (ex_windows_sound E0 xP1_st1c sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 Hw)].
- intros x Hx1 Hx2. apply HFr2. intros Hin. destruct (ex_windows_sound E0 xP1_st1c sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 Hw)].
- apply (vf_band_present W E0 xP1_st2 ms2 sp0 HS2 ltac:(vm_compute; reflexivity) Usp0 ltac:(lia)). }
clear VX1 HF2 HFr2.
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_xcall B LAWS HB X1_PC XW1 XTRUE X1 W E0 xP1_st2 ms2 _ ly S sp0 xP1_r02 xP1_rest2 36 X1_RA OSP_X1
HS2 eq_refl eq_refl Usp0 G3_0 G4_0 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_X1; lia) ltac:(unfold OSP_X1; lia) ltac:(unfold X1_RA; lia) ltac:(reflexivity)
(ex_rest_ok E0 xP1_rest2 (as_tp B) ltac:(vm_compute; reflexivity) U4_0 ltac:(rewrite HTP; unfold TFIB_TPX; lia) ltac:(rewrite HTP; unfold TFIB_TPX; lia))
ltac:(intros r a Hr Ha; destruct (ex_rest_range E0 xP1_rest2 (as_tp B) ltac:(vm_compute; reflexivity) U4_0 r a Hr Ha) as [[HcanR Hcr]|Hcr];
[ split; [left; exact HcanR | unfold XW1; unfold A_GOT_canary in Hcr; GEO]
| split; [right; apply HXown; exact Hcr | unfold XW1; unfold ex_cell_range, vo_file, vf_file in Hcr; GEO] ])
ltac:(intros a Hx; unfold XW1 in Hx; unfold vf_band; GEO)
(ex_rest_w E0 xP1_rest2 ltac:(vm_compute; reflexivity))
(proj1 VX2) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VX2))) ltac:(exact I)) HAI2).
intros W2' c2' _ HAI2' (-> & ms2' & mat2' & -> & HS2' & HAR2' & HP2' & Hfr2' & Hpm2'). cbn [cfg_model] in HAI2'.
rewrite wvb_wvb in HAI2', HAR2' |- *.
change (vf_after_icpt 36 xP1_st2 X1_RA OSP_X1 0 []) with xP1_af2 in HS2'.
assert (VX2' : VX B ly S W sp0 mem md exm XS (ms_mem ms2') (with_vm_backing (m_vm_lazy md) mat2' md)).
{ eapply (VX_splice B ly S W sp0 mem md exm XS Hstk Htop (ms_mem ms2) _ (ms_mem ms2') _
(fun a => (sp0 + OSP_X1 - ESTACK <= a < sp0 + OSP_X1) \/ aowned B ly S a \/ XW1 a)).
- exact VX2.
- exact HAR2'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat2' mat2 md). apply with_vm_backing_same.
- intros a [Ha|[Ha|Ha]]; [left; unfold vf_band, OSP_X1 in *; lia | right; right; unfold XS; tauto | right; right; unfold XS; tauto].
- intros a Hr Hna. apply Hfr2'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; left; exact H' | intros H'; apply Hna; right; right; exact H'].
- intros a Hr Hba. apply Hpm2'; [exact Hr|]. destruct Hba as [Hb|Hns]; [intros Hx; unfold XW1 in Hx; unfold vf_band in Hb; GEO | intros Hx; apply Hns; right; right; exact Hx]. }
remember (havoc E0 36 (map (getr (ms_regs ms2')) CLOB)) as E1 eqn:HE1.
assert (OLD1 : forall j, (j < 36)%nat -> ew E1 j = ew E0 j) by (intros j Hj; rewrite HE1; apply ew_havoc_old; exact Hj).
assert (Usp1 : bv_unsigned (ew E1 2) = sp0) by (rewrite OLD1 by (cbv; lia); exact Usp0).
assert (G3_1 : ew E1 3 = w64 (as_gp B)) by (rewrite OLD1 by (cbv; lia); exact G3_0).
assert (G4_1 : ew E1 4 = w64 (as_tp B)) by (rewrite OLD1 by (cbv; lia); exact G4_0).
assert (U4_1 : bv_unsigned (ew E1 4) = as_tp B) by (rewrite OLD1 by (cbv; lia); exact U4_0).
assert (A10_1 : ew E1 10 = Z_to_bv 64 code) by (rewrite OLD1 by (cbv; lia); exact A10_0).
assert (A34_1 : bv_unsigned (ew E1 34) = wp) by (rewrite OLD1 by (cbv; lia); exact A34_0).
clear HE1 HS2 VX2.
eapply (SRr_srealizes tfibsegs W _ _ _ (ex_phase W E1 xP1_af2 xP1_st3 _ _ _ HS2' xP1_run3) HAI2').
intros W3 c3 _ HAI3 (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). cbn [cfg_model] in HAI3. clear HS2'.
rewrite ?wvb_wvb in HAI3 |- *.
assert (VX3 : VX B ly S W sp0 mem md exm XS (ms_mem ms3) (with_vm_backing (m_vm_lazy md) mat3 md)).
{ pose proof (VX_run B LAWS ly S W sp0 mem md exm exm_img exm_dec HFownM XS Hstk Htop _ _ (ms_mem ms3) mat3 VX2') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF3. intros Hin. destruct (ex_windows_sound E1 xP1_af2 sp0 _ ltac:(vm_compute; reflexivity) Usp1 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 Hw)].
- intros x Hx1 Hx2. apply HFr3. intros Hin. destruct (ex_windows_sound E1 xP1_af2 sp0 _ ltac:(vm_compute; reflexivity) Usp1 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 Hw)].
- apply (vf_band_present W E1 xP1_st3 ms3 sp0 HS3 ltac:(vm_compute; reflexivity) Usp1 ltac:(lia)). }
clear VX2' HF3 HFr3.
pose proof HS3 as HSc3. destruct HSc3 as (_ & _ & _ & _ & _ & _ & _ & Hmem3 & _). cbn [restrict ms_mem] in Hmem3.
assert (X3P : X3PRE W (ms_mem ms3)).
{ split; (eapply (val_mem_of_lit E1 (mrestrict (w_H W) (ms_mem ms3)) (ss_mem xP1_st3) _ _ _ Hmem3); vm_compute; reflexivity). }
clear Hmem3.
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_xcall B LAWS HB X3_PC XW3 X3PRE X3 W E1 xP1_st3 ms3 _ ly S sp0 xP1_r03 xP1_rest3 52 X23_RA OSP_X23
HS3 eq_refl eq_refl Usp1 G3_1 G4_1 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_X23; lia) ltac:(unfold OSP_X23; lia) ltac:(unfold X23_RA; lia) ltac:(reflexivity)
(ex_rest_ok E1 xP1_rest3 (as_tp B) ltac:(vm_compute; reflexivity) U4_1 ltac:(rewrite HTP; unfold TFIB_TPX; lia) ltac:(rewrite HTP; unfold TFIB_TPX; lia))
ltac:(intros r a Hr Ha; destruct (ex_rest_range E1 xP1_rest3 (as_tp B) ltac:(vm_compute; reflexivity) U4_1 r a Hr Ha) as [[HcanR Hcr]|Hcr];
[ split; [left; exact HcanR | unfold XW3; unfold A_GOT_canary in Hcr; GEO]
| split; [right; apply HXown; exact Hcr | unfold XW3; unfold ex_cell_range, vo_file, vf_file in Hcr; GEO] ])
ltac:(intros a Hx; unfold XW3 in Hx; unfold vf_band; GEO)
(ex_rest_w E1 xP1_rest3 ltac:(vm_compute; reflexivity))
(proj1 VX3) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VX3))) ltac:(exact X3P)) HAI3).
intros W3' c3' _ HAI3' (-> & ms3' & mat3' & -> & HS3' & HAR3' & HP3' & Hfr3' & Hpm3'). cbn [cfg_model] in HAI3'.
rewrite wvb_wvb in HAI3', HAR3' |- *.
change (vf_after_icpt 52 xP1_st3 X23_RA OSP_X23 0 []) with xP1_af3 in HS3'.
assert (VX3' : VX B ly S W sp0 mem md exm XS (ms_mem ms3') (with_vm_backing (m_vm_lazy md) mat3' md)).
{ eapply (VX_splice B ly S W sp0 mem md exm XS Hstk Htop (ms_mem ms3) _ (ms_mem ms3') _
(fun a => (sp0 + OSP_X23 - ESTACK <= a < sp0 + OSP_X23) \/ aowned B ly S a \/ XW3 a)).
- exact VX3.
- exact HAR3'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat3' mat3 md). apply with_vm_backing_same.
- intros a [Ha|[Ha|Ha]]; [left; unfold vf_band, OSP_X23 in *; lia | right; right; unfold XS; tauto | right; right; unfold XS; tauto].
- intros a Hr Hna. apply Hfr3'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; left; exact H' | intros H'; apply Hna; right; right; exact H'].
- intros a Hr Hba. apply Hpm3'; [exact Hr|]. destruct Hba as [Hb|Hns]; [intros Hx; unfold XW3 in Hx; unfold vf_band in Hb; GEO | intros Hx; apply Hns; right; right; exact Hx]. }
remember (havoc E1 52 (map (getr (ms_regs ms3')) CLOB)) as E2 eqn:HE2.
assert (OLD2 : forall j, (j < 52)%nat -> ew E2 j = ew E1 j) by (intros j Hj; rewrite HE2; apply ew_havoc_old; exact Hj).
assert (Usp2 : bv_unsigned (ew E2 2) = sp0) by (rewrite OLD2 by (cbv; lia); exact Usp1).
assert (G3_2 : ew E2 3 = w64 (as_gp B)) by (rewrite OLD2 by (cbv; lia); exact G3_1).
assert (G4_2 : ew E2 4 = w64 (as_tp B)) by (rewrite OLD2 by (cbv; lia); exact G4_1).
assert (U4_2 : bv_unsigned (ew E2 4) = as_tp B) by (rewrite OLD2 by (cbv; lia); exact U4_1).
assert (A10_2 : ew E2 10 = Z_to_bv 64 code) by (rewrite OLD2 by (cbv; lia); exact A10_1).
assert (A34_2 : bv_unsigned (ew E2 34) = wp) by (rewrite OLD2 by (cbv; lia); exact A34_1).
clear HE2 HS3 VX3.
eapply (SRr_srealizes tfibsegs W _ _ _ (ex_phase W E2 xP1_af3 xP1_st4 _ _ _ HS3' xP1_run4) HAI3').
intros W4 c4 _ HAI4 (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). cbn [cfg_model] in HAI4. clear HS3'.
rewrite ?wvb_wvb in HAI4 |- *.
assert (VX4 : VX B ly S W sp0 mem md exm XS (ms_mem ms4) (with_vm_backing (m_vm_lazy md) mat4 md)).
{ pose proof (VX_run B LAWS ly S W sp0 mem md exm exm_img exm_dec HFownM XS Hstk Htop _ _ (ms_mem ms4) mat4 VX3') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF4. intros Hin. destruct (ex_windows_sound E2 xP1_af3 sp0 _ ltac:(vm_compute; reflexivity) Usp2 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 Hw)].
- intros x Hx1 Hx2. apply HFr4. intros Hin. destruct (ex_windows_sound E2 xP1_af3 sp0 _ ltac:(vm_compute; reflexivity) Usp2 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 Hw)].
- apply (vf_band_present W E2 xP1_st4 ms4 sp0 HS4 ltac:(vm_compute; reflexivity) Usp2 ltac:(lia)). }
clear VX3' HF4 HFr4.
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_xcall_noar B X2_PC XW2 XTRUE X2 W E2 xP1_st4 ms4 _ ly S sp0 xP1_r04 xP1_rest4 68 X23_RA OSP_X23
HS4 eq_refl eq_refl Usp2 G3_2 G4_2 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_X23; lia) ltac:(unfold OSP_X23; lia) ltac:(unfold X23_RA; lia) ltac:(reflexivity)
(ex_rest_ok E2 xP1_rest4 (as_tp B) ltac:(vm_compute; reflexivity) U4_2 ltac:(rewrite HTP; unfold TFIB_TPX; lia) ltac:(rewrite HTP; unfold TFIB_TPX; lia))
ltac:(intros r a Hr Ha; destruct (ex_rest_range E2 xP1_rest4 (as_tp B) ltac:(vm_compute; reflexivity) U4_2 r a Hr Ha) as [[HcanR Hcr]|Hcr];
[ split; [left; exact HcanR | unfold XW2; unfold A_GOT_canary in Hcr; GEO]
| split; [right; apply HXown; exact Hcr | unfold XW2; unfold ex_cell_range, vo_file, vf_file in Hcr; GEO] ])
ltac:(intros a Hx; unfold XW2 in Hx; unfold vf_band; GEO)
(ex_rest_w E2 xP1_rest4 ltac:(vm_compute; reflexivity))
(proj1 VX4) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VX4))) ltac:(exact I)) HAI4).
intros W4' c4' _ HAI4' (-> & ms4' & mat4' & -> & HS4' & HP4' & Hfr4' & Hpm4'). cbn [cfg_model] in HAI4'.
rewrite wvb_wvb in HAI4' |- *.
change (vf_after_icpt 68 xP1_st4 X23_RA OSP_X23 0 []) with xP1_af4 in HS4'.
remember (havoc E2 68 (map (getr (ms_regs ms4')) CLOB)) as E3 eqn:HE3.
assert (OLD3 : forall j, (j < 68)%nat -> ew E3 j = ew E2 j) by (intros j Hj; rewrite HE3; apply ew_havoc_old; exact Hj).
assert (Usp3 : bv_unsigned (ew E3 2) = sp0) by (rewrite OLD3 by (cbv; lia); exact Usp2).
assert (G3_3 : ew E3 3 = w64 (as_gp B)) by (rewrite OLD3 by (cbv; lia); exact G3_2).
assert (G4_3 : ew E3 4 = w64 (as_tp B)) by (rewrite OLD3 by (cbv; lia); exact G4_2).
assert (U4_3 : bv_unsigned (ew E3 4) = as_tp B) by (rewrite OLD3 by (cbv; lia); exact U4_2).
assert (A10_3 : ew E3 10 = Z_to_bv 64 code) by (rewrite OLD3 by (cbv; lia); exact A10_2).
assert (A34_3 : bv_unsigned (ew E3 34) = wp) by (rewrite OLD3 by (cbv; lia); exact A34_2).
clear HE3 HS4 VX4.
eapply (SRr_srealizes tfibsegs W _ _ _ (ex_phase W E3 xP1_af4 xP1_st5 _ _ _ HS4' xP1_run5) HAI4').
intros W5 c5 _ HAI5 (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). cbn [cfg_model] in HAI5. clear HS4'.
rewrite ?wvb_wvb in HAI5 |- *.
clear HF5 HFr5.
rewrite <- (m_fs_wvb (m_vm_lazy md) mat5 md).
apply (srz_sym_exit W E3 xP1_st5 ms5 _ (Z_to_bv 64 code) HAI5 HS5 eq_refl eq_refl); [| rewrite unsigned_lit_small by lia; lia].
match goal with |- sv_denot _ ?x = _ => let x' := eval vm_compute in x in change x with x' end.
cbn [sv_denot]. rewrite Z.add_0_r, A10_3, unsigned_lit_small by lia. reflexivity.
Qed.
Theorem tfib_exit_empty : forall ly S (W : world tfibsegs) regs mem md code tid cval sew,
ecall_pre tfibsegs B ly S W regs mem md ->
2 ^ 44 <= spZ regs -> ly_stk_lo ly + VF_STK <= spZ regs ->
(forall a, vf_band (spZ regs) a -> apresent (w_H W) mem a) ->
getr regs 10 = w64 code -> 0 <= code < 256 ->
as_tp B = TFIB_TPX ->
cells_are ex_consts (mrestrict (w_H W) mem) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (as_tp B - 168) 4 tid -> 0 < tid < 2 ^ 31 ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (F_STDERR + 40) 8 sew -> val_mem tfibsegs (mrestrict (w_H W) mem) (F_STDERR + 56) 8 sew -> 0 <= sew < 2 ^ 64 ->
stdout_mid STDOUT_BUFA (mrestrict (w_H W) mem) ->
(forall a, ex_cell_range (as_tp B) a -> ~ aowned B ly S a) ->
(forall a, STDOUT_BUFA <= a < STDOUT_BUFA + STDOUT_BSZ -> ~ aowned B ly S a) ->
AI tfibsegs (w_H W) (w_A W) md ->
srealizes tfibsegs (cfg_at tfibsegs A_exit regs mem md) (t_exit (Z_to_bv 64 code) (m_fs md)).
Proof.
intros ly S W regs mem md code tid cval sew HPRE Hsp44 Hstk Hpres Ha0 Hcode HTP HC Htid Htidr Hgot Hcan Hcv Hew1 Hew2 Hewr HFO HXown HBown HAI0.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity. assert (HVF : VF_STK = 9104) by reflexivity.
assert (HFF : F_STDOUT = 665192) by reflexivity. assert (HFS : FILE_SZ = 232) by reflexivity. assert (HFE : F_STDERR = 664952) by reflexivity.
assert (HBF : STDOUT_BUFA = 6264480) by reflexivity. assert (HBS : STDOUT_BSZ = 1024) by reflexivity. assert (HFI : F_STDIN = 665432) by reflexivity.
assert (HGC : A_GOT_canary = 650296) by reflexivity. assert (HCA : A_canary = 6262736) by reflexivity.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hsp47 : sp0 <= 2 ^ 47) by lia.
set (XS := fun a => aowned B ly S a \/ XW1 a \/ XW2 a \/ XW3 a).
assert (HFownM : forall a, exm a -> ~ aowned B ly S a).
{ intros a Ha. apply HXown. unfold exm in Ha. unfold ex_cell_range. destruct Ha as [H|[H|[H|H]]]; [left; exact H | right; left; exact H | lia | lia]. }
unfold cfg_at. change (w64 A_exit) with (Z_to_bv 64 A_exit).
pose proof (ex_entryE W regs mem tid cval sew Hsp44 Hsp47 Hal16 ltac:(intros a Ha; apply Hpres; exact Ha) Htp HTP HC Htid Htidr Hgot Hcan Hcv Hew1 Hew2 Hewr HFO) as HS0.
set (EL := [Z_to_bv 64 tid; Z_to_bv 64 cval; Z_to_bv 64 STDOUT_BUFA; Z_to_bv 64 sew]) in *.
remember (Ereg regs EL) as E0 eqn:HE0.
assert (EE : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E0 i = getr regs r)
by (intros i r Hi; rewrite HE0; exact (ew_Ereg_nat regs _ i r Hi)).
assert (Usp0 : bv_unsigned (ew E0 2) = sp0) by (rewrite (EE 2%nat (2%bv : bv 5) eq_refl); reflexivity).
assert (G3_0 : ew E0 3 = w64 (as_gp B)) by (rewrite (EE 3%nat (3%bv : bv 5) eq_refl); exact Hgp).
assert (G4_0 : ew E0 4 = w64 (as_tp B)) by (rewrite (EE 4%nat (4%bv : bv 5) eq_refl); exact Htp).
assert (U4_0 : bv_unsigned (ew E0 4) = as_tp B) by (rewrite G4_0; apply unsigned_lit_small; rewrite HTP; unfold TFIB_TPX; lia).
assert (A10_0 : ew E0 10 = Z_to_bv 64 code) by (rewrite (EE 10%nat (10%bv : bv 5) eq_refl); exact Ha0).
assert (A32_0 : bv_unsigned (ew E0 32) = tid) by (rewrite HE0; pose proof (ew_Ereg_extra regs EL 0) as X; cbn [nth Nat.add EL] in X; rewrite X; apply unsigned_lit_small; lia).
pose (wp := STDOUT_BUFA). assert (A34_0 : bv_unsigned (ew E0 34) = wp) by (rewrite HE0; pose proof (ew_Ereg_extra regs EL 2) as X; cbn [nth Nat.add EL] in X; rewrite X; apply unsigned_lit_small; unfold wp; GEO).
clear HE0 EE.
pose proof (VX_init B ly S W sp0 mem md exm XS HAR Hpres) as VX0.
eapply (SRr_srealizes tfibsegs W _ _ _ (ex_phase W E0 ss_exE xE_st1 _ _ _ HS0 xE_run1) HAI0).
intros W1 c1 _ HAI1 (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). cbn [cfg_model] in HAI1. clear HS0.
rewrite ?wvb_wvb in HAI1 |- *.
assert (VX1 : VX B ly S W sp0 mem md exm XS (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat1 md)).
{ pose proof (VX_run B LAWS ly S W sp0 mem md exm exm_img exm_dec HFownM XS Hstk Htop _ _ (ms_mem ms1) mat1 VX0) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF1. intros Hin. destruct (ex_windows_sound E0 ss_exE sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 Hw)].
- intros x Hx1 Hx2. apply HFr1. intros Hin. destruct (ex_windows_sound E0 ss_exE sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 Hw)].
- apply (vf_band_present W E0 xE_st1 ms1 sp0 HS1 ltac:(vm_compute; reflexivity) Usp0 ltac:(lia)). }
clear VX0 HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs E0 xE_st1 _ BC_EQ (SLit 0) (SExt true 32 (SOff 32 0)) HS1
ltac:(apply (beq0_sext32_false E0 32 tid A32_0); lia)) as HS1c.
change (YP06.add_cond xE_st1 (mkAC (neg_bc BC_EQ) (SLit 0) (SExt true 32 (SOff 32 0)))) with xE_st1c in HS1c. clear HS1.
eapply (SRr_srealizes tfibsegs W _ _ _ (ex_phase W E0 xE_st1c xE_st2 _ _ _ HS1c xE_run2) HAI1).
intros W2 c2 _ HAI2 (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). cbn [cfg_model] in HAI2. clear HS1c.
rewrite ?wvb_wvb in HAI2 |- *.
assert (VX2 : VX B ly S W sp0 mem md exm XS (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md)).
{ pose proof (VX_run B LAWS ly S W sp0 mem md exm exm_img exm_dec HFownM XS Hstk Htop _ _ (ms_mem ms2) mat2 VX1) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF2. intros Hin. destruct (ex_windows_sound E0 xE_st1c sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 Hw)].
- intros x Hx1 Hx2. apply HFr2. intros Hin. destruct (ex_windows_sound E0 xE_st1c sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 Hw)].
- apply (vf_band_present W E0 xE_st2 ms2 sp0 HS2 ltac:(vm_compute; reflexivity) Usp0 ltac:(lia)). }
clear VX1 HF2 HFr2.
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_xcall B LAWS HB X1_PC XW1 XTRUE X1 W E0 xE_st2 ms2 _ ly S sp0 xE_r02 xE_rest2 36 X1_RA OSP_X1
HS2 eq_refl eq_refl Usp0 G3_0 G4_0 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_X1; lia) ltac:(unfold OSP_X1; lia) ltac:(unfold X1_RA; lia) ltac:(reflexivity)
(ex_rest_ok E0 xE_rest2 (as_tp B) ltac:(vm_compute; reflexivity) U4_0 ltac:(rewrite HTP; unfold TFIB_TPX; lia) ltac:(rewrite HTP; unfold TFIB_TPX; lia))
ltac:(intros r a Hr Ha; destruct (ex_rest_range E0 xE_rest2 (as_tp B) ltac:(vm_compute; reflexivity) U4_0 r a Hr Ha) as [[HcanR Hcr]|Hcr];
[ split; [left; exact HcanR | unfold XW1; unfold A_GOT_canary in Hcr; GEO]
| split; [right; apply HXown; exact Hcr | unfold XW1; unfold ex_cell_range, vo_file, vf_file in Hcr; GEO] ])
ltac:(intros a Hx; unfold XW1 in Hx; unfold vf_band; GEO)
(ex_rest_w E0 xE_rest2 ltac:(vm_compute; reflexivity))
(proj1 VX2) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VX2))) ltac:(exact I)) HAI2).
intros W2' c2' _ HAI2' (-> & ms2' & mat2' & -> & HS2' & HAR2' & HP2' & Hfr2' & Hpm2'). cbn [cfg_model] in HAI2'.
rewrite wvb_wvb in HAI2', HAR2' |- *.
change (vf_after_icpt 36 xE_st2 X1_RA OSP_X1 0 []) with xE_af2 in HS2'.
assert (VX2' : VX B ly S W sp0 mem md exm XS (ms_mem ms2') (with_vm_backing (m_vm_lazy md) mat2' md)).
{ eapply (VX_splice B ly S W sp0 mem md exm XS Hstk Htop (ms_mem ms2) _ (ms_mem ms2') _
(fun a => (sp0 + OSP_X1 - ESTACK <= a < sp0 + OSP_X1) \/ aowned B ly S a \/ XW1 a)).
- exact VX2.
- exact HAR2'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat2' mat2 md). apply with_vm_backing_same.
- intros a [Ha|[Ha|Ha]]; [left; unfold vf_band, OSP_X1 in *; lia | right; right; unfold XS; tauto | right; right; unfold XS; tauto].
- intros a Hr Hna. apply Hfr2'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; left; exact H' | intros H'; apply Hna; right; right; exact H'].
- intros a Hr Hba. apply Hpm2'; [exact Hr|]. destruct Hba as [Hb|Hns]; [intros Hx; unfold XW1 in Hx; unfold vf_band in Hb; GEO | intros Hx; apply Hns; right; right; exact Hx]. }
remember (havoc E0 36 (map (getr (ms_regs ms2')) CLOB)) as E1 eqn:HE1.
assert (OLD1 : forall j, (j < 36)%nat -> ew E1 j = ew E0 j) by (intros j Hj; rewrite HE1; apply ew_havoc_old; exact Hj).
assert (Usp1 : bv_unsigned (ew E1 2) = sp0) by (rewrite OLD1 by (cbv; lia); exact Usp0).
assert (G3_1 : ew E1 3 = w64 (as_gp B)) by (rewrite OLD1 by (cbv; lia); exact G3_0).
assert (G4_1 : ew E1 4 = w64 (as_tp B)) by (rewrite OLD1 by (cbv; lia); exact G4_0).
assert (U4_1 : bv_unsigned (ew E1 4) = as_tp B) by (rewrite OLD1 by (cbv; lia); exact U4_0).
assert (A10_1 : ew E1 10 = Z_to_bv 64 code) by (rewrite OLD1 by (cbv; lia); exact A10_0).
assert (A34_1 : bv_unsigned (ew E1 34) = wp) by (rewrite OLD1 by (cbv; lia); exact A34_0).
clear HE1 HS2 VX2.
eapply (SRr_srealizes tfibsegs W _ _ _ (ex_phase W E1 xE_af2 xE_st3 _ _ _ HS2' xE_run3) HAI2').
intros W3 c3 _ HAI3 (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). cbn [cfg_model] in HAI3. clear HS2'.
rewrite ?wvb_wvb in HAI3 |- *.
assert (VX3 : VX B ly S W sp0 mem md exm XS (ms_mem ms3) (with_vm_backing (m_vm_lazy md) mat3 md)).
{ pose proof (VX_run B LAWS ly S W sp0 mem md exm exm_img exm_dec HFownM XS Hstk Htop _ _ (ms_mem ms3) mat3 VX2') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF3. intros Hin. destruct (ex_windows_sound E1 xE_af2 sp0 _ ltac:(vm_compute; reflexivity) Usp1 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 Hw)].
- intros x Hx1 Hx2. apply HFr3. intros Hin. destruct (ex_windows_sound E1 xE_af2 sp0 _ ltac:(vm_compute; reflexivity) Usp1 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 Hw)].
- apply (vf_band_present W E1 xE_st3 ms3 sp0 HS3 ltac:(vm_compute; reflexivity) Usp1 ltac:(lia)). }
clear VX2' HF3 HFr3.
pose proof HS3 as HSc3. destruct HSc3 as (_ & _ & _ & _ & _ & _ & _ & Hmem3 & _). cbn [restrict ms_mem] in Hmem3.
assert (X3P : X3PRE W (ms_mem ms3)).
{ split; (eapply (val_mem_of_lit E1 (mrestrict (w_H W) (ms_mem ms3)) (ss_mem xE_st3) _ _ _ Hmem3); vm_compute; reflexivity). }
clear Hmem3.
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_xcall B LAWS HB X3_PC XW3 X3PRE X3 W E1 xE_st3 ms3 _ ly S sp0 xE_r03 xE_rest3 52 X23_RA OSP_X23
HS3 eq_refl eq_refl Usp1 G3_1 G4_1 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_X23; lia) ltac:(unfold OSP_X23; lia) ltac:(unfold X23_RA; lia) ltac:(reflexivity)
(ex_rest_ok E1 xE_rest3 (as_tp B) ltac:(vm_compute; reflexivity) U4_1 ltac:(rewrite HTP; unfold TFIB_TPX; lia) ltac:(rewrite HTP; unfold TFIB_TPX; lia))
ltac:(intros r a Hr Ha; destruct (ex_rest_range E1 xE_rest3 (as_tp B) ltac:(vm_compute; reflexivity) U4_1 r a Hr Ha) as [[HcanR Hcr]|Hcr];
[ split; [left; exact HcanR | unfold XW3; unfold A_GOT_canary in Hcr; GEO]
| split; [right; apply HXown; exact Hcr | unfold XW3; unfold ex_cell_range, vo_file, vf_file in Hcr; GEO] ])
ltac:(intros a Hx; unfold XW3 in Hx; unfold vf_band; GEO)
(ex_rest_w E1 xE_rest3 ltac:(vm_compute; reflexivity))
(proj1 VX3) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VX3))) ltac:(exact X3P)) HAI3).
intros W3' c3' _ HAI3' (-> & ms3' & mat3' & -> & HS3' & HAR3' & HP3' & Hfr3' & Hpm3'). cbn [cfg_model] in HAI3'.
rewrite wvb_wvb in HAI3', HAR3' |- *.
change (vf_after_icpt 52 xE_st3 X23_RA OSP_X23 0 []) with xE_af3 in HS3'.
assert (VX3' : VX B ly S W sp0 mem md exm XS (ms_mem ms3') (with_vm_backing (m_vm_lazy md) mat3' md)).
{ eapply (VX_splice B ly S W sp0 mem md exm XS Hstk Htop (ms_mem ms3) _ (ms_mem ms3') _
(fun a => (sp0 + OSP_X23 - ESTACK <= a < sp0 + OSP_X23) \/ aowned B ly S a \/ XW3 a)).
- exact VX3.
- exact HAR3'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat3' mat3 md). apply with_vm_backing_same.
- intros a [Ha|[Ha|Ha]]; [left; unfold vf_band, OSP_X23 in *; lia | right; right; unfold XS; tauto | right; right; unfold XS; tauto].
- intros a Hr Hna. apply Hfr3'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; left; exact H' | intros H'; apply Hna; right; right; exact H'].
- intros a Hr Hba. apply Hpm3'; [exact Hr|]. destruct Hba as [Hb|Hns]; [intros Hx; unfold XW3 in Hx; unfold vf_band in Hb; GEO | intros Hx; apply Hns; right; right; exact Hx]. }
remember (havoc E1 52 (map (getr (ms_regs ms3')) CLOB)) as E2 eqn:HE2.
assert (OLD2 : forall j, (j < 52)%nat -> ew E2 j = ew E1 j) by (intros j Hj; rewrite HE2; apply ew_havoc_old; exact Hj).
assert (Usp2 : bv_unsigned (ew E2 2) = sp0) by (rewrite OLD2 by (cbv; lia); exact Usp1).
assert (G3_2 : ew E2 3 = w64 (as_gp B)) by (rewrite OLD2 by (cbv; lia); exact G3_1).
assert (G4_2 : ew E2 4 = w64 (as_tp B)) by (rewrite OLD2 by (cbv; lia); exact G4_1).
assert (U4_2 : bv_unsigned (ew E2 4) = as_tp B) by (rewrite OLD2 by (cbv; lia); exact U4_1).
assert (A10_2 : ew E2 10 = Z_to_bv 64 code) by (rewrite OLD2 by (cbv; lia); exact A10_1).
assert (A34_2 : bv_unsigned (ew E2 34) = wp) by (rewrite OLD2 by (cbv; lia); exact A34_1).
clear HE2 HS3 VX3.
eapply (SRr_srealizes tfibsegs W _ _ _ (ex_phase W E2 xE_af3 xE_st4 _ _ _ HS3' xE_run4) HAI3').
intros W4 c4 _ HAI4 (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). cbn [cfg_model] in HAI4. clear HS3'.
rewrite ?wvb_wvb in HAI4 |- *.
assert (VX4 : VX B ly S W sp0 mem md exm XS (ms_mem ms4) (with_vm_backing (m_vm_lazy md) mat4 md)).
{ pose proof (VX_run B LAWS ly S W sp0 mem md exm exm_img exm_dec HFownM XS Hstk Htop _ _ (ms_mem ms4) mat4 VX3') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF4. intros Hin. destruct (ex_windows_sound E2 xE_af3 sp0 _ ltac:(vm_compute; reflexivity) Usp2 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 Hw)].
- intros x Hx1 Hx2. apply HFr4. intros Hin. destruct (ex_windows_sound E2 xE_af3 sp0 _ ltac:(vm_compute; reflexivity) Usp2 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 Hw)].
- apply (vf_band_present W E2 xE_st4 ms4 sp0 HS4 ltac:(vm_compute; reflexivity) Usp2 ltac:(lia)). }
clear VX3' HF4 HFr4.
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_xcall_noar B X2_PC XW2 XTRUE X2 W E2 xE_st4 ms4 _ ly S sp0 xE_r04 xE_rest4 68 X23_RA OSP_X23
HS4 eq_refl eq_refl Usp2 G3_2 G4_2 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_X23; lia) ltac:(unfold OSP_X23; lia) ltac:(unfold X23_RA; lia) ltac:(reflexivity)
(ex_rest_ok E2 xE_rest4 (as_tp B) ltac:(vm_compute; reflexivity) U4_2 ltac:(rewrite HTP; unfold TFIB_TPX; lia) ltac:(rewrite HTP; unfold TFIB_TPX; lia))
ltac:(intros r a Hr Ha; destruct (ex_rest_range E2 xE_rest4 (as_tp B) ltac:(vm_compute; reflexivity) U4_2 r a Hr Ha) as [[HcanR Hcr]|Hcr];
[ split; [left; exact HcanR | unfold XW2; unfold A_GOT_canary in Hcr; GEO]
| split; [right; apply HXown; exact Hcr | unfold XW2; unfold ex_cell_range, vo_file, vf_file in Hcr; GEO] ])
ltac:(intros a Hx; unfold XW2 in Hx; unfold vf_band; GEO)
(ex_rest_w E2 xE_rest4 ltac:(vm_compute; reflexivity))
(proj1 VX4) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VX4))) ltac:(exact I)) HAI4).
intros W4' c4' _ HAI4' (-> & ms4' & mat4' & -> & HS4' & HP4' & Hfr4' & Hpm4'). cbn [cfg_model] in HAI4'.
rewrite wvb_wvb in HAI4' |- *.
change (vf_after_icpt 68 xE_st4 X23_RA OSP_X23 0 []) with xE_af4 in HS4'.
remember (havoc E2 68 (map (getr (ms_regs ms4')) CLOB)) as E3 eqn:HE3.
assert (OLD3 : forall j, (j < 68)%nat -> ew E3 j = ew E2 j) by (intros j Hj; rewrite HE3; apply ew_havoc_old; exact Hj).
assert (Usp3 : bv_unsigned (ew E3 2) = sp0) by (rewrite OLD3 by (cbv; lia); exact Usp2).
assert (G3_3 : ew E3 3 = w64 (as_gp B)) by (rewrite OLD3 by (cbv; lia); exact G3_2).
assert (G4_3 : ew E3 4 = w64 (as_tp B)) by (rewrite OLD3 by (cbv; lia); exact G4_2).
assert (U4_3 : bv_unsigned (ew E3 4) = as_tp B) by (rewrite OLD3 by (cbv; lia); exact U4_2).
assert (A10_3 : ew E3 10 = Z_to_bv 64 code) by (rewrite OLD3 by (cbv; lia); exact A10_2).
assert (A34_3 : bv_unsigned (ew E3 34) = wp) by (rewrite OLD3 by (cbv; lia); exact A34_2).
clear HE3 HS4 VX4.
eapply (SRr_srealizes tfibsegs W _ _ _ (ex_phase W E3 xE_af4 xE_st5 _ _ _ HS4' xE_run5) HAI4').
intros W5 c5 _ HAI5 (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). cbn [cfg_model] in HAI5. clear HS4'.
rewrite ?wvb_wvb in HAI5 |- *.
clear HF5 HFr5.
rewrite <- (m_fs_wvb (m_vm_lazy md) mat5 md).
apply (srz_sym_exit W E3 xE_st5 ms5 _ (Z_to_bv 64 code) HAI5 HS5 eq_refl eq_refl); [| rewrite unsigned_lit_small by lia; lia].
match goal with |- sv_denot _ ?x = _ => let x' := eval vm_compute in x in change x with x' end.
cbn [sv_denot]. rewrite Z.add_0_r, A10_3, unsigned_lit_small by lia. reflexivity.
Qed.
Theorem tfib_exit_flush : forall ly S (W : world tfibsegs) regs mem md code tid cval sew wp (pend : list byte) ch,
ecall_pre tfibsegs B ly S W regs mem md ->
2 ^ 44 <= spZ regs -> ly_stk_lo ly + VF_STK <= spZ regs ->
(forall a, vf_band (spZ regs) a -> apresent (w_H W) mem a) ->
getr regs 10 = w64 code -> 0 <= code < 256 ->
as_tp B = TFIB_TPX ->
cells_are ex_consts (mrestrict (w_H W) mem) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (as_tp B - 168) 4 tid -> 0 < tid < 2 ^ 31 ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (F_STDERR + 40) 8 sew -> val_mem tfibsegs (mrestrict (w_H W) mem) (F_STDERR + 56) 8 sew -> 0 <= sew < 2 ^ 64 ->
stdout_mid wp (mrestrict (w_H W) mem) -> wp = STDOUT_BUFA + Z.of_nat (length pend) -> (0 < length pend)%nat -> wp <= STDOUT_BUFA + STDOUT_BSZ ->
(forall i, (i < length pend)%nat -> aview tfibsegs (w_H W) mem (STDOUT_BUFA + Z.of_nat i) = Some (bv_unsigned (nth i pend 0%bv))) ->
fdchan (Z_to_bv 64 1) ch md ->
(forall a, ex_cell_range (as_tp B) a -> ~ aowned B ly S a) ->
(forall a, STDOUT_BUFA <= a < STDOUT_BUFA + STDOUT_BSZ -> ~ aowned B ly S a) ->
AI tfibsegs (w_H W) (w_A W) md ->
srealizes tfibsegs (cfg_at tfibsegs A_exit regs mem md) (t_emit (map (WriteEv ch) pend) (t_exit (Z_to_bv 64 code) (m_fs md))).
Proof.
intros ly S W regs mem md code tid cval sew wp pend ch HPRE Hsp44 Hstk Hpres Ha0 Hcode HTP HC Htid Htidr Hgot Hcan Hcv Hew1 Hew2 Hewr HFO Hwp Hpend Hwphi HPEND Hch HXown HBown HAI0.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity. assert (HVF : VF_STK = 9104) by reflexivity.
assert (HFF : F_STDOUT = 665192) by reflexivity. assert (HFS : FILE_SZ = 232) by reflexivity. assert (HFE : F_STDERR = 664952) by reflexivity.
assert (HBF : STDOUT_BUFA = 6264480) by reflexivity. assert (HBS : STDOUT_BSZ = 1024) by reflexivity. assert (HFI : F_STDIN = 665432) by reflexivity.
assert (HGC : A_GOT_canary = 650296) by reflexivity. assert (HCA : A_canary = 6262736) by reflexivity.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hsp47 : sp0 <= 2 ^ 47) by lia.
set (XS := fun a => aowned B ly S a \/ XW1 a \/ XW2 a \/ XW3 a).
assert (HFownM : forall a, exm a -> ~ aowned B ly S a).
{ intros a Ha. apply HXown. unfold exm in Ha. unfold ex_cell_range. destruct Ha as [H|[H|[H|H]]]; [left; exact H | right; left; exact H | lia | lia]. }
unfold cfg_at. change (w64 A_exit) with (Z_to_bv 64 A_exit).
pose proof (ex_entryF W regs mem tid cval sew wp Hsp44 Hsp47 Hal16 ltac:(intros a Ha; apply Hpres; exact Ha) Htp HTP HC Htid Htidr Hgot Hcan Hcv Hew1 Hew2 Hewr HFO ltac:(lia)) as HS0.
set (EL := [Z_to_bv 64 tid; Z_to_bv 64 cval; Z_to_bv 64 wp; Z_to_bv 64 sew]) in *.
remember (Ereg regs EL) as E0 eqn:HE0.
assert (EE : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E0 i = getr regs r)
by (intros i r Hi; rewrite HE0; exact (ew_Ereg_nat regs _ i r Hi)).
assert (Usp0 : bv_unsigned (ew E0 2) = sp0) by (rewrite (EE 2%nat (2%bv : bv 5) eq_refl); reflexivity).
assert (G3_0 : ew E0 3 = w64 (as_gp B)) by (rewrite (EE 3%nat (3%bv : bv 5) eq_refl); exact Hgp).
assert (G4_0 : ew E0 4 = w64 (as_tp B)) by (rewrite (EE 4%nat (4%bv : bv 5) eq_refl); exact Htp).
assert (U4_0 : bv_unsigned (ew E0 4) = as_tp B) by (rewrite G4_0; apply unsigned_lit_small; rewrite HTP; unfold TFIB_TPX; lia).
assert (A10_0 : ew E0 10 = Z_to_bv 64 code) by (rewrite (EE 10%nat (10%bv : bv 5) eq_refl); exact Ha0).
assert (A32_0 : bv_unsigned (ew E0 32) = tid) by (rewrite HE0; pose proof (ew_Ereg_extra regs EL 0) as X; cbn [nth Nat.add EL] in X; rewrite X; apply unsigned_lit_small; lia).
assert (A34_0 : bv_unsigned (ew E0 34) = wp) by (rewrite HE0; pose proof (ew_Ereg_extra regs EL 2) as X; cbn [nth Nat.add EL] in X; rewrite X; apply unsigned_lit_small; GEO).
clear HE0 EE.
pose proof (VX_init B ly S W sp0 mem md exm XS HAR Hpres) as VX0.
pose proof HPEND as PEND0.
eapply (SRr_srealizes tfibsegs W _ _ _ (ex_phase W E0 ss_exF xF_st1 _ _ _ HS0 xF_run1) HAI0).
intros W1 c1 _ HAI1 (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). cbn [cfg_model] in HAI1. clear HS0.
rewrite ?wvb_wvb in HAI1 |- *.
assert (VX1 : VX B ly S W sp0 mem md exm XS (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat1 md)).
{ pose proof (VX_run B LAWS ly S W sp0 mem md exm exm_img exm_dec HFownM XS Hstk Htop _ _ (ms_mem ms1) mat1 VX0) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF1. intros Hin. destruct (ex_windows_sound E0 ss_exF sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 Hw)].
- intros x Hx1 Hx2. apply HFr1. intros Hin. destruct (ex_windows_sound E0 ss_exF sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 Hw)].
- apply (vf_band_present W E0 xF_st1 ms1 sp0 HS1 ltac:(vm_compute; reflexivity) Usp0 ltac:(lia)). }
assert (PEND1 : forall i, (i < length pend)%nat -> aview tfibsegs (w_H W) (ms_mem ms1) (STDOUT_BUFA + Z.of_nat i) = Some (bv_unsigned (nth i pend 0%bv))).
{ intros i Hi. rewrite <- (PEND0 i Hi). apply aview_eq_of. apply HFr1. rewrite unsigned_lit_small by GEO. intros Hin.
destruct (ex_windows_sound E0 ss_exF sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin) as [Hw|Hw]; [unfold vf_band in Hw; GEO | unfold exm, vo_file, vf_file, F_STDOUT, F_STDERR, FILE_SZ in Hw; GEO]. }
clear VX0 HF1 HFr1 PEND0.
pose proof (st_ok_add_cond_neg tfibsegs E0 xF_st1 _ BC_EQ (SLit 0) (SExt true 32 (SOff 32 0)) HS1
ltac:(apply (beq0_sext32_false E0 32 tid A32_0); lia)) as HS1c.
change (YP06.add_cond xF_st1 (mkAC (neg_bc BC_EQ) (SLit 0) (SExt true 32 (SOff 32 0)))) with xF_st1c in HS1c. clear HS1.
eapply (SRr_srealizes tfibsegs W _ _ _ (ex_phase W E0 xF_st1c xF_st2 _ _ _ HS1c xF_run2) HAI1).
intros W2 c2 _ HAI2 (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). cbn [cfg_model] in HAI2. clear HS1c.
rewrite ?wvb_wvb in HAI2 |- *.
assert (VX2 : VX B ly S W sp0 mem md exm XS (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md)).
{ pose proof (VX_run B LAWS ly S W sp0 mem md exm exm_img exm_dec HFownM XS Hstk Htop _ _ (ms_mem ms2) mat2 VX1) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF2. intros Hin. destruct (ex_windows_sound E0 xF_st1c sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 Hw)].
- intros x Hx1 Hx2. apply HFr2. intros Hin. destruct (ex_windows_sound E0 xF_st1c sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 Hw)].
- apply (vf_band_present W E0 xF_st2 ms2 sp0 HS2 ltac:(vm_compute; reflexivity) Usp0 ltac:(lia)). }
assert (PEND2 : forall i, (i < length pend)%nat -> aview tfibsegs (w_H W) (ms_mem ms2) (STDOUT_BUFA + Z.of_nat i) = Some (bv_unsigned (nth i pend 0%bv))).
{ intros i Hi. rewrite <- (PEND1 i Hi). apply aview_eq_of. apply HFr2. rewrite unsigned_lit_small by GEO. intros Hin.
destruct (ex_windows_sound E0 xF_st1c sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin) as [Hw|Hw]; [unfold vf_band in Hw; GEO | unfold exm, vo_file, vf_file, F_STDOUT, F_STDERR, FILE_SZ in Hw; GEO]. }
clear VX1 HF2 HFr2 PEND1.
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_xcall B LAWS HB X1_PC XW1 XTRUE X1 W E0 xF_st2 ms2 _ ly S sp0 xF_r02 xF_rest2 36 X1_RA OSP_X1
HS2 eq_refl eq_refl Usp0 G3_0 G4_0 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_X1; lia) ltac:(unfold OSP_X1; lia) ltac:(unfold X1_RA; lia) ltac:(reflexivity)
(ex_rest_ok E0 xF_rest2 (as_tp B) ltac:(vm_compute; reflexivity) U4_0 ltac:(rewrite HTP; unfold TFIB_TPX; lia) ltac:(rewrite HTP; unfold TFIB_TPX; lia))
ltac:(intros r a Hr Ha; destruct (ex_rest_range E0 xF_rest2 (as_tp B) ltac:(vm_compute; reflexivity) U4_0 r a Hr Ha) as [[HcanR Hcr]|Hcr];
[ split; [left; exact HcanR | unfold XW1; unfold A_GOT_canary in Hcr; GEO]
| split; [right; apply HXown; exact Hcr | unfold XW1; unfold ex_cell_range, vo_file, vf_file in Hcr; GEO] ])
ltac:(intros a Hx; unfold XW1 in Hx; unfold vf_band; GEO)
(ex_rest_w E0 xF_rest2 ltac:(vm_compute; reflexivity))
(proj1 VX2) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VX2))) ltac:(exact I)) HAI2).
intros W2' c2' _ HAI2' (-> & ms2' & mat2' & -> & HS2' & HAR2' & HP2' & Hfr2' & Hpm2'). cbn [cfg_model] in HAI2'.
rewrite wvb_wvb in HAI2', HAR2' |- *.
change (vf_after_icpt 36 xF_st2 X1_RA OSP_X1 0 []) with xF_af2 in HS2'.
assert (VX2' : VX B ly S W sp0 mem md exm XS (ms_mem ms2') (with_vm_backing (m_vm_lazy md) mat2' md)).
{ eapply (VX_splice B ly S W sp0 mem md exm XS Hstk Htop (ms_mem ms2) _ (ms_mem ms2') _
(fun a => (sp0 + OSP_X1 - ESTACK <= a < sp0 + OSP_X1) \/ aowned B ly S a \/ XW1 a)).
- exact VX2.
- exact HAR2'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat2' mat2 md). apply with_vm_backing_same.
- intros a [Ha|[Ha|Ha]]; [left; unfold vf_band, OSP_X1 in *; lia | right; right; unfold XS; tauto | right; right; unfold XS; tauto].
- intros a Hr Hna. apply Hfr2'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; left; exact H' | intros H'; apply Hna; right; right; exact H'].
- intros a Hr Hba. apply Hpm2'; [exact Hr|]. destruct Hba as [Hb|Hns]; [intros Hx; unfold XW1 in Hx; unfold vf_band in Hb; GEO | intros Hx; apply Hns; right; right; exact Hx]. }
assert (PEND2' : forall i, (i < length pend)%nat -> aview tfibsegs (w_H W) (ms_mem ms2') (STDOUT_BUFA + Z.of_nat i) = Some (bv_unsigned (nth i pend 0%bv))).
{ intros i Hi. rewrite <- (PEND2 i Hi). apply Hfr2'; [GEO | unfold OSP_X1; GEO | apply HBown; GEO | unfold XW1; GEO]. }
remember (havoc E0 36 (map (getr (ms_regs ms2')) CLOB)) as E1 eqn:HE1.
assert (OLD1 : forall j, (j < 36)%nat -> ew E1 j = ew E0 j) by (intros j Hj; rewrite HE1; apply ew_havoc_old; exact Hj).
assert (Usp1 : bv_unsigned (ew E1 2) = sp0) by (rewrite OLD1 by (cbv; lia); exact Usp0).
assert (G3_1 : ew E1 3 = w64 (as_gp B)) by (rewrite OLD1 by (cbv; lia); exact G3_0).
assert (G4_1 : ew E1 4 = w64 (as_tp B)) by (rewrite OLD1 by (cbv; lia); exact G4_0).
assert (U4_1 : bv_unsigned (ew E1 4) = as_tp B) by (rewrite OLD1 by (cbv; lia); exact U4_0).
assert (A10_1 : ew E1 10 = Z_to_bv 64 code) by (rewrite OLD1 by (cbv; lia); exact A10_0).
assert (A34_1 : bv_unsigned (ew E1 34) = wp) by (rewrite OLD1 by (cbv; lia); exact A34_0).
clear HE1 HS2 VX2 PEND2.
eapply (SRr_srealizes tfibsegs W _ _ _ (ex_phase W E1 xF_af2 xF_st3 _ _ _ HS2' xF_run3) HAI2').
intros W3 c3 _ HAI3 (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). cbn [cfg_model] in HAI3. clear HS2'.
rewrite ?wvb_wvb in HAI3 |- *.
assert (VX3 : VX B ly S W sp0 mem md exm XS (ms_mem ms3) (with_vm_backing (m_vm_lazy md) mat3 md)).
{ pose proof (VX_run B LAWS ly S W sp0 mem md exm exm_img exm_dec HFownM XS Hstk Htop _ _ (ms_mem ms3) mat3 VX2') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF3. intros Hin. destruct (ex_windows_sound E1 xF_af2 sp0 _ ltac:(vm_compute; reflexivity) Usp1 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 Hw)].
- intros x Hx1 Hx2. apply HFr3. intros Hin. destruct (ex_windows_sound E1 xF_af2 sp0 _ ltac:(vm_compute; reflexivity) Usp1 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 Hw)].
- apply (vf_band_present W E1 xF_st3 ms3 sp0 HS3 ltac:(vm_compute; reflexivity) Usp1 ltac:(lia)). }
assert (PEND3 : forall i, (i < length pend)%nat -> aview tfibsegs (w_H W) (ms_mem ms3) (STDOUT_BUFA + Z.of_nat i) = Some (bv_unsigned (nth i pend 0%bv))).
{ intros i Hi. rewrite <- (PEND2' i Hi). apply aview_eq_of. apply HFr3. rewrite unsigned_lit_small by GEO. intros Hin.
destruct (ex_windows_sound E1 xF_af2 sp0 _ ltac:(vm_compute; reflexivity) Usp1 Hin) as [Hw|Hw]; [unfold vf_band in Hw; GEO | unfold exm, vo_file, vf_file, F_STDOUT, F_STDERR, FILE_SZ in Hw; GEO]. }
clear VX2' HF3 HFr3 PEND2'.
pose proof HS3 as HSc3. destruct HSc3 as (_ & _ & _ & _ & _ & _ & _ & Hmem3 & _). cbn [restrict ms_mem] in Hmem3.
assert (X3P : X3PRE W (ms_mem ms3)).
{ split; (eapply (val_mem_of_lit E1 (mrestrict (w_H W) (ms_mem ms3)) (ss_mem xF_st3) _ _ _ Hmem3); vm_compute; reflexivity). }
clear Hmem3.
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_xcall B LAWS HB X3_PC XW3 X3PRE X3 W E1 xF_st3 ms3 _ ly S sp0 xF_r03 xF_rest3 52 X23_RA OSP_X23
HS3 eq_refl eq_refl Usp1 G3_1 G4_1 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_X23; lia) ltac:(unfold OSP_X23; lia) ltac:(unfold X23_RA; lia) ltac:(reflexivity)
(ex_rest_ok E1 xF_rest3 (as_tp B) ltac:(vm_compute; reflexivity) U4_1 ltac:(rewrite HTP; unfold TFIB_TPX; lia) ltac:(rewrite HTP; unfold TFIB_TPX; lia))
ltac:(intros r a Hr Ha; destruct (ex_rest_range E1 xF_rest3 (as_tp B) ltac:(vm_compute; reflexivity) U4_1 r a Hr Ha) as [[HcanR Hcr]|Hcr];
[ split; [left; exact HcanR | unfold XW3; unfold A_GOT_canary in Hcr; GEO]
| split; [right; apply HXown; exact Hcr | unfold XW3; unfold ex_cell_range, vo_file, vf_file in Hcr; GEO] ])
ltac:(intros a Hx; unfold XW3 in Hx; unfold vf_band; GEO)
(ex_rest_w E1 xF_rest3 ltac:(vm_compute; reflexivity))
(proj1 VX3) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VX3))) ltac:(exact X3P)) HAI3).
intros W3' c3' _ HAI3' (-> & ms3' & mat3' & -> & HS3' & HAR3' & HP3' & Hfr3' & Hpm3'). cbn [cfg_model] in HAI3'.
rewrite wvb_wvb in HAI3', HAR3' |- *.
change (vf_after_icpt 52 xF_st3 X23_RA OSP_X23 0 []) with xF_af3 in HS3'.
assert (VX3' : VX B ly S W sp0 mem md exm XS (ms_mem ms3') (with_vm_backing (m_vm_lazy md) mat3' md)).
{ eapply (VX_splice B ly S W sp0 mem md exm XS Hstk Htop (ms_mem ms3) _ (ms_mem ms3') _
(fun a => (sp0 + OSP_X23 - ESTACK <= a < sp0 + OSP_X23) \/ aowned B ly S a \/ XW3 a)).
- exact VX3.
- exact HAR3'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat3' mat3 md). apply with_vm_backing_same.
- intros a [Ha|[Ha|Ha]]; [left; unfold vf_band, OSP_X23 in *; lia | right; right; unfold XS; tauto | right; right; unfold XS; tauto].
- intros a Hr Hna. apply Hfr3'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; left; exact H' | intros H'; apply Hna; right; right; exact H'].
- intros a Hr Hba. apply Hpm3'; [exact Hr|]. destruct Hba as [Hb|Hns]; [intros Hx; unfold XW3 in Hx; unfold vf_band in Hb; GEO | intros Hx; apply Hns; right; right; exact Hx]. }
assert (PEND3' : forall i, (i < length pend)%nat -> aview tfibsegs (w_H W) (ms_mem ms3') (STDOUT_BUFA + Z.of_nat i) = Some (bv_unsigned (nth i pend 0%bv))).
{ intros i Hi. rewrite <- (PEND3 i Hi). apply Hfr3'; [GEO | unfold OSP_X23; GEO | apply HBown; GEO | unfold XW3; GEO]. }
remember (havoc E1 52 (map (getr (ms_regs ms3')) CLOB)) as E2 eqn:HE2.
assert (OLD2 : forall j, (j < 52)%nat -> ew E2 j = ew E1 j) by (intros j Hj; rewrite HE2; apply ew_havoc_old; exact Hj).
assert (Usp2 : bv_unsigned (ew E2 2) = sp0) by (rewrite OLD2 by (cbv; lia); exact Usp1).
assert (G3_2 : ew E2 3 = w64 (as_gp B)) by (rewrite OLD2 by (cbv; lia); exact G3_1).
assert (G4_2 : ew E2 4 = w64 (as_tp B)) by (rewrite OLD2 by (cbv; lia); exact G4_1).
assert (U4_2 : bv_unsigned (ew E2 4) = as_tp B) by (rewrite OLD2 by (cbv; lia); exact U4_1).
assert (A10_2 : ew E2 10 = Z_to_bv 64 code) by (rewrite OLD2 by (cbv; lia); exact A10_1).
assert (A34_2 : bv_unsigned (ew E2 34) = wp) by (rewrite OLD2 by (cbv; lia); exact A34_1).
clear HE2 HS3 VX3 PEND3.
eapply (SRr_srealizes tfibsegs W _ _ _ (ex_phase W E2 xF_af3 xF_st4 _ _ _ HS3' xF_run4) HAI3').
intros W4 c4 _ HAI4 (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). cbn [cfg_model] in HAI4. clear HS3'.
rewrite ?wvb_wvb in HAI4 |- *.
assert (VX4 : VX B ly S W sp0 mem md exm XS (ms_mem ms4) (with_vm_backing (m_vm_lazy md) mat4 md)).
{ pose proof (VX_run B LAWS ly S W sp0 mem md exm exm_img exm_dec HFownM XS Hstk Htop _ _ (ms_mem ms4) mat4 VX3') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF4. intros Hin. destruct (ex_windows_sound E2 xF_af3 sp0 _ ltac:(vm_compute; reflexivity) Usp2 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 Hw)].
- intros x Hx1 Hx2. apply HFr4. intros Hin. destruct (ex_windows_sound E2 xF_af3 sp0 _ ltac:(vm_compute; reflexivity) Usp2 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 Hw)].
- apply (vf_band_present W E2 xF_st4 ms4 sp0 HS4 ltac:(vm_compute; reflexivity) Usp2 ltac:(lia)). }
assert (PEND4 : forall i, (i < length pend)%nat -> aview tfibsegs (w_H W) (ms_mem ms4) (STDOUT_BUFA + Z.of_nat i) = Some (bv_unsigned (nth i pend 0%bv))).
{ intros i Hi. rewrite <- (PEND3' i Hi). apply aview_eq_of. apply HFr4. rewrite unsigned_lit_small by GEO. intros Hin.
destruct (ex_windows_sound E2 xF_af3 sp0 _ ltac:(vm_compute; reflexivity) Usp2 Hin) as [Hw|Hw]; [unfold vf_band in Hw; GEO | unfold exm, vo_file, vf_file, F_STDOUT, F_STDERR, FILE_SZ in Hw; GEO]. }
clear VX3' HF4 HFr4 PEND3'.
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_xcall_noar B X2_PC XW2 XTRUE X2 W E2 xF_st4 ms4 _ ly S sp0 xF_r04 xF_rest4 68 X23_RA OSP_X23
HS4 eq_refl eq_refl Usp2 G3_2 G4_2 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_X23; lia) ltac:(unfold OSP_X23; lia) ltac:(unfold X23_RA; lia) ltac:(reflexivity)
(ex_rest_ok E2 xF_rest4 (as_tp B) ltac:(vm_compute; reflexivity) U4_2 ltac:(rewrite HTP; unfold TFIB_TPX; lia) ltac:(rewrite HTP; unfold TFIB_TPX; lia))
ltac:(intros r a Hr Ha; destruct (ex_rest_range E2 xF_rest4 (as_tp B) ltac:(vm_compute; reflexivity) U4_2 r a Hr Ha) as [[HcanR Hcr]|Hcr];
[ split; [left; exact HcanR | unfold XW2; unfold A_GOT_canary in Hcr; GEO]
| split; [right; apply HXown; exact Hcr | unfold XW2; unfold ex_cell_range, vo_file, vf_file in Hcr; GEO] ])
ltac:(intros a Hx; unfold XW2 in Hx; unfold vf_band; GEO)
(ex_rest_w E2 xF_rest4 ltac:(vm_compute; reflexivity))
(proj1 VX4) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VX4))) ltac:(exact I)) HAI4).
intros W4' c4' _ HAI4' (-> & ms4' & mat4' & -> & HS4' & HP4' & Hfr4' & Hpm4'). cbn [cfg_model] in HAI4'.
rewrite wvb_wvb in HAI4' |- *.
change (vf_after_icpt 68 xF_st4 X23_RA OSP_X23 0 []) with xF_af4 in HS4'.
assert (PEND4' : forall i, (i < length pend)%nat -> aview tfibsegs (w_H W) (ms_mem ms4') (STDOUT_BUFA + Z.of_nat i) = Some (bv_unsigned (nth i pend 0%bv))).
{ intros i Hi. rewrite <- (PEND4 i Hi). apply Hfr4'; [GEO | unfold OSP_X23; GEO | apply HBown; GEO | unfold XW2; GEO]. }
remember (havoc E2 68 (map (getr (ms_regs ms4')) CLOB)) as E3 eqn:HE3.
assert (OLD3 : forall j, (j < 68)%nat -> ew E3 j = ew E2 j) by (intros j Hj; rewrite HE3; apply ew_havoc_old; exact Hj).
assert (Usp3 : bv_unsigned (ew E3 2) = sp0) by (rewrite OLD3 by (cbv; lia); exact Usp2).
assert (G3_3 : ew E3 3 = w64 (as_gp B)) by (rewrite OLD3 by (cbv; lia); exact G3_2).
assert (G4_3 : ew E3 4 = w64 (as_tp B)) by (rewrite OLD3 by (cbv; lia); exact G4_2).
assert (U4_3 : bv_unsigned (ew E3 4) = as_tp B) by (rewrite OLD3 by (cbv; lia); exact U4_2).
assert (A10_3 : ew E3 10 = Z_to_bv 64 code) by (rewrite OLD3 by (cbv; lia); exact A10_2).
assert (A34_3 : bv_unsigned (ew E3 34) = wp) by (rewrite OLD3 by (cbv; lia); exact A34_2).
clear HE3 HS4 VX4 PEND4.
eapply (SRr_srealizes tfibsegs W _ _ _ (ex_phase W E3 xF_af4 xF_st5 _ _ _ HS4' xF_run5) HAI4').
intros W5 c5 _ HAI5 (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). cbn [cfg_model] in HAI5. clear HS4'.
rewrite ?wvb_wvb in HAI5 |- *.
assert (PEND5 : forall i, (i < length pend)%nat -> aview tfibsegs (w_H W) (ms_mem ms5) (STDOUT_BUFA + Z.of_nat i) = Some (bv_unsigned (nth i pend 0%bv))).
{ intros i Hi. rewrite <- (PEND4' i Hi). apply aview_eq_of. apply HFr5. rewrite unsigned_lit_small by GEO. intros Hin.
destruct (ex_windows_sound E3 xF_af4 sp0 _ ltac:(vm_compute; reflexivity) Usp3 Hin) as [Hw|Hw]; [unfold vf_band in Hw; GEO | unfold exm, vo_file, vf_file, F_STDOUT, F_STDERR, FILE_SZ in Hw; GEO]. }
clear HF5 HFr5 PEND4'.
pose proof HS5 as HSc5. destruct HSc5 as (_ & _ & _ & _ & _ & _ & Hregs5 & Hmem5 & HG5). cbn [restrict ms_mem] in Hmem5.
pose proof (lit_buf_sound tfibsegs E3 (mrestrict (w_H W) (ms_mem ms5)) (ss_mem xF_st5) (SLit (F_STDOUT + 120)) 4 [1; 0; 0; 0] Hmem5
ltac:(vm_compute; reflexivity)) as Hfdrd. cbn [sv_denot] in Hfdrd.
replace (map (WriteEv ch) pend) with (map (WriteEv ch) (pend ++ [])) by (rewrite app_nil_r; reflexivity).
eapply (srz_sym_stdio_writev2 W E3 xF_st5 ms5 _ (Z_to_bv 64 1) ch 0 2 (-144) F_STDOUT _ (SLit STDOUT_BUFA) (SOff 34 (- STDOUT_BUFA)) (SLit 0) (SLit 0)
pend [] (map (Z_to_bv 8) [1; 0; 0; 0]) 84 _ HAI5 HS5 eq_refl eq_refl eq_refl).
- reflexivity.
- eapply fdchan_sbm; [exact Hch | apply with_vm_backing_same].
- reflexivity.
- vm_compute. reflexivity.
- match goal with |- sv_denot _ ?x = _ => let x' := eval vm_compute in x in change x with x' end.
rewrite iovcnt_val, U_off, U_SLit by (rewrite A34_3; unfold M64; GEO). rewrite A34_3. rewrite (zcanon_id _) by (unfold M64; GEO).
rewrite (proj2 (Z.eqb_neq _ _)) by GEO. reflexivity.
- match goal with |- sv_denot _ ?x = _ => let x' := eval vm_compute in x in change x with x' end.
rewrite iovcnt_val', U_off, U_SLit by (rewrite A34_3; unfold M64; GEO). rewrite A34_3. rewrite (zcanon_id _) by (unfold M64; GEO).
rewrite (proj2 (Z.eqb_neq _ _)) by GEO. reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- match goal with |- U _ ?x = _ => let x' := eval vm_compute in x in change x with x' end.
rewrite !U_off, U_SLit by (rewrite ?A34_3; unfold M64; GEO). change (zcanon 0) with 0. lia.
- match goal with |- U _ ?x = _ => let x' := eval vm_compute in x in change x with x' end. rewrite U_SLit. reflexivity.
- reflexivity.
- reflexivity.
- cbn. lia. - cbn. lia. - cbn. lia. - cbn. lia.
- vm_compute. reflexivity.
-   rewrite word_to_nat_U, U_off by (rewrite A34_3; unfold M64; GEO). cbn [sv_denot]. rewrite A34_3.
replace (Z.to_nat (wp + - STDOUT_BUFA)) with (length pend) by lia. exact (rdn_of_aview (w_H W) (ms_mem ms5) STDOUT_BUFA pend PEND5).
- reflexivity.
- rewrite U_off, U_SLit by (rewrite A34_3; unfold M64; GEO). rewrite A34_3. change (zcanon 0) with 0. GEO.
- rewrite U_off, U_SLit by (rewrite A34_3; unfold M64; GEO). rewrite A34_3. rewrite (zcanon_id _) by (unfold M64; GEO). GEO.
- rewrite U_off, U_SLit, Usp3 by (rewrite A34_3; unfold M64; GEO). rewrite A34_3. rewrite (zcanon_id _) by (unfold M64; GEO). GEO.
- rewrite !U_SLit. change (zcanon 0) with 0. lia.
- rewrite !U_SLit, Usp3. change (zcanon 0) with 0. lia.
- exact Hfdrd.
- vm_compute. reflexivity.
- unfold F_STDOUT. lia.
- unfold F_STDOUT. lia.
- rewrite Usp3. unfold F_STDOUT. lia.
- rewrite Usp3. lia.
- rewrite Usp3. lia.
- vm_compute. reflexivity.
- intros ms5' ws5 mat5' HS5' HF5' HFr5' HAI5'. rewrite ?wvb_wvb in HAI5' |- *.
change (wl_after xF_st5 0 (-144) 84) with xF_af5 in HS5'.
remember (havoc E3 84 ws5) as E4 eqn:HE4.
assert (OLD4 : forall j, (j < 84)%nat -> ew E4 j = ew E3 j) by (intros j Hj; rewrite HE4; apply ew_havoc_old; exact Hj).
assert (Usp4 : bv_unsigned (ew E4 2) = sp0) by (rewrite OLD4 by (cbv; lia); exact Usp3).
assert (G3_4 : ew E4 3 = w64 (as_gp B)) by (rewrite OLD4 by (cbv; lia); exact G3_3).
assert (G4_4 : ew E4 4 = w64 (as_tp B)) by (rewrite OLD4 by (cbv; lia); exact G4_3).
assert (U4_4 : bv_unsigned (ew E4 4) = as_tp B) by (rewrite OLD4 by (cbv; lia); exact U4_3).
assert (A10_4 : ew E4 10 = Z_to_bv 64 code) by (rewrite OLD4 by (cbv; lia); exact A10_3).
assert (A34_4 : bv_unsigned (ew E4 34) = wp) by (rewrite OLD4 by (cbv; lia); exact A34_3).
clear HE4 HS5 Hfdrd Hregs5 Hmem5 HG5 HF5' HFr5' PEND5.
eapply (SRr_srealizes tfibsegs W _ _ _ (ex_phase W E4 xF_af5 xF_st6 _ _ _ HS5' xF_run6) HAI5').
intros W6 c6 _ HAI6 (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). cbn [cfg_model] in HAI6. clear HS5'.
rewrite ?wvb_wvb in HAI6 |- *.
rewrite <- (m_fs_wvb (m_vm_lazy md) mat6 md).
apply (srz_sym_exit W E4 xF_st6 ms6 _ (Z_to_bv 64 code) HAI6 HS6 eq_refl eq_refl); [| rewrite unsigned_lit_small by lia; lia].
match goal with |- sv_denot _ ?x = _ => let x' := eval vm_compute in x in change x with x' end.
cbn [sv_denot]. rewrite Z.add_0_r, A10_4, unsigned_lit_small by lia. reflexivity.
Qed.
End S.
End d.
