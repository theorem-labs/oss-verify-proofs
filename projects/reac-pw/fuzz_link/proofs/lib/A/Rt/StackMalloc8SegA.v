(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_scene (asan). Seg A of the __asan_stack_malloc_8
   walk: `sm8_segA` of lib/A/Rt/StackMalloc8Cuts.v, from PC_STACK_MALLOC_8 to the head of the flag-search loop
   PC_SM8_LOOP. It is the opening of cgif_rgb_fuzzer's released class-7 proof (lib/YF9c.v:32, tra_stack_malloc7_at,
   up to its first `fs_phase_to ... FS_LOOP`), with the class-8 constants and the scene image:
   - one symbolic run (cgif's SRr engine, SRr_run_to_gen over a code table that is tbl_icpt plus the malloc_8 body
     and the TLS chain of StackMalloc8Tbl.v) from the entry to PC_SM8_LOOP. The run decides every branch on its
     own: [TP] = F is a pointer above 4096, so the null-fake-stack test (entry +0x30) falls through; AR's
     z1 (AF 96) 0 sends the GC test (entry +0x3c) past the GC call; AR's z8 (AF 88) kStackSizeLog makes
     1 << (20 - 14) = 64 > 0, so the `blez` at entry +0x5c (the zero-return path (F) of CLASS8-DESIGN.md
     section 3) falls through. Paths (A)-(D) start at entry +0xc0, reached only from the null-fake-stack branch;
     path (E) starts after the loop (Seg B). No branch is left open, and the run ends RS_running at PC_SM8_LOOP.
   - the cut sm8_midAB is read off the run's final symbolic state: each register's symbolic value, the five saved
     words of the stack region, the stack window as the only write window (frame_of).
   The facts AR does not give generically are facts about B's certificate (its start-up constant list as_const B and
   the fields as_tp / as_tsd): named Section hypotheses HC_tp, HC_tsd and one HC_ per cell, each the exact cell of
   the staged start-up table (A/AF0m.v Tfib_const) that the walk reads. The start-up tables
   themselves are NOT imported (no A/AB01, A/AB03, A/AD2j, A/AD1k, A/AF0m, nor their Y twins, in this file or its
   imports). The generic image lemmas of A/AF0x.v, A/AF0r.v and A/AE2y.v that the walk needs are restated here,
   since those files import A/AF0m. No Axiom, no Admitted, no admit. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0s YG0t YCe5.
From OSSVerify.reac_pw.fuzz_link.images Require Import Asan.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AE34.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import StackMalloc8Tbl StackMalloc8Cuts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* ---- Image lemmas over tfibsegs (restated from A/AF0x.v:23-157, :250-336, :500-513 with SM8_IMG_LO / SM8_IMG_END
   for TFIB_IMG_LO / TFIB_IMG_END; A/AF0x.v imports A/AF0m.v, so it is not Required here). ---- *)
Lemma sm8_Hwx : wx_segs_nowrap tfibsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma sm8_seg_rom_none_high : forall a, SM8_IMG_END <= a < 2 ^ 64 -> seg_rom tfibsegs (Z_to_bv 64 a) = None.
Proof.
intros a Ha. unfold SM8_IMG_END in Ha. unfold seg_rom, memory_read, tfibsegs, Asan.M.loaded_segments.
cbn -[Z_to_bv bv_unsigned Z.leb Z.ltb Z.add].
rewrite !unsigned_lit_small by lia.
repeat match goal with
| |- context [ (?x <=? a) && (a + 1 <=? ?y) ] =>
replace ((x <=? a) && (a + 1 <=? y)) with false
by (symmetry; apply Bool.andb_false_iff; destruct (Z.leb_spec x a); [right; apply Z.leb_gt; lia | left; reflexivity])
end. reflexivity.
Qed.
Lemma sm8_find_segment_none_high : forall x, SM8_IMG_END <= x -> find_segment tfibsegs x 1 = None.
Proof.
intros x Hx. apply (find_segment1_none_above tfibsegs SM8_IMG_END x); [vm_compute; reflexivity | exact Hx].
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition sm8_img_cover (ly : alayout) : Prop := fst (ly_img ly) <= SM8_IMG_LO /\ SM8_IMG_END <= fst (ly_img ly) + snd (ly_img ly).
Lemma sm8_img_cover_of_ledger : forall ly S md, ALedger tfibsegs ly S md -> sm8_img_cover ly.
Proof.
intros ly S md L. split.
- destruct (al_img _ _ _ _ L Asan.Asan_segment_000 ltac:(left; reflexivity)) as [H _].
cbn in H. unfold SM8_IMG_LO. lia.
- destruct (al_img _ _ _ _ L Asan.Asan_segment_003 ltac:(do 3 right; left; reflexivity)) as [_ H].
cbn in H. unfold SM8_IMG_END. lia.
Qed.
Definition sm8_zone3cases (x sz : Z) : Prop :=
x + sz <= SM8_IMG_LO \/ (SM8_IMG_END <= x /\ x + sz <= kLowShadowBeg) \/ (kHighMemBeg <= x /\ x + sz <= ASAN_CEIL).
Definition sm8_zone3 (x sz : Z) : Prop := 4096 <= x /\ x + sz <= ASAN_CEIL /\ sm8_zone3cases x sz.
Lemma sm8_zone3_intro : forall ly x sz, sm8_img_cover ly -> 0 <= sz ->
in_app x sz -> zdisjoint (x, sz) (ly_img ly) -> sm8_zone3 x sz.
Proof.
intros ly x sz [C1 C2] Hsz [A1 A2] D. unfold zdisjoint in D. cbn [fst snd] in D.
pose proof ASAN_CEIL_range as [CR _].
unfold sm8_zone3, sm8_zone3cases, SM8_IMG_LO, SM8_IMG_END, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
Lemma sm8_aview_some : forall H mem a v,
aview tfibsegs H mem a = Some v <-> exists b, mbyte tfibsegs (mrestrict H mem) a = Some b /\ bv_unsigned b = v.
Proof.
intros H mem a v. unfold aview. destruct (mbyte tfibsegs (mrestrict H mem) a) as [b|]; cbn.
- split; [intros E; injection E as <-; exists b; auto | intros (b' & E & <-); congruence].
- split; [discriminate | intros (b & E & _); discriminate].
Qed.
Lemma sm8_aview_byte : forall H mem a v,
aview tfibsegs H mem a = Some v -> mbyte tfibsegs (mrestrict H mem) a = Some (Z_to_bv 8 v).
Proof.
intros H mem a v Hv. apply sm8_aview_some in Hv as (b & E & <-). rewrite Z_to_bv_bv_unsigned. exact E.
Qed.
Lemma sm8_cell_holds_val_mem : forall B ly H mem e (w : nat) e',
cell_holds B ly (aview tfibsegs H mem) (ACell e w (AV e')) ->
val_mem tfibsegs (mrestrict H mem) (aeval B ly e) w (aeval B ly e').
Proof.
intros B ly H mem e w e' Hc k Hk. cbn [cell_holds c_at c_val c_w] in Hc.
exact (sm8_aview_byte H mem _ _ (Hc k Hk)).
Qed.
Lemma sm8_writable_high_apresent : forall (H : word -> bool) mem a,
SM8_IMG_END <= a < 2 ^ 64 -> writable_at tfibsegs (mrestrict H mem) a -> apresent H mem a.
Proof.
intros H mem a Ha Hw. unfold writable_at, wview, mrestrict in Hw. unfold apresent. unfold SM8_IMG_END in Ha.
rewrite (unsigned_lit_small a) in Hw by lia.
rewrite (sm8_find_segment_none_high a ltac:(unfold SM8_IMG_END; lia)) in Hw.
destruct (H (Z_to_bv 64 a)) eqn:Hh; [exfalso; apply Hw; reflexivity|].
split; [reflexivity|]. destruct (mem (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | exfalso; apply Hw; reflexivity].
Qed.
Lemma sm8_st_ok_window_apresent : forall (H : word -> bool) E ss ms i r a,
st_ok tfibsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
SM8_IMG_END <= a < 2 ^ 64 -> apresent H (ms_mem ms) a.
Proof.
intros H E ss ms i r a HS Hi Ha Hhi. apply sm8_writable_high_apresent; [exact Hhi|].
pose proof (st_ok_mem_ok tfibsegs E ss _ HS) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)) as (_ & _ & Hw & _).
replace a with (base_val E (YP09.r_base r) + (a - base_val E (YP09.r_base r))) by lia. apply Hw. lia.
Qed.
Lemma sm8_st_ok_chunk_val : forall (H : word -> bool) E ss ms i r j off (n : N) e v,
st_ok tfibsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
nth_error (YP09.r_chunks r) j = Some (YP09.mkChunk off (CVal n e)) ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
val_mem tfibsegs (mrestrict H (ms_mem ms)) (base_val E (YP09.r_base r) + off) (N.to_nat n) v.
Proof.
intros H E ss ms i r j off n e v HS Hi Hj He Hv Hn.
pose proof (st_ok_mem_ok tfibsegs E ss _ HS) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)) as (_ & _ & _ & Hcs).
apply (val_of_chunk_ok tfibsegs E _ _ off n e v); [|exact He | exact Hv | exact Hn].
exact (proj1 (Forall_forall _ _) Hcs _ (nth_error_In _ _ Hj)).
Qed.
Lemma sm8_apresent_same : forall (H : word -> bool) (mem mem' : word -> option byte) a,
mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a) -> apresent H mem a -> apresent H mem' a.
Proof. intros H mem mem' a E [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite E. exact Hb. Qed.
Lemma sm8_unsigned_lit_small8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. exact Hz. Qed.
Lemma sm8_le_bytes8_sum : forall z, 0 <= z < 2 ^ 64 ->
let b := fun k => YG0f.le_byte z 8 k in
b 0%nat + 256 * (b 1%nat + 256 * (b 2%nat + 256 * (b 3%nat + 256 * (b 4%nat + 256 * (b 5%nat + 256 * (b 6%nat + 256 * b 7%nat)))))) = z.
Proof.
intros z Hz. cbn beta. unfold YG0f.le_byte. rewrite !Z.shiftr_div_pow2 by lia.
rewrite (Z.mod_small z) by (change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); lia).
change (2 ^ (8 * Z.of_nat 0)) with 1. change (2 ^ (8 * Z.of_nat 1)) with 256. change (2 ^ (8 * Z.of_nat 2)) with (256 * 256).
change (2 ^ (8 * Z.of_nat 3)) with (256 * 256 * 256). change (2 ^ (8 * Z.of_nat 4)) with (256 * 256 * 256 * 256).
change (2 ^ (8 * Z.of_nat 5)) with (256 * 256 * 256 * 256 * 256). change (2 ^ (8 * Z.of_nat 6)) with (256 * 256 * 256 * 256 * 256 * 256).
change (2 ^ (8 * Z.of_nat 7)) with (256 * 256 * 256 * 256 * 256 * 256 * 256).
rewrite Z.div_1_r. rewrite <- !Z.div_div by lia.
assert (H7 : z / 256 / 256 / 256 / 256 / 256 / 256 / 256 < 256).
{ change (2 ^ 64) with (256 * 256 * 256 * 256 * 256 * 256 * 256 * 256) in Hz.
repeat (apply Z.div_lt_upper_bound; [lia|]). lia. }
rewrite (Z.mod_small (z / 256 / 256 / 256 / 256 / 256 / 256 / 256)) by (split; [repeat (apply Z.div_pos; [|lia]); lia | exact H7]).
pose proof (Z.div_mod z 256 ltac:(lia)) as E0.
pose proof (Z.div_mod (z / 256) 256 ltac:(lia)) as E1.
pose proof (Z.div_mod (z / 256 / 256) 256 ltac:(lia)) as E2.
pose proof (Z.div_mod (z / 256 / 256 / 256) 256 ltac:(lia)) as E3.
pose proof (Z.div_mod (z / 256 / 256 / 256 / 256) 256 ltac:(lia)) as E4.
pose proof (Z.div_mod (z / 256 / 256 / 256 / 256 / 256) 256 ltac:(lia)) as E5.
pose proof (Z.div_mod (z / 256 / 256 / 256 / 256 / 256 / 256) 256 ltac:(lia)) as E6.
lia.
Qed.
Lemma sm8_val_mem_rdword : forall (H : word -> bool) mem a v,
0 <= v < 2 ^ 64 -> val_mem tfibsegs (mrestrict H mem) a 8 v -> rdword (aview tfibsegs H mem) a = Some v.
Proof.
intros H mem a v Hv Hm. unfold rdword, aview.
assert (Bq : forall k, (k < 8)%nat -> mbyte tfibsegs (mrestrict H mem) (a + Z.of_nat k) = Some (Z_to_bv 8 (YG0f.le_byte v 8 k))).
{ intros k Hk. exact (Hm k Hk). }
assert (R : forall k, 0 <= YG0f.le_byte v 8 k < 256) by (intros k; unfold YG0f.le_byte; apply Z.mod_pos_bound; lia).
replace a with (a + Z.of_nat 0) at 1 by lia.
replace (a + 1) with (a + Z.of_nat 1) by lia. replace (a + 2) with (a + Z.of_nat 2) by lia. replace (a + 3) with (a + Z.of_nat 3) by lia.
replace (a + 4) with (a + Z.of_nat 4) by lia. replace (a + 5) with (a + Z.of_nat 5) by lia. replace (a + 6) with (a + Z.of_nat 6) by lia.
replace (a + 7) with (a + Z.of_nat 7) by lia.
rewrite !Bq by lia. cbn [option_map]. rewrite !sm8_unsigned_lit_small8 by apply R.
f_equal. apply sm8_le_bytes8_sum. exact Hv.
Qed.
Lemma sm8_combine_seq_nth : forall {X} (l : list X) (d : X) s k, (k < length l)%nat -> In ((s + k)%nat, nth k l d) (combine (seq s (length l)) l).
Proof.
induction l as [|x l IH]; intros d s k Hk; cbn in Hk; [lia|]. cbn [length seq combine].
destruct k as [|k]; [left; rewrite Nat.add_0_r; reflexivity | right]. replace (s + S k)%nat with (S s + k)%nat by lia. apply IH. lia.
Qed.
Lemma sm8_In_fs_cells_acells : forall (B : asyms) ly S c, In c (fs_cells S) -> In c (acells B ly S).
Proof. intros B ly S c H. unfold acells. rewrite !in_app_iff. right; right; right; right; right; left. exact H. Qed.
Lemma sm8_val_mem_mod64 : forall (m : word -> option byte) a x, val_mem tfibsegs m a 8 x -> val_mem tfibsegs m a 8 (x mod 2 ^ 64).
Proof.
intros m a x Hv k Hk. rewrite (Hv k Hk). f_equal. f_equal. unfold YG0f.le_byte, YO0f.le_byte.
change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma sm8_w64_mod : forall z k, Z_to_bv 64 (z mod 2 ^ 64 + k) = Z_to_bv 64 (z + k).
Proof.
intros z k. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

(* ---- The Seg A symbolic setup: cgif_rgb_fuzzer lib/YF9a.v:43-103 for class 8, over the scene image. ---- *)
(* The code the run may fetch: tbl_icpt (A/AE34.v; it holds __wrap___tls_get_addr and TryAsanInitFromRtl), the
   95 instructions of __asan_stack_malloc_8, and the rest of the TLS chain (StackMalloc8Tbl.v). *)
Definition sm8A_ranges : list (Z * nat) :=
[(PC_STACK_MALLOC_8, 95%nat); (SM8_ICPT_TGA, 31%nat); (SM8_TGA, 9%nat); (SM8_GET_THREAD, 8%nat);
(SM8_TSD_GET, 6%nat); (SM8_GETSPECIFIC, 7%nat); (SM8_DTLS_ON_TGA, 140%nat)].
Definition tbl_sm8A : ctable := Eval vm_compute in build_ranges sm8A_ranges tbl_icpt.
Lemma tbl_sm8A_eq : tbl_sm8A = build_ranges sm8A_ranges tbl_icpt. Proof. vm_cast_no_check (eq_refl tbl_sm8A). Qed.
Lemma tbl_sm8A_ok : table_ok tfibsegs tbl_sm8A.
Proof.
rewrite tbl_sm8A_eq. apply build_ranges_ok; [|exact tbl_icpt_ok].
unfold sm8A_ranges. repeat apply Forall_cons; try apply Forall_nil; cbv; intro Hq; discriminate Hq.
Qed.
(* Read-only regions holding literal words (A/AE2y.v:47-49). *)
Definition ro_chunk (base : Z) (c : Z * N * Z) : YP09.chunk := YP09.mkChunk (base + fst (fst c)) (CVal (snd (fst c)) (SLit (snd c))).
Definition ro_region (r : Z * Z * list (Z * N * Z)) : YP09.region :=
YP09.mkRegion None (fst (fst r)) (fst (fst r) + snd (fst r)) (fst (fst r)) (fst (fst r)) (map (ro_chunk (fst (fst r))) (snd r)).
(* The cells a read-only table states, as start-up cells. *)
Definition ro_cells (l : list (Z * Z * list (Z * N * Z))) : list acell :=
flat_map (fun r => map (fun c => ACell (ANum (fst (fst r) + fst (fst c))) (N.to_nat (snd (fst c))) (AV (ANum (snd c)))) (snd r)) l.
Definition ro_wf (l : list (Z * Z * list (Z * N * Z))) : bool :=
forallb (fun r => (0 <=? fst (fst r)) && (fst (fst r) + snd (fst r) <=? 2 ^ 64) &&
forallb (fun c => (0 <=? snd c) && (snd c <? 2 ^ (8 * Z.of_N (snd (fst c)))) && (Z.of_N (snd (fst c)) <=? 8)) (snd r)) l.
(* The absolute cells the TLS chain reads, each with the instruction that reads it (StackMalloc8Tbl.v). *)
Definition sm8A_rodata : list (Z * Z * list (Z * N * Z)) :=
[(SM8_TLS_GOT, 16, [(0, 8%N, 1); (8, 8%N, SM8_TLS_GOT_OFF)]);       (* __tls_get_addr 0x9b7fc / 0x9b804 *)
(SM8_REAL_TGA, 8, [(0, 8%N, SM8_TGA)]);                             (* interceptor 0x47fc8 *)
(SM8_DTV + 8, 8, [(0, 8%N, SM8_TP + 2048)]);                         (* __tls_get_addr 0x9b810: dtv[1] *)
(SM8_ASAN_INITED, 1, [(0, 1%N, 1)]);                                 (* TryAsanInitFromRtl 0x5b228 *)
(SM8_TSD_KEY_INITED, 8, [(0, 1%N, 1); (4, 4%N, 0)]);                 (* AsanTSDGet 0x56318 / 0x56320 *)
(SM8_GOT_CFLAGS, 8, [(0, 8%N, SM8_CFLAGS)]);                         (* DTLS_on_tls_get_addr 0x6b27c *)
(SM8_CFLAG_TGA, 1, [(0, 1%N, 1)]);                                   (* DTLS_on_tls_get_addr 0x6b280 *)
(SM8_GOT_VERB, 8, [(0, 8%N, SM8_VERB)]);                             (* DTLS_on_tls_get_addr 0x6b290 *)
(SM8_VERB, 4, [(0, 4%N, 0)]);                                        (* DTLS_on_tls_get_addr 0x6b29c *)
(SM8_GOT_DTLS, 8, [(0, 8%N, SM8_DTLS_TPOFF)])].                      (* DTLS_on_tls_get_addr 0x6b2a0 *)
Definition aT : nat := 32. Definition aC : nat := 33. Definition aD : nat := 34. Definition aF : nat := 35. Definition aH : nat := 36.
Definition HOFF8 : Z := 8 * CID8.
Definition stkA : YP09.region := YP09.mkRegion (Some 2%nat) (- SM8_WIN) 0 (- SM8_WIN) 0 [].
Definition rTSD : YP09.region := YP09.mkRegion None SM8_TSD (SM8_TSD + 8) SM8_TSD SM8_TSD [YP09.mkChunk SM8_TSD (CVal 8 (SOff aC 0))].
Definition rTP0 : YP09.region := YP09.mkRegion None SM8_TP (SM8_TP + 8) SM8_TP SM8_TP [YP09.mkChunk SM8_TP (CVal 8 (SOff aF 0))].
Definition rTP8 : YP09.region := YP09.mkRegion None (SM8_TP + 8) (SM8_TP + 16) (SM8_TP + 8) (SM8_TP + 8) [YP09.mkChunk (SM8_TP + 8) (CVal 8 (SOff aD 0))].
Definition rT : YP09.region := YP09.mkRegion (Some aT) 48 64 48 48 [YP09.mkChunk 48 (CVal 8 (SLit SM8_T_TLS_BEG)); YP09.mkChunk 56 (CVal 8 (SLit SM8_T_TLS_END))].
Definition rC : YP09.region := YP09.mkRegion (Some aC) 152 160 152 152 [YP09.mkChunk 152 (CVal 8 (SOff aT 0))].
Definition rD : YP09.region := YP09.mkRegion (Some aD) 24 32 24 24 [YP09.mkChunk 24 (CVal 8 (SLit SM8_TP))].
(* The fake-stack header cells of AR's fs_cells (YG0n.v:100): the class-8 hint, kStackSizeLog and the GC byte. No
   write window: Seg A writes none of them. *)
Definition rF : YP09.region := YP09.mkRegion (Some aF) HOFF8 97 HOFF8 HOFF8
[YP09.mkChunk HOFF8 (CVal 8 (SOff aH 0)); YP09.mkChunk 88 (CVal 8 (SLit kStackSizeLog)); YP09.mkChunk 96 (CVal 1 (SLit 0))].
Definition rTPm88 : YP09.region := ro_region (SM8_TP - 88, 8, [(0, 8%N, SM8_TSD)]).
Definition rTPm8 : YP09.region := ro_region (SM8_TP - 8, 8, [(0, 8%N, SM8_DTV)]).
Definition memA : smem := stkA :: rTSD :: rTP0 :: rTP8 :: rT :: rC :: rD :: rF :: rTPm88 :: rTPm8 :: map ro_region sm8A_rodata.
Definition factsA : list (nat * afact) :=
[(2%nat, mkAF (kHighMemBeg + SM8_WIN) kHighMemEnd 4);
(aT, mkAF 4096 (CEIL_MAX - 4096) 12);
(aC, mkAF 4096 (CEIL_MAX - 256) 3);
(aD, mkAF 4096 (CEIL_MAX - 4096) 12);
(aF, mkAF 4096 (CEIL_MAX - kFakeStackSize) 12);
(aH, mkAF 0 (2^64 - 1) 0)].
Definition regsA : list sv := Eval vm_compute in (firstn 4 sr_atoms ++ [SLit SM8_TP] ++ skipn 5 sr_atoms).
Definition ssA : sstate := mkSS PC_STACK_MALLOC_8 regsA memA None (mkFacts factsA [] []).
Definition RUNTO (stop : Z) (s : sstate) := sym_run_toN tfibsegs tbl_sm8A FUEL stop s.
Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (RG ss r) v.
Definition eA : sstate := Eval vm_compute in fst (RUNTO PC_SM8_LOOP ssA).
Lemma r_A : RUNTO PC_SM8_LOOP ssA = (eA, RS_running). Proof. vm_compute. reflexivity. Qed.
(* The registers at PC_SM8_LOOP, as the run leaves them (they are sm8_midAB's values, MEASURED by the run). *)
Lemma eA_facts : ss_pc eA = PC_SM8_LOOP /\ ss_resv eA = None /\
reg_is eA 2 (SOff 2 (- SM8_FRAME)) = true /\ reg_is eA 8 (SOff 2 0) = true /\ reg_is eA 9 (SOff 10 0) = true /\
reg_is eA 18 (SOff aF 0) = true /\ reg_is eA 19 (SLit kStackSizeLog) = true /\ reg_is eA 10 (SLit (fs_frames CID8)) = true /\
reg_is eA 11 (SOff aF kFakeFlagsOff) = true /\ reg_is eA 12 (SOff aH 0) = true /\
reg_is eA 13 (SOff aH (fs_frames CID8 - 1)) = true /\ reg_is eA 14 (SOff aF (fs_flag_off CID8 0)) = true /\
reg_is eA 15 (SLit (fs_frames CID8 - 1)) = true /\ reg_is eA 16 (SOff aH (fs_frames CID8)) = true /\
reg_is eA 4 (SLit SM8_TP) = true /\
forallb (fun r => reg_is eA r (SOff (Z.to_nat r) 0)) [3; 20; 21; 22; 23; 24; 25; 26; 27] = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
(* The stack region at PC_SM8_LOOP and its five saved words: ra, s0, s1, s2, s3 of the entry. *)
Definition rSTKA : YP09.region := Eval vm_compute in nth 0 (ss_mem eA) stkA.
Lemma eA_stk : nth_error (ss_mem eA) 0 = Some rSTKA /\ YP09.r_base rSTKA = Some 2%nat /\
YP09.r_wlo rSTKA = - SM8_WIN /\ YP09.r_whi rSTKA = 0 /\
nth_error (YP09.r_chunks rSTKA) 23 = Some (YP09.mkChunk (-8) (CVal 8 (SOff 1 0))) /\
nth_error (YP09.r_chunks rSTKA) 22 = Some (YP09.mkChunk (-16) (CVal 8 (SOff 8 0))) /\
nth_error (YP09.r_chunks rSTKA) 21 = Some (YP09.mkChunk (-24) (CVal 8 (SOff 9 0))) /\
nth_error (YP09.r_chunks rSTKA) 20 = Some (YP09.mkChunk (-32) (CVal 8 (SOff 18 0))) /\
nth_error (YP09.r_chunks rSTKA) 19 = Some (YP09.mkChunk (-40) (CVal 8 (SOff 19 0))).
Proof. vm_compute. repeat split; reflexivity. Qed.
(* The run's only write window is the stack window. *)
Lemma memA_windows : forall E a, in_wrange E memA a -> bv_unsigned (ew E 2) - SM8_WIN <= a < bv_unsigned (ew E 2).
Proof.
intros E a Hin. destruct (in_wrange_windows E _ _ Hin) as (b & lo & hi & Ht & Hw).
vm_compute in Ht. repeat (destruct Ht as [Hq | Ht]; [injection Hq as <- <- <-; cbn [base_val] in Hw; unfold SM8_WIN; lia |]). destruct Ht.
Qed.
Lemma ro_region_ok : forall E m base n v, 0 <= base -> base + Z.of_N n <= 2 ^ 64 ->
0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 -> val_mem tfibsegs m base (N.to_nat n) v ->
region_ok tfibsegs E m (ro_region (base, Z.of_N n, [(0, n, v)])).
Proof.
intros E m base n v H0 Hhi Hv Hn Hm. unfold ro_region, region_ok.
cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val map].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil]. unfold ro_chunk. cbn [fst snd].
apply (chunk_ok_val tfibsegs E _ 0 (base + 0) n (SLit v) v); [reflexivity | exact Hv | exact Hn |].
rewrite Z.add_0_l, Z.add_0_r. exact Hm.
Qed.
Lemma sbm_wvb : forall md mat, same_but_materialized md (with_vm_backing (m_vm_lazy md) mat md).
Proof. intros md mat. apply with_vm_backing_same. Qed.

Section f.
Variable B : asyms.
(* ---- B's certificate: the start-up facts Seg A reads, one named hypothesis per field or cell, each in the form of
   the staged start-up table (A/AF0m.v: PcapSyms, Tfib_const_sym :23-27, Tfib_const_abs), which this file does not
   import. AR's am_const (YG0n.v:211) turns a cell of as_const B into the byte facts the walk uses. ---- *)
(* PcapSyms.ts_tp: the main thread's tp; every tp-relative cell below is at a literal address through it. *)
Hypothesis HC_tp : as_tp B = SM8_TP.
(* PcapSyms.ts_tsd: __pthread_tsd_main. *)
Hypothesis HC_tsd : as_tsd B = SM8_TSD.
(* [TP] = F, the thread's fake stack (the TLS slot __tls_get_addr returns): malloc_8 entry +0x2c `ld s2,0(a0)`. *)
Hypothesis HC_fake_stack : forall ly, In (c8 (ATp 0) (AF 0)) (as_const B ly).
(* [TP - 88] = TSD: pthread_getspecific 0x9c8b0 `ld a1,-0x58(a1)`. *)
Hypothesis HC_tsd_slot : forall ly, In (c8 (ATp (-88)) (ATsd 0)) (as_const B ly).
(* [TP - 8] = the dtv: __tls_get_addr 0x9b800 `ld a1,-8(a1)`. *)
Hypothesis HC_dtv : forall ly, In (z8 (ATp (-8)) SM8_DTV) (as_const B ly).
(* [TP + SM8_DTLS_TPOFF] = D, DTLS's dtv block: DTLS_on_tls_get_addr 0x6b2b0 `ld s6,0(s5)`. *)
Hypothesis HC_dtls : forall ly, In (c8 (ATp 8) (AD 0)) (as_const B ly).
(* [D + 16 + 8] = TP, dtv entry 1 already recorded: DTLS_on_tls_get_addr 0x6b410 `ld a0,8(s0)`. *)
Hypothesis HC_dtls_dtv1 : forall ly, In (c8 (AD 24) (ATp 0)) (as_const B ly).
(* [TSD + 8 * tsd_key] = C, the thread context: pthread_getspecific 0x9c8c0 `ld a0,0(a0)`. *)
Hypothesis HC_tsd_main : forall ly, In (c8 (ATsd 0) (AC 0)) (as_const B ly).
(* [C + 0x98] = T, the AsanThread: GetCurrentThread 0x5da24 `ld a0,0x98(a0)`. *)
Hypothesis HC_ctx_thread : forall ly, In (c8 (AC 152) (AT 0)) (as_const B ly).
(* [T + 0x30], [T + 0x38]: the interceptor's loads at 0x47fe8 / 0x47fec. *)
Hypothesis HC_thread_tls_beg : forall ly, In (z8 (AT 48) SM8_T_TLS_BEG) (as_const B ly).
Hypothesis HC_thread_tls_end : forall ly, In (z8 (AT 56) SM8_T_TLS_END) (as_const B ly).
(* The TLS-GD .got pair (module 1, offset -0x800): __tls_get_addr 0x9b7fc / 0x9b804, DTLS_on_tls_get_addr 0x6b294. *)
Hypothesis HC_tls_got_mod : forall ly, In (z8 (ANum SM8_TLS_GOT) 1) (as_const B ly).
Hypothesis HC_tls_got_off : forall ly, In (z8 (ANum (SM8_TLS_GOT + 8)) SM8_TLS_GOT_OFF) (as_const B ly).
(* real___tls_get_addr = musl __tls_get_addr: the interceptor's load at 0x47fc8. *)
Hypothesis HC_real_tga : forall ly, In (z8 (ANum SM8_REAL_TGA) SM8_TGA) (as_const B ly).
(* dtv[1] = TP + 0x800: __tls_get_addr 0x9b810 `ld a1,0(a1)`. *)
Hypothesis HC_dtv1 : forall ly, In (z8 (ANum (SM8_DTV + 8)) (SM8_TP + 2048)) (as_const B ly).
(* asan_inited = 1: TryAsanInitFromRtl 0x5b228 `lb a1,0(s0)`. *)
Hypothesis HC_asan_inited : forall ly, In (z1 (ANum SM8_ASAN_INITED) 1) (as_const B ly).
(* tsd_key_inited = 1 and tsd_key = 0: AsanTSDGet 0x56318 `lbu` / 0x56320 `lw`. *)
Hypothesis HC_tsd_key_inited : forall ly, In (z1 (ANum SM8_TSD_KEY_INITED) 1) (as_const B ly).
Hypothesis HC_tsd_key : forall ly, In (z4 (ANum (SM8_TSD_KEY_INITED + 4)) 0) (as_const B ly).
(* The .got slot of common_flags and its intercept_tls_get_addr byte = 1: DTLS_on_tls_get_addr 0x6b27c / 0x6b280. *)
Hypothesis HC_got_cflags : forall ly, In (z8 (ANum SM8_GOT_CFLAGS) SM8_CFLAGS) (as_const B ly).
Hypothesis HC_cflag_tga : forall ly, In (z1 (ANum SM8_CFLAG_TGA) 1) (as_const B ly).
(* The .got slot of current_verbosity and its value 0: DTLS_on_tls_get_addr 0x6b290 / 0x6b29c. *)
Hypothesis HC_got_verb : forall ly, In (z8 (ANum SM8_GOT_VERB) SM8_VERB) (as_const B ly).
Hypothesis HC_verb : forall ly, In (z4 (ANum SM8_VERB) 0) (as_const B ly).
(* The .got slot of DTLS's tp offset: DTLS_on_tls_get_addr 0x6b2a0. *)
Hypothesis HC_got_dtls : forall ly, In (z8 (ANum SM8_GOT_DTLS) SM8_DTLS_TPOFF) (as_const B ly).

(* The absolute cells of sm8A_rodata are exactly the HC_ cells above. *)
Lemma sm8A_abs_incl : forall ly, incl (ro_cells sm8A_rodata) (as_const B ly).
Proof.
intros ly c Hc. unfold ro_cells, sm8A_rodata in Hc. cbn [In flat_map map fst snd app] in Hc.
repeat (destruct Hc as [<- | Hc];
[ first [ exact (HC_tls_got_mod ly) | exact (HC_tls_got_off ly) | exact (HC_real_tga ly) | exact (HC_dtv1 ly)
| exact (HC_asan_inited ly) | exact (HC_tsd_key_inited ly) | exact (HC_tsd_key ly) | exact (HC_got_cflags ly)
| exact (HC_cflag_tga ly) | exact (HC_got_verb ly) | exact (HC_verb ly) | exact (HC_got_dtls ly) ] |]).
destruct Hc.
Qed.

Lemma sm8A_const_val : forall ly S W mem md e (w : nat) e', AR tfibsegs B ly S W mem md ->
In (ACell e w (AV e')) (as_const B ly) -> val_mem tfibsegs (mrestrict (w_H W) mem) (aeval B ly e) w (aeval B ly e').
Proof.
intros ly S W mem md e w e' HAR Hin. apply sm8_cell_holds_val_mem.
exact (proj1 (Forall_forall _ _) (am_const B ly S _ (proj1 HAR)) _ Hin).
Qed.
Lemma sm8A_rodata_ok : forall ly S W mem md E, AR tfibsegs B ly S W mem md ->
Forall (region_ok tfibsegs E (mrestrict (w_H W) mem)) (map ro_region sm8A_rodata).
Proof.
intros ly S W mem md E HAR.
assert (Hwf : ro_wf sm8A_rodata = true) by (vm_compute; reflexivity).
unfold ro_wf in Hwf. rewrite forallb_forall in Hwf.
apply Forall_map. apply Forall_forall. intros [[base sz] cs] Hin.
specialize (Hwf _ Hin). cbn [fst snd] in Hwf. apply andb_prop in Hwf as [Hw Hcs]. apply andb_prop in Hw as [H0 Hhi].
apply Z.leb_le in H0. apply Z.leb_le in Hhi.
unfold ro_region, region_ok. cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
rewrite forallb_forall in Hcs. apply Forall_map. apply Forall_forall. intros [[off nn] v] Hc.
specialize (Hcs _ Hc). cbn [fst snd] in Hcs.
apply andb_prop in Hcs as [Hcs H3]. apply andb_prop in Hcs as [H1 H2].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3.
unfold ro_chunk. cbn [fst snd].
apply (chunk_ok_val tfibsegs E _ 0 (base + off) nn (SLit v) v); [reflexivity | lia | lia |]. rewrite Z.add_0_l.
assert (Hcell : In (ACell (ANum (base + off)) (N.to_nat nn) (AV (ANum v))) (as_const B ly)).
{ apply (sm8A_abs_incl ly). unfold ro_cells. apply in_flat_map. exists (base, sz, cs). split; [exact Hin|].
exact (in_map (fun c => ACell (ANum (fst (fst (base, sz, cs)) + fst (fst c))) (N.to_nat (snd (fst c))) (AV (ANum (snd c)))) cs (off, nn, v) Hc). }
exact (sm8A_const_val ly S W mem md (ANum (base + off)) (N.to_nat nn) (ANum v) HAR Hcell).
Qed.

Lemma sm8_segA_holds : sm8_segA B.
Proof.
intros ly S W regs mem md pos S' n HE.
destruct HE as (HPRE & G10n & Hnr & Hn8 & Hcnt & Hpath).
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp). unfold ESTACK in Hslo, HpresE.
pose proof sm8_Hwx as Hwx.
set (hints := fs_hint (st_fs S)) in *. set (hint := znth 0 CID8 hints) in *.
pose proof (proj1 HAR) as M.
pose proof (wfs_hints _ (wf_fakestack _ _ _ _ _ (am_wf _ _ _ _ M))) as [Hlen Hpos0]. fold hints in Hlen, Hpos0.
assert (Hh0 : 0 <= hint).
{ unfold hint, znth. destruct (Nat.lt_ge_cases (Z.to_nat CID8) (length hints)) as [L|L];
[exact (proj1 (Forall_forall _ _) Hpos0 _ (nth_In _ 0 L)) | rewrite nth_overflow by exact L; lia]. }
pose proof (am_layout B ly S _ M) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
pose proof (sm8_img_cover_of_ledger ly _ _ (proj1 (proj2 HAR))) as IMG.
assert (ZI : forall e, In e (owned_extents ly) -> sm8_zone3 (fst e) (snd e)).
{ intros e Hex. pose proof (proj1 (Forall_forall _ _) (lo_app ly HLY) e Hex) as IA. cbv beta in IA.
assert (D9 : zdisjoint e (ly_img ly)).
{ pose proof (lo_disj ly HLY) as PD.
exact (pairwise_In zdisjoint (static_extents ly) e (ly_img ly) (owned_extents ly ++ [(ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)]) [ly_img ly]
ltac:(unfold static_extents; rewrite <- app_assoc; reflexivity) PD ltac:(apply in_app_iff; left; exact Hex) ltac:(left; reflexivity)). }
assert (SZ : 0 <= snd e).
{ unfold owned_extents in Hex. cbn [In] in Hex. decompose [or] Hex; subst; cbn [snd];
unfold kPrimResvSize, kPtrArrayResv, kThreadObjSize, kFakeStackSize, kNodesBlockSize, kStoreBlockSize; lia. }
exact (sm8_zone3_intro ly (fst e) (snd e) IMG SZ IA ltac:(destruct e; exact D9)). }
pose proof (ZI (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; cbn; tauto)) as (HT1 & HT2 & HTz).
pose proof (ZI (ly_F ly, kFakeStackSize) ltac:(unfold owned_extents; cbn; tauto)) as (HF1 & HF2 & HFz).
pose proof (ZI (ly_C ly, 256) ltac:(unfold owned_extents; cbn; tauto)) as (HC1 & HC2 & HCz).
pose proof (ZI (ly_D ly, 4096) ltac:(unfold owned_extents; cbn; tauto)) as (HD1 & HD2 & HDz).
cbn [fst snd] in HT1, HT2, HTz, HF1, HF2, HFz, HC1, HC2, HCz, HD1, HD2, HDz.
ceil; unfold ASAN_CEIL, kThreadObjSize, kFakeStackSize in HT1, HT2, HF1, HF2, HC1, HC2, HD1, HD2.
unfold sm8_zone3cases, SM8_IMG_LO, SM8_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kFakeStackSize in HTz, HFz, HCz, HDz.
assert (CE : alloc_ceiling <= 140737479966720) by (ceil; lia).
apply (fun X => Z.le_trans _ _ _ X CE) in HT2. apply (fun X => Z.le_trans _ _ _ X CE) in HC2.
apply (fun X => Z.le_trans _ _ _ X CE) in HD2. apply (fun X => Z.le_trans _ _ _ X CE) in HF2.
pose proof (lo_T_al ly HLY) as HTal. pose proof (lo_F_al ly HLY) as HFal. pose proof (lo_D_al ly HLY) as HDal. pose proof (lo_C_al ly HLY) as HCal.
unfold page_aligned in HTal, HFal, HDal.
pose proof (lo_disj ly HLY) as PW. unfold static_extents, owned_extents in PW. cbn [app pairwise] in PW.
destruct PW as (_ & _ & PWT & PWF & _ & _ & PWC & PWD & _).
assert (DTF : zdisjoint (ly_T ly, kThreadObjSize) (ly_F ly, kFakeStackSize)) by (exact (Forall_inv PWT)).
assert (DTC : zdisjoint (ly_T ly, kThreadObjSize) (ly_C ly, 256)) by (exact (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail PWT))))).
assert (DTD : zdisjoint (ly_T ly, kThreadObjSize) (ly_D ly, 4096)) by (exact (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail PWT)))))).
assert (DTS : zdisjoint (ly_T ly, kThreadObjSize) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)) by (exact (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail PWT))))))).
assert (DFC : zdisjoint (ly_F ly, kFakeStackSize) (ly_C ly, 256)) by (exact (Forall_inv (Forall_inv_tail (Forall_inv_tail PWF)))).
assert (DFD : zdisjoint (ly_F ly, kFakeStackSize) (ly_D ly, 4096)) by (exact (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail PWF))))).
assert (DFS : zdisjoint (ly_F ly, kFakeStackSize) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)) by (exact (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail PWF)))))).
assert (DCD : zdisjoint (ly_C ly, 256) (ly_D ly, 4096)) by (exact (Forall_inv PWC)).
assert (DCS : zdisjoint (ly_C ly, 256) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)) by (exact (Forall_inv (Forall_inv_tail PWC))).
assert (DDS : zdisjoint (ly_D ly, 4096) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)) by (exact (Forall_inv PWD)).
clear PWT PWF PWC PWD. unfold zdisjoint, kThreadObjSize, kFakeStackSize in DTF, DTC, DTD, DTS, DFC, DFD, DFS, DCD, DCS, DDS.
cbn [fst snd] in DTF, DTC, DTD, DTS, DFC, DFD, DFS, DCD, DCS, DDS.
set (T := ly_T ly) in *. set (C := ly_C ly) in *. set (D := ly_D ly) in *. set (F := ly_F ly) in *.
set (sp0 := spZ regs) in *. set (H := w_H W) in *.
assert (Hsp44 : 2 ^ 44 <= sp0 <= 2 ^ 47) by (clear - Hslo Htop Lbeg Lhi; lia).
(* The start-up cells, from B's certificate through AR's am_const. *)
assert (CV : forall e (w : nat) e', In (ACell e w (AV e')) (as_const B ly) ->
val_mem tfibsegs (mrestrict H mem) (aeval B ly e) w (aeval B ly e')).
{ intros e w e' Hin. exact (sm8A_const_val ly S W mem md e w e' HAR Hin). }
assert (HTSDv : ly_tsd ly = SM8_TSD) by (rewrite (am_tsd B ly S _ M), HC_tsd; reflexivity).
assert (VT0 : val_mem tfibsegs (mrestrict H mem) SM8_TP 8 F).
{ pose proof (CV (ATp 0) 8%nat (AF 0) (HC_fake_stack ly)) as V.
cbn [aeval] in V. rewrite HC_tp, !Z.add_0_r in V. exact V. }
assert (VTm88 : val_mem tfibsegs (mrestrict H mem) (SM8_TP - 88) 8 SM8_TSD).
{ pose proof (CV (ATp (-88)) 8%nat (ATsd 0) (HC_tsd_slot ly)) as V.
cbn [aeval] in V. rewrite HC_tp, HTSDv, Z.add_0_r in V. exact V. }
assert (VTm8 : val_mem tfibsegs (mrestrict H mem) (SM8_TP - 8) 8 SM8_DTV).
{ pose proof (CV (ATp (-8)) 8%nat (ANum SM8_DTV) (HC_dtv ly)) as V.
cbn [aeval] in V. rewrite HC_tp in V. exact V. }
assert (VT8 : val_mem tfibsegs (mrestrict H mem) (SM8_TP + 8) 8 D).
{ pose proof (CV (ATp 8) 8%nat (AD 0) (HC_dtls ly)) as V.
cbn [aeval] in V. rewrite HC_tp, !Z.add_0_r in V. exact V. }
assert (VD24 : val_mem tfibsegs (mrestrict H mem) (D + 24) 8 SM8_TP).
{ pose proof (CV (AD 24) 8%nat (ATp 0) (HC_dtls_dtv1 ly)) as V.
cbn [aeval] in V. rewrite HC_tp, !Z.add_0_r in V. exact V. }
assert (VTSD : val_mem tfibsegs (mrestrict H mem) SM8_TSD 8 C).
{ pose proof (CV (ATsd 0) 8%nat (AC 0) (HC_tsd_main ly)) as V.
cbn [aeval] in V. rewrite HTSDv, !Z.add_0_r in V. exact V. }
assert (VC152 : val_mem tfibsegs (mrestrict H mem) (C + 152) 8 T).
{ pose proof (CV (AC 152) 8%nat (AT 0) (HC_ctx_thread ly)) as V.
cbn [aeval] in V. rewrite !Z.add_0_r in V. exact V. }
assert (VT48 : val_mem tfibsegs (mrestrict H mem) (T + 48) 8 SM8_T_TLS_BEG).
{ pose proof (CV (AT 48) 8%nat (ANum SM8_T_TLS_BEG) (HC_thread_tls_beg ly)) as V.
cbn [aeval] in V. exact V. }
assert (VT56 : val_mem tfibsegs (mrestrict H mem) (T + 56) 8 SM8_T_TLS_END).
{ pose proof (CV (AT 56) 8%nat (ANum SM8_T_TLS_END) (HC_thread_tls_end ly)) as V.
cbn [aeval] in V. exact V. }
(* AR's fake-stack header cells (fs_cells, YG0n.v:100): kStackSizeLog, the GC byte, the class-8 hint. *)
assert (CELL : forall e (ww : nat) z, In (ACell e ww (AV (ANum z))) (fs_cells S) -> val_mem tfibsegs (mrestrict H mem) (aeval B ly e) ww z).
{ intros e ww z Hin. exact (sm8_cell_holds_val_mem B ly H mem e ww (ANum z) (proj1 (Forall_forall _ _) (am_cells B ly S _ M) _ (sm8_In_fs_cells_acells B ly S _ Hin))). }
assert (VF88 : val_mem tfibsegs (mrestrict H mem) (F + 88) 8 kStackSizeLog) by (exact (CELL (AF 88) 8%nat kStackSizeLog ltac:(left; reflexivity))).
assert (VF96 : val_mem tfibsegs (mrestrict H mem) (F + 96) 1 0) by (exact (CELL (AF 96) 1%nat 0 ltac:(right; left; reflexivity))).
assert (VFH : val_mem tfibsegs (mrestrict H mem) (F + HOFF8) 8 hint).
{ refine (CELL (AF HOFF8) 8%nat hint _). right; right. unfold fs_cells.
change (AF HOFF8) with (AF (8 * Z.of_nat 8%nat)). unfold hint, znth. change (Z.to_nat CID8) with 8%nat.
apply (in_map (fun iv : nat * Z => z8 (AF (8 * Z.of_nat (fst iv))) (snd iv)) _ (8%nat, nth 8 hints 0)).
fold hints. rewrite <- Hlen. apply (sm8_combine_seq_nth hints 0 0 8). lia. }
set (hm := hint mod 2 ^ 64). assert (Hhm : 0 <= hm < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
assert (VFH' : val_mem tfibsegs (mrestrict H mem) (F + HOFF8) 8 hm) by (exact (sm8_val_mem_mod64 _ _ _ VFH)).
(* The symbolic environment: atoms 0..31 are the entry registers, 32..36 are T, C, D, F and the hint. *)
set (E := Ereg regs [w64 T; w64 C; w64 D; w64 F; w64 hm]).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (E2 : bv_unsigned (ew E 2) = sp0) by (rewrite (EEreg 2%nat 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = w64 T) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 C) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 D) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = w64 F) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = w64 hm) by (subst E; exact (ew_Ereg_extra regs _ 4)).
assert (U32 : bv_unsigned (ew E 32) = T) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = C) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = D) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = F) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = hm) by (rewrite E36; apply unsigned_lit_small; lia).
assert (DSO : forall k c z, bv_unsigned (ew E k) = z -> sv_denot E (SOff k c) = Z_to_bv 64 (z + c)).
{ intros k c z Hk. cbn [sv_denot]. rewrite Hk. reflexivity. }
assert (DEN0 : forall k z, bv_unsigned (ew E k) = z -> 0 <= z < 2 ^ 64 -> sv_denot E (SOff k 0) = Z_to_bv 64 z).
{ intros k z Hk Hr. cbn [sv_denot]. rewrite Hk, Z.add_0_r. reflexivity. }
(* The entry state is the symbolic state ssA. *)
assert (HS0 : st_ok tfibsegs E ssA (restrict H (mkst regs (Z_to_bv 64 PC_STACK_MALLOC_8) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssA.
apply (st_ok_regs tfibsegs E (mkSS PC_STACK_MALLOC_8 sr_atoms memA None (mkFacts factsA [] [])) _ regsA).
2:{ apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; rewrite (EEreg 4%nat 4%bv eq_refl), Htp, HC_tp; reflexivity) ] |]).
destruct Hr. }
unfold memA. apply (entry_st_ok_full tfibsegs); change (Ereg regs [w64 T; w64 C; w64 D; w64 F; w64 hm]) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- assert (RO : Forall (region_ok tfibsegs E (mrestrict H mem)) (map ro_region sm8A_rodata)) by (exact (sm8A_rodata_ok ly S W mem md E HAR)).
assert (CK : forall base off (nn : N) e v, sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N nn) -> Z.of_N nn <= 8 ->
val_mem tfibsegs (mrestrict H mem) (base + off) (N.to_nat nn) v -> YP09.chunk_ok tfibsegs E (mrestrict H mem) base (YP09.mkChunk off (CVal nn e))).
{ intros. eapply (chunk_ok_val tfibsegs E); eassumption. }
change (stkA :: rTSD :: rTP0 :: rTP8 :: rT :: rC :: rD :: rF :: rTPm88 :: rTPm8 :: map ro_region sm8A_rodata)
with ([stkA; rTSD; rTP0; rTP8; rT; rC; rD; rF; rTPm88; rTPm8] ++ map ro_region sm8A_rodata).
apply Forall_app. split; [|exact RO]. repeat apply Forall_cons; try apply Forall_nil.
+ unfold stkA. apply (region_ok_stack tfibsegs E _ 2 sp0 (- SM8_WIN)); [exact E2 | unfold SM8_WIN; lia | lia |].
intros a Ha. apply (YCe5.apresent_writable tfibsegs). apply HpresE. unfold SM8_WIN in Ha. lia.
+ unfold rTSD, aC, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold SM8_TSD.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (CK 0 _ 8%N _ C); [apply (DEN0 _ C U33); lia | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact VTSD].
+ unfold rTP0, aF, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold SM8_TP.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (CK 0 _ 8%N _ F); [apply (DEN0 _ F U35); lia | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact VT0].
+ unfold rTP8, aD, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold SM8_TP.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (CK 0 _ 8%N _ D); [apply (DEN0 _ D U34); lia | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact VT8].
+ unfold rT, aT, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U32.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [apply (CK T _ 8%N _ SM8_T_TLS_BEG); [reflexivity | cbn; unfold SM8_T_TLS_BEG; lia | cbn; lia | exact VT48]|].
apply Forall_cons; [apply (CK T _ 8%N _ SM8_T_TLS_END); [reflexivity | cbn; unfold SM8_T_TLS_END; lia | cbn; lia | exact VT56] | apply Forall_nil].
+ unfold rC, aC, aT, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U33.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (CK C _ 8%N _ T); [apply (DEN0 _ T U32); lia | cbn; lia | cbn; lia | exact VC152].
+ unfold rD, aD, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U34.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (CK D _ 8%N _ SM8_TP); [reflexivity | cbn; unfold SM8_TP; lia | cbn; lia | exact VD24].
+ unfold rF, aF, aH, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U35. unfold HOFF8, CID8.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [apply (CK F _ 8%N _ hm); [apply (DEN0 _ hm U36); lia | cbn; lia | cbn; lia | exact VFH']|].
apply Forall_cons; [apply (CK F _ 8%N _ kStackSizeLog); [reflexivity | cbn; unfold kStackSizeLog; lia | cbn; lia | exact VF88]|].
apply Forall_cons; [apply (CK F _ 1%N _ 0); [reflexivity | cbn; lia | cbn; lia | exact VF96] | apply Forall_nil].
+ unfold rTPm88. apply (ro_region_ok E _ (SM8_TP - 88) 8%N SM8_TSD); [unfold SM8_TP; lia | cbn; unfold SM8_TP; lia | cbn; unfold SM8_TSD; lia | cbn; lia | exact VTm88].
+ unfold rTPm8. apply (ro_region_ok E _ (SM8_TP - 8) 8%N SM8_DTV); [unfold SM8_TP; lia | cbn; unfold SM8_TP; lia | cbn; unfold SM8_DTV; lia | cbn; lia | exact VTm8].
- apply pairwise_disjoint_of_extents.
unfold stkA, rTSD, rTP0, rTP8, rT, rC, rD, rF, rTPm88, rTPm8, aT, aC, aD, aF, aH, sm8A_rodata, ro_region, extent_of_region, HOFF8, CID8,
SM8_WIN, SM8_TSD, SM8_TP, SM8_DTV, SM8_TLS_GOT, SM8_REAL_TGA, SM8_ASAN_INITED, SM8_TSD_KEY_INITED, SM8_GOT_CFLAGS, SM8_CFLAG_TGA,
SM8_GOT_VERB, SM8_VERB, SM8_GOT_DTLS.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, U32, U33, U34, U35.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat split; first [ clear - HT1 HTz; lia | clear - HC1 HCz; lia | clear - HD1 HDz; lia | clear - HF1 HFz; lia
| clear DTF DTC DTD DTS DFC DFD DFS DCD DCS DDS HTz HFz HCz HDz; lia | clear HTz HFz HCz HDz; lia ].
- split; [|split; exact I]. cbn [f_atoms atoms_ok factsA]. unfold afact_ok, aT, aC, aD, aF, aH. cbn [af_lo af_hi af_al2].
rewrite E2, U32, U33, U34, U35, U36. ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, kFakeStackSize, SM8_WIN.
change (2 ^ 4) with 16. change (2 ^ 12) with 4096. change (2 ^ 3) with 8. change (2 ^ 0) with 1.
repeat split; first [exact Hal16 | exact HTal | exact HCal | exact HDal | exact HFal | apply Z.mod_1_r | clear HTz HFz HCz HDz; lia]. }
(* One symbolic run from the entry to PC_SM8_LOOP. *)
unfold cfg_at.
eapply (SRr_run_to_gen tfibsegs tbl_sm8A tbl_sm8A_ok Hwx W FUEL PC_SM8_LOOP E ssA eA RS_running _ md _ HS0 r_A).
intros ms1 mat1 HS1 HF _. change (st_ok tfibsegs E eA (restrict H ms1)) in HS1. cbn [ms_mem mkst] in HF.
destruct eA_facts as (PCA & RVA & R2 & R8 & R9 & R18 & R19 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R4 & RK).
pose proof (st_ok_restrict_mkst tfibsegs H E eA ms1 HS1 RVA) as Hshape. rewrite PCA in Hshape.
assert (RD : forall (r : bv 5) v, reg_is eA (bv_unsigned r) v = true -> getr (ms_regs ms1) r = sv_denot E v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr.
exact (st_ok_restrict_reg tfibsegs H E eA ms1 r HS1). }
assert (MEQ : forall z : word, ~ (sp0 - SM8_WIN <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. apply HF. intros Hin. apply Hz. pose proof (memA_windows E _ Hin) as Hw. rewrite E2 in Hw. exact Hw. }
apply SRr_ret. split; [reflexivity|].
exists (ms_regs ms1), (ms_mem ms1), (with_vm_backing (m_vm_lazy md) mat1 md).
split; [f_equal; exact Hshape|].
destruct eA_stk as (NS0 & BS0 & WS1 & WS2 & C8 & C16 & C24 & C32 & C40).
assert (SAV : forall (j : nat) off (k : nat), nth_error (YP09.r_chunks rSTKA) j = Some (YP09.mkChunk off (CVal 8 (SOff k 0))) ->
rdword (aview tfibsegs H (ms_mem ms1)) (sp0 + off) = Some (bv_unsigned (ew E k))).
{ intros j off k Hj. pose proof (bv_unsigned_in_range 64 (ew E k)) as Hk. change (bv_modulus 64) with (2 ^ 64) in Hk.
apply sm8_val_mem_rdword; [exact Hk|].
pose proof (sm8_st_ok_chunk_val H E eA ms1 0 rSTKA j off 8%N (SOff k 0) (bv_unsigned (ew E k)) HS1 NS0 Hj
ltac:(cbn [sv_denot]; rewrite Z.add_0_r; reflexivity) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hk) ltac:(cbn; lia)) as V.
rewrite BS0 in V. cbn [base_val] in V. rewrite E2 in V. exact V. }
unfold sm8_midAB.
split; [rewrite (RD 2%bv _ R2), (DSO 2%nat _ sp0 E2); replace (sp0 + - SM8_FRAME) with (sp0 - SM8_FRAME) by lia; reflexivity|].
split; [rewrite (RD 8%bv _ R8), (DSO 2%nat _ sp0 E2), Z.add_0_r; reflexivity|].
split; [rewrite (RD 9%bv _ R9); cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EEreg 10%nat 10%bv eq_refl); exact G10n|].
split; [rewrite (RD 18%bv _ R18), (DSO aF _ F U35), Z.add_0_r; reflexivity|].
split; [rewrite (RD 19%bv _ R19); reflexivity|].
split; [rewrite (RD 10%bv _ R10); reflexivity|].
split; [rewrite (RD 11%bv _ R11), (DSO aF _ F U35); reflexivity|].
split; [rewrite (RD 12%bv _ R12), (DSO aH _ (hint mod 2 ^ 64) U36), sm8_w64_mod, Z.add_0_r; reflexivity|].
split; [rewrite (RD 13%bv _ R13), (DSO aH _ (hint mod 2 ^ 64) U36), sm8_w64_mod;
replace (hint + (fs_frames CID8 - 1)) with (hint + fs_frames CID8 - 1) by lia; reflexivity|].
split; [rewrite (RD 14%bv _ R14), (DSO aF _ F U35); reflexivity|].
split; [rewrite (RD 15%bv _ R15); reflexivity|].
split; [rewrite (RD 16%bv _ R16), (DSO aH _ (hint mod 2 ^ 64) U36), sm8_w64_mod; reflexivity|].
split.
{ (* gp, tp and s4..s11 *)
intros r Hr. destruct (Z.eq_dec r 4) as [->|Hr4].
- replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity).
rewrite (RD 4%bv _ R4). cbn [sv_denot]. rewrite Htp, HC_tp. reflexivity.
- assert (Hin : In r [3; 20; 21; 22; 23; 24; 25; 26; 27]) by (clear - Hr Hr4; cbn [In]; lia).
rewrite forallb_forall in RK. specialize (RK r Hin). cbv beta in RK.
assert (U5 : bv_unsigned (Z_to_bv 5 r) = r).
{ rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. apply Z.mod_small. clear - Hr; lia. }
rewrite (RD (Z_to_bv 5 r) (SOff (Z.to_nat r) 0)) by (rewrite U5; exact RK).
cbn [sv_denot]. rewrite (EEreg (Z.to_nat r) (Z_to_bv 5 r)) by (rewrite U5; lia).
rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
split.
{ (* the five saved words *)
unfold sm8_saved. change (w_H W) with H. change (spZ regs) with sp0.
split; [replace (sp0 - 8) with (sp0 + -8) by lia; rewrite (SAV 23%nat (-8) 1%nat C8), (EEreg 1%nat 1%bv eq_refl); reflexivity|].
split; [replace (sp0 - 16) with (sp0 + -16) by lia; rewrite (SAV 22%nat (-16) 8%nat C16), (EEreg 8%nat 8%bv eq_refl); reflexivity|].
split; [replace (sp0 - 24) with (sp0 + -24) by lia; rewrite (SAV 21%nat (-24) 9%nat C24), (EEreg 9%nat 9%bv eq_refl); reflexivity|].
split; [replace (sp0 - 32) with (sp0 + -32) by lia; rewrite (SAV 20%nat (-32) 18%nat C32), (EEreg 18%nat 18%bv eq_refl); reflexivity|].
replace (sp0 - 40) with (sp0 + -40) by lia; rewrite (SAV 19%nat (-40) 19%nat C40), (EEreg 19%nat 19%bv eq_refl); reflexivity. }
split; [exact MEQ|].
split.
{ (* the ESTACK window stays present *)
intros a Ha. change (w_H W) with H. change (spZ regs) with sp0 in Ha. unfold ESTACK in Ha.
destruct (Z_lt_le_dec a (sp0 - SM8_WIN)) as [L|L].
- apply (sm8_apresent_same H mem); [apply MEQ; rewrite unsigned_lit_small by lia; lia | apply HpresE; lia].
- apply (sm8_st_ok_window_apresent H E eA ms1 0 rSTKA a HS1 NS0); [rewrite BS0, WS1, WS2; cbn [base_val]; rewrite E2; lia | unfold SM8_IMG_END; lia]. }
apply sbm_wvb.
Qed.
End f.
End d.
