(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bk X1bj X1cf X1bs X1c2 X1bq X1bu X1cc.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hu X1nq X1g7.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac ms_eq := cbv [mkR]; repeat first [ reflexivity | apply (f_equal (Z_to_bv 64)); lia | progress f_equal ].

Definition cdbk_bytes (base : Z) (n : nat) : list byte :=
match image_bytes rsegs base n with Some bs => bs | None => [] end.

Lemma cdbk_ro : forall m base n, mem_inv rsegs m ->
ro_bytes_b rsegs base (cdbk_bytes base n) = true -> 0 <= base -> base + Z.of_nat (length (cdbk_bytes base n)) <= 2^64 ->
u8ro rsegs m base (cdbk_bytes base n).
Proof.
intros m base n MI RB H0 HL. unfold u8ro.
pose proof (ro_cells_bytes_at rsegs m base _ (ro_cells_image rsegs m base _ MI RB H0 HL)) as BY.
cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY. exact BY.
Qed.

Ltac cdbk_ro_tac base n :=
let m := fresh "m" in let MI := fresh "MI" in let L := fresh "L" in
intros m MI; exists (cdbk_bytes base n);
assert (L : length (cdbk_bytes base n) = n) by (vm_compute; reflexivity);
split; [| exact L]; apply cdbk_ro; [exact MI| vm_compute; reflexivity| lia| rewrite L; lia].

Lemma cdbk_nb_ro : forall m, mem_inv rsegs m -> exists CD, u8ro rsegs m 0x113a8 CD /\ length CD = 640%nat.
Proof. cdbk_ro_tac 0x113a8 640%nat. Qed.
Lemma cdbk_nb_low1_ro : forall m, mem_inv rsegs m -> exists CD, u8ro rsegs m 0x11628 CD /\ length CD = 320%nat.
Proof. cdbk_ro_tac 0x11628 320%nat. Qed.
Lemma cdbk_nb_low2_ro : forall m, mem_inv rsegs m -> exists CD, u8ro rsegs m 0x11768 CD /\ length CD = 320%nat.
Proof. cdbk_ro_tac 0x11768 320%nat. Qed.
Lemma cdbk_nb_high1_ro : forall m, mem_inv rsegs m -> exists CD, u8ro rsegs m 0x118a8 CD /\ length CD = 320%nat.
Proof. cdbk_ro_tac 0x118a8 320%nat. Qed.
Lemma cdbk_nb_high2_ro : forall m, mem_inv rsegs m -> exists CD, u8ro rsegs m 0x119e8 CD /\ length CD = 320%nat.
Proof. cdbk_ro_tac 0x119e8 320%nat. Qed.
Lemma high_lsp_cdbk_ro : forall m, mem_inv rsegs m -> exists CD, u8ro rsegs m 0x11b28 CD /\ length CD = 512%nat.
Proof. cdbk_ro_tac 0x11b28 512%nat. Qed.
Lemma high_lsp_cdbk2_ro : forall m, mem_inv rsegs m -> exists CD, u8ro rsegs m 0x11d28 CD /\ length CD = 512%nat.
Proof. cdbk_ro_tac 0x11d28 512%nat. Qed.

Lemma rodata_ro : forall x, 0x10000 <= x < 0x1b000 -> ro_addr rsegs (wa x) = true.
Proof.
intros x Hx. unfold ro_addr. unfold wa. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2^64). rewrite Z.mod_small by lia.
cbn [find_segment Ubsan.M.loaded_segments Ubsan_loaded_segments Ubsan_segment_000 seg_base seg_size].
replace (Z.of_N 0x10000 <=? x) with true by (symmetry; apply Z.leb_le; lia).
replace (x + 1 <=? Z.of_N 0x10000 + Z.of_N 0xb000) with true by (symmetry; apply Z.leb_le; lia).
cbn [andb]. reflexivity.
Qed.

Lemma wr_at_apart_ro : forall m q k c n, mem_inv rsegs m -> wr_at rsegs m q k -> 0 < k -> 0 < n ->
0x10000 <= c -> c + n <= 0x1b000 ->
q + k <= c \/ c + n <= q.
Proof.
intros m q k c n MI [Hq0 [Hqk W]] Hk Hn Hc0 Hc1.
destruct (Z_lt_dec q (c + n)); [|lia]. destruct (Z_lt_dec c (q + k)); [|lia]. exfalso.
set (x := Z.max q c).
assert (Hx1 : q <= x < q + k) by lia. assert (Hx2 : c <= x < c + n) by lia.
specialize (W (x - q) ltac:(lia)). replace (q + (x - q)) with x in W by lia.
pose proof (rodata_ro x ltac:(lia)) as RO.
destruct (m (wa x)) eqn:E.
- pose proof (mem_inv_ro _ _ MI _ _ E). congruence.
- pose proof (wview_not_ro rsegs m (wa x) W E). congruence.
Qed.

Ltac bdec :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
    rewrite ?swrap32_small, ?slti0_nonneg by lia;
    first [ if_false_x | if_true_x | if_false_z | if_true_z ]
end.

Section F.
Context {RCEIL : RunCeiling}.
Context {ptr : Type}.
Implicit Types b : bits_st ptr.

#[using="Type"] Lemma unpack_pair : forall b n, speex_bits_unpack_unsigned b n = (uv b n, ub b n).
Proof. intros. unfold uv, ub. destruct (speex_bits_unpack_unsigned b n); reflexivity. Qed.

#[using="Type"] Lemma high_loop0 : forall (k : nat) (i qlsp pa pb pc : Z) (cur : list word) (m0 : mem)
(ra sp gp tp t0 t1 t2 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F1 : bvmap 5 word) (fc1 : bv 32) (m1 : mem),
Z.of_nat k = 8 - i -> 0 <= i < 8 -> pa = qlsp + 4 * i -> pb = qlsp + 4 * i -> pc = 8 - i -> 0 < qlsp ->
u32arr rsegs m1 qlsp cur -> length cur = 8%nat ->
munch [(qlsp, qlsp + 32)] m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> frm0 fc1 ->
evt rsegs (fun ms' => exists (xa6 : word) (F2 : bvmap 5 word) (fc2 : bv 32) (m2 : mem) (cur' : list word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 qlsp) s1 (Z_to_bv 64 8) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 (qlsp + 32)) (Z_to_bv 64 (qlsp + 32)) xa6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F2 (Z_to_bv 64 0x2b750) fc2 None m2 (seg_rom rsegs)
/\ munch [(qlsp, qlsp + 32)] m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ frm0 fc2 /\ u32arr rsegs m2 qlsp cur' /\ length cur' = 8%nat)
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 qlsp) s1 (Z_to_bv 64 i) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 pc) (Z_to_bv 64 pa) (Z_to_bv 64 pb) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x2b718) fc1 None m1 (seg_rom rsegs)).
Proof.
intros n. induction n as [|n Step];
intros i qlsp pa pb pc cur m0 ra sp gp tp t0 t1 t2 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F1 fc1 m1
Cnt Irng -> -> -> Qpos Qarr Qlen Foot Mono MI FRM; [lia|].
pose proof (u32arr_bound _ _ _ _ Qarr) as Qbnd. rewrite Qlen in Qbnd.
pose proof (u32arr_store_ok rsegs m1 qlsp cur i (wa (qlsp + 4 * i)) Qarr ltac:(rewrite Qlen; lia) eq_refl) as Wok.
zstep. bdec.
do 3 zstep. bdec.
zstep. bdec.
do 6 zstep.
let v := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 _ (le4 ?v)) _) => v end in
pose proof (u32arr_write rsegs m1 qlsp cur i v Qarr ltac:(rewrite Qlen; lia)) as Qarrw;
pose proof (mem_inv_store rsegs m1 (wa (qlsp + 4 * i)) (le4 v) MI ltac:(rewrite length_le4; exact Wok)) as MIw;
pose proof (wmono_write rsegs m0 m1 (wa (qlsp + 4 * i)) (le4 v) Mono) as Monow;
pose proof (munch_write _ m0 m1 (qlsp + 4 * i) (le4 v) Foot ltac:(lia) ltac:(rewrite length_le4; lia)
  ltac:(cbn [inside]; rewrite length_le4; lia)) as Footw;
change (wa (qlsp + 4 * i)) with (Z_to_bv 64 (qlsp + 4 * i)) in Qarrw, MIw, Monow, Footw;
set (mw := write_to_mem m1 (Z_to_bv 64 (qlsp + 4 * i)) (le4 v)) in *; clearbody mw.
clear Qarr Foot Mono MI Wok.
do 3 zstep.
destruct n as [|n].
- bdec. apply evt_done. do 5 eexists. split; [ms_eq|].
  split; [exact Footw|]. split; [exact Monow|]. split; [exact MIw|]. split; [exact FRM|].
  split; [exact Qarrw| rewrite upd_length; exact Qlen].
- bdec. eapply (Step (i + 1) qlsp (qlsp + 4 * i + 4) (qlsp + 4 * i + 4) (8 - i + -1));
  first [ eassumption | rewrite upd_length; assumption | lia ].
Qed.

Ltac high_cdbk_loop :=
intros n; induction n as [|n Step];
intros i qlsp CDB row po CD cur m0 ra sp gp tp t0 t1 t2 s1 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F1 fc1 m1
Cnt Irng -> Tpos Rnn Rfit Tsz Tab Apart Qarr Qlen Foot Mono MI FRM; [lia|];
pose proof (u32arr_bound _ _ _ _ Qarr) as Qbnd; rewrite Qlen in Qbnd;
pose proof (bytes_at_bound _ _ _ _ Tab) as Tbnd;
destruct (nth_error CD (Z.to_nat (row + i))) as [cb|] eqn:Pick; [|apply nth_error_None in Pick; lia];
pose proof (u8ro_read rsegs m1 CDB CD (row + i) cb (wa (CDB + (row + i))) Tab Pick ltac:(lia) eq_refl) as Rbyte;
pose proof (u32arr_read_nth rsegs m1 qlsp cur i (wa (qlsp + 4 * i)) Qarr ltac:(rewrite Qlen; lia) eq_refl) as Rword;
pose proof (u32arr_store_ok rsegs m1 qlsp cur i (wa (qlsp + 4 * i)) Qarr ltac:(rewrite Qlen; lia) eq_refl) as Wok;
do 3 zstep; bdec;
do 3 zstep; bdec;
do 5 zstep; bdec;
zstep; bdec;
do 9 zstep;
let v := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 _ (le4 ?v)) _) => v end in
pose proof (u32arr_write rsegs m1 qlsp cur i v Qarr ltac:(rewrite Qlen; lia)) as Qarrw;
pose proof (mem_inv_store rsegs m1 (wa (qlsp + 4 * i)) (le4 v) MI ltac:(rewrite length_le4; exact Wok)) as MIw;
pose proof (wmono_write rsegs m0 m1 (wa (qlsp + 4 * i)) (le4 v) Mono) as Monow;
pose proof (munch_write _ m0 m1 (qlsp + 4 * i) (le4 v) Foot ltac:(lia) ltac:(rewrite length_le4; lia)
  ltac:(cbn [inside]; rewrite length_le4; lia)) as Footw;
pose proof (u8ro_frame rsegs m1 CDB CD (qlsp + 4 * i) (le4 v) Tab ltac:(lia) ltac:(rewrite length_le4; lia)
  ltac:(rewrite length_le4; lia)) as Tabw;
change (wa (qlsp + 4 * i)) with (Z_to_bv 64 (qlsp + 4 * i)) in Qarrw, MIw, Monow, Footw, Tabw;
set (mw := write_to_mem m1 (Z_to_bv 64 (qlsp + 4 * i)) (le4 v)) in *; clearbody mw;
clear Qarr Foot Mono MI Wok Tab Rbyte Rword;
do 2 zstep;
destruct n as [|n];
[ bdec; apply evt_done; do 7 eexists; split; [ms_eq|];
  split; [exact Footw|]; split; [exact Monow|]; split; [exact MIw|]; split; [exact FRM|];
  split; [exact Qarrw| rewrite upd_length; exact Qlen]
| bdec; eapply (Step (i + 1) qlsp CDB row (4 * i + 4));
  first [ eassumption | rewrite upd_length; assumption | lia ] ].

#[using="Type"] Lemma high_loop1 : forall (k : nat) (i qlsp CDB row po : Z) (CD : list byte) (cur : list word) (m0 : mem)
(ra sp gp tp t0 t1 t2 s1 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F1 : bvmap 5 word) (fc1 : bv 32) (m1 : mem),
Z.of_nat k = 8 - i -> 0 <= i < 8 -> po = 4 * i -> 0 < CDB ->
0 <= row -> row + 8 <= Z.of_nat (length CD) -> Z.of_nat (length CD) <= 512 -> u8ro rsegs m1 CDB CD ->
qlsp + 32 <= CDB \/ CDB + Z.of_nat (length CD) <= qlsp ->
u32arr rsegs m1 qlsp cur -> length cur = 8%nat ->
munch [(qlsp, qlsp + 32)] m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> frm0 fc1 ->
evt rsegs (fun ms' => exists (xa5 xa6 xa7 : word) (F2 : bvmap 5 word) (fc2 : bv 32) (m2 : mem) (cur' : list word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 qlsp) s1 (Z_to_bv 64 8) (Z_to_bv 64 32) (Z_to_bv 64 CDB) (Z_to_bv 64 32) (Z_to_bv 64 row) xa5 xa6 xa7 s2 (Z_to_bv 64 (18446744073709551615 - qlsp)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F2 (Z_to_bv 64 0x2b7e8) fc2 None m2 (seg_rom rsegs)
/\ munch [(qlsp, qlsp + 32)] m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ frm0 fc2 /\ u32arr rsegs m2 qlsp cur' /\ length cur' = 8%nat)
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 qlsp) s1 (Z_to_bv 64 i) (Z_to_bv 64 po) (Z_to_bv 64 CDB) (Z_to_bv 64 32) (Z_to_bv 64 row) a5 a6 a7 s2 (Z_to_bv 64 (18446744073709551615 - qlsp)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x2b78c) fc1 None m1 (seg_rom rsegs)).
Proof. high_cdbk_loop. Qed.

#[using="Type"] Lemma high_loop2 : forall (k : nat) (i qlsp CDB row po : Z) (CD : list byte) (cur : list word) (m0 : mem)
(ra sp gp tp t0 t1 t2 s1 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F1 : bvmap 5 word) (fc1 : bv 32) (m1 : mem),
Z.of_nat k = 8 - i -> 0 <= i < 8 -> po = 4 * i -> 0 < CDB ->
0 <= row -> row + 8 <= Z.of_nat (length CD) -> Z.of_nat (length CD) <= 512 -> u8ro rsegs m1 CDB CD ->
qlsp + 32 <= CDB \/ CDB + Z.of_nat (length CD) <= qlsp ->
u32arr rsegs m1 qlsp cur -> length cur = 8%nat ->
munch [(qlsp, qlsp + 32)] m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> frm0 fc1 ->
evt rsegs (fun ms' => exists (xa5 xa6 xa7 : word) (F2 : bvmap 5 word) (fc2 : bv 32) (m2 : mem) (cur' : list word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 qlsp) s1 (Z_to_bv 64 8) (Z_to_bv 64 32) (Z_to_bv 64 CDB) (Z_to_bv 64 32) (Z_to_bv 64 row) xa5 xa6 xa7 s2 (Z_to_bv 64 (18446744073709551615 - qlsp)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F2 (Z_to_bv 64 0x2b880) fc2 None m2 (seg_rom rsegs)
/\ munch [(qlsp, qlsp + 32)] m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ frm0 fc2 /\ u32arr rsegs m2 qlsp cur' /\ length cur' = 8%nat)
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 qlsp) s1 (Z_to_bv 64 i) (Z_to_bv 64 po) (Z_to_bv 64 CDB) (Z_to_bv 64 32) (Z_to_bv 64 row) a5 a6 a7 s2 (Z_to_bv 64 (18446744073709551615 - qlsp)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x2b824) fc1 None m1 (seg_rom rsegs)).
Proof. high_cdbk_loop. Qed.

Ltac rebits R A D bb rj Lrj OBJ bs DAT Hbs SIDE :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (R : bits_rep rsegs mc A D bb)
by (split; [exists rj; split; [exact Lrj| exact OBJ]| split; [exists bs; split; [exact DAT| exact Hbs]| exact SIDE]]);
clear OBJ DAT
end.

Ltac after_unpack b0 bb n rj Lrj OBJ bs DAT Hbs SIDE OKp OKn Hv Lbs :=
try rename MI0 into MI; rewrite (unpack_pair bb n) in *; cbn [fst snd] in *;
lazymatch goal with H : bits_rep _ _ _ _ (ub bb n) |- _ =>
destruct H as ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE); unfold bits_cells in OBJ end;
lazymatch goal with H : ?v = Z_to_bv 64 (uv bb n) |- _ => subst v end;
pose proof (speex_bits_unpack_unsigned_ok bb n _ _ OKp ltac:(lia) (unpack_pair bb n)) as (OKn & Hv & _);
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b0)
by (let X := fresh in pose proof OKn as X; unfold bits_ok in X; rewrite Hbs, zlength_map_unsigned, ?ub_size in X; lia).

#[using="Type"] Lemma lsp_unquant_high_proof : @lsp_unquant_stmt ptr LspUnquantHigh.
Proof.
intros A D b qlsp old lo ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
Brep Ok0 Got Qold Qlen Stk Deep Glo Qglo Aglo Sq Sa Sd Qa Qd -> -> -> MI FRM Qpos Qal.
cbn [lsp_order lsp_entry] in *. unfold A_lsp_unquant_high, LSPQ_DEPTH, NB_GLOBALS_TOP in *.
change (Z.to_nat 8) with 8%nat in Qlen. change (4 * 8) with 32 in Sq, Qa, Qd.
assert (Bsz : BITS_SIZEOF = 48) by reflexivity.
pose proof (bv_unsigned_in_range 64 sp) as Usp. unfold bv_modulus in Usp.
apply u32arr_of_f32 in Qold. pose proof (u32arr_bound _ _ _ _ Qold) as Qbnd. rewrite Qlen in Qbnd.
destruct Got as (GotHi & _). unfold NB_GOT_LSP_HIGH in GotHi.
destruct Brep as ((pad0 & Plen0 & Cell0) & (buf0 & Buf0 & Dmap0) & Side0). unfold bits_cells in Cell0.
assert (Dlen0 : Z.of_nat (length buf0) = sb_buf_size b)
  by (pose proof Ok0 as Okx; unfold bits_ok in Okx; rewrite Dmap0, zlength_map_unsigned in Okx; lia).
pose proof (munch_refl [(lo, bv_unsigned sp); (qlsp, qlsp + 32); (A, A + BITS_SIZEOF)] m) as Foot.
pose proof (wmono_refl rsegs m) as Mono.
carve_frame 48%nat Stk.
do 8 zstep. bdec.
do 14 zstep. cond_prep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => call (high_loop0 8%nat 0 qlsp qlsp qlsp 8 old mc) end;
first [lia | eassumption | apply munch_refl | apply wmono_refl | idtac].
rename MI0 into MI.
do 3 zstep.
rebits Brep1 A D b pad0 Plen0 Cell0 buf0 Buf0 Dmap0 Side0.
call (X1g7.speex_bits_unpack_unsigned_spec A D b 6); first [exact Brep1 | exact Ok0 | lia | assumption | idtac].
after_unpack b b 6 pad1 Plen1 Cell1 buf1 Buf1 Dmap1 Side1 Ok0 Ok1 Vrng1 Dlen1.
clear Brep1.
do 3 zstep. bdec.
do 9 zstep.
rewrite zb_lxor_ones, Z.add_0_r, swrap32_small by lia.
pose proof (high_lsp_cdbk_ro _ MI) as (CD1 & Tab1 & Tlen1).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
  call (high_loop1 8%nat 0 qlsp 0x11b28 (uv b 6 * 8) 0 CD1 _ mc) end;
first [lia | eassumption | apply munch_refl | apply wmono_refl | idtac].
rename MI0 into MI.
do 3 zstep.
rebits Brep2 A D (ub b 6) pad1 Plen1 Cell1 buf1 Buf1 Dmap1 Side1.
call (X1g7.speex_bits_unpack_unsigned_spec A D (ub b 6) 6); first [exact Brep2 | exact Ok1 | lia | assumption | idtac].
after_unpack b (ub b 6) 6 pad2 Plen2 Cell2 buf2 Buf2 Dmap2 Side2 Ok1 Ok2 Vrng2 Dlen2.
clear Brep2.
do 3 zstep. bdec.
do 9 zstep.
rewrite Z.add_0_r, swrap32_small by lia.
pose proof (high_lsp_cdbk2_ro _ MI) as (CD2 & Tab2 & Tlen2).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
  call (high_loop2 8%nat 0 qlsp 0x11d28 (uv (ub b 6) 6 * 8) 0 CD2 _ mc) end;
first [lia | eassumption | apply munch_refl | apply wmono_refl | idtac].
rename MI0 into MI.
do 7 zstep.
release_frame FR Stk (bv_unsigned sp).
rebits Brep3 A D (ub (ub b 6) 6) pad2 Plen2 Cell2 buf2 Buf2 Dmap2 Side2.
apply evt_done. unfold lsp_unquant_post.
eexists. eexists (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _). do 4 eexists.
split; [reflexivity|].
split; [exact Foot|]. split; [exact Mono|]. split; [exact MI|]. split; [eassumption|].
split; [exact Stk|]. split; [apply f32_of_u32arr; eassumption|].
split; [eassumption|]. split; [exact Brep3| exact Ok2].
Qed.

End F.
