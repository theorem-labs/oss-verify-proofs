(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bs X1c2 X1bn X1cc X1c8.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1ri.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1gj X1fd X1fl X1ei X1ea.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1en.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require X0pt.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c4.
Local Ltac plia_gen stock ::= plia_size stock.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation rsegs := X1gj.rsegs.
Notation mem := (word -> option byte).

Definition memcpy_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Dst Src N : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(Dst, Dst + N)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' Dst [CB (Z.to_nat N) src]
/\ bytes_at rsegs m' Src src.

Lemma memcpy_callw : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (Dst Src N : Z) (src junk : list byte),
bytes_at rsegs m Src src -> length src = Z.to_nat N -> rw_cells rsegs m Dst [CB (Z.to_nat N) junk] ->
(Src + N <= Dst \/ Dst + N <= Src)%Z -> (0 <= N < 2^64)%Z -> (0 <= Src < 2^64)%Z -> (0 <= Dst < 2^64)%Z -> mem_inv rsegs m ->
evt rsegs (memcpy_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst Src N src m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x39c5c) fc None m (seg_rom rsegs)).
Proof.
intros until junk. intros BA LEN DC SEP HN HS HD MI.
assert (ED : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit; lia).
assert (ES : bv_unsigned (Z_to_bv 64 Src) = Src) by (apply unsigned_lit; lia).
assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
eapply evt_mono. { eapply U.X1fd.memcpy_spec with (src := src) (junk := junk); rewrite ?ED, ?ES, ?EN; [exact BA | exact LEN | exact DC | exact SEP | exact MI]. }
intros ms' P. unfold U.X1fd.memcpy_post, memcpy_postv in *. rewrite ED, ES, EN in P. exact P.
Qed.

Definition fwx_nofit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp S l wfn lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 wfn) t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 S) (Z_to_bv 64 l) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 wfn) fc None m' (seg_rom rsegs)
/\ munch [(lo, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp).

Lemma fwx_nofit : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(Fp : Z) (flags : word) (wend wpos wbase wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) (S l lo : Z),
rw_cells rsegs m Fp (file_cells flags wend wpos wbase wfn bufp bufsize fd mode lbf tail) ->
a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 l -> a2 = Z_to_bv 64 Fp ->
(0 < wend < 2^64) -> (0 <= wpos <= wend) -> (wend - wpos < l < 2^64) -> (0 <= S < 2^64) -> (0 <= wfn < 2^64) -> (wfn mod 2 = 0) ->
stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 64) -> (0 <= lo) ->
mem_inv rsegs m ->
(Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
evt rsegs (fwx_nofit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp S l wfn lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x34d08) fc None m (seg_rom rsegs)).
Proof.
intros until lo. intros FC -> -> -> WEND WPOS L SR WFN WFE ST LO LO0 MI SEPF.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
pose proof (wmono_refl rsegs m) as WM.
unfold file_cells in FC.
carve_frame 64%nat ST.
do 13 step.
if_cases Hw; zify_cond Hw. 1:{ exfalso. lia. }
do 3 step.
if_cases Hr; zify_cond Hr. 1:{ exfalso. rewrite land_W64, Z.mod_small in Hr by lia. lia. }
do 13 step.
rewrite (ret_pc_even wfn) by (first [lia | exact WFE]).
release_frame FR ST (bv_unsigned sp).
unfold fwx_nofit_post. sys_finish.
Qed.

Definition fwx_ret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp : Z) (flags : word) (wend wpos wbase wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte)
(cap : nat) (junk src : list byte) (S l r lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' Fp (file_cells flags wend (wpos + l) wbase wfn bufp bufsize fd mode lbf tail)
/\ rw_cells rsegs m' wpos [CB (length src) src; CB (cap - length src) (skipn (length src) junk)]
/\ bytes_at rsegs m' S src.

Lemma fwx_tail : forall (x1 ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(s0v s1v s2v s3v s4v s5v : word) (j8 : list byte)
(F : bvmap 5 word) (fc : bv 32) (m0 m : mem)
(Fp : Z) (flags : word) (wend wpos wbase wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte)
(cap : nat) (junk src : list byte) (S l i lo : Z),
rw_cells rsegs m (bv_unsigned sp + -64) [CB 8 j8; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
rw_cells rsegs m Fp (file_cells flags wend wpos wbase wfn bufp bufsize fd mode lbf tail) ->
rw_cells rsegs m wpos [CB cap junk] -> (length src <= cap)%nat ->
bytes_at rsegs m S src -> Z.of_nat (length src) = l ->
stk rsegs m lo (bv_unsigned sp + -64) -> (0 <= lo <= bv_unsigned sp - 64) -> (bv_unsigned sp < 2^63) ->
munch [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
(0 <= Fp) -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
(0 <= wpos) -> (wpos + Z.of_nat cap < 2^64) -> (wpos + Z.of_nat cap <= lo \/ bv_unsigned sp <= wpos) ->
(wpos + Z.of_nat cap <= Fp \/ Fp + 232 <= wpos) ->
(S + l <= wpos \/ wpos + l <= S) -> (S + l <= lo \/ bv_unsigned sp <= S) -> (S + l <= Fp + 40 \/ Fp + 48 <= S) ->
(0 <= i) -> (i + l < 2^63) -> (S < 2^64) ->
evt rsegs (fwx_ret_post ra sp gp tp s0v s1v s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 F fc
Fp flags wend wpos wbase wfn bufp bufsize fd mode lbf tail cap junk src S l (i + l) lo m0)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 l)
(Z_to_bv 64 wpos) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 i) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x34e00) fc None m (seg_rom rsegs)).
Proof.
intros until lo. intros FR FC DST CAP SRC LEN ST LO0 SPHI MU WM MI Fp0 SEPF W0 WHI SEPW1 SEPW2 SEPS1 SEPS2 SEPS3 I0 IL SHI.
pose proof (rw_cells_bound _ _ _ _ DST) as BD. cbn [cells_size csize Nat.add] in BD. rewrite Nat.add_0_r in BD.
assert (LJ : length junk = cap) by (destruct DST as [[WF _] _]; cbn in WF; exact (proj1 WF)).
pose proof (rw_cells_bound _ _ _ _ FC) as BF.
pose proof (bytes_at_bound _ _ _ _ SRC) as BS.
unfold file_cells in FC.

apply (rw_cells_split_CB rsegs _ _ [] cap junk [] [length src; cap - length src]%nat) in DST; [ | cbn; lia ].
cbn [mk_CB_cells app] in DST.
apply (proj1 (X1en.rw_cells_app rsegs _ _ [_] _)) in DST. destruct DST as [DSTa DSTb].
cbn [cells_size csize Nat.add] in DSTb. rewrite Nat.add_0_r in DSTb.
step. step. step.
replace (Z_to_bv 64 l : word) with (Z_to_bv 64 (Z.of_nat (length src)) : word) by (rewrite LEN; reflexivity).
assert (SEPfr : bv_unsigned sp + -64 + 64 <= wpos \/ wpos + Z.of_nat (length src) <= bv_unsigned sp + -64) by lia.
call memcpy_callw.
1:{ exact SRC. }
1:{ rewrite Nat2Z.id. reflexivity. }
1:{ rewrite Nat2Z.id. exact DSTa. }
1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact MI. }
rewrite !Nat2Z.id in *.
do 4 step.
do 9 step.
release_frame FR ST (bv_unsigned sp).
rewrite firstn_all2 in DSTb by (rewrite length_skipn; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (DST' : rw_cells rsegs mm wpos ([CB (length src) src] ++ [CB (cap - length src)%nat (skipn (length src) junk)]))
by (apply (proj2 (X1en.rw_cells_app rsegs _ _ [_] _)); split; [exact PC|]; cbn [cells_size csize]; rewrite Nat.add_0_r; exact DSTb)
end.
cbn [app] in DST'. rewrite !LEN in *.
unfold fwx_ret_post, file_cells. sys_finish.
Qed.

Lemma fwx_fit_plain : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(Fp : Z) (flags : word) (wend wpos wbase wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte)
(cap : nat) (junk src : list byte) (S l lo : Z),
rw_cells rsegs m Fp (file_cells flags wend wpos wbase wfn bufp bufsize fd mode lbf tail) ->
rw_cells rsegs m wpos [CB cap junk] -> Z.of_nat cap = wend - wpos ->
bytes_at rsegs m S src -> Z.of_nat (length src) = l ->
a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 l -> a2 = Z_to_bv 64 Fp ->
(0 < wend < 2^64) -> (0 <= wpos) -> (l <= wend - wpos) -> (S < 2^64) ->
(2^31 <= lbf < 2^32) ->
stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 64) -> (0 <= lo) -> (bv_unsigned sp < 2^63) ->
mem_inv rsegs m ->
(0 <= Fp) -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
(wend <= lo \/ bv_unsigned sp <= wpos) -> (wend <= Fp \/ Fp + 232 <= wpos) ->
(S + l <= wpos \/ wend <= S) -> (S + l <= lo \/ bv_unsigned sp <= S) -> (S + l <= Fp \/ Fp + 232 <= S) ->
evt rsegs (fwx_ret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
Fp flags wend wpos wbase wfn bufp bufsize fd mode lbf tail cap junk src S l l lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x34d08) fc None m (seg_rom rsegs)).
Proof.
intros until lo. intros FC DST CAPE SRC LEN -> -> -> WEND W0 FIT SHI LBF ST LO LO0 SPHI MI Fp0 SEPF SEPW1 SEPW2 SEPS1 SEPS2 SEPS3.
pose proof (bytes_at_bound _ _ _ _ SRC) as BS.
pose proof (munch_refl [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)] m) as MU.
pose proof (wmono_refl rsegs m) as WM.
unfold file_cells in FC.
carve_frame 64%nat ST.
do 13 step.
if_cases Hw; zify_cond Hw. 1:{ exfalso. lia. }
do 3 step.
if_cases Hr; zify_cond Hr. 2:{ exfalso. rewrite land_W64, Z.mod_small in Hr by lia. lia. }
do 3 step.
pose proof (X1en.sx32_neg (Z_to_bv 64 lbf)) as NEG. rewrite unsigned_lit in NEG by lia. rewrite Z.mod_small in NEG by lia.
specialize (NEG ltac:(lia)).
if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
eapply fwx_tail; [exact FR | exact FC | exact DST | lia | exact SRC | exact LEN | exact ST | lia | lia | exact MU | exact WM | exact MI | lia ..].
Qed.
