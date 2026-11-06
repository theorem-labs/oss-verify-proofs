(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW Qc27 Qc6I QJFf QVsB QDM6 QCiC Qpj5 QdZp Q13u QHig QwAs Q0Do Q6sh QKTr QJBH QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk QpY2 Q9Ho Qu3b QYyZ QnRU QteI QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QTVW.Mq5.
Import Qc27 Qc6I QJFf QVsB QDM6.
Import QCiC.Mq1 Qpj5.Mq1 QdZp.
Import Q13u QHig QwAs.Mq2 Q0Do.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5.
Import Q9Ho.Mq0.
Import QTVW.Mq4 Qu3b.Mq1 QYyZ.Mq2 QnRU.Mq4 QteI.Mq1 Qu3b.Mq0.
Import QlES.

Local Unset Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

Definition memcpy_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Dst Src N : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(Dst, Dst + N)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' Dst [CB (Z.to_nat N) src]
/\ bytes_at asegs m' Src src.

Definition fwx_saves_post {BAND : Band} (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) : machine_state -> Prop :=
fun ms' => exists (m' : mem) (j8 : list byte),
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 a2 a1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd33f0) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ stk asegs m' lo (bv_unsigned sp + -64).

Lemma fwx_saves {BAND : Band} : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> 0 <= lo -> mem_inv asegs m ->
evt asegs (fwx_saves_post ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd33c8) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros ST LO LO0 MI.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
carve_frame 64%nat ST.
do 10 step.
apply evt_done. unfold fwx_saves_post. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FR| exact ST].
Qed.

Definition fwx_nofit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp S l wfn lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 wfn) t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 S) (Z_to_bv 64 l) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 wfn) fc None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp).

Lemma fwx_nofit : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(Fp : Z) (flags : word) (wend wpos wbase wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) (S l lo : Z),
rw_cells asegs m Fp (file_cells flags wend wpos wbase wfn bufp bufsize fd mode lbf tail) ->
a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 l -> a2 = Z_to_bv 64 Fp ->
(0 < wend < 2^64) -> (0 <= wpos <= wend) -> (wend - wpos < l < 2^64) -> (0 <= S < 2^64) -> (0 <= wfn < 2^64) -> (wfn mod 2 = 0) ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 64) -> (0 <= lo) ->
mem_inv asegs m ->
(Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
evt asegs (fwx_nofit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp S l wfn lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd33c8) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros FC -> -> -> WEND WPOS L SR WFN WFE ST LO LO0 MI SEPF.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
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
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' Fp (file_cells flags wend (wpos + l) wbase wfn bufp bufsize fd mode lbf tail)
/\ rw_cells asegs m' wpos [CB (length src) src; CB (cap - length src) (skipn (length src) junk)]
/\ bytes_at asegs m' S src.

Lemma fwx_tail {BAND : Band} : forall (x1 ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(s0v s1v s2v s3v s4v s5v : word) (j8 : list byte)
(F : bvmap 5 word) (fc : bv 32) (m0 m : mem)
(Fp : Z) (flags : word) (wend wpos wbase wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte)
(cap : nat) (junk src : list byte) (S l i lo : Z),
rw_cells asegs m (bv_unsigned sp + -64) [CB 8 j8; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
rw_cells asegs m Fp (file_cells flags wend wpos wbase wfn bufp bufsize fd mode lbf tail) ->
rw_cells asegs m wpos [CB cap junk] -> (length src <= cap)%nat ->
bytes_at asegs m S src -> Z.of_nat (length src) = l ->
stk asegs m lo (bv_unsigned sp + -64) -> (0 <= lo <= bv_unsigned sp - 64) -> (bv_unsigned sp <= 2^47) ->
munch [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)] m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
(0 <= Fp) -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
(0 <= wpos) -> (wpos + Z.of_nat cap < 2^64) -> (wpos + Z.of_nat cap <= lo \/ bv_unsigned sp <= wpos) ->
(wpos + Z.of_nat cap <= Fp \/ Fp + 232 <= wpos) ->
(S + l <= wpos \/ wpos + l <= S) -> (S + l <= lo \/ bv_unsigned sp <= S) -> (S + l <= Fp + 40 \/ Fp + 48 <= S) ->
(0 <= i) -> (i + l < 2^63) -> (S < 2^64) ->

(band_lo <= lo) -> (lo <= bv_unsigned sp - QnRU.Mq3.FWRITEX_STACK) ->
shadow_base asegs m -> rt_consts_at asegs m -> rng_ok m S l -> rng_ok m wpos l ->
evt asegs (fwx_ret_post ra sp gp tp s0v s1v s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 F fc
Fp flags wend wpos wbase wfn bufp bufsize fd mode lbf tail cap junk src S l (i + l) lo m0)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 l)
(Z_to_bv 64 wpos) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 i) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd34c0) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros FR FC DST CAP SRC LEN ST LO0 SPHI MU WM MI Fp0 SEPF W0 WHI SEPW1 SEPW2 SEPS1 SEPS2 SEPS3 I0 IL SHI CEIL LOI SB RC RS RD.
pose proof CEIL as CEIL'. idtac. unfold QnRU.Mq3.FWRITEX_STACK, MEMCPY_ICPT_STACK in LOI.
pose proof (rw_cells_bound _ _ _ _ DST) as BD. cbn [cells_size csize Nat.add] in BD. rewrite Nat.add_0_r in BD.
assert (LJ : length junk = cap) by (destruct DST as [[WF _] _]; cbn in WF; exact (proj1 WF)).
pose proof (rw_cells_bound _ _ _ _ FC) as BF.
pose proof (bytes_at_bound _ _ _ _ SRC) as BS.
unfold file_cells in FC.

apply (rw_cells_split_CB asegs _ _ [] cap junk [] [length src; cap - length src]%nat) in DST; [ | cbn; lia ].
cbn [mk_CB_cells app] in DST.
apply (proj1 (QnRU.Mq3.rw_cells_app asegs _ _ [_] _)) in DST. destruct DST as [DSTa DSTb].
cbn [cells_size csize Nat.add] in DSTb. rewrite Nat.add_0_r in DSTb.
step. step. step.
replace (Z_to_bv 64 l : word) with (Z_to_bv 64 (Z.of_nat (length src)) : word) by (rewrite LEN; reflexivity).
assert (SEPfr : bv_unsigned sp + -64 + 64 <= wpos \/ wpos + Z.of_nat (length src) <= bv_unsigned sp + -64) by lia.
rewrite <- LEN in RS, RD.
call_u (memcpy_icpt_spec wpos S (Z.of_nat (length src)) lo src (firstn (length src) junk));
[ exact SRC| rewrite Nat2Z.id; reflexivity| rewrite Nat2Z.id; exact DSTa| lia| exact MI| lia
| unsigned_lits; exact ST| exact CEIL| unsigned_lits; unfold MEMCPY_ICPT_STACK; lia| unsigned_lits; lia| unsigned_lits; lia
| exact SB| exact RC| exact RS| exact RD|].
rewrite ?(unsigned_lit wpos), ?(unsigned_lit S), ?(unsigned_lit (Z.of_nat (length src))) in * by lia.
rewrite !Nat2Z.id in *.
match goal with Hd : rw_cells asegs _ wpos [CB (length src) src] |- _ => rename Hd into DSTa' end.
do 4 step.
do 9 step.
match goal with STa : stk asegs ?mc lo (bv_unsigned sp + -64)%Z, FRx : rw_cells asegs ?mc (bv_unsigned sp + -64)%Z _ |- _ =>
release_frame FRx STa (bv_unsigned sp) end.
rewrite firstn_all2 in DSTb by (rewrite length_skipn; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (DST' : rw_cells asegs mm wpos ([CB (length src) src] ++ [CB (cap - length src)%nat (skipn (length src) junk)]))
by (apply (proj2 (QnRU.Mq3.rw_cells_app asegs _ _ [_] _)); split; [exact DSTa'|]; cbn [cells_size csize]; rewrite Nat.add_0_r; exact DSTb)
end.
cbn [app] in DST'. rewrite !LEN in *.
unfold fwx_ret_post, file_cells. sys_finish.
Qed.

Lemma fwx_fit_plain {BAND : Band} : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(Fp : Z) (flags : word) (wend wpos wbase wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte)
(cap : nat) (junk src : list byte) (S l lo : Z),
rw_cells asegs m Fp (file_cells flags wend wpos wbase wfn bufp bufsize fd mode lbf tail) ->
rw_cells asegs m wpos [CB cap junk] -> Z.of_nat cap = wend - wpos ->
bytes_at asegs m S src -> Z.of_nat (length src) = l ->
a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 l -> a2 = Z_to_bv 64 Fp ->
(0 < wend < 2^64) -> (0 <= wpos) -> (l <= wend - wpos) -> (S < 2^64) ->
(2^31 <= lbf < 2^32) ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 64) -> (0 <= lo) -> (bv_unsigned sp <= 2^47) ->
mem_inv asegs m ->
(0 <= Fp) -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
(wend <= lo \/ bv_unsigned sp <= wpos) -> (wend <= Fp \/ Fp + 232 <= wpos) ->
(S + l <= wpos \/ wend <= S) -> (S + l <= lo \/ bv_unsigned sp <= S) -> (S + l <= Fp \/ Fp + 232 <= S) ->
(band_lo <= lo) -> (lo <= bv_unsigned sp - 64 - QnRU.Mq3.FWRITEX_STACK) ->
shadow_base asegs m -> rt_consts_at asegs m -> rng_ok m S l -> rng_ok m wpos l ->
evt asegs (fwx_ret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
Fp flags wend wpos wbase wfn bufp bufsize fd mode lbf tail cap junk src S l l lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd33c8) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros FC DST CAPE SRC LEN -> -> -> WEND W0 FIT SHI LBF ST LO LO0 SPHI MI Fp0 SEPF SEPW1 SEPW2 SEPS1 SEPS2 SEPS3 CEIL LOI SB RC RS RD.
pose proof CEIL as CEIL'. idtac.
pose proof (bytes_at_bound _ _ _ _ SRC) as BS. pose proof (proj1 (proj2 RD)) as WP47.
pose proof (munch_refl [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)] m) as MU.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUs.
pose proof (wmono_refl asegs m) as WM.
unfold file_cells in FC.
carve_frame 64%nat ST.
do 13 step.
if_cases Hw; zify_cond Hw. 1:{ exfalso. lia. }
do 3 step.
if_cases Hr; zify_cond Hr. 2:{ exfalso. rewrite land_W64, Z.mod_small in Hr by lia. lia. }
do 3 step.
pose proof (QnRU.Mq3.sx32_neg (Z_to_bv 64 lbf)) as NEG. rewrite unsigned_lit in NEG by lia. rewrite Z.mod_small in NEG by lia.
specialize (NEG ltac:(lia)).
if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (shadow_base_munch _ _ _ SB MUs ltac:(rt_wzones)) as SB1;
pose proof (rt_consts_at_munch _ _ _ RC MUs WM ltac:(rt_wzones)) as RC1;
assert (RS1 : rng_ok mc S l)
by (eapply rng_ok_munch; [exact RS| exact MUs| exact WM|]; apply Forall_cons; [| apply Forall_nil]; cbn [fst snd]; rewrite !SH_eq;
left; pose proof (proj1 (proj2 RS)); clear - H CEIL' BS; Z.div_mod_to_equations; lia);
assert (RD1 : rng_ok mc wpos l)
by (eapply rng_ok_munch; [exact RD| exact MUs| exact WM|]; apply Forall_cons; [| apply Forall_nil]; cbn [fst snd]; rewrite !SH_eq;
left; pose proof (proj1 (proj2 RD)); clear - H CEIL' BS W0; Z.div_mod_to_equations; lia)
end.
clear MUs.
eapply fwx_tail; [exact FR | exact FC | exact DST | lia | exact SRC | exact LEN | exact ST | lia | lia | exact MU | exact WM | exact MI | lia .. | exact SB1 | exact RC1 | exact RS1 | exact RD1].
Qed.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCNF QoNr Qk8e QoBx Qs9x QFd5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QTVW.Mq5.
Import Q13u Qc6I QJFf QVsB.
Import QCiC.Mq1 Qpj5.Mq1. Import QCNF.Mq1 QoNr. Import QdZp Qk8e.Mq0.
Import Qu3b.Mq3.
Import QTVW.Mq1 Qu3b.Mq1 QnRU.Mq3 QnRU.Mq4 QteI.Mq1.
Import QCNF.Mq0.
Import QoBx Qu3b.Mq0.
Import Qs9x. Import QJBH.
Import QHig QwAs.Mq2 Q0Do.
Import Q6sh QKTr.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5.
Import Q9Ho.Mq0.
Import QYyZ.Mq2 QFd5.Mq0 QteI.Mq2.
Import QlES.
Local Set Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Notation mem := (word -> option byte).

Definition OUT_DEPTH : Z := 3264.
Definition PC_DEPTH : Z := 5184.
Definition VF_DEPTH : Z := 5552.
Definition GLOBALS_TOP {BAND : Band} : Z := band_lo.
Definition STATIC_SPLIT : Z := 0x23080.

Section Sink.
Context {BAND : Band}.
Context {St : Type}.
Variables (Fp B BS : Z).
Variable SINK : mem -> St -> Prop.
Variable TOPOK : Z -> Prop.
Variable OUT : list Z -> M St unit.
Variable OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z.

Definition SR : list (Z * Z) := [(Fp, Fp + 232); (B, B + BS)].

Definition sink_frame_stmt : Prop :=
forall (W : list (Z * Z)) (m m' : mem) (st : St),
SINK m st -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= Fp \/ Fp + 232 <= fst iv) W ->
Forall (fun iv => snd iv <= B \/ B + BS <= fst iv) W ->
Forall (fun iv => GLOBALS_TOP <= fst iv) W ->
SINK m' st.

Definition sink_flags_stmt : Prop :=
forall m st, SINK m st -> exists fl : byte, rw_cells asegs m Fp [CB 1 [fl]] /\ Z.land (bv_unsigned fl) 32 = 0 /\ ISH m.

Definition topok_stmt : Prop := forall a b, a <= b -> TOPOK b -> TOPOK a.

Definition sink_ish_stmt : Prop := forall m st, SINK m st -> ISH m.

Definition out_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(S : Z) (bs : list Z) (lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch ((lo, bv_unsigned sp) :: SR) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ SINK m' st'
/\ ssp_cells m' canary
/\ bytes_at asegs m' S (zb bs).

Definition out_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (bs : list Z) (lo : Z) (canary : word),
SINK m st ->
bytes_at asegs m (bv_unsigned a0) (zb bs) ->
Forall (fun c => 0 <= c < 256) bs -> zlength bs < 2^31 ->
szone (bv_unsigned a0) (zlength bs) ->
a1 = Z_to_bv 64 (zlength bs) ->
a2 = Z_to_bv 64 Fp ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - OUT_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned sp <= 2^47) -> TOPOK (bv_unsigned sp) ->
ssp_cells m canary ->
mem_inv asegs m ->
(Fp + 232 <= lo \/ bv_unsigned sp <= Fp) -> (B + BS <= lo \/ bv_unsigned sp <= B) ->
(bv_unsigned a0 + zlength bs <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
(bv_unsigned a0 + zlength bs <= Fp \/ Fp + 232 <= bv_unsigned a0) ->
(bv_unsigned a0 + zlength bs <= B \/ B + BS <= bv_unsigned a0) ->
(bv_unsigned a0 + zlength bs <= 2^47) ->
implM asegs (OUT bs) st
(out_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) bs lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd33c8) fc None m (seg_rom asegs)).

Definition fpcall_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(lo : Z) (canary : word) (m : mem) : Z -> St -> machine_state -> Prop :=
fun r st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch ((lo, bv_unsigned sp) :: SR) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ frm0 fc'
/\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
/\ stk asegs m' lo (bv_unsigned sp)
/\ SINK m' st'
/\ ssp_cells m' canary.

Definition fpcall_stmt (c : Z * Z * Z * Z * Z) : Prop :=
let '(y, w, p, fl, t) := c in
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word),
SINK m st ->
y = bv_unsigned a1 + 2^64 * bv_unsigned a2 ->
a0 = Z_to_bv 64 Fp -> a3 = Z_to_bv 64 w -> a4 = Z_to_bv 64 p -> a5 = Z_to_bv 64 fl -> a6 = Z_to_bv 64 t ->
bv_unsigned a7 <> 5 ->
(-2^31 <= w <= 1) -> (-2^31 <= p < 2^20) -> (0 <= fl < 2^32) -> (0 <= t < 256) -> Z.lor t 32 <> 97 ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FMT_FP_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned sp <= 2^47) -> TOPOK (bv_unsigned sp) ->
ssp_cells m canary ->
mem_inv asegs m -> frm0 fc ->
(Fp + 232 <= lo \/ bv_unsigned sp <= Fp) -> (B + BS <= lo \/ bv_unsigned sp <= B) ->
implM asegs (OUTFP y w p fl t) st
(fpcall_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd4a44) fc None m (seg_rom asegs)).

Definition arg_ok (m : mem) (lo sp ap : Z) (slot : word) (a : parg) : Prop :=
match a with
| PA_s s => exists slack : list byte,
bytes_at asegs m (bv_unsigned slot) (zb s ++ Z_to_bv 8 0 :: slack)
/\ Forall (fun c => 0 < c < 256) s
/\ ((- (bv_unsigned slot + zlength s + 1)) mod 8 <= zlength slack)
/\ 0 < bv_unsigned slot
/\ szone (bv_unsigned slot) (zlength s + 1)
/\ (bv_unsigned slot + zlength s + 1 + zlength slack <= lo \/ sp <= bv_unsigned slot)
/\ (bv_unsigned slot + zlength s + 1 + zlength slack <= Fp \/ Fp + 232 <= bv_unsigned slot)
/\ (bv_unsigned slot + zlength s + 1 + zlength slack <= B \/ B + BS <= bv_unsigned slot)
/\ (bv_unsigned slot + zlength s + 1 + zlength slack <= ap \/ ap + 8 <= bv_unsigned slot)
/\ bv_unsigned slot + zlength s + 1 + zlength slack <= 2^47
| PA_i i => -2^31 <= i < 2^31 /\ bv_unsigned slot mod 2^32 = i mod 2^32
| PA_u u => 0 <= u < 2^32 /\ bv_unsigned slot mod 2^32 = u
| PA_g d => bv_unsigned slot = d
end.
Fixpoint args_ok (m : mem) (lo sp ap : Z) (slots : list word) (args : list parg) : Prop :=
match args with
| [] => True
| a :: args' => match slots with
| [] => False
| w :: slots' => arg_ok m lo sp ap w a /\ args_ok m lo sp ap slots' args'
end
end.

Definition printf_core_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(AP lo : Z) (canary : word) (m : mem) : Z -> St -> machine_state -> Prop :=
fun r st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (apv : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch ((lo, bv_unsigned sp) :: (AP, AP + 8) :: SR) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ frm0 fc'
/\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
/\ stk asegs m' lo (bv_unsigned sp)
/\ SINK m' st'
/\ ssp_cells m' canary
/\ rw_cells asegs m' AP [C8 apv]
/\ (0 <= r <= INT_MAX).

Definition printf_core_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word)
(fmt : list Z) (VA i : Z) (slots : list word) (args : list parg),
SINK m st ->
bytes_at asegs m (bv_unsigned a1) (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt ->
a0 = Z_to_bv 64 Fp ->
rw_cells asegs m (bv_unsigned a2) [C8 (Z_to_bv 64 (VA + 8 * i))] ->
va_area m VA slots -> 0 <= i -> args_ok m lo (bv_unsigned sp) (bv_unsigned a2) (skipn (Z.to_nat i) slots) args ->
Forall fpcall_stmt (fp_calls (length fmt) fmt args) ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - PC_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned sp + 16 <= 2^47) -> TOPOK (bv_unsigned sp) ->
ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->

(bv_unsigned a1 + zlength fmt <= STATIC_SPLIT) -> szone (bv_unsigned a1) (zlength fmt) -> (0 <= BS) ->
((945072 <= Fp /\ Fp + 232 <= 6565536) \/ (bv_unsigned a2 + 8 <= Fp /\ Fp + 232 <= VA)) ->
((6566104 <= B /\ B + BS <= lo) \/ (bv_unsigned a2 + 8 <= B /\ B + BS <= VA)) ->
(bv_unsigned sp <= bv_unsigned a2) -> (bv_unsigned a2 + 8 <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
implM asegs (printf_model OUT OUTFP fmt args) st
(printf_core_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (bv_unsigned a2) lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd3a0c) fc None m (seg_rom asegs)).
End Sink.

Definition printf_core1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ ssp_cells m' canary.

Definition printf_core1_stmt {BAND : Band} : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (canary : word) (fmt : list Z),
bytes_at asegs m (bv_unsigned a1) (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt ->
pass1_ok fmt = true ->
a0 = Z_to_bv 64 0 ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - PC_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned sp + 16 <= 2^47) ->
ssp_cells m canary -> mem_inv asegs m ->
(bv_unsigned a1 + zlength fmt <= STATIC_SPLIT) -> szone (bv_unsigned a1) (zlength fmt) ->
(bv_unsigned sp <= bv_unsigned a2) -> (bv_unsigned a2 + 8 <= 2^64) ->
evt asegs (printf_core1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd3a0c) fc None m (seg_rom asegs)).

Definition TOPOK_none (sp : Z) : Prop := sp + 16 <= 2^47.

Definition OUT_MAX : Z := 16777216.

Section StderrSink.
Context {BAND : Band}.
Context {St : Type}.
Variable B : Z.

Definition SINK_stderr (m : mem) (bs : list Z * St) : Prop :=
let buf := fst bs in
exists (flags mode : word) (tail : list byte) (rest : list byte),
rw_cells asegs m RSTDERR (file_cells flags (B + 80) (B + zlength buf) B F_STDIO_WRITE B 80 2 mode 0xffffffff tail)
/\ Z.land (bv_unsigned flags) 32 = 0 /\ Z.land (bv_unsigned flags) 8 = 0
/\ rw_cells asegs m B [CB 80 (zb buf ++ rest)]
/\ zlength buf + zlength rest = 80
/\ B + 80 < 2^63 /\ GLOBALS_TOP + 64 <= B /\ B + 96 <= 2^47
/\ ISH m.

Definition OUT_stderr (s : list Z) : M (list Z * St) unit :=
fun bs => let '(buf, st) := bs in
if OUT_MAX <? zlength s then Qc6I.Ret Unr
else if INTERNAL_BUFSIZ - zlength buf <? zlength s
then ebind (stdio_writev 2 buf s st) (fun r => Qc6I.Ret (Ok (tt, ([], snd r))))
else Qc6I.Ret (Ok (tt, (buf ++ s, st))).
Definition OUTFP_stderr (y w p fl t : Z) : M (list Z * St) Z := fun _ => Qc6I.Ret Unr.
End StderrSink.

Section StdoutSink.
Context {BAND : Band}.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

Definition SINK_stdout (m : mem) (st : St) : Prop :=
let so := get_so st in
so_active so = true /\
exists (flags mode : word) (tail bufbytes : list byte),
rw_cells asegs m RSTDOUT
(file_cells flags (RSTDOUT_BUF + 1024) (RSTDOUT_BUF + zlength (so_buf so)) RSTDOUT_BUF
(if so_first so then F_STDOUT_WRITE else F_STDIO_WRITE)
RSTDOUT_BUF 1024 1 mode
(if so_lbf_nl so then 10 else 0xffffffff) tail)
/\ Z.land (bv_unsigned flags) 104 = 0
/\ rw_cells asegs m RSTDOUT_BUF [CB 1024 bufbytes]
/\ firstn (length (so_buf so)) bufbytes = to_bytes (so_buf so)
/\ zlength (so_buf so) <= 1024
/\ ISH m.
Definition OUTFP_stdout (y w p fl t : Z) : M St Z := fun _ => Qc6I.Ret Unr.

Definition OUT_stdout (s : list Z) : M St unit :=
if OUT_MAX <? zlength s then munr else stdout_fwritex get_so set_so s.
End StdoutSink.

Definition stderr_wfile (m : mem) : Prop :=
exists (flags mode : word) (e wend : Z) (tail : list byte),
rw_cells asegs m RSTDERR (file_cells flags wend e e F_STDIO_WRITE 0x6435e0 0 2 mode 0xffffffff tail)
/\ Z.land (bv_unsigned flags) 40 = 0.

Definition fwritex_stderr_stmt {BAND : Band} : Prop :=
forall (St : Type) (B : Z),
@out_stmt _ (list Z * St) RSTDERR B 80 (SINK_stderr B) TOPOK_none OUT_stderr.

Definition fwritex_stdout_stmt {BAND : Band} : Prop :=
forall (St : Type) (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St),
(forall s so, get_so (set_so so s) = so) -> (forall s so so', set_so so' (set_so so s) = set_so so' s) ->
@out_stmt _ St RSTDOUT RSTDOUT_BUF 1024 (SINK_stdout get_so) TOPOK_none (OUT_stdout get_so set_so).

Definition stdio_write_flush_post {BAND : Band} {St : Type} (B : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(F : bvmap 5 word) (fc : bv 32) (lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232); (B, B + 80)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ SINK_stderr B m' ([], st')
/\ ssp_cells m' canary.
Definition stdio_write_flush_stmt {BAND : Band} : Prop :=
forall (St : Type) (B : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (buf : list Z) (st : St) (lo : Z) (canary : word),
SINK_stderr B m (buf, st) ->
a0 = Z_to_bv 64 RSTDERR -> a2 = Z_to_bv 64 0 ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - OUT_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned sp <= 2^47) -> (B + 80 <= lo \/ bv_unsigned sp <= B) ->
ssp_cells m canary -> mem_inv asegs m ->
bv_unsigned a1 <= 2^47 ->
implM asegs (stdio_writev 2 buf [] : M St unit) st
(stdio_write_flush_post B ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd29d0) fc None m (seg_rom asegs)).

Definition towrite_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(flags mode : word) (wend wpos wbase writefn buf bufsize fd lbf : Z) (tail : list byte),
rw_cells asegs m (bv_unsigned a0) (file_cells flags wend wpos wbase writefn buf bufsize fd mode lbf tail) ->
Z.land (bv_unsigned flags) 8 = 0 ->
(0 <= buf) -> (buf + bufsize < 2^64) -> (0 <= bufsize) ->
mem_inv asegs m ->
evt asegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mode' : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned a0, bv_unsigned a0 + 232)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' (bv_unsigned a0) (file_cells flags (buf + bufsize) buf buf writefn buf bufsize fd mode' lbf tail))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd3374) fc None m (seg_rom asegs)).

Definition EMIT_DEPTH : Z := 5728.
Section Emit.
Context {BAND : Band}.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

Definition emit_printf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ frm0 fc'
/\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
/\ stk asegs m' lo (bv_unsigned sp)
/\ stdout_file m' (get_so st')
/\ ssp_cells m' canary.

Definition emit_printf_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word) (v : Z),
(forall x so, get_so (set_so so x) = so) -> (forall x so so', set_so so' (set_so so x) = set_so so' x) ->
fwritex_stdout_stmt ->
stdout_file m (get_so st) -> ISH m ->
(-2^31 <= v < 2^31) -> (bv_unsigned a1 mod 2^32 = v mod 2^32) ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - EMIT_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned sp + 16 <= 2^47) ->
ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
implM asegs (s_emit get_so set_so v) st
(emit_printf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x91a50) fc None m (seg_rom asegs)).

Definition FPRINTF_DEPTH : Z := 5664.

Definition AFMT_emit_d : Z := 0x14e05.      Definition AFMT_usage : Z := 0x1610a.
Definition AFMT_too_big : Z := 0x1a7dd.     Definition AFMT_cannot_open : Z := 0x1edde.
Definition AFMT_read_error : Z := 0x1edf3.

Definition diag_args (d : diag_msg) (m : mem) (fmtp argw : word) (lo sp : Z) : Prop :=
match d with
| DUsage s | DCannotOpen s | DReadError s =>
fmtp = Z_to_bv 64 (match d with DUsage _ => AFMT_usage | DCannotOpen _ => AFMT_cannot_open | _ => AFMT_read_error end)
/\ exists slack : list byte,
bytes_at asegs m (bv_unsigned argw) (zb s ++ Z_to_bv 8 0 :: slack)
/\ Forall (fun c => 0 < c < 256) s
/\ ((- (bv_unsigned argw + zlength s + 1)) mod 8 <= zlength slack)
/\ (zlength s <= OUT_MAX)
/\ (bv_unsigned argw + zlength s + 1 + zlength slack <= lo \/ sp <= bv_unsigned argw)
/\ (GLOBALS_TOP + 64 <= bv_unsigned argw) /\ (bv_unsigned argw + zlength s + 9 <= 2^47)
/\ (bv_unsigned argw + zlength s + 1 + zlength slack <= 2^47)
| DTooBig => fmtp = Z_to_bv 64 AFMT_too_big /\ bv_unsigned argw mod 2^32 = 67108864
| _ => False
end.

Definition fprintf_diag_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(lo : Z) (canary : word) (m : mem) (st : St) : unit -> St -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ frm0 fc'
/\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
/\ stk asegs m' lo (bv_unsigned sp)
/\ stderr_wfile m'
/\ ssp_cells m' canary
/\ st' = st.

Definition fprintf_diag_stmt : Prop :=
forall (d : diag_msg)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word),
fwritex_stderr_stmt -> stdio_write_flush_stmt ->
stderr_wfile m -> ISH m ->
a0 = Z_to_bv 64 RSTDERR -> diag_args d m a1 a2 lo (bv_unsigned sp) ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned sp + 16 <= 2^47) ->
ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
implM asegs (s_diag (St:=St) d) st
(fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x4f998) fc None m (seg_rom asegs)).
End Emit.

End Mq1.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Uaccess.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Qc6I QJFf QVsB QDM6.
Import QCiC.Mq1 Qpj5.Mq1 QdZp.
Import QTVW.Mq4 QnRU.Mq4 QteI.Mq1 Qu3b.Mq0.
Import QvG1.
Import QlES. Local Ltac QoSL.solve_load ::= QsGW.mkr__solve_load_1.
Local Unset Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

Definition STDIO_WRITE : Z := 0xd29d0.
Definition STDIO_WRITE_DEPTH : Z := 112.

Lemma dec_writev_Some : forall total rsp k, dec_writev total rsp = Some k ->
rsp = eff0 (Z_to_bv 64 k) /\ ((total = 0 /\ k = 0) \/ (1 <= k <= total)) /\ (0 <= k < 2^64).
Proof.
intros total [r ws zs us cs ci] k H. unfold dec_writev in H.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
destruct cs; [|discriminate]. destruct ci; [|discriminate].
pose proof (bv_unsigned_in_range 64 r) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2^64) in R.
destruct (((total =? 0) && (bv_unsigned r =? 0)) || ((1 <=? bv_unsigned r) && (bv_unsigned r <=? total)))%bool eqn:E; [|discriminate].
inversion H; subst. split. { unfold eff0. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split; [|lia]. apply Bool.orb_prop in E. destruct E as [E|E]; apply andb_prop in E; destruct E as [E1 E2].
- left. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. lia.
- right. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
Qed.

Section Glue.
Context {St : Type}.

Lemma implM_sys_k : forall {A B} (n : node) (dec : resp -> option A) (k : A -> M St B) (s0 : St)
(Q : B -> St -> machine_state -> Prop) ms,
evt asegs (fun ms1 : machine_state => at_node asegs n ms1 /\
(forall (rsp : resp) (a : A), dec rsp = Some a -> implM asegs (k a) s0 Q (nret ms1 rsp))) ms ->
implM asegs (Qpj5.Mq1.mbind (msys n dec) k) s0 Q ms.
Proof.
intros A B n dec k s0 Q ms H.
eapply implM_bind with (Q1 := fun a s' ms' => s' = s0 /\ implM asegs (k a) s0 Q ms').
- apply implM_sys. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
intros rsp a E. apply evt_done. split; [reflexivity|]. exact (Hk rsp a E).
- intros a s' ms' [-> H']. exact H'.
Qed.
End Glue.

Lemma land_ones64_l : forall x, (0 <= x < 2^64)%Z -> Z.land 18446744073709551615 x = x.
Proof. intros x Hx. rewrite Z.land_comm. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma land_0_l' : forall x, Z.land 0 x = 0.
Proof. intros. apply Z.land_0_l. Qed.
Lemma to_bytes_skipn : forall k (l : list Z), to_bytes (skipn k l) = skipn k (to_bytes l).
Proof. intros k l. unfold to_bytes. rewrite skipn_map. reflexivity. Qed.
Lemma bytes_at_skipn : forall segs m a bs k, bytes_at segs m a bs -> (k <= length bs)%nat ->
bytes_at segs m (a + Z.of_nat k) (skipn k bs).
Proof.
intros segs m a bs k H Hk. rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. destruct H as [_ H].
rewrite length_firstn, Nat.min_l in H by lia. exact H.
Qed.

Lemma zlength_skipn : forall (k : nat) (l : list Z), (k <= length l)%nat -> zlength (skipn k l) = zlength l - Z.of_nat k.
Proof. intros. unfold zlength. rewrite length_skipn. lia. Qed.
Lemma wv_advance_move : forall v0 v1 cnt, zlength v0 < cnt ->
wv_advance [v0; v1] cnt = [skipn (Z.to_nat (cnt - zlength v0)) v1].
Proof. intros. unfold wv_advance. replace (zlength v0 <? cnt) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.
Lemma wv_advance_stay : forall v0 rest cnt, cnt <= zlength v0 ->
wv_advance (v0 :: rest) cnt = skipn (Z.to_nat cnt) v0 :: rest.
Proof. intros. unfold wv_advance. replace (zlength v0 <? cnt) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.
Lemma skipn_skipn' : forall {A} (a b : nat) (l : list A), skipn a (skipn b l) = skipn (b + a) l.
Proof. intros. rewrite skipn_skipn. f_equal. lia. Qed.

Definition boxed (P : Prop) : Prop := P.

Ltac src_now SRC SEPS MU LSB :=
unfold boxed in SRC;
lazymatch goal with
| |- bytes_at _ ?m' ?S (to_bytes ?s) =>
destruct SEPS as [-> | [SEP1 SEP2]];
[ apply bytes_at_nil; lia
| apply (bytes_at_transport _ _ _ m' _ _ SRC MU); cbn [disjoint_from]; rewrite LSB; unfold zlength in SEP1, SEP2; lia ]
end.
Lemma length_to_bytes : forall l, length (to_bytes l) = length l.
Proof. intros. unfold to_bytes. apply length_map. Qed.
Lemma evt_evt : forall P ms, evt asegs P ms -> evt asegs (fun ms' => evt asegs P ms') ms.
Proof. intros P ms H. eapply evt_mono; [exact H|]. intros ms' H'. apply evt_done. exact H'. Qed.

Ltac lit_ret_pc :=
lazymatch goal with
| |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
end.

Ltac sysret_fast :=
step; step; step; step;
let Hc := fresh "Hc" in
if_cases Hc; zify_cond Hc; [| exfalso; lia]; step; try lit_ret_pc.

Section StdioWrite.
Context {BAND : Band}.
Context {St : Type}.

Definition stdio_write_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp : Z) (flags : word) (B bufsize wfn fd : Z) (mode : word) (lbf : Z) (tail : list byte)
(l : Z) (lo : Z) (canary : word) (m : mem) (st : St) : unit -> St -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 l) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - STDIO_WRITE_DEPTH, bv_unsigned sp); (Fp + 32, Fp + 64)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' Fp (file_cells flags (B + bufsize) B B wfn B bufsize fd mode lbf tail)
/\ ssp_cells m' canary
/\ st' = st.

Section Fixed.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St).
Variables (Fp : Z) (flags : word) (wend B bufsize wfn fd : Z) (mode : word) (lbf : Z) (tail : list byte).
Variables (buf s : list Z) (S lo : Z) (canary : word).
Hypothesis FD : fd = 1 \/ fd = 2.
Hypothesis LO : lo <= bv_unsigned sp - 112.
Hypothesis GLO : band_lo <= lo.
Hypothesis Fp0 : 0 <= Fp.
Hypothesis FPLO : Fp + 232 <= lo.
Hypothesis FSEP1 : Fp + 232 <= 0xe6b80 \/ 0xe6b80 + 8 <= Fp.
Hypothesis FSEP2 : Fp + 232 <= 0x642ea0 \/ 0x642ea0 + 8 <= Fp.
Hypothesis B0 : 0 <= B. Hypothesis BS0 : 0 <= bufsize. Hypothesis BUFLE : Z.of_nat (length buf) <= bufsize. Hypothesis BShi : B + bufsize <= 2^47.
Hypothesis LENS : Z.of_nat (length buf) + Z.of_nat (length s) <= 2^26.
Hypothesis S0 : 0 <= S < 2^64. Hypothesis Shi : S + Z.of_nat (length s) <= 2^47.
Hypothesis SEPS : s = [] \/ ((S + Z.of_nat (length s) <= lo \/ bv_unsigned sp <= S) /\ (S + Z.of_nat (length s) <= Fp + 32 \/ Fp + 64 <= S)).
Hypothesis SEPB : B + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= B.
Hypothesis SPHI : 0 <= bv_unsigned sp <= 2^47.
Hypothesis BUFB : bytes_at asegs m B (to_bytes buf).
Hypothesis SRC : bytes_at asegs m S (to_bytes s).

Local Notation W0 := ([(bv_unsigned sp - 112, bv_unsigned sp)] : list (Z * Z)).
Local Notation W := ([(bv_unsigned sp - 112, bv_unsigned sp); (Fp + 32, Fp + 64)] : list (Z * Z)).
Let POSTQ := stdio_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp flags B bufsize wfn fd mode lbf tail (Z.of_nat (length s)) lo canary m st.

Definition frame (mc : mem) (j8 : list byte) (p0 n0 p1 n1 : Z) : Prop :=
rw_cells asegs mc (bv_unsigned sp + -112)
[CB 8 j8; C8 (Z_to_bv 64 p0); C8 (Z_to_bv 64 n0); C8 (Z_to_bv 64 p1); C8 (Z_to_bv 64 n1); C8 canary;
C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma succ_tail : forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x6 t3 t4 t5 t6 : word) (mc : mem) j8 p0 n0 p1 n1,
frame mc j8 p0 n0 p1 n1 ->
rw_cells asegs mc Fp (file_cells flags wend (B + Z.of_nat (length buf)) B wfn B bufsize fd mode lbf tail) ->
rw_cells asegs mc 0xe6b80 [C8 (Z_to_bv 64 0x642ea0)] -> rw_cells asegs mc 0x642ea0 [C8 canary] ->
munch W0 m mc -> wmono asegs m mc -> mem_inv asegs mc -> stk asegs mc lo (bv_unsigned sp - 112) ->
evt asegs (POSTQ tt st)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 (Z.of_nat (length s))) (Z_to_bv 64 Fp)
a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 (Z_to_bv 64 0x642ea0) x6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd2a64) fc None mc (seg_rom asegs)).
Proof.
intros until n1. intros FR FC GOT GUARD MU0 WM MI ST. subst POSTQ.
assert (MU : munch W m mc).
{ eapply munch_weaken; [|exact MU0]. unfold sub_fp; cbn [outside]; intros; lia. }
clear MU0. unfold frame in FR. unfold file_cells in FC.
do 6 step. step. step. step. step. if_false.
do 10 step.
release_frame FR ST (bv_unsigned sp).
unfold stdio_write_post, file_cells, STDIO_WRITE_DEPTH. sys_finish.
+ split; [exact GOT| exact GUARD].
+ reflexivity.
Qed.

Definition iovsZ (two : bool) (i j : Z) : list (list Z) :=
if two then [skipn (Z.to_nat i) buf; skipn (Z.to_nat j) s] else [skipn (Z.to_nat j) s].
Definition remZ (two : bool) (i j : Z) : Z :=
(if two then Z.of_nat (length buf) - i else 0) + (Z.of_nat (length s) - j).

Lemma adv_move : forall i j cnt, 0 <= i <= Z.of_nat (length buf) -> 0 <= j -> Z.of_nat (length buf) - i < cnt ->
wv_advance (iovsZ true i j) cnt = iovsZ false i (j + (cnt - (Z.of_nat (length buf) - i))).
Proof.
intros i j cnt Hi Hj Hc. unfold iovsZ. rewrite wv_advance_move by (rewrite zlength_skipn by lia; unfold zlength; lia).
rewrite zlength_skipn by lia. unfold zlength. rewrite skipn_skipn'. f_equal. f_equal. lia.
Qed.
Lemma adv_stay2 : forall i j cnt, 0 <= i <= Z.of_nat (length buf) -> 0 <= cnt <= Z.of_nat (length buf) - i ->
wv_advance (iovsZ true i j) cnt = iovsZ true (i + cnt) j.
Proof.
intros i j cnt Hi Hc. unfold iovsZ. rewrite wv_advance_stay by (rewrite zlength_skipn by lia; unfold zlength; lia).
rewrite skipn_skipn'. f_equal. f_equal. lia.
Qed.
Lemma adv_stay1 : forall i j cnt, 0 <= j <= Z.of_nat (length s) -> 0 <= cnt <= Z.of_nat (length s) - j ->
wv_advance (iovsZ false i j) cnt = iovsZ false i (j + cnt).
Proof.
intros i j cnt Hj Hc. unfold iovsZ. rewrite wv_advance_stay by (rewrite zlength_skipn by lia; unfold zlength; lia).
rewrite skipn_skipn'. f_equal. f_equal. lia.
Qed.

Lemma src_at : forall mc k, munch W0 m mc -> (k <= length s)%nat ->
bytes_at asegs mc (S + Z.of_nat k) (to_bytes (skipn k s)).
Proof.
intros mc k MU Hk. destruct SEPS as [-> | [SEP1 SEP2]].
- rewrite skipn_nil. cbn [to_bytes map]. apply bytes_at_nil. cbn in Hk. lia.
- rewrite to_bytes_skipn. apply bytes_at_skipn; [| rewrite length_to_bytes; exact Hk].
apply (bytes_at_transport _ _ _ mc _ _ SRC MU). cbn [disjoint_from]. rewrite length_to_bytes. lia.
Qed.
Lemma buf_at : forall mc k, munch W0 m mc -> (k <= length buf)%nat ->
bytes_at asegs mc (B + Z.of_nat k) (to_bytes (skipn k buf)).
Proof.
intros mc k MU Hk.
rewrite to_bytes_skipn. apply bytes_at_skipn; [| rewrite length_to_bytes; exact Hk].
apply (bytes_at_transport _ _ _ mc _ _ BUFB MU). cbn [disjoint_from]. rewrite length_to_bytes. lia.
Qed.

Lemma src_iov : forall mc j, munch W0 m mc -> 0 <= j <= Z.of_nat (length s) ->
bytes_at asegs mc (bv_unsigned (Z_to_bv 64 (S + j))) (to_bytes (skipn (Z.to_nat j) s)).
Proof.
intros mc j MU Hj. destruct (Z.eq_dec (S + j) (2^64)) as [E|NE].
- rewrite skipn_all2 by lia. cbn [to_bytes map]. apply bytes_at_nil.
pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 (S + j))) as R. unfold bv_modulus in R. cbn in R. lia.
- rewrite unsigned_lit by lia. replace (S + j) with (S + Z.of_nat (Z.to_nat j)) by lia. apply src_at; [exact MU| lia].
Qed.
Lemma buf_iov : forall mc i, munch W0 m mc -> 0 <= i <= Z.of_nat (length buf) ->
bytes_at asegs mc (bv_unsigned (Z_to_bv 64 (B + i))) (to_bytes (skipn (Z.to_nat i) buf)).
Proof.
intros mc i MU Hi. rewrite unsigned_lit by lia. replace (B + i) with (B + Z.of_nat (Z.to_nat i)) by lia. apply buf_at; [exact MU| lia].
Qed.

Lemma wnode : forall ms1 (two : bool) i j p0 n0 p1 n1 j8,
ms_svc_pending ms1 = Some (Z_to_bv 64 66) -> ms_rom ms1 = seg_rom asegs ->
areg ms1 10 = Z_to_bv 64 fd -> areg ms1 12 = Z_to_bv 64 (if two then 2 else 1) ->
areg ms1 11 = Z_to_bv 64 (bv_unsigned sp + (if two then -104 else -88)) ->
frame (ms_mem ms1) j8 p0 n0 p1 n1 -> munch W0 m (ms_mem ms1) ->
(if two then p0 = B + i /\ n0 = Z.of_nat (length buf) - i else True) ->
p1 = S + j -> n1 = Z.of_nat (length s) - j ->
0 <= i <= Z.of_nat (length buf) -> 0 <= j <= Z.of_nat (length s) ->
at_node asegs (NWritev fd (map to_bytes (iovsZ two i j))) ms1.
Proof.
intros ms1 two i j p0 n0 p1 n1 j8 SVC ROM R10 R12 R11 FR MU TWO -> -> Hi Hj.
cbn [at_node]. rewrite SVC, ROM, R10, R11, R12. clear SVC ROM R10 R11 R12. unfold frame in FR.
destruct FR as [[WF FB] _]. cbn [cells_wf cell_wf] in WF. destruct WF as [L8 _]. cbn [cells_bytes cbytes] in FB.
apply bytes_at_app in FB as [_ FB]. rewrite L8 in FB.
apply bytes_at_app in FB as [FB1 FB]. rewrite length_le8 in FB.
apply bytes_at_app in FB as [FB2 FB]. rewrite length_le8 in FB.
apply bytes_at_app in FB as [FB3 FB]. rewrite length_le8 in FB.
apply bytes_at_app in FB as [FB4 _].
destruct two.
- destruct TWO as [-> ->]. unfold iovsZ. cbn [map length concat app].
split_spine; try reflexivity; try lia.
+ rewrite app_nil_r, length_app, !length_to_bytes, !length_skipn. unfold QJFf.writev_bytes_max. lia.
+ exists [(Z_to_bv 64 (B + i), Z_to_bv 64 (Z.of_nat (length buf) - i)); (Z_to_bv 64 (S + j), Z_to_bv 64 (Z.of_nat (length s) - j))]. split; [|split; [|split]].
3:{ rewrite unsigned_lit by lia. unfold TASK_SIZE. cbn [length]. lia. }
3:{ constructor; [|constructor; [|constructor]]; cbn [fst snd]; rewrite !unsigned_lit by lia; unfold TASK_SIZE; lia. }
* rewrite unsigned_lit by lia. cbn [iovec_bytes flat_map fst snd]. rewrite app_nil_r.
apply bytes_at_app. rewrite length_app, !length_le8. split.
-- apply bytes_at_app. rewrite length_le8. split.
++ match type of FB1 with bytes_at _ _ ?a _ => replace (bv_unsigned sp + -104) with a by lia end. exact FB1.
++ match type of FB2 with bytes_at _ _ ?a _ => replace (bv_unsigned sp + -104 + Z.of_nat 8) with a by lia end. exact FB2.
-- apply bytes_at_app. rewrite length_le8. split.
++ match type of FB3 with bytes_at _ _ ?a _ => replace (bv_unsigned sp + -104 + Z.of_nat (8 + 8)) with a by lia end. exact FB3.
++ match type of FB4 with bytes_at _ _ ?a _ => replace (bv_unsigned sp + -104 + Z.of_nat (8 + 8) + Z.of_nat 8) with a by lia end. exact FB4.
* constructor; [| constructor; [|constructor]].
-- split; [cbn [snd]; f_equal; rewrite length_to_bytes, length_skipn; lia|]. cbn [fst]. apply buf_iov; [exact MU| lia].
-- split; [cbn [snd]; f_equal; rewrite length_to_bytes, length_skipn; lia|]. cbn [fst]. apply src_iov; [exact MU| lia].
- unfold iovsZ. cbn [map length concat app].
split_spine; try reflexivity; try lia.
+ rewrite app_nil_r, !length_to_bytes, !length_skipn. unfold QJFf.writev_bytes_max. lia.
+ exists [(Z_to_bv 64 (S + j), Z_to_bv 64 (Z.of_nat (length s) - j))]. split; [|split; [|split]].
3:{ rewrite unsigned_lit by lia. unfold TASK_SIZE. cbn [length]. lia. }
3:{ constructor; [|constructor]; cbn [fst snd]; rewrite !unsigned_lit by lia; unfold TASK_SIZE; lia. }
* rewrite unsigned_lit by lia. cbn [iovec_bytes flat_map fst snd]. rewrite app_nil_r.
apply bytes_at_app. rewrite length_le8. split.
-- match type of FB3 with bytes_at _ _ ?a _ => replace (bv_unsigned sp + -88) with a by lia end. exact FB3.
-- match type of FB4 with bytes_at _ _ ?a _ => replace (bv_unsigned sp + -88 + Z.of_nat 8) with a by lia end. exact FB4.
* constructor; [| constructor].
split; [cbn [snd]; f_equal; rewrite length_to_bytes, length_skipn; lia|]. cbn [fst]. apply src_iov; [exact MU| lia].
Qed.

Ltac use_wnode FR MU :=
eapply wnode;
[ reflexivity | reflexivity
| at_node_red; reflexivity | at_node_red; reflexivity | at_node_red; reflexivity
| cbn [ms_mem MSsvc MS]; exact FR | cbn [ms_mem MSsvc MS]; exact MU
| first [exact I | split; lia] | lia | lia | lia | lia ].

Lemma retry_loop : forall (f : nat) (two : bool) (i j cnt : Z) (vs2 vs3 vs6 : Z)
(x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x20 t3 t4 t5 t6 : word) (mc : mem) j8 p0 n0 p1 n1,
(0 <= i <= Z.of_nat (length buf)) -> (0 <= j <= Z.of_nat (length s)) ->
(1 <= cnt < remZ two i j) ->
(if two then p0 = B + i /\ n0 = Z.of_nat (length buf) - i else True) ->
p1 = S + j -> n1 = Z.of_nat (length s) - j ->
vs2 = (if two then 2 else 1) -> vs3 = bv_unsigned sp + (if two then -104 else -88) -> vs6 = remZ two i j ->
frame mc j8 p0 n0 p1 n1 ->
rw_cells asegs mc Fp (file_cells flags wend (B + Z.of_nat (length buf)) B wfn B bufsize fd mode lbf tail) ->
rw_cells asegs mc 0xe6b80 [C8 (Z_to_bv 64 0x642ea0)] -> rw_cells asegs mc 0x642ea0 [C8 canary] ->
munch W0 m mc -> wmono asegs m mc -> mem_inv asegs mc -> stk asegs mc lo (bv_unsigned sp - 112) ->
implM asegs (mloop f (wv_body (St:=St) fd) (wv_advance (iovsZ two i j) cnt, remZ two i j - cnt)) st POSTQ
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 (Z.of_nat (length s))) (Z_to_bv 64 Fp)
(Z_to_bv 64 cnt) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 vs2) (Z_to_bv 64 vs3) x20 (Z_to_bv 64 0x642ea0) (Z_to_bv 64 vs6) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd2af0) fc None mc (seg_rom asegs)).
Proof.
induction f as [|f IH]; intros until n1; intros Hi Hj Hcnt TWO P1 N1 E2 E3 E6 FR FC GOT GUARD MU WM MI ST.
{ cbn [mloop]. apply implM_unr. }
unfold frame in FR. unfold file_cells in FC.
destruct two.
- destruct TWO as [P0 N0]. change (vs2 = 2) in E2. change (vs3 = bv_unsigned sp + -104) in E3. subst vs2 vs3.
destruct (Z_lt_le_dec n0 cnt) as [LT|GE].
+
rewrite adv_move by lia.
replace (remZ true i j - cnt) with (remZ false i (j + (cnt - (Z.of_nat (length buf) - i)))) by (unfold remZ; lia).
unfold remZ in Hcnt, E6.
apply implM_loop_S. unfold wv_body at 1. cbn [fst snd]. apply implM_sys_k.
step. if_cases K0; zify_cond K0. { exfalso. lia. }
step. step.
replace (v_sltu (Z_to_bv 64 n0) (Z_to_bv 64 cnt)) with (Z_to_bv 64 1)
by (unfold v_sltu, c_ltu, bv_ltu; rewrite !unsigned_lit by lia; destruct (Z.ltb_spec0 n0 cnt); [reflexivity|lia]).
zstep. zstep. zstep. zstep. zstep. rewrite ?land_ones64_l by lia. zstep. zstep. zstep.
zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
zstep. zstep. zstep.
replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd) by (symmetry; apply sx32_lit; lia).
step_ecall. split.
{ use_wnode FR MU. }
intros rsp a Hdec. apply dec_writev_Some in Hdec. destruct Hdec as (-> & Hk & Ha). unfold remZ in Hk.

eapply implM_evt; [| intros ms' HP; exact HP]. unfold eff0. sys_nret. sysret_fast. step. step. apply evt_done.
destruct (Z.eq_dec a (remZ false i (j + (cnt - (Z.of_nat (length buf) - i))))) as [Heq|Hne].
* replace (a =? remZ false i (j + (cnt - (Z.of_nat (length buf) - i)))) with true by (symmetry; apply Z.eqb_eq; exact Heq). unfold remZ in Heq. apply implM_ret. cbv beta iota. apply evt_evt.
if_cases Hb; zify_cond Hb. 2:{ exfalso. lia. }
eapply succ_tail; [exact FR | exact FC | exact GOT | exact GUARD | exact MU | exact WM | exact MI | exact ST].
* replace (a =? _) with false by (symmetry; apply Z.eqb_neq; exact Hne). unfold remZ in Hne.
apply implM_ret. cbv beta iota.
if_cases Hb; zify_cond Hb. { exfalso. lia. }
apply evt_done. eapply IH; try eassumption; try reflexivity; unfold remZ; first [lia | exact I | split; lia].
+
rewrite adv_stay2 by lia.
replace (remZ true i j - cnt) with (remZ true (i + cnt) j) by (unfold remZ; lia).
unfold remZ in Hcnt, E6.
apply implM_loop_S. unfold wv_body at 1. cbn [fst snd]. apply implM_sys_k.
step. if_cases K0; zify_cond K0. { exfalso. lia. }
step. step.
replace (v_sltu (Z_to_bv 64 n0) (Z_to_bv 64 cnt)) with (Z_to_bv 64 0)
by (unfold v_sltu, c_ltu, bv_ltu; rewrite !unsigned_lit by lia; destruct (Z.ltb_spec0 n0 cnt); [lia|reflexivity]).
zstep. zstep. zstep. zstep. zstep. rewrite ?land_0_l'. zstep. zstep. zstep.
zstep. if_cases K1; zify_cond K1. 2:{ exfalso. lia. }
zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
zstep. zstep.
replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd) by (symmetry; apply sx32_lit; lia).
step_ecall. split.
{ use_wnode FR MU. }
intros rsp a Hdec. apply dec_writev_Some in Hdec. destruct Hdec as (-> & Hk & Ha). unfold remZ in Hk.

eapply implM_evt; [| intros ms' HP; exact HP]. unfold eff0. sys_nret. sysret_fast. step. step. apply evt_done.
destruct (Z.eq_dec a (remZ true (i + cnt) j)) as [Heq|Hne].
* replace (a =? remZ true (i + cnt) j) with true by (symmetry; apply Z.eqb_eq; exact Heq). unfold remZ in Heq. apply implM_ret. cbv beta iota. apply evt_evt.
if_cases Hb; zify_cond Hb. 2:{ exfalso. lia. }
eapply succ_tail; [exact FR | exact FC | exact GOT | exact GUARD | exact MU | exact WM | exact MI | exact ST].
* replace (a =? _) with false by (symmetry; apply Z.eqb_neq; exact Hne). unfold remZ in Hne.
apply implM_ret. cbv beta iota.
if_cases Hb; zify_cond Hb. { exfalso. lia. }
apply evt_done. eapply IH; try eassumption; try reflexivity; unfold remZ; first [lia | exact I | split; lia].
-
change (vs2 = 1) in E2. change (vs3 = bv_unsigned sp + -88) in E3. subst vs2 vs3.
rewrite adv_stay1 by (unfold remZ in Hcnt; lia).
replace (remZ false i j - cnt) with (remZ false i (j + cnt)) by (unfold remZ; lia).
unfold remZ in Hcnt, E6.
apply implM_loop_S. unfold wv_body at 1. cbn [fst snd]. apply implM_sys_k.
step. if_cases K0; zify_cond K0. { exfalso. lia. }
step. step.
replace (v_sltu (Z_to_bv 64 n1) (Z_to_bv 64 cnt)) with (Z_to_bv 64 0)
by (unfold v_sltu, c_ltu, bv_ltu; rewrite !unsigned_lit by lia; destruct (Z.ltb_spec0 n1 cnt); [lia|reflexivity]).
zstep. zstep. zstep. zstep. zstep. rewrite ?land_0_l'. zstep. zstep. zstep.
zstep. if_cases K1; zify_cond K1. 2:{ exfalso. lia. }
zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
zstep. zstep.
replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd) by (symmetry; apply sx32_lit; lia).
step_ecall. split.
{ use_wnode FR MU. }
intros rsp a Hdec. apply dec_writev_Some in Hdec. destruct Hdec as (-> & Hk & Ha). unfold remZ in Hk.

eapply implM_evt; [| intros ms' HP; exact HP]. unfold eff0. sys_nret. sysret_fast. step. step. apply evt_done.
destruct (Z.eq_dec a (remZ false i (j + cnt))) as [Heq|Hne].
* replace (a =? remZ false i (j + cnt)) with true by (symmetry; apply Z.eqb_eq; exact Heq). unfold remZ in Heq. apply implM_ret. cbv beta iota. apply evt_evt.
if_cases Hb; zify_cond Hb. 2:{ exfalso. lia. }
eapply succ_tail; [exact FR | exact FC | exact GOT | exact GUARD | exact MU | exact WM | exact MI | exact ST].
* replace (a =? _) with false by (symmetry; apply Z.eqb_neq; exact Hne). unfold remZ in Hne.
apply implM_ret. cbv beta iota.
if_cases Hb; zify_cond Hb. { exfalso. lia. }
apply evt_done. eapply IH; try eassumption; try reflexivity; unfold remZ; first [lia | exact I | split; lia].
Qed.

End Fixed.

Ltac wnode_side FR MU :=
lazymatch goal with
| |- areg _ _ = _ => at_node_red; reflexivity
| |- ms_svc_pending _ = _ => reflexivity
| |- ms_rom _ = _ => reflexivity
| |- True => exact I
| |- context [ms_mem _] => cbn [ms_mem MSsvc MS]; first [exact FR | exact MU]
| |- _ => first [eassumption | cbn [length]; lia | split; cbn [length]; lia]
end.

Lemma stdio_write_spec :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
(Fp : Z) (flags : word) (wend B bufsize wfn fd : Z) (mode : word) (lbf : Z) (tail : list byte)
(buf s : list Z) (S lo : Z) (canary : word),
rw_cells asegs m Fp (file_cells flags wend (B + zlength buf) B wfn B bufsize fd mode lbf tail) ->
bytes_at asegs m B (to_bytes buf) ->
bytes_at asegs m S (to_bytes s) ->
a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlength s) ->
(fd = 1 \/ fd = 2) ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - STDIO_WRITE_DEPTH) -> (band_lo <= lo) ->
ssp_cells m canary -> mem_inv asegs m ->
(0 <= Fp) -> (Fp + 232 <= lo) ->
(Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
(0 <= B) -> (0 <= bufsize) -> (zlength buf <= bufsize) -> (B + bufsize <= 2^47) ->
(zlength buf + zlength s <= 2^26) -> (0 <= S < 2^64) -> (S + zlength s <= 2^47) ->
(s = [] \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= Fp + 32 \/ Fp + 64 <= S))) ->
(B + zlength buf <= lo \/ bv_unsigned sp <= B) ->
bv_unsigned sp <= 2^47 ->
implM asegs (stdio_writev (St:=St) fd buf s) st
(stdio_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp flags B bufsize wfn fd mode lbf tail
(zlength s) lo canary m st)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd29d0) fc None m (seg_rom asegs)).
Proof.
intros until canary. intros FC BUFB SRC -> -> -> FD ST LO GLO SSP MI Fp0 FPLO FSEP1 FSEP2 B0 BS0 BUFLE BShi LENS S0 Shi SEPS SEPB SPT.
assert (SPHI : 0 <= bv_unsigned sp <= 2^47) by (pose proof (bv_unsigned_in_range 64 sp) as X; unfold bv_modulus in X; cbn in X; lia).
destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard, STDIO_WRITE_DEPTH in *.
unfold zlength in *.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
unfold file_cells in FC.
change (bytes_at asegs m S (to_bytes s)) with (boxed (bytes_at asegs m S (to_bytes s))) in SRC.
change (bytes_at asegs m B (to_bytes buf)) with (boxed (bytes_at asegs m B (to_bytes buf))) in BUFB.

eapply implM_evt; [| intros ms' HP; exact HP].
carve_frame 112%nat ST.
do 12 step. do 13 step.
rewrite !unsigned_lit by lia. rewrite !unsigned_lit in FR by lia.
apply evt_done.
destruct buf as [|b0 buf'].
-
unfold stdio_writev. unfold zlength. change [s] with (iovsZ [] s false 0 0).
replace (Z.of_nat (@length Z []) + Z.of_nat (length s)) with (remZ [] s false 0 0) by (unfold remZ; cbn [length]; lia).
apply implM_loop_S. unfold wv_body at 1. cbn [fst snd]. apply implM_sys_k.
change (Z.of_nat (@length Z [])) with 0. rewrite !Z.add_0_r. rewrite Z.lxor_nilpotent.
change (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 0)) with (Z_to_bv 64 0).
step. if_true. do 6 step.
replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd) by (symmetry; apply sx32_lit; lia).
replace (B - B + Z.of_nat (length s)) with (Z.of_nat (length s)) by lia.
step_ecall. split.
{ eapply (wnode ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st Fp flags B bufsize wfn fd mode lbf tail _ _ S lo canary).
all: unfold boxed in *; wnode_side FR MU. }
intros rsp a Hdec. apply dec_writev_Some in Hdec. destruct Hdec as (-> & Hk & Ha). unfold remZ in Hk. cbn [length] in Hk.

eapply implM_evt; [| intros ms' HP; exact HP]. unfold eff0. sys_nret. sysret_fast. step. apply evt_done.
destruct (Z.eq_dec a (remZ [] s false 0 0)) as [Heq|Hne].
+ replace (a =? remZ [] s false 0 0) with true by (symmetry; apply Z.eqb_eq; exact Heq). unfold remZ in Heq. cbn [length] in Heq.
apply implM_ret. cbv beta iota. apply evt_evt.
if_cases Hb; zify_cond Hb. { exfalso. lia. }
eapply succ_tail; try eassumption; cbn [length]; rewrite ?Z.add_0_r; first [lia | exact FC].
+ replace (a =? _) with false by (symmetry; apply Z.eqb_neq; exact Hne). unfold remZ in Hne. cbn [length] in Hne.
apply implM_ret. cbv beta iota.
if_cases Hb; zify_cond Hb. 2:{ exfalso. lia. }
apply evt_done. unfold boxed in *.
eapply (retry_loop ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st Fp flags wend B bufsize wfn fd mode lbf tail _ _ S lo canary).
all: try exact FR.
all: first [eassumption | exact I | reflexivity | cbn [length]; unfold remZ; cbn [length]; lia].
-
unfold stdio_writev. unfold zlength. change [b0 :: buf'; s] with (iovsZ (b0 :: buf') s true 0 0).
replace (Z.of_nat (length (b0 :: buf')) + Z.of_nat (length s)) with (remZ (b0 :: buf') s true 0 0) by (unfold remZ; lia).
set (nb := Z.of_nat (length (b0 :: buf'))) in *.
assert (NB1 : 1 <= nb) by (subst nb; cbn [length]; lia).
apply implM_loop_S. unfold wv_body at 1. cbn [fst snd]. apply implM_sys_k.
replace (Z.lxor (B + nb) B) with (Z.lxor (B + nb) (B + 0)) by (rewrite Z.add_0_r; reflexivity).
assert (XNZ : Z.lxor (B + nb) (B + 0) <> 0).
{ intros E. apply Z.lxor_eq in E. lia. }
replace (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.lxor (B + nb) (B + 0)))) with (Z_to_bv 64 1).
2:{ pose proof (Z_lxor_range (B + nb) (B + 0) ltac:(lia) ltac:(lia)) as XR.
unfold v_sltu, c_ltu, bv_ltu. rewrite !unsigned_lit by lia.
destruct (Z.ltb_spec0 0 (Z.lxor (B + nb) (B + 0))); [reflexivity| exfalso; lia]. }
step. if_cases Hb0; zify_cond Hb0. 1:{ exfalso. lia. } do 7 step.
replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd) by (symmetry; apply sx32_lit; lia).
replace (B + nb - B + Z.of_nat (length s)) with (nb + Z.of_nat (length s)) by lia.
step_ecall. split.
{ eapply (wnode ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st Fp flags B bufsize wfn fd mode lbf tail _ _ S lo canary).
all: unfold boxed in *; subst nb; wnode_side FR MU. }
intros rsp a Hdec. apply dec_writev_Some in Hdec. destruct Hdec as (-> & Hk & Ha). unfold remZ in Hk.

eapply implM_evt; [| intros ms' HP; exact HP]. unfold eff0. sys_nret. sysret_fast. step. apply evt_done.
destruct (Z.eq_dec a (remZ (b0 :: buf') s true 0 0)) as [Heq|Hne].
+ replace (a =? remZ (b0 :: buf') s true 0 0) with true by (symmetry; apply Z.eqb_eq; exact Heq). unfold remZ in Heq.
apply implM_ret. cbv beta iota. apply evt_evt.
if_cases Hb; zify_cond Hb. { exfalso. lia. }
eapply succ_tail; try eassumption; subst nb; first [lia | exact FC].
+ replace (a =? _) with false by (symmetry; apply Z.eqb_neq; exact Hne). unfold remZ in Hne.
apply implM_ret. cbv beta iota.
if_cases Hb; zify_cond Hb. 2:{ exfalso. lia. }
apply evt_done. unfold boxed in *.
eapply (retry_loop ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st Fp flags wend B bufsize wfn fd mode lbf tail _ _ S lo canary).
all: try exact FR.
all: first [eassumption | exact I | reflexivity | subst nb; unfold remZ; lia | split; subst nb; lia].
Qed.
End StdioWrite.
End Mq2.
From Stdlib Require String Ascii.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0z1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String Stdlib.Strings.Ascii.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do Qc6I QJFf QVsB QJFf.Mq0.
Import QCiC.Mq1 Qpj5.Mq1 QdZp Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5.
Import Q9Ho.Mq0.
Import QteI.Mq1.
Import Q0z1.
Import QlES.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_1 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_2 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Ltac addr_diff E A ::=
let k :=
lazymatch E with
| Z.add ?X ?c1 =>
lazymatch A with
| Z.add X ?c2 => let c1 := zlit c1 in let c2 := zlit c2 in eval vm_compute in (c1 - c2)%Z
| X => zlit c1
| _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
end
| _ =>
lazymatch A with
| Z.add E ?c2 => let c2 := zlit c2 in eval vm_compute in (- c2)%Z
| E => constr:(0%Z)
| _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
end
end in
let ok := eval vm_compute in (Z.ltb k 65536) in
lazymatch ok with true => k end. Ltac mkr__addr_diff_3 E A := let k :=
lazymatch E with
| Z.add ?X ?c1 =>
lazymatch A with
| Z.add X ?c2 => let c1 := zlit c1 in let c2 := zlit c2 in eval vm_compute in (c1 - c2)%Z
| X => zlit c1
| _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
end
| _ =>
lazymatch A with
| Z.add E ?c2 => let c2 := zlit c2 in eval vm_compute in (- c2)%Z
| E => constr:(0%Z)
| _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
end
end in
let ok := eval vm_compute in (Z.ltb k 65536) in
lazymatch ok with true => k end.

Ltac has_var c := match c with context [?x] => is_var x end.
Ltac bif := try (lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
tryif has_var c then idtac else
(let v := eval vm_compute in c in
lazymatch v with
| true => replace c with true by (vm_compute; reflexivity); cbv iota
| false => replace c with false by (vm_compute; reflexivity); cbv iota
end) end).

Ltac subfix := repeat match goal with |- context [Z_to_bv 64 (?x - ?k)] => is_Zlit k; let nk := eval vm_compute in (- k)%Z in replace (x - k)%Z with (x + nk)%Z by lia end.
Lemma zx8_lit : forall e, 0 <= e < 2^64 -> zx8 (Z_to_bv 64 e) = Z_to_bv 64 (e mod 256).
Proof. intros e He. unfold zx8. rewrite unsigned_lit by lia. reflexivity. Qed.

Ltac bnorm :=
repeat match goal with
| |- context [zx8 (Z_to_bv 64 ?e)] => is_Zlit e; rewrite (zx8_lit e) by lia;
let v := eval vm_compute in (e mod 256)%Z in change (e mod 256)%Z with v
| |- context [bv_unsigned (Z_to_bv 64 ?e)] => is_Zlit e;
let v := eval vm_compute in (bv_unsigned (Z_to_bv 64 e)) in change (bv_unsigned (Z_to_bv 64 e)) with v
end.
Ltac bstep := istep; subfix; bnorm; bif.

Ltac run_to pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => bstep end).

Definition pcommon_entry : Z := 0x533cc.
Definition PCOMMON_STACK : Z := 2320.

Definition S_diouxXn : Z := 0x1d915.  Definition S_float : Z := 0x16c7d.  Definition S_flags : Z := 0x15b57.
Definition S_lenmod : Z := 0x1c640.   Definition S_cCsS : Z := 0x146d7.   Definition S_CS : Z := 0x1abb9.
Definition S_csb : Z := 0x1086e.      Definition S_sS : Z := 0x13f97.     Definition K_aa : Z := 0x10460.

Lemma lor_range64 : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> 0 <= Z.lor a b < 2^64.
Proof.
intros a b Ha Hb. pose proof (Z.lor_nonneg a b).
destruct (Z.eq_dec (Z.lor a b) 0) as [E|NE]; [lia|].
split; [lia|]. apply (proj2 (Z.log2_lt_pow2 (Z.lor a b) 64 ltac:(lia))).
rewrite Z.log2_lor by lia. apply Z.max_lub_lt.
- destruct (Z.eq_dec a 0) as [->|Na]; [cbn; lia|]. apply (proj1 (Z.log2_lt_pow2 a 64 ltac:(lia))). lia.
- destruct (Z.eq_dec b 0) as [->|Nb]; [cbn; lia|]. apply (proj1 (Z.log2_lt_pow2 b 64 ltac:(lia))). lia.
Qed.
Lemma lor40_and15 : forall x, Z.land (Z.lor 40 x) 15 <> 0.
Proof.
intros x E. apply (f_equal (fun z => Z.testbit z 3)) in E.
rewrite Z.land_spec, Z.lor_spec, Z.bits_0 in E. cbn in E. discriminate.
Qed.

Definition imemset_bpost (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (d n cur : Z) (k : nat) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz d) (wz 0) (wz (d + n)) (wz (d + n)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(cur, d + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' cur [CB k (repeat (b8 0) k)].

Lemma imemset_bloop : forall (k : nat) ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (d n cur : Z) (rest : list byte),
rw_cells asegs m cur [CB k rest] -> mem_inv asegs m ->
cur + Z.of_nat k = d + n -> (0 < k)%nat -> 0 <= d -> d <= cur -> d + n < 2^64 ->
evt asegs (imemset_bpost ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc d n cur k m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz d) (wz 0) (wz (d + n)) (wz cur) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x74f88) fc None m (seg_rom asegs)).
Proof.
induction k as [|k IH]; intros until rest; intros DST MI HK K0 D0 DC DN; [lia|].
assert (LR : length rest = S k) by (destruct DST as [[WF _] _]; cbn in WF; exact (proj1 WF)).
pose proof (munch_refl [(cur, d + n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
apply (rw_cells_split_CB asegs _ _ [] (S k) rest [] [1%nat; k]) in DST; [| cbn; lia]. cbn [mk_CB_cells app] in DST.
step. change (bv_unsigned (wz 0)) with 0 in DST.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in DST. destruct DST as [B0 DST]. cbn [cells_size csize Nat.add Z.of_nat] in DST.
step. step.
destruct k as [|k'].
-
ifF. step. step.
apply evt_done. unfold imemset_bpost. exists m0.
replace (cur + 1) with (d + n) by lia.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
eapply rw_cells_recast'; [exact B0| cbn; split; [reflexivity| exact I]| reflexivity].
- ifT. replace (Z.pos (Pos.of_succ_nat 0)) with 1 in DST by reflexivity.
replace (Z.pos (Pos.of_succ_nat 0)) with 1 in DST by reflexivity.
eapply evt_mono; [eapply (IH ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 d n (cur + 1)); [exact DST| exact MI| lia| lia| lia| lia| lia] |].
cbv beta. intros ms' (m' & -> & MU2 & WM2 & MI2 & Z2). unfold imemset_bpost. exists m'.
split; [reflexivity|].
split. { apply (munch_trans _ m m0 m'); [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn; intros; lia. }
split; [eapply wmono_trans; [exact WM| exact WM2]|]. split; [exact MI2|].
assert (B0' : rw_cells asegs m' cur [C1 (b8 0)]).
{ eapply rw_cells_apart; [exact B0| exact MU2| exact WM2|]. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
pose proof (proj2 (rw_cells_app asegs m' cur [C1 (b8 0)] [CB (S k') (repeat (b8 0) (S k'))]) (conj B0' Z2)) as J.
eapply rw_cells_recast'; [exact J| cbn; split; [| exact I]; cbn; rewrite repeat_length; reflexivity| reflexivity].
Qed.

Definition imemset40_post (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (d : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz d) (wz 0) (wz (d + 40)) (wz (d + 40)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(d, d + 40)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' d [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)].

Lemma imemset40_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (d : Z) (cs : list cell),
rw_cells asegs m d cs -> cells_size cs = 40%nat -> mem_inv asegs m -> d + 40 < 2^64 ->
evt asegs (imemset40_post ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc d m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz d) (wz 0) (wz 40) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x74f70) fc None m (seg_rom asegs)).
Proof.
intros until cs; intros DST SZ MI DN.
pose proof (rw_cells_bound _ _ _ _ DST) as BD. rewrite SZ in BD. cbn in BD.
pose proof (rw_cells_merge asegs m d [] cs [] ltac:(cbn [app]; rewrite app_nil_r; exact DST)) as D40.
cbn [app] in D40. rewrite SZ in D40.
assert (L15 : 0 < Z.land (Z.lor 40 d) 15 < 16).
{ pose proof (lor40_and15 d). split; [pose proof (Z.land_nonneg (Z.lor 40 d) 15); lia|].
change 16 with (2^4). replace 15 with (Z.ones 4) by reflexivity. rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
step. step. rewrite ?(unsigned_lit d) by lia. rewrite (unsigned_lit (Z.lor 40 d)) by (apply lor_range64; lia).
step. ifz. step. ifz. step. step.
eapply evt_mono; [eapply (imemset_bloop 40 ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d 40 d); [exact D40| exact MI| lia| lia| lia| lia| lia] |].
cbv beta. intros ms' (m' & -> & MU & WM & MI' & Z40). unfold imemset40_post. exists m'.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
eapply rw_cells_recast'; [exact Z40| cbn; repeat split; exact I| reflexivity].
Qed.

Lemma zb_length : forall l, length (zb l) = length l.
Proof. intros. unfold zb. apply length_map. Qed.
Lemma zb_nth : forall (s : list Z) (t : list byte) i, 0 <= i < zlength s ->
firstn 1 (skipn (Z.to_nat i) (zb s ++ t)) = [b8 (nth (Z.to_nat i) s 0)].
Proof.
intros s t i Hi. unfold zlength in Hi. rewrite skipn_app. unfold zb. rewrite skipn_map.
replace (Z.to_nat i - length (map (λ z : Z, b8 z) s))%nat with 0%nat by (rewrite length_map; lia). cbn [skipn].
destruct (skipn (Z.to_nat i) s) as [|c rest] eqn:E.
- exfalso. apply (f_equal (@length Z)) in E. rewrite length_skipn in E. cbn in E. lia.
- cbn. f_equal. f_equal. rewrite <- (Nat.add_0_r (Z.to_nat i)), <- (nth_skipn _ s 0 0%Z), E. reflexivity.
Qed.
Lemma zb_end : forall (s : list Z) (b : byte) (t : list byte), firstn 1 (skipn (Z.to_nat (zlength s)) (zb s ++ b :: t)) = [b].
Proof.
intros s b t. unfold zlength. rewrite Nat2Z.id, skipn_app. unfold zb. rewrite skipn_all2 by (rewrite length_map; lia).
rewrite length_map, Nat.sub_diag. reflexivity.
Qed.

Section IStrlen.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Variables (p : Z) (s : list Z) (t : list byte).
Hypothesis SRC : bytes_at asegs m p (zb s ++ b8 0 :: t).
Hypothesis BYT : Forall (fun c => 0 < c < 256) s.

Definition istrlen_post : machine_state -> Prop :=
eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (zlength s)) (wz (zlength s + 1)) (wz 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs)).

Lemma istrlen_loop : forall (n : nat) (i : Z) (a2 : word), Z.of_nat n = zlength s - i -> 0 <= i <= zlength s ->
evt asegs istrlen_post
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz p) (wz i) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x750c8) fc None m (seg_rom asegs)).
Proof.
induction n as [|n IH]; intros i a2 Hn Hi.
-
assert (RD : ov_read_bytes asegs m (wa (p + i)) 1 = Some [b8 0]).
{ rewrite (bytes_at_read asegs m p _ i 1 SRC) by (rewrite ?length_app, ?zb_length; cbn; unfold zlength in *; lia).
replace i with (zlength s) by lia. rewrite zb_end. reflexivity. }
pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite length_app, zb_length in BS. cbn [length] in BS. unfold zlength in *.
step. replace (wz (p + i) : word) with (wa (p + i)) by reflexivity. step. clear RD.
change (zxb (b8 0)) with (wz 0). step. step. bif. step. step.
apply evt_done. unfold istrlen_post, zlength. replace i with (Z.of_nat (length s)) by lia. reflexivity.
- pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite length_app, zb_length in BS. cbn [length] in BS.
assert (CR : 0 < nth (Z.to_nat i) s 0 < 256).
{ apply (proj1 (List.Forall_forall _ _) BYT). apply nth_In. unfold zlength in *; lia. }
assert (RD : ov_read_bytes asegs m (wa (p + i)) 1 = Some [b8 (nth (Z.to_nat i) s 0)]).
{ rewrite (bytes_at_read asegs m p _ i 1 SRC) by (rewrite ?length_app, ?zb_length; cbn; unfold zlength in *; lia).
rewrite zb_nth by lia. reflexivity. }
unfold zlength in *.
step. replace (wz (p + i) : word) with (wa (p + i)) by reflexivity. step. clear RD.
rewrite zxb_b8, Z.mod_small by lia.
step. step. ifT. apply (IH (i + 1)); lia.
Qed.

Lemma istrlen_spec : forall (a1 a2 : word),
evt asegs istrlen_post
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x750c4) fc None m (seg_rom asegs)).
Proof.
intros a1 a2. step. apply (istrlen_loop (Z.to_nat (zlength s)) 0); unfold zlength; lia.
Qed.
End IStrlen.

Fixpoint strchr_res (q : Z) (l : list Z) (c : Z) : Z :=
match l with [] => 0 | z :: l' => if z =? c then q else strchr_res (q + 1) l' c end.

Section IStrchr.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : Z).
Hypothesis CR : 0 < c < 256.

Definition istrchr_post (r : Z) : machine_state -> Prop :=
fun ms' => exists a1' a3' : word,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz r) a1' (wz c) a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs).

Lemma istrchr_loop : forall (l : list Z) (q : Z) (t : list byte) (a1 : word),
bytes_at asegs m q (zb l ++ b8 0 :: t) -> Forall (fun z => 0 < z < 256) l -> hd 0 l <> c ->
evt asegs (istrchr_post (strchr_res q l c))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz q) a1 (wz c) (wz (hd 0 l)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x75034) fc None m (seg_rom asegs)).
Proof.
induction l as [|z l IH]; intros q t a1 STR BYT NE.
- cbn [hd strchr_res]. step. ifT. step. step. apply evt_done. unfold istrchr_post. do 2 eexists. reflexivity.
- cbn [hd] in NE |- *. apply Forall_cons_iff in BYT. destruct BYT as [Bz BYT].
pose proof (bytes_at_bound _ _ _ _ STR) as BS. rewrite length_app, zb_length in BS. cbn [length] in BS.
cbn [strchr_res]. replace (z =? c) with false by (symmetry; apply Z.eqb_neq; exact NE).
step. ifF.
assert (RD : ov_read_bytes asegs m (wa (q + 1)) 1 = Some [b8 (hd 0 l)]).
{ rewrite (bytes_at_read asegs m q _ 1 1 STR) by (rewrite ?length_app, ?zb_length; cbn; lia).
destruct l as [|z' l']; reflexivity. }
assert (CR' : 0 <= hd 0 l < 256).
{ destruct l as [|z' l']; cbn; [lia|]. apply Forall_cons_iff in BYT. lia. }
step. clear RD. rewrite zxb_b8, Z.mod_small by lia. step. step. step.
destruct (Z.eq_dec (hd 0 l) c) as [E|NE'].
+ ifF. step. step. apply evt_done. unfold istrchr_post.
destruct l as [|z' l']; cbn [hd] in E; [lia|]. cbn [strchr_res]. rewrite (proj2 (Z.eqb_eq _ _) E). do 2 eexists. reflexivity.
+ ifT. apply (IH (q + 1) t); [| exact BYT| exact NE'].
pose proof STR as STR'. change (zb (z :: l) ++ b8 0 :: t) with ([b8 z] ++ (zb l ++ b8 0 :: t)) in STR'.
apply bytes_at_app in STR'. destruct STR' as [_ S2]. cbn [length Z.of_nat Pos.of_succ_nat] in S2. exact S2.
Qed.

Lemma istrchr_spec : forall (l : list Z) (q : Z) (t : list byte) (a1 a2 a3 : word),
bytes_at asegs m q (zb l ++ b8 0 :: t) -> Forall (fun z => 0 < z < 256) l -> a1 = wz c ->
evt asegs (istrchr_post (strchr_res q l c))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz q) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x75024) fc None m (seg_rom asegs)).
Proof.
intros l q t a1 a2 a3 STR BYT ->.
pose proof (bytes_at_bound _ _ _ _ STR) as BS. rewrite length_app, zb_length in BS. cbn [length] in BS.
assert (RD : ov_read_bytes asegs m (wa (q + 0)) 1 = Some [b8 (hd 0 l)]).
{ rewrite (bytes_at_read asegs m q _ 0 1 STR) by (rewrite ?length_app, ?zb_length; cbn; lia). destruct l; reflexivity. }
assert (CR' : 0 <= hd 0 l < 256).
{ destruct l as [|z' l']; cbn; [lia|]. apply Forall_cons_iff in BYT. lia. }
step. clear RD. rewrite zxb_b8, Z.mod_small by lia.
step. rewrite (unsigned_lit c) by lia. change (Z.land c 255) with (Z.land c (Z.ones 8)). rewrite Z.land_ones, Z.mod_small by lia.
step. destruct (Z.eq_dec (hd 0 l) c) as [E|NE].
- ifF. step. apply evt_done. unfold istrchr_post.
destruct l as [|z' l']; cbn [hd] in E; [lia|]. cbn [strchr_res]. rewrite (proj2 (Z.eqb_eq _ _) E). do 2 eexists. reflexivity.
- ifT. apply (istrchr_loop l q t); assumption.
Qed.
End IStrchr.

Definition boxed (P : Prop) : Prop := P.

Lemma rwc_eq : forall m A A' cs, rw_cells asegs m A cs -> A = A' -> rw_cells asegs m A' cs.
Proof. intros m A A' cs H <-. exact H. Qed.

Lemma ash_szone_words {BAND : Band} : forall m p n, ash m -> szone p n -> 0 < n ->
ro_cells asegs m (8 * (SH p / 8)) [C8 (wz 0)] /\ ro_cells asegs m (8 * (SH (p + n - 1) / 8)) [C8 (wz 0)].
Proof.
intros m p n (Z1 & Z2 & Z3) SZ N0.  unfold szone in SZ.
destruct SZ as [(A1 & A2)|[(B1 & B2)|(D1 & D2)]].
- split; (eapply (zrd_ro8 _ _ _ _ Z1); rewrite SH_eq; Z.div_mod_to_equations; lia).
- split; (eapply (zrd_ro8 _ _ _ _ Z2); rewrite !SH_eq; unfold KHI in *; Z.div_mod_to_equations; lia).
- split; (eapply (zrd_ro8 _ _ _ _ Z3); rewrite SH_eq; Z.div_mod_to_equations; lia).
Qed.

Lemma ro_str : forall m A (l : list Z), mem_inv asegs m -> ro_bytes_b asegs A (map b8 l) = true ->
0 <= A -> A + Z.of_nat (length l) <= 2^64 -> ro_cells asegs m A (map (fun z => C1 (b8 z)) l).
Proof.
intros m A l MI RB H0 HL.
pose proof (ro_cells_image asegs m A (map b8 l) MI RB H0 ltac:(rewrite length_map; exact HL)) as R.
eapply ro_cells_recast'; [exact R| |].
- clear. induction l as [|z l IH]; cbn; [exact I|]. split; [exact I| exact IH].
- cbn [cells_bytes cbytes]. rewrite app_nil_r. clear. induction l as [|z l IH]; cbn; [reflexivity|]. rewrite IH. reflexivity.
Qed.
Lemma ro_img8 : forall m A v, mem_inv asegs m -> ro_bytes_b asegs A (le8 (wz v)) = true -> 0 <= A -> A + 8 <= 2^64 ->
ro_cells asegs m A [C8 (wz v)].
Proof.
intros m A v MI RB H0 HL.
pose proof (ro_cells_image asegs m A (le8 (wz v)) MI RB H0 ltac:(rewrite length_le8; exact HL)) as R.
eapply ro_cells_recast'; [exact R| cbn; split; exact I| cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity].
Qed.

Ltac name_towers H :=
repeat match type of H with
| context [CB ?n ?j] =>
lazymatch j with
| firstn _ _ => idtac | skipn _ _ => idtac
end;
let x := fresh "jk" in set (x := j) in H; clearbody x
end.
Ltac pc_carve ST :=
carve_frame 2240%nat ST;
lazymatch goal with FR : rw_cells _ _ _ [CB 2240 _] |- _ =>
apply (rw_cells_split_CB asegs _ _ [] 2240 _ _ [2136; 104]%nat) in FR; [| reflexivity]; cbn [mk_CB_cells app] in FR;
name_towers FR end.

Definition pc_prologue_post {BAND : Band} (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (ms' : machine_state) : Prop :=
exists (m' : mem) (jk : list byte),
ms' = MS (mkR ra (wz (bv_unsigned sp + -2240)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x5340c) fc None m' (seg_rom asegs)
/\ rw_cells asegs m' (bv_unsigned sp + -2240) [CB 2136 jk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ stk asegs m' lo (bv_unsigned sp + -2240)
/\ munch [(bv_unsigned sp - 2320, bv_unsigned sp)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m'.

Lemma pc_prologue {BAND : Band} : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m -> band_lo <= lo -> lo <= bv_unsigned sp - 2320 ->
evt asegs (pc_prologue_post ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pcommon_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros ST MI CEIL LO.
pose proof CEIL as CEIL'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 2320, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold pcommon_entry.
pc_carve ST.
do 16 bstep.
apply evt_done. unfold pc_prologue_post. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
split; [exact FR|]. split; [exact ST|]. split; [exact MU|]. split; [exact WM| exact MI].
Qed.

Lemma u8_lit' : forall c, (0 <= c < 256)%Z -> bv_unsigned (Z_to_bv 8 c) = c.
Proof. intros c Hc. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. apply Z.mod_small. cbn. lia. Qed.
Lemma forallb_skipn' {X} (f : X -> bool) : forall i l, forallb f l = true -> forallb f (skipn i l) = true.
Proof. induction i as [|i IH]; intros l H; [exact H|]. destruct l as [|x l]; [reflexivity|]. cbn in H |- *. apply andb_prop in H as [_ H]. apply IH. exact H. Qed.
Lemma cells_size_mapC1 : forall l, cells_size (map (fun c => C1 (b8 c)) l) = length l.
Proof. induction l as [|c l IH]; [reflexivity|]. cbn [map cells_size csize length]. rewrite IH. lia. Qed.
Lemma ro_C1_skipn : forall segs m A l i, ro_cells segs m A (map (fun c => C1 (b8 c)) l) -> (i <= length l)%nat ->
ro_cells segs m (A + Z.of_nat i) (map (fun c => C1 (b8 c)) (skipn i l)).
Proof.
intros segs m A l i H Hi. rewrite <- (firstn_skipn i l), map_app in H. apply ro_cells_app in H. destruct H as [_ H].
rewrite cells_size_mapC1, length_firstn, Nat.min_l in H by lia. exact H.
Qed.

Lemma pc_scan_core {BAND : Band} : forall (n : nat) (l : list Z) (p : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P : machine_state -> Prop),
ro_cells asegs m p (map (fun c => C1 (b8 c)) l) ->
0 <= p -> p + Z.of_nat (length l) <= 2^47 -> (n < length l)%nat ->
forallb (fun c => (0 <=? c) && (c <? 256)) l = true ->
forallb (fun c => negb (c =? 37) && negb (c =? 0)) (firstn n l) = true ->
nth n l 0 = 37 ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 37) a1 a2 a3 a4 a5 a6 a7 s2 (wz (p + Z.of_nat n)) s4 s5 s6 s7 s8 s9 s10 (wz 37) t3 t4 t5 t6)
F (wz 0x53524) fc None m (seg_rom asegs)) ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz p) s4 s5 s6 s7 s8 s9 s10 (wz 37) t3 t4 t5 t6)
F (wz 0x5350c) fc None m (seg_rom asegs)).
Proof.
induction n as [|n IH]; intros l p ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m P FM Hp Hl Hn HB HN H37 K;
(destruct l as [|c l']; [cbn in Hn; lia|]);
change (map (fun c => C1 (b8 c)) (c :: l')) with ([C1 (b8 c)] ++ map (fun c => C1 (b8 c)) l') in FM;
apply ro_cells_app in FM; destruct FM as [C0 FM]; cbn [cells_size csize Nat.add] in FM;
cbn [forallb] in HB; apply andb_prop in HB as [Hc HB]; apply andb_prop in Hc as [Hc1 Hc2]; apply Z.leb_le in Hc1; apply Z.ltb_lt in Hc2.
- cbn [nth] in H37. subst c. rewrite Z.add_0_r in K.
bstep. bstep. exact K.
- cbn [firstn forallb] in HN. apply andb_prop in HN as [Hc HN]. apply andb_prop in Hc as [Hc3 Hc4].
apply Bool.negb_true_iff, Z.eqb_neq in Hc3. apply Bool.negb_true_iff, Z.eqb_neq in Hc4.
bstep. bstep.
if_cases K1; zify_cond K1; rewrite ?(u8_lit' c), ?unsigned_lit in K1 by lia; [exfalso; lia|].
bstep.
if_cases K2; zify_cond K2; rewrite ?(u8_lit' c), ?unsigned_lit in K2 by lia; [exfalso; lia|].
bstep. bstep. bstep.
eapply (IH l' (p + 1)); clear IH.
+ exact FM.
+ lia.
+ cbn [length] in Hl. lia.
+ cbn [length] in Hn. lia.
+ exact HB.
+ exact HN.
+ exact H37.
+ replace (p + 1 + Z.of_nat n) with (p + Z.of_nat (S n)) by lia. exact K.
Qed.

Lemma pc_scan {BAND : Band} : forall (n i : nat) (l : list Z) (A q p : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P : machine_state -> Prop),
ro_cells asegs m A (map (fun c => C1 (b8 c)) l) ->
q = A + Z.of_nat (i + n) -> p = A + Z.of_nat i -> 0 <= A -> A + Z.of_nat (length l) <= 2^47 -> (i + n < length l)%nat ->
forallb (fun c => (0 <=? c) && (c <? 256)) l = true ->
forallb (fun c => negb (c =? 37) && negb (c =? 0)) (firstn n (skipn i l)) = true ->
nth (i + n) l 0 = 37 ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 37) a1 a2 a3 a4 a5 a6 a7 s2 (wz q) s4 s5 s6 s7 s8 s9 s10 (wz 37) t3 t4 t5 t6)
F (wz 0x53524) fc None m (seg_rom asegs)) ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz p) s4 s5 s6 s7 s8 s9 s10 (wz 37) t3 t4 t5 t6)
F (wz 0x5350c) fc None m (seg_rom asegs)).
Proof.
intros n i l A q p ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m P FM Hq -> HA Hl Hn HB HN H37 K.
eapply (pc_scan_core n (skipn i l)).
- apply ro_C1_skipn; [exact FM| lia].
- lia.
- rewrite length_skipn. lia.
- rewrite length_skipn. lia.
- apply forallb_skipn'. exact HB.
- exact HN.
- rewrite nth_skipn. exact H37.
- replace (A + Z.of_nat i + Z.of_nat n) with q by lia. exact K.
Qed.

Lemma pc_scan_nul_core {BAND : Band} : forall (n : nat) (l : list Z) (p : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P : machine_state -> Prop),
ro_cells asegs m p (map (fun c => C1 (b8 c)) l) ->
0 <= p -> p + Z.of_nat (length l) <= 2^47 -> (n < length l)%nat ->
forallb (fun c => (0 <=? c) && (c <? 256)) l = true ->
forallb (fun c => negb (c =? 37) && negb (c =? 0)) (firstn n l) = true ->
nth n l 0 = 0 ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 (wz (p + Z.of_nat n)) s4 s5 s6 s7 s8 s9 s10 (wz 37) t3 t4 t5 t6)
F (wz 0x535b4) fc None m (seg_rom asegs)) ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz p) s4 s5 s6 s7 s8 s9 s10 (wz 37) t3 t4 t5 t6)
F (wz 0x5350c) fc None m (seg_rom asegs)).
Proof.
induction n as [|n IH]; intros l p ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m P FM Hp Hl Hn HB HN H0 K;
(destruct l as [|c l']; [cbn in Hn; lia|]);
change (map (fun c => C1 (b8 c)) (c :: l')) with ([C1 (b8 c)] ++ map (fun c => C1 (b8 c)) l') in FM;
apply ro_cells_app in FM; destruct FM as [C0 FM]; cbn [cells_size csize Nat.add] in FM;
cbn [forallb] in HB; apply andb_prop in HB as [Hc HB]; apply andb_prop in Hc as [Hc1 Hc2]; apply Z.leb_le in Hc1; apply Z.ltb_lt in Hc2.
- cbn [nth] in H0. subst c. rewrite Z.add_0_r in K.
bstep. bstep. bstep. exact K.
- cbn [firstn forallb] in HN. apply andb_prop in HN as [Hc HN]. apply andb_prop in Hc as [Hc3 Hc4].
apply Bool.negb_true_iff, Z.eqb_neq in Hc3. apply Bool.negb_true_iff, Z.eqb_neq in Hc4.
bstep. bstep.
if_cases K1; zify_cond K1; rewrite ?(u8_lit' c), ?unsigned_lit in K1 by lia; [exfalso; lia|].
bstep.
if_cases K2; zify_cond K2; rewrite ?(u8_lit' c), ?unsigned_lit in K2 by lia; [exfalso; lia|].
bstep. bstep. bstep.
eapply (IH l' (p + 1)); clear IH.
+ exact FM.
+ lia.
+ cbn [length] in Hl. lia.
+ cbn [length] in Hn. lia.
+ exact HB.
+ exact HN.
+ exact H0.
+ replace (p + 1 + Z.of_nat n) with (p + Z.of_nat (S n)) by lia. exact K.
Qed.

Lemma pc_scan_nul {BAND : Band} : forall (n i : nat) (l : list Z) (A q p : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P : machine_state -> Prop),
ro_cells asegs m A (map (fun c => C1 (b8 c)) l) ->
q = A + Z.of_nat (i + n) -> p = A + Z.of_nat i -> 0 <= A -> A + Z.of_nat (length l) <= 2^47 -> (i + n < length l)%nat ->
forallb (fun c => (0 <=? c) && (c <? 256)) l = true ->
forallb (fun c => negb (c =? 37) && negb (c =? 0)) (firstn n (skipn i l)) = true ->
nth (i + n) l 0 = 0 ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 (wz q) s4 s5 s6 s7 s8 s9 s10 (wz 37) t3 t4 t5 t6)
F (wz 0x535b4) fc None m (seg_rom asegs)) ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz p) s4 s5 s6 s7 s8 s9 s10 (wz 37) t3 t4 t5 t6)
F (wz 0x5350c) fc None m (seg_rom asegs)).
Proof.
intros n i l A q p ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m P FM Hq -> HA Hl Hn HB HN H0 K.
eapply (pc_scan_nul_core n (skipn i l)).
- apply ro_C1_skipn; [exact FM| lia].
- lia.
- rewrite length_skipn. lia.
- rewrite length_skipn. lia.
- apply forallb_skipn'. exact HB.
- exact HN.
- rewrite nth_skipn. exact H0.
- replace (A + Z.of_nat i + Z.of_nat n) with q by lia. exact K.
Qed.

Ltac scan_side A := first [ lazymatch goal with H : ro_cells _ _ A _ |- ro_cells _ _ A _ => exact H end | reflexivity | lia
| apply Z.leb_le; vm_compute; reflexivity | apply Nat.ltb_lt; vm_compute; reflexivity | vm_compute; reflexivity ].
Ltac scan_pct n i l A := run_to 0x5350c; let q := eval vm_compute in (A + Z.of_nat (i + n)) in eapply (pc_scan n i l A q); [ scan_side A .. | ].
Ltac scan_nul n i l A := run_to 0x5350c; let q := eval vm_compute in (A + Z.of_nat (i + n)) in eapply (pc_scan_nul n i l A q); [ scan_side A .. | ].

Tactic Notation "pose_str" ident(nm) constr(A) constr(l) constr(MI) := pose proof (ro_str _ A l MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as nm; cbn [map] in nm.
Ltac pose_rodata MI :=
pose_str RS1 0x1d915 [100; 105; 111; 117; 120; 88; 110; 0] MI;
pose_str RS2 0x16c7d [97; 65; 101; 69; 102; 70; 103; 71; 0] MI;
pose_str RS3 0x15b57 [39; 45; 43; 32; 35; 48; 0] MI;
pose_str RS4 0x1c640 [106; 122; 116; 76; 113; 0] MI;
pose_str RS5 0x146d7 [99; 67; 115; 83; 0] MI;
pose_str RS6 0x1abb9 [67; 83; 0] MI;
pose_str RS7 0x1086e [99; 115; 91; 0] MI;
pose_str RS8 0x13f97 [115; 83; 0] MI;
pose proof (ro_img8 _ 0x10460 0xaaaaaaaaaaaaaaaa MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as RK.

Ltac stop_pc pc := lazymatch pc with 479088%Z => idtac | 479268%Z => idtac | 479428%Z => idtac | 358144%Z => idtac | 414124%Z => idtac end.

Ltac run := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => first [stop_pc pc; fail 1 | bstep] end).

Ltac fixret := try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).

Ltac call_strchr A lst :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MIc : mem_inv asegs mc |- _ =>
eapply evt_cut;
[ eapply istrchr_spec with (l := lst) (q := A) (t := []); [ | | | reflexivity];
[ lia
| exact (proj2 (ro_str _ A (lst ++ [0]) MIc ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))
| repeat (apply Forall_cons; [lia|]); apply Forall_nil ]
| let ms' := fresh "ms'" in let PO := fresh "PO" in
intros ms' PO; destruct PO as (? & ? & ->); cbn [strchr_res Z.eqb Pos.eqb]; lits; fixret ]
end end.

Ltac call_strlen FMT l :=
eapply evt_cut;
[ eapply istrlen_spec with (s := l) (t := []); [exact (proj2 FMT)| repeat (apply Forall_cons; [lia|]); apply Forall_nil]
| let ms' := fresh "ms'" in intros ms' <-; let n := eval vm_compute in (zlength l) in change (zlength l) with n; lits; fixret ].

Ltac call_memset DIR :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_cut;
[ eapply imemset40_spec; [exact DIR| reflexivity| assumption| lia]
| let ms' := fresh "ms'" in let PO := fresh "PO" in let m' := fresh "m" in
let MU2 := fresh "MU2" in let WM2 := fresh "WM2" in
intros ms' PO; destruct PO as (m' & -> & MU2 & WM2 & ? & ?DIR2); clear DIR;
transport_after_call asegs mc m' MU2 WM2; clear MU2 WM2; try clear mc; rename DIR2 into DIR; fixret ]
end.

Ltac dir_L2 DIR :=
lazymatch type of DIR with rw_cells _ ?mm ?A [C8 ?w0; C8 ?w1; C8 ?b; C8 ?e; C8 ?w4] =>
let D := fresh "DIR" in
assert (D : rw_cells asegs mm A [CB 8 (le8 w0); CB 8 (le8 w1); C8 b; C8 e; CB 8 (le8 w4)])
by (eapply rw_cells_recast'; [exact DIR| cbn [cells_wf cell_wf]; rewrite ?length_le8; repeat split; reflexivity| reflexivity]);
clear DIR; rename D into DIR
end.
Ltac dir_L1 DIR :=
lazymatch type of DIR with rw_cells _ ?mm ?A (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?rest) =>
let D := fresh "DIR" in
assert (D : rw_cells asegs mm A ([c0; c1; c2; c3] ++ rest ++ [])) by (rewrite app_nil_r; exact DIR);
apply rw_cells_merge in D; cbn [cells_size csize cells_bytes cbytes app Nat.add] in D;
clear DIR; rename D into DIR
end.

Ltac bvlist_eq := lazymatch goal with
| |- cons _ _ = cons _ _ => apply (f_equal2 cons); [apply bv_eq; reflexivity | bvlist_eq]
| |- nil = nil => reflexivity end.
Ltac dir_L2c DIR :=
lazymatch type of DIR with rw_cells _ ?mm ?A [C8 (Z_to_bv 64 ?w0); C8 (Z_to_bv 64 ?w1); C8 ?b; C8 ?e; C8 ?w4] =>
let l0 := eval vm_compute in (w0 mod 2^32) in let h0 := eval vm_compute in ((w0 / 2^32) mod 2^32) in
let l1 := eval vm_compute in (w1 mod 2^32) in let h1 := eval vm_compute in ((w1 / 2^32) mod 2^32) in
let D := fresh "DIR" in
assert (D : rw_cells asegs mm A [C4 (Z_to_bv 64 l0); C4 (Z_to_bv 64 h0); C4 (Z_to_bv 64 l1); C4 (Z_to_bv 64 h1); C8 b; C8 e; CB 8 (le8 w4)])
by (eapply rw_cells_recast'; [exact DIR| cbn [cells_wf cell_wf]; rewrite ?length_le8; repeat split; reflexivity|
lazymatch goal with |- ?g => tryif has_var g then fail 1 "dir_L2c: open cells" else (vm_compute; bvlist_eq) end]);
clear DIR; rename D into DIR
end.
Ltac dir_back DIR :=
lazymatch goal with |- rw_cells _ _ _ ?cs => eapply rw_cells_recast'; [exact DIR| cbn [cells_wf cell_wf]; rewrite ?length_le8, ?length_take, ?length_drop; repeat split; reflexivity|
lazymatch goal with |- ?g => tryif has_var g then fail 1 "dir_back: open cells" else (vm_compute; bvlist_eq) end] end.

Lemma cbytes_mapC1 : forall l, cells_bytes (map (fun z => C1 (b8 z)) l) = zb l.
Proof. unfold zb. induction l as [|z l IH]; cbn [map cells_bytes cbytes app]; [reflexivity| now rewrite IH]. Qed.

Definition pc_setup_post {BAND : Band} (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo A : Z) (ms' : machine_state) : Prop :=
exists (m' : mem) (junk1 junk2 : list byte),
ms' = MS (mkR (wz 0x53508) (wz (bv_unsigned sp + -2240)) gp tp t0 t1 t2 sp s1
(wz (bv_unsigned sp + -2216)) (wz 0) (wz (bv_unsigned sp + -2176)) (wz (bv_unsigned sp + -2176)) (wz 0) a5 a6 a7
(wz 10) (wz A) (wz 0x15b57) a2 s6 (wz 9) (wz (bv_unsigned sp + -2184)) (wz 12297829382473034410) (wz (-1)) (wz 37) t3 t4 t5 t6)
F (wz 0x5350c) fc None m' (seg_rom asegs)
/\ rw_cells asegs m' (bv_unsigned sp + -2240) [CB 8 junk1; C8 (wz (bv_unsigned sp + -120)); C8 a0]
/\ rw_cells asegs m' (bv_unsigned sp + -2216) [C8 (wz 0); C8 (wz 18446744073709551615); C8 (wz 0); C8 (wz 0); C8 (wz 0)]
/\ rw_cells asegs m' (bv_unsigned sp + -2176) [CB 2072 junk2; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ stk asegs m' lo (bv_unsigned sp + -2240)
/\ munch [(bv_unsigned sp - 2320, bv_unsigned sp)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m'.

Lemma pc_setup {BAND : Band} : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo A c : Z) (l : list Z),
ISH m -> stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m -> band_lo <= lo -> lo <= bv_unsigned sp - 2320 ->
ro_bytes_b asegs A (map b8 (c :: l ++ [0])) = true ->
forallb (fun z => (0 <? z) && (z <? 256)) (c :: l) = true ->
(length l < 63)%nat -> 0x10000 <= A -> A + Z.of_nat (length l) + 2 <= 0x23080 ->
evt asegs (pc_setup_post ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo A)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz A) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pcommon_entry) fc None m (seg_rom asegs)).
Proof.
intros until l. intros ISH0 ST MI CEIL LO RB BYT LEN ZLO ZHI.
pose proof CEIL as CEIL'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 2320, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
destruct ISH0 as (ASH & RC & SB).
assert (BYT' : Forall (fun z => 0 < z < 256) (c :: l)).
{ apply Forall_forall. intros x Hx. eapply forallb_forall in BYT; [|exact Hx]. apply andb_prop in BYT as [B1 B2].
apply Z.ltb_lt in B1, B2. lia. }
assert (C0 : 0 < c < 256) by (inversion BYT'; assumption).
clear BYT.
assert (SZ : szone A (zlength (c :: l) + 1)) by (left; unfold zlength; cbn [length]; lia).
assert (NR : 1 <= zlength (c :: l) < 64) by (unfold zlength; cbn [length]; lia).
change (boxed (szone A (zlength (c :: l) + 1))) in SZ.
unfold pcommon_entry.
eapply evt_cut; [ eapply pc_prologue; [exact ST | exact MI | exact CEIL | lia] | ].
intros ms' (m' & jk & -> & FR & ST' & MUc & WMc & MIc).
transport_after_call asegs m m' MUc WMc. clear MUc WMc.
try clear ST. try clear MI. rename ST' into ST. rename MIc into MI.
apply (rw_cells_split_CB asegs _ _ [] 2136 _ _ [8;8;8;8;8;8;8;8;2072]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
apply (proj1 (rw_cells_app asegs _ _ [_;_;_] _)) in FR. destruct FR as [FRa FR].
apply (proj1 (rw_cells_app asegs _ _ [_;_;_;_;_] _)) in FR. destruct FR as [DIR FRb].
cbn [cells_size csize Nat.add app] in FRa, DIR, FRb.
replace (bv_unsigned sp + -2240 + Z.of_nat 24) with (bv_unsigned sp + -2216) in DIR by lia.
replace (bv_unsigned sp + -2240 + Z.of_nat 24 + Z.of_nat 40) with (bv_unsigned sp + -2176) in FRb by lia.
lazymatch type of FRa with rw_cells _ _ _ (CB 8 ?j :: _) => remember j as junk1 eqn:EJ1; clear EJ1 end.
lazymatch type of FRb with rw_cells _ _ _ (CB 2072 ?j :: _) => remember j as junk2 eqn:EJ2; clear EJ2 end.
name_towers FRa. name_towers DIR.

pose proof (ro_str _ A (c :: l ++ [0]) MI RB ltac:(lia) ltac:(cbn [length]; rewrite length_app; cbn [length]; lia)) as FMT.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (SRC : bytes_at asegs mc A (zb (c :: l) ++ b8 0 :: []));
[ pose proof (proj2 FMT) as B; rewrite cbytes_mapC1 in B; unfold zb in B |- *;
replace (c :: l ++ [0]) with ((c :: l) ++ [0]) in B by reflexivity; rewrite map_app in B; exact B |] end.
change (map (fun z => C1 (b8 z)) (c :: l ++ [0])) with ([C1 (b8 c)] ++ map (fun z => C1 (b8 z)) (l ++ [0])) in FMT.
apply ro_cells_app in FMT. destruct FMT as [FC0 _].
run.
eapply evt_cut; [eapply istrlen_spec with (s := c :: l) (t := []); [exact SRC| exact BYT'] |].
intros ms' <-. fixret. clear SRC BYT'.
assert (ZN : A + zlength (c :: l) + 1 <= 0x23080) by (unfold zlength; cbn [length]; lia).
set (n := zlength (c :: l)) in *. clearbody n.
bstep. bstep. bstep.
rewrite (unsigned_lit A), zb_lxor_ones by lia. ifF.
bstep. bstep. ifF.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (ash_munch _ _ _ ASH MU WM ltac:(zforalls)) as ASHc;
pose proof (shadow_base_munch _ _ _ SB MU ltac:(rt_wzones)) as SBc end.
unfold boxed in SZ.
destruct (ash_szone_words _ _ _ ASHc SZ ltac:(lia)) as [W1 W2]. clear ASHc.
destruct SBc as [SB1 SB2]. unfold A_SHADOW_GOT, A_SHADOW_CELL, A_SHADOW_OFS in SB1, SB2.
bstep. bstep. bstep. bstep. bstep. bstep. bstep. bstep.
rewrite ?(unsigned_lit A), ?(unsigned_lit (n + A)) by lia.
replace (2147450880 + A ≫ 3) with (SH A) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; lia).
replace (2147450880 + (n + A) ≫ 3) with (SH (A + (n + 1) - 1))
by (rewrite Z.shiftr_div_pow2, SH_eq by lia; replace (A + (n + 1) - 1) with (n + A) by lia; change (2^3) with 8; lia).
assert (SHR : 0x7fff8000 <= SH A /\ SH A <= SH (A + (n + 1) - 1) < 0x10007fff8000)
by (rewrite !SH_eq; clear - NR ZN ZLO; Z.div_mod_to_equations; lia).
stp. stp. rewrite (unsigned_lit (SH A)), (unsigned_lit (SH (A + (n + 1) - 1))) by lia. rewrite !land_m8 by lia.
replace (SH A - SH A mod 8) with (8 * (SH A / 8)) by (Z.div_mod_to_equations; lia).
replace (SH (A + (n + 1) - 1) - SH (A + (n + 1) - 1) mod 8) with (8 * (SH (A + (n + 1) - 1) / 8)) by (Z.div_mod_to_equations; lia).
bstep. bstep. bstep. bstep.
clear W1 W2 SB1 SB2 SHR.
bstep. bstep. bstep. bstep.
rewrite zxb_b8, (Z.mod_small c) by lia.
bstep. ifF.
run_to 0x534b0.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MIc : mem_inv asegs mc |- _ =>
pose proof (ro_img8 _ 0x10460 0xaaaaaaaaaaaaaaaa MIc ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as RK end end.
run_to 0x534b4. clear RK.
run. call_memset DIR.
bstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => apply evt_done; unfold pc_setup_post; exists mc, junk1, junk2 end.
split; [reflexivity|].
split; [exact FRa|]. split; [exact DIR|]. split; [exact FRb|].
split; [assumption|]. split; [exact MU|]. split; [exact WM| assumption].
Qed.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp Qsn5 QQwg QUxU QOJv QqLk QMSY QpME QkJ4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1 QTVW.Mq0 QNQk.Mq4 QpY2.Mq8 QTVW.Mq3 QOJv.Mq4 QNQk.Mq2 Q9Ho.Mq2 QqLk QnRU.Mqa QMSY.
Import QpME.Mq1 QkJ4.
Import QlES.
Import ListNotations. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Variables (n i : Z) (gp : word).
Let c := class_of n.
Let sz := class_size c.
Let rz := rz_size n.
Let n' := used_size n.
Let nd := needed n.
Let AB := slot_beg RE c i.
Let A := AB + rz.
Hypothesis RL : rlay_ok RE X.
Hypothesis Hn : 0 <= n.
Hypothesis HP : from_primary n = true.
Hypothesis PAB : prim_lo RE <= AB.
Hypothesis ABP : AB + sz <= prim_lo RE + 2^37.
Hypothesis AL16 : AB mod 16 = 0.

Lemma geomS : 1 <= c <= 30 /\ nd <= sz <= 65536 /\ sz mod 32 = 0 /\ 16 <= rz <= 2048 /\ rz mod 16 = 0
/\ 1 <= n' /\ n' <= Z.max n 8 /\ n <= 65536 /\ Z.max n 8 + rz <= nd /\ nd < Z.max n 8 + 8 + rz /\ nd mod 8 = 0 /\ 24 <= nd <= 65536
/\ A mod 16 = 0 /\ 0x10007fff8000 <= AB /\ AB + sz <= band_lo
/\ appr_lia (rl_T X) 4096 /\ rl_T X + 4096 <= band_lo /\ rl_T X mod 4096 = 0
/\ (rl_T X + 4096 <= AB \/ AB + sz <= rl_T X)
/\ appr_lia (rl_ctx X) 65536 /\ rl_ctx X + 65536 <= band_lo
/\ (rl_ctx X + 65536 <= AB \/ AB + sz <= rl_ctx X)
/\ appr_lia (rl_dn X) 0x100000 /\ rl_dn X + 0x100000 <= band_lo
/\ (rl_dn X + 0x100000 <= AB \/ AB + sz <= rl_dn X)
/\ appr_lia (rl_ssb X) 0x800000 /\ rl_ssb X + 0x800000 <= band_lo
/\ (rl_ssb X + 0x800000 <= AB \/ AB + sz <= rl_ssb X).
Proof. exact (geom RE X n i RL Hn HP PAB ABP AL16). Qed.

Lemma alloc_hdr : forall ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (s7r : word) (sp : word) (F : bvmap 5 word) fc m lo
(fj : list byte) (canfill v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 rav : word) (b0 b1 : byte) (h w d : word) (Q : machine_state -> Prop),
RTconst RE X m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -128) -> band_lo <= lo -> lo <= bv_unsigned sp - 816 ->
rw_cells asegs m (bv_unsigned sp + -128) (alloc_frame fj canfill v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 rav) ->
rw_cells asegs m (A + -16) [C1 b0; C1 b1; C2 h; C4 w; C8 d] ->
(forall m1 (u0 u1 u2 u3 u5 u6 u7 : word),
munch [(A + -16, A)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp + -128) ->
rw_cells asegs m1 (bv_unsigned sp + -128) (alloc_frame fj canfill v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 rav) ->
rw_cells asegs m1 (A + -16) [C1 b0; C1 (b8 (hb1 b1)); C2 (wz 0); C4 (wz n'); C8 d] ->
RTconst RE X m1 ->
evt asegs Q (MS (mkR ra (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 (wz 1) (wz n') u0 u1 u2 u3 (wz (AB + nd)) u5 u6 u7
(wz AB) (wz nd) (wz A) (wz (A + -16)) (wz A_INSTANCE) s7r (wz 0) (wz (A + n')) (wz (rl_T X)) (wz 1) t3 t4 t5 t6)
F (wz 0x3f408) fc None m1 (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 (wz 1) (wz n') (wz AB) a1 a2 a3 a4 a5 a6 a7
(wz AB) (wz nd) (wz rz) (wz n) (wz A_INSTANCE) s7r (wz (-8)) (wz 7) (wz (rl_T X)) (wz 1) t3 t4 t5 t6)
F (wz 0x3f310) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT MI ST CEIL LO FR HDR CONT.
pose proof geomS as (Gc & Gsz & Gsz32 & Grz & Grz16 & Gn1 & Gn2 & Gn3 & Gnd1 & Gnd2 & Gnd8 & Gnd3 & GA16 & GK & GC & TK & TB & TA & TD & CK & CC & CD & _).
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (RT_T _ _ _ RT) as TT. pose proof (RT_ctx_tid _ _ _ RT) as CT. cbv beta delta [rt_T_cells] in TT.
pose proof (munch_refl [(A + -16, A)] m) as MU. pose proof (wmono_refl asegs m) as WM.
subst A. unfold alloc_frame in FR.
step.
step.
rewrite (unsigned_lit (AB + rz)), land_7 by lia.
replace ((AB + rz) mod 8) with 0 by (clear - GA16; Z.div_mod_to_equations; lia).
step.
step. if_lit.
step.
step. ifz.
step.
stp.
step.
step.
step.
rewrite (unsigned_lit n'), Z.shiftr_div_pow2, (Z.div_small n') by lia.
step.
rewrite (unsigned_lit n), Z.shiftr_div_pow2, (Z.div_small n) by lia.
step.
step.
step.
step. if_lit.
step.
step.
step.
step.
step.
rewrite hb1_norm in HDR.
step. ifz.
step.
stp.
stp.
step.
replace (nd + AB) with (AB + nd) by lia.
eapply CONT; [exact MU| exact WM| assumption| exact ST| exact FR| exact HDR| ].
eapply RTconst_munch; [exact RT| exact MU| exact WM|].
constructor; [apply rt_avoid_prim; [exact RL| lia| unfold prim_hi; unfold prim_lo in *; lia]| constructor].
Qed.

Definition depot_W (sp : Z) : list (Z * Z) :=
[(sp - 352, sp - 128); (SS_BASE, DP_END); (rl_dn X, rl_dn X + 0x100000); (rl_ssb X, rl_ssb X + 0x800000)].

Lemma alloc_depot : forall ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (sp : word) (F : bvmap 5 word) fc m lo
(obj tsz dn : Z) (q : list word) (b0 : byte) (b1v : Z) (d : word) (Q : machine_state -> Prop),
RTconst RE X m -> RDepot RE X m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -128) -> band_lo <= lo -> lo <= bv_unsigned sp - 816 ->
rw_cells asegs m obj [C8 (wz (obj + 16)); C8 (wz tsz)] ->
u64arr asegs m (obj + 16) q -> Z.of_nat (length q) = 30 -> 1 <= tsz <= 30 ->
depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
bv_unsigned sp <= obj -> obj + 256 < 2^64 ->
rw_cells asegs m (A + -16) [C1 b0; C1 (b8 b1v); C2 (wz 0); C4 (wz n'); C8 d] ->
(forall m1 (u0 u1 u2 u5 u6 u7 u10 u11 u12 u13 u14 u15 u16 u17 : word) (id : Z),
munch ((A + -8, A) :: depot_W (bv_unsigned sp)) m m1 -> wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp + -128) ->
RTconst RE X m1 -> RDepot RE X m1 ->
rw_cells asegs m1 obj [C8 (wz (obj + 16)); C8 (wz tsz)] -> u64arr asegs m1 (obj + 16) q ->
1 <= id < 2^16 -> (exists dn', depot_n asegs m1 dn' /\ dn <= dn' <= dn + 1) ->
rw_cells asegs m1 (A + -16) [C1 b0; C1 (b8 b1v); C2 (wz 0); C4 (wz n'); C8 (wz id)] ->
evt asegs Q (MS (mkR (wz 0x3f414) (wz (bv_unsigned sp + -128)) gp (wz A_TP) u0 u1 u2 (wz 1) (wz n') (wz id) u5 u6 u7 u10 u11 u12 u13
(wz AB) (wz nd) (wz A) (wz (A + -16)) (wz A_INSTANCE) (wz obj) (wz 0) (wz (A + n')) (wz (rl_T X)) (wz 1) u14 u15 u16 u17)
F (wz 0x3f424) fc None m1 (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 (wz 1) (wz n') a0 a1 a2 a3 a4 a5 a6 a7
(wz AB) (wz nd) (wz A) (wz (A + -16)) (wz A_INSTANCE) (wz obj) (wz 0) (wz (A + n')) (wz (rl_T X)) (wz 1) t3 t4 t5 t6)
F (wz 0x3f408) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT RD MI ST CEIL LO OBJ TRQ LQ SZR DNH DCAP OB1 OB2 HDR CONT.
pose proof geomS as (Gc & Gsz & Gsz32 & Grz & Grz16 & Gn1 & Gn2 & Gn3 & Gnd1 & Gnd2 & Gnd8 & Gnd3 & GA16 & GK & GC & TK' & TB & TA & TD & CK & CC & CD & NK & NC & ND & BK & BC & BD).
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (munch_refl ((A + -8, A) :: depot_W (bv_unsigned sp)) m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold depot_W, SS_BASE, DP_END in MU. subst A.
step.
step.
step.
call_sp_ch (depot_put_spec RE X) ltac:(fun PO => unfold depot_stack, SS_BASE, DP_END in PO);
[exact RL| exact RD| assumption| exact ST| exact CEIL'| unfold depot_stack; lia| exact TRQ| exact LQ| exact SZR| exact DNH| exact DCAP| lia| lia|].
match goal with H : stk asegs _ lo _ |- _ => try rename H into ST end.
match goal with H : (exists id, _) |- _ => destruct H as (id & -> & ID & RD1 & TRQ1 & (dn1 & [DNC DNP] & DNR)) end. unfold DP_N in DNC.
step.
step.
rewrite (unsigned_lit id), (zext32_small id) by lia.
step.
rewrite (unsigned_lit id), Z.lor_0_l by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(AB + rz + -8, AB + rz)] mm) as MUh; pose proof (wmono_refl asegs mm) as WMh end.
step.
eapply CONT; [exact MU| exact WM| assumption| exact ST| | | exact OBJ| exact TRQ| exact ID| exists dn1; split; [split; [unfold DP_N; exact DNC| exact DNP]| exact DNR]| exact HDR].
- eapply RTconst_munch; [exact RT| exact MU| exact WM|]. unfold depot_W.
constructor; [apply rt_avoid_prim; [exact RL| lia| unfold prim_hi; unfold prim_lo in *; lia]|].
constructor; [apply rt_avoid_stack; [exact RL| lia]|].
constructor; [apply rt_avoid_depot_img; exact RL|].
constructor; [apply rt_avoid_dn; exact RL|].
constructor; [apply rt_avoid_ssb; exact RL| constructor].
- eapply RDepot_frame; [exact RD1| exact WMh|].
eapply agree_on_of_munch; [exact MUh| exact WMh|]. intros z Fz _. cbn [outside]. split; [| exact I].
destruct Fz as [Fz|[Fz|[Fz|Fz]]]; [destruct Fz as [F1 F2]; cbn [fst snd] in F1, F2; lia
| destruct Fz as [F1 F2]; cbn [fst snd] in F1, F2; (first [ clear - F2 F1 z ND TK' GK Gnd3 Gnd8 Gnd2 Gnd1 Grz16 Grz Gsz32 Gsz ks q AL16 AB nd rz sz c i n X RE BAND; lia | lia ]) | destruct Fz as [F1 F2]; cbn [fst snd] in F1, F2; (first [ clear - F2 F1 z BD TK' GK Gnd3 Gnd8 Gnd2 Gnd1 Grz16 Grz Gsz32 Gsz ks q AL16 AB nd rz sz c i n X RE BAND; lia | lia ]) | (first [ clear - Fz z TA TK' GK Gnd3 Grz16 Grz ks q AL16 AB nd rz sz c i n X RE BAND; lia | lia ])].
Qed.

End S.
End Mq4.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1 QTVW.Mq0 QNQk.Mq4 QpY2.Mq8 QTVW.Mq3 QOJv.Mq4 QNQk.Mq2 Q9Ho.Mq2 QqLk QnRU.Mqa QMSY.
Import QpME.Mq1 QkJ4.
Import QlES.
Import ListNotations. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Variables (n i : Z) (gp : word).
Let c := class_of n.
Let sz := class_size c.
Let rz := rz_size n.
Let n' := used_size n.
Let nd := needed n.
Let AB := slot_beg RE c i.
Let A := AB + rz.
Hypothesis RL : rlay_ok RE X.
Hypothesis Hn : 0 <= n.
Hypothesis HP : from_primary n = true.
Hypothesis PAB : prim_lo RE <= AB.
Hypothesis ABP : AB + sz <= prim_lo RE + 2^37.
Hypothesis AL16 : AB mod 16 = 0.

Lemma geomS : 1 <= c <= 30 /\ nd <= sz <= 65536 /\ sz mod 32 = 0 /\ 16 <= rz <= 2048 /\ rz mod 16 = 0
/\ 1 <= n' /\ n' <= Z.max n 8 /\ n <= 65536 /\ Z.max n 8 + rz <= nd /\ nd < Z.max n 8 + 8 + rz /\ nd mod 8 = 0 /\ 24 <= nd <= 65536
/\ A mod 16 = 0 /\ 0x10007fff8000 <= AB /\ AB + sz <= band_lo
/\ appr_lia (rl_T X) 4096 /\ rl_T X + 4096 <= band_lo /\ rl_T X mod 4096 = 0
/\ (rl_T X + 4096 <= AB \/ AB + sz <= rl_T X)
/\ appr_lia (rl_ctx X) 65536 /\ rl_ctx X + 65536 <= band_lo
/\ (rl_ctx X + 65536 <= AB \/ AB + sz <= rl_ctx X)
/\ appr_lia (rl_dn X) 0x100000 /\ rl_dn X + 0x100000 <= band_lo
/\ (rl_dn X + 0x100000 <= AB \/ AB + sz <= rl_dn X)
/\ appr_lia (rl_ssb X) 0x800000 /\ rl_ssb X + 0x800000 <= band_lo
/\ (rl_ssb X + 0x800000 <= AB \/ AB + sz <= rl_ssb X).
Proof. exact (geom RE X n i RL Hn HP PAB ABP AL16). Qed.

Lemma alloc_partial : forall ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (sp : word) (F : bvmap 5 word) fc m
(obj : Z) (pb : byte) (Q : machine_state -> Prop),
RTconst RE X m -> mem_inv asegs m ->
(n' mod 8 <> 0 -> rw_cells asegs m (SH A + n' / 8) [C1 pb]) ->
(forall m1 (u u0 u1 u2 u3 u4 u5 u6 u7 u10 u11 u12 u14 u15 u16 u17 u22 : word),
munch [(SH A + n' / 8, SH A + ngran n')] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 -> RTconst RE X m1 ->
(n' mod 8 <> 0 -> rw_cells asegs m1 (SH A + n' / 8) [C1 (b8 (n' mod 8))]) ->
evt asegs Q (MS (mkR u (wz (bv_unsigned sp + -128)) gp (wz A_TP) u0 u1 u2 (wz 1) (wz n') u3 u4 u5 u6 u7 u10 u11 u12
(wz AB) (wz nd) (wz A) (wz (A + -16)) u22 (wz obj) (wz 0) (wz (A + n')) (wz (rl_T X)) (wz 1) u14 u15 u16 u17)
F (wz 0x3f5b4) fc None m1 (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 (wz 1) (wz n') a0 a1 a2 a3 a4 a5 a6 a7
(wz AB) (wz nd) (wz A) (wz (A + -16)) (wz (8 * (n' / 8))) (wz obj) (wz 0) (wz (A + n')) (wz (rl_T X)) (wz 1) t3 t4 t5 t6)
F (wz 0x3f520) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT MI P3 CONT.
pose proof geomS as (Gc & Gsz & Gsz32 & Grz & Grz16 & Gn1 & Gn2 & Gn3 & Gnd1 & Gnd2 & Gnd8 & Gnd3 & GA16 & GK & GC & _).
assert (SHa : SH AB = AB / 8 + 0x7fff8000) by reflexivity.
assert (SHA : SH (AB + rz) = SH AB + rz / 8) by (rewrite <- SH_plus8; f_equal; clear - Grz16; Z.div_mod_to_equations; lia).
assert (N8 : 0 <= n' / 8 /\ 0 <= n' mod 8 < 8 /\ n' = 8 * (n' / 8) + n' mod 8) by (clear - Gn1; Z.div_mod_to_equations; lia).
pose proof (ngran_eq n' ltac:(lia)) as (NG1 & NG2 & NG3). pose proof (round_up_8 n' ltac:(lia)) as [RU8 _].
subst A.
step.
destruct (Z.eq_dec (n' mod 8) 0) as [Z0|NZ].
- ifz.
eapply CONT; [| apply wmono_refl| exact MI| exact RT| intros NE; exfalso; exact (NE Z0)].
replace (ngran n') with (n' / 8) by (rewrite NG1; unfold round_up; clear -Z0 N8; Z.div_mod_to_equations; lia). apply munch_refl.
- ifz. specialize (P3 NZ).
remember (SH (AB + rz) + n' / 8) as SP8 eqn:ESP8.
pose proof (munch_refl [(SP8, SH (AB + rz) + ngran n')] m) as MU. pose proof (wmono_refl asegs m) as WM.
rtc RT 19%nat K19. rtc RT 5%nat K5. rtc RT 1%nat K1. rtc RT 14%nat K14.
step. call0 (can_poison_spec RE X); [exact RT| exact MI|]. subst_words.
step. if_lit.
step. step. step.
step.
stp. stp. stp. stp.
step. unfold_cond; cond_unsig; if_false.
step. step. step. step.
step. step.
stp.
step. ifz.
step. step. step.
stp. stp.
step. ifz.
step. ifz.
step. step.
step.
lits.
step.
rewrite (unsigned_lit (AB + rz + 8 * (n' / 8))), Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
step.
replace (2147450880 + (AB + rz + 8 * (n' / 8)) / 8) with SP8 by (rewrite ESP8, SHA, SHa; clear - AL16 Grz16 N8; Z.div_mod_to_equations; lia).
stp.
step.
rewrite (unsigned_lit n'), (Z.land_comm n' 18446744073709551615), land_ones64 by lia.
step.
rewrite (unsigned_lit n'), land_7 by lia.
step.
rewrite (unsigned_lit (n' mod 8)) in P3 by lia.
eapply CONT; [exact MU| exact WM| assumption| | intros _; exact P3].
eapply RTconst_munch; [exact RT| exact MU| exact WM|].
constructor; [| constructor]. rewrite ESP8, SHA, SHa. apply rt_avoid_gap; [exact RL| clear - GK N8 Grz; Z.div_mod_to_equations; lia| rewrite ?KHI_eq, NG1; unfold round_up; clear - GC Gsz Gnd1 Gn2 N8 NZ Grz; Z.div_mod_to_equations; lia].
Qed.

Lemma alloc_shadow : forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (sp : word) (F : bvmap 5 word) fc m lo
(obj : Z) (j2 : list byte) (pb : byte) (Q : machine_state -> Prop),
RTconst RE X m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -128) -> band_lo <= lo -> lo <= bv_unsigned sp - 816 ->
rw_cells asegs m (SH AB) [C1 fa_byte] ->
(n' / 8 <> 0 -> rw_cells asegs m (SH A) [CB (Z.to_nat (n' / 8)) j2]) ->
(n' mod 8 <> 0 -> rw_cells asegs m (SH A + n' / 8) [C1 pb]) ->
(forall m1 (u u0 u1 u2 u3 u4 u5 u6 u7 u10 u11 u12 u14 u15 u16 u17 u22 : word),
munch [(bv_unsigned sp - 192, bv_unsigned sp - 128); (SH A, SH A + ngran n')] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
stk asegs m1 lo (bv_unsigned sp + -128) -> RTconst RE X m1 ->
rw_cells asegs m1 (SH AB) [C1 fa_byte] ->
(n' / 8 <> 0 -> rw_cells asegs m1 (SH A) [CB (Z.to_nat (n' / 8)) (repeat (b8 0) (Z.to_nat (n' / 8)))]) ->
(n' mod 8 <> 0 -> rw_cells asegs m1 (SH A + n' / 8) [C1 (b8 (n' mod 8))]) ->
evt asegs Q (MS (mkR u (wz (bv_unsigned sp + -128)) gp (wz A_TP) u0 u1 u2 (wz 1) (wz n') u3 u4 u5 u6 u7 u10 u11 u12
(wz AB) (wz nd) (wz A) (wz (A + -16)) u22 (wz obj) (wz 0) (wz (A + n')) (wz (rl_T X)) (wz 1) u14 u15 u16 u17)
F (wz 0x3f5b4) fc None m1 (seg_rom asegs))) ->
evt asegs Q (MS (mkR (wz 0x3f414) (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 (wz 1) (wz n') a0 a1 a2 a3 a4 a5 a6 a7
(wz AB) (wz nd) (wz A) (wz (A + -16)) (wz A_INSTANCE) (wz obj) (wz 0) (wz (A + n')) (wz (rl_T X)) (wz 1) t3 t4 t5 t6)
F (wz 0x3f424) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT MI ST CEIL LO P1 P2 P3 CONT.
pose proof geomS as (Gc & Gsz & Gsz32 & Grz & Grz16 & Gn1 & Gn2 & Gn3 & Gnd1 & Gnd2 & Gnd8 & Gnd3 & GA16 & GK & GC & _).
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
assert (SHa : SH AB = AB / 8 + 0x7fff8000) by reflexivity.
assert (SHA : SH A = SH AB + rz / 8) by (subst A; rewrite <- SH_plus8; f_equal; clear - Grz16; Z.div_mod_to_equations; lia).
assert (N8 : 0 <= n' / 8 /\ 0 <= n' mod 8 < 8 /\ n' = 8 * (n' / 8) + n' mod 8) by (clear - Gn1; Z.div_mod_to_equations; lia).
pose proof (ngran_eq n' ltac:(lia)) as (NG1 & NG2 & NG3). pose proof (round_up_8 n' ltac:(lia)) as [RU8 _].
pose proof (munch_refl [(bv_unsigned sp - 192, bv_unsigned sp - 128); (SH A, SH A + ngran n')] m) as MU. pose proof (wmono_refl asegs m) as WM.
rtc RT 19%nat K19. rtc RT 5%nat K5.
step. if_lit.
step. step.
step.
step.
rewrite (unsigned_lit AB), Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
step.
replace (2147450880 + AB / 8) with (SH AB) by lia.
step.
unfold fa_byte at 1. lits.
step. if_lit.
stp. stp.
step.
rewrite (unsigned_lit n'), land_mask8_48 by lia. replace (n' - n' mod 8) with (8 * (n' / 8)) by lia.
assert (D8 : 8 * (n' / 8) / 8 = n' / 8) by (rewrite Z.mul_comm; apply Z.div_mul; lia).
step.
destruct (Z.eq_dec (n' / 8) 0) as [Q0|QP].
- ifz.
eapply alloc_partial; [exact RT| exact MI| exact P3|].
intros m1 u u0 u1 u2 u3 u4 u5 u6 u7 u10 u11 u12 u14 u15 u16 u17 u22 MUp WMp MIp RTp P3p.
transport_after_call asegs m m1 MUp WMp.
eapply CONT; [exact MU| exact WM| exact MIp| exact ST| exact RTp| exact P1| intros NE; exfalso; exact (NE Q0)| exact P3p].
- unfold_cond; cond_unsig; if_false.
step. step. step. step.
specialize (P2 QP). rewrite <- D8 in P2.
pose proof (munch_refl [(bv_unsigned sp - 192, bv_unsigned sp - 128); (SH A, SH A + n' / 8)] m) as MUx.
call_sp_ch (poison_shadow_spec RE X) ltac:(fun PO => rewrite ?D8 in PO);
[exact RT| exact RL| assumption| exact ST| exact CEIL'| lia
| clear - GA16; Z.div_mod_to_equations; lia| clear; Z.div_mod_to_equations; lia| lia| rewrite ?KHI_eq; lia| lia| lia| right; rewrite D8; lia| exact P2|].
match goal with H : stk asegs _ lo _ |- _ => try rename H into ST end.
match goal with H : RTconst RE X ?mm, H2 : rw_cells asegs ?mm (SH A) _ |- _ => rename H into RT1; rename H2 into P2z end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (P3x : n' mod 8 <> 0 -> rw_cells asegs mm (SH A + n' / 8) [C1 pb])
by (intros NE; eapply rw_cells_transport; [exact (P3 NE)| exact MUx| exact WM| cbn [disjoint_from cells_size csize]; lia]) end.
clear MUx.
eapply alloc_partial; [exact RT1| assumption| exact P3x|].
intros m1 u u0 u1 u2 u3 u4 u5 u6 u7 u10 u11 u12 u14 u15 u16 u17 u22 MUp WMp MIp RTp P3p.
lazymatch type of MUp with munch _ ?ma _ => transport_after_call asegs ma m1 MUp WMp end.
eapply CONT; [exact MU| exact WM| exact MIp| exact ST| exact RTp| exact P1| intros _; exact P2z| exact P3p].
Qed.
End S.
End Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7 QvDJ Q67d.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig.
Import Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QDw3 QUxU QNwL QYnC QSsj QNQk.Mq1 QpY2.Mq1 QYyZ.Mq4 QmP7.Mq0 Q9Ho.Mq1 QYyZ.Mq0 QnRU.Mq0 QnRU.Mq7 QOJv.Mq5 Qu3b.Mq2 QteI.Mq4.
Import Qc6I QJFf QDM6.
Import QCiC Qpj5.Mq1 QvDJ.Mq2 Q67d QCiC.Mq0.
Import QlES. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation mem := (word -> option byte) (only parsing).
Local Notation wz := (Z_to_bv 64).

Lemma coff_shl4 : forall RE c i, 1 <= c <= 31 -> 0 <= i -> reg_beg (ae_L RE) c + coff c i * 16 = slot_beg RE c i.
Proof.
intros RE c i Hc Hi. unfold coff, slot_beg. pose proof (class_size_facts c Hc) as [S1 S2].
assert (E : exists q, class_size c = 16 * q) by (exists (class_size c / 16); Z.div_mod_to_equations; lia).
destruct E as [q E]. rewrite E. replace (16 * q) with (q * 16) by lia. rewrite Z.div_mul by lia. lia.
Qed.

Lemma cr_pure_pop : forall a a' G c K t,
cr_pure a G c K -> 1 <= c <= 31 -> 1 <= c_count (cls a c) -> tag_prim t = false ->
cls a' c = set_count (c_count (cls a c) - 1) (cls a c) -> as_cache_inited a' = true ->
let CA := pk_ca K in let n1 := Z.to_nat (c_count (cls a c) - 1) in let i := nth n1 CA 0 in
cr_pure a' (set_tag c i t G) c (mkPK (pk_fl K) (firstn n1 CA)).
Proof.
intros a a' G c K t PU Hc CNT NP Ea EI CA n1 i.
destruct PU as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & G1 & G2 & G3 & G4 & G5).
fold CA in P2, P4, P6.
assert (LCA : length CA = S n1) by (subst n1; lia).
assert (HIN : In i CA) by (apply nth_In; lia).
pose proof (P6 i HIN) as TI. pose proof (tag_at_Some_lt _ _ _ _ TI) as [I0 _].
assert (ECA : CA = firstn n1 CA ++ [i]).
{ rewrite <- (firstn_skipn n1 CA) at 1. f_equal.
destruct (skipn n1 CA) as [|y l] eqn:E; [apply (f_equal (@length Z)) in E; rewrite length_skipn in E; cbn in E; lia|].
assert (L1 : l = []) by (apply (f_equal (@length Z)) in E; rewrite length_skipn in E; cbn in E; destruct l; [reflexivity| cbn in E; lia]).
subst l. f_equal. unfold i. rewrite <- (firstn_skipn n1 CA) at 1. rewrite app_nth2 by (rewrite length_firstn; lia).
rewrite length_firstn. replace (n1 - Nat.min n1 (length CA))%nat with 0%nat by lia. rewrite E. reflexivity. }
assert (NI : ~ In i (firstn n1 CA)).
{ intros Hin. rewrite ECA in P4. apply NoDup_remove_2 in P4. apply P4. rewrite app_nil_r. exact Hin. }
assert (NIF : ~ In i (pk_fl K)).
{ intros Hin. pose proof (P5 i Hin) as TF. rewrite TI in TF. discriminate. }
unfold cr_pure. rewrite Ea, EI. cbn [pk_fl pk_ca set_count c_count c_num_freed c_mapped_fa c_alloc_user c_mapped_user].
repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
- rewrite length_firstn. lia.
- apply NoDup_firstn. exact P4.
- intros j Hj. rewrite tag_at_set_tag_ne; [apply P5; exact Hj| exact I0| right; intros ->; exact (NIF Hj)].
- intros j Hj. rewrite tag_at_set_tag_ne; [apply P6; exact (In_firstn_In _ _ _ Hj)| exact I0| right; intros ->; exact (NI Hj)].
- rewrite (count_tag_set_tag _ G c i t TCached TI). rewrite P7. destruct t; cbn in NP |- *; try discriminate; lia.
- rewrite (count_tag_set_tag _ G c i t TCached TI). rewrite P8. destruct t; cbn in NP |- *; try discriminate; lia.
- pose proof (ncarved_set_tag c i t G c) as NC. unfold ncarved in NC. rewrite NC. exact G1.
Qed.

Lemma pop_close {BAND : Band} : forall (a a' : AState) G RE X (m m' : mem) c (K : Z -> pcls),
let x := cls a c in let cnt := c_count x in
let CA := pk_ca (K c) in let n1 := Z.to_nat (cnt - 1) in let i := nth n1 CA 0 in
rlay_ok RE X -> 1 <= c <= 30 -> as_cache_inited a = true -> 1 <= cnt ->
cls a' c = set_count (cnt - 1) x -> (forall c0, c0 <> c -> cls a' c0 = cls a c0) -> as_cache_inited a' = true ->
hjunk m (rl_T X + 2768) (rl_T X + 2800) ->
(forall c0, G c0 <> [] -> 1 <= c0 < kNumClasses) ->
(forall c0, 0 <= c0 < kNumClasses -> class_rep a G RE X m c0 (K c0)) ->
wmono asegs m m' ->
(forall c0, 0 <= c0 < kNumClasses -> c0 <> c -> agree_on asegs (fp_cls RE X c0) m m') ->
agree_on asegs (fun z => fp_cls RE X c z /\ ~ (pc_addr X c <= z < pc_addr X c + 4)) m m' ->
rw_cells asegs m' (pc_addr X c) [C4 (wz (cnt - 1))] ->
tag_at G c i = Some TCached
/\ (exists CH, u32arr asegs m (pc_addr X c + 16) CH /\ length CH = 16%nat /\ nth_error CH n1 = Some (wz (coff c i)))
/\ (forall t, tag_prim t = false -> RPrim a' (set_tag c i t G) RE X m')
/\ hjunk m' (slot_beg RE c i) (slot_beg RE c i + class_size c)
/\ rw_cells asegs m' (SH (slot_beg RE c i)) [CB (Z.to_nat (class_size c / 8)) (repeat fa_byte (Z.to_nat (class_size c / 8)))].
Proof.
intros until K; intros x cnt CA n1 i RL Hc EI CNT Ea EO EI' HJS GNE HCall WM OTH AG PCk.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (HCall c ltac:(rewrite K32; lia)) as HC.
pose proof HC as (((j1 & j2 & j3 & j4 & RI) & PC & (CH & ACH & LCH & HCH)) & PU & REG).
pose proof PU as (P1 & P2 & P3 & P4 & P5 & P6 & _). fold CA in P2, P4, P6, HCH.
assert (LCA : length CA = S n1) by (subst n1 cnt x; lia).
assert (HIN : In i CA) by (apply nth_In; lia).
pose proof (P6 i HIN) as TI. pose proof (tag_at_Some_lt _ _ _ _ TI) as [I0 _].
specialize (REG ltac:(lia)). destruct REG as (FA & FJ & SL & UT & SS & US & UJ & FS).

pose proof (reg_geom RE X RL c ltac:(lia)) as (RB & FB & PAL & PK & PCH & PH & RIq).
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB, TD.
unfold iv_disjoint in TD; cbn [fst snd] in TD. idtac. rewrite ?KHI_eq in TK.
assert (NPC : forall z, (z < rl_T X \/ rl_T X + 4096 <= z) -> ~ (pc_addr X c <= z < pc_addr X c + 4)) by (intros z Hz; unfold pc_addr; lia).
assert (AGU : agree_on asegs (uzone RE c) m m').
{ eapply agree_on_mono; [exact AG|]. intros z Uz. split.
- destruct Uz as [Uz|Uz]; [do 4 right; left; exact Uz| do 5 right; exact Uz].
- apply NPC. apply (uzone_bounds RE X c z RL ltac:(lia)) in Uz. rewrite RB in Uz. unfold SH, A_SHADOW_OFS in Uz.
clear - Uz TD PK PCH PH TK Hc. Z.div_mod_to_equations. lia. }
assert (AGFA : agree_on asegs (fun z => fa_beg (ae_L RE) c <= z < fa_beg (ae_L RE) c + kFreeArraySize) m m').
{ eapply agree_on_mono; [exact AG|]. intros z Hz. split; [do 2 right; left; exact Hz| apply NPC]. rewrite FB, KS in Hz. clear - Hz TD PK Hc. lia. }
assert (AGFS : agree_on asegs (in_sh (fa_beg (ae_L RE) c, kFreeArraySize)) m m').
{ eapply agree_on_mono; [exact AG|]. intros z Hz. split; [do 3 right; left; exact Hz| apply NPC]. unfold in_sh in Hz. cbn [fst snd] in Hz.
rewrite FB, KS in Hz. unfold SH, A_SHADOW_OFS in Hz. clear - Hz TD PK PCH PH TK Hc. Z.div_mod_to_equations. lia. }
split; [exact TI|]. split; [exists CH; split; [exact ACH| split; [exact LCH| apply HCH; lia]]|].
split; [| split].
2:{ eapply hjunk_wmono; [exact (SL i TCached TI eq_refl)| exact WM]. }
2:{ pose proof (cr_user_agree a G RE m m' c (K c) PU (conj SL (conj UT (conj SS (conj US UJ)))) ltac:(lia) AGU) as (_ & _ & SS' & _).
exact (SS' i TCached TI eq_refl). }
intros t NP.
exists (fun c0 => if c0 =? c then mkPK (pk_fl (K c)) (firstn n1 CA) else K c0).
split; [eapply hjunk_wmono; [exact HJS| exact WM]|]. split.
{ intros c0 NE0. apply GNE. destruct (Z.eq_dec c0 c) as [->|NE]; [| rewrite set_tag_other_class in NE0 by exact NE; exact NE0].
intros E. apply NE0. apply length_zero_iff_nil. pose proof (ncarved_set_tag c i t G c) as NC. unfold ncarved in NC.
rewrite <- Nat2Z.inj_iff. rewrite NC, E. reflexivity. }
intros c0 Hc0. destruct (Z.eqb_spec c0 c) as [->|NE].
2:{ eapply class_rep_ext; [| apply EO; exact NE| rewrite EI, EI'; reflexivity| apply set_tag_other_class; exact NE].
eapply class_rep_agree; [apply HCall; exact Hc0| rewrite K32 in Hc0; exact Hc0| apply OTH; [exact Hc0| exact NE]]. }
apply class_rep_split. split; [| split].
- unfold cr_cells. rewrite Ea, EI'. cbn [pk_ca set_count c_count c_num_freed c_mapped_fa c_alloc_user c_mapped_user].
split; [| split].
+ exists j1, j2, j3, j4. eapply rw_cells_agree; [exact AG| exact RI|]. intros z Hz. cbn [ri_cells cells_size csize Nat.add] in Hz.
split; [left; exact Hz| apply NPC]. unfold ri_addr in Hz. rewrite RIq in Hz. clear - Hz TD PK Hc. lia.
+ apply (proj2 (rw_cells_app asegs _ _ [C4 (wz (cnt - 1))] _)). cbn [cells_size csize Nat.add]. split; [exact PCk|].
cbv beta delta [pc_cells] in PC. rewrite EI in PC. apply (proj1 (rw_cells_app asegs _ _ [C4 (wz cnt)] _)) in PC as [_ PCt].
cbn [cells_size csize Nat.add] in PCt. eapply rw_cells_agree; [exact AG| exact PCt|]. intros z Hz. cbn [cells_size csize Nat.add] in Hz.
split; [right; left; lia| lia].
+ exists CH. split; [| split; [exact LCH|]].
* eapply u32arr_agree; [exact AG| exact ACH|]. intros z Hz. rewrite LCH in Hz. split; [right; left; cbn in Hz; lia| cbn in Hz; lia].
* intros j Hj. rewrite length_firstn in Hj. rewrite HCH by lia. rewrite nth_firstn. replace (Nat.ltb j n1) with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
- apply (cr_pure_pop a a' G c (K c) t PU ltac:(lia) CNT NP Ea EI').
- intros _. rewrite Ea. cbn [pk_fl set_count c_count c_num_freed c_mapped_fa c_alloc_user c_mapped_user].
split; [eapply u32arr_agree; [exact AGFA| exact FA|]; intros z Hz; rewrite length_map, P1 in Hz; pose proof PU as (_&_&_&_&_&_&_&_&_&_&_& P12 & P13 &_); lia|].
split; [eapply hjunk_wmono; [exact FJ| exact WM]|]. split; [| eapply hjunk_wmono; [exact FS| exact WM]].
eapply (cr_user_retag a a' G); [| | rewrite Ea; reflexivity| rewrite Ea; reflexivity].
+ eapply cr_user_agree; [exact PU| exact (conj SL (conj UT (conj SS (conj US UJ))))| lia| exact AGU].
+ intros i' t' Ht' Hp'. destruct (Z.eq_dec i' i) as [->|NE].
* rewrite (tag_at_set_tag_eq G c i t TCached TI) in Ht'. inversion Ht'; subst t'. rewrite NP in Hp'. discriminate.
* rewrite tag_at_set_tag_ne in Ht'; [exists t'; split; assumption| exact I0| right; exact NE].
Qed.

Section Model.
Variable L : ALay.
Local Notation TT := (fun (_ : evA) (_ : ansA) => True).

Lemma get_from_allocator_inited a c k :
tall TT (okrel (fun r => as_cache_inited (snd r) = as_cache_inited a)) (get_from_allocator L a c k).
Proof.
eapply tall_mono; [apply get_from_allocator_prel|]. intros [[b s1]| |w]; cbn; try exact (fun x => x).
intros (_ & EI & _). exact EI.
Qed.

Lemma refill_facts a c :
tall TT (okrel (fun r => as_cache_inited (snd r) = true /\ (fst r = true -> c_count (cls (snd r) c) = max_count c / 2))) (refill L a c).
Proof.
unfold refill. eapply tall_bind_ok with (P1 := fun r => as_cache_inited (snd r) = true).
{ eapply tall_mono; [apply get_from_allocator_inited|]. intros [[b s1]| |w]; cbn; exact (fun x => x). }
intros [ok s1] H1. cbn in H1. destruct ok; cbn [negb]; apply tall_ret; cbn.
- split; [exact H1|]. intros _. unfold upd_cls. rewrite cls_set_cls_eq. reflexivity.
- split; [exact H1| intros E; discriminate].
Qed.
End Model.
End Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg Q61C QbcP_c1 QWRO QFQR QKBN QN4c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QTVW.Mqc.
Import Qc27 Qc6I QJFf QVsB QDM6.
Import QCiC.Mq1 Qpj5.Mq1 QdZp.
Import Q13u QHig QwAs.Mq2 Q0Do.
Import Q6sh QKTr.
Import QJBH.
Import QZzg QTVW Q61C QbcP_c1 QWRO QFQR QmP7 QKBN QN4c QNQk.Mq8 QNQk QpY2.Mqf.
Import Q9Ho.
Import QTVW.Mqb Qu3b.Mq5 QYyZ.Mq9 QnRU QteI.Mqb Qu3b.Mq4.
Import QlES.
Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A.
Local Unset Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

Definition memcpy_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Dst Src N : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(Dst, Dst + N)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' Dst [CB (Z.to_nat N) src]
/\ bytes_at asegs m' Src src.

Definition fwx_saves_post {BAND : Band} (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) : machine_state -> Prop :=
fun ms' => exists (m' : mem) (j8 : list byte),
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 a2 a1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd5ab4) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ stk asegs m' lo (bv_unsigned sp + -64).

Lemma fwx_saves {BAND : Band} : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> 0 <= lo -> mem_inv asegs m ->
evt asegs (fwx_saves_post ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd5a8c) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros ST LO LO0 MI.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
carve_frame 64%nat ST.
do 10 step.
apply evt_done. unfold fwx_saves_post. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FR| exact ST].
Qed.

Definition fwx_nofit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp S l wfn lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 wfn) t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 S) (Z_to_bv 64 l) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 wfn) fc None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp).

Lemma fwx_nofit : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(Fp : Z) (flags : word) (wend wpos wbase wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) (S l lo : Z),
rw_cells asegs m Fp (file_cells flags wend wpos wbase wfn bufp bufsize fd mode lbf tail) ->
a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 l -> a2 = Z_to_bv 64 Fp ->
(0 < wend < 2^64) -> (0 <= wpos <= wend) -> (wend - wpos < l < 2^64) -> (0 <= S < 2^64) -> (0 <= wfn < 2^64) -> (wfn mod 2 = 0) ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 64) -> (0 <= lo) ->
mem_inv asegs m ->
(Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
evt asegs (fwx_nofit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp S l wfn lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd5a8c) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros FC -> -> -> WEND WPOS L SR WFN WFE ST LO LO0 MI SEPF.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
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
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' Fp (file_cells flags wend (wpos + l) wbase wfn bufp bufsize fd mode lbf tail)
/\ rw_cells asegs m' wpos [CB (length src) src; CB (cap - length src) (skipn (length src) junk)]
/\ bytes_at asegs m' S src.

Lemma fwx_tail {BAND : Band} : forall (x1 ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(s0v s1v s2v s3v s4v s5v : word) (j8 : list byte)
(F : bvmap 5 word) (fc : bv 32) (m0 m : mem)
(Fp : Z) (flags : word) (wend wpos wbase wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte)
(cap : nat) (junk src : list byte) (S l i lo : Z),
rw_cells asegs m (bv_unsigned sp + -64) [CB 8 j8; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
rw_cells asegs m Fp (file_cells flags wend wpos wbase wfn bufp bufsize fd mode lbf tail) ->
rw_cells asegs m wpos [CB cap junk] -> (length src <= cap)%nat ->
bytes_at asegs m S src -> Z.of_nat (length src) = l ->
stk asegs m lo (bv_unsigned sp + -64) -> (0 <= lo <= bv_unsigned sp - 64) -> (bv_unsigned sp <= 2^47) ->
munch [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)] m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
(0 <= Fp) -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
(0 <= wpos) -> (wpos + Z.of_nat cap < 2^64) -> (wpos + Z.of_nat cap <= lo \/ bv_unsigned sp <= wpos) ->
(wpos + Z.of_nat cap <= Fp \/ Fp + 232 <= wpos) ->
(S + l <= wpos \/ wpos + l <= S) -> (S + l <= lo \/ bv_unsigned sp <= S) -> (S + l <= Fp + 40 \/ Fp + 48 <= S) ->
(0 <= i) -> (i + l < 2^63) -> (S < 2^64) ->

(band_lo <= lo) -> (lo <= bv_unsigned sp - QnRU.Mqf.FWRITEX_STACK) ->
shadow_base asegs m -> rt_consts_at asegs m -> rng_ok m S l -> rng_ok m wpos l ->
evt asegs (fwx_ret_post ra sp gp tp s0v s1v s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 F fc
Fp flags wend wpos wbase wfn bufp bufsize fd mode lbf tail cap junk src S l (i + l) lo m0)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 l)
(Z_to_bv 64 wpos) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 i) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd5b84) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros FR FC DST CAP SRC LEN ST LO0 SPHI MU WM MI Fp0 SEPF W0 WHI SEPW1 SEPW2 SEPS1 SEPS2 SEPS3 I0 IL SHI CEIL LOI SB RC RS RD.
pose proof CEIL as CEIL'. idtac. unfold QnRU.Mqf.FWRITEX_STACK, MEMCPY_ICPT_STACK in LOI.
pose proof (rw_cells_bound _ _ _ _ DST) as BD. cbn [cells_size csize Nat.add] in BD. rewrite Nat.add_0_r in BD.
assert (LJ : length junk = cap) by (destruct DST as [[WF _] _]; cbn in WF; exact (proj1 WF)).
pose proof (rw_cells_bound _ _ _ _ FC) as BF.
pose proof (bytes_at_bound _ _ _ _ SRC) as BS.
unfold file_cells in FC.

apply (rw_cells_split_CB asegs _ _ [] cap junk [] [length src; cap - length src]%nat) in DST; [ | cbn; lia ].
cbn [mk_CB_cells app] in DST.
apply (proj1 (QnRU.Mqf.rw_cells_app asegs _ _ [_] _)) in DST. destruct DST as [DSTa DSTb].
cbn [cells_size csize Nat.add] in DSTb. rewrite Nat.add_0_r in DSTb.
step. step. step.
replace (Z_to_bv 64 l : word) with (Z_to_bv 64 (Z.of_nat (length src)) : word) by (rewrite LEN; reflexivity).
assert (SEPfr : bv_unsigned sp + -64 + 64 <= wpos \/ wpos + Z.of_nat (length src) <= bv_unsigned sp + -64) by lia.
rewrite <- LEN in RS, RD.
call_u (memcpy_icpt_spec wpos S (Z.of_nat (length src)) lo src (firstn (length src) junk));
[ exact SRC| rewrite Nat2Z.id; reflexivity| rewrite Nat2Z.id; exact DSTa| lia| exact MI| lia
| unsigned_lits; exact ST| exact CEIL| unsigned_lits; unfold MEMCPY_ICPT_STACK; lia| unsigned_lits; lia| unsigned_lits; lia
| exact SB| exact RC| exact RS| exact RD|].
rewrite ?(unsigned_lit wpos), ?(unsigned_lit S), ?(unsigned_lit (Z.of_nat (length src))) in * by lia.
rewrite !Nat2Z.id in *.
match goal with Hd : rw_cells asegs _ wpos [CB (length src) src] |- _ => rename Hd into DSTa' end.
do 4 step.
do 9 step.
match goal with STa : stk asegs ?mc lo (bv_unsigned sp + -64)%Z, FRx : rw_cells asegs ?mc (bv_unsigned sp + -64)%Z _ |- _ =>
release_frame FRx STa (bv_unsigned sp) end.
rewrite firstn_all2 in DSTb by (rewrite length_skipn; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (DST' : rw_cells asegs mm wpos ([CB (length src) src] ++ [CB (cap - length src)%nat (skipn (length src) junk)]))
by (apply (proj2 (QnRU.Mqf.rw_cells_app asegs _ _ [_] _)); split; [exact DSTa'|]; cbn [cells_size csize]; rewrite Nat.add_0_r; exact DSTb)
end.
cbn [app] in DST'. rewrite !LEN in *.
unfold fwx_ret_post, file_cells. sys_finish.
Qed.

Lemma fwx_fit_plain {BAND : Band} : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(Fp : Z) (flags : word) (wend wpos wbase wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte)
(cap : nat) (junk src : list byte) (S l lo : Z),
rw_cells asegs m Fp (file_cells flags wend wpos wbase wfn bufp bufsize fd mode lbf tail) ->
rw_cells asegs m wpos [CB cap junk] -> Z.of_nat cap = wend - wpos ->
bytes_at asegs m S src -> Z.of_nat (length src) = l ->
a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 l -> a2 = Z_to_bv 64 Fp ->
(0 < wend < 2^64) -> (0 <= wpos) -> (l <= wend - wpos) -> (S < 2^64) ->
(2^31 <= lbf < 2^32) ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 64) -> (0 <= lo) -> (bv_unsigned sp <= 2^47) ->
mem_inv asegs m ->
(0 <= Fp) -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
(wend <= lo \/ bv_unsigned sp <= wpos) -> (wend <= Fp \/ Fp + 232 <= wpos) ->
(S + l <= wpos \/ wend <= S) -> (S + l <= lo \/ bv_unsigned sp <= S) -> (S + l <= Fp \/ Fp + 232 <= S) ->
(band_lo <= lo) -> (lo <= bv_unsigned sp - 64 - QnRU.Mqf.FWRITEX_STACK) ->
shadow_base asegs m -> rt_consts_at asegs m -> rng_ok m S l -> rng_ok m wpos l ->
evt asegs (fwx_ret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
Fp flags wend wpos wbase wfn bufp bufsize fd mode lbf tail cap junk src S l l lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd5a8c) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros FC DST CAPE SRC LEN -> -> -> WEND W0 FIT SHI LBF ST LO LO0 SPHI MI Fp0 SEPF SEPW1 SEPW2 SEPS1 SEPS2 SEPS3 CEIL LOI SB RC RS RD.
pose proof CEIL as CEIL'. idtac.
pose proof (bytes_at_bound _ _ _ _ SRC) as BS. pose proof (proj1 (proj2 RD)) as WP47.
pose proof (munch_refl [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)] m) as MU.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUs.
pose proof (wmono_refl asegs m) as WM.
unfold file_cells in FC.
carve_frame 64%nat ST.
do 13 step.
if_cases Hw; zify_cond Hw. 1:{ exfalso. lia. }
do 3 step.
if_cases Hr; zify_cond Hr. 2:{ exfalso. rewrite land_W64, Z.mod_small in Hr by lia. lia. }
do 3 step.
pose proof (QnRU.Mqf.sx32_neg (Z_to_bv 64 lbf)) as NEG. rewrite unsigned_lit in NEG by lia. rewrite Z.mod_small in NEG by lia.
specialize (NEG ltac:(lia)).
if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (shadow_base_munch _ _ _ SB MUs ltac:(rt_wzones)) as SB1;
pose proof (rt_consts_at_munch _ _ _ RC MUs WM ltac:(rt_wzones)) as RC1;
assert (RS1 : rng_ok mc S l)
by (eapply rng_ok_munch; [exact RS| exact MUs| exact WM|]; apply Forall_cons; [| apply Forall_nil]; cbn [fst snd]; rewrite !SH_eq;
left; pose proof (proj1 (proj2 RS)); clear - H CEIL' BS; Z.div_mod_to_equations; lia);
assert (RD1 : rng_ok mc wpos l)
by (eapply rng_ok_munch; [exact RD| exact MUs| exact WM|]; apply Forall_cons; [| apply Forall_nil]; cbn [fst snd]; rewrite !SH_eq;
left; pose proof (proj1 (proj2 RD)); clear - H CEIL' BS W0; Z.div_mod_to_equations; lia)
end.
clear MUs.
eapply fwx_tail; [exact FR | exact FC | exact DST | lia | exact SRC | exact LEN | exact ST | lia | lia | exact MU | exact WM | exact MI | lia .. | exact SB1 | exact RC1 | exact RS1 | exact RD1].
Qed.
End Mq7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWHo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QTVW.Mqc.
Import Q13u Qc6I QJFf QVsB.
Import QCiC.Mq1 Qpj5.Mq1. Import QCNF QoNr.Mq0. Import QdZp Qk8e.Mq0.
Import Qu3b.Mq6.
Import QTVW.Mq8 Qu3b.Mq5 QnRU.Mqf QnRU QteI.Mqb.
Import QCNF.Mq2.
Import QoBx.Mq0 Qu3b.Mq4.
Import QWHo. Import QJBH.
Import QHig QwAs.Mq2 Q0Do.
Import Q6sh QKTr.
Import QZzg QTVW Q61C QbcP_c1 QWRO QFQR QmP7 QKBN QN4c QNQk.Mq8 QNQk QpY2.Mqf.
Import Q9Ho.
Import QYyZ.Mq9 QFd5 QteI.
Import QlES. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A.
Local Set Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Notation mem := (word -> option byte).

Definition OUT_DEPTH : Z := 3264.
Definition PC_DEPTH : Z := 5184.
Definition VF_DEPTH : Z := 5552.
Definition GLOBALS_TOP {BAND : Band} : Z := band_lo.
Definition STATIC_SPLIT : Z := 0x230c0.

Section Sink.
Context {BAND : Band}.
Context {St : Type}.
Variables (Fp B BS : Z).
Variable SINK : mem -> St -> Prop.
Variable TOPOK : Z -> Prop.
Variable OUT : list Z -> M St unit.
Variable OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z.

Definition SR : list (Z * Z) := [(Fp, Fp + 232); (B, B + BS)].

Definition sink_frame_stmt : Prop :=
forall (W : list (Z * Z)) (m m' : mem) (st : St),
SINK m st -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= Fp \/ Fp + 232 <= fst iv) W ->
Forall (fun iv => snd iv <= B \/ B + BS <= fst iv) W ->
Forall (fun iv => GLOBALS_TOP <= fst iv) W ->
SINK m' st.

Definition sink_flags_stmt : Prop :=
forall m st, SINK m st -> exists fl : byte, rw_cells asegs m Fp [CB 1 [fl]] /\ Z.land (bv_unsigned fl) 32 = 0 /\ ISH m.

Definition topok_stmt : Prop := forall a b, a <= b -> TOPOK b -> TOPOK a.

Definition sink_ish_stmt : Prop := forall m st, SINK m st -> ISH m.

Definition out_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(S : Z) (bs : list Z) (lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch ((lo, bv_unsigned sp) :: SR) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ SINK m' st'
/\ ssp_cells m' canary
/\ bytes_at asegs m' S (zb bs).

Definition out_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (bs : list Z) (lo : Z) (canary : word),
SINK m st ->
bytes_at asegs m (bv_unsigned a0) (zb bs) ->
Forall (fun c => 0 <= c < 256) bs -> zlength bs < 2^31 ->
szone (bv_unsigned a0) (zlength bs) ->
a1 = Z_to_bv 64 (zlength bs) ->
a2 = Z_to_bv 64 Fp ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - OUT_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned sp <= 2^47) -> TOPOK (bv_unsigned sp) ->
ssp_cells m canary ->
mem_inv asegs m ->
(Fp + 232 <= lo \/ bv_unsigned sp <= Fp) -> (B + BS <= lo \/ bv_unsigned sp <= B) ->
(bv_unsigned a0 + zlength bs <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
(bv_unsigned a0 + zlength bs <= Fp \/ Fp + 232 <= bv_unsigned a0) ->
(bv_unsigned a0 + zlength bs <= B \/ B + BS <= bv_unsigned a0) ->
(bv_unsigned a0 + zlength bs <= 2^47) ->
implM asegs (OUT bs) st
(out_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) bs lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd5a8c) fc None m (seg_rom asegs)).

Definition fpcall_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(lo : Z) (canary : word) (m : mem) : Z -> St -> machine_state -> Prop :=
fun r st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch ((lo, bv_unsigned sp) :: SR) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ frm0 fc'
/\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
/\ stk asegs m' lo (bv_unsigned sp)
/\ SINK m' st'
/\ ssp_cells m' canary.

Definition fpcall_stmt (c : Z * Z * Z * Z * Z) : Prop :=
let '(y, w, p, fl, t) := c in
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word),
SINK m st ->
y = bv_unsigned a1 + 2^64 * bv_unsigned a2 ->
a0 = Z_to_bv 64 Fp -> a3 = Z_to_bv 64 w -> a4 = Z_to_bv 64 p -> a5 = Z_to_bv 64 fl -> a6 = Z_to_bv 64 t ->
bv_unsigned a7 <> 5 ->
(-2^31 <= w <= 1) -> (-2^31 <= p < 2^20) -> (0 <= fl < 2^32) -> (0 <= t < 256) -> Z.lor t 32 <> 97 ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FMT_FP_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned sp <= 2^47) -> TOPOK (bv_unsigned sp) ->
ssp_cells m canary ->
mem_inv asegs m -> frm0 fc ->
(Fp + 232 <= lo \/ bv_unsigned sp <= Fp) -> (B + BS <= lo \/ bv_unsigned sp <= B) ->
implM asegs (OUTFP y w p fl t) st
(fpcall_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd7108) fc None m (seg_rom asegs)).

Definition arg_ok (m : mem) (lo sp ap : Z) (slot : word) (a : parg) : Prop :=
match a with
| PA_s s => exists slack : list byte,
bytes_at asegs m (bv_unsigned slot) (zb s ++ Z_to_bv 8 0 :: slack)
/\ Forall (fun c => 0 < c < 256) s
/\ ((- (bv_unsigned slot + zlength s + 1)) mod 8 <= zlength slack)
/\ 0 < bv_unsigned slot
/\ szone (bv_unsigned slot) (zlength s + 1)
/\ (bv_unsigned slot + zlength s + 1 + zlength slack <= lo \/ sp <= bv_unsigned slot)
/\ (bv_unsigned slot + zlength s + 1 + zlength slack <= Fp \/ Fp + 232 <= bv_unsigned slot)
/\ (bv_unsigned slot + zlength s + 1 + zlength slack <= B \/ B + BS <= bv_unsigned slot)
/\ (bv_unsigned slot + zlength s + 1 + zlength slack <= ap \/ ap + 8 <= bv_unsigned slot)
/\ bv_unsigned slot + zlength s + 1 + zlength slack <= 2^47
| PA_i i => -2^31 <= i < 2^31 /\ bv_unsigned slot mod 2^32 = i mod 2^32
| PA_u u => 0 <= u < 2^32 /\ bv_unsigned slot mod 2^32 = u
| PA_g d => bv_unsigned slot = d
end.
Fixpoint args_ok (m : mem) (lo sp ap : Z) (slots : list word) (args : list parg) : Prop :=
match args with
| [] => True
| a :: args' => match slots with
| [] => False
| w :: slots' => arg_ok m lo sp ap w a /\ args_ok m lo sp ap slots' args'
end
end.

Definition printf_core_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(AP lo : Z) (canary : word) (m : mem) : Z -> St -> machine_state -> Prop :=
fun r st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (apv : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch ((lo, bv_unsigned sp) :: (AP, AP + 8) :: SR) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ frm0 fc'
/\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
/\ stk asegs m' lo (bv_unsigned sp)
/\ SINK m' st'
/\ ssp_cells m' canary
/\ rw_cells asegs m' AP [C8 apv]
/\ (0 <= r <= INT_MAX).

Definition printf_core_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word)
(fmt : list Z) (VA i : Z) (slots : list word) (args : list parg),
SINK m st ->
bytes_at asegs m (bv_unsigned a1) (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt ->
a0 = Z_to_bv 64 Fp ->
rw_cells asegs m (bv_unsigned a2) [C8 (Z_to_bv 64 (VA + 8 * i))] ->
va_area m VA slots -> 0 <= i -> args_ok m lo (bv_unsigned sp) (bv_unsigned a2) (skipn (Z.to_nat i) slots) args ->
Forall fpcall_stmt (fp_calls (length fmt) fmt args) ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - PC_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned sp + 16 <= 2^47) -> TOPOK (bv_unsigned sp) ->
ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->

(bv_unsigned a1 + zlength fmt <= STATIC_SPLIT) -> szone (bv_unsigned a1) (zlength fmt) -> (0 <= BS) ->
((954304 <= Fp /\ Fp + 232 <= 6575456) \/ (bv_unsigned a2 + 8 <= Fp /\ Fp + 232 <= VA)) ->
((6576024 <= B /\ B + BS <= lo) \/ (bv_unsigned a2 + 8 <= B /\ B + BS <= VA)) ->
(bv_unsigned sp <= bv_unsigned a2) -> (bv_unsigned a2 + 8 <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
implM asegs (printf_model OUT OUTFP fmt args) st
(printf_core_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (bv_unsigned a2) lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd60d0) fc None m (seg_rom asegs)).
End Sink.

Definition printf_core1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ ssp_cells m' canary.

Definition printf_core1_stmt {BAND : Band} : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (canary : word) (fmt : list Z),
bytes_at asegs m (bv_unsigned a1) (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt ->
pass1_ok fmt = true ->
a0 = Z_to_bv 64 0 ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - PC_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned sp + 16 <= 2^47) ->
ssp_cells m canary -> mem_inv asegs m ->
(bv_unsigned a1 + zlength fmt <= STATIC_SPLIT) -> szone (bv_unsigned a1) (zlength fmt) ->
(bv_unsigned sp <= bv_unsigned a2) -> (bv_unsigned a2 + 8 <= 2^64) ->
evt asegs (printf_core1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd60d0) fc None m (seg_rom asegs)).

Definition TOPOK_none (sp : Z) : Prop := sp + 16 <= 2^47.

Definition OUT_MAX : Z := 16777216.

Section StderrSink.
Context {BAND : Band}.
Context {St : Type}.
Variable B : Z.

Definition SINK_stderr (m : mem) (bs : list Z * St) : Prop :=
let buf := fst bs in
exists (flags mode : word) (tail : list byte) (rest : list byte),
rw_cells asegs m RSTDERR (file_cells flags (B + 80) (B + zlength buf) B F_STDIO_WRITE B 80 2 mode 0xffffffff tail)
/\ Z.land (bv_unsigned flags) 32 = 0 /\ Z.land (bv_unsigned flags) 8 = 0
/\ rw_cells asegs m B [CB 80 (zb buf ++ rest)]
/\ zlength buf + zlength rest = 80
/\ B + 80 < 2^63 /\ GLOBALS_TOP + 64 <= B /\ B + 96 <= 2^47
/\ ISH m.

Definition OUT_stderr (s : list Z) : M (list Z * St) unit :=
fun bs => let '(buf, st) := bs in
if OUT_MAX <? zlength s then Qc6I.Ret Unr
else if INTERNAL_BUFSIZ - zlength buf <? zlength s
then ebind (stdio_writev 2 buf s st) (fun r => Qc6I.Ret (Ok (tt, ([], snd r))))
else Qc6I.Ret (Ok (tt, (buf ++ s, st))).
Definition OUTFP_stderr (y w p fl t : Z) : M (list Z * St) Z := fun _ => Qc6I.Ret Unr.
End StderrSink.

Section StdoutSink.
Context {BAND : Band}.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

Definition SINK_stdout (m : mem) (st : St) : Prop :=
let so := get_so st in
so_active so = true /\
exists (flags mode : word) (tail bufbytes : list byte),
rw_cells asegs m RSTDOUT
(file_cells flags (RSTDOUT_BUF + 1024) (RSTDOUT_BUF + zlength (so_buf so)) RSTDOUT_BUF
(if so_first so then F_STDOUT_WRITE else F_STDIO_WRITE)
RSTDOUT_BUF 1024 1 mode
(if so_lbf_nl so then 10 else 0xffffffff) tail)
/\ Z.land (bv_unsigned flags) 104 = 0
/\ rw_cells asegs m RSTDOUT_BUF [CB 1024 bufbytes]
/\ firstn (length (so_buf so)) bufbytes = to_bytes (so_buf so)
/\ zlength (so_buf so) <= 1024
/\ ISH m.
Definition OUTFP_stdout (y w p fl t : Z) : M St Z := fun _ => Qc6I.Ret Unr.

Definition OUT_stdout (s : list Z) : M St unit :=
if OUT_MAX <? zlength s then munr else stdout_fwritex get_so set_so s.
End StdoutSink.

Definition stderr_wfile (m : mem) : Prop :=
exists (flags mode : word) (e wend : Z) (tail : list byte),
rw_cells asegs m RSTDERR (file_cells flags wend e e F_STDIO_WRITE 0x645ca0 0 2 mode 0xffffffff tail)
/\ Z.land (bv_unsigned flags) 40 = 0.

Definition fwritex_stderr_stmt {BAND : Band} : Prop :=
forall (St : Type) (B : Z),
@out_stmt _ (list Z * St) RSTDERR B 80 (SINK_stderr B) TOPOK_none OUT_stderr.

Definition fwritex_stdout_stmt {BAND : Band} : Prop :=
forall (St : Type) (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St),
(forall s so, get_so (set_so so s) = so) -> (forall s so so', set_so so' (set_so so s) = set_so so' s) ->
@out_stmt _ St RSTDOUT RSTDOUT_BUF 1024 (SINK_stdout get_so) TOPOK_none (OUT_stdout get_so set_so).

Definition stdio_write_flush_post {BAND : Band} {St : Type} (B : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(F : bvmap 5 word) (fc : bv 32) (lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232); (B, B + 80)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ SINK_stderr B m' ([], st')
/\ ssp_cells m' canary.
Definition stdio_write_flush_stmt {BAND : Band} : Prop :=
forall (St : Type) (B : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (buf : list Z) (st : St) (lo : Z) (canary : word),
SINK_stderr B m (buf, st) ->
a0 = Z_to_bv 64 RSTDERR -> a2 = Z_to_bv 64 0 ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - OUT_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned sp <= 2^47) -> (B + 80 <= lo \/ bv_unsigned sp <= B) ->
ssp_cells m canary -> mem_inv asegs m ->
bv_unsigned a1 <= 2^47 ->
implM asegs (stdio_writev 2 buf [] : M St unit) st
(stdio_write_flush_post B ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd5094) fc None m (seg_rom asegs)).

Definition towrite_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(flags mode : word) (wend wpos wbase writefn buf bufsize fd lbf : Z) (tail : list byte),
rw_cells asegs m (bv_unsigned a0) (file_cells flags wend wpos wbase writefn buf bufsize fd mode lbf tail) ->
Z.land (bv_unsigned flags) 8 = 0 ->
(0 <= buf) -> (buf + bufsize < 2^64) -> (0 <= bufsize) ->
mem_inv asegs m ->
evt asegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mode' : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned a0, bv_unsigned a0 + 232)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' (bv_unsigned a0) (file_cells flags (buf + bufsize) buf buf writefn buf bufsize fd mode' lbf tail))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd5a38) fc None m (seg_rom asegs)).

Definition EMIT_DEPTH : Z := 5728.
Section Emit.
Context {BAND : Band}.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

Definition emit_printf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ frm0 fc'
/\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
/\ stk asegs m' lo (bv_unsigned sp)
/\ stdout_file m' (get_so st')
/\ ssp_cells m' canary.

Definition emit_printf_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word) (v : Z),
(forall x so, get_so (set_so so x) = so) -> (forall x so so', set_so so' (set_so so x) = set_so so' x) ->
fwritex_stdout_stmt ->
stdout_file m (get_so st) -> ISH m ->
(-2^31 <= v < 2^31) -> (bv_unsigned a1 mod 2^32 = v mod 2^32) ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - EMIT_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned sp + 16 <= 2^47) ->
ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
implM asegs (s_emit get_so set_so v) st
(emit_printf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x91e28) fc None m (seg_rom asegs)).

Definition FPRINTF_DEPTH : Z := 5664.

Definition AFMT_emit_d : Z := 0x14f44.      Definition AFMT_usage : Z := 0x16263.
Definition AFMT_too_big : Z := 0x1a8f3.     Definition AFMT_cannot_open : Z := 0x1ef3c.
Definition AFMT_read_error : Z := 0x1ef51.

Definition diag_args (d : diag_msg) (m : mem) (fmtp argw : word) (lo sp : Z) : Prop :=
match d with
| DUsage s | DCannotOpen s | DReadError s =>
fmtp = Z_to_bv 64 (match d with DUsage _ => AFMT_usage | DCannotOpen _ => AFMT_cannot_open | _ => AFMT_read_error end)
/\ exists slack : list byte,
bytes_at asegs m (bv_unsigned argw) (zb s ++ Z_to_bv 8 0 :: slack)
/\ Forall (fun c => 0 < c < 256) s
/\ ((- (bv_unsigned argw + zlength s + 1)) mod 8 <= zlength slack)
/\ (zlength s <= OUT_MAX)
/\ (bv_unsigned argw + zlength s + 1 + zlength slack <= lo \/ sp <= bv_unsigned argw)
/\ (GLOBALS_TOP + 64 <= bv_unsigned argw) /\ (bv_unsigned argw + zlength s + 9 <= 2^47)
/\ (bv_unsigned argw + zlength s + 1 + zlength slack <= 2^47)
| DTooBig => fmtp = Z_to_bv 64 AFMT_too_big /\ bv_unsigned argw mod 2^32 = 67108864
| _ => False
end.

Definition fprintf_diag_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(lo : Z) (canary : word) (m : mem) (st : St) : unit -> St -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ frm0 fc'
/\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
/\ stk asegs m' lo (bv_unsigned sp)
/\ stderr_wfile m'
/\ ssp_cells m' canary
/\ st' = st.

Definition fprintf_diag_stmt : Prop :=
forall (d : diag_msg)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word),
fwritex_stderr_stmt -> stdio_write_flush_stmt ->
stderr_wfile m -> ISH m ->
a0 = Z_to_bv 64 RSTDERR -> diag_args d m a1 a2 lo (bv_unsigned sp) ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned sp + 16 <= 2^47) ->
ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
implM asegs (s_diag (St:=St) d) st
(fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x4fd70) fc None m (seg_rom asegs)).
End Emit.

End Mq8.

Module Mq9.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String Stdlib.Strings.Ascii.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do Qc6I QJFf QVsB QJFf.Mq0.
Import QCiC.Mq1 Qpj5.Mq1 QdZp Q6sh QKTr.
Import QJBH.
Import QZzg QTVW Q61C QbcP_c1 QWRO QFQR QmP7 QKBN QN4c QNQk.Mq8 QNQk QpY2.Mqf.
Import Q9Ho.
Import QteI.Mqb.
Import Q0z1.
Import QlES. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_1 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_2 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Ltac addr_diff E A ::=
let k :=
lazymatch E with
| Z.add ?X ?c1 =>
lazymatch A with
| Z.add X ?c2 => let c1 := zlit c1 in let c2 := zlit c2 in eval vm_compute in (c1 - c2)%Z
| X => zlit c1
| _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
end
| _ =>
lazymatch A with
| Z.add E ?c2 => let c2 := zlit c2 in eval vm_compute in (- c2)%Z
| E => constr:(0%Z)
| _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
end
end in
let ok := eval vm_compute in (Z.ltb k 65536) in
lazymatch ok with true => k end. Ltac mkr__addr_diff_3 E A := let k :=
lazymatch E with
| Z.add ?X ?c1 =>
lazymatch A with
| Z.add X ?c2 => let c1 := zlit c1 in let c2 := zlit c2 in eval vm_compute in (c1 - c2)%Z
| X => zlit c1
| _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
end
| _ =>
lazymatch A with
| Z.add E ?c2 => let c2 := zlit c2 in eval vm_compute in (- c2)%Z
| E => constr:(0%Z)
| _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
end
end in
let ok := eval vm_compute in (Z.ltb k 65536) in
lazymatch ok with true => k end.

Ltac has_var c := match c with context [?x] => is_var x end.
Ltac bif := try (lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
tryif has_var c then idtac else
(let v := eval vm_compute in c in
lazymatch v with
| true => replace c with true by (vm_compute; reflexivity); cbv iota
| false => replace c with false by (vm_compute; reflexivity); cbv iota
end) end).

Ltac subfix := repeat match goal with |- context [Z_to_bv 64 (?x - ?k)] => is_Zlit k; let nk := eval vm_compute in (- k)%Z in replace (x - k)%Z with (x + nk)%Z by lia end.
Lemma zx8_lit : forall e, 0 <= e < 2^64 -> zx8 (Z_to_bv 64 e) = Z_to_bv 64 (e mod 256).
Proof. intros e He. unfold zx8. rewrite unsigned_lit by lia. reflexivity. Qed.

Ltac bnorm :=
repeat match goal with
| |- context [zx8 (Z_to_bv 64 ?e)] => is_Zlit e; rewrite (zx8_lit e) by lia;
let v := eval vm_compute in (e mod 256)%Z in change (e mod 256)%Z with v
| |- context [bv_unsigned (Z_to_bv 64 ?e)] => is_Zlit e;
let v := eval vm_compute in (bv_unsigned (Z_to_bv 64 e)) in change (bv_unsigned (Z_to_bv 64 e)) with v
end.
Ltac bstep := istep; subfix; bnorm; bif.

Ltac run_to pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => bstep end).

Definition pcommon_entry : Z := 0x537a4.
Definition PCOMMON_STACK : Z := 2320.

Definition S_diouxXn : Z := 0x1da50.  Definition S_float : Z := 0x16dde.  Definition S_flags : Z := 0x15cb0.
Definition S_lenmod : Z := 0x1c77b.   Definition S_cCsS : Z := 0x14816.   Definition S_CS : Z := 0x1acf4.
Definition S_csb : Z := 0x1088e.      Definition S_sS : Z := 0x140d6.     Definition K_aa : Z := 0x10480.

Lemma lor_range64 : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> 0 <= Z.lor a b < 2^64.
Proof.
intros a b Ha Hb. pose proof (Z.lor_nonneg a b).
destruct (Z.eq_dec (Z.lor a b) 0) as [E|NE]; [lia|].
split; [lia|]. apply (proj2 (Z.log2_lt_pow2 (Z.lor a b) 64 ltac:(lia))).
rewrite Z.log2_lor by lia. apply Z.max_lub_lt.
- destruct (Z.eq_dec a 0) as [->|Na]; [cbn; lia|]. apply (proj1 (Z.log2_lt_pow2 a 64 ltac:(lia))). lia.
- destruct (Z.eq_dec b 0) as [->|Nb]; [cbn; lia|]. apply (proj1 (Z.log2_lt_pow2 b 64 ltac:(lia))). lia.
Qed.
Lemma lor40_and15 : forall x, Z.land (Z.lor 40 x) 15 <> 0.
Proof.
intros x E. apply (f_equal (fun z => Z.testbit z 3)) in E.
rewrite Z.land_spec, Z.lor_spec, Z.bits_0 in E. cbn in E. discriminate.
Qed.

Definition imemset_bpost (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (d n cur : Z) (k : nat) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz d) (wz 0) (wz (d + n)) (wz (d + n)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(cur, d + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' cur [CB k (repeat (b8 0) k)].

Lemma imemset_bloop : forall (k : nat) ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (d n cur : Z) (rest : list byte),
rw_cells asegs m cur [CB k rest] -> mem_inv asegs m ->
cur + Z.of_nat k = d + n -> (0 < k)%nat -> 0 <= d -> d <= cur -> d + n < 2^64 ->
evt asegs (imemset_bpost ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc d n cur k m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz d) (wz 0) (wz (d + n)) (wz cur) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x75360) fc None m (seg_rom asegs)).
Proof.
induction k as [|k IH]; intros until rest; intros DST MI HK K0 D0 DC DN; [lia|].
assert (LR : length rest = S k) by (destruct DST as [[WF _] _]; cbn in WF; exact (proj1 WF)).
pose proof (munch_refl [(cur, d + n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
apply (rw_cells_split_CB asegs _ _ [] (S k) rest [] [1%nat; k]) in DST; [| cbn; lia]. cbn [mk_CB_cells app] in DST.
step. change (bv_unsigned (wz 0)) with 0 in DST.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in DST. destruct DST as [B0 DST]. cbn [cells_size csize Nat.add Z.of_nat] in DST.
step. step.
destruct k as [|k'].
-
ifF. step. step.
apply evt_done. unfold imemset_bpost. exists m0.
replace (cur + 1) with (d + n) by lia.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
eapply rw_cells_recast'; [exact B0| cbn; split; [reflexivity| exact I]| reflexivity].
- ifT. replace (Z.pos (Pos.of_succ_nat 0)) with 1 in DST by reflexivity.
replace (Z.pos (Pos.of_succ_nat 0)) with 1 in DST by reflexivity.
eapply evt_mono; [eapply (IH ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 d n (cur + 1)); [exact DST| exact MI| lia| lia| lia| lia| lia] |].
cbv beta. intros ms' (m' & -> & MU2 & WM2 & MI2 & Z2). unfold imemset_bpost. exists m'.
split; [reflexivity|].
split. { apply (munch_trans _ m m0 m'); [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn; intros; lia. }
split; [eapply wmono_trans; [exact WM| exact WM2]|]. split; [exact MI2|].
assert (B0' : rw_cells asegs m' cur [C1 (b8 0)]).
{ eapply rw_cells_apart; [exact B0| exact MU2| exact WM2|]. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
pose proof (proj2 (rw_cells_app asegs m' cur [C1 (b8 0)] [CB (S k') (repeat (b8 0) (S k'))]) (conj B0' Z2)) as J.
eapply rw_cells_recast'; [exact J| cbn; split; [| exact I]; cbn; rewrite repeat_length; reflexivity| reflexivity].
Qed.

Definition imemset40_post (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (d : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz d) (wz 0) (wz (d + 40)) (wz (d + 40)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(d, d + 40)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' d [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)].

Lemma imemset40_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (d : Z) (cs : list cell),
rw_cells asegs m d cs -> cells_size cs = 40%nat -> mem_inv asegs m -> d + 40 < 2^64 ->
evt asegs (imemset40_post ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc d m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz d) (wz 0) (wz 40) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x75348) fc None m (seg_rom asegs)).
Proof.
intros until cs; intros DST SZ MI DN.
pose proof (rw_cells_bound _ _ _ _ DST) as BD. rewrite SZ in BD. cbn in BD.
pose proof (rw_cells_merge asegs m d [] cs [] ltac:(cbn [app]; rewrite app_nil_r; exact DST)) as D40.
cbn [app] in D40. rewrite SZ in D40.
assert (L15 : 0 < Z.land (Z.lor 40 d) 15 < 16).
{ pose proof (lor40_and15 d). split; [pose proof (Z.land_nonneg (Z.lor 40 d) 15); lia|].
change 16 with (2^4). replace 15 with (Z.ones 4) by reflexivity. rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
step. step. rewrite ?(unsigned_lit d) by lia. rewrite (unsigned_lit (Z.lor 40 d)) by (apply lor_range64; lia).
step. ifz. step. ifz. step. step.
eapply evt_mono; [eapply (imemset_bloop 40 ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d 40 d); [exact D40| exact MI| lia| lia| lia| lia| lia] |].
cbv beta. intros ms' (m' & -> & MU & WM & MI' & Z40). unfold imemset40_post. exists m'.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
eapply rw_cells_recast'; [exact Z40| cbn; repeat split; exact I| reflexivity].
Qed.

Lemma zb_length : forall l, length (zb l) = length l.
Proof. intros. unfold zb. apply length_map. Qed.
Lemma zb_nth : forall (s : list Z) (t : list byte) i, 0 <= i < zlength s ->
firstn 1 (skipn (Z.to_nat i) (zb s ++ t)) = [b8 (nth (Z.to_nat i) s 0)].
Proof.
intros s t i Hi. unfold zlength in Hi. rewrite skipn_app. unfold zb. rewrite skipn_map.
replace (Z.to_nat i - length (map (λ z : Z, b8 z) s))%nat with 0%nat by (rewrite length_map; lia). cbn [skipn].
destruct (skipn (Z.to_nat i) s) as [|c rest] eqn:E.
- exfalso. apply (f_equal (@length Z)) in E. rewrite length_skipn in E. cbn in E. lia.
- cbn. f_equal. f_equal. rewrite <- (Nat.add_0_r (Z.to_nat i)), <- (nth_skipn _ s 0 0%Z), E. reflexivity.
Qed.
Lemma zb_end : forall (s : list Z) (b : byte) (t : list byte), firstn 1 (skipn (Z.to_nat (zlength s)) (zb s ++ b :: t)) = [b].
Proof.
intros s b t. unfold zlength. rewrite Nat2Z.id, skipn_app. unfold zb. rewrite skipn_all2 by (rewrite length_map; lia).
rewrite length_map, Nat.sub_diag. reflexivity.
Qed.

Section IStrlen.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Variables (p : Z) (s : list Z) (t : list byte).
Hypothesis SRC : bytes_at asegs m p (zb s ++ b8 0 :: t).
Hypothesis BYT : Forall (fun c => 0 < c < 256) s.

Definition istrlen_post : machine_state -> Prop :=
eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (zlength s)) (wz (zlength s + 1)) (wz 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs)).

Lemma istrlen_loop : forall (n : nat) (i : Z) (a2 : word), Z.of_nat n = zlength s - i -> 0 <= i <= zlength s ->
evt asegs istrlen_post
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz p) (wz i) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x754a0) fc None m (seg_rom asegs)).
Proof.
induction n as [|n IH]; intros i a2 Hn Hi.
-
assert (RD : ov_read_bytes asegs m (wa (p + i)) 1 = Some [b8 0]).
{ rewrite (bytes_at_read asegs m p _ i 1 SRC) by (rewrite ?length_app, ?zb_length; cbn; unfold zlength in *; lia).
replace i with (zlength s) by lia. rewrite zb_end. reflexivity. }
pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite length_app, zb_length in BS. cbn [length] in BS. unfold zlength in *.
step. replace (wz (p + i) : word) with (wa (p + i)) by reflexivity. step. clear RD.
change (zxb (b8 0)) with (wz 0). step. step. bif. step. step.
apply evt_done. unfold istrlen_post, zlength. replace i with (Z.of_nat (length s)) by lia. reflexivity.
- pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite length_app, zb_length in BS. cbn [length] in BS.
assert (CR : 0 < nth (Z.to_nat i) s 0 < 256).
{ apply (proj1 (List.Forall_forall _ _) BYT). apply nth_In. unfold zlength in *; lia. }
assert (RD : ov_read_bytes asegs m (wa (p + i)) 1 = Some [b8 (nth (Z.to_nat i) s 0)]).
{ rewrite (bytes_at_read asegs m p _ i 1 SRC) by (rewrite ?length_app, ?zb_length; cbn; unfold zlength in *; lia).
rewrite zb_nth by lia. reflexivity. }
unfold zlength in *.
step. replace (wz (p + i) : word) with (wa (p + i)) by reflexivity. step. clear RD.
rewrite zxb_b8, Z.mod_small by lia.
step. step. ifT. apply (IH (i + 1)); lia.
Qed.

Lemma istrlen_spec : forall (a1 a2 : word),
evt asegs istrlen_post
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x7549c) fc None m (seg_rom asegs)).
Proof.
intros a1 a2. step. apply (istrlen_loop (Z.to_nat (zlength s)) 0); unfold zlength; lia.
Qed.
End IStrlen.

Fixpoint strchr_res (q : Z) (l : list Z) (c : Z) : Z :=
match l with [] => 0 | z :: l' => if z =? c then q else strchr_res (q + 1) l' c end.

Section IStrchr.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : Z).
Hypothesis CR : 0 < c < 256.

Definition istrchr_post (r : Z) : machine_state -> Prop :=
fun ms' => exists a1' a3' : word,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz r) a1' (wz c) a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs).

Lemma istrchr_loop : forall (l : list Z) (q : Z) (t : list byte) (a1 : word),
bytes_at asegs m q (zb l ++ b8 0 :: t) -> Forall (fun z => 0 < z < 256) l -> hd 0 l <> c ->
evt asegs (istrchr_post (strchr_res q l c))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz q) a1 (wz c) (wz (hd 0 l)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x7540c) fc None m (seg_rom asegs)).
Proof.
induction l as [|z l IH]; intros q t a1 STR BYT NE.
- cbn [hd strchr_res]. step. ifT. step. step. apply evt_done. unfold istrchr_post. do 2 eexists. reflexivity.
- cbn [hd] in NE |- *. apply Forall_cons_iff in BYT. destruct BYT as [Bz BYT].
pose proof (bytes_at_bound _ _ _ _ STR) as BS. rewrite length_app, zb_length in BS. cbn [length] in BS.
cbn [strchr_res]. replace (z =? c) with false by (symmetry; apply Z.eqb_neq; exact NE).
step. ifF.
assert (RD : ov_read_bytes asegs m (wa (q + 1)) 1 = Some [b8 (hd 0 l)]).
{ rewrite (bytes_at_read asegs m q _ 1 1 STR) by (rewrite ?length_app, ?zb_length; cbn; lia).
destruct l as [|z' l']; reflexivity. }
assert (CR' : 0 <= hd 0 l < 256).
{ destruct l as [|z' l']; cbn; [lia|]. apply Forall_cons_iff in BYT. lia. }
step. clear RD. rewrite zxb_b8, Z.mod_small by lia. step. step. step.
destruct (Z.eq_dec (hd 0 l) c) as [E|NE'].
+ ifF. step. step. apply evt_done. unfold istrchr_post.
destruct l as [|z' l']; cbn [hd] in E; [lia|]. cbn [strchr_res]. rewrite (proj2 (Z.eqb_eq _ _) E). do 2 eexists. reflexivity.
+ ifT. apply (IH (q + 1) t); [| exact BYT| exact NE'].
pose proof STR as STR'. change (zb (z :: l) ++ b8 0 :: t) with ([b8 z] ++ (zb l ++ b8 0 :: t)) in STR'.
apply bytes_at_app in STR'. destruct STR' as [_ S2]. cbn [length Z.of_nat Pos.of_succ_nat] in S2. exact S2.
Qed.

Lemma istrchr_spec : forall (l : list Z) (q : Z) (t : list byte) (a1 a2 a3 : word),
bytes_at asegs m q (zb l ++ b8 0 :: t) -> Forall (fun z => 0 < z < 256) l -> a1 = wz c ->
evt asegs (istrchr_post (strchr_res q l c))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz q) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x753fc) fc None m (seg_rom asegs)).
Proof.
intros l q t a1 a2 a3 STR BYT ->.
pose proof (bytes_at_bound _ _ _ _ STR) as BS. rewrite length_app, zb_length in BS. cbn [length] in BS.
assert (RD : ov_read_bytes asegs m (wa (q + 0)) 1 = Some [b8 (hd 0 l)]).
{ rewrite (bytes_at_read asegs m q _ 0 1 STR) by (rewrite ?length_app, ?zb_length; cbn; lia). destruct l; reflexivity. }
assert (CR' : 0 <= hd 0 l < 256).
{ destruct l as [|z' l']; cbn; [lia|]. apply Forall_cons_iff in BYT. lia. }
step. clear RD. rewrite zxb_b8, Z.mod_small by lia.
step. rewrite (unsigned_lit c) by lia. change (Z.land c 255) with (Z.land c (Z.ones 8)). rewrite Z.land_ones, Z.mod_small by lia.
step. destruct (Z.eq_dec (hd 0 l) c) as [E|NE].
- ifF. step. apply evt_done. unfold istrchr_post.
destruct l as [|z' l']; cbn [hd] in E; [lia|]. cbn [strchr_res]. rewrite (proj2 (Z.eqb_eq _ _) E). do 2 eexists. reflexivity.
- ifT. apply (istrchr_loop l q t); assumption.
Qed.
End IStrchr.

Definition boxed (P : Prop) : Prop := P.

Lemma rwc_eq : forall m A A' cs, rw_cells asegs m A cs -> A = A' -> rw_cells asegs m A' cs.
Proof. intros m A A' cs H <-. exact H. Qed.

Lemma ash_szone_words {BAND : Band} : forall m p n, ash m -> szone p n -> 0 < n ->
ro_cells asegs m (8 * (SH p / 8)) [C8 (wz 0)] /\ ro_cells asegs m (8 * (SH (p + n - 1) / 8)) [C8 (wz 0)].
Proof.
intros m p n (Z1 & Z2 & Z3) SZ N0.  unfold szone in SZ.
destruct SZ as [(A1 & A2)|[(B1 & B2)|(D1 & D2)]].
- split; (eapply (zrd_ro8 _ _ _ _ Z1); rewrite SH_eq; Z.div_mod_to_equations; lia).
- split; (eapply (zrd_ro8 _ _ _ _ Z2); rewrite !SH_eq; unfold KHI in *; Z.div_mod_to_equations; lia).
- split; (eapply (zrd_ro8 _ _ _ _ Z3); rewrite SH_eq; Z.div_mod_to_equations; lia).
Qed.

Lemma ro_str : forall m A (l : list Z), mem_inv asegs m -> ro_bytes_b asegs A (map b8 l) = true ->
0 <= A -> A + Z.of_nat (length l) <= 2^64 -> ro_cells asegs m A (map (fun z => C1 (b8 z)) l).
Proof.
intros m A l MI RB H0 HL.
pose proof (ro_cells_image asegs m A (map b8 l) MI RB H0 ltac:(rewrite length_map; exact HL)) as R.
eapply ro_cells_recast'; [exact R| |].
- clear. induction l as [|z l IH]; cbn; [exact I|]. split; [exact I| exact IH].
- cbn [cells_bytes cbytes]. rewrite app_nil_r. clear. induction l as [|z l IH]; cbn; [reflexivity|]. rewrite IH. reflexivity.
Qed.
Lemma ro_img8 : forall m A v, mem_inv asegs m -> ro_bytes_b asegs A (le8 (wz v)) = true -> 0 <= A -> A + 8 <= 2^64 ->
ro_cells asegs m A [C8 (wz v)].
Proof.
intros m A v MI RB H0 HL.
pose proof (ro_cells_image asegs m A (le8 (wz v)) MI RB H0 ltac:(rewrite length_le8; exact HL)) as R.
eapply ro_cells_recast'; [exact R| cbn; split; exact I| cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity].
Qed.

Ltac name_towers H :=
repeat match type of H with
| context [CB ?n ?j] =>
lazymatch j with
| firstn _ _ => idtac | skipn _ _ => idtac
end;
let x := fresh "jk" in set (x := j) in H; clearbody x
end.
Ltac pc_carve ST :=
carve_frame 2240%nat ST;
lazymatch goal with FR : rw_cells _ _ _ [CB 2240 _] |- _ =>
apply (rw_cells_split_CB asegs _ _ [] 2240 _ _ [2136; 104]%nat) in FR; [| reflexivity]; cbn [mk_CB_cells app] in FR;
name_towers FR end.

Definition pc_prologue_post {BAND : Band} (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (ms' : machine_state) : Prop :=
exists (m' : mem) (jk : list byte),
ms' = MS (mkR ra (wz (bv_unsigned sp + -2240)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x537e4) fc None m' (seg_rom asegs)
/\ rw_cells asegs m' (bv_unsigned sp + -2240) [CB 2136 jk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ stk asegs m' lo (bv_unsigned sp + -2240)
/\ munch [(bv_unsigned sp - 2320, bv_unsigned sp)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m'.

Lemma pc_prologue {BAND : Band} : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m -> band_lo <= lo -> lo <= bv_unsigned sp - 2320 ->
evt asegs (pc_prologue_post ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pcommon_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros ST MI CEIL LO.
pose proof CEIL as CEIL'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 2320, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold pcommon_entry.
pc_carve ST.
do 16 bstep.
apply evt_done. unfold pc_prologue_post. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
split; [exact FR|]. split; [exact ST|]. split; [exact MU|]. split; [exact WM| exact MI].
Qed.

Lemma u8_lit' : forall c, (0 <= c < 256)%Z -> bv_unsigned (Z_to_bv 8 c) = c.
Proof. intros c Hc. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. apply Z.mod_small. cbn. lia. Qed.
Lemma forallb_skipn' {X} (f : X -> bool) : forall i l, forallb f l = true -> forallb f (skipn i l) = true.
Proof. induction i as [|i IH]; intros l H; [exact H|]. destruct l as [|x l]; [reflexivity|]. cbn in H |- *. apply andb_prop in H as [_ H]. apply IH. exact H. Qed.
Lemma cells_size_mapC1 : forall l, cells_size (map (fun c => C1 (b8 c)) l) = length l.
Proof. induction l as [|c l IH]; [reflexivity|]. cbn [map cells_size csize length]. rewrite IH. lia. Qed.
Lemma ro_C1_skipn : forall segs m A l i, ro_cells segs m A (map (fun c => C1 (b8 c)) l) -> (i <= length l)%nat ->
ro_cells segs m (A + Z.of_nat i) (map (fun c => C1 (b8 c)) (skipn i l)).
Proof.
intros segs m A l i H Hi. rewrite <- (firstn_skipn i l), map_app in H. apply ro_cells_app in H. destruct H as [_ H].
rewrite cells_size_mapC1, length_firstn, Nat.min_l in H by lia. exact H.
Qed.

Lemma pc_scan_core {BAND : Band} : forall (n : nat) (l : list Z) (p : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P : machine_state -> Prop),
ro_cells asegs m p (map (fun c => C1 (b8 c)) l) ->
0 <= p -> p + Z.of_nat (length l) <= 2^47 -> (n < length l)%nat ->
forallb (fun c => (0 <=? c) && (c <? 256)) l = true ->
forallb (fun c => negb (c =? 37) && negb (c =? 0)) (firstn n l) = true ->
nth n l 0 = 37 ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 37) a1 a2 a3 a4 a5 a6 a7 s2 (wz (p + Z.of_nat n)) s4 s5 s6 s7 s8 s9 s10 (wz 37) t3 t4 t5 t6)
F (wz 0x538fc) fc None m (seg_rom asegs)) ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz p) s4 s5 s6 s7 s8 s9 s10 (wz 37) t3 t4 t5 t6)
F (wz 0x538e4) fc None m (seg_rom asegs)).
Proof.
induction n as [|n IH]; intros l p ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m P FM Hp Hl Hn HB HN H37 K;
(destruct l as [|c l']; [cbn in Hn; lia|]);
change (map (fun c => C1 (b8 c)) (c :: l')) with ([C1 (b8 c)] ++ map (fun c => C1 (b8 c)) l') in FM;
apply ro_cells_app in FM; destruct FM as [C0 FM]; cbn [cells_size csize Nat.add] in FM;
cbn [forallb] in HB; apply andb_prop in HB as [Hc HB]; apply andb_prop in Hc as [Hc1 Hc2]; apply Z.leb_le in Hc1; apply Z.ltb_lt in Hc2.
- cbn [nth] in H37. subst c. rewrite Z.add_0_r in K.
bstep. bstep. exact K.
- cbn [firstn forallb] in HN. apply andb_prop in HN as [Hc HN]. apply andb_prop in Hc as [Hc3 Hc4].
apply Bool.negb_true_iff, Z.eqb_neq in Hc3. apply Bool.negb_true_iff, Z.eqb_neq in Hc4.
bstep. bstep.
if_cases K1; zify_cond K1; rewrite ?(u8_lit' c), ?unsigned_lit in K1 by lia; [exfalso; lia|].
bstep.
if_cases K2; zify_cond K2; rewrite ?(u8_lit' c), ?unsigned_lit in K2 by lia; [exfalso; lia|].
bstep. bstep. bstep.
eapply (IH l' (p + 1)); clear IH.
+ exact FM.
+ lia.
+ cbn [length] in Hl. lia.
+ cbn [length] in Hn. lia.
+ exact HB.
+ exact HN.
+ exact H37.
+ replace (p + 1 + Z.of_nat n) with (p + Z.of_nat (S n)) by lia. exact K.
Qed.

Lemma pc_scan {BAND : Band} : forall (n i : nat) (l : list Z) (A q p : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P : machine_state -> Prop),
ro_cells asegs m A (map (fun c => C1 (b8 c)) l) ->
q = A + Z.of_nat (i + n) -> p = A + Z.of_nat i -> 0 <= A -> A + Z.of_nat (length l) <= 2^47 -> (i + n < length l)%nat ->
forallb (fun c => (0 <=? c) && (c <? 256)) l = true ->
forallb (fun c => negb (c =? 37) && negb (c =? 0)) (firstn n (skipn i l)) = true ->
nth (i + n) l 0 = 37 ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 37) a1 a2 a3 a4 a5 a6 a7 s2 (wz q) s4 s5 s6 s7 s8 s9 s10 (wz 37) t3 t4 t5 t6)
F (wz 0x538fc) fc None m (seg_rom asegs)) ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz p) s4 s5 s6 s7 s8 s9 s10 (wz 37) t3 t4 t5 t6)
F (wz 0x538e4) fc None m (seg_rom asegs)).
Proof.
intros n i l A q p ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m P FM Hq -> HA Hl Hn HB HN H37 K.
eapply (pc_scan_core n (skipn i l)).
- apply ro_C1_skipn; [exact FM| lia].
- lia.
- rewrite length_skipn. lia.
- rewrite length_skipn. lia.
- apply forallb_skipn'. exact HB.
- exact HN.
- rewrite nth_skipn. exact H37.
- replace (A + Z.of_nat i + Z.of_nat n) with q by lia. exact K.
Qed.

Lemma pc_scan_nul_core {BAND : Band} : forall (n : nat) (l : list Z) (p : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P : machine_state -> Prop),
ro_cells asegs m p (map (fun c => C1 (b8 c)) l) ->
0 <= p -> p + Z.of_nat (length l) <= 2^47 -> (n < length l)%nat ->
forallb (fun c => (0 <=? c) && (c <? 256)) l = true ->
forallb (fun c => negb (c =? 37) && negb (c =? 0)) (firstn n l) = true ->
nth n l 0 = 0 ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 (wz (p + Z.of_nat n)) s4 s5 s6 s7 s8 s9 s10 (wz 37) t3 t4 t5 t6)
F (wz 0x5398c) fc None m (seg_rom asegs)) ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz p) s4 s5 s6 s7 s8 s9 s10 (wz 37) t3 t4 t5 t6)
F (wz 0x538e4) fc None m (seg_rom asegs)).
Proof.
induction n as [|n IH]; intros l p ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m P FM Hp Hl Hn HB HN H0 K;
(destruct l as [|c l']; [cbn in Hn; lia|]);
change (map (fun c => C1 (b8 c)) (c :: l')) with ([C1 (b8 c)] ++ map (fun c => C1 (b8 c)) l') in FM;
apply ro_cells_app in FM; destruct FM as [C0 FM]; cbn [cells_size csize Nat.add] in FM;
cbn [forallb] in HB; apply andb_prop in HB as [Hc HB]; apply andb_prop in Hc as [Hc1 Hc2]; apply Z.leb_le in Hc1; apply Z.ltb_lt in Hc2.
- cbn [nth] in H0. subst c. rewrite Z.add_0_r in K.
bstep. bstep. bstep. exact K.
- cbn [firstn forallb] in HN. apply andb_prop in HN as [Hc HN]. apply andb_prop in Hc as [Hc3 Hc4].
apply Bool.negb_true_iff, Z.eqb_neq in Hc3. apply Bool.negb_true_iff, Z.eqb_neq in Hc4.
bstep. bstep.
if_cases K1; zify_cond K1; rewrite ?(u8_lit' c), ?unsigned_lit in K1 by lia; [exfalso; lia|].
bstep.
if_cases K2; zify_cond K2; rewrite ?(u8_lit' c), ?unsigned_lit in K2 by lia; [exfalso; lia|].
bstep. bstep. bstep.
eapply (IH l' (p + 1)); clear IH.
+ exact FM.
+ lia.
+ cbn [length] in Hl. lia.
+ cbn [length] in Hn. lia.
+ exact HB.
+ exact HN.
+ exact H0.
+ replace (p + 1 + Z.of_nat n) with (p + Z.of_nat (S n)) by lia. exact K.
Qed.

Lemma pc_scan_nul {BAND : Band} : forall (n i : nat) (l : list Z) (A q p : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P : machine_state -> Prop),
ro_cells asegs m A (map (fun c => C1 (b8 c)) l) ->
q = A + Z.of_nat (i + n) -> p = A + Z.of_nat i -> 0 <= A -> A + Z.of_nat (length l) <= 2^47 -> (i + n < length l)%nat ->
forallb (fun c => (0 <=? c) && (c <? 256)) l = true ->
forallb (fun c => negb (c =? 37) && negb (c =? 0)) (firstn n (skipn i l)) = true ->
nth (i + n) l 0 = 0 ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 (wz q) s4 s5 s6 s7 s8 s9 s10 (wz 37) t3 t4 t5 t6)
F (wz 0x5398c) fc None m (seg_rom asegs)) ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz p) s4 s5 s6 s7 s8 s9 s10 (wz 37) t3 t4 t5 t6)
F (wz 0x538e4) fc None m (seg_rom asegs)).
Proof.
intros n i l A q p ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m P FM Hq -> HA Hl Hn HB HN H0 K.
eapply (pc_scan_nul_core n (skipn i l)).
- apply ro_C1_skipn; [exact FM| lia].
- lia.
- rewrite length_skipn. lia.
- rewrite length_skipn. lia.
- apply forallb_skipn'. exact HB.
- exact HN.
- rewrite nth_skipn. exact H0.
- replace (A + Z.of_nat i + Z.of_nat n) with q by lia. exact K.
Qed.

Ltac scan_side A := first [ lazymatch goal with H : ro_cells _ _ A _ |- ro_cells _ _ A _ => exact H end | reflexivity | lia
| apply Z.leb_le; vm_compute; reflexivity | apply Nat.ltb_lt; vm_compute; reflexivity | vm_compute; reflexivity ].
Ltac scan_pct n i l A := run_to 0x538e4; let q := eval vm_compute in (A + Z.of_nat (i + n)) in eapply (pc_scan n i l A q); [ scan_side A .. | ].
Ltac scan_nul n i l A := run_to 0x538e4; let q := eval vm_compute in (A + Z.of_nat (i + n)) in eapply (pc_scan_nul n i l A q); [ scan_side A .. | ].

Tactic Notation "pose_str" ident(nm) constr(A) constr(l) constr(MI) := pose proof (ro_str _ A l MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as nm; cbn [map] in nm.
Ltac pose_rodata MI :=
pose_str RS1 0x1da50 [100; 105; 111; 117; 120; 88; 110; 0] MI;
pose_str RS2 0x16dde [97; 65; 101; 69; 102; 70; 103; 71; 0] MI;
pose_str RS3 0x15cb0 [39; 45; 43; 32; 35; 48; 0] MI;
pose_str RS4 0x1c77b [106; 122; 116; 76; 113; 0] MI;
pose_str RS5 0x14816 [99; 67; 115; 83; 0] MI;
pose_str RS6 0x1acf4 [67; 83; 0] MI;
pose_str RS7 0x1088e [99; 115; 91; 0] MI;
pose_str RS8 0x140d6 [115; 83; 0] MI;
pose proof (ro_img8 _ 0x10480 0xaaaaaaaaaaaaaaaa MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as RK.

Ltac stop_pc pc := lazymatch pc with 480072%Z => idtac | 480252%Z => idtac | 480412%Z => idtac | 359128%Z => idtac | 415108%Z => idtac end.

Ltac run := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => first [stop_pc pc; fail 1 | bstep] end).

Ltac fixret := try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).

Ltac call_strchr A lst :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MIc : mem_inv asegs mc |- _ =>
eapply evt_cut;
[ eapply istrchr_spec with (l := lst) (q := A) (t := []); [ | | | reflexivity];
[ lia
| exact (proj2 (ro_str _ A (lst ++ [0]) MIc ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))
| repeat (apply Forall_cons; [lia|]); apply Forall_nil ]
| let ms' := fresh "ms'" in let PO := fresh "PO" in
intros ms' PO; destruct PO as (? & ? & ->); cbn [strchr_res Z.eqb Pos.eqb]; lits; fixret ]
end end.

Ltac call_strlen FMT l :=
eapply evt_cut;
[ eapply istrlen_spec with (s := l) (t := []); [exact (proj2 FMT)| repeat (apply Forall_cons; [lia|]); apply Forall_nil]
| let ms' := fresh "ms'" in intros ms' <-; let n := eval vm_compute in (zlength l) in change (zlength l) with n; lits; fixret ].

Ltac call_memset DIR :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_cut;
[ eapply imemset40_spec; [exact DIR| reflexivity| assumption| lia]
| let ms' := fresh "ms'" in let PO := fresh "PO" in let m' := fresh "m" in
let MU2 := fresh "MU2" in let WM2 := fresh "WM2" in
intros ms' PO; destruct PO as (m' & -> & MU2 & WM2 & ? & ?DIR2); clear DIR;
transport_after_call asegs mc m' MU2 WM2; clear MU2 WM2; try clear mc; rename DIR2 into DIR; fixret ]
end.

Ltac dir_L2 DIR :=
lazymatch type of DIR with rw_cells _ ?mm ?A [C8 ?w0; C8 ?w1; C8 ?b; C8 ?e; C8 ?w4] =>
let D := fresh "DIR" in
assert (D : rw_cells asegs mm A [CB 8 (le8 w0); CB 8 (le8 w1); C8 b; C8 e; CB 8 (le8 w4)])
by (eapply rw_cells_recast'; [exact DIR| cbn [cells_wf cell_wf]; rewrite ?length_le8; repeat split; reflexivity| reflexivity]);
clear DIR; rename D into DIR
end.
Ltac dir_L1 DIR :=
lazymatch type of DIR with rw_cells _ ?mm ?A (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?rest) =>
let D := fresh "DIR" in
assert (D : rw_cells asegs mm A ([c0; c1; c2; c3] ++ rest ++ [])) by (rewrite app_nil_r; exact DIR);
apply rw_cells_merge in D; cbn [cells_size csize cells_bytes cbytes app Nat.add] in D;
clear DIR; rename D into DIR
end.

Ltac bvlist_eq := lazymatch goal with
| |- cons _ _ = cons _ _ => apply (f_equal2 cons); [apply bv_eq; reflexivity | bvlist_eq]
| |- nil = nil => reflexivity end.
Ltac dir_L2c DIR :=
lazymatch type of DIR with rw_cells _ ?mm ?A [C8 (Z_to_bv 64 ?w0); C8 (Z_to_bv 64 ?w1); C8 ?b; C8 ?e; C8 ?w4] =>
let l0 := eval vm_compute in (w0 mod 2^32) in let h0 := eval vm_compute in ((w0 / 2^32) mod 2^32) in
let l1 := eval vm_compute in (w1 mod 2^32) in let h1 := eval vm_compute in ((w1 / 2^32) mod 2^32) in
let D := fresh "DIR" in
assert (D : rw_cells asegs mm A [C4 (Z_to_bv 64 l0); C4 (Z_to_bv 64 h0); C4 (Z_to_bv 64 l1); C4 (Z_to_bv 64 h1); C8 b; C8 e; CB 8 (le8 w4)])
by (eapply rw_cells_recast'; [exact DIR| cbn [cells_wf cell_wf]; rewrite ?length_le8; repeat split; reflexivity|
lazymatch goal with |- ?g => tryif has_var g then fail 1 "dir_L2c: open cells" else (vm_compute; bvlist_eq) end]);
clear DIR; rename D into DIR
end.
Ltac dir_back DIR :=
lazymatch goal with |- rw_cells _ _ _ ?cs => eapply rw_cells_recast'; [exact DIR| cbn [cells_wf cell_wf]; rewrite ?length_le8, ?length_take, ?length_drop; repeat split; reflexivity|
lazymatch goal with |- ?g => tryif has_var g then fail 1 "dir_back: open cells" else (vm_compute; bvlist_eq) end] end.

Lemma cbytes_mapC1 : forall l, cells_bytes (map (fun z => C1 (b8 z)) l) = zb l.
Proof. unfold zb. induction l as [|z l IH]; cbn [map cells_bytes cbytes app]; [reflexivity| now rewrite IH]. Qed.

Definition pc_setup_post {BAND : Band} (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo A : Z) (ms' : machine_state) : Prop :=
exists (m' : mem) (junk1 junk2 : list byte),
ms' = MS (mkR (wz 0x538e0) (wz (bv_unsigned sp + -2240)) gp tp t0 t1 t2 sp s1
(wz (bv_unsigned sp + -2216)) (wz 0) (wz (bv_unsigned sp + -2176)) (wz (bv_unsigned sp + -2176)) (wz 0) a5 a6 a7
(wz 10) (wz A) (wz 0x15cb0) a2 s6 (wz 9) (wz (bv_unsigned sp + -2184)) (wz 12297829382473034410) (wz (-1)) (wz 37) t3 t4 t5 t6)
F (wz 0x538e4) fc None m' (seg_rom asegs)
/\ rw_cells asegs m' (bv_unsigned sp + -2240) [CB 8 junk1; C8 (wz (bv_unsigned sp + -120)); C8 a0]
/\ rw_cells asegs m' (bv_unsigned sp + -2216) [C8 (wz 0); C8 (wz 18446744073709551615); C8 (wz 0); C8 (wz 0); C8 (wz 0)]
/\ rw_cells asegs m' (bv_unsigned sp + -2176) [CB 2072 junk2; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ stk asegs m' lo (bv_unsigned sp + -2240)
/\ munch [(bv_unsigned sp - 2320, bv_unsigned sp)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m'.

Lemma pc_setup {BAND : Band} : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo A c : Z) (l : list Z),
ISH m -> stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m -> band_lo <= lo -> lo <= bv_unsigned sp - 2320 ->
ro_bytes_b asegs A (map b8 (c :: l ++ [0])) = true ->
forallb (fun z => (0 <? z) && (z <? 256)) (c :: l) = true ->
(length l < 63)%nat -> 0x10000 <= A -> A + Z.of_nat (length l) + 2 <= 0x230c0 ->
evt asegs (pc_setup_post ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo A)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz A) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pcommon_entry) fc None m (seg_rom asegs)).
Proof.
intros until l. intros ISH0 ST MI CEIL LO RB BYT LEN ZLO ZHI.
pose proof CEIL as CEIL'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 2320, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
destruct ISH0 as (ASH & RC & SB).
assert (BYT' : Forall (fun z => 0 < z < 256) (c :: l)).
{ apply Forall_forall. intros x Hx. eapply forallb_forall in BYT; [|exact Hx]. apply andb_prop in BYT as [B1 B2].
apply Z.ltb_lt in B1, B2. lia. }
assert (C0 : 0 < c < 256) by (inversion BYT'; assumption).
clear BYT.
assert (SZ : szone A (zlength (c :: l) + 1)) by (left; unfold zlength; cbn [length]; lia).
assert (NR : 1 <= zlength (c :: l) < 64) by (unfold zlength; cbn [length]; lia).
change (boxed (szone A (zlength (c :: l) + 1))) in SZ.
unfold pcommon_entry.
eapply evt_cut; [ eapply pc_prologue; [exact ST | exact MI | exact CEIL | lia] | ].
intros ms' (m' & jk & -> & FR & ST' & MUc & WMc & MIc).
transport_after_call asegs m m' MUc WMc. clear MUc WMc.
try clear ST. try clear MI. rename ST' into ST. rename MIc into MI.
apply (rw_cells_split_CB asegs _ _ [] 2136 _ _ [8;8;8;8;8;8;8;8;2072]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
apply (proj1 (rw_cells_app asegs _ _ [_;_;_] _)) in FR. destruct FR as [FRa FR].
apply (proj1 (rw_cells_app asegs _ _ [_;_;_;_;_] _)) in FR. destruct FR as [DIR FRb].
cbn [cells_size csize Nat.add app] in FRa, DIR, FRb.
replace (bv_unsigned sp + -2240 + Z.of_nat 24) with (bv_unsigned sp + -2216) in DIR by lia.
replace (bv_unsigned sp + -2240 + Z.of_nat 24 + Z.of_nat 40) with (bv_unsigned sp + -2176) in FRb by lia.
lazymatch type of FRa with rw_cells _ _ _ (CB 8 ?j :: _) => remember j as junk1 eqn:EJ1; clear EJ1 end.
lazymatch type of FRb with rw_cells _ _ _ (CB 2072 ?j :: _) => remember j as junk2 eqn:EJ2; clear EJ2 end.
name_towers FRa. name_towers DIR.

pose proof (ro_str _ A (c :: l ++ [0]) MI RB ltac:(lia) ltac:(cbn [length]; rewrite length_app; cbn [length]; lia)) as FMT.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (SRC : bytes_at asegs mc A (zb (c :: l) ++ b8 0 :: []));
[ pose proof (proj2 FMT) as B; rewrite cbytes_mapC1 in B; unfold zb in B |- *;
replace (c :: l ++ [0]) with ((c :: l) ++ [0]) in B by reflexivity; rewrite map_app in B; exact B |] end.
change (map (fun z => C1 (b8 z)) (c :: l ++ [0])) with ([C1 (b8 c)] ++ map (fun z => C1 (b8 z)) (l ++ [0])) in FMT.
apply ro_cells_app in FMT. destruct FMT as [FC0 _].
run.
eapply evt_cut; [eapply istrlen_spec with (s := c :: l) (t := []); [exact SRC| exact BYT'] |].
intros ms' <-. fixret. clear SRC BYT'.
assert (ZN : A + zlength (c :: l) + 1 <= 0x230c0) by (unfold zlength; cbn [length]; lia).
set (n := zlength (c :: l)) in *. clearbody n.
bstep. bstep. bstep.
rewrite (unsigned_lit A), zb_lxor_ones by lia. ifF.
bstep. bstep. ifF.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (ash_munch _ _ _ ASH MU WM ltac:(zforalls)) as ASHc;
pose proof (shadow_base_munch _ _ _ SB MU ltac:(rt_wzones)) as SBc end.
unfold boxed in SZ.
destruct (ash_szone_words _ _ _ ASHc SZ ltac:(lia)) as [W1 W2]. clear ASHc.
destruct SBc as [SB1 SB2]. unfold A_SHADOW_GOT, A_SHADOW_CELL, A_SHADOW_OFS in SB1, SB2.
bstep. bstep. bstep. bstep. bstep. bstep. bstep. bstep.
rewrite ?(unsigned_lit A), ?(unsigned_lit (n + A)) by lia.
replace (2147450880 + A ≫ 3) with (SH A) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; lia).
replace (2147450880 + (n + A) ≫ 3) with (SH (A + (n + 1) - 1))
by (rewrite Z.shiftr_div_pow2, SH_eq by lia; replace (A + (n + 1) - 1) with (n + A) by lia; change (2^3) with 8; lia).
assert (SHR : 0x7fff8000 <= SH A /\ SH A <= SH (A + (n + 1) - 1) < 0x10007fff8000)
by (rewrite !SH_eq; clear - NR ZN ZLO; Z.div_mod_to_equations; lia).
stp. stp. rewrite (unsigned_lit (SH A)), (unsigned_lit (SH (A + (n + 1) - 1))) by lia. rewrite !land_m8 by lia.
replace (SH A - SH A mod 8) with (8 * (SH A / 8)) by (Z.div_mod_to_equations; lia).
replace (SH (A + (n + 1) - 1) - SH (A + (n + 1) - 1) mod 8) with (8 * (SH (A + (n + 1) - 1) / 8)) by (Z.div_mod_to_equations; lia).
bstep. bstep. bstep. bstep.
clear W1 W2 SB1 SB2 SHR.
bstep. bstep. bstep. bstep.
rewrite zxb_b8, (Z.mod_small c) by lia.
bstep. ifF.
run_to 0x53888.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MIc : mem_inv asegs mc |- _ =>
pose proof (ro_img8 _ 0x10480 0xaaaaaaaaaaaaaaaa MIc ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as RK end end.
run_to 0x5388c. clear RK.
run. call_memset DIR.
bstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => apply evt_done; unfold pc_setup_post; exists mc, junk1, junk2 end.
split; [reflexivity|].
split; [exact FRa|]. split; [exact DIR|]. split; [exact FRb|].
split; [assumption|]. split; [exact MU|]. split; [exact WM| assumption].
Qed.
End Mq9.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu4g QV3O QpF1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqa.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QTVW.Mq7 QNQk.Mq8 QpY2.Mqi QTVW.Mqa QOJv.Mqb QNQk Q9Ho.Mq4 QV3O QnRU.Mql QMSY.Mq0.
Import QpME.Mq8 QpF1.
Import QlES.
Import ListNotations. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Variables (n i : Z) (gp : word).
Let c := class_of n.
Let sz := class_size c.
Let rz := rz_size n.
Let n' := used_size n.
Let nd := needed n.
Let AB := slot_beg RE c i.
Let A := AB + rz.
Hypothesis RL : rlay_ok RE X.
Hypothesis Hn : 0 <= n.
Hypothesis HP : from_primary n = true.
Hypothesis PAB : prim_lo RE <= AB.
Hypothesis ABP : AB + sz <= prim_lo RE + 2^37.
Hypothesis AL16 : AB mod 16 = 0.

Lemma geomS : 1 <= c <= 30 /\ nd <= sz <= 65536 /\ sz mod 32 = 0 /\ 16 <= rz <= 2048 /\ rz mod 16 = 0
/\ 1 <= n' /\ n' <= Z.max n 8 /\ n <= 65536 /\ Z.max n 8 + rz <= nd /\ nd < Z.max n 8 + 8 + rz /\ nd mod 8 = 0 /\ 24 <= nd <= 65536
/\ A mod 16 = 0 /\ 0x10007fff8000 <= AB /\ AB + sz <= band_lo
/\ appr_lia (rl_T X) 4096 /\ rl_T X + 4096 <= band_lo /\ rl_T X mod 4096 = 0
/\ (rl_T X + 4096 <= AB \/ AB + sz <= rl_T X)
/\ appr_lia (rl_ctx X) 65536 /\ rl_ctx X + 65536 <= band_lo
/\ (rl_ctx X + 65536 <= AB \/ AB + sz <= rl_ctx X)
/\ appr_lia (rl_dn X) 0x100000 /\ rl_dn X + 0x100000 <= band_lo
/\ (rl_dn X + 0x100000 <= AB \/ AB + sz <= rl_dn X)
/\ appr_lia (rl_ssb X) 0x800000 /\ rl_ssb X + 0x800000 <= band_lo
/\ (rl_ssb X + 0x800000 <= AB \/ AB + sz <= rl_ssb X).
Proof. exact (geom RE X n i RL Hn HP PAB ABP AL16). Qed.

Lemma alloc_hdr : forall ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (s7r : word) (sp : word) (F : bvmap 5 word) fc m lo
(fj : list byte) (canfill v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 rav : word) (b0 b1 : byte) (h w d : word) (Q : machine_state -> Prop),
RTconst RE X m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -128) -> band_lo <= lo -> lo <= bv_unsigned sp - 816 ->
rw_cells asegs m (bv_unsigned sp + -128) (alloc_frame fj canfill v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 rav) ->
rw_cells asegs m (A + -16) [C1 b0; C1 b1; C2 h; C4 w; C8 d] ->
(forall m1 (u0 u1 u2 u3 u5 u6 u7 : word),
munch [(A + -16, A)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp + -128) ->
rw_cells asegs m1 (bv_unsigned sp + -128) (alloc_frame fj canfill v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 rav) ->
rw_cells asegs m1 (A + -16) [C1 b0; C1 (b8 (hb1 b1)); C2 (wz 0); C4 (wz n'); C8 d] ->
RTconst RE X m1 ->
evt asegs Q (MS (mkR ra (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 (wz 1) (wz n') u0 u1 u2 u3 (wz (AB + nd)) u5 u6 u7
(wz AB) (wz nd) (wz A) (wz (A + -16)) (wz A_INSTANCE) s7r (wz 0) (wz (A + n')) (wz (rl_T X)) (wz 1) t3 t4 t5 t6)
F (wz 0x3f634) fc None m1 (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 (wz 1) (wz n') (wz AB) a1 a2 a3 a4 a5 a6 a7
(wz AB) (wz nd) (wz rz) (wz n) (wz A_INSTANCE) s7r (wz (-8)) (wz 7) (wz (rl_T X)) (wz 1) t3 t4 t5 t6)
F (wz 0x3f53c) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT MI ST CEIL LO FR HDR CONT.
pose proof geomS as (Gc & Gsz & Gsz32 & Grz & Grz16 & Gn1 & Gn2 & Gn3 & Gnd1 & Gnd2 & Gnd8 & Gnd3 & GA16 & GK & GC & TK & TB & TA & TD & CK & CC & CD & _).
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (RT_T _ _ _ RT) as TT. pose proof (RT_ctx_tid _ _ _ RT) as CT. cbv beta delta [rt_T_cells] in TT.
pose proof (munch_refl [(A + -16, A)] m) as MU. pose proof (wmono_refl asegs m) as WM.
subst A. unfold alloc_frame in FR.
step.
step.
rewrite (unsigned_lit (AB + rz)), land_7 by lia.
replace ((AB + rz) mod 8) with 0 by (clear - GA16; Z.div_mod_to_equations; lia).
step.
step. if_lit.
step.
step. ifz.
step.
stp.
step.
step.
step.
rewrite (unsigned_lit n'), Z.shiftr_div_pow2, (Z.div_small n') by lia.
step.
rewrite (unsigned_lit n), Z.shiftr_div_pow2, (Z.div_small n) by lia.
step.
step.
step.
step. if_lit.
step.
step.
step.
step.
step.
rewrite hb1_norm in HDR.
step. ifz.
step.
stp.
stp.
step.
replace (nd + AB) with (AB + nd) by lia.
eapply CONT; [exact MU| exact WM| assumption| exact ST| exact FR| exact HDR| ].
eapply RTconst_munch; [exact RT| exact MU| exact WM|].
constructor; [apply rt_avoid_prim; [exact RL| lia| unfold prim_hi; unfold prim_lo in *; lia]| constructor].
Qed.

Definition depot_W (sp : Z) : list (Z * Z) :=
[(sp - 352, sp - 128); (SS_BASE, DP_END); (rl_dn X, rl_dn X + 0x100000); (rl_ssb X, rl_ssb X + 0x800000)].

Lemma alloc_depot : forall ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (sp : word) (F : bvmap 5 word) fc m lo
(obj tsz dn : Z) (q : list word) (b0 : byte) (b1v : Z) (d : word) (Q : machine_state -> Prop),
RTconst RE X m -> RDepot RE X m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -128) -> band_lo <= lo -> lo <= bv_unsigned sp - 816 ->
rw_cells asegs m obj [C8 (wz (obj + 16)); C8 (wz tsz)] ->
u64arr asegs m (obj + 16) q -> Z.of_nat (length q) = 30 -> 1 <= tsz <= 30 ->
depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
bv_unsigned sp <= obj -> obj + 256 < 2^64 ->
rw_cells asegs m (A + -16) [C1 b0; C1 (b8 b1v); C2 (wz 0); C4 (wz n'); C8 d] ->
(forall m1 (u0 u1 u2 u5 u6 u7 u10 u11 u12 u13 u14 u15 u16 u17 : word) (id : Z),
munch ((A + -8, A) :: depot_W (bv_unsigned sp)) m m1 -> wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp + -128) ->
RTconst RE X m1 -> RDepot RE X m1 ->
rw_cells asegs m1 obj [C8 (wz (obj + 16)); C8 (wz tsz)] -> u64arr asegs m1 (obj + 16) q ->
1 <= id < 2^16 -> (exists dn', depot_n asegs m1 dn' /\ dn <= dn' <= dn + 1) ->
rw_cells asegs m1 (A + -16) [C1 b0; C1 (b8 b1v); C2 (wz 0); C4 (wz n'); C8 (wz id)] ->
evt asegs Q (MS (mkR (wz 0x3f640) (wz (bv_unsigned sp + -128)) gp (wz A_TP) u0 u1 u2 (wz 1) (wz n') (wz id) u5 u6 u7 u10 u11 u12 u13
(wz AB) (wz nd) (wz A) (wz (A + -16)) (wz A_INSTANCE) (wz obj) (wz 0) (wz (A + n')) (wz (rl_T X)) (wz 1) u14 u15 u16 u17)
F (wz 0x3f650) fc None m1 (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 (wz 1) (wz n') a0 a1 a2 a3 a4 a5 a6 a7
(wz AB) (wz nd) (wz A) (wz (A + -16)) (wz A_INSTANCE) (wz obj) (wz 0) (wz (A + n')) (wz (rl_T X)) (wz 1) t3 t4 t5 t6)
F (wz 0x3f634) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT RD MI ST CEIL LO OBJ TRQ LQ SZR DNH DCAP OB1 OB2 HDR CONT.
pose proof geomS as (Gc & Gsz & Gsz32 & Grz & Grz16 & Gn1 & Gn2 & Gn3 & Gnd1 & Gnd2 & Gnd8 & Gnd3 & GA16 & GK & GC & TK' & TB & TA & TD & CK & CC & CD & NK & NC & ND & BK & BC & BD).
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (munch_refl ((A + -8, A) :: depot_W (bv_unsigned sp)) m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold depot_W, SS_BASE, DP_END in MU. subst A.
step.
step.
step.
call_sp_ch (depot_put_spec RE X) ltac:(fun PO => unfold depot_stack, SS_BASE, DP_END in PO);
[exact RL| exact RD| assumption| exact ST| exact CEIL'| unfold depot_stack; lia| exact TRQ| exact LQ| exact SZR| exact DNH| exact DCAP| lia| lia|].
match goal with H : stk asegs _ lo _ |- _ => try rename H into ST end.
match goal with H : (exists id, _) |- _ => destruct H as (id & -> & ID & RD1 & TRQ1 & (dn1 & [DNC DNP] & DNR)) end. unfold DP_N in DNC.
step.
step.
rewrite (unsigned_lit id), (zext32_small id) by lia.
step.
rewrite (unsigned_lit id), Z.lor_0_l by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(AB + rz + -8, AB + rz)] mm) as MUh; pose proof (wmono_refl asegs mm) as WMh end.
step.
eapply CONT; [exact MU| exact WM| assumption| exact ST| | | exact OBJ| exact TRQ| exact ID| exists dn1; split; [split; [unfold DP_N; exact DNC| exact DNP]| exact DNR]| exact HDR].
- eapply RTconst_munch; [exact RT| exact MU| exact WM|]. unfold depot_W.
constructor; [apply rt_avoid_prim; [exact RL| lia| unfold prim_hi; unfold prim_lo in *; lia]|].
constructor; [apply rt_avoid_stack; [exact RL| lia]|].
constructor; [apply rt_avoid_depot_img; exact RL|].
constructor; [apply rt_avoid_dn; exact RL|].
constructor; [apply rt_avoid_ssb; exact RL| constructor].
- eapply RDepot_frame; [exact RD1| exact WMh|].
eapply agree_on_of_munch; [exact MUh| exact WMh|]. intros z Fz _. cbn [outside]. split; [| exact I].
destruct Fz as [Fz|[Fz|[Fz|Fz]]]; [destruct Fz as [F1 F2]; cbn [fst snd] in F1, F2; lia
| destruct Fz as [F1 F2]; cbn [fst snd] in F1, F2; (first [ clear - F2 F1 z ND TK' GK Gnd3 Gnd8 Gnd2 Gnd1 Grz16 Grz Gsz32 Gsz ks q AL16 AB nd rz sz c i n X RE BAND; lia | lia ]) | destruct Fz as [F1 F2]; cbn [fst snd] in F1, F2; (first [ clear - F2 F1 z BD TK' GK Gnd3 Gnd8 Gnd2 Gnd1 Grz16 Grz Gsz32 Gsz ks q AL16 AB nd rz sz c i n X RE BAND; lia | lia ]) | (first [ clear - Fz z TA TK' GK Gnd3 Grz16 Grz ks q AL16 AB nd rz sz c i n X RE BAND; lia | lia ])].
Qed.

End S.
End Mqa.

Module Mqb.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QTVW.Mq7 QNQk.Mq8 QpY2.Mqi QTVW.Mqa QOJv.Mqb QNQk Q9Ho.Mq4 QV3O QnRU.Mql QMSY.Mq0.
Import QpME.Mq8 QpF1.
Import QlES.
Import ListNotations. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Variables (n i : Z) (gp : word).
Let c := class_of n.
Let sz := class_size c.
Let rz := rz_size n.
Let n' := used_size n.
Let nd := needed n.
Let AB := slot_beg RE c i.
Let A := AB + rz.
Hypothesis RL : rlay_ok RE X.
Hypothesis Hn : 0 <= n.
Hypothesis HP : from_primary n = true.
Hypothesis PAB : prim_lo RE <= AB.
Hypothesis ABP : AB + sz <= prim_lo RE + 2^37.
Hypothesis AL16 : AB mod 16 = 0.

Lemma geomS : 1 <= c <= 30 /\ nd <= sz <= 65536 /\ sz mod 32 = 0 /\ 16 <= rz <= 2048 /\ rz mod 16 = 0
/\ 1 <= n' /\ n' <= Z.max n 8 /\ n <= 65536 /\ Z.max n 8 + rz <= nd /\ nd < Z.max n 8 + 8 + rz /\ nd mod 8 = 0 /\ 24 <= nd <= 65536
/\ A mod 16 = 0 /\ 0x10007fff8000 <= AB /\ AB + sz <= band_lo
/\ appr_lia (rl_T X) 4096 /\ rl_T X + 4096 <= band_lo /\ rl_T X mod 4096 = 0
/\ (rl_T X + 4096 <= AB \/ AB + sz <= rl_T X)
/\ appr_lia (rl_ctx X) 65536 /\ rl_ctx X + 65536 <= band_lo
/\ (rl_ctx X + 65536 <= AB \/ AB + sz <= rl_ctx X)
/\ appr_lia (rl_dn X) 0x100000 /\ rl_dn X + 0x100000 <= band_lo
/\ (rl_dn X + 0x100000 <= AB \/ AB + sz <= rl_dn X)
/\ appr_lia (rl_ssb X) 0x800000 /\ rl_ssb X + 0x800000 <= band_lo
/\ (rl_ssb X + 0x800000 <= AB \/ AB + sz <= rl_ssb X).
Proof. exact (geom RE X n i RL Hn HP PAB ABP AL16). Qed.

Lemma alloc_partial : forall ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (sp : word) (F : bvmap 5 word) fc m
(obj : Z) (pb : byte) (Q : machine_state -> Prop),
RTconst RE X m -> mem_inv asegs m ->
(n' mod 8 <> 0 -> rw_cells asegs m (SH A + n' / 8) [C1 pb]) ->
(forall m1 (u u0 u1 u2 u3 u4 u5 u6 u7 u10 u11 u12 u14 u15 u16 u17 u22 : word),
munch [(SH A + n' / 8, SH A + ngran n')] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 -> RTconst RE X m1 ->
(n' mod 8 <> 0 -> rw_cells asegs m1 (SH A + n' / 8) [C1 (b8 (n' mod 8))]) ->
evt asegs Q (MS (mkR u (wz (bv_unsigned sp + -128)) gp (wz A_TP) u0 u1 u2 (wz 1) (wz n') u3 u4 u5 u6 u7 u10 u11 u12
(wz AB) (wz nd) (wz A) (wz (A + -16)) u22 (wz obj) (wz 0) (wz (A + n')) (wz (rl_T X)) (wz 1) u14 u15 u16 u17)
F (wz 0x3f7e0) fc None m1 (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 (wz 1) (wz n') a0 a1 a2 a3 a4 a5 a6 a7
(wz AB) (wz nd) (wz A) (wz (A + -16)) (wz (8 * (n' / 8))) (wz obj) (wz 0) (wz (A + n')) (wz (rl_T X)) (wz 1) t3 t4 t5 t6)
F (wz 0x3f74c) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT MI P3 CONT.
pose proof geomS as (Gc & Gsz & Gsz32 & Grz & Grz16 & Gn1 & Gn2 & Gn3 & Gnd1 & Gnd2 & Gnd8 & Gnd3 & GA16 & GK & GC & _).
assert (SHa : SH AB = AB / 8 + 0x7fff8000) by reflexivity.
assert (SHA : SH (AB + rz) = SH AB + rz / 8) by (rewrite <- SH_plus8; f_equal; clear - Grz16; Z.div_mod_to_equations; lia).
assert (N8 : 0 <= n' / 8 /\ 0 <= n' mod 8 < 8 /\ n' = 8 * (n' / 8) + n' mod 8) by (clear - Gn1; Z.div_mod_to_equations; lia).
pose proof (ngran_eq n' ltac:(lia)) as (NG1 & NG2 & NG3). pose proof (round_up_8 n' ltac:(lia)) as [RU8 _].
subst A.
step.
destruct (Z.eq_dec (n' mod 8) 0) as [Z0|NZ].
- ifz.
eapply CONT; [| apply wmono_refl| exact MI| exact RT| intros NE; exfalso; exact (NE Z0)].
replace (ngran n') with (n' / 8) by (rewrite NG1; unfold round_up; clear -Z0 N8; Z.div_mod_to_equations; lia). apply munch_refl.
- ifz. specialize (P3 NZ).
remember (SH (AB + rz) + n' / 8) as SP8 eqn:ESP8.
pose proof (munch_refl [(SP8, SH (AB + rz) + ngran n')] m) as MU. pose proof (wmono_refl asegs m) as WM.
rtc RT 19%nat K19. rtc RT 5%nat K5. rtc RT 1%nat K1. rtc RT 14%nat K14.
step. call0 (can_poison_spec RE X); [exact RT| exact MI|]. subst_words.
step. if_lit.
step. step. step.
step.
stp. stp. stp. stp.
step. unfold_cond; cond_unsig; if_false.
step. step. step. step.
step. step.
stp.
step. ifz.
step. step. step.
stp. stp.
step. ifz.
step. ifz.
step. step.
step.
lits.
step.
rewrite (unsigned_lit (AB + rz + 8 * (n' / 8))), Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
step.
replace (2147450880 + (AB + rz + 8 * (n' / 8)) / 8) with SP8 by (rewrite ESP8, SHA, SHa; clear - AL16 Grz16 N8; Z.div_mod_to_equations; lia).
stp.
step.
rewrite (unsigned_lit n'), (Z.land_comm n' 18446744073709551615), land_ones64 by lia.
step.
rewrite (unsigned_lit n'), land_7 by lia.
step.
rewrite (unsigned_lit (n' mod 8)) in P3 by lia.
eapply CONT; [exact MU| exact WM| assumption| | intros _; exact P3].
eapply RTconst_munch; [exact RT| exact MU| exact WM|].
constructor; [| constructor]. rewrite ESP8, SHA, SHa. apply rt_avoid_gap; [exact RL| clear - GK N8 Grz; Z.div_mod_to_equations; lia| rewrite ?KHI_eq, NG1; unfold round_up; clear - GC Gsz Gnd1 Gn2 N8 NZ Grz; Z.div_mod_to_equations; lia].
Qed.

Lemma alloc_shadow : forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (sp : word) (F : bvmap 5 word) fc m lo
(obj : Z) (j2 : list byte) (pb : byte) (Q : machine_state -> Prop),
RTconst RE X m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -128) -> band_lo <= lo -> lo <= bv_unsigned sp - 816 ->
rw_cells asegs m (SH AB) [C1 fa_byte] ->
(n' / 8 <> 0 -> rw_cells asegs m (SH A) [CB (Z.to_nat (n' / 8)) j2]) ->
(n' mod 8 <> 0 -> rw_cells asegs m (SH A + n' / 8) [C1 pb]) ->
(forall m1 (u u0 u1 u2 u3 u4 u5 u6 u7 u10 u11 u12 u14 u15 u16 u17 u22 : word),
munch [(bv_unsigned sp - 192, bv_unsigned sp - 128); (SH A, SH A + ngran n')] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
stk asegs m1 lo (bv_unsigned sp + -128) -> RTconst RE X m1 ->
rw_cells asegs m1 (SH AB) [C1 fa_byte] ->
(n' / 8 <> 0 -> rw_cells asegs m1 (SH A) [CB (Z.to_nat (n' / 8)) (repeat (b8 0) (Z.to_nat (n' / 8)))]) ->
(n' mod 8 <> 0 -> rw_cells asegs m1 (SH A + n' / 8) [C1 (b8 (n' mod 8))]) ->
evt asegs Q (MS (mkR u (wz (bv_unsigned sp + -128)) gp (wz A_TP) u0 u1 u2 (wz 1) (wz n') u3 u4 u5 u6 u7 u10 u11 u12
(wz AB) (wz nd) (wz A) (wz (A + -16)) u22 (wz obj) (wz 0) (wz (A + n')) (wz (rl_T X)) (wz 1) u14 u15 u16 u17)
F (wz 0x3f7e0) fc None m1 (seg_rom asegs))) ->
evt asegs Q (MS (mkR (wz 0x3f640) (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 (wz 1) (wz n') a0 a1 a2 a3 a4 a5 a6 a7
(wz AB) (wz nd) (wz A) (wz (A + -16)) (wz A_INSTANCE) (wz obj) (wz 0) (wz (A + n')) (wz (rl_T X)) (wz 1) t3 t4 t5 t6)
F (wz 0x3f650) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT MI ST CEIL LO P1 P2 P3 CONT.
pose proof geomS as (Gc & Gsz & Gsz32 & Grz & Grz16 & Gn1 & Gn2 & Gn3 & Gnd1 & Gnd2 & Gnd8 & Gnd3 & GA16 & GK & GC & _).
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
assert (SHa : SH AB = AB / 8 + 0x7fff8000) by reflexivity.
assert (SHA : SH A = SH AB + rz / 8) by (subst A; rewrite <- SH_plus8; f_equal; clear - Grz16; Z.div_mod_to_equations; lia).
assert (N8 : 0 <= n' / 8 /\ 0 <= n' mod 8 < 8 /\ n' = 8 * (n' / 8) + n' mod 8) by (clear - Gn1; Z.div_mod_to_equations; lia).
pose proof (ngran_eq n' ltac:(lia)) as (NG1 & NG2 & NG3). pose proof (round_up_8 n' ltac:(lia)) as [RU8 _].
pose proof (munch_refl [(bv_unsigned sp - 192, bv_unsigned sp - 128); (SH A, SH A + ngran n')] m) as MU. pose proof (wmono_refl asegs m) as WM.
rtc RT 19%nat K19. rtc RT 5%nat K5.
step. if_lit.
step. step.
step.
step.
rewrite (unsigned_lit AB), Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
step.
replace (2147450880 + AB / 8) with (SH AB) by lia.
step.
unfold fa_byte at 1. lits.
step. if_lit.
stp. stp.
step.
rewrite (unsigned_lit n'), land_mask8_48 by lia. replace (n' - n' mod 8) with (8 * (n' / 8)) by lia.
assert (D8 : 8 * (n' / 8) / 8 = n' / 8) by (rewrite Z.mul_comm; apply Z.div_mul; lia).
step.
destruct (Z.eq_dec (n' / 8) 0) as [Q0|QP].
- ifz.
eapply alloc_partial; [exact RT| exact MI| exact P3|].
intros m1 u u0 u1 u2 u3 u4 u5 u6 u7 u10 u11 u12 u14 u15 u16 u17 u22 MUp WMp MIp RTp P3p.
transport_after_call asegs m m1 MUp WMp.
eapply CONT; [exact MU| exact WM| exact MIp| exact ST| exact RTp| exact P1| intros NE; exfalso; exact (NE Q0)| exact P3p].
- unfold_cond; cond_unsig; if_false.
step. step. step. step.
specialize (P2 QP). rewrite <- D8 in P2.
pose proof (munch_refl [(bv_unsigned sp - 192, bv_unsigned sp - 128); (SH A, SH A + n' / 8)] m) as MUx.
call_sp_ch (poison_shadow_spec RE X) ltac:(fun PO => rewrite ?D8 in PO);
[exact RT| exact RL| assumption| exact ST| exact CEIL'| lia
| clear - GA16; Z.div_mod_to_equations; lia| clear; Z.div_mod_to_equations; lia| lia| rewrite ?KHI_eq; lia| lia| lia| right; rewrite D8; lia| exact P2|].
match goal with H : stk asegs _ lo _ |- _ => try rename H into ST end.
match goal with H : RTconst RE X ?mm, H2 : rw_cells asegs ?mm (SH A) _ |- _ => rename H into RT1; rename H2 into P2z end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (P3x : n' mod 8 <> 0 -> rw_cells asegs mm (SH A + n' / 8) [C1 pb])
by (intros NE; eapply rw_cells_transport; [exact (P3 NE)| exact MUx| exact WM| cbn [disjoint_from cells_size csize]; lia]) end.
clear MUx.
eapply alloc_partial; [exact RT1| assumption| exact P3x|].
intros m1 u u0 u1 u2 u3 u4 u5 u6 u7 u10 u11 u12 u14 u15 u16 u17 u22 MUp WMp MIp RTp P3p.
lazymatch type of MUp with munch _ ?ma _ => transport_after_call asegs ma m1 MUp WMp end.
eapply CONT; [exact MU| exact WM| exact MIp| exact ST| exact RTp| exact P1| intros _; exact P2z| exact P3p].
Qed.
End S.
End Mqb.

Module Mqc.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig.
Import Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW Q61C QWRO Qu4g QFQR QmP7 QKBN QNQk.Mq6 QpY2.Mqb QYyZ.Mqb QmP7.Mq1 Q9Ho.Mq3 QYyZ.Mq8 QnRU.Mqc QnRU.Mqi QOJv.Mqc Qu3b QteI.Mqd.
Import Qc6I QJFf QDM6.
Import QCiC Qpj5.Mq1 QvDJ.Mq2 Q67d QCiC.Mq0.
Import QlES. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation mem := (word -> option byte) (only parsing).
Local Notation wz := (Z_to_bv 64).

Lemma coff_shl4 : forall RE c i, 1 <= c <= 31 -> 0 <= i -> reg_beg (ae_L RE) c + coff c i * 16 = slot_beg RE c i.
Proof.
intros RE c i Hc Hi. unfold coff, slot_beg. pose proof (class_size_facts c Hc) as [S1 S2].
assert (E : exists q, class_size c = 16 * q) by (exists (class_size c / 16); Z.div_mod_to_equations; lia).
destruct E as [q E]. rewrite E. replace (16 * q) with (q * 16) by lia. rewrite Z.div_mul by lia. lia.
Qed.

Lemma cr_pure_pop : forall a a' G c K t,
cr_pure a G c K -> 1 <= c <= 31 -> 1 <= c_count (cls a c) -> tag_prim t = false ->
cls a' c = set_count (c_count (cls a c) - 1) (cls a c) -> as_cache_inited a' = true ->
let CA := pk_ca K in let n1 := Z.to_nat (c_count (cls a c) - 1) in let i := nth n1 CA 0 in
cr_pure a' (set_tag c i t G) c (mkPK (pk_fl K) (firstn n1 CA)).
Proof.
intros a a' G c K t PU Hc CNT NP Ea EI CA n1 i.
destruct PU as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & G1 & G2 & G3 & G4 & G5).
fold CA in P2, P4, P6.
assert (LCA : length CA = S n1) by (subst n1; lia).
assert (HIN : In i CA) by (apply nth_In; lia).
pose proof (P6 i HIN) as TI. pose proof (tag_at_Some_lt _ _ _ _ TI) as [I0 _].
assert (ECA : CA = firstn n1 CA ++ [i]).
{ rewrite <- (firstn_skipn n1 CA) at 1. f_equal.
destruct (skipn n1 CA) as [|y l] eqn:E; [apply (f_equal (@length Z)) in E; rewrite length_skipn in E; cbn in E; lia|].
assert (L1 : l = []) by (apply (f_equal (@length Z)) in E; rewrite length_skipn in E; cbn in E; destruct l; [reflexivity| cbn in E; lia]).
subst l. f_equal. unfold i. rewrite <- (firstn_skipn n1 CA) at 1. rewrite app_nth2 by (rewrite length_firstn; lia).
rewrite length_firstn. replace (n1 - Nat.min n1 (length CA))%nat with 0%nat by lia. rewrite E. reflexivity. }
assert (NI : ~ In i (firstn n1 CA)).
{ intros Hin. rewrite ECA in P4. apply NoDup_remove_2 in P4. apply P4. rewrite app_nil_r. exact Hin. }
assert (NIF : ~ In i (pk_fl K)).
{ intros Hin. pose proof (P5 i Hin) as TF. rewrite TI in TF. discriminate. }
unfold cr_pure. rewrite Ea, EI. cbn [pk_fl pk_ca set_count c_count c_num_freed c_mapped_fa c_alloc_user c_mapped_user].
repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
- rewrite length_firstn. lia.
- apply NoDup_firstn. exact P4.
- intros j Hj. rewrite tag_at_set_tag_ne; [apply P5; exact Hj| exact I0| right; intros ->; exact (NIF Hj)].
- intros j Hj. rewrite tag_at_set_tag_ne; [apply P6; exact (In_firstn_In _ _ _ Hj)| exact I0| right; intros ->; exact (NI Hj)].
- rewrite (count_tag_set_tag _ G c i t TCached TI). rewrite P7. destruct t; cbn in NP |- *; try discriminate; lia.
- rewrite (count_tag_set_tag _ G c i t TCached TI). rewrite P8. destruct t; cbn in NP |- *; try discriminate; lia.
- pose proof (ncarved_set_tag c i t G c) as NC. unfold ncarved in NC. rewrite NC. exact G1.
Qed.

Lemma pop_close {BAND : Band} : forall (a a' : AState) G RE X (m m' : mem) c (K : Z -> pcls),
let x := cls a c in let cnt := c_count x in
let CA := pk_ca (K c) in let n1 := Z.to_nat (cnt - 1) in let i := nth n1 CA 0 in
rlay_ok RE X -> 1 <= c <= 30 -> as_cache_inited a = true -> 1 <= cnt ->
cls a' c = set_count (cnt - 1) x -> (forall c0, c0 <> c -> cls a' c0 = cls a c0) -> as_cache_inited a' = true ->
hjunk m (rl_T X + 2768) (rl_T X + 2800) ->
(forall c0, G c0 <> [] -> 1 <= c0 < kNumClasses) ->
(forall c0, 0 <= c0 < kNumClasses -> class_rep a G RE X m c0 (K c0)) ->
wmono asegs m m' ->
(forall c0, 0 <= c0 < kNumClasses -> c0 <> c -> agree_on asegs (fp_cls RE X c0) m m') ->
agree_on asegs (fun z => fp_cls RE X c z /\ ~ (pc_addr X c <= z < pc_addr X c + 4)) m m' ->
rw_cells asegs m' (pc_addr X c) [C4 (wz (cnt - 1))] ->
tag_at G c i = Some TCached
/\ (exists CH, u32arr asegs m (pc_addr X c + 16) CH /\ length CH = 16%nat /\ nth_error CH n1 = Some (wz (coff c i)))
/\ (forall t, tag_prim t = false -> RPrim a' (set_tag c i t G) RE X m')
/\ hjunk m' (slot_beg RE c i) (slot_beg RE c i + class_size c)
/\ rw_cells asegs m' (SH (slot_beg RE c i)) [CB (Z.to_nat (class_size c / 8)) (repeat fa_byte (Z.to_nat (class_size c / 8)))].
Proof.
intros until K; intros x cnt CA n1 i RL Hc EI CNT Ea EO EI' HJS GNE HCall WM OTH AG PCk.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (HCall c ltac:(rewrite K32; lia)) as HC.
pose proof HC as (((j1 & j2 & j3 & j4 & RI) & PC & (CH & ACH & LCH & HCH)) & PU & REG).
pose proof PU as (P1 & P2 & P3 & P4 & P5 & P6 & _). fold CA in P2, P4, P6, HCH.
assert (LCA : length CA = S n1) by (subst n1 cnt x; lia).
assert (HIN : In i CA) by (apply nth_In; lia).
pose proof (P6 i HIN) as TI. pose proof (tag_at_Some_lt _ _ _ _ TI) as [I0 _].
specialize (REG ltac:(lia)). destruct REG as (FA & FJ & SL & UT & SS & US & UJ & FS).

pose proof (reg_geom RE X RL c ltac:(lia)) as (RB & FB & PAL & PK & PCH & PH & RIq).
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB, TD.
unfold iv_disjoint in TD; cbn [fst snd] in TD. idtac. rewrite ?KHI_eq in TK.
assert (NPC : forall z, (z < rl_T X \/ rl_T X + 4096 <= z) -> ~ (pc_addr X c <= z < pc_addr X c + 4)) by (intros z Hz; unfold pc_addr; lia).
assert (AGU : agree_on asegs (uzone RE c) m m').
{ eapply agree_on_mono; [exact AG|]. intros z Uz. split.
- destruct Uz as [Uz|Uz]; [do 4 right; left; exact Uz| do 5 right; exact Uz].
- apply NPC. apply (uzone_bounds RE X c z RL ltac:(lia)) in Uz. rewrite RB in Uz. unfold SH, A_SHADOW_OFS in Uz.
clear - Uz TD PK PCH PH TK Hc. Z.div_mod_to_equations. lia. }
assert (AGFA : agree_on asegs (fun z => fa_beg (ae_L RE) c <= z < fa_beg (ae_L RE) c + kFreeArraySize) m m').
{ eapply agree_on_mono; [exact AG|]. intros z Hz. split; [do 2 right; left; exact Hz| apply NPC]. rewrite FB, KS in Hz. clear - Hz TD PK Hc. lia. }
assert (AGFS : agree_on asegs (in_sh (fa_beg (ae_L RE) c, kFreeArraySize)) m m').
{ eapply agree_on_mono; [exact AG|]. intros z Hz. split; [do 3 right; left; exact Hz| apply NPC]. unfold in_sh in Hz. cbn [fst snd] in Hz.
rewrite FB, KS in Hz. unfold SH, A_SHADOW_OFS in Hz. clear - Hz TD PK PCH PH TK Hc. Z.div_mod_to_equations. lia. }
split; [exact TI|]. split; [exists CH; split; [exact ACH| split; [exact LCH| apply HCH; lia]]|].
split; [| split].
2:{ eapply hjunk_wmono; [exact (SL i TCached TI eq_refl)| exact WM]. }
2:{ pose proof (cr_user_agree a G RE m m' c (K c) PU (conj SL (conj UT (conj SS (conj US UJ)))) ltac:(lia) AGU) as (_ & _ & SS' & _).
exact (SS' i TCached TI eq_refl). }
intros t NP.
exists (fun c0 => if c0 =? c then mkPK (pk_fl (K c)) (firstn n1 CA) else K c0).
split; [eapply hjunk_wmono; [exact HJS| exact WM]|]. split.
{ intros c0 NE0. apply GNE. destruct (Z.eq_dec c0 c) as [->|NE]; [| rewrite set_tag_other_class in NE0 by exact NE; exact NE0].
intros E. apply NE0. apply length_zero_iff_nil. pose proof (ncarved_set_tag c i t G c) as NC. unfold ncarved in NC.
rewrite <- Nat2Z.inj_iff. rewrite NC, E. reflexivity. }
intros c0 Hc0. destruct (Z.eqb_spec c0 c) as [->|NE].
2:{ eapply class_rep_ext; [| apply EO; exact NE| rewrite EI, EI'; reflexivity| apply set_tag_other_class; exact NE].
eapply class_rep_agree; [apply HCall; exact Hc0| rewrite K32 in Hc0; exact Hc0| apply OTH; [exact Hc0| exact NE]]. }
apply class_rep_split. split; [| split].
- unfold cr_cells. rewrite Ea, EI'. cbn [pk_ca set_count c_count c_num_freed c_mapped_fa c_alloc_user c_mapped_user].
split; [| split].
+ exists j1, j2, j3, j4. eapply rw_cells_agree; [exact AG| exact RI|]. intros z Hz. cbn [ri_cells cells_size csize Nat.add] in Hz.
split; [left; exact Hz| apply NPC]. unfold ri_addr in Hz. rewrite RIq in Hz. clear - Hz TD PK Hc. lia.
+ apply (proj2 (rw_cells_app asegs _ _ [C4 (wz (cnt - 1))] _)). cbn [cells_size csize Nat.add]. split; [exact PCk|].
cbv beta delta [pc_cells] in PC. rewrite EI in PC. apply (proj1 (rw_cells_app asegs _ _ [C4 (wz cnt)] _)) in PC as [_ PCt].
cbn [cells_size csize Nat.add] in PCt. eapply rw_cells_agree; [exact AG| exact PCt|]. intros z Hz. cbn [cells_size csize Nat.add] in Hz.
split; [right; left; lia| lia].
+ exists CH. split; [| split; [exact LCH|]].
* eapply u32arr_agree; [exact AG| exact ACH|]. intros z Hz. rewrite LCH in Hz. split; [right; left; cbn in Hz; lia| cbn in Hz; lia].
* intros j Hj. rewrite length_firstn in Hj. rewrite HCH by lia. rewrite nth_firstn. replace (Nat.ltb j n1) with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
- apply (cr_pure_pop a a' G c (K c) t PU ltac:(lia) CNT NP Ea EI').
- intros _. rewrite Ea. cbn [pk_fl set_count c_count c_num_freed c_mapped_fa c_alloc_user c_mapped_user].
split; [eapply u32arr_agree; [exact AGFA| exact FA|]; intros z Hz; rewrite length_map, P1 in Hz; pose proof PU as (_&_&_&_&_&_&_&_&_&_&_& P12 & P13 &_); lia|].
split; [eapply hjunk_wmono; [exact FJ| exact WM]|]. split; [| eapply hjunk_wmono; [exact FS| exact WM]].
eapply (cr_user_retag a a' G); [| | rewrite Ea; reflexivity| rewrite Ea; reflexivity].
+ eapply cr_user_agree; [exact PU| exact (conj SL (conj UT (conj SS (conj US UJ))))| lia| exact AGU].
+ intros i' t' Ht' Hp'. destruct (Z.eq_dec i' i) as [->|NE].
* rewrite (tag_at_set_tag_eq G c i t TCached TI) in Ht'. inversion Ht'; subst t'. rewrite NP in Hp'. discriminate.
* rewrite tag_at_set_tag_ne in Ht'; [exists t'; split; assumption| exact I0| right; exact NE].
Qed.

Section Model.
Variable L : ALay.
Local Notation TT := (fun (_ : evA) (_ : ansA) => True).

Lemma get_from_allocator_inited a c k :
tall TT (okrel (fun r => as_cache_inited (snd r) = as_cache_inited a)) (get_from_allocator L a c k).
Proof.
eapply tall_mono; [apply get_from_allocator_prel|]. intros [[b s1]| |w]; cbn; try exact (fun x => x).
intros (_ & EI & _). exact EI.
Qed.

Lemma refill_facts a c :
tall TT (okrel (fun r => as_cache_inited (snd r) = true /\ (fst r = true -> c_count (cls (snd r) c) = max_count c / 2))) (refill L a c).
Proof.
unfold refill. eapply tall_bind_ok with (P1 := fun r => as_cache_inited (snd r) = true).
{ eapply tall_mono; [apply get_from_allocator_inited|]. intros [[b s1]| |w]; cbn; exact (fun x => x). }
intros [ok s1] H1. cbn in H1. destruct ok; cbn [negb]; apply tall_ret; cbn.
- split; [exact H1|]. intros _. unfold upd_cls. rewrite cls_set_cls_eq. reflexivity.
- split; [exact H1| intros E; discriminate].
Qed.
End Model.
End Mqc.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Uaccess.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVsB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDM6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDM6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdZp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdZp.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QteI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QteI.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QoSL.solve_load ::= QbcP_c1.mkr__solve_load_1.
Local Unset Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

Definition STDIO_WRITE : Z := 0xd5094.
Definition STDIO_WRITE_DEPTH : Z := 112.

Lemma dec_writev_Some : forall total rsp k, dec_writev total rsp = Some k ->
rsp = eff0 (Z_to_bv 64 k) /\ ((total = 0 /\ k = 0) \/ (1 <= k <= total)) /\ (0 <= k < 2^64).
Proof.
intros total [r ws zs us cs ci] k H. unfold dec_writev in H.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
destruct cs; [|discriminate]. destruct ci; [|discriminate].
pose proof (bv_unsigned_in_range 64 r) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2^64) in R.
destruct (((total =? 0) && (bv_unsigned r =? 0)) || ((1 <=? bv_unsigned r) && (bv_unsigned r <=? total)))%bool eqn:E; [|discriminate].
inversion H; subst. split. { unfold eff0. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split; [|lia]. apply Bool.orb_prop in E. destruct E as [E|E]; apply andb_prop in E; destruct E as [E1 E2].
- left. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. lia.
- right. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
Qed.

Section Glue.
Context {St : Type}.

Lemma implM_sys_k : forall {A B} (n : node) (dec : resp -> option A) (k : A -> M St B) (s0 : St)
(Q : B -> St -> machine_state -> Prop) ms,
evt asegs (fun ms1 : machine_state => at_node asegs n ms1 /\
(forall (rsp : resp) (a : A), dec rsp = Some a -> implM asegs (k a) s0 Q (nret ms1 rsp))) ms ->
implM asegs (Qpj5.Mq1.mbind (msys n dec) k) s0 Q ms.
Proof.
intros A B n dec k s0 Q ms H.
eapply implM_bind with (Q1 := fun a s' ms' => s' = s0 /\ implM asegs (k a) s0 Q ms').
- apply implM_sys. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
intros rsp a E. apply evt_done. split; [reflexivity|]. exact (Hk rsp a E).
- intros a s' ms' [-> H']. exact H'.
Qed.
End Glue.

Lemma land_ones64_l : forall x, (0 <= x < 2^64)%Z -> Z.land 18446744073709551615 x = x.
Proof. intros x Hx. rewrite Z.land_comm. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma land_0_l' : forall x, Z.land 0 x = 0.
Proof. intros. apply Z.land_0_l. Qed.
Lemma to_bytes_skipn : forall k (l : list Z), to_bytes (skipn k l) = skipn k (to_bytes l).
Proof. intros k l. unfold to_bytes. rewrite skipn_map. reflexivity. Qed.
Lemma bytes_at_skipn : forall segs m a bs k, bytes_at segs m a bs -> (k <= length bs)%nat ->
bytes_at segs m (a + Z.of_nat k) (skipn k bs).
Proof.
intros segs m a bs k H Hk. rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. destruct H as [_ H].
rewrite length_firstn, Nat.min_l in H by lia. exact H.
Qed.

Lemma zlength_skipn : forall (k : nat) (l : list Z), (k <= length l)%nat -> zlength (skipn k l) = zlength l - Z.of_nat k.
Proof. intros. unfold zlength. rewrite length_skipn. lia. Qed.
Lemma wv_advance_move : forall v0 v1 cnt, zlength v0 < cnt ->
wv_advance [v0; v1] cnt = [skipn (Z.to_nat (cnt - zlength v0)) v1].
Proof. intros. unfold wv_advance. replace (zlength v0 <? cnt) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.
Lemma wv_advance_stay : forall v0 rest cnt, cnt <= zlength v0 ->
wv_advance (v0 :: rest) cnt = skipn (Z.to_nat cnt) v0 :: rest.
Proof. intros. unfold wv_advance. replace (zlength v0 <? cnt) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.
Lemma skipn_skipn' : forall {A} (a b : nat) (l : list A), skipn a (skipn b l) = skipn (b + a) l.
Proof. intros. rewrite skipn_skipn. f_equal. lia. Qed.

Definition boxed (P : Prop) : Prop := P.

Ltac src_now SRC SEPS MU LSB :=
unfold boxed in SRC;
lazymatch goal with
| |- bytes_at _ ?m' ?S (to_bytes ?s) =>
destruct SEPS as [-> | [SEP1 SEP2]];
[ apply bytes_at_nil; lia
| apply (bytes_at_transport _ _ _ m' _ _ SRC MU); cbn [disjoint_from]; rewrite LSB; unfold zlength in SEP1, SEP2; lia ]
end.
Lemma length_to_bytes : forall l, length (to_bytes l) = length l.
Proof. intros. unfold to_bytes. apply length_map. Qed.
Lemma evt_evt : forall P ms, evt asegs P ms -> evt asegs (fun ms' => evt asegs P ms') ms.
Proof. intros P ms H. eapply evt_mono; [exact H|]. intros ms' H'. apply evt_done. exact H'. Qed.

Ltac lit_ret_pc :=
lazymatch goal with
| |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
end.

Ltac sysret_fast :=
step; step; step; step;
let Hc := fresh "Hc" in
if_cases Hc; zify_cond Hc; [| exfalso; lia]; step; try lit_ret_pc.

Section StdioWrite.
Context {BAND : Band}.
Context {St : Type}.

Definition stdio_write_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp : Z) (flags : word) (B bufsize wfn fd : Z) (mode : word) (lbf : Z) (tail : list byte)
(l : Z) (lo : Z) (canary : word) (m : mem) (st : St) : unit -> St -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 l) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - STDIO_WRITE_DEPTH, bv_unsigned sp); (Fp + 32, Fp + 64)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' Fp (file_cells flags (B + bufsize) B B wfn B bufsize fd mode lbf tail)
/\ ssp_cells m' canary
/\ st' = st.

Section Fixed.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St).
Variables (Fp : Z) (flags : word) (wend B bufsize wfn fd : Z) (mode : word) (lbf : Z) (tail : list byte).
Variables (buf s : list Z) (S lo : Z) (canary : word).
Hypothesis FD : fd = 1 \/ fd = 2.
Hypothesis LO : lo <= bv_unsigned sp - 112.
Hypothesis GLO : band_lo <= lo.
Hypothesis Fp0 : 0 <= Fp.
Hypothesis FPLO : Fp + 232 <= lo.
Hypothesis FSEP1 : Fp + 232 <= 0xe8f90 \/ 0xe8f90 + 8 <= Fp.
Hypothesis FSEP2 : Fp + 232 <= 0x645560 \/ 0x645560 + 8 <= Fp.
Hypothesis B0 : 0 <= B. Hypothesis BS0 : 0 <= bufsize. Hypothesis BUFLE : Z.of_nat (length buf) <= bufsize. Hypothesis BShi : B + bufsize <= 2^47.
Hypothesis LENS : Z.of_nat (length buf) + Z.of_nat (length s) <= 2^26.
Hypothesis S0 : 0 <= S < 2^64. Hypothesis Shi : S + Z.of_nat (length s) <= 2^47.
Hypothesis SEPS : s = [] \/ ((S + Z.of_nat (length s) <= lo \/ bv_unsigned sp <= S) /\ (S + Z.of_nat (length s) <= Fp + 32 \/ Fp + 64 <= S)).
Hypothesis SEPB : B + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= B.
Hypothesis SPHI : 0 <= bv_unsigned sp <= 2^47.
Hypothesis BUFB : bytes_at asegs m B (to_bytes buf).
Hypothesis SRC : bytes_at asegs m S (to_bytes s).

Local Notation W0 := ([(bv_unsigned sp - 112, bv_unsigned sp)] : list (Z * Z)).
Local Notation W := ([(bv_unsigned sp - 112, bv_unsigned sp); (Fp + 32, Fp + 64)] : list (Z * Z)).
Let POSTQ := stdio_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp flags B bufsize wfn fd mode lbf tail (Z.of_nat (length s)) lo canary m st.

Definition frame (mc : mem) (j8 : list byte) (p0 n0 p1 n1 : Z) : Prop :=
rw_cells asegs mc (bv_unsigned sp + -112)
[CB 8 j8; C8 (Z_to_bv 64 p0); C8 (Z_to_bv 64 n0); C8 (Z_to_bv 64 p1); C8 (Z_to_bv 64 n1); C8 canary;
C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma succ_tail : forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x6 t3 t4 t5 t6 : word) (mc : mem) j8 p0 n0 p1 n1,
frame mc j8 p0 n0 p1 n1 ->
rw_cells asegs mc Fp (file_cells flags wend (B + Z.of_nat (length buf)) B wfn B bufsize fd mode lbf tail) ->
rw_cells asegs mc 0xe8f90 [C8 (Z_to_bv 64 0x645560)] -> rw_cells asegs mc 0x645560 [C8 canary] ->
munch W0 m mc -> wmono asegs m mc -> mem_inv asegs mc -> stk asegs mc lo (bv_unsigned sp - 112) ->
evt asegs (POSTQ tt st)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 (Z.of_nat (length s))) (Z_to_bv 64 Fp)
a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 (Z_to_bv 64 0x645560) x6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd5128) fc None mc (seg_rom asegs)).
Proof.
intros until n1. intros FR FC GOT GUARD MU0 WM MI ST. subst POSTQ.
assert (MU : munch W m mc).
{ eapply munch_weaken; [|exact MU0]. unfold sub_fp; cbn [outside]; intros; lia. }
clear MU0. unfold frame in FR. unfold file_cells in FC.
do 6 step. step. step. step. step. if_false.
do 10 step.
release_frame FR ST (bv_unsigned sp).
unfold stdio_write_post, file_cells, STDIO_WRITE_DEPTH. sys_finish.
+ split; [exact GOT| exact GUARD].
+ reflexivity.
Qed.

Definition iovsZ (two : bool) (i j : Z) : list (list Z) :=
if two then [skipn (Z.to_nat i) buf; skipn (Z.to_nat j) s] else [skipn (Z.to_nat j) s].
Definition remZ (two : bool) (i j : Z) : Z :=
(if two then Z.of_nat (length buf) - i else 0) + (Z.of_nat (length s) - j).

Lemma adv_move : forall i j cnt, 0 <= i <= Z.of_nat (length buf) -> 0 <= j -> Z.of_nat (length buf) - i < cnt ->
wv_advance (iovsZ true i j) cnt = iovsZ false i (j + (cnt - (Z.of_nat (length buf) - i))).
Proof.
intros i j cnt Hi Hj Hc. unfold iovsZ. rewrite wv_advance_move by (rewrite zlength_skipn by lia; unfold zlength; lia).
rewrite zlength_skipn by lia. unfold zlength. rewrite skipn_skipn'. f_equal. f_equal. lia.
Qed.
Lemma adv_stay2 : forall i j cnt, 0 <= i <= Z.of_nat (length buf) -> 0 <= cnt <= Z.of_nat (length buf) - i ->
wv_advance (iovsZ true i j) cnt = iovsZ true (i + cnt) j.
Proof.
intros i j cnt Hi Hc. unfold iovsZ. rewrite wv_advance_stay by (rewrite zlength_skipn by lia; unfold zlength; lia).
rewrite skipn_skipn'. f_equal. f_equal. lia.
Qed.
Lemma adv_stay1 : forall i j cnt, 0 <= j <= Z.of_nat (length s) -> 0 <= cnt <= Z.of_nat (length s) - j ->
wv_advance (iovsZ false i j) cnt = iovsZ false i (j + cnt).
Proof.
intros i j cnt Hj Hc. unfold iovsZ. rewrite wv_advance_stay by (rewrite zlength_skipn by lia; unfold zlength; lia).
rewrite skipn_skipn'. f_equal. f_equal. lia.
Qed.

Lemma src_at : forall mc k, munch W0 m mc -> (k <= length s)%nat ->
bytes_at asegs mc (S + Z.of_nat k) (to_bytes (skipn k s)).
Proof.
intros mc k MU Hk. destruct SEPS as [-> | [SEP1 SEP2]].
- rewrite skipn_nil. cbn [to_bytes map]. apply bytes_at_nil. cbn in Hk. lia.
- rewrite to_bytes_skipn. apply bytes_at_skipn; [| rewrite length_to_bytes; exact Hk].
apply (bytes_at_transport _ _ _ mc _ _ SRC MU). cbn [disjoint_from]. rewrite length_to_bytes. lia.
Qed.
Lemma buf_at : forall mc k, munch W0 m mc -> (k <= length buf)%nat ->
bytes_at asegs mc (B + Z.of_nat k) (to_bytes (skipn k buf)).
Proof.
intros mc k MU Hk.
rewrite to_bytes_skipn. apply bytes_at_skipn; [| rewrite length_to_bytes; exact Hk].
apply (bytes_at_transport _ _ _ mc _ _ BUFB MU). cbn [disjoint_from]. rewrite length_to_bytes. lia.
Qed.

Lemma src_iov : forall mc j, munch W0 m mc -> 0 <= j <= Z.of_nat (length s) ->
bytes_at asegs mc (bv_unsigned (Z_to_bv 64 (S + j))) (to_bytes (skipn (Z.to_nat j) s)).
Proof.
intros mc j MU Hj. destruct (Z.eq_dec (S + j) (2^64)) as [E|NE].
- rewrite skipn_all2 by lia. cbn [to_bytes map]. apply bytes_at_nil.
pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 (S + j))) as R. unfold bv_modulus in R. cbn in R. lia.
- rewrite unsigned_lit by lia. replace (S + j) with (S + Z.of_nat (Z.to_nat j)) by lia. apply src_at; [exact MU| lia].
Qed.
Lemma buf_iov : forall mc i, munch W0 m mc -> 0 <= i <= Z.of_nat (length buf) ->
bytes_at asegs mc (bv_unsigned (Z_to_bv 64 (B + i))) (to_bytes (skipn (Z.to_nat i) buf)).
Proof.
intros mc i MU Hi. rewrite unsigned_lit by lia. replace (B + i) with (B + Z.of_nat (Z.to_nat i)) by lia. apply buf_at; [exact MU| lia].
Qed.

Lemma wnode : forall ms1 (two : bool) i j p0 n0 p1 n1 j8,
ms_svc_pending ms1 = Some (Z_to_bv 64 66) -> ms_rom ms1 = seg_rom asegs ->
areg ms1 10 = Z_to_bv 64 fd -> areg ms1 12 = Z_to_bv 64 (if two then 2 else 1) ->
areg ms1 11 = Z_to_bv 64 (bv_unsigned sp + (if two then -104 else -88)) ->
frame (ms_mem ms1) j8 p0 n0 p1 n1 -> munch W0 m (ms_mem ms1) ->
(if two then p0 = B + i /\ n0 = Z.of_nat (length buf) - i else True) ->
p1 = S + j -> n1 = Z.of_nat (length s) - j ->
0 <= i <= Z.of_nat (length buf) -> 0 <= j <= Z.of_nat (length s) ->
at_node asegs (NWritev fd (map to_bytes (iovsZ two i j))) ms1.
Proof.
intros ms1 two i j p0 n0 p1 n1 j8 SVC ROM R10 R12 R11 FR MU TWO -> -> Hi Hj.
cbn [at_node]. rewrite SVC, ROM, R10, R11, R12. clear SVC ROM R10 R11 R12. unfold frame in FR.
destruct FR as [[WF FB] _]. cbn [cells_wf cell_wf] in WF. destruct WF as [L8 _]. cbn [cells_bytes cbytes] in FB.
apply bytes_at_app in FB as [_ FB]. rewrite L8 in FB.
apply bytes_at_app in FB as [FB1 FB]. rewrite length_le8 in FB.
apply bytes_at_app in FB as [FB2 FB]. rewrite length_le8 in FB.
apply bytes_at_app in FB as [FB3 FB]. rewrite length_le8 in FB.
apply bytes_at_app in FB as [FB4 _].
destruct two.
- destruct TWO as [-> ->]. unfold iovsZ. cbn [map length concat app].
split_spine; try reflexivity; try lia.
+ rewrite app_nil_r, length_app, !length_to_bytes, !length_skipn. unfold QJFf.writev_bytes_max. lia.
+ exists [(Z_to_bv 64 (B + i), Z_to_bv 64 (Z.of_nat (length buf) - i)); (Z_to_bv 64 (S + j), Z_to_bv 64 (Z.of_nat (length s) - j))]. split; [|split; [|split]].
3:{ rewrite unsigned_lit by lia. unfold TASK_SIZE. cbn [length]. lia. }
3:{ constructor; [|constructor; [|constructor]]; cbn [fst snd]; rewrite !unsigned_lit by lia; unfold TASK_SIZE; lia. }
* rewrite unsigned_lit by lia. cbn [iovec_bytes flat_map fst snd]. rewrite app_nil_r.
apply bytes_at_app. rewrite length_app, !length_le8. split.
-- apply bytes_at_app. rewrite length_le8. split.
++ match type of FB1 with bytes_at _ _ ?a _ => replace (bv_unsigned sp + -104) with a by lia end. exact FB1.
++ match type of FB2 with bytes_at _ _ ?a _ => replace (bv_unsigned sp + -104 + Z.of_nat 8) with a by lia end. exact FB2.
-- apply bytes_at_app. rewrite length_le8. split.
++ match type of FB3 with bytes_at _ _ ?a _ => replace (bv_unsigned sp + -104 + Z.of_nat (8 + 8)) with a by lia end. exact FB3.
++ match type of FB4 with bytes_at _ _ ?a _ => replace (bv_unsigned sp + -104 + Z.of_nat (8 + 8) + Z.of_nat 8) with a by lia end. exact FB4.
* constructor; [| constructor; [|constructor]].
-- split; [cbn [snd]; f_equal; rewrite length_to_bytes, length_skipn; lia|]. cbn [fst]. apply buf_iov; [exact MU| lia].
-- split; [cbn [snd]; f_equal; rewrite length_to_bytes, length_skipn; lia|]. cbn [fst]. apply src_iov; [exact MU| lia].
- unfold iovsZ. cbn [map length concat app].
split_spine; try reflexivity; try lia.
+ rewrite app_nil_r, !length_to_bytes, !length_skipn. unfold QJFf.writev_bytes_max. lia.
+ exists [(Z_to_bv 64 (S + j), Z_to_bv 64 (Z.of_nat (length s) - j))]. split; [|split; [|split]].
3:{ rewrite unsigned_lit by lia. unfold TASK_SIZE. cbn [length]. lia. }
3:{ constructor; [|constructor]; cbn [fst snd]; rewrite !unsigned_lit by lia; unfold TASK_SIZE; lia. }
* rewrite unsigned_lit by lia. cbn [iovec_bytes flat_map fst snd]. rewrite app_nil_r.
apply bytes_at_app. rewrite length_le8. split.
-- match type of FB3 with bytes_at _ _ ?a _ => replace (bv_unsigned sp + -88) with a by lia end. exact FB3.
-- match type of FB4 with bytes_at _ _ ?a _ => replace (bv_unsigned sp + -88 + Z.of_nat 8) with a by lia end. exact FB4.
* constructor; [| constructor].
split; [cbn [snd]; f_equal; rewrite length_to_bytes, length_skipn; lia|]. cbn [fst]. apply src_iov; [exact MU| lia].
Qed.

Ltac use_wnode FR MU :=
eapply wnode;
[ reflexivity | reflexivity
| at_node_red; reflexivity | at_node_red; reflexivity | at_node_red; reflexivity
| cbn [ms_mem MSsvc MS]; exact FR | cbn [ms_mem MSsvc MS]; exact MU
| first [exact I | split; lia] | lia | lia | lia | lia ].

Lemma retry_loop : forall (f : nat) (two : bool) (i j cnt : Z) (vs2 vs3 vs6 : Z)
(x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x20 t3 t4 t5 t6 : word) (mc : mem) j8 p0 n0 p1 n1,
(0 <= i <= Z.of_nat (length buf)) -> (0 <= j <= Z.of_nat (length s)) ->
(1 <= cnt < remZ two i j) ->
(if two then p0 = B + i /\ n0 = Z.of_nat (length buf) - i else True) ->
p1 = S + j -> n1 = Z.of_nat (length s) - j ->
vs2 = (if two then 2 else 1) -> vs3 = bv_unsigned sp + (if two then -104 else -88) -> vs6 = remZ two i j ->
frame mc j8 p0 n0 p1 n1 ->
rw_cells asegs mc Fp (file_cells flags wend (B + Z.of_nat (length buf)) B wfn B bufsize fd mode lbf tail) ->
rw_cells asegs mc 0xe8f90 [C8 (Z_to_bv 64 0x645560)] -> rw_cells asegs mc 0x645560 [C8 canary] ->
munch W0 m mc -> wmono asegs m mc -> mem_inv asegs mc -> stk asegs mc lo (bv_unsigned sp - 112) ->
implM asegs (mloop f (wv_body (St:=St) fd) (wv_advance (iovsZ two i j) cnt, remZ two i j - cnt)) st POSTQ
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 (Z.of_nat (length s))) (Z_to_bv 64 Fp)
(Z_to_bv 64 cnt) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 vs2) (Z_to_bv 64 vs3) x20 (Z_to_bv 64 0x645560) (Z_to_bv 64 vs6) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd51b4) fc None mc (seg_rom asegs)).
Proof.
induction f as [|f IH]; intros until n1; intros Hi Hj Hcnt TWO P1 N1 E2 E3 E6 FR FC GOT GUARD MU WM MI ST.
{ cbn [mloop]. apply implM_unr. }
unfold frame in FR. unfold file_cells in FC.
destruct two.
- destruct TWO as [P0 N0]. change (vs2 = 2) in E2. change (vs3 = bv_unsigned sp + -104) in E3. subst vs2 vs3.
destruct (Z_lt_le_dec n0 cnt) as [LT|GE].
+
rewrite adv_move by lia.
replace (remZ true i j - cnt) with (remZ false i (j + (cnt - (Z.of_nat (length buf) - i)))) by (unfold remZ; lia).
unfold remZ in Hcnt, E6.
apply implM_loop_S. unfold wv_body at 1. cbn [fst snd]. apply implM_sys_k.
step. if_cases K0; zify_cond K0. { exfalso. lia. }
step. step.
replace (v_sltu (Z_to_bv 64 n0) (Z_to_bv 64 cnt)) with (Z_to_bv 64 1)
by (unfold v_sltu, c_ltu, bv_ltu; rewrite !unsigned_lit by lia; destruct (Z.ltb_spec0 n0 cnt); [reflexivity|lia]).
zstep. zstep. zstep. zstep. zstep. rewrite ?land_ones64_l by lia. zstep. zstep. zstep.
zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
zstep. zstep. zstep.
replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd) by (symmetry; apply sx32_lit; lia).
step_ecall. split.
{ use_wnode FR MU. }
intros rsp a Hdec. apply dec_writev_Some in Hdec. destruct Hdec as (-> & Hk & Ha). unfold remZ in Hk.

eapply implM_evt; [| intros ms' HP; exact HP]. unfold eff0. sys_nret. sysret_fast. step. step. apply evt_done.
destruct (Z.eq_dec a (remZ false i (j + (cnt - (Z.of_nat (length buf) - i))))) as [Heq|Hne].
* replace (a =? remZ false i (j + (cnt - (Z.of_nat (length buf) - i)))) with true by (symmetry; apply Z.eqb_eq; exact Heq). unfold remZ in Heq. apply implM_ret. cbv beta iota. apply evt_evt.
if_cases Hb; zify_cond Hb. 2:{ exfalso. lia. }
eapply succ_tail; [exact FR | exact FC | exact GOT | exact GUARD | exact MU | exact WM | exact MI | exact ST].
* replace (a =? _) with false by (symmetry; apply Z.eqb_neq; exact Hne). unfold remZ in Hne.
apply implM_ret. cbv beta iota.
if_cases Hb; zify_cond Hb. { exfalso. lia. }
apply evt_done. eapply IH; try eassumption; try reflexivity; unfold remZ; first [lia | exact I | split; lia].
+
rewrite adv_stay2 by lia.
replace (remZ true i j - cnt) with (remZ true (i + cnt) j) by (unfold remZ; lia).
unfold remZ in Hcnt, E6.
apply implM_loop_S. unfold wv_body at 1. cbn [fst snd]. apply implM_sys_k.
step. if_cases K0; zify_cond K0. { exfalso. lia. }
step. step.
replace (v_sltu (Z_to_bv 64 n0) (Z_to_bv 64 cnt)) with (Z_to_bv 64 0)
by (unfold v_sltu, c_ltu, bv_ltu; rewrite !unsigned_lit by lia; destruct (Z.ltb_spec0 n0 cnt); [lia|reflexivity]).
zstep. zstep. zstep. zstep. zstep. rewrite ?land_0_l'. zstep. zstep. zstep.
zstep. if_cases K1; zify_cond K1. 2:{ exfalso. lia. }
zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
zstep. zstep.
replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd) by (symmetry; apply sx32_lit; lia).
step_ecall. split.
{ use_wnode FR MU. }
intros rsp a Hdec. apply dec_writev_Some in Hdec. destruct Hdec as (-> & Hk & Ha). unfold remZ in Hk.

eapply implM_evt; [| intros ms' HP; exact HP]. unfold eff0. sys_nret. sysret_fast. step. step. apply evt_done.
destruct (Z.eq_dec a (remZ true (i + cnt) j)) as [Heq|Hne].
* replace (a =? remZ true (i + cnt) j) with true by (symmetry; apply Z.eqb_eq; exact Heq). unfold remZ in Heq. apply implM_ret. cbv beta iota. apply evt_evt.
if_cases Hb; zify_cond Hb. 2:{ exfalso. lia. }
eapply succ_tail; [exact FR | exact FC | exact GOT | exact GUARD | exact MU | exact WM | exact MI | exact ST].
* replace (a =? _) with false by (symmetry; apply Z.eqb_neq; exact Hne). unfold remZ in Hne.
apply implM_ret. cbv beta iota.
if_cases Hb; zify_cond Hb. { exfalso. lia. }
apply evt_done. eapply IH; try eassumption; try reflexivity; unfold remZ; first [lia | exact I | split; lia].
-
change (vs2 = 1) in E2. change (vs3 = bv_unsigned sp + -88) in E3. subst vs2 vs3.
rewrite adv_stay1 by (unfold remZ in Hcnt; lia).
replace (remZ false i j - cnt) with (remZ false i (j + cnt)) by (unfold remZ; lia).
unfold remZ in Hcnt, E6.
apply implM_loop_S. unfold wv_body at 1. cbn [fst snd]. apply implM_sys_k.
step. if_cases K0; zify_cond K0. { exfalso. lia. }
step. step.
replace (v_sltu (Z_to_bv 64 n1) (Z_to_bv 64 cnt)) with (Z_to_bv 64 0)
by (unfold v_sltu, c_ltu, bv_ltu; rewrite !unsigned_lit by lia; destruct (Z.ltb_spec0 n1 cnt); [lia|reflexivity]).
zstep. zstep. zstep. zstep. zstep. rewrite ?land_0_l'. zstep. zstep. zstep.
zstep. if_cases K1; zify_cond K1. 2:{ exfalso. lia. }
zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
zstep. zstep.
replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd) by (symmetry; apply sx32_lit; lia).
step_ecall. split.
{ use_wnode FR MU. }
intros rsp a Hdec. apply dec_writev_Some in Hdec. destruct Hdec as (-> & Hk & Ha). unfold remZ in Hk.

eapply implM_evt; [| intros ms' HP; exact HP]. unfold eff0. sys_nret. sysret_fast. step. step. apply evt_done.
destruct (Z.eq_dec a (remZ false i (j + cnt))) as [Heq|Hne].
* replace (a =? remZ false i (j + cnt)) with true by (symmetry; apply Z.eqb_eq; exact Heq). unfold remZ in Heq. apply implM_ret. cbv beta iota. apply evt_evt.
if_cases Hb; zify_cond Hb. 2:{ exfalso. lia. }
eapply succ_tail; [exact FR | exact FC | exact GOT | exact GUARD | exact MU | exact WM | exact MI | exact ST].
* replace (a =? _) with false by (symmetry; apply Z.eqb_neq; exact Hne). unfold remZ in Hne.
apply implM_ret. cbv beta iota.
if_cases Hb; zify_cond Hb. { exfalso. lia. }
apply evt_done. eapply IH; try eassumption; try reflexivity; unfold remZ; first [lia | exact I | split; lia].
Qed.

End Fixed.

Ltac wnode_side FR MU :=
lazymatch goal with
| |- areg _ _ = _ => at_node_red; reflexivity
| |- ms_svc_pending _ = _ => reflexivity
| |- ms_rom _ = _ => reflexivity
| |- True => exact I
| |- context [ms_mem _] => cbn [ms_mem MSsvc MS]; first [exact FR | exact MU]
| |- _ => first [eassumption | cbn [length]; lia | split; cbn [length]; lia]
end.

Lemma stdio_write_spec :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
(Fp : Z) (flags : word) (wend B bufsize wfn fd : Z) (mode : word) (lbf : Z) (tail : list byte)
(buf s : list Z) (S lo : Z) (canary : word),
rw_cells asegs m Fp (file_cells flags wend (B + zlength buf) B wfn B bufsize fd mode lbf tail) ->
bytes_at asegs m B (to_bytes buf) ->
bytes_at asegs m S (to_bytes s) ->
a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlength s) ->
(fd = 1 \/ fd = 2) ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - STDIO_WRITE_DEPTH) -> (band_lo <= lo) ->
ssp_cells m canary -> mem_inv asegs m ->
(0 <= Fp) -> (Fp + 232 <= lo) ->
(Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
(0 <= B) -> (0 <= bufsize) -> (zlength buf <= bufsize) -> (B + bufsize <= 2^47) ->
(zlength buf + zlength s <= 2^26) -> (0 <= S < 2^64) -> (S + zlength s <= 2^47) ->
(s = [] \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= Fp + 32 \/ Fp + 64 <= S))) ->
(B + zlength buf <= lo \/ bv_unsigned sp <= B) ->
bv_unsigned sp <= 2^47 ->
implM asegs (stdio_writev (St:=St) fd buf s) st
(stdio_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp flags B bufsize wfn fd mode lbf tail
(zlength s) lo canary m st)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd5094) fc None m (seg_rom asegs)).
Proof.
intros until canary. intros FC BUFB SRC -> -> -> FD ST LO GLO SSP MI Fp0 FPLO FSEP1 FSEP2 B0 BS0 BUFLE BShi LENS S0 Shi SEPS SEPB SPT.
assert (SPHI : 0 <= bv_unsigned sp <= 2^47) by (pose proof (bv_unsigned_in_range 64 sp) as X; unfold bv_modulus in X; cbn in X; lia).
destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard, STDIO_WRITE_DEPTH in *.
unfold zlength in *.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
unfold file_cells in FC.
change (bytes_at asegs m S (to_bytes s)) with (boxed (bytes_at asegs m S (to_bytes s))) in SRC.
change (bytes_at asegs m B (to_bytes buf)) with (boxed (bytes_at asegs m B (to_bytes buf))) in BUFB.

eapply implM_evt; [| intros ms' HP; exact HP].
carve_frame 112%nat ST.
do 12 step. do 13 step.
rewrite !unsigned_lit by lia. rewrite !unsigned_lit in FR by lia.
apply evt_done.
destruct buf as [|b0 buf'].
-
unfold stdio_writev. unfold zlength. change [s] with (iovsZ [] s false 0 0).
replace (Z.of_nat (@length Z []) + Z.of_nat (length s)) with (remZ [] s false 0 0) by (unfold remZ; cbn [length]; lia).
apply implM_loop_S. unfold wv_body at 1. cbn [fst snd]. apply implM_sys_k.
change (Z.of_nat (@length Z [])) with 0. rewrite !Z.add_0_r. rewrite Z.lxor_nilpotent.
change (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 0)) with (Z_to_bv 64 0).
step. if_true. do 6 step.
replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd) by (symmetry; apply sx32_lit; lia).
replace (B - B + Z.of_nat (length s)) with (Z.of_nat (length s)) by lia.
step_ecall. split.
{ eapply (wnode ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st Fp flags B bufsize wfn fd mode lbf tail _ _ S lo canary).
all: unfold boxed in *; wnode_side FR MU. }
intros rsp a Hdec. apply dec_writev_Some in Hdec. destruct Hdec as (-> & Hk & Ha). unfold remZ in Hk. cbn [length] in Hk.

eapply implM_evt; [| intros ms' HP; exact HP]. unfold eff0. sys_nret. sysret_fast. step. apply evt_done.
destruct (Z.eq_dec a (remZ [] s false 0 0)) as [Heq|Hne].
+ replace (a =? remZ [] s false 0 0) with true by (symmetry; apply Z.eqb_eq; exact Heq). unfold remZ in Heq. cbn [length] in Heq.
apply implM_ret. cbv beta iota. apply evt_evt.
if_cases Hb; zify_cond Hb. { exfalso. lia. }
eapply succ_tail; try eassumption; cbn [length]; rewrite ?Z.add_0_r; first [lia | exact FC].
+ replace (a =? _) with false by (symmetry; apply Z.eqb_neq; exact Hne). unfold remZ in Hne. cbn [length] in Hne.
apply implM_ret. cbv beta iota.
if_cases Hb; zify_cond Hb. 2:{ exfalso. lia. }
apply evt_done. unfold boxed in *.
eapply (retry_loop ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st Fp flags wend B bufsize wfn fd mode lbf tail _ _ S lo canary).
all: try exact FR.
all: first [eassumption | exact I | reflexivity | cbn [length]; unfold remZ; cbn [length]; lia].
-
unfold stdio_writev. unfold zlength. change [b0 :: buf'; s] with (iovsZ (b0 :: buf') s true 0 0).
replace (Z.of_nat (length (b0 :: buf')) + Z.of_nat (length s)) with (remZ (b0 :: buf') s true 0 0) by (unfold remZ; lia).
set (nb := Z.of_nat (length (b0 :: buf'))) in *.
assert (NB1 : 1 <= nb) by (subst nb; cbn [length]; lia).
apply implM_loop_S. unfold wv_body at 1. cbn [fst snd]. apply implM_sys_k.
replace (Z.lxor (B + nb) B) with (Z.lxor (B + nb) (B + 0)) by (rewrite Z.add_0_r; reflexivity).
assert (XNZ : Z.lxor (B + nb) (B + 0) <> 0).
{ intros E. apply Z.lxor_eq in E. lia. }
replace (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.lxor (B + nb) (B + 0)))) with (Z_to_bv 64 1).
2:{ pose proof (Z_lxor_range (B + nb) (B + 0) ltac:(lia) ltac:(lia)) as XR.
unfold v_sltu, c_ltu, bv_ltu. rewrite !unsigned_lit by lia.
destruct (Z.ltb_spec0 0 (Z.lxor (B + nb) (B + 0))); [reflexivity| exfalso; lia]. }
step. if_cases Hb0; zify_cond Hb0. 1:{ exfalso. lia. } do 7 step.
replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd) by (symmetry; apply sx32_lit; lia).
replace (B + nb - B + Z.of_nat (length s)) with (nb + Z.of_nat (length s)) by lia.
step_ecall. split.
{ eapply (wnode ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st Fp flags B bufsize wfn fd mode lbf tail _ _ S lo canary).
all: unfold boxed in *; subst nb; wnode_side FR MU. }
intros rsp a Hdec. apply dec_writev_Some in Hdec. destruct Hdec as (-> & Hk & Ha). unfold remZ in Hk.

eapply implM_evt; [| intros ms' HP; exact HP]. unfold eff0. sys_nret. sysret_fast. step. apply evt_done.
destruct (Z.eq_dec a (remZ (b0 :: buf') s true 0 0)) as [Heq|Hne].
+ replace (a =? remZ (b0 :: buf') s true 0 0) with true by (symmetry; apply Z.eqb_eq; exact Heq). unfold remZ in Heq.
apply implM_ret. cbv beta iota. apply evt_evt.
if_cases Hb; zify_cond Hb. { exfalso. lia. }
eapply succ_tail; try eassumption; subst nb; first [lia | exact FC].
+ replace (a =? _) with false by (symmetry; apply Z.eqb_neq; exact Hne). unfold remZ in Hne.
apply implM_ret. cbv beta iota.
if_cases Hb; zify_cond Hb. 2:{ exfalso. lia. }
apply evt_done. unfold boxed in *.
eapply (retry_loop ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st Fp flags wend B bufsize wfn fd mode lbf tail _ _ S lo canary).
all: try exact FR.
all: first [eassumption | exact I | reflexivity | subst nb; unfold remZ; lia | split; subst nb; lia].
Qed.
End StdioWrite.
