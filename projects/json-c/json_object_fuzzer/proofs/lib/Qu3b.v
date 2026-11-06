(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Q13u QwAs Qc6I QJFf QVsB QDM6 QCiC Qpj5 QdZp Qk8e QTVW QvG1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QwAs Qc6I QJFf QVsB QDM6 QVsB.Mq0.
Import QCiC.Mq1 Qpj5.Mq1 QdZp Qk8e.Mq0.
Import QTVW.Mq1.
Import QvG1.
Import ListNotations. Local Ltac QoSL.cell_of_bytes bs ::= QoSL.mkr__cell_of_bytes_10 bs. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.
Import Qc6I.Exc.

Notation RTP := 0x622e60%Z (only parsing).
Notation z64 := (Z_to_bv 64 0).

Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
[C4 flags; C4 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 0xd2884);
C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 z64; C8 (Z_to_bv 64 wbase); C8 z64;
C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0xd29c8); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
C8 z64; C8 z64; C4 (Z_to_bv 64 fd); C4 z64; C8 z64; C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 z64;
CB 80 tail].

Notation RSTDOUT := 0xea750%Z (only parsing).
Notation RSTDOUT_BUF := 0x6435e8%Z (only parsing).
Notation RSTDERR := 0xea660%Z (only parsing).
Notation F_STDOUT_WRITE := 0xd36bc%Z (only parsing).
Notation F_STDIO_WRITE := 0xd29d0%Z (only parsing).

Definition stdout_file (m : word -> option byte) (so : stdout_st) : Prop :=
exists (flags mode : word) (tail bufbytes : list byte),
rw_cells asegs m RSTDOUT
(file_cells flags
(if so_active so then RSTDOUT_BUF + 1024 else 0)%Z
(if so_active so then RSTDOUT_BUF + zlength (so_buf so) else 0)%Z
(if so_active so then RSTDOUT_BUF else 0)%Z
(if so_first so then F_STDOUT_WRITE else F_STDIO_WRITE)
RSTDOUT_BUF 1024 1 mode
(if so_lbf_nl so then 10 else 0xffffffff)%Z tail)
/\ Z.land (bv_unsigned flags) 72 = 0%Z
/\ rw_cells asegs m RSTDOUT_BUF [CB 1024 bufbytes]
/\ firstn (length (so_buf so)) bufbytes = to_bytes (so_buf so)
/\ (zlength (so_buf so) <= 1024)%Z
/\ (so_active so = false -> so_buf so = []).

Definition stderr_file (m : word -> option byte) : Prop :=
exists (flags mode : word) (e wend : Z) (tail : list byte),
rw_cells asegs m RSTDERR (file_cells flags wend e e F_STDIO_WRITE 0x6435e0 0 2 mode 0xffffffff tail).

Section StdioExitStatement.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

Definition stdio_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (guard : word) (m : word -> option byte) (s : St) : unit -> St -> machine_state -> Prop :=
fun _ s' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 so' m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 160, bv_unsigned sp); (RSTDOUT, 0xea838); (RSTDOUT_BUF, 0x6439e8)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ s' = set_so so' s
/\ stdout_file m' so' /\ so_buf so' = []
/\ stderr_file m'
/\ rw_cells asegs m' 0xe6b80 [C8 (Z_to_bv 64 0x642ea0)] /\ rw_cells asegs m' 0x642ea0 [C8 guard].

Definition stdio_exit_spec_stmt : Prop :=
forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (s : St) (guard : word)
(cdt thr sec : byte) (tm1 : word),
stk asegs m lo (bv_unsigned sp) ->
rw_cells asegs m 0x6430f0 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
rw_cells asegs m 0x6435d0 [C8 z64] ->
rw_cells asegs m 0xea928 [C8 z64] ->
rw_cells asegs m 0xea838 [C8 (Z_to_bv 64 RSTDOUT)] ->
rw_cells asegs m 0xea748 [C8 (Z_to_bv 64 RSTDERR)] ->
stdout_file m (get_so s) -> stderr_file m ->
rw_cells asegs m 0xe6b80 [C8 (Z_to_bv 64 0x642ea0)] -> rw_cells asegs m 0x642ea0 [C8 guard] ->
mem_inv asegs m ->
tp = Z_to_bv 64 RTP ->
(lo <= bv_unsigned sp - 160)%Z -> (0x645000 <= lo)%Z ->
(bv_unsigned sp <= 2^47)%Z ->
implM asegs (stdout_exit_flush get_so set_so) s
(stdio_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m s)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd2fb0) fc None m (seg_rom asegs)).
End StdioExitStatement.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QwAs.
Import QvDJ.Mq3.
Import QTVW.Mq6.
Import QvG1.
Import ListNotations. Local Ltac QoSL.cell_of_bytes bs ::= QoSL.mkr__cell_of_bytes_10 bs. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.

Definition memcpy_entry := 0xdb34c%Z.

Definition memcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 a2 : word) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
/\ bytes_at asegs m' (bv_unsigned a1) src.

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (src : list byte).
Notation S := (bv_unsigned a1).
Notation D := (bv_unsigned a0).
Notation n := (bv_unsigned a2).
Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
Hypothesis LEN : length src = Z.to_nat n.
Hypothesis AB : (0 <= S /\ S + n <= 2^64 /\ 0 <= D /\ D + n <= 2^64 /\ 0 <= n < 2^64)%Z.
Hypothesis SEP : (S + n <= D \/ D + n <= S)%Z.

Notation POST := (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m).

Notation ST pc mm x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 :=
(MS (mkR ra sp gp tp x5 x6 x7 s0 s1 a0 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

Definition INV (m1 : word -> option byte) (bs : list byte) (P : Z) : Prop :=
bytes_at asegs m1 S src /\ u8arr asegs m1 D bs /\ copied src bs (Z.to_nat P) /\
mem_inv asegs m1 /\ munch W m m1 /\ wmono asegs m m1.

Ltac open_inv H := destruct H as (SRC & DST & CP & MI & MU & WM).
Ltac inv_tac :=
lazymatch goal with
| |- INV _ _ _ => split; [eassumption | split; [eassumption | split; [ | repeat split; eassumption ]]];
lazymatch goal with CP : copied _ _ (Z.to_nat ?P) |- copied _ _ (Z.to_nat ?P') =>
first [ exact CP | replace (Z.to_nat P') with (Z.to_nat P) by lia; exact CP ] end
end.

Ltac fin :=
lazymatch goal with
| DST : u8arr _ ?m1 _ ?bs, CP : copied _ ?bs (Z.to_nat ?P) |- _ =>
let E := fresh "E" in
pose proof (copied_all _ _ _ CP ltac:(lia)) as E; rewrite E in DST; clear E CP;
apply rw_cells_of_u8arr in DST; rewrite LEN in DST
end;
finish2.

Tactic Notation "use" uconstr(L) :=
eapply L; first [ inv_tac | idtac ]; try (f_equal; lia); try lia;
try (rewrite ?unsigned_lit by lia; Z.div_mod_to_equations; lia);
try (rewrite ?Z.add_0_r, ?Z.sub_0_r; symmetry; apply Z_to_bv_bv_unsigned).

Lemma mc_a8c : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 4 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xdb70c m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. rewrite land_bit_2 by lia.
zstep. if_cases K2; zify_cond K2.
-
destruct (Z.ltb_spec0 (bv_unsigned r mod 4) 2) as [Hl4|Hl4]; [exfalso; cbn in K2; lia|]; apply (proj1 (Z.nlt_ge _ _)) in Hl4.
window P 2%nat HW.
ld1 HW 0%nat. ld1 HW 1%nat. zstep. zstep.
st1 HW 0%nat. st1 HW 1%nat.
zstep. zstep. rewrite land_1.
zstep. if_cases K1; zify_cond K1.
+ zstep. fin.
+ window (P + 2)%Z 1%nat HW1.
ld1 HW1 0%nat. st1 HW1 0%nat. zstep. fin.
- destruct (Z.ltb_spec0 (bv_unsigned r mod 4) 2) as [Hl4|Hl4]; [|exfalso; cbn in K2; lia].
zstep. rewrite land_1.
zstep. if_cases K1; zify_cond K1.
+ window P 1%nat HW. ld1 HW 0%nat. st1 HW 0%nat. zstep. fin.
+ zstep. fin.
Qed.

Lemma mc_a60 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + 4 + bv_unsigned r mod 4 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xdb6e0 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
window P 4%nat HW.
ld1 HW 0%nat. ld1 HW 1%nat. ld1 HW 2%nat. ld1 HW 3%nat. zstep. zstep.
st1 HW 0%nat. st1 HW 1%nat. st1 HW 2%nat. st1 HW 3%nat. zstep.
use (mc_a8c _ _ (P + 4)%Z).
Qed.

Lemma mc_a58 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 8 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xdb6d8 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. rewrite land_bit_4 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 8) 4) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_a8c m1 bs P).
- use (mc_a60 m1 bs P).
Qed.

Lemma mc_a0c : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + 8 + bv_unsigned r mod 8 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xdb68c m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
window P 8%nat HW.
ld1 HW 0%nat. ld1 HW 1%nat. ld1 HW 2%nat. ld1 HW 3%nat. ld1 HW 4%nat. ld1 HW 5%nat. ld1 HW 6%nat. ld1 HW 7%nat.
zstep.
st1 HW 0%nat. st1 HW 1%nat. st1 HW 2%nat. st1 HW 3%nat. zstep.
st1 HW 4%nat. st1 HW 5%nat. st1 HW 6%nat. st1 HW 7%nat. zstep.
use (mc_a58 _ _ (P + 8)%Z).
Qed.

Lemma mc_734 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 8 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xdb3b4 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. rewrite land_bit_4 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 8) 4) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_a60 m1 bs P).
- zstep. use (mc_a8c m1 bs P).
Qed.

Lemma mc_a04 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 16 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xdb684 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. rewrite land_bit_8 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 16) 8) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_734 m1 bs P).
- use (mc_a0c m1 bs P).
Qed.

Lemma mc_72c : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 16 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xdb3ac m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. rewrite land_bit_8 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 16) 8) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_a0c m1 bs P).
- use (mc_734 m1 bs P).
Qed.

Lemma mc_978 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + 16 + bv_unsigned r mod 16 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xdb5f8 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
window P 16%nat HW.
ld1 HW 0%nat. ld1 HW 1%nat. ld1 HW 2%nat. ld1 HW 3%nat. ld1 HW 4%nat. ld1 HW 5%nat. ld1 HW 6%nat. ld1 HW 7%nat.
st1 HW 0%nat. st1 HW 1%nat. st1 HW 2%nat. st1 HW 3%nat.
ld1 HW 8%nat. ld1 HW 9%nat. ld1 HW 10%nat. ld1 HW 11%nat.
st1 HW 4%nat. st1 HW 5%nat. st1 HW 6%nat. st1 HW 7%nat.
ld1 HW 12%nat. ld1 HW 13%nat. ld1 HW 14%nat. ld1 HW 15%nat.
zstep.
st1 HW 8%nat. st1 HW 9%nat. st1 HW 10%nat. st1 HW 11%nat.
zstep.
st1 HW 12%nat. st1 HW 13%nat. st1 HW 14%nat. st1 HW 15%nat.
zstep.
use (mc_a04 _ _ (P + 16)%Z).
Qed.

Lemma mc_848 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 8 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xdb4c8 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. rewrite land_bit_4 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 8) 4) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_a8c m1 bs P).
- window P 4%nat HW. ld4 HW 0%nat q0. zstep. st4 HW 0%nat. zstep. zstep.
use (mc_a8c _ _ (P + 4)%Z).
Qed.

Lemma mc_828 : forall m1 bs (P r : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + r = n)%Z -> (0 <= r < 16)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 r -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xdb4a8 m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr Rr -> -> ->; open_inv I.
zstep. zstep. if_cases K8; zify_cond K8.
- use (mc_848 m1 bs P (Z_to_bv 64 r)).
- window P 8%nat HW. ld4 HW 0%nat q0. ld4 HW 4%nat q1. st4 HW 0%nat. st4 HW 4%nat. zstep. zstep.
use (mc_848 _ _ (P + 8)%Z (Z_to_bv 64 r)).
Qed.

Lemma mc_7f8 : forall (K : nat) m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28,
Z.to_nat (n - P) = K -> INV m1 bs P -> (0 <= P)%Z -> (16 <= n - P)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xdb478 m1 x5 x6 x7 xa1 xa2 xa3 (Z_to_bv 64 15) x15 x16 x17 x28).
Proof using AB LEN SEP.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 HK I HP Hr -> -> ->; open_inv I.
window P 16%nat HW.
ld4 HW 0%nat q0. ld4 HW 4%nat q1. ld4 HW 8%nat q2. ld4 HW 12%nat q3.
zstep. zstep.
st4 HW 0%nat. st4 HW 4%nat. st4 HW 8%nat. st4 HW 12%nat.
zstep. zstep. if_cases Kl; zify_cond Kl.
- use (IH (Z.to_nat (n - (P + 16))) ltac:(lia) _ _ (P + 16)%Z).
- use (mc_828 _ _ (P + 16)%Z (n - (P + 16))%Z).
Qed.

Lemma mc_7ec : forall m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P <= n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xdb46c m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP -> -> ->; open_inv I.
zstep. zstep. if_cases K16; zify_cond K16.
- use (mc_828 m1 bs P (n - P)%Z).
- zstep. use (mc_7f8 (Z.to_nat (n - P)) m1 bs P).
Qed.

Notation LW w := (sext 64 (bv_extract 0 32 (le_bytes_to_word w))).

Lemma mc_770 : forall (K : nat) m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x16 x17 x28,
Z.to_nat (n - P) = K -> INV m1 bs P -> (2 <= P)%Z -> (18 <= n - P)%Z ->
w = firstn 4 (skipn (Z.to_nat (P - 2)) src) ->
xa1 = Z_to_bv 64 (S + P + 14) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xdb3f0 m1 x5 x6 x7 xa1 xa2 xa3 (LW w) (Z_to_bv 64 17) x16 x17 x28).
Proof using AB LEN SEP.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x16 x17 x28 HK I HP Hr Hw -> -> ->; open_inv I.
window (P - 2)%Z 20%nat HW.
pose proof (window_sub src _ (P - 2)%Z 20 0 4 (P - 2)%Z HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
zstep.
ld4 HW 4%nat q1. ld4 HW 8%nat q2. ld4 HW 12%nat q3. ld4 HW 16%nat q4.
do 11 zstep. zstep.
st HW 2%nat 4%nat ltac:(by_le 16%Z). st HW 6%nat 4%nat ltac:(by_le 16%Z).
st HW 10%nat 4%nat ltac:(by_le 16%Z). st HW 14%nat 4%nat ltac:(by_le 16%Z).
zstep. zstep. zstep. if_cases Kl; zify_cond Kl.
- use (IH (Z.to_nat (n - (P + 16))) ltac:(lia) _ _ (P + 16)%Z q4). by_win HW 16%nat.
- zstep. zstep. zstep. if_cases K16; zify_cond K16.
+ use (mc_72c _ _ (P + 16)%Z).
+ zstep. use (mc_978 _ _ (P + 16)%Z).
Qed.

Lemma mc_754 : forall m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (32 <= n - P)%Z ->
w = firstn 4 (skipn (Z.to_nat P) src) ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xdb3d4 m1 x5 x6 x7 xa1 xa2 xa3 (LW w) x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 I HP Hr Hw -> -> ->; open_inv I.
window P 4%nat HW.
pose proof (window_sub src _ P 4 0 4 P HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
zstep. zstep.
st HW 0%nat 1%nat ltac:(by_le 0%Z). st HW 1%nat 1%nat ltac:(by_le 0%Z).
zstep. zstep. zstep.
use (mc_770 (Z.to_nat (n - (P + 2))) _ _ (P + 2)%Z w). by_win HW 0%nat.
Qed.

Lemma mc_878 : forall (K : nat) m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x16 x17 x28,
Z.to_nat (n - P) = K -> INV m1 bs P -> (1 <= P)%Z -> (19 <= n - P)%Z ->
w = firstn 4 (skipn (Z.to_nat (P - 1)) src) ->
xa1 = Z_to_bv 64 (S + P + 15) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xdb4f8 m1 x5 x6 x7 xa1 xa2 xa3 (LW w) (Z_to_bv 64 18) x16 x17 x28).
Proof using AB LEN SEP.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x16 x17 x28 HK I HP Hr Hw -> -> ->; open_inv I.
window (P - 1)%Z 20%nat HW.
pose proof (window_sub src _ (P - 1)%Z 20 0 4 (P - 1)%Z HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
zstep.
ld4 HW 4%nat q1. ld4 HW 8%nat q2. ld4 HW 12%nat q3. ld4 HW 16%nat q4.
do 11 zstep. zstep.
st HW 1%nat 4%nat ltac:(by_le 24%Z). st HW 5%nat 4%nat ltac:(by_le 24%Z).
st HW 9%nat 4%nat ltac:(by_le 24%Z). st HW 13%nat 4%nat ltac:(by_le 24%Z).
zstep. zstep. zstep. if_cases Kl; zify_cond Kl.
- use (IH (Z.to_nat (n - (P + 16))) ltac:(lia) _ _ (P + 16)%Z q4). by_win HW 16%nat.
- zstep. zstep. zstep. if_cases K16; zify_cond K16.
+ use (mc_72c _ _ (P + 16)%Z).
+ zstep. use (mc_978 _ _ (P + 16)%Z).
Qed.

Lemma mc_864 : forall m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (32 <= n - P)%Z ->
w = firstn 4 (skipn (Z.to_nat P) src) ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xdb4e4 m1 x5 x6 x7 xa1 xa2 xa3 (LW w) x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 I HP Hr Hw -> -> ->; open_inv I.
window P 4%nat HW.
pose proof (window_sub src _ P 4 0 4 P HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
st HW 0%nat 1%nat ltac:(by_le 0%Z).
zstep. zstep. zstep. zstep.
use (mc_878 (Z.to_nat (n - (P + 1))) _ _ (P + 1)%Z w). by_win HW 0%nat.
Qed.

Lemma mc_90c : forall (K : nat) m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x16 x17 x28,
Z.to_nat (n - P) = K -> INV m1 bs P -> (3 <= P)%Z -> (17 <= n - P)%Z ->
w = firstn 4 (skipn (Z.to_nat (P - 3)) src) ->
xa1 = Z_to_bv 64 (S + P + 13) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xdb58c m1 x5 x6 x7 xa1 xa2 xa3 (LW w) (Z_to_bv 64 16) x16 x17 x28).
Proof using AB LEN SEP.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x16 x17 x28 HK I HP Hr Hw -> -> ->; open_inv I.
window (P - 3)%Z 20%nat HW.
pose proof (window_sub src _ (P - 3)%Z 20 0 4 (P - 3)%Z HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
zstep.
ld4 HW 4%nat q1. ld4 HW 8%nat q2. ld4 HW 12%nat q3. ld4 HW 16%nat q4.
do 11 zstep. zstep.
st HW 3%nat 4%nat ltac:(by_le 8%Z). st HW 7%nat 4%nat ltac:(by_le 8%Z).
st HW 11%nat 4%nat ltac:(by_le 8%Z). st HW 15%nat 4%nat ltac:(by_le 8%Z).
zstep. zstep. zstep. if_cases Kl; zify_cond Kl.
- use (IH (Z.to_nat (n - (P + 16))) ltac:(lia) _ _ (P + 16)%Z q4). by_win HW 16%nat.
- zstep. zstep. zstep. if_cases K16; zify_cond K16.
+ use (mc_72c _ _ (P + 16)%Z).
+ use (mc_978 _ _ (P + 16)%Z).
Qed.

Lemma mc_8e8 : forall m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (32 <= n - P)%Z ->
w = firstn 4 (skipn (Z.to_nat P) src) ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xdb568 m1 x5 x6 x7 xa1 xa2 xa3 (LW w) x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 I HP Hr Hw -> -> ->; open_inv I.
window P 4%nat HW.
pose proof (window_sub src _ P 4 0 4 P HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
zstep. zstep. zstep.
st HW 0%nat 1%nat ltac:(by_le 0%Z). st HW 1%nat 1%nat ltac:(by_le 0%Z). st HW 2%nat 1%nat ltac:(by_le 0%Z).
zstep. zstep. zstep.
use (mc_90c (Z.to_nat (n - (P + 3))) _ _ (P + 3)%Z w). by_win HW 0%nat.
Qed.

Lemma mc_740 : forall m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (32 <= n - P)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xdb3c0 m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> -> ->; open_inv I.
window P 4%nat HW. ld4 HW 0%nat q0.
zstep. zstep. if_cases K3; zify_cond K3.
- use (mc_864 m1 bs P q0). by_win HW 0%nat.
- zstep. zstep. if_cases K2; zify_cond K2.
+ use (mc_8e8 m1 bs P q0). by_win HW 0%nat.
+ use (mc_754 m1 bs P q0). by_win HW 0%nat.
Qed.

Lemma mc_71c : forall m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P <= n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xdb39c m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP -> -> ->; open_inv I.
zstep. zstep. if_cases K32; zify_cond K32.
- use (mc_740 m1 bs P).
- zstep. zstep. if_cases K16; zify_cond K16.
+ use (mc_978 m1 bs P).
+ use (mc_72c m1 bs P).
Qed.

Lemma mc_714 : forall m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P <= n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xdb394 m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP -> -> ->; open_inv I.
zstep. zstep. if_cases Kal; zify_cond Kal.
- use (mc_7ec m1 bs P).
- use (mc_71c m1 bs P).
Qed.

Lemma mc_6e4 : forall (K : nat) m1 bs (P : Z) xa1 xa2 xa3 xa4 x5 x6 x7 x16 x17 x28,
Z.to_nat (n - P) = K -> INV m1 bs P -> (0 <= P < n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
xa4 = Z_to_bv 64 (S + P + 1) ->
evt asegs POST (ST 0xdb364 m1 x5 x6 x7 xa1 xa2 xa3 xa4 (Z_to_bv 64 1) x16 x17 x28).
Proof using AB LEN SEP.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P xa1 xa2 xa3 xa4 x5 x6 x7 x16 x17 x28 HK I HP -> -> -> ->; open_inv I.
window P 1%nat HW.
ld1 HW 0%nat. zstep. zstep. zstep. rewrite land_3.
st1 HW 0%nat. zstep. zstep. zstep. if_cases Kal; zify_cond Kal.
- use (mc_714 _ _ (P + 1)%Z).
- zstep. zstep. if_cases K1; zify_cond K1.
+ use (IH (Z.to_nat (n - (P + 1))) ltac:(lia) _ _ (P + 1)%Z).
+ zstep. use (mc_714 _ _ (P + 1)%Z).
Qed.

Lemma memcpy_body : forall junk,
rw_cells asegs m D [CB (Z.to_nat n) junk] -> bytes_at asegs m S src -> mem_inv asegs m ->
evt asegs POST (ST 0xdb34c m t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3).
Proof using AB LEN SEP.
intros junk DST0 SRC MI.
pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (u8arr_of_rw_cells _ _ _ _ _ DST0) as DST.
pose proof (copied_0 src junk ltac:(rewrite (rw_cells_CB_length _ _ _ _ _ DST0); lia)) as CP.
change 0%nat with (Z.to_nat 0) in CP. clear DST0.
zstep. rewrite land_3. zstep. if_cases Ksal; zify_cond Ksal.
-
zstep. zstep. rewrite land_3. zstep. if_cases Kdal; zify_cond Kdal.
+ use (mc_71c m junk 0%Z).
+ use (mc_7ec m junk 0%Z).
- zstep. if_cases K0; zify_cond K0.
+ zstep. use (mc_714 m junk 0%Z).
+ zstep. zstep. zstep. use (mc_6e4 (Z.to_nat n) m junk 0%Z).
Qed.
End Proofs.

Lemma memcpy_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte),
bytes_at asegs m (bv_unsigned a1) src ->
length src = Z.to_nat (bv_unsigned a2) ->
rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
(bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1)%Z ->
mem_inv asegs m ->
evt asegs (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdb34c) fc None m (seg_rom asegs)).
Proof.
intros until junk. intros SRC LEN DST SEP MI.
eapply memcpy_body; try eassumption.
pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
pose proof (bytes_at_bound _ _ _ _ SRC) as B2.
pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R. cbn. lia.
Qed.
End Mq1.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q67d Q6sh QQwg QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qc27 Qc6I QJFf QDM6.
Import QCiC Qpj5.Mq1 QvDJ.Mq2 Q67d QCiC.Mq0 Q6sh QQwg QKTr.
Import QvG1 QTVW.Mq0.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.cell_of_bytes bs ::= QoSL.mkr__cell_of_bytes_10 bs. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Definition qframe (s s' : AState) : Prop :=
as_tq s' = as_tq s /\ as_gq s' = as_gq s /\ as_reg s' = as_reg s /\ as_nres s' = as_nres s /\ as_spent s' = as_spent s /\ as_next s' = as_next s.

Lemma qframe_refl s : qframe s s.
Proof. repeat split; reflexivity. Qed.
Lemma qframe_trans s1 s2 s3 : qframe s1 s2 -> qframe s2 s3 -> qframe s1 s3.
Proof. intros (A1&A2&A3&A4&A5&A6) (B1&B2&B3&B4&B5&B6). repeat split; congruence. Qed.
Lemma qframe_set_cls s c x : qframe s (set_cls c x s).
Proof. repeat split; reflexivity. Qed.
Lemma qframe_upd_cls s c f : qframe s (upd_cls c f s).
Proof. repeat split; reflexivity. Qed.
Lemma qframe_set_inited s : qframe s (set_inited s).
Proof. repeat split; reflexivity. Qed.

Fixpoint split_last_spec {A} (l : list A) :
match split_last l with None => l = [] | Some (f, x) => l = f ++ [x] end.
Proof.
induction l as [|y l IH]; cbn; [reflexivity|].
destruct (split_last l) as [[f x]|]; subst; reflexivity.
Qed.

Local Notation TT := (fun (_ : evA) (_ : ansA) => True).

Definition okrel {R} (P : R -> Prop) (r : res R) : Prop := match r with ROk x => P x | _ => True end.

Lemma tall_bind_ok {R S} (P1 : R -> Prop) (P : S -> Prop) (t : T R) (f : R -> T S) :
tall TT (okrel P1) t -> (forall r, P1 r -> tall TT (okrel P) (f r)) -> tall TT (okrel P) (tbind t f).
Proof.
intros Ht Hf. apply tall_bind. eapply tall_mono; [exact Ht|]. intros [r| |w] Hr; cbn in *; [apply Hf; exact Hr| exact I| exact I].
Qed.

Ltac tret_ok := apply tall_ret; cbn.

Section S.
Variable L : ALay.

Lemma ensure_fa_qframe s c nf : tall TT (okrel (fun r => qframe s (snd r))) (ensure_fa L s c nf).
Proof.
unfold ensure_fa. destruct (_ <=? _); [tret_ok; apply qframe_refl|]. destruct (_ <? _); [exact I|].
apply tall_vis. intros a _. destruct (fixed_ok a); tret_ok; [apply qframe_set_cls| apply qframe_refl].
Qed.

Lemma populate_qframe s c req : tall TT (okrel (fun r => qframe s (snd r))) (populate L s c req).
Proof.
unfold populate. eapply tall_bind_ok with (P1 := fun r => qframe s (snd r)).
{ destruct (_ <? _); [| tret_ok; apply qframe_refl]. destruct (_ <? _); [exact I|].
apply tall_vis. intros a _. destruct (fixed_ok a); tret_ok; [apply qframe_set_cls| apply qframe_refl]. }
intros [ok s1] H1. cbn in H1. destruct ok; cbn [negb]; [| tret_ok; exact H1].
eapply tall_bind_ok with (P1 := fun r => qframe s (snd r)).
{ eapply tall_mono; [apply ensure_fa_qframe|]. intros [[b s2]| |w]; cbn; [| exact (fun x => x)| exact (fun x => x)]. intros H2. eapply qframe_trans; eauto. }
intros [ok2 s2] H2. cbn in H2. destruct ok2; cbn [negb]; tret_ok; [| exact H2]. eapply qframe_trans; [exact H2| apply qframe_set_cls].
Qed.

Lemma get_from_allocator_qframe s c k : tall TT (okrel (fun r => qframe s (snd r))) (get_from_allocator L s c k).
Proof.
unfold get_from_allocator. eapply tall_bind_ok with (P1 := fun r => qframe s (snd r)).
{ destruct (_ <? _); [apply populate_qframe| tret_ok; apply qframe_refl]. }
intros [ok s1] H1. cbn in H1. destruct ok; cbn [negb]; [| tret_ok; exact H1].
destruct (_ <? _); [exact I| tret_ok; eapply qframe_trans; [exact H1| apply qframe_set_cls]].
Qed.

Lemma refill_qframe s c : tall TT (okrel (fun r => qframe s (snd r))) (refill L s c).
Proof.
unfold refill. eapply tall_bind_ok with (P1 := fun r => qframe s (snd r)).
{ eapply tall_mono; [apply get_from_allocator_qframe|]. intros [[b s1]| |w]; cbn; [| exact (fun x => x)| exact (fun x => x)]. intros H. eapply qframe_trans; [apply qframe_set_inited| exact H]. }
intros [ok s1] H1. cbn in H1. destruct ok; cbn [negb]; tret_ok; [| exact H1]. eapply qframe_trans; [exact H1| apply qframe_upd_cls].
Qed.

Lemma cache_alloc_qframe s c : tall TT (okrel (fun r => qframe s (snd r))) (cache_alloc L s c).
Proof.
unfold cache_alloc. eapply tall_bind_ok with (P1 := fun r => qframe s (snd r)).
{ destruct (_ =? _); [apply refill_qframe| tret_ok; apply qframe_refl]. }
intros [ok s1] H1. cbn in H1. destruct ok; cbn [negb]; tret_ok; [| exact H1]. eapply qframe_trans; [exact H1| apply qframe_upd_cls].
Qed.

Lemma enqueue_qptrs s p : 0 <= aptr_req p -> tall TT (okrel (fun s' =>
concat (map b_chunks (q_list (as_tq s'))) = concat (map b_chunks (q_list (as_tq s))) ++ [p]
/\ q_bytes (as_tq s') <= q_bytes (as_tq s) + aptr_used p + kBatchBytes
/\ as_gq s' = as_gq s /\ as_reg s' = as_reg s /\ as_nres s' = as_nres s /\ as_spent s' = as_spent s /\ as_next s' = as_next s)) (enqueue L s p).
Proof.
intros Hp. assert (KBB : kBatchBytes = 8192) by reflexivity.
assert (UP : 1 <= aptr_used p) by (unfold aptr_used, used_size; lia).
unfold enqueue. pose proof (split_last_spec (q_list (as_tq s))) as SL.
assert (NB : forall s1, as_tq s1 = as_tq s -> qframe s s1 ->
tall TT (okrel (fun s' => concat (map b_chunks (q_list (as_tq s'))) = concat (map b_chunks (q_list (as_tq s))) ++ [p]
/\ q_bytes (as_tq s') <= q_bytes (as_tq s) + aptr_used p + kBatchBytes
/\ as_gq s' = as_gq s /\ as_reg s' = as_reg s /\ as_nres s' = as_nres s /\ as_spent s' = as_spent s /\ as_next s' = as_next s))
(new_batch L s1 p (aptr_used p))).
{ intros s1 E1 Q1. unfold new_batch. eapply tall_bind_ok with (P1 := fun r => qframe s1 (snd r)); [apply cache_alloc_qframe|].
intros [ok s2] H2. cbn in H2. destruct ok; cbn [negb]; [| exact I]. tret_ok.
pose proof (qframe_trans _ _ _ Q1 H2) as (Etq & Egq & Ereg & Enres & Espent & Enext). rewrite <- Etq.
unfold q_push_back. cbn [q_list q_bytes b_chunks b_size]. rewrite map_app, concat_app. cbn [map concat b_chunks app]. rewrite ?app_nil_r.
repeat split; try assumption; try lia. }
destruct (split_last (q_list (as_tq s))) as [[front b]|].
- destruct (_ =? _); [apply NB; [reflexivity| apply qframe_refl]|]. tret_ok. cbn [q_list q_bytes]. rewrite SL.
rewrite !map_app, !concat_app. cbn [map concat b_chunks]. rewrite !app_nil_r, app_assoc. repeat split; try reflexivity. lia.
- apply NB; [reflexivity| apply qframe_refl].
Qed.
End S.

Section Bridge.
Variable atn : node -> machine_state -> Prop.

Lemma aimplT_tall {R} (t : T R) (P : R -> Prop) s Q ms :
tall TT (okrel P) t -> aimplT atn t s Q ms -> aimplT atn t s (fun r s' ms' => P r /\ Q r s' ms') ms.
Proof.
unfold aimplT. revert s ms. induction t as [[r| |w]|e k IH]; intros s ms Ht H; cbn [membedA] in *.
- unfold implMG, mret in *. cbn in *. eapply evt_mono; [exact H|]. intros ms' HQ; cbn; auto.
- eapply implMA_mspin_any. exact H.
- apply implMG_unr.
- eapply implMG_bind.
+ eapply ev_stepA_state. unfold implMG, mbind, ebind in H.
instantiate (1 := fun a s' ms' => impl asegs atn (membedA (k a) s') (epost (fun p => Q (fst p) (snd p))) ms').
unfold implMG. revert H. generalize (ev_stepA e s). intros t H.
revert ms H. induction t as [x|n kk IHt]; intros ms H; cbn [Qc6I.bind] in *.
* unfold epost in H |- *. destruct x as [|[a s']]; cbn in *; apply evt_done; [exact I| exact H].
* rewrite aimpl_vis_unfold in H. rewrite aimpl_vis_unfold. eapply evt_mono; [exact H|].
intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. apply IHt. apply Hk.
+ intros a s' ms' [-> H1]. cbn in H1. apply IH; [apply Ht; exact I| exact H1].
Qed.

Lemma impl_then {R} (t : itree node R) (Q Q' : R -> machine_state -> Prop) ms :
impl asegs atn t Q ms -> (forall r ms', Q r ms' -> evt asegs (Q' r) ms') -> impl asegs atn t Q' ms.
Proof.
revert ms. induction t as [r|n k IH]; intros ms H HQ; cbn in *.
- eapply evt_cut; [exact H|]. intros ms' H'. exact (HQ r ms' H').
- eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; [apply Hk| exact HQ].
Qed.

Lemma aimplT_then {R} (t : T R) s (Q Q' : R -> PStateA -> machine_state -> Prop) ms :
aimplT atn t s Q ms -> (forall r s' ms', Q r s' ms' -> evt asegs (Q' r s') ms') -> aimplT atn t s Q' ms.
Proof.
unfold aimplT, implMG. intros H HQ. eapply impl_then; [exact H|].
intros [|[a s']] ms' H'; cbn in *; [apply evt_done; exact I| apply HQ; exact H'].
Qed.
End Bridge.
End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Export QTVW.Mq5.
Import ListNotations. Local Ltac QoSL.cell_of_bytes bs ::= QoSL.mkr__cell_of_bytes_10 bs. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9.
Local Open Scope Z_scope.

Import ListNotations.

Local Open Scope Z_scope.

Lemma zb_land_pow2_bit0 : forall x k, 0 <= k -> Z.testbit x k = false -> Z.land x (2^k) = 0.
Proof.
intros x k Hk Hb. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by lia.
destruct (Z.eqb_spec k i) as [<-|]; [rewrite Hb; reflexivity| apply Bool.andb_false_r].
Qed.

Lemma zb_lxor_pow2 : forall x k, 0 <= k ->
Z.lxor x (2^k) = x + 2^k - 2 * 2^k * ((x / 2^k) mod 2).
Proof.
intros x k Hk.
destruct (Z.testbit x k) eqn:Hb.
- pose proof (proj1 (Z.testbit_true x k Hk) Hb) as Hm. rewrite Hm.
set (y := Z.lxor x (2^k)).
assert (Hy : Z.testbit y k = false).
{ subst y. rewrite Z.lxor_spec, Hb, Z.pow2_bits_true by lia. reflexivity. }
assert (E : Z.lxor y (2^k) = y + 2^k).
{ symmetry. apply Z.add_nocarry_lxor. apply zb_land_pow2_bit0; assumption. }
subst y. rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r in E. lia.
- pose proof (proj1 (Z.testbit_false x k Hk) Hb) as Hm. rewrite Hm.
rewrite <- Z.add_nocarry_lxor by (apply zb_land_pow2_bit0; assumption). lia.
Qed.

Lemma zb_lxor_b31 : forall x, Z.lxor x 2147483648 = x + 2147483648 - 4294967296 * ((x / 2147483648) mod 2).
Proof. intros x. change 2147483648 with (2^31). rewrite zb_lxor_pow2 by lia. lia. Qed.

Lemma bv_wrap32_eq : forall z, bv_wrap 32 z = z mod 4294967296.
Proof. reflexivity. Qed.

Lemma swrap32_eq : forall z, bv_swrap 32 z = (z + 2147483648) mod 4294967296 - 2147483648.
Proof. reflexivity. Qed.

Lemma swrap32_small_A : forall z, - 2147483648 <= z < 2147483648 -> bv_swrap 32 z = z.
Proof. intros z Hz. rewrite swrap32_eq. rewrite Z.mod_small by lia. lia. Qed.

Lemma sext32_eq : forall z, sext32 z = ((z + 2147483648) mod 4294967296 - 2147483648) mod 18446744073709551616.
Proof.
intros z. unfold sext32, sub64, M32. rewrite wrap64_mod. change (2^64) with 18446744073709551616. f_equal.
change 4294967295 with (2^32 - 1). rewrite zb_land_mask by lia. change 2147483648 with (2^31).
rewrite zb_lxor_pow2 by lia. change 4294967296 with (2^32).
Z.div_mod_to_equations. nia.
Qed.

Lemma land_swrap32_sext32 : forall z, Z.land (bv_swrap 32 z) 18446744073709551615 = sext32 z.
Proof. intros z. rewrite land_W64, sext32_eq, swrap32_eq. reflexivity. Qed.

Lemma Z_to_bv_swrap32 : forall z, Z_to_bv 64 (bv_swrap 32 z) = Z_to_bv 64 (sext32 z).
Proof. intros z. rewrite <- land_swrap32_sext32. symmetry. apply Z_to_bv_land64. Qed.

Lemma sext32_range : forall z, 0 <= sext32 z < 18446744073709551616.
Proof. intros z. rewrite sext32_eq. apply Z.mod_pos_bound. lia. Qed.

Lemma sext32_small : forall z, 0 <= z < 2147483648 -> sext32 z = z.
Proof. intros z Hz. rewrite sext32_eq. rewrite (Z.mod_small (z + _)) by lia. rewrite Z.mod_small by lia. lia. Qed.

Lemma sext32_mod32 : forall z, sext32 (z mod 4294967296) = sext32 z.
Proof.
intros z. rewrite !sext32_eq. f_equal. f_equal.
rewrite Z.add_mod_idemp_l by lia. reflexivity.
Qed.

Lemma sext32_low : forall z, (sext32 z) mod 4294967296 = z mod 4294967296.
Proof.
intros z. rewrite sext32_eq. change 18446744073709551616 with (4294967296 * 4294967296).
rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z.mod_add by lia.
Z.div_mod_to_equations. lia.
Qed.

Lemma zext32_eq : forall z, zext32 z = z mod 4294967296.
Proof. intros z. unfold zext32, M32. change 4294967295 with (2^32 - 1). rewrite zb_land_mask by lia. reflexivity. Qed.

Lemma zext32_small : forall z, 0 <= z < 4294967296 -> zext32 z = z.
Proof. intros z Hz. rewrite zext32_eq. apply Z.mod_small. lia. Qed.

Lemma srliw_pos : forall x k, 0 < k -> srliw x k = Z.shiftr (x mod 4294967296) k.
Proof.
intros x k Hk. unfold srliw. unfold M32. change 4294967295 with (2^32 - 1). rewrite zb_land_mask by lia.
change (2^32) with 4294967296.
apply sext32_small. pose proof (Z.mod_pos_bound x 4294967296 ltac:(lia)) as Hr.
rewrite Z.shiftr_div_pow2 by lia. split. { apply Z.div_pos; lia. }
apply Z.div_lt_upper_bound; [lia|]. apply Z.lt_le_trans with 4294967296; [lia|].
assert (2^1 <= 2^k) by (apply Z.pow_le_mono_r; lia). change (2^1) with 2 in *. lia.
Qed.

Lemma walk_srliw : forall x k, 0 < k -> 0 <= x ->
bv_swrap 32 (Z.shiftr (bv_wrap 32 x) k) = Z.shiftr (x mod 4294967296) k.
Proof.
intros x k Hk Hx. rewrite bv_wrap32_eq. apply swrap32_small_A.
pose proof (Z.mod_pos_bound x 4294967296 ltac:(lia)) as Hr.
rewrite Z.shiftr_div_pow2 by lia. split. { apply Z.le_trans with 0; [lia|]. apply Z.div_pos; lia. }
apply Z.div_lt_upper_bound; [lia|]. apply Z.lt_le_trans with 4294967296; [lia|].
assert (2^1 <= 2^k) by (apply Z.pow_le_mono_r; lia). change (2^1) with 2 in *. lia.
Qed.

Lemma land_mask_small : forall x k, 0 <= k -> 0 <= x < 2^k -> Z.land x (2^k - 1) = x.
Proof. intros x k Hk Hx. rewrite zb_land_mask by lia. apply Z.mod_small. lia. Qed.

Lemma land_W64_small : forall x, 0 <= x < 18446744073709551616 -> Z.land x 18446744073709551615 = x.
Proof. intros x Hx. change 18446744073709551615 with (2^64 - 1). apply land_mask_small; [lia|]. change (2^64) with 18446744073709551616. lia. Qed.

Lemma land_M32_small : forall x, 0 <= x < 4294967296 -> Z.land x 4294967295 = x.
Proof. intros x Hx. change 4294967295 with (2^32 - 1). apply land_mask_small; [lia|]. change (2^32) with 4294967296. lia. Qed.

Lemma gcc_sext_small : forall v, 0 <= v < 2147483648 ->
Z.land (Z.lxor v 2147483648 - 2147483648) 18446744073709551615 = v.
Proof.
intros v Hv. rewrite zb_lxor_b31, (Z.div_small v) by lia. change (0 mod 2) with 0.
rewrite land_W64. rewrite Z.mod_small; lia.
Qed.

Lemma shiftr_mod32_bound : forall x k, 0 < k -> 0 <= Z.shiftr (x mod 4294967296) k < 2147483648.
Proof.
intros x k Hk. pose proof (Z.mod_pos_bound x 4294967296 ltac:(lia)) as Hr.
rewrite Z.shiftr_div_pow2 by lia. split. { apply Z.div_pos; lia. }
apply Z.div_lt_upper_bound; [lia|]. apply Z.lt_le_trans with 4294967296; [lia|].
assert (2^1 <= 2^k) by (apply Z.pow_le_mono_r; lia). change (2^1) with 2 in *. lia.
Qed.

Lemma lxor31_sub_small : forall v, 0 <= v < 2147483648 -> Z.lxor v 2147483648 - 2147483648 = v.
Proof. intros v Hv. rewrite zb_lxor_b31, (Z.div_small v) by lia. change (0 mod 2) with 0. lia. Qed.

Ltac fix32 :=
repeat first
[ rewrite walk_srliw by (first [lia | zrange_nonneg])
| match goal with
| |- context [Z.lxor (Z.shiftr (?x mod 4294967296) ?k) 2147483648 - 2147483648] =>
rewrite (lxor31_sub_small (Z.shiftr (x mod 4294967296) k)) by (apply shiftr_mod32_bound; lia)
| |- context [Z.land (Z.lxor (Z.shiftr (?x mod 4294967296) ?k) 2147483648 - 2147483648) 18446744073709551615] =>
rewrite (gcc_sext_small (Z.shiftr (x mod 4294967296) k)) by (apply shiftr_mod32_bound; lia)
end ].

Ltac wstep := zstep; fix32.

Ltac name_as_by_tac X e tac :=
set (X := e) in *;
let RX := fresh "R" X in
assert (RX : 0 <= X < 18446744073709551616) by (subst X; tac).

Tactic Notation "name_as_by" ident(X) constr(e) tactic3(tac) := name_as_by_tac X e tac.

Ltac model_reg_w_tac n X mexpr :=
let w := getreg n in
lazymatch w with
| Z_to_bv 64 ?e =>
replace (Z_to_bv 64 e) with (Z_to_bv 64 mexpr)
by (rewrite ?srliw_pos by lia; first [ f_equal; zeq | rewrite Z_to_bv_land64; f_equal; zeq ]);
set (X := mexpr) in *;
let RX := fresh "R" X in
assert (RX : 0 <= X < 18446744073709551616) by (subst X; rewrite ?srliw_pos by lia; zrange)
| _ => fail "model_reg_w: register" n "holds" w
end.

Tactic Notation "model_reg_w" constr(n) ident(X) constr(mexpr) := model_reg_w_tac n X mexpr.

Lemma zb_land_pow2 : forall x k, 0 <= k -> Z.land x (2^k) = 2^k * ((x / 2^k) mod 2).
Proof.
intros x k Hk. destruct (Z.testbit x k) eqn:Hb.
- pose proof (proj1 (Z.testbit_true x k Hk) Hb) as Hm. rewrite Hm, Z.mul_1_r.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.pow2_bits_eqb by lia.
destruct (Z.eqb_spec k i) as [<-|]; [rewrite Hb; reflexivity | apply Bool.andb_false_r].
- pose proof (proj1 (Z.testbit_false x k Hk) Hb) as Hm. rewrite Hm, Z.mul_0_r.
apply zb_land_pow2_bit0; assumption.
Qed.

Ltac reg_rewrite n lem :=
let w := getreg n in
lazymatch w with
| Z_to_bv 64 ?e =>
let e' := fresh "e" in let E := fresh "E" in
remember e as e' eqn:E in |- *;
rewrite lem in E; subst e'
end.

Lemma ltb1_eqb0 : forall x, 0 <= x -> (x <? 1) = (x =? 0).
Proof. intros x Hx. destruct (Z.ltb_spec0 x 1); destruct (Z.eqb_spec x 0); try reflexivity; exfalso; lia. Qed.

Lemma sext32_congr : forall x y, x mod 4294967296 = y mod 4294967296 -> sext32 x = sext32 y.
Proof. intros x y H. rewrite <- (sext32_mod32 x), <- (sext32_mod32 y), H. reflexivity. Qed.

Definition to_d_pack (dE dS a_hi : Z) : Z := Z.lor (Z.lor (shl64 dE 52) (shl64 (shr64 a_hi 63) 63)) dS.

Definition to_d_normD (sig1 exp0 : Z) : Z * Z :=
let carry := shr64 sig1 52 in (add64 carry exp0, Z.land (sub64 carry 1) sig1).

Definition to_d_subD (sig1 : Z) : Z * Z :=
let carry := nez64 (shr64 sig1 52) in (carry, Z.lxor sig1 (shl64 carry 52)).

Lemma lo64_words : forall lo hi, (0 <= lo < 2^64)%Z -> lo64 (lo + 2^64 * hi) = lo.
Proof.
intros lo hi H. unfold lo64. rewrite wrap64_mod.
rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma hi64_words : forall lo hi, (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z -> hi64 (lo + 2^64 * hi) = hi.
Proof.
intros lo hi Hl Hh. unfold hi64. rewrite wrap64_mod, Z.shiftr_div_pow2 by lia.
rewrite Z.mul_comm, Z.div_add, Z.div_small by lia. apply Z.mod_small. lia.
Qed.

Definition to_d_pack_g (dE dS sgn : Z) : Z := Z.lor (shl64 dE 52) (Z.lor dS sgn).

End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QwAs Qc6I QJFf QVsB QDM6 QVsB.Mq0.
Import QCiC.Mq1 Qpj5.Mq1 QdZp Qk8e.Mq0.
Import QTVW.Mq8.
Import QZzg.
Import ListNotations. Local Ltac QoSL.cell_of_bytes bs ::= QoSL.mkr__cell_of_bytes_10 bs. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.
Import Qc6I.Exc.

Notation RTP := 0x625520%Z (only parsing).
Notation z64 := (Z_to_bv 64 0).

Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
[C4 flags; C4 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 0xd4f48);
C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 z64; C8 (Z_to_bv 64 wbase); C8 z64;
C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0xd508c); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
C8 z64; C8 z64; C4 (Z_to_bv 64 fd); C4 z64; C8 z64; C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 z64;
CB 80 tail].

Notation RSTDOUT := 0xece30%Z (only parsing).
Notation RSTDOUT_BUF := 0x645ca8%Z (only parsing).
Notation RSTDERR := 0xecd40%Z (only parsing).
Notation F_STDOUT_WRITE := 0xd5d80%Z (only parsing).
Notation F_STDIO_WRITE := 0xd5094%Z (only parsing).

Definition stdout_file (m : word -> option byte) (so : stdout_st) : Prop :=
exists (flags mode : word) (tail bufbytes : list byte),
rw_cells asegs m RSTDOUT
(file_cells flags
(if so_active so then RSTDOUT_BUF + 1024 else 0)%Z
(if so_active so then RSTDOUT_BUF + zlength (so_buf so) else 0)%Z
(if so_active so then RSTDOUT_BUF else 0)%Z
(if so_first so then F_STDOUT_WRITE else F_STDIO_WRITE)
RSTDOUT_BUF 1024 1 mode
(if so_lbf_nl so then 10 else 0xffffffff)%Z tail)
/\ Z.land (bv_unsigned flags) 72 = 0%Z
/\ rw_cells asegs m RSTDOUT_BUF [CB 1024 bufbytes]
/\ firstn (length (so_buf so)) bufbytes = to_bytes (so_buf so)
/\ (zlength (so_buf so) <= 1024)%Z
/\ (so_active so = false -> so_buf so = []).

Definition stderr_file (m : word -> option byte) : Prop :=
exists (flags mode : word) (e wend : Z) (tail : list byte),
rw_cells asegs m RSTDERR (file_cells flags wend e e F_STDIO_WRITE 0x645ca0 0 2 mode 0xffffffff tail).

Section StdioExitStatement.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

Definition stdio_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (guard : word) (m : word -> option byte) (s : St) : unit -> St -> machine_state -> Prop :=
fun _ s' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 so' m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 160, bv_unsigned sp); (RSTDOUT, 0xecf18); (RSTDOUT_BUF, 0x6460a8)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ s' = set_so so' s
/\ stdout_file m' so' /\ so_buf so' = []
/\ stderr_file m'
/\ rw_cells asegs m' 0xe8f90 [C8 (Z_to_bv 64 0x645560)] /\ rw_cells asegs m' 0x645560 [C8 guard].

Definition stdio_exit_spec_stmt : Prop :=
forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (s : St) (guard : word)
(cdt thr sec : byte) (tm1 : word),
stk asegs m lo (bv_unsigned sp) ->
rw_cells asegs m 0x6457b0 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
rw_cells asegs m 0x645c90 [C8 z64] ->
rw_cells asegs m 0xed008 [C8 z64] ->
rw_cells asegs m 0xecf18 [C8 (Z_to_bv 64 RSTDOUT)] ->
rw_cells asegs m 0xece28 [C8 (Z_to_bv 64 RSTDERR)] ->
stdout_file m (get_so s) -> stderr_file m ->
rw_cells asegs m 0xe8f90 [C8 (Z_to_bv 64 0x645560)] -> rw_cells asegs m 0x645560 [C8 guard] ->
mem_inv asegs m ->
tp = Z_to_bv 64 RTP ->
(lo <= bv_unsigned sp - 160)%Z -> (0x647000 <= lo)%Z ->
(bv_unsigned sp <= 2^47)%Z ->
implM asegs (stdout_exit_flush get_so set_so) s
(stdio_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m s)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd5674) fc None m (seg_rom asegs)).
End StdioExitStatement.
End Mq4.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QwAs.
Import QvDJ.Mq3.
Import QTVW.Mqd.
Import QZzg.
Import ListNotations. Local Ltac QoSL.cell_of_bytes bs ::= QoSL.mkr__cell_of_bytes_10 bs. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.

Definition memcpy_entry := 0xdda10%Z.

Definition memcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 a2 : word) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
/\ bytes_at asegs m' (bv_unsigned a1) src.

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (src : list byte).
Notation S := (bv_unsigned a1).
Notation D := (bv_unsigned a0).
Notation n := (bv_unsigned a2).
Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
Hypothesis LEN : length src = Z.to_nat n.
Hypothesis AB : (0 <= S /\ S + n <= 2^64 /\ 0 <= D /\ D + n <= 2^64 /\ 0 <= n < 2^64)%Z.
Hypothesis SEP : (S + n <= D \/ D + n <= S)%Z.

Notation POST := (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m).

Notation ST pc mm x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 :=
(MS (mkR ra sp gp tp x5 x6 x7 s0 s1 a0 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

Definition INV (m1 : word -> option byte) (bs : list byte) (P : Z) : Prop :=
bytes_at asegs m1 S src /\ u8arr asegs m1 D bs /\ copied src bs (Z.to_nat P) /\
mem_inv asegs m1 /\ munch W m m1 /\ wmono asegs m m1.

Ltac open_inv H := destruct H as (SRC & DST & CP & MI & MU & WM).
Ltac inv_tac :=
lazymatch goal with
| |- INV _ _ _ => split; [eassumption | split; [eassumption | split; [ | repeat split; eassumption ]]];
lazymatch goal with CP : copied _ _ (Z.to_nat ?P) |- copied _ _ (Z.to_nat ?P') =>
first [ exact CP | replace (Z.to_nat P') with (Z.to_nat P) by lia; exact CP ] end
end.

Ltac fin :=
lazymatch goal with
| DST : u8arr _ ?m1 _ ?bs, CP : copied _ ?bs (Z.to_nat ?P) |- _ =>
let E := fresh "E" in
pose proof (copied_all _ _ _ CP ltac:(lia)) as E; rewrite E in DST; clear E CP;
apply rw_cells_of_u8arr in DST; rewrite LEN in DST
end;
finish2.

Tactic Notation "use" uconstr(L) :=
eapply L; first [ inv_tac | idtac ]; try (f_equal; lia); try lia;
try (rewrite ?unsigned_lit by lia; Z.div_mod_to_equations; lia);
try (rewrite ?Z.add_0_r, ?Z.sub_0_r; symmetry; apply Z_to_bv_bv_unsigned).

Lemma mc_a8c : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 4 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xdddd0 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. rewrite land_bit_2 by lia.
zstep. if_cases K2; zify_cond K2.
-
destruct (Z.ltb_spec0 (bv_unsigned r mod 4) 2) as [Hl4|Hl4]; [exfalso; cbn in K2; lia|]; apply (proj1 (Z.nlt_ge _ _)) in Hl4.
window P 2%nat HW.
ld1 HW 0%nat. ld1 HW 1%nat. zstep. zstep.
st1 HW 0%nat. st1 HW 1%nat.
zstep. zstep. rewrite land_1.
zstep. if_cases K1; zify_cond K1.
+ zstep. fin.
+ window (P + 2)%Z 1%nat HW1.
ld1 HW1 0%nat. st1 HW1 0%nat. zstep. fin.
- destruct (Z.ltb_spec0 (bv_unsigned r mod 4) 2) as [Hl4|Hl4]; [|exfalso; cbn in K2; lia].
zstep. rewrite land_1.
zstep. if_cases K1; zify_cond K1.
+ window P 1%nat HW. ld1 HW 0%nat. st1 HW 0%nat. zstep. fin.
+ zstep. fin.
Qed.

Lemma mc_a60 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + 4 + bv_unsigned r mod 4 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xddda4 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
window P 4%nat HW.
ld1 HW 0%nat. ld1 HW 1%nat. ld1 HW 2%nat. ld1 HW 3%nat. zstep. zstep.
st1 HW 0%nat. st1 HW 1%nat. st1 HW 2%nat. st1 HW 3%nat. zstep.
use (mc_a8c _ _ (P + 4)%Z).
Qed.

Lemma mc_a58 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 8 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xddd9c m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. rewrite land_bit_4 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 8) 4) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_a8c m1 bs P).
- use (mc_a60 m1 bs P).
Qed.

Lemma mc_a0c : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + 8 + bv_unsigned r mod 8 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xddd50 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
window P 8%nat HW.
ld1 HW 0%nat. ld1 HW 1%nat. ld1 HW 2%nat. ld1 HW 3%nat. ld1 HW 4%nat. ld1 HW 5%nat. ld1 HW 6%nat. ld1 HW 7%nat.
zstep.
st1 HW 0%nat. st1 HW 1%nat. st1 HW 2%nat. st1 HW 3%nat. zstep.
st1 HW 4%nat. st1 HW 5%nat. st1 HW 6%nat. st1 HW 7%nat. zstep.
use (mc_a58 _ _ (P + 8)%Z).
Qed.

Lemma mc_734 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 8 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xdda78 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. rewrite land_bit_4 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 8) 4) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_a60 m1 bs P).
- zstep. use (mc_a8c m1 bs P).
Qed.

Lemma mc_a04 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 16 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xddd48 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. rewrite land_bit_8 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 16) 8) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_734 m1 bs P).
- use (mc_a0c m1 bs P).
Qed.

Lemma mc_72c : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 16 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xdda70 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. rewrite land_bit_8 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 16) 8) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_a0c m1 bs P).
- use (mc_734 m1 bs P).
Qed.

Lemma mc_978 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + 16 + bv_unsigned r mod 16 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xddcbc m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
window P 16%nat HW.
ld1 HW 0%nat. ld1 HW 1%nat. ld1 HW 2%nat. ld1 HW 3%nat. ld1 HW 4%nat. ld1 HW 5%nat. ld1 HW 6%nat. ld1 HW 7%nat.
st1 HW 0%nat. st1 HW 1%nat. st1 HW 2%nat. st1 HW 3%nat.
ld1 HW 8%nat. ld1 HW 9%nat. ld1 HW 10%nat. ld1 HW 11%nat.
st1 HW 4%nat. st1 HW 5%nat. st1 HW 6%nat. st1 HW 7%nat.
ld1 HW 12%nat. ld1 HW 13%nat. ld1 HW 14%nat. ld1 HW 15%nat.
zstep.
st1 HW 8%nat. st1 HW 9%nat. st1 HW 10%nat. st1 HW 11%nat.
zstep.
st1 HW 12%nat. st1 HW 13%nat. st1 HW 14%nat. st1 HW 15%nat.
zstep.
use (mc_a04 _ _ (P + 16)%Z).
Qed.

Lemma mc_848 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 8 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xddb8c m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. rewrite land_bit_4 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 8) 4) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_a8c m1 bs P).
- window P 4%nat HW. ld4 HW 0%nat q0. zstep. st4 HW 0%nat. zstep. zstep.
use (mc_a8c _ _ (P + 4)%Z).
Qed.

Lemma mc_828 : forall m1 bs (P r : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + r = n)%Z -> (0 <= r < 16)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 r -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xddb6c m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P r xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr Rr -> -> ->; open_inv I.
zstep. zstep. if_cases K8; zify_cond K8.
- use (mc_848 m1 bs P (Z_to_bv 64 r)).
- window P 8%nat HW. ld4 HW 0%nat q0. ld4 HW 4%nat q1. st4 HW 0%nat. st4 HW 4%nat. zstep. zstep.
use (mc_848 _ _ (P + 8)%Z (Z_to_bv 64 r)).
Qed.

Lemma mc_7f8 : forall (K : nat) m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28,
Z.to_nat (n - P) = K -> INV m1 bs P -> (0 <= P)%Z -> (16 <= n - P)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xddb3c m1 x5 x6 x7 xa1 xa2 xa3 (Z_to_bv 64 15) x15 x16 x17 x28).
Proof using AB LEN SEP.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 HK I HP Hr -> -> ->; open_inv I.
window P 16%nat HW.
ld4 HW 0%nat q0. ld4 HW 4%nat q1. ld4 HW 8%nat q2. ld4 HW 12%nat q3.
zstep. zstep.
st4 HW 0%nat. st4 HW 4%nat. st4 HW 8%nat. st4 HW 12%nat.
zstep. zstep. if_cases Kl; zify_cond Kl.
- use (IH (Z.to_nat (n - (P + 16))) ltac:(lia) _ _ (P + 16)%Z).
- use (mc_828 _ _ (P + 16)%Z (n - (P + 16))%Z).
Qed.

Lemma mc_7ec : forall m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P <= n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xddb30 m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP -> -> ->; open_inv I.
zstep. zstep. if_cases K16; zify_cond K16.
- use (mc_828 m1 bs P (n - P)%Z).
- zstep. use (mc_7f8 (Z.to_nat (n - P)) m1 bs P).
Qed.

Notation LW w := (sext 64 (bv_extract 0 32 (le_bytes_to_word w))).

Lemma mc_770 : forall (K : nat) m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x16 x17 x28,
Z.to_nat (n - P) = K -> INV m1 bs P -> (2 <= P)%Z -> (18 <= n - P)%Z ->
w = firstn 4 (skipn (Z.to_nat (P - 2)) src) ->
xa1 = Z_to_bv 64 (S + P + 14) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xddab4 m1 x5 x6 x7 xa1 xa2 xa3 (LW w) (Z_to_bv 64 17) x16 x17 x28).
Proof using AB LEN SEP.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x16 x17 x28 HK I HP Hr Hw -> -> ->; open_inv I.
window (P - 2)%Z 20%nat HW.
pose proof (window_sub src _ (P - 2)%Z 20 0 4 (P - 2)%Z HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
zstep.
ld4 HW 4%nat q1. ld4 HW 8%nat q2. ld4 HW 12%nat q3. ld4 HW 16%nat q4.
do 11 zstep. zstep.
st HW 2%nat 4%nat ltac:(by_le 16%Z). st HW 6%nat 4%nat ltac:(by_le 16%Z).
st HW 10%nat 4%nat ltac:(by_le 16%Z). st HW 14%nat 4%nat ltac:(by_le 16%Z).
zstep. zstep. zstep. if_cases Kl; zify_cond Kl.
- use (IH (Z.to_nat (n - (P + 16))) ltac:(lia) _ _ (P + 16)%Z q4). by_win HW 16%nat.
- zstep. zstep. zstep. if_cases K16; zify_cond K16.
+ use (mc_72c _ _ (P + 16)%Z).
+ zstep. use (mc_978 _ _ (P + 16)%Z).
Qed.

Lemma mc_754 : forall m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (32 <= n - P)%Z ->
w = firstn 4 (skipn (Z.to_nat P) src) ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xdda98 m1 x5 x6 x7 xa1 xa2 xa3 (LW w) x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 I HP Hr Hw -> -> ->; open_inv I.
window P 4%nat HW.
pose proof (window_sub src _ P 4 0 4 P HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
zstep. zstep.
st HW 0%nat 1%nat ltac:(by_le 0%Z). st HW 1%nat 1%nat ltac:(by_le 0%Z).
zstep. zstep. zstep.
use (mc_770 (Z.to_nat (n - (P + 2))) _ _ (P + 2)%Z w). by_win HW 0%nat.
Qed.

Lemma mc_878 : forall (K : nat) m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x16 x17 x28,
Z.to_nat (n - P) = K -> INV m1 bs P -> (1 <= P)%Z -> (19 <= n - P)%Z ->
w = firstn 4 (skipn (Z.to_nat (P - 1)) src) ->
xa1 = Z_to_bv 64 (S + P + 15) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xddbbc m1 x5 x6 x7 xa1 xa2 xa3 (LW w) (Z_to_bv 64 18) x16 x17 x28).
Proof using AB LEN SEP.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x16 x17 x28 HK I HP Hr Hw -> -> ->; open_inv I.
window (P - 1)%Z 20%nat HW.
pose proof (window_sub src _ (P - 1)%Z 20 0 4 (P - 1)%Z HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
zstep.
ld4 HW 4%nat q1. ld4 HW 8%nat q2. ld4 HW 12%nat q3. ld4 HW 16%nat q4.
do 11 zstep. zstep.
st HW 1%nat 4%nat ltac:(by_le 24%Z). st HW 5%nat 4%nat ltac:(by_le 24%Z).
st HW 9%nat 4%nat ltac:(by_le 24%Z). st HW 13%nat 4%nat ltac:(by_le 24%Z).
zstep. zstep. zstep. if_cases Kl; zify_cond Kl.
- use (IH (Z.to_nat (n - (P + 16))) ltac:(lia) _ _ (P + 16)%Z q4). by_win HW 16%nat.
- zstep. zstep. zstep. if_cases K16; zify_cond K16.
+ use (mc_72c _ _ (P + 16)%Z).
+ zstep. use (mc_978 _ _ (P + 16)%Z).
Qed.

Lemma mc_864 : forall m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (32 <= n - P)%Z ->
w = firstn 4 (skipn (Z.to_nat P) src) ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xddba8 m1 x5 x6 x7 xa1 xa2 xa3 (LW w) x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 I HP Hr Hw -> -> ->; open_inv I.
window P 4%nat HW.
pose proof (window_sub src _ P 4 0 4 P HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
st HW 0%nat 1%nat ltac:(by_le 0%Z).
zstep. zstep. zstep. zstep.
use (mc_878 (Z.to_nat (n - (P + 1))) _ _ (P + 1)%Z w). by_win HW 0%nat.
Qed.

Lemma mc_90c : forall (K : nat) m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x16 x17 x28,
Z.to_nat (n - P) = K -> INV m1 bs P -> (3 <= P)%Z -> (17 <= n - P)%Z ->
w = firstn 4 (skipn (Z.to_nat (P - 3)) src) ->
xa1 = Z_to_bv 64 (S + P + 13) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xddc50 m1 x5 x6 x7 xa1 xa2 xa3 (LW w) (Z_to_bv 64 16) x16 x17 x28).
Proof using AB LEN SEP.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x16 x17 x28 HK I HP Hr Hw -> -> ->; open_inv I.
window (P - 3)%Z 20%nat HW.
pose proof (window_sub src _ (P - 3)%Z 20 0 4 (P - 3)%Z HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
zstep.
ld4 HW 4%nat q1. ld4 HW 8%nat q2. ld4 HW 12%nat q3. ld4 HW 16%nat q4.
do 11 zstep. zstep.
st HW 3%nat 4%nat ltac:(by_le 8%Z). st HW 7%nat 4%nat ltac:(by_le 8%Z).
st HW 11%nat 4%nat ltac:(by_le 8%Z). st HW 15%nat 4%nat ltac:(by_le 8%Z).
zstep. zstep. zstep. if_cases Kl; zify_cond Kl.
- use (IH (Z.to_nat (n - (P + 16))) ltac:(lia) _ _ (P + 16)%Z q4). by_win HW 16%nat.
- zstep. zstep. zstep. if_cases K16; zify_cond K16.
+ use (mc_72c _ _ (P + 16)%Z).
+ use (mc_978 _ _ (P + 16)%Z).
Qed.

Lemma mc_8e8 : forall m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (32 <= n - P)%Z ->
w = firstn 4 (skipn (Z.to_nat P) src) ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xddc2c m1 x5 x6 x7 xa1 xa2 xa3 (LW w) x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 I HP Hr Hw -> -> ->; open_inv I.
window P 4%nat HW.
pose proof (window_sub src _ P 4 0 4 P HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
zstep. zstep. zstep.
st HW 0%nat 1%nat ltac:(by_le 0%Z). st HW 1%nat 1%nat ltac:(by_le 0%Z). st HW 2%nat 1%nat ltac:(by_le 0%Z).
zstep. zstep. zstep.
use (mc_90c (Z.to_nat (n - (P + 3))) _ _ (P + 3)%Z w). by_win HW 0%nat.
Qed.

Lemma mc_740 : forall m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (32 <= n - P)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xdda84 m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> -> ->; open_inv I.
window P 4%nat HW. ld4 HW 0%nat q0.
zstep. zstep. if_cases K3; zify_cond K3.
- use (mc_864 m1 bs P q0). by_win HW 0%nat.
- zstep. zstep. if_cases K2; zify_cond K2.
+ use (mc_8e8 m1 bs P q0). by_win HW 0%nat.
+ use (mc_754 m1 bs P q0). by_win HW 0%nat.
Qed.

Lemma mc_71c : forall m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P <= n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xdda60 m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP -> -> ->; open_inv I.
zstep. zstep. if_cases K32; zify_cond K32.
- use (mc_740 m1 bs P).
- zstep. zstep. if_cases K16; zify_cond K16.
+ use (mc_978 m1 bs P).
+ use (mc_72c m1 bs P).
Qed.

Lemma mc_714 : forall m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P <= n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt asegs POST (ST 0xdda58 m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
Proof using AB LEN SEP.
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP -> -> ->; open_inv I.
zstep. zstep. if_cases Kal; zify_cond Kal.
- use (mc_7ec m1 bs P).
- use (mc_71c m1 bs P).
Qed.

Lemma mc_6e4 : forall (K : nat) m1 bs (P : Z) xa1 xa2 xa3 xa4 x5 x6 x7 x16 x17 x28,
Z.to_nat (n - P) = K -> INV m1 bs P -> (0 <= P < n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
xa4 = Z_to_bv 64 (S + P + 1) ->
evt asegs POST (ST 0xdda28 m1 x5 x6 x7 xa1 xa2 xa3 xa4 (Z_to_bv 64 1) x16 x17 x28).
Proof using AB LEN SEP.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P xa1 xa2 xa3 xa4 x5 x6 x7 x16 x17 x28 HK I HP -> -> -> ->; open_inv I.
window P 1%nat HW.
ld1 HW 0%nat. zstep. zstep. zstep. rewrite land_3.
st1 HW 0%nat. zstep. zstep. zstep. if_cases Kal; zify_cond Kal.
- use (mc_714 _ _ (P + 1)%Z).
- zstep. zstep. if_cases K1; zify_cond K1.
+ use (IH (Z.to_nat (n - (P + 1))) ltac:(lia) _ _ (P + 1)%Z).
+ zstep. use (mc_714 _ _ (P + 1)%Z).
Qed.

Lemma memcpy_body : forall junk,
rw_cells asegs m D [CB (Z.to_nat n) junk] -> bytes_at asegs m S src -> mem_inv asegs m ->
evt asegs POST (ST 0xdda10 m t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3).
Proof using AB LEN SEP.
intros junk DST0 SRC MI.
pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (u8arr_of_rw_cells _ _ _ _ _ DST0) as DST.
pose proof (copied_0 src junk ltac:(rewrite (rw_cells_CB_length _ _ _ _ _ DST0); lia)) as CP.
change 0%nat with (Z.to_nat 0) in CP. clear DST0.
zstep. rewrite land_3. zstep. if_cases Ksal; zify_cond Ksal.
-
zstep. zstep. rewrite land_3. zstep. if_cases Kdal; zify_cond Kdal.
+ use (mc_71c m junk 0%Z).
+ use (mc_7ec m junk 0%Z).
- zstep. if_cases K0; zify_cond K0.
+ zstep. use (mc_714 m junk 0%Z).
+ zstep. zstep. zstep. use (mc_6e4 (Z.to_nat n) m junk 0%Z).
Qed.
End Proofs.

Lemma memcpy_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte),
bytes_at asegs m (bv_unsigned a1) src ->
length src = Z.to_nat (bv_unsigned a2) ->
rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
(bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1)%Z ->
mem_inv asegs m ->
evt asegs (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdda10) fc None m (seg_rom asegs)).
Proof.
intros until junk. intros SRC LEN DST SEP MI.
eapply memcpy_body; try eassumption.
pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
pose proof (bytes_at_bound _ _ _ _ SRC) as B2.
pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R. cbn. lia.
Qed.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Export QTVW.Mqc.
Import ListNotations. Local Ltac QoSL.cell_of_bytes bs ::= QoSL.mkr__cell_of_bytes_10 bs. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9.
Local Open Scope Z_scope.

Import ListNotations.

Local Open Scope Z_scope.

Lemma zb_land_pow2_bit0 : forall x k, 0 <= k -> Z.testbit x k = false -> Z.land x (2^k) = 0.
Proof.
intros x k Hk Hb. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by lia.
destruct (Z.eqb_spec k i) as [<-|]; [rewrite Hb; reflexivity| apply Bool.andb_false_r].
Qed.

Lemma zb_lxor_pow2 : forall x k, 0 <= k ->
Z.lxor x (2^k) = x + 2^k - 2 * 2^k * ((x / 2^k) mod 2).
Proof.
intros x k Hk.
destruct (Z.testbit x k) eqn:Hb.
- pose proof (proj1 (Z.testbit_true x k Hk) Hb) as Hm. rewrite Hm.
set (y := Z.lxor x (2^k)).
assert (Hy : Z.testbit y k = false).
{ subst y. rewrite Z.lxor_spec, Hb, Z.pow2_bits_true by lia. reflexivity. }
assert (E : Z.lxor y (2^k) = y + 2^k).
{ symmetry. apply Z.add_nocarry_lxor. apply zb_land_pow2_bit0; assumption. }
subst y. rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r in E. lia.
- pose proof (proj1 (Z.testbit_false x k Hk) Hb) as Hm. rewrite Hm.
rewrite <- Z.add_nocarry_lxor by (apply zb_land_pow2_bit0; assumption). lia.
Qed.

Lemma zb_lxor_b31 : forall x, Z.lxor x 2147483648 = x + 2147483648 - 4294967296 * ((x / 2147483648) mod 2).
Proof. intros x. change 2147483648 with (2^31). rewrite zb_lxor_pow2 by lia. lia. Qed.

Lemma bv_wrap32_eq : forall z, bv_wrap 32 z = z mod 4294967296.
Proof. reflexivity. Qed.

Lemma swrap32_eq : forall z, bv_swrap 32 z = (z + 2147483648) mod 4294967296 - 2147483648.
Proof. reflexivity. Qed.

Lemma swrap32_small_A : forall z, - 2147483648 <= z < 2147483648 -> bv_swrap 32 z = z.
Proof. intros z Hz. rewrite swrap32_eq. rewrite Z.mod_small by lia. lia. Qed.

Lemma sext32_eq : forall z, sext32 z = ((z + 2147483648) mod 4294967296 - 2147483648) mod 18446744073709551616.
Proof.
intros z. unfold sext32, sub64, M32. rewrite wrap64_mod. change (2^64) with 18446744073709551616. f_equal.
change 4294967295 with (2^32 - 1). rewrite zb_land_mask by lia. change 2147483648 with (2^31).
rewrite zb_lxor_pow2 by lia. change 4294967296 with (2^32).
Z.div_mod_to_equations. nia.
Qed.

Lemma land_swrap32_sext32 : forall z, Z.land (bv_swrap 32 z) 18446744073709551615 = sext32 z.
Proof. intros z. rewrite land_W64, sext32_eq, swrap32_eq. reflexivity. Qed.

Lemma Z_to_bv_swrap32 : forall z, Z_to_bv 64 (bv_swrap 32 z) = Z_to_bv 64 (sext32 z).
Proof. intros z. rewrite <- land_swrap32_sext32. symmetry. apply Z_to_bv_land64. Qed.

Lemma sext32_range : forall z, 0 <= sext32 z < 18446744073709551616.
Proof. intros z. rewrite sext32_eq. apply Z.mod_pos_bound. lia. Qed.

Lemma sext32_small : forall z, 0 <= z < 2147483648 -> sext32 z = z.
Proof. intros z Hz. rewrite sext32_eq. rewrite (Z.mod_small (z + _)) by lia. rewrite Z.mod_small by lia. lia. Qed.

Lemma sext32_mod32 : forall z, sext32 (z mod 4294967296) = sext32 z.
Proof.
intros z. rewrite !sext32_eq. f_equal. f_equal.
rewrite Z.add_mod_idemp_l by lia. reflexivity.
Qed.

Lemma sext32_low : forall z, (sext32 z) mod 4294967296 = z mod 4294967296.
Proof.
intros z. rewrite sext32_eq. change 18446744073709551616 with (4294967296 * 4294967296).
rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z.mod_add by lia.
Z.div_mod_to_equations. lia.
Qed.

Lemma zext32_eq : forall z, zext32 z = z mod 4294967296.
Proof. intros z. unfold zext32, M32. change 4294967295 with (2^32 - 1). rewrite zb_land_mask by lia. reflexivity. Qed.

Lemma zext32_small : forall z, 0 <= z < 4294967296 -> zext32 z = z.
Proof. intros z Hz. rewrite zext32_eq. apply Z.mod_small. lia. Qed.

Lemma srliw_pos : forall x k, 0 < k -> srliw x k = Z.shiftr (x mod 4294967296) k.
Proof.
intros x k Hk. unfold srliw. unfold M32. change 4294967295 with (2^32 - 1). rewrite zb_land_mask by lia.
change (2^32) with 4294967296.
apply sext32_small. pose proof (Z.mod_pos_bound x 4294967296 ltac:(lia)) as Hr.
rewrite Z.shiftr_div_pow2 by lia. split. { apply Z.div_pos; lia. }
apply Z.div_lt_upper_bound; [lia|]. apply Z.lt_le_trans with 4294967296; [lia|].
assert (2^1 <= 2^k) by (apply Z.pow_le_mono_r; lia). change (2^1) with 2 in *. lia.
Qed.

Lemma walk_srliw : forall x k, 0 < k -> 0 <= x ->
bv_swrap 32 (Z.shiftr (bv_wrap 32 x) k) = Z.shiftr (x mod 4294967296) k.
Proof.
intros x k Hk Hx. rewrite bv_wrap32_eq. apply swrap32_small_A.
pose proof (Z.mod_pos_bound x 4294967296 ltac:(lia)) as Hr.
rewrite Z.shiftr_div_pow2 by lia. split. { apply Z.le_trans with 0; [lia|]. apply Z.div_pos; lia. }
apply Z.div_lt_upper_bound; [lia|]. apply Z.lt_le_trans with 4294967296; [lia|].
assert (2^1 <= 2^k) by (apply Z.pow_le_mono_r; lia). change (2^1) with 2 in *. lia.
Qed.

Lemma land_mask_small : forall x k, 0 <= k -> 0 <= x < 2^k -> Z.land x (2^k - 1) = x.
Proof. intros x k Hk Hx. rewrite zb_land_mask by lia. apply Z.mod_small. lia. Qed.

Lemma land_W64_small : forall x, 0 <= x < 18446744073709551616 -> Z.land x 18446744073709551615 = x.
Proof. intros x Hx. change 18446744073709551615 with (2^64 - 1). apply land_mask_small; [lia|]. change (2^64) with 18446744073709551616. lia. Qed.

Lemma land_M32_small : forall x, 0 <= x < 4294967296 -> Z.land x 4294967295 = x.
Proof. intros x Hx. change 4294967295 with (2^32 - 1). apply land_mask_small; [lia|]. change (2^32) with 4294967296. lia. Qed.

Lemma gcc_sext_small : forall v, 0 <= v < 2147483648 ->
Z.land (Z.lxor v 2147483648 - 2147483648) 18446744073709551615 = v.
Proof.
intros v Hv. rewrite zb_lxor_b31, (Z.div_small v) by lia. change (0 mod 2) with 0.
rewrite land_W64. rewrite Z.mod_small; lia.
Qed.

Lemma shiftr_mod32_bound : forall x k, 0 < k -> 0 <= Z.shiftr (x mod 4294967296) k < 2147483648.
Proof.
intros x k Hk. pose proof (Z.mod_pos_bound x 4294967296 ltac:(lia)) as Hr.
rewrite Z.shiftr_div_pow2 by lia. split. { apply Z.div_pos; lia. }
apply Z.div_lt_upper_bound; [lia|]. apply Z.lt_le_trans with 4294967296; [lia|].
assert (2^1 <= 2^k) by (apply Z.pow_le_mono_r; lia). change (2^1) with 2 in *. lia.
Qed.

Lemma lxor31_sub_small : forall v, 0 <= v < 2147483648 -> Z.lxor v 2147483648 - 2147483648 = v.
Proof. intros v Hv. rewrite zb_lxor_b31, (Z.div_small v) by lia. change (0 mod 2) with 0. lia. Qed.

Ltac fix32 :=
repeat first
[ rewrite walk_srliw by (first [lia | zrange_nonneg])
| match goal with
| |- context [Z.lxor (Z.shiftr (?x mod 4294967296) ?k) 2147483648 - 2147483648] =>
rewrite (lxor31_sub_small (Z.shiftr (x mod 4294967296) k)) by (apply shiftr_mod32_bound; lia)
| |- context [Z.land (Z.lxor (Z.shiftr (?x mod 4294967296) ?k) 2147483648 - 2147483648) 18446744073709551615] =>
rewrite (gcc_sext_small (Z.shiftr (x mod 4294967296) k)) by (apply shiftr_mod32_bound; lia)
end ].

Ltac wstep := zstep; fix32.

Ltac name_as_by_tac X e tac :=
set (X := e) in *;
let RX := fresh "R" X in
assert (RX : 0 <= X < 18446744073709551616) by (subst X; tac).

Tactic Notation "name_as_by" ident(X) constr(e) tactic3(tac) := name_as_by_tac X e tac.

Ltac model_reg_w_tac n X mexpr :=
let w := getreg n in
lazymatch w with
| Z_to_bv 64 ?e =>
replace (Z_to_bv 64 e) with (Z_to_bv 64 mexpr)
by (rewrite ?srliw_pos by lia; first [ f_equal; zeq | rewrite Z_to_bv_land64; f_equal; zeq ]);
set (X := mexpr) in *;
let RX := fresh "R" X in
assert (RX : 0 <= X < 18446744073709551616) by (subst X; rewrite ?srliw_pos by lia; zrange)
| _ => fail "model_reg_w: register" n "holds" w
end.

Tactic Notation "model_reg_w" constr(n) ident(X) constr(mexpr) := model_reg_w_tac n X mexpr.

Lemma zb_land_pow2 : forall x k, 0 <= k -> Z.land x (2^k) = 2^k * ((x / 2^k) mod 2).
Proof.
intros x k Hk. destruct (Z.testbit x k) eqn:Hb.
- pose proof (proj1 (Z.testbit_true x k Hk) Hb) as Hm. rewrite Hm, Z.mul_1_r.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.pow2_bits_eqb by lia.
destruct (Z.eqb_spec k i) as [<-|]; [rewrite Hb; reflexivity | apply Bool.andb_false_r].
- pose proof (proj1 (Z.testbit_false x k Hk) Hb) as Hm. rewrite Hm, Z.mul_0_r.
apply zb_land_pow2_bit0; assumption.
Qed.

Ltac reg_rewrite n lem :=
let w := getreg n in
lazymatch w with
| Z_to_bv 64 ?e =>
let e' := fresh "e" in let E := fresh "E" in
remember e as e' eqn:E in |- *;
rewrite lem in E; subst e'
end.

Lemma ltb1_eqb0 : forall x, 0 <= x -> (x <? 1) = (x =? 0).
Proof. intros x Hx. destruct (Z.ltb_spec0 x 1); destruct (Z.eqb_spec x 0); try reflexivity; exfalso; lia. Qed.

Lemma sext32_congr : forall x y, x mod 4294967296 = y mod 4294967296 -> sext32 x = sext32 y.
Proof. intros x y H. rewrite <- (sext32_mod32 x), <- (sext32_mod32 y), H. reflexivity. Qed.

Definition to_d_pack (dE dS a_hi : Z) : Z := Z.lor (Z.lor (shl64 dE 52) (shl64 (shr64 a_hi 63) 63)) dS.

Definition to_d_normD (sig1 exp0 : Z) : Z * Z :=
let carry := shr64 sig1 52 in (add64 carry exp0, Z.land (sub64 carry 1) sig1).

Definition to_d_subD (sig1 : Z) : Z * Z :=
let carry := nez64 (shr64 sig1 52) in (carry, Z.lxor sig1 (shl64 carry 52)).

Lemma lo64_words : forall lo hi, (0 <= lo < 2^64)%Z -> lo64 (lo + 2^64 * hi) = lo.
Proof.
intros lo hi H. unfold lo64. rewrite wrap64_mod.
rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma hi64_words : forall lo hi, (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z -> hi64 (lo + 2^64 * hi) = hi.
Proof.
intros lo hi Hl Hh. unfold hi64. rewrite wrap64_mod, Z.shiftr_div_pow2 by lia.
rewrite Z.mul_comm, Z.div_add, Z.div_small by lia. apply Z.mod_small. lia.
Qed.

Definition to_d_pack_g (dE dS sgn : Z) : Z := Z.lor (shl64 dE 52) (Z.lor dS sgn).

End Mq6.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDM6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDM6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q67d.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q67d. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQwg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQwg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mq7.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.cell_of_bytes bs ::= QoSL.mkr__cell_of_bytes_10 bs. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Definition qframe (s s' : AState) : Prop :=
as_tq s' = as_tq s /\ as_gq s' = as_gq s /\ as_reg s' = as_reg s /\ as_nres s' = as_nres s /\ as_spent s' = as_spent s /\ as_next s' = as_next s.

Lemma qframe_refl s : qframe s s.
Proof. repeat split; reflexivity. Qed.
Lemma qframe_trans s1 s2 s3 : qframe s1 s2 -> qframe s2 s3 -> qframe s1 s3.
Proof. intros (A1&A2&A3&A4&A5&A6) (B1&B2&B3&B4&B5&B6). repeat split; congruence. Qed.
Lemma qframe_set_cls s c x : qframe s (set_cls c x s).
Proof. repeat split; reflexivity. Qed.
Lemma qframe_upd_cls s c f : qframe s (upd_cls c f s).
Proof. repeat split; reflexivity. Qed.
Lemma qframe_set_inited s : qframe s (set_inited s).
Proof. repeat split; reflexivity. Qed.

Fixpoint split_last_spec {A} (l : list A) :
match split_last l with None => l = [] | Some (f, x) => l = f ++ [x] end.
Proof.
induction l as [|y l IH]; cbn; [reflexivity|].
destruct (split_last l) as [[f x]|]; subst; reflexivity.
Qed.

Local Notation TT := (fun (_ : evA) (_ : ansA) => True).

Definition okrel {R} (P : R -> Prop) (r : res R) : Prop := match r with ROk x => P x | _ => True end.

Lemma tall_bind_ok {R S} (P1 : R -> Prop) (P : S -> Prop) (t : T R) (f : R -> T S) :
tall TT (okrel P1) t -> (forall r, P1 r -> tall TT (okrel P) (f r)) -> tall TT (okrel P) (tbind t f).
Proof.
intros Ht Hf. apply tall_bind. eapply tall_mono; [exact Ht|]. intros [r| |w] Hr; cbn in *; [apply Hf; exact Hr| exact I| exact I].
Qed.

Ltac tret_ok := apply tall_ret; cbn.

Section S.
Variable L : ALay.

Lemma ensure_fa_qframe s c nf : tall TT (okrel (fun r => qframe s (snd r))) (ensure_fa L s c nf).
Proof.
unfold ensure_fa. destruct (_ <=? _); [tret_ok; apply qframe_refl|]. destruct (_ <? _); [exact I|].
apply tall_vis. intros a _. destruct (fixed_ok a); tret_ok; [apply qframe_set_cls| apply qframe_refl].
Qed.

Lemma populate_qframe s c req : tall TT (okrel (fun r => qframe s (snd r))) (populate L s c req).
Proof.
unfold populate. eapply tall_bind_ok with (P1 := fun r => qframe s (snd r)).
{ destruct (_ <? _); [| tret_ok; apply qframe_refl]. destruct (_ <? _); [exact I|].
apply tall_vis. intros a _. destruct (fixed_ok a); tret_ok; [apply qframe_set_cls| apply qframe_refl]. }
intros [ok s1] H1. cbn in H1. destruct ok; cbn [negb]; [| tret_ok; exact H1].
eapply tall_bind_ok with (P1 := fun r => qframe s (snd r)).
{ eapply tall_mono; [apply ensure_fa_qframe|]. intros [[b s2]| |w]; cbn; [| exact (fun x => x)| exact (fun x => x)]. intros H2. eapply qframe_trans; eauto. }
intros [ok2 s2] H2. cbn in H2. destruct ok2; cbn [negb]; tret_ok; [| exact H2]. eapply qframe_trans; [exact H2| apply qframe_set_cls].
Qed.

Lemma get_from_allocator_qframe s c k : tall TT (okrel (fun r => qframe s (snd r))) (get_from_allocator L s c k).
Proof.
unfold get_from_allocator. eapply tall_bind_ok with (P1 := fun r => qframe s (snd r)).
{ destruct (_ <? _); [apply populate_qframe| tret_ok; apply qframe_refl]. }
intros [ok s1] H1. cbn in H1. destruct ok; cbn [negb]; [| tret_ok; exact H1].
destruct (_ <? _); [exact I| tret_ok; eapply qframe_trans; [exact H1| apply qframe_set_cls]].
Qed.

Lemma refill_qframe s c : tall TT (okrel (fun r => qframe s (snd r))) (refill L s c).
Proof.
unfold refill. eapply tall_bind_ok with (P1 := fun r => qframe s (snd r)).
{ eapply tall_mono; [apply get_from_allocator_qframe|]. intros [[b s1]| |w]; cbn; [| exact (fun x => x)| exact (fun x => x)]. intros H. eapply qframe_trans; [apply qframe_set_inited| exact H]. }
intros [ok s1] H1. cbn in H1. destruct ok; cbn [negb]; tret_ok; [| exact H1]. eapply qframe_trans; [exact H1| apply qframe_upd_cls].
Qed.

Lemma cache_alloc_qframe s c : tall TT (okrel (fun r => qframe s (snd r))) (cache_alloc L s c).
Proof.
unfold cache_alloc. eapply tall_bind_ok with (P1 := fun r => qframe s (snd r)).
{ destruct (_ =? _); [apply refill_qframe| tret_ok; apply qframe_refl]. }
intros [ok s1] H1. cbn in H1. destruct ok; cbn [negb]; tret_ok; [| exact H1]. eapply qframe_trans; [exact H1| apply qframe_upd_cls].
Qed.

Lemma enqueue_qptrs s p : 0 <= aptr_req p -> tall TT (okrel (fun s' =>
concat (map b_chunks (q_list (as_tq s'))) = concat (map b_chunks (q_list (as_tq s))) ++ [p]
/\ q_bytes (as_tq s') <= q_bytes (as_tq s) + aptr_used p + kBatchBytes
/\ as_gq s' = as_gq s /\ as_reg s' = as_reg s /\ as_nres s' = as_nres s /\ as_spent s' = as_spent s /\ as_next s' = as_next s)) (enqueue L s p).
Proof.
intros Hp. assert (KBB : kBatchBytes = 8192) by reflexivity.
assert (UP : 1 <= aptr_used p) by (unfold aptr_used, used_size; lia).
unfold enqueue. pose proof (split_last_spec (q_list (as_tq s))) as SL.
assert (NB : forall s1, as_tq s1 = as_tq s -> qframe s s1 ->
tall TT (okrel (fun s' => concat (map b_chunks (q_list (as_tq s'))) = concat (map b_chunks (q_list (as_tq s))) ++ [p]
/\ q_bytes (as_tq s') <= q_bytes (as_tq s) + aptr_used p + kBatchBytes
/\ as_gq s' = as_gq s /\ as_reg s' = as_reg s /\ as_nres s' = as_nres s /\ as_spent s' = as_spent s /\ as_next s' = as_next s))
(new_batch L s1 p (aptr_used p))).
{ intros s1 E1 Q1. unfold new_batch. eapply tall_bind_ok with (P1 := fun r => qframe s1 (snd r)); [apply cache_alloc_qframe|].
intros [ok s2] H2. cbn in H2. destruct ok; cbn [negb]; [| exact I]. tret_ok.
pose proof (qframe_trans _ _ _ Q1 H2) as (Etq & Egq & Ereg & Enres & Espent & Enext). rewrite <- Etq.
unfold q_push_back. cbn [q_list q_bytes b_chunks b_size]. rewrite map_app, concat_app. cbn [map concat b_chunks app]. rewrite ?app_nil_r.
repeat split; try assumption; try lia. }
destruct (split_last (q_list (as_tq s))) as [[front b]|].
- destruct (_ =? _); [apply NB; [reflexivity| apply qframe_refl]|]. tret_ok. cbn [q_list q_bytes]. rewrite SL.
rewrite !map_app, !concat_app. cbn [map concat b_chunks]. rewrite !app_nil_r, app_assoc. repeat split; try reflexivity. lia.
- apply NB; [reflexivity| apply qframe_refl].
Qed.
End S.

Section Bridge.
Variable atn : node -> machine_state -> Prop.

Lemma aimplT_tall {R} (t : T R) (P : R -> Prop) s Q ms :
tall TT (okrel P) t -> aimplT atn t s Q ms -> aimplT atn t s (fun r s' ms' => P r /\ Q r s' ms') ms.
Proof.
unfold aimplT. revert s ms. induction t as [[r| |w]|e k IH]; intros s ms Ht H; cbn [membedA] in *.
- unfold implMG, mret in *. cbn in *. eapply evt_mono; [exact H|]. intros ms' HQ; cbn; auto.
- eapply implMA_mspin_any. exact H.
- apply implMG_unr.
- eapply implMG_bind.
+ eapply ev_stepA_state. unfold implMG, mbind, ebind in H.
instantiate (1 := fun a s' ms' => impl asegs atn (membedA (k a) s') (epost (fun p => Q (fst p) (snd p))) ms').
unfold implMG. revert H. generalize (ev_stepA e s). intros t H.
revert ms H. induction t as [x|n kk IHt]; intros ms H; cbn [Qc6I.bind] in *.
* unfold epost in H |- *. destruct x as [|[a s']]; cbn in *; apply evt_done; [exact I| exact H].
* rewrite aimpl_vis_unfold in H. rewrite aimpl_vis_unfold. eapply evt_mono; [exact H|].
intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. apply IHt. apply Hk.
+ intros a s' ms' [-> H1]. cbn in H1. apply IH; [apply Ht; exact I| exact H1].
Qed.

Lemma impl_then {R} (t : itree node R) (Q Q' : R -> machine_state -> Prop) ms :
impl asegs atn t Q ms -> (forall r ms', Q r ms' -> evt asegs (Q' r) ms') -> impl asegs atn t Q' ms.
Proof.
revert ms. induction t as [r|n k IH]; intros ms H HQ; cbn in *.
- eapply evt_cut; [exact H|]. intros ms' H'. exact (HQ r ms' H').
- eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; [apply Hk| exact HQ].
Qed.

Lemma aimplT_then {R} (t : T R) s (Q Q' : R -> PStateA -> machine_state -> Prop) ms :
aimplT atn t s Q ms -> (forall r s' ms', Q r s' ms' -> evt asegs (Q' r s') ms') -> aimplT atn t s Q' ms.
Proof.
unfold aimplT, implMG. intros H HQ. eapply impl_then; [exact H|].
intros [|[a s']] ms' H'; cbn in *; [apply evt_done; exact I| apply HQ; exact H'].
Qed.
End Bridge.
