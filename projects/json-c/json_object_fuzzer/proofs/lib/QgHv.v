(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QRjH QHnV QCcH QfLs Q0Ek QTEu Qsw7 QJjn QRUw Q7UD Qhd4 Qwm6 QlKV QsKa QpNt QgoM Q4v2 Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7 QpNt.Mq4 QgoM.Mq1 Q4v2.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition realloc_nf_stmt (HIx : heap_iface_A A4L) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FR : list frame) (B : bud) (p n0 n lo : Z) (errv : word) (old junk0 : list byte) (u : uwd),
HEAPA A4L HIx A LB LM FR B m c -> In (p, n0) LB ->
rw_cells (hl_segs A4L) m p [CB (Z.to_nat n0) (old ++ junk0)] ->
stk (hl_segs A4L) m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A A4L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top A4L HIx + 64 ->
rw_cells (hl_segs A4L) m (hl_tp A4L - 164) [C4 errv] ->
tp = Z_to_bv 64 (hl_tp A4L) ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 n -> 1 <= n < 2^40 ->
uw_pre A4L (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok A4L (hl_realloc A4L) ra u ->
16 * n + 512 <= bB B -> uw_cost u <= bD B ->
(forall ms' m' c' (A' : ASA A4L HIx) (r : Z) (errv' : word),
ret_state A4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only (cfg_model c) (cfg_model c') ->
stk (hl_segs A4L) m' lo (bv_unsigned sp) ->
rw_cells (hl_segs A4L) m' (hl_tp A4L - 164) [C4 errv'] ->
(r <> 0 /\ heap_pres A4L (lb_remove p LB ++ LM ++ fr_ivs A4L FR) (bv_unsigned sp) m m'
/\ (exists junk, rw_cells (hl_segs A4L) m' r [CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n (Z.of_nat (length old)))) old ++ junk)])
/\ HEAPA A4L HIx A' ((r, n) :: lb_remove p LB) LM FR (charge B (16 * n + 512) (uw_cost u)) m' c') ->
AJ5 A4L HIx A' T c' ms') ->
AJ5 A4L HIx A T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_realloc A4L)) fc None m (seg_rom (hl_segs A4L))).

Section APbMemappendNF.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Definition memappend_A_post_nf (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (pb buf bpos cap : Z) (content src : list byte) (n lo : Z)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : Z) (errv' : word) (buf' cap' : Z) (B' : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\
bB B - memappend_costX2 cap bpos n <= bB B' /\ bD B <= bD B' /\
HEAPAx A' ((pb, PB_SZ) :: (buf', cap') :: LB) LM FRS B' m' md' /\
((r = n /\ cap' = memappend_cap2 cap bpos n /\ pbufc asegs m' [(pb, PB_SZ); (buf', cap')] pb (firstn (Z.to_nat bpos) content ++ src))
\/ (r = 2^64 - 1 /\ buf' = buf /\ cap' = cap /\ bB B <= bB B' /\ pbuf_core asegs m' pb buf bpos cap content)).

Section Tail.
Variables (ra sp gp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud) (lo : Z) (pb buf0 bpos0 cap0 n : Z) (content0 : list byte) (T : TSet).
Variable (s0 : word).

Lemma memappend_A_tail_nf :
forall (xra t0 t1 t2 x9 a3 a4 a5 a6 a7 x18 x19 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(buf bpos cap b : Z) (content src : list byte) (errv : word) (fjunk : list byte),
HEAPAx A ((pb, PB_SZ) :: (buf, cap) :: LB) LM FRS B m md ->
pbufx m pb buf bpos cap content ->
bpos + n + 1 <= cap -> 0 <= n < 2^31 ->
bytes_at asegs m b src -> Z.of_nat (length src) = n -> 0 <= b -> b + n <= alloc_ceiling ->
(0 < n -> unpoisoned asegs m A_SB b n) -> (n <= 64 \/ app_mem b n) ->
(b + n <= buf \/ buf + cap <= b) ->
stk asegs m lo (bv_unsigned sp + -112) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -112 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m (bv_unsigned sp + -112) [CB 8 fjunk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs m A_ERRNO [C4 errv] ->
bv_unsigned ra mod 2 = 0 ->
model_vm_only (cfg_model md0) (cfg_model md) -> heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m ->
bB B0 - memappend_costX2 cap0 bpos0 n <= bB B -> bD B0 <= bD B ->
cap = memappend_cap2 cap0 bpos0 n ->
bpos = bpos0 -> firstn (Z.to_nat bpos) content = firstn (Z.to_nat bpos0) content0 ->
(forall ms' md' A', memappend_A_post_nf ra sp gp (Z_to_bv 64 A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 pb buf0 bpos0 cap0 content0 src n lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pb + 8)) x9
(Z_to_bv 64 pb) (Z_to_bv 64 b) (Z_to_bv 64 n) a3 a4 a5 a6 a7
x18 x19 (Z_to_bv 64 A_SB) (Z_to_bv 64 (pb / 8 + 1 + A_SB)) (Z_to_bv 64 (pb / 8)) x23 x24 x25 x26 x27 t3 t4 t5 t6)
F (Z_to_bv 64 0x9a24c) fc None m (seg_rom asegs)).
Proof.
intros until fjunk. intros HP PBX ROOM Hn SRC SRCL Hb0 Hbn UPS AMS BSEP ST LO LOS SPA HT FR ERR RA VM0 HPR BB BD CAPE Ebpos Epre K.
destruct PBX as (Hbp & Hcap & Hlen & PBS & PBUF).
unfold_consts. unfold A_SB, A_TP, A_ERRNO in *. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
blk_factsA A4L HIx HP pb 16 Hal Hlo Hhi Himg.
blk_factsA A4L HIx HP buf cap Hbal Hblo Hbhi Hbimg.
assert (Hne : pb <> buf).
{ intros E. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. cbn in ND. inversion ND as [|x l Hni Hnd]; subst. apply Hni. left. reflexivity. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ pb 16 buf cap HP ltac:(left; reflexivity) ltac:(right; left; reflexivity) Hne) as DISJ.
shadow_nowA A4L HIx HP pb 16 SHpb.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ pb 16 0 pb 16 HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ pb 16 1 buf cap HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEP1b.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ pb 16 0 buf cap HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEP0b.
a4l.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp); (buf + bpos, buf + bpos + n + 1); (pb, pb + 16); (lo, bv_unsigned sp + -112)] m) as MU.

destruct (rw_cells_CB_cut asegs _ _ _ _ (Z.to_nat bpos) PBUF ltac:(lia)) as [PB0 PB1].
destruct (rw_cells_CB_cut asegs _ _ _ _ (Z.to_nat n) PB1 ltac:(lia)) as [PBD PB2].
clear PBUF PB1.
replace (buf + Z.of_nat (Z.to_nat bpos)) with (buf + bpos) in PBD, PB2 by lia.
replace (buf + bpos + Z.of_nat (Z.to_nat n)) with (buf + bpos + n) in PB2 by lia.
destruct (rw_cells_CB_cut asegs _ _ _ _ 1%nat PB2 ltac:(lia)) as [PBZ PB3]. clear PB2.
replace (buf + bpos + n + Z.of_nat 1) with (buf + bpos + n + 1) in PB3 by lia.

pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(right; left; reflexivity)) as SHb. unfold shad in SHb.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ buf cap ((bpos + n) / 8) buf cap HP ltac:(right; left; reflexivity) ltac:(Z.div_mod_to_equations; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEPgb.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ buf cap ((bpos + n) / 8) pb 16 HP ltac:(right; left; reflexivity) ltac:(Z.div_mod_to_equations; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEPgp.
a4l.
assert (SHZ : exists v, ro_cells asegs m (buf / 8 + 2147450880 + (bpos + n) / 8) [C1 (Z_to_bv 8 v)] /\ (v = 0 \/ (0 < v < 8 /\ (buf + bpos + n) mod 8 < v))).
{ destruct (Z.lt_ge_cases (8 * ((bpos + n) / 8) + 8) (cap + 1)) as [HA | HB].
- exists 0. split; [| left; reflexivity].
exact (shadow_granule0 asegs m (buf / 8 + 2147450880) cap ((bpos + n) / 8) ltac:(Z.div_mod_to_equations; lia) ltac:(lia) SHb).
- assert (Hm : cap mod 8 <> 0) by (Z.div_mod_to_equations; lia).
assert (Hg : (bpos + n) / 8 = cap / 8) by (Z.div_mod_to_equations; lia).
exists (cap mod 8). split; [| right; Z.div_mod_to_equations; lia].
rewrite Hg. exact (shadow_tail asegs m (buf / 8 + 2147450880) cap ltac:(lia) Hm SHb). }
clear SHb.
stash PB0. stash PB3. stash SRC. stash SHZ. stash SEPgb. stash SEPgp. stash AMS. stash BSEP. stash UPS.
reenterA asegs A4L HIx asegs_wx HP.
step.
try replace (2147450880 + pb / 8) with (pb / 8 + 2147450880) by lia.
step. step. if_false. rewrite ?zxb_zero.
try replace (pb / 8 + 1 + 2147450880) with (pb / 8 + 2147450880 + 1) by lia.
step.
step.
step. if_false. rewrite ?sxb_zero.
clear SHpb SEP0 SEP1b SEP0b.
step. norm_w32.
step. step. step. step.
step.
unstash SRC. unstash AMS. unstash BSEP. unstash UPS.
eapply amemmove_sound_U with (d := buf + bpos) (s := b) (n := n) (lo := lo);
rewrite ?unsigned_lit by lia;
[ intros Hpos; eapply (unpoisoned_of_blk HIx); [exact HP | right; left; reflexivity | lia | lia | lia]
| exact UPS
| eapply (asan_rt_ok_of_HEAPA HIx); exact HP
| lia | lia | lia | lia | lia | lia
| reflexivity | reflexivity | reflexivity | lia
| destruct AMS as [Hs64 | AMb]; [left; exact Hs64 | right; split; [eapply (blk_app_mem HIx); [exact HP | right; left; reflexivity | lia | lia] | exact AMb]]
| lia
| exact PBD | exact SRC | lia
| exact ST | exact LO | lia | replace (bv_unsigned sp + -112) with (bv_unsigned sp - 112) by lia; rewrite Zminus_mod, SPA; reflexivity
| exact MI | reflexivity | ].
clear AMS UPS.
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m4 MU4 WM4 MI4 DST4 SRC4 ST4.
stash SRC4.
lazymatch type of MU4 with munch _ ?mc _ =>
transport_after_call asegs mc m4 MU4 WM4; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU4 WM4 end.
replace (ret_pc (Z_to_bv 64 0x9a27c)) with (Z_to_bv 64 0x9a27c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step.
step. norm_w32. step.
step. norm_w32.
stepz.
step.
try replace (buf + (bpos + n)) with (buf + bpos + n) by lia.

unstash SHZ. unstash SEPgb. unstash SEPgp. destruct SHZ as (v & SHZc & Hv).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (ro_cells_transport asegs _ m mc) in SHZc; [| exact MU | cbn [disjoint_from]; simpl_sizes; unfold alloc_ceiling in *; lia] end.
clear SEPgb SEPgp.
pose proof (ov_read1_of_ro asegs _ _ _ SHZc) as HR.
step. step. sh_norm.
replace ((buf + bpos + n) / 8 + 2147450880) with (buf / 8 + 2147450880 + (bpos + n) / 8) by (Z.div_mod_to_equations; lia).
step. rewrite (sxb_small v) by (destruct Hv as [->|(? & ?)]; lia). clear HR SHZc.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (STORE : forall y2 y3 : word,
evt asegs (AJ5e A4L HIx A T md)
(MS (mkR (Z_to_bv 64 0x9a27c) (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 6434400) t0' t1' t2' (Z_to_bv 64 n) (Z_to_bv 64 pb)
(Z_to_bv 64 n) (Z_to_bv 64 (buf + bpos + n)) y2 y3 a4' a5' a6' a7'
x18 x19 (Z_to_bv 64 2147450880) (Z_to_bv 64 (pb / 8 + 2147450881)) (Z_to_bv 64 (pb / 8 + 2147450880)) x23 x24 x25 x26 x27 t3' t4' t5' t6')
F (Z_to_bv 64 0x9a2a4) fc None mc (seg_rom asegs)))
end.
{ intros y2 y3.
set (ez := buf + bpos + n) in *.
stepz.
subst ez.
do 15 step.
evt_done5. apply K. unfold memappend_A_post_nf.
unstash PB0. unstash PB3. unstash SRC4.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
eapply (rw_cells_transport asegs _ m mf) in PB0; [| exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; unfold alloc_ceiling in *; lia];
eapply (rw_cells_transport asegs _ m mf) in PB3; [| exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; unfold alloc_ceiling in *; lia];
exists mf, n, errv, buf, cap, B end.
split; [| split; [exact VM0 | split; [| split; [| split; [ | split; [exact BB | split; [exact BD | split; [| left; split; [reflexivity|]; split; [exact CAPE|]]]]]]]]].
- apply ret_statew_same.
- release_frame FR ST4 (bv_unsigned sp). exact ST4.
- eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros bb Hbb; right; right; exact Hbb | clia | solve_clientWA A4L HIx HP].
- assumption.
- eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption].
-
rewrite <- Epre.
exists buf, (bpos + n), cap, (skipn 1 (skipn (Z.to_nat n) (skipn (Z.to_nat bpos) content))).
split; [reflexivity|]. split. { rewrite length_app, length_firstn. lia. }
unfold pbuf_core. split; [lia|]. split; [lia|]. split; [| split; [eassumption|]].
{ rewrite !length_app, length_firstn, !length_skipn. cbn [length]. lia. }
pose proof (rw_cells_CB_join asegs _ _ _ _ _ _ PB0 ltac:(replace (buf + Z.of_nat (Z.to_nat bpos)) with (buf + bpos) by lia; exact DST4)) as J1.
match goal with PZ : rw_cells asegs ?mf (buf + bpos + n) [C1 _] |- _ =>
apply (rw_cells_recast asegs _ _ _ [CB 1 [Z_to_bv 8 0]]) in PZ; [| cbn; auto | reflexivity | reflexivity];
pose proof (rw_cells_CB_join asegs _ _ _ _ _ _ J1 ltac:(replace (buf + Z.of_nat (Z.to_nat bpos + Z.to_nat n)) with (buf + bpos + n) by lia; exact PZ)) as J2 end.
pose proof (rw_cells_CB_join asegs _ _ _ _ _ _ J2 ltac:(replace (buf + Z.of_nat (Z.to_nat bpos + Z.to_nat n + 1)) with (buf + bpos + n + 1) by lia; exact PB3)) as J3.
replace (Z.to_nat bpos + Z.to_nat n + 1 + (Z.to_nat cap - Z.to_nat bpos - Z.to_nat n - 1))%nat with (Z.to_nat cap) in J3 by lia.
revert J3. rewrite <- ?app_assoc. intros J3. rewrite <- ?app_assoc in J3. exact J3. }
step.
destruct Hv as [-> | (Hk & Hlast)].
+ if_false. apply STORE.
+ if_truex. step. rewrite (unsigned_lit (buf + bpos + n)) by lia. rewrite land7_mod8 by lia.
step. if_truex. apply STORE.
Qed.
End Tail.
End APbMemappendNF.
End RC__1.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTEu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTEu. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.    From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpNt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpNt.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgoM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgoM. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4v2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4v2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition realloc_nf_stmt (HIx : heap_iface_A A4L) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FR : list frame) (B : bud) (p n0 n lo : Z) (errv : word) (old junk0 : list byte) (u : uwd),
HEAPA A4L HIx A LB LM FR B m c -> In (p, n0) LB ->
rw_cells (hl_segs A4L) m p [CB (Z.to_nat n0) (old ++ junk0)] ->
stk (hl_segs A4L) m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A A4L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top A4L HIx + 64 ->
rw_cells (hl_segs A4L) m (hl_tp A4L - 164) [C4 errv] ->
tp = Z_to_bv 64 (hl_tp A4L) ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 n -> 1 <= n < 2^40 ->
uw_pre A4L (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok A4L (hl_realloc A4L) ra u ->
16 * n + 512 <= bB B -> uw_cost u <= bD B ->
(forall ms' m' c' (A' : ASA A4L HIx) (r : Z) (errv' : word),
ret_state A4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only (cfg_model c) (cfg_model c') ->
stk (hl_segs A4L) m' lo (bv_unsigned sp) ->
rw_cells (hl_segs A4L) m' (hl_tp A4L - 164) [C4 errv'] ->
(r <> 0 /\ heap_pres A4L (lb_remove p LB ++ LM ++ fr_ivs A4L FR) (bv_unsigned sp) m m'
/\ (exists junk, rw_cells (hl_segs A4L) m' r [CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n (Z.of_nat (length old)))) old ++ junk)])
/\ HEAPA A4L HIx A' ((r, n) :: lb_remove p LB) LM FR (charge B (16 * n + 512) (uw_cost u)) m' c') ->
AJ5 A4L HIx A' T c' ms') ->
AJ5 A4L HIx A T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_realloc A4L)) fc None m (seg_rom (hl_segs A4L))).

Section APbMemappendNF.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Definition memappend_A_post_nf (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (pb buf bpos cap : Z) (content src : list byte) (n lo : Z)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : Z) (errv' : word) (buf' cap' : Z) (B' : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\
bB B - memappend_costX2 cap bpos n <= bB B' /\ bD B <= bD B' /\
HEAPAx A' ((pb, PB_SZ) :: (buf', cap') :: LB) LM FRS B' m' md' /\
((r = n /\ cap' = memappend_cap2 cap bpos n /\ pbufc asegs m' [(pb, PB_SZ); (buf', cap')] pb (firstn (Z.to_nat bpos) content ++ src))
\/ (r = 2^64 - 1 /\ buf' = buf /\ cap' = cap /\ bB B <= bB B' /\ pbuf_core asegs m' pb buf bpos cap content)).

Section Tail.
Variables (ra sp gp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud) (lo : Z) (pb buf0 bpos0 cap0 n : Z) (content0 : list byte) (T : TSet).
Variable (s0 : word).

Lemma memappend_A_tail_nf :
forall (xra t0 t1 t2 x9 a3 a4 a5 a6 a7 x18 x19 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(buf bpos cap b : Z) (content src : list byte) (errv : word) (fjunk : list byte),
HEAPAx A ((pb, PB_SZ) :: (buf, cap) :: LB) LM FRS B m md ->
pbufx m pb buf bpos cap content ->
bpos + n + 1 <= cap -> 0 <= n < 2^31 ->
bytes_at asegs m b src -> Z.of_nat (length src) = n -> 0 <= b -> b + n <= alloc_ceiling ->
(0 < n -> unpoisoned asegs m A_SB b n) -> (n <= 64 \/ app_mem b n) ->
(b + n <= buf \/ buf + cap <= b) ->
stk asegs m lo (bv_unsigned sp + -112) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -112 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m (bv_unsigned sp + -112) [CB 8 fjunk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs m A_ERRNO [C4 errv] ->
bv_unsigned ra mod 2 = 0 ->
model_vm_only (cfg_model md0) (cfg_model md) -> heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m ->
bB B0 - memappend_costX2 cap0 bpos0 n <= bB B -> bD B0 <= bD B ->
cap = memappend_cap2 cap0 bpos0 n ->
bpos = bpos0 -> firstn (Z.to_nat bpos) content = firstn (Z.to_nat bpos0) content0 ->
(forall ms' md' A', memappend_A_post_nf ra sp gp (Z_to_bv 64 A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 pb buf0 bpos0 cap0 content0 src n lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pb + 8)) x9
(Z_to_bv 64 pb) (Z_to_bv 64 b) (Z_to_bv 64 n) a3 a4 a5 a6 a7
x18 x19 (Z_to_bv 64 A_SB) (Z_to_bv 64 (pb / 8 + 1 + A_SB)) (Z_to_bv 64 (pb / 8)) x23 x24 x25 x26 x27 t3 t4 t5 t6)
F (Z_to_bv 64 0x9b704) fc None m (seg_rom asegs)).
Proof.
intros until fjunk. intros HP PBX ROOM Hn SRC SRCL Hb0 Hbn UPS AMS BSEP ST LO LOS SPA HT FR ERR RA VM0 HPR BB BD CAPE Ebpos Epre K.
destruct PBX as (Hbp & Hcap & Hlen & PBS & PBUF).
unfold_consts. unfold A_SB, A_TP, A_ERRNO in *. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
blk_factsA A4L HIx HP pb 16 Hal Hlo Hhi Himg.
blk_factsA A4L HIx HP buf cap Hbal Hblo Hbhi Hbimg.
assert (Hne : pb <> buf).
{ intros E. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. cbn in ND. inversion ND as [|x l Hni Hnd]; subst. apply Hni. left. reflexivity. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ pb 16 buf cap HP ltac:(left; reflexivity) ltac:(right; left; reflexivity) Hne) as DISJ.
shadow_nowA A4L HIx HP pb 16 SHpb.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ pb 16 0 pb 16 HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ pb 16 1 buf cap HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEP1b.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ pb 16 0 buf cap HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEP0b.
a4l.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp); (buf + bpos, buf + bpos + n + 1); (pb, pb + 16); (lo, bv_unsigned sp + -112)] m) as MU.

destruct (rw_cells_CB_cut asegs _ _ _ _ (Z.to_nat bpos) PBUF ltac:(lia)) as [PB0 PB1].
destruct (rw_cells_CB_cut asegs _ _ _ _ (Z.to_nat n) PB1 ltac:(lia)) as [PBD PB2].
clear PBUF PB1.
replace (buf + Z.of_nat (Z.to_nat bpos)) with (buf + bpos) in PBD, PB2 by lia.
replace (buf + bpos + Z.of_nat (Z.to_nat n)) with (buf + bpos + n) in PB2 by lia.
destruct (rw_cells_CB_cut asegs _ _ _ _ 1%nat PB2 ltac:(lia)) as [PBZ PB3]. clear PB2.
replace (buf + bpos + n + Z.of_nat 1) with (buf + bpos + n + 1) in PB3 by lia.

pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(right; left; reflexivity)) as SHb. unfold shad in SHb.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ buf cap ((bpos + n) / 8) buf cap HP ltac:(right; left; reflexivity) ltac:(Z.div_mod_to_equations; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEPgb.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ buf cap ((bpos + n) / 8) pb 16 HP ltac:(right; left; reflexivity) ltac:(Z.div_mod_to_equations; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEPgp.
a4l.
assert (SHZ : exists v, ro_cells asegs m (buf / 8 + 2147450880 + (bpos + n) / 8) [C1 (Z_to_bv 8 v)] /\ (v = 0 \/ (0 < v < 8 /\ (buf + bpos + n) mod 8 < v))).
{ destruct (Z.lt_ge_cases (8 * ((bpos + n) / 8) + 8) (cap + 1)) as [HA | HB].
- exists 0. split; [| left; reflexivity].
exact (shadow_granule0 asegs m (buf / 8 + 2147450880) cap ((bpos + n) / 8) ltac:(Z.div_mod_to_equations; lia) ltac:(lia) SHb).
- assert (Hm : cap mod 8 <> 0) by (Z.div_mod_to_equations; lia).
assert (Hg : (bpos + n) / 8 = cap / 8) by (Z.div_mod_to_equations; lia).
exists (cap mod 8). split; [| right; Z.div_mod_to_equations; lia].
rewrite Hg. exact (shadow_tail asegs m (buf / 8 + 2147450880) cap ltac:(lia) Hm SHb). }
clear SHb.
stash PB0. stash PB3. stash SRC. stash SHZ. stash SEPgb. stash SEPgp. stash AMS. stash BSEP. stash UPS.
reenterA asegs A4L HIx asegs_wx HP.
step.
try replace (2147450880 + pb / 8) with (pb / 8 + 2147450880) by lia.
step. step. if_false. rewrite ?zxb_zero.
try replace (pb / 8 + 1 + 2147450880) with (pb / 8 + 2147450880 + 1) by lia.
step.
step.
step. if_false. rewrite ?sxb_zero.
step. norm_w32.
step.
step. step. ub_nzpair buf (bpos + buf). step. if_falsex.
step. step. step. step. ub_nowrap (bpos + buf) buf bpos. step. if_falsex.
step. step. step.
replace (bpos + buf) with (buf + bpos) by lia.
step.
unstash SRC. unstash AMS. unstash BSEP. unstash UPS.
eapply amemmove_sound_U with (d := buf + bpos) (s := b) (n := n) (lo := lo);
rewrite ?unsigned_lit by lia;
[ intros Hpos; eapply (unpoisoned_of_blk HIx); [exact HP | right; left; reflexivity | lia | lia | lia]
| exact UPS
| eapply (asan_rt_ok_of_HEAPA HIx); exact HP
| lia | lia | lia | lia | lia | lia
| reflexivity | reflexivity | reflexivity | lia
| destruct AMS as [Hs64 | AMb]; [left; exact Hs64 | right; split; [eapply (blk_app_mem HIx); [exact HP | right; left; reflexivity | lia | lia] | exact AMb]]
| lia
| exact PBD | exact SRC | lia
| exact ST | exact LO | lia | replace (bv_unsigned sp + -112) with (bv_unsigned sp - 112) by lia; rewrite Zminus_mod, SPA; reflexivity
| exact MI | reflexivity | ].
clear AMS UPS.
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m4 MU4 WM4 MI4 DST4 SRC4 ST4.
stash SRC4.
lazymatch type of MU4 with munch _ ?mc _ =>
transport_after_call asegs mc m4 MU4 WM4; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU4 WM4 end.
replace (ret_pc (Z_to_bv 64 0x9b754)) with (Z_to_bv 64 0x9b754) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. step. if_false. rewrite ?sxb_zero.
step. norm_w32.
step. step. norm_w32. step. if_falsex.
step. step.
step. step. if_false. rewrite ?sxb_zero.
step. norm_w32.
stepz.
step. step. if_false. rewrite ?zxb_zero.
clear SHpb SEP0 SEP1b SEP0b.
step.
step.
step. step. ub_nzpair buf (buf + (bpos + n)). step. if_falsex.
step. step. step. step. ub_nowrap (buf + (bpos + n)) buf (bpos + n). step. if_falsex.
step. if_falsex.
try replace (buf + (bpos + n)) with (buf + bpos + n) by lia.

unstash SHZ. unstash SEPgb. unstash SEPgp. destruct SHZ as (v & SHZc & Hv).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (ro_cells_transport asegs _ m mc) in SHZc; [| exact MU | cbn [disjoint_from]; simpl_sizes; unfold alloc_ceiling in *; lia] end.
clear SEPgb SEPgp.
pose proof (ov_read1_of_ro asegs _ _ _ SHZc) as HR.
step. step. sh_norm.
replace ((buf + bpos + n) / 8 + 2147450880) with (buf / 8 + 2147450880 + (bpos + n) / 8) by (Z.div_mod_to_equations; lia).
step. rewrite (sxb_small v) by (destruct Hv as [->|(? & ?)]; lia). clear HR SHZc.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (STORE : forall y2 y3 : word,
evt asegs (AJ5e A4L HIx A T md)
(MS (mkR (Z_to_bv 64 0x9b754) (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 6444320) t0' t1' t2' (Z_to_bv 64 (pb + 8)) (Z_to_bv 64 pb)
(Z_to_bv 64 n) (Z_to_bv 64 (buf + bpos + n)) y2 y3 (Z_to_bv 64 0) (Z_to_bv 64 0) a6' a7'
(Z_to_bv 64 n) x19 (Z_to_bv 64 2147450880) (Z_to_bv 64 (pb / 8 + 2147450881)) (Z_to_bv 64 (pb / 8 + 2147450880)) x23 x24 x25 x26 x27 t3' t4' t5' t6')
F (Z_to_bv 64 0x9b7c8) fc None mc (seg_rom asegs)))
end.
{ intros y2 y3.
set (ez := buf + bpos + n) in *.
stepz.
subst ez.
do 15 step.
evt_done5. apply K. unfold memappend_A_post_nf.
unstash PB0. unstash PB3. unstash SRC4.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
eapply (rw_cells_transport asegs _ m mf) in PB0; [| exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; unfold alloc_ceiling in *; lia];
eapply (rw_cells_transport asegs _ m mf) in PB3; [| exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; unfold alloc_ceiling in *; lia];
exists mf, n, errv, buf, cap, B end.
split; [| split; [exact VM0 | split; [| split; [| split; [ | split; [exact BB | split; [exact BD | split; [| left; split; [reflexivity|]; split; [exact CAPE|]]]]]]]]].
- apply ret_statew_same.
- release_frame FR ST4 (bv_unsigned sp). exact ST4.
- eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros bb Hbb; right; right; exact Hbb | clia | solve_clientWA A4L HIx HP].
- assumption.
- eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption].
-
rewrite <- Epre.
exists buf, (bpos + n), cap, (skipn 1 (skipn (Z.to_nat n) (skipn (Z.to_nat bpos) content))).
split; [reflexivity|]. split. { rewrite length_app, length_firstn. lia. }
unfold pbuf_core. split; [lia|]. split; [lia|]. split; [| split; [eassumption|]].
{ rewrite !length_app, length_firstn, !length_skipn. cbn [length]. lia. }
pose proof (rw_cells_CB_join asegs _ _ _ _ _ _ PB0 ltac:(replace (buf + Z.of_nat (Z.to_nat bpos)) with (buf + bpos) by lia; exact DST4)) as J1.
match goal with PZ : rw_cells asegs ?mf (buf + bpos + n) [C1 _] |- _ =>
apply (rw_cells_recast asegs _ _ _ [CB 1 [Z_to_bv 8 0]]) in PZ; [| cbn; auto | reflexivity | reflexivity];
pose proof (rw_cells_CB_join asegs _ _ _ _ _ _ J1 ltac:(replace (buf + Z.of_nat (Z.to_nat bpos + Z.to_nat n)) with (buf + bpos + n) by lia; exact PZ)) as J2 end.
pose proof (rw_cells_CB_join asegs _ _ _ _ _ _ J2 ltac:(replace (buf + Z.of_nat (Z.to_nat bpos + Z.to_nat n + 1)) with (buf + bpos + n + 1) by lia; exact PB3)) as J3.
replace (Z.to_nat bpos + Z.to_nat n + 1 + (Z.to_nat cap - Z.to_nat bpos - Z.to_nat n - 1))%nat with (Z.to_nat cap) in J3 by lia.
revert J3. rewrite <- ?app_assoc. intros J3. rewrite <- ?app_assoc in J3. exact J3. }
step.
destruct Hv as [-> | (Hk & Hlast)].
+ if_false. apply STORE.
+ if_truex. step. rewrite (unsigned_lit (buf + bpos + n)) by lia. rewrite land7_mod8 by lia.
step. if_truex. apply STORE.
Qed.
End Tail.
End APbMemappendNF.
End RC__1.
