(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QRjH QHnV QCcH Q0Ek Qwm6 QlKV QpNt QJZd Q6oO Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup.
Import QRjH.
Import QHnV QCcH Q0Ek.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QpNt.Mq4 QJZd.Mq1 QJZd.Mq2 QJZd.Mq3 Q6oO Q6oO.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section C.
Variable HIx : heap_iface_A A4L.
Definition json_object_new_boolean_A := QJZd.Mq1.json_object_new_boolean_A_cps HIx (amemset_A HIx).
Definition json_object_new_int64_A   := QJZd.Mq2.json_object_new_int64_A_cps HIx (amemset_A HIx).
Definition json_object_new_uint64_A  := QJZd.Mq3.json_object_new_uint64_A_cps HIx (amemset_A HIx).
Definition json_object_new_double_A  := Q6oO.json_object_new_double_A_cps HIx (amemset_A HIx).
Definition json_object_new_string_len_A := Q6oO.Mq0.json_object_new_string_len_A_cps HIx (amemset_A HIx) (amemcpy_any_A HIx).
End C.
End RC__1.
End Mq0.
From Stdlib Require Permutation.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply QfLs QjDH QmZZ QTEu Qsw7 QJjn QRUw QKQo Q6WR Q7UD Qhd4 QsKa QW22.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ. Import QTEu. Import Qsw7 QJjn QRUw QKQo.
Import Q6WR Q6WR.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mq7 QlKV.Mqa QsKa.Mq7 QJZd.Mq4 QW22.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section MF2.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud) (lo : Z) (errv : word)
(s : jshape) (BS : list blk) (x rc : Z) (T : TSet).

Lemma mf_strA : forall (h : bool)
(x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x19 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (junk8 : list byte),
s = Sstr h ->
HEAPAx A (BS ++ LB) LM FRS B m md ->
jval asegs A4F s m BS x 0 ->
mf_frameA ra sp s0 s1 s2 s3 m junk8 ->
stk asegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -48 - 16 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> bv_unsigned ra mod 2 = 0 ->
model_vm_only (cfg_model md0) (cfg_model md) -> heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m -> fsaved F F1 -> (frm0 fc -> frm0 fc1) -> rc = 1 ->
bD B0 <= bD B -> bB B0 <= bB B -> 512 * Z.of_nat (length BS) <= bB B ->
KPOSTA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo errv s BS x rc T ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 x) x9 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 A_SB) x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x9ac74) fc1 None m (seg_rom asegs)).
Proof.
intros until junk8. intros Hs HP J FR ST LO LOS SPA HT ERR RA VM0 HPR FS FRM Hrc BD BB0 BB K.
pose proof FR as FR0. unfold mf_frameA in FR. unfold_consts. unfold A_SB, A_TP, A_ERRNO in *. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP) as [HB00 HD00].
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [] m) as MU.
subst s. destruct h.
-
destruct J as (pb & PBS & REST & EBS & OPB & len & pd & pdn & str & junk2 & ER & HL & HS & HPD & HDR & HD). subst REST BS.
cbn [app] in HP.
blk_factsA A4L HIx HP x 56 Hxal Hxlo Hxhi Hximg.
blk_factsA A4L HIx HP pd pdn Hpal Hplo Hphi Hpimg.
assert (Hxpd : x <> pd).
{ intros E. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. cbn in ND. inversion ND as [|y l Hni Hnd]. apply Hni. left. symmetry. exact E. }
shadow_nowA A4L HIx HP x 56 SHx.
a4l. clear HD.
unfold jhdr_cells in HDR. cbn [app] in HDR.
cbn [length app] in BB. rewrite ?Nat2Z.inj_succ in BB.
reenterA asegs A4L HIx asegs_wx HP.
asan_chk0.
step. norm_w32. step. step. if_truex.
step.
asan_chkA.
step.
step. if_falsex.
step.
asan_chkA.
step. step.

clear SHx.
alloc_callA (hiA_free A4L HIx) blk pd uw UWptr A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists pdn. right; left. reflexivity. }
all: try (cbn [uw_pre uw_ok uw_key uw_cost]; intros _; split; [left; lia | unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (destruct (Z.eqb_spec pd 0); cbn [bB bD charge uw_cost] in *; lia).
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. a4l.
rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in HPR3 by lia.
rewrite lb_remove_other in HPR3, HP3 by (cbn; lia). rewrite lb_remove_head in HPR3, HP3.
replace (if pd =? 0 then 0 else uw_cost UWptr) with 0 in HP3 by (destruct (Z.eqb_spec pd 0); reflexivity).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in HDR; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]].
assert (OPB3 : opt_pbuf asegs m3 PBS pb).
{ eapply opt_pbuf_agree; [exact OPB | | apply incl_refl].
eapply (agree_of_heap_pres asegs A4H); [exact HPR3 | reflexivity | intros b Hb; apply in_or_app; left; right; apply in_or_app; left; exact Hb]. }
assert (HPRb : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m3).
{ eapply heap_pres_trans; [exact HPR|].
eapply heap_pres_weaken; [exact HPR3 | lia | intros b Hb; cbn; right; apply in_or_app; apply in_app_or in Hb; destruct Hb; [left; apply in_or_app; right; assumption | right; assumption]]. }
replace (ret_pc (Z_to_bv 64 0x9ad20)) with (Z_to_bv 64 0x9ad20) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
a4l.
eapply (mf_genA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo errv (Sstr true) ((x, 56) :: (pd, pdn) :: PBS) x rc T);
[ exact HP3 | lia | unfold jhdr_cells; cbn [app]; exact HDR | exact OPB3 | unfold mf_frameA; exact FR | exact ST3 | clia | clia | exact SPA | exact HT
| exact ERR3 | exact RA | eapply model_vm_only_trans; [exact VM0 | exact VM3] | exact HPRb | exact FS | exact FRM | exact Hrc
| cbn [bD charge] in *; lia | cbn [bB charge length app] in *; rewrite ?Nat2Z.inj_succ in *; lia | cbn [bB charge length app] in *; rewrite ?Nat2Z.inj_succ in *; lia | exact K ].
-
destruct J as (pb & PBS & REST & EBS & OPB & len & str & junk & ER & HL & HS & HDR). subst REST BS.
cbn [app] in HP.
blk_factsA A4L HIx HP x (str_objsize len) Hxal Hxlo Hxhi Hximg.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ x (str_objsize len) HP ltac:(left; reflexivity)) as SHx. unfold shad in SHx. a4l.
assert (SH : ro_cells asegs m (x / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ rewrite (shadow_bytes_split (str_objsize len) 6) in SHx by (unfold str_objsize; lia).
apply bytes_at_app in SHx as [SH6 _]. split; [cbn; repeat split; exact I | cbn [cells_bytes cbytes app]; exact SH6]. }
clear SHx. unfold str_objsize in *.
pose proof HDR as HDR0. unfold jhdr_cells in HDR. cbn [app] in HDR.
cbn [length app] in BB. rewrite ?Nat2Z.inj_succ in BB.
reenterA asegs A4L HIx asegs_wx HP.
asan_chk0.
step. norm_w32. step. step. if_truex.
step.
asan_chkA.
step.
step. if_truex.
evt_done5.
eapply (mf_genA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo errv (Sstr false) ((x, 49 + Z.max len 8) :: PBS) x rc T);
[ exact HP | lia | exact HDR0 | exact OPB | exact FR0 | exact ST | clia | clia | exact SPA | exact HT
| exact ERR | exact RA | exact VM0 | exact HPR | exact FS | exact FRM | exact Hrc
| exact BD | cbn [length app] in *; rewrite ?Nat2Z.inj_succ in *; lia | cbn [length app] in *; rewrite ?Nat2Z.inj_succ in *; lia | exact K ].
Qed.
End MF2.
End RC__1.
End Mq1.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Monad Fs Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Uapi.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZsi QCKW Q0TL QsRG Qnhz QBxa QsV0 Qn1e QMz4 Q9ox QSpR QWxq_c1 Qe4Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q7UD.
Import QZsi Qhd4.Mq1.
Import QCKW.Mq0 Q0TL.
Import QsRG.Mq0 Qnhz.Mq0 QsRG QBxa.Mq0 QRjH QsV0 Qn1e QMz4 Q9ox.Mq0 QSpR.Mq2.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.
Import Qe4Y.
Import QHnV QCcH QfLs Qsw7 QJjn QRUw.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7 QJZd.Mq8 QpNt.Mq3.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.

Definition A_IGETRANDOM : Z := 0x4f9f0.

Lemma size_test_w : forall n, 0 < n <= 64 -> bv_ltu (Z_to_bv 64 (n + -65)) (Z_to_bv 64 (-64)) = false.
Proof.
intros n Hn. unfold bv_ltu. rewrite !unsigned_lit_wrap.
replace ((-64) mod 2^64) with (2^64 - 64) by reflexivity.
replace ((n + -65) mod 2^64) with (2^64 + n - 65) by (Z.div_mod_to_equations; lia).
apply Z.ltb_ge. lia.
Qed.

Lemma zext32_flag : forall f, 0 <= f < 2^32 ->
Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 f)) 32))) 32) = Z_to_bv 64 f.
Proof.
intros f Hf. rewrite (unsigned_lit f) by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite unsigned_lit by lia.
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.

Section MIgetrandom.
Context {RC__ : Q6q3.RunConsts}.
Variable J : aj_base asegs.
Hypothesis SYSG : forall (F : FPF) (fc : FPC), @aj_getrandom_stmt F fc asegs J.

Definition igetrandom_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (K : TSet)
(buf len lo : Z) (junk : list byte),
CK J c ->
unpoisoned asegs m A_SB buf len -> asan_rt_ok m ->
1 <= len <= 64 -> 0x645000 <= buf -> app_mem buf len -> buf + len <= 2^47 ->
a0 = Z_to_bv 64 buf -> a1 = Z_to_bv 64 len -> (a2 = Z_to_bv 64 0 \/ a2 = Z_to_bv 64 GRND_NONBLOCK) ->
rw_cells asegs m buf [CB (Z.to_nat len) junk] ->
(buf + len <= lo \/ bv_unsigned sp <= buf) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 ->
bv_unsigned sp <= 2^47 -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte) (c' : config) (bs : list byte),
Z.of_nat (length bs) = len ->
munch [(buf, buf + len); (lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) ->
rw_cells asegs m' buf [CB (Z.to_nat len) bs] ->
CNEXT J c c' -> m_fds (cfg_model c') = m_fds (cfg_model c) -> m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJ J K c'
(MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 len) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
AJ J K c (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_IGETRANDOM) fc None m (seg_rom asegs)).

End MIgetrandom.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg Lib.SepCache QgoP Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.
Import QgoP.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7 Qw5U.Mq4 QJZd.Mq8 QsKa.Mq0 QpNt.Mq3.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Ltac rt_cell RT c H :=
pose proof (proj1 (Forall_forall _ _) RT c
ltac:(unfold a4_rt_cells, a4_rt_consts; cbn [app]; repeat (first [left; reflexivity | right]))) as H;
cbn [fst snd] in H.

Lemma lower_word : forall x : byte,
Z_to_bv 64 (bv_unsigned (zxb x) + Z.shiftl (bv_unsigned (v_sltiu (Z_to_bv 64 (bv_unsigned (zxb x) + -65)) 26)) 5)
= Z_to_bv 64 (lower8 (bv_unsigned x)).
Proof.
intros x. pose proof (byte_rng x) as R. unfold zxb. rewrite (unsigned_lit (bv_unsigned x)) by lia.
unfold v_sltiu, lower8. rewrite unsigned_lit_wrap. change (bv_wrap 64 26) with 26.
destruct ((65 <=? bv_unsigned x) && (bv_unsigned x <=? 90))%bool eqn:E.
- apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1, E2.
rewrite Z.mod_small by lia. replace (bv_unsigned x + -65 <? 26) with true by (symmetry; apply Z.ltb_lt; lia).
rewrite (unsigned_lit 1) by lia. reflexivity.
- replace ((bv_unsigned x + -65) mod 2 ^ 64 <? 26) with false.
+ rewrite (unsigned_lit 0) by lia. change (Z.shiftl 0 5) with 0. rewrite Z.add_0_r. reflexivity.
+ symmetry. apply Z.ltb_ge. apply andb_false_iff in E. destruct E as [E|E]; [apply Z.leb_gt in E | apply Z.leb_gt in E].
* replace ((bv_unsigned x + -65) mod 2 ^ 64) with (bv_unsigned x + -65 + 2^64) by (apply Z.mod_unique with (q := -1); lia). lia.
* rewrite Z.mod_small by lia. lia.
Qed.

Lemma lit_eqb : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma istrncasecmp_sound_U : istrncasecmp_spec_U.
Proof.
unfold istrncasecmp_spec_U, istrn_spec_U.
intros until Q. intros MODEL UPA UPB RT Ha Ha47 Hb Hb47 HaLo HbLo Ea0 Ea1 Ea2 Hn STRA STRB ST LO LOS SPA MI RA K.
subst a0 a1 a2. unfold_consts. word_range sp SPR.
rt_cell RT (0xf07d8, [Z_to_bv 8 1]) INITED. apply ro_C1_of_bytes_at in INITED.
rt_cell RT (0xe5da8, le8 (Z_to_bv 64 0x181628)) GOTFL. apply ro_C8_of_bytes_at in GOTFL.
rt_cell RT (0x18171d, [Z_to_bv 8 0]) STRICT. apply ro_C1_of_bytes_at in STRICT.
rt_cell RT (A_GOT_SB, le8 (Z_to_bv 64 A_SB_CELL)) GOT. apply ro_C8_of_bytes_at in GOT.
rt_cell RT (A_SB_CELL, le8 (Z_to_bv 64 A_SB)) CELL. apply ro_C8_of_bytes_at in CELL.
unfold A_GOT_SB, A_SB_CELL, A_SB in GOT, CELL. unfold A_SB_CELL in GOT.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
stash STRA. stash STRB.
unfold A_ISTRNCASECMP. carve_frame 104%nat ST.
step.
do 14 step.
do 6 step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with STc : stk asegs mc lo ?hi |- _ =>
destruct (stk_split asegs mc lo (bv_unsigned sp - 2176) hi STc ltac:(lia)) as [ST1 ST2]; clear STc end end.
eapply try_asan_init_spec; [exact MI | assumption | rewrite unsigned_lit by lia; exact ST1 | rewrite unsigned_lit by lia; lia
| lia | rewrite unsigned_lit by lia; reflexivity |].
rewrite ?unsigned_lit by lia.
intros a1x m2 MU2 WM2 MI2 ST1'.
lazymatch type of MU2 with munch _ ?mc _ =>
transport_after_call asegs mc m2 MU2 WM2; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU2 WM2 end.
replace (ret_pc (Z_to_bv 64 0x50a9c)) with (Z_to_bv 64 0x50a9c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. if_false.
step. if_falsex.
step.

unfold istrncasecmp_model in MODEL.
destruct (icmp_walk_nread _ _ _ _ _ _ _ MODEL) as (Kf & Kl & Kr).
pose proof (icmp_walk_pos _ _ _ _ _ _ _ MODEL ltac:(lia)) as Kpos.
destruct (icmp_walk_last _ _ _ _ _ _ _ MODEL Kpos) as (xa & xb & NA & NB & LAST).
unstash STRA. unstash STRB.
assert (STRA2 : bytes_at asegs m2 a la)
by (eapply bytes_at_transport; [exact STRA | eassumption | cbn [disjoint_from]; lia]).
assert (STRB2 : bytes_at asegs m2 b lb)
by (eapply bytes_at_transport; [exact STRB | eassumption | cbn [disjoint_from]; lia]).
remember (Z.of_nat k - 1) as len eqn:Elen.
assert (Ek : Z.of_nat k = len + 1) by lia.
assert (Hlen : 0 <= len < n) by lia.

assert (POST : forall (idx : Z) (ya yb : byte) (x10 x11 : word),
0 <= idx <= n -> Z.min (idx + 1) n = len + 1 -> v = casecmp_val ya yb ->
evt asegs Q (MS (mkR (Z_to_bv 64 0x50a9c) (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp t0 t1 t2 sp (Z_to_bv 64 n) x10 x11 (Z_to_bv 64 n) a3 a4 a5 a6 a7
(Z_to_bv 64 b) (Z_to_bv 64 a) ra s5 s6 s7 (zxb yb) (zxb ya) s10 (Z_to_bv 64 idx) t3 t4 t5 t6)
F (Z_to_bv 64 0x50aec) fc None m2 (seg_rom asegs))).
2: {
assert (LOOP : forall (Kn : nat) (i : Z) (x10 x11 x24 x25 : word),
Z.to_nat (Z.of_nat k - i) = Kn -> 0 <= i < Z.of_nat k ->
evt asegs Q (MS (mkR (Z_to_bv 64 0x50a9c) (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp t0 t1 t2 sp (Z_to_bv 64 n) x10 x11 (Z_to_bv 64 n) a3 a4 a5 a6 a7
(Z_to_bv 64 b) (Z_to_bv 64 a) ra s5 s6 s7 x24 x25 s10 (Z_to_bv 64 i) t3 t4 t5 t6)
F (Z_to_bv 64 0x50aa8) fc None m2 (seg_rom asegs))).
{ induction Kn as [|Kn IH]; intros i x10 x11 x24 x25 HK Hi; [lia|].
assert (RDS : exists ya yb, nth_error la (Z.to_nat i) = Some ya /\ nth_error lb (Z.to_nat i) = Some yb /\
((i + 1 < Z.of_nat k /\ casecmp_stop ya yb = false) \/ (i + 1 = Z.of_nat k /\ ya = xa /\ yb = xb))).
{ destruct (Z.eq_dec (i + 1) (Z.of_nat k)) as [E|NE].
- exists xa, xb. replace (Z.to_nat i) with (k - 1)%nat by lia. split; [exact NA|]. split; [exact NB|]. right. auto.
- destruct (icmp_walk_before _ _ _ _ _ _ _ (Z.to_nat i) MODEL ltac:(lia)) as (ya & yb & H1 & H2 & H3).
exists ya, yb. split; [exact H1|]. split; [exact H2|]. left. split; [lia | exact H3]. }
destruct RDS as (ya & yb & NYA & NYB & CASE).
pose proof (u8ro_read asegs m2 a la i ya _ STRA2 NYA ltac:(lia) eq_refl) as RD1.
pose proof (u8ro_read asegs m2 b lb i yb _ STRB2 NYB ltac:(lia) eq_refl) as RD2.
pose proof (byte_rng ya) as RYA. pose proof (byte_rng yb) as RYB.
pose proof (lower8_range _ RYA) as LYA. pose proof (lower8_range _ RYB) as LYB.
step. step. step. step.
step. rewrite zxb_eqb0.
destruct CASE as [(Hlt & NS) | (Hlast & -> & ->)].
- unfold casecmp_stop in NS. apply orb_false_iff in NS. destruct NS as (NS1 & NS2). apply negb_false_iff in NS1.
rewrite NS2. cbv iota.
do 8 step. rewrite !lower_word.
step. rewrite lit_eqb by lia. rewrite NS1. cbv [negb]. cbv iota.
step.
step. if_truex.
apply (IH (i + 1)); lia.
- destruct LAST as [(STOP & Ev) | (NSTOP & Hk & Ev)].
+ unfold casecmp_stop in STOP.
destruct (bv_unsigned xa =? 0) eqn:E0; cbv iota.
* apply (POST i xa xb); [lia | lia | exact Ev].
* rewrite orb_false_r in STOP. apply negb_true_iff in STOP.
do 8 step. rewrite !lower_word.
step. rewrite lit_eqb by lia. rewrite STOP. cbv [negb]. cbv iota.
apply (POST i xa xb); [lia | lia | exact Ev].
+ unfold casecmp_stop in NSTOP. apply orb_false_iff in NSTOP. destruct NSTOP as (NS1 & NS2). apply negb_false_iff in NS1.
rewrite NS2. cbv iota.
do 8 step. rewrite !lower_word.
step. rewrite lit_eqb by lia. rewrite NS1. cbv [negb]. cbv iota.
step.
step. if_falsex.
step.
apply (POST n xa xb); [lia | lia |].
rewrite Ev. unfold casecmp_val. apply Z.eqb_eq in NS1. lia. }
apply (LOOP k 0); lia. }
intros idx ya yb x10 x11 Hidx Hmin Ev.
rewrite Ek in *.
assert (UPA2 : unpoisoned asegs m2 A_SB a (len + 1))
by (eapply unpoisoned_transport; [exact UPA | exact MU | intros a' k' Ha' Hk'; eapply (shadow_outside_stack A_SB a (len + 1)); try eassumption; unfold A_SB; lia]).
assert (UPB2 : unpoisoned asegs m2 A_SB b (len + 1))
by (eapply unpoisoned_transport; [exact UPB | exact MU | intros a' k' Ha' Hk'; eapply (shadow_outside_stack A_SB b (len + 1)); try eassumption; unfold A_SB; lia]).
clear UPA UPB.

assert (TAIL : forall (xra q0 q1 q2 w0 w1 y0 y1 y2 y3 y4 y5 y6 y7 w2 w3 w4 w5 w6 w7 w10 w11 q3 q4 q5 q6 : word),
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp q0 q1 q2 w0 w1 y0 y1 y2 y3 y4 y5 y6 y7
w2 w3 w4 w5 w6 w7 (zxb yb) (zxb ya) w10 w11 q3 q4 q5 q6)
F (Z_to_bv 64 0x50c60) fc None m2 (seg_rom asegs))).
{ intros xra q0 q1 q2 w0 w1 y0 y1 y2 y3 y4 y5 y6 y7 w2 w3 w4 w5 w6 w7 w10 w11 q3 q4 q5 q6.
pose proof (byte_rng ya) as RYA. pose proof (byte_rng yb) as RYB.
pose proof (lower8_range _ RYA) as LYA. pose proof (lower8_range _ RYB) as LYB.
do 8 step. rewrite !lower_word.
step. rewrite !unsigned_lit by lia. fold (casecmp_val ya yb). rewrite <- Ev.
do 5 step.
step. step.
step. step.
do 13 step.
step. step.
eapply K; [exact MU | exact WM | exact MI2 | exact STRA2 | exact STRB2 |].
assert (STm : stk asegs m2 lo (bv_unsigned sp + -104)) by (eapply stk_merge; [exact ST1' | exact ST2 | lia]).
release_frame FR STm (bv_unsigned sp). exact STm. }

assert (CHK2 : forall (xra q0 q1 q2 w0 w1 y0 y1 y2 y3 y4 y5 y6 y7 w3 w4 w6 w7 w10 w11 q3 q4 q5 q6 : word),
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp q0 q1 q2 w0 w1 y0 y1 y2 y3 y4 y5 y6 y7
(Z_to_bv 64 b) w3 w4 (Z_to_bv 64 (len + 1)) w6 w7 (zxb yb) (zxb ya) w10 w11 q3 q4 q5 q6)
F (Z_to_bv 64 0x50c18) fc None m2 (seg_rom asegs))).
{ intros xra q0 q1 q2 w0 w1 y0 y1 y2 y3 y4 y5 y6 y7 w3 w4 w6 w7 w10 w11 q3 q4 q5 q6.
step. replace (len + 1 + -65) with (len + -64) by lia.
step.
step. replace (len + -64) with ((len + 1) + -65) by lia. rewrite size_test_n by lia. cbv iota.
assert (Hh : b / 8 <= (b + len) / 8 <= b / 8 + 8) by (Z.div_mod_to_equations; lia).
destruct (unpoisoned_word asegs _ _ _ _ (b / 8 + A_SB) UPB2 ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (v1 & Lv1 & V1c).
destruct (unpoisoned_word asegs _ _ _ _ ((b + len) / 8 + A_SB) UPB2 ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (v2 & Lv2 & V2c).
unfold A_SB in V1c, V2c.
assert (GS0 : forall j, 0 <= j -> b / 8 + j < (b + len) / 8 ->
ov_read_bytes asegs m2 (Z_to_bv 64 (b / 8 + 2147450880 + j)) 1 = Some [Z_to_bv 8 0]).
{ intros j Hj Hjl. apply ov_read1_of_ro.
replace (b / 8 + 2147450880 + j) with ((b / 8 + j) + A_SB) by (unfold A_SB; lia).
apply (unpoisoned_gran0 asegs _ _ _ _ _ UPB2). replace (b + (len + 1) - 1) with (b + len) by lia. lia. }
assert (HRL : exists v, ov_read_bytes asegs m2 (Z_to_bv 64 ((b + len) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 v]
/\ (v = 0 \/ (0 < v < 8 /\ (b + len) mod 8 < v))).
{ destruct (unpoisoned_last asegs _ _ _ _ UPB2) as (v0 & Hro & Hv). replace (b + (len + 1) - 1) with (b + len) in Hro, Hv by lia.
exists v0. split; [| exact Hv]. apply ov_read1_of_ro. unfold A_SB in Hro. exact Hro. }
do 2 step.
step.
step.
step.
step. replace (b + (len + 1) + -1) with (b + len) by lia.
step. do 2 step. do 2 step.
sh_norm.
replace (2147450880 + b / 8) with (b / 8 + 2147450880) by lia.
replace (2147450880 + (b + len) / 8) with ((b + len) / 8 + 2147450880) by lia.
rewrite (unsigned_lit (b / 8 + 2147450880)) by lia. rewrite (unsigned_lit ((b + len) / 8 + 2147450880)) by lia.
rewrite !land_m8_64 by lia.
do 2 step. step.

assert (LOOPG : forall (Kn : nat) (i : Z) (y3' y4' : word),
Z.to_nat ((b + len) / 8 - b / 8 - i) = Kn -> 0 <= i -> b / 8 + i < (b + len) / 8 ->
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp q0 q1 q2 w0 w1 (Z_to_bv 64 (b / 8 + 2147450880 + i)) (Z_to_bv 64 ((b + len) / 8 + 2147450880)) (Z_to_bv 64 0) y3' y4' y5 y6 y7
(Z_to_bv 64 b) w3 w4 (Z_to_bv 64 (len + 1)) w6 w7 (zxb yb) (zxb ya) w10 w11 q3 q4 q5 q6)
F (Z_to_bv 64 0x50edc) fc None m2 (seg_rom asegs))).
{ clear Hh V1c V2c HRL.
induction Kn as [|Kn IH]; intros i y3' y4' HK Hi Hig; [lia|].
pose proof (GS0 i Hi Hig) as HR.
step. rewrite ?zxb_zero. clear HR.
step. step. rewrite ?(unsigned_lit 0) by lia. change (Z.lor 0 0) with 0.
step.
destruct (Z.eq_dec (b / 8 + i + 1) ((b + len) / 8)) as [Heq|Hne].
- if_falsex. step. step. if_true. apply TAIL.
- if_truex. replace (b / 8 + 2147450880 + i + 1) with (b / 8 + 2147450880 + (i + 1)) by lia. apply (IH (i + 1)); lia. }
step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd end.
2: { apply TAIL. }
destruct HRL as (vv & HR & Hv).
assert (Hv8 : 0 <= vv < 128) by (destruct Hv as [->|(? & ?)]; lia).
clear V1c V2c.
step. rewrite (sxb_small vv) by lia. clear HR.
step. rewrite (unsigned_lit (b + len)) by lia. rewrite land7_mod8 by lia.
step. step. step. step.
destruct Hv as [-> | (Hk & Hlast)].
- rewrite (v_sltu_0' (Z_to_bv 64 0) (Z_to_bv 64 0)) by (rewrite !unsigned_lit by lia; lia).
rewrite (unsigned_lit 0) by lia. rewrite Z.land_0_l.
step.
destruct (Z.eq_dec (b / 8) ((b + len) / 8)) as [Heq1|Hne1].
+ if_truex. step. step. if_true. apply TAIL.
+ if_falsex. replace (b / 8 + 2147450880) with (b / 8 + 2147450880 + 0) by lia.
apply (LOOPG (Z.to_nat ((b + len) / 8 - b / 8 - 0)) 0); lia.
- rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 vv)) by (rewrite !unsigned_lit by lia; lia).
rewrite (v_slt_1 (Z_to_bv 64 ((b + len) mod 8)) (Z_to_bv 64 vv)) by (rewrite !signed_lit by lia; clear Hh; Z.div_mod_to_equations; lia).
rewrite !(unsigned_lit 1) by lia. change (Z.lxor 1 1) with 0. rewrite Z.land_0_r.
step.
destruct (Z.eq_dec (b / 8) ((b + len) / 8)) as [Heq1|Hne1].
+ if_truex. step. step. if_true. apply TAIL.
+ if_falsex. replace (b / 8 + 2147450880) with (b / 8 + 2147450880 + 0) by lia.
apply (LOOPG (Z.to_nat ((b + len) / 8 - b / 8 - 0)) 0); lia. }

assert (NEXT1 : forall (xra q0 q1 q2 w0 y0 y1 y2 y3 y4 y5 y6 y7 w4 w5 w6 w7 w10 q3 q4 q5 q6 : word),
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp q0 q1 q2 w0 (Z_to_bv 64 n) y0 y1 y2 y3 y4 y5 y6 y7
(Z_to_bv 64 b) (Z_to_bv 64 a) w4 w5 w6 w7 (zxb yb) (zxb ya) w10 (Z_to_bv 64 idx) q3 q4 q5 q6)
F (Z_to_bv 64 0x50c08) fc None m2 (seg_rom asegs))).
{ intros xra q0 q1 q2 w0 y0 y1 y2 y3 y4 y5 y6 y7 w4 w5 w6 w7 w10 q3 q4 q5 q6.
step.
step.
destruct (Z_lt_ge_dec (idx + 1) n) as [Hlt | Hge].
- if_falsex. replace (idx + 1) with (len + 1) by lia.
step. step. rewrite (unsigned_lit b) by lia. rewrite (lxor_ones64 b) by lia. if_falsex.
apply CHK2.
- if_truex.
step. replace n with (len + 1) at 2 by lia.
step. step. rewrite (unsigned_lit b) by lia. rewrite (lxor_ones64 b) by lia. if_truex.
apply CHK2. }
assert (CHK1 : forall (xra q0 q1 q2 w0 y0 y1 y2 y3 y4 y5 y6 y7 w4 w6 w7 w10 q3 q4 q5 q6 : word),
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp q0 q1 q2 w0 (Z_to_bv 64 n) y0 y1 y2 y3 y4 y5 y6 y7
(Z_to_bv 64 b) (Z_to_bv 64 a) w4 (Z_to_bv 64 (len + 1)) w6 w7 (zxb yb) (zxb ya) w10 (Z_to_bv 64 idx) q3 q4 q5 q6)
F (Z_to_bv 64 0x50bc0) fc None m2 (seg_rom asegs))).
{ intros xra q0 q1 q2 w0 y0 y1 y2 y3 y4 y5 y6 y7 w4 w6 w7 w10 q3 q4 q5 q6.
step. replace (len + 1 + -65) with (len + -64) by lia.
step.
step. replace (len + -64) with ((len + 1) + -65) by lia. rewrite size_test_n by lia. cbv iota.
assert (Hh : a / 8 <= (a + len) / 8 <= a / 8 + 8) by (Z.div_mod_to_equations; lia).
destruct (unpoisoned_word asegs _ _ _ _ (a / 8 + A_SB) UPA2 ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (v1 & Lv1 & V1c).
destruct (unpoisoned_word asegs _ _ _ _ ((a + len) / 8 + A_SB) UPA2 ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (v2 & Lv2 & V2c).
unfold A_SB in V1c, V2c.
assert (GS0 : forall j, 0 <= j -> a / 8 + j < (a + len) / 8 ->
ov_read_bytes asegs m2 (Z_to_bv 64 (a / 8 + 2147450880 + j)) 1 = Some [Z_to_bv 8 0]).
{ intros j Hj Hjl. apply ov_read1_of_ro.
replace (a / 8 + 2147450880 + j) with ((a / 8 + j) + A_SB) by (unfold A_SB; lia).
apply (unpoisoned_gran0 asegs _ _ _ _ _ UPA2). replace (a + (len + 1) - 1) with (a + len) by lia. lia. }
assert (HRL : exists v, ov_read_bytes asegs m2 (Z_to_bv 64 ((a + len) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 v]
/\ (v = 0 \/ (0 < v < 8 /\ (a + len) mod 8 < v))).
{ destruct (unpoisoned_last asegs _ _ _ _ UPA2) as (v0 & Hro & Hv). replace (a + (len + 1) - 1) with (a + len) in Hro, Hv by lia.
exists v0. split; [| exact Hv]. apply ov_read1_of_ro. unfold A_SB in Hro. exact Hro. }
do 2 step.
step.
step.
step.
step. replace (a + (len + 1) + -1) with (a + len) by lia.
step. do 2 step. do 2 step.
sh_norm.
replace (2147450880 + a / 8) with (a / 8 + 2147450880) by lia.
replace (2147450880 + (a + len) / 8) with ((a + len) / 8 + 2147450880) by lia.
rewrite (unsigned_lit (a / 8 + 2147450880)) by lia. rewrite (unsigned_lit ((a + len) / 8 + 2147450880)) by lia.
rewrite !land_m8_64 by lia.
do 2 step. step.

assert (LOOPG : forall (Kn : nat) (i : Z) (y3' y4' : word),
Z.to_nat ((a + len) / 8 - a / 8 - i) = Kn -> 0 <= i -> a / 8 + i < (a + len) / 8 ->
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp q0 q1 q2 w0 (Z_to_bv 64 n) (Z_to_bv 64 (a / 8 + 2147450880 + i)) (Z_to_bv 64 ((a + len) / 8 + 2147450880)) (Z_to_bv 64 0) y3' y4' y5 y6 y7
(Z_to_bv 64 b) (Z_to_bv 64 a) w4 (Z_to_bv 64 (len + 1)) w6 w7 (zxb yb) (zxb ya) w10 (Z_to_bv 64 idx) q3 q4 q5 q6)
F (Z_to_bv 64 0x50e14) fc None m2 (seg_rom asegs))).
{ clear Hh V1c V2c HRL.
induction Kn as [|Kn IH]; intros i y3' y4' HK Hi Hig; [lia|].
pose proof (GS0 i Hi Hig) as HR.
step. rewrite ?zxb_zero. clear HR.
step. step. rewrite ?(unsigned_lit 0) by lia. change (Z.lor 0 0) with 0.
step.
destruct (Z.eq_dec (a / 8 + i + 1) ((a + len) / 8)) as [Heq|Hne].
- if_falsex. step. step. if_true. apply NEXT1.
- if_truex. replace (a / 8 + 2147450880 + i + 1) with (a / 8 + 2147450880 + (i + 1)) by lia. apply (IH (i + 1)); lia. }
step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd end.
2: { apply NEXT1. }
destruct HRL as (vv & HR & Hv).
assert (Hv8 : 0 <= vv < 128) by (destruct Hv as [->|(? & ?)]; lia).
clear V1c V2c.
step. rewrite (sxb_small vv) by lia. clear HR.
step. rewrite (unsigned_lit (a + len)) by lia. rewrite land7_mod8 by lia.
step. step. step. step.
destruct Hv as [-> | (Hk & Hlast)].
- rewrite (v_sltu_0' (Z_to_bv 64 0) (Z_to_bv 64 0)) by (rewrite !unsigned_lit by lia; lia).
rewrite (unsigned_lit 0) by lia. rewrite Z.land_0_l.
step.
destruct (Z.eq_dec (a / 8) ((a + len) / 8)) as [Heq1|Hne1].
+ if_truex. step. step. if_true. apply NEXT1.
+ if_falsex. replace (a / 8 + 2147450880) with (a / 8 + 2147450880 + 0) by lia.
apply (LOOPG (Z.to_nat ((a + len) / 8 - a / 8 - 0)) 0); lia.
- rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 vv)) by (rewrite !unsigned_lit by lia; lia).
rewrite (v_slt_1 (Z_to_bv 64 ((a + len) mod 8)) (Z_to_bv 64 vv)) by (rewrite !signed_lit by lia; clear Hh; Z.div_mod_to_equations; lia).
rewrite !(unsigned_lit 1) by lia. change (Z.lxor 1 1) with 0. rewrite Z.land_0_r.
step.
destruct (Z.eq_dec (a / 8) ((a + len) / 8)) as [Heq1|Hne1].
+ if_truex. step. step. if_true. apply NEXT1.
+ if_falsex. replace (a / 8 + 2147450880) with (a / 8 + 2147450880 + 0) by lia.
apply (LOOPG (Z.to_nat ((a + len) / 8 - a / 8 - 0)) 0); lia. }

step.
destruct (Z_lt_ge_dec idx n) as [Hlt | Hge].
-
if_falsex.
do 2 step.
step. rewrite ?zxb_zero.
step.
step. change (Z.land (bv_unsigned (Z_to_bv 64 0)) 1) with 0.
step. if_true.
step.
step.
destruct (Z_lt_ge_dec (idx + 1) n) as [Hlt1 | Hge1].
+ if_falsex. replace (idx + 1) with (len + 1) by lia.
step. step. step.
step. rewrite (unsigned_lit a) by lia. rewrite (lxor_ones64 a) by lia. if_falsex.
apply CHK1.
+ if_truex.
step. replace n with (len + 1) at 2 by lia.
step. step. step.
step. rewrite (unsigned_lit a) by lia. rewrite (lxor_ones64 a) by lia. if_truex.
apply CHK1.
-
if_truex.
step.
step. if_falsex.
step. replace n with (len + 1) at 2 by lia.
step. step. step.
step. rewrite (unsigned_lit a) by lia. rewrite (lxor_ones64 a) by lia. if_truex.
apply CHK1.
Qed.
End RC__1.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.
Import QgoP.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7 Qw5U.Mq4 QJZd.Mq8 QsKa.Mq0 QpNt.Mq3.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Ltac rt_cell RT c H :=
pose proof (proj1 (Forall_forall _ _) RT c
ltac:(unfold a4_rt_cells, a4_rt_consts; cbn [app]; repeat (first [left; reflexivity | right]))) as H;
cbn [fst snd] in H.

Lemma istrncmp_sound_U : istrncmp_spec_U.
Proof.
unfold istrncmp_spec_U, istrn_spec_U.
intros until Q. intros MODEL UPA UPB RT Ha Ha47 Hb Hb47 HaLo HbLo Ea0 Ea1 Ea2 Hn STRA STRB ST LO LOS SPA MI RA K.
subst a0 a1 a2. unfold_consts. word_range sp SPR.
rt_cell RT (0xf07d8, [Z_to_bv 8 1]) INITED. apply ro_C1_of_bytes_at in INITED.
rt_cell RT (0xe5da8, le8 (Z_to_bv 64 0x181628)) GOTFL. apply ro_C8_of_bytes_at in GOTFL.
rt_cell RT (0x18171d, [Z_to_bv 8 0]) STRICT. apply ro_C1_of_bytes_at in STRICT.
rt_cell RT (A_GOT_SB, le8 (Z_to_bv 64 A_SB_CELL)) GOT. apply ro_C8_of_bytes_at in GOT.
rt_cell RT (A_SB_CELL, le8 (Z_to_bv 64 A_SB)) CELL. apply ro_C8_of_bytes_at in CELL.
unfold A_GOT_SB, A_SB_CELL, A_SB in GOT, CELL. unfold A_SB_CELL in GOT.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
stash STRA. stash STRB.
unfold A_ISTRNCMP. carve_frame 104%nat ST.
step.
do 14 step.
do 6 step.
step.
apply asan_inited_spec; [exact MI | assumption |].
replace (ret_pc (Z_to_bv 64 0x504c0)) with (Z_to_bv 64 0x504c0) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. if_false.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with STc : stk asegs mc lo ?hi |- _ =>
destruct (stk_split asegs mc lo (bv_unsigned sp - 2176) hi STc ltac:(lia)) as [ST1 ST2]; clear STc end end.
eapply try_asan_init_spec; [exact MI | assumption | rewrite unsigned_lit by lia; exact ST1 | rewrite unsigned_lit by lia; lia
| lia | rewrite unsigned_lit by lia; reflexivity |].
rewrite ?unsigned_lit by lia.
intros a1x m2 MU2 WM2 MI2 ST1'.
lazymatch type of MU2 with munch _ ?mc _ =>
transport_after_call asegs mc m2 MU2 WM2; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU2 WM2 end.
replace (ret_pc (Z_to_bv 64 0x504c8)) with (Z_to_bv 64 0x504c8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. if_false.
step. if_falsex.
step.

unfold istrncmp_model in MODEL.
destruct (icmp_walk_nread _ _ _ _ _ _ _ MODEL) as (Kf & Kl & Kr).
pose proof (icmp_walk_pos _ _ _ _ _ _ _ MODEL ltac:(lia)) as Kpos.
destruct (icmp_walk_last _ _ _ _ _ _ _ MODEL Kpos) as (xa & xb & NA & NB & LAST).
unstash STRA. unstash STRB.
assert (STRA2 : bytes_at asegs m2 a la)
by (eapply bytes_at_transport; [exact STRA | eassumption | cbn [disjoint_from]; lia]).
assert (STRB2 : bytes_at asegs m2 b lb)
by (eapply bytes_at_transport; [exact STRB | eassumption | cbn [disjoint_from]; lia]).
remember (Z.of_nat k - 1) as len eqn:Elen.
assert (Ek : Z.of_nat k = len + 1) by lia.
assert (Hlen : 0 <= len < n) by lia.

assert (POST : forall (idx : Z) (ya yb : byte) (x10 : word),
0 <= idx <= n -> Z.min (idx + 1) n = len + 1 -> v = cmp_sign ya yb ->
evt asegs Q (MS (mkR (Z_to_bv 64 0x504c8) (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp t0 t1 t2 sp (Z_to_bv 64 n) x10 a1x (Z_to_bv 64 n) a3 a4 a5 a6 a7
(Z_to_bv 64 b) (Z_to_bv 64 a) ra s5 s6 s7 (zxb ya) (zxb yb) s10 (Z_to_bv 64 idx) t3 t4 t5 t6)
F (Z_to_bv 64 0x504fc) fc None m2 (seg_rom asegs))).
2: {
assert (LOOP : forall (Kn : nat) (i : Z) (x10 x24 x25 : word),
Z.to_nat (Z.of_nat k - i) = Kn -> 0 <= i < Z.of_nat k ->
evt asegs Q (MS (mkR (Z_to_bv 64 0x504c8) (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp t0 t1 t2 sp (Z_to_bv 64 n) x10 a1x (Z_to_bv 64 n) a3 a4 a5 a6 a7
(Z_to_bv 64 b) (Z_to_bv 64 a) ra s5 s6 s7 x24 x25 s10 (Z_to_bv 64 i) t3 t4 t5 t6)
F (Z_to_bv 64 0x504d4) fc None m2 (seg_rom asegs))).
{ induction Kn as [|Kn IH]; intros i x10 x24 x25 HK Hi; [lia|].
assert (RDS : exists ya yb, nth_error la (Z.to_nat i) = Some ya /\ nth_error lb (Z.to_nat i) = Some yb /\
((i + 1 < Z.of_nat k /\ cmp_stop ya yb = false) \/ (i + 1 = Z.of_nat k /\ ya = xa /\ yb = xb))).
{ destruct (Z.eq_dec (i + 1) (Z.of_nat k)) as [E|NE].
- exists xa, xb. replace (Z.to_nat i) with (k - 1)%nat by lia. split; [exact NA|]. split; [exact NB|]. right. auto.
- destruct (icmp_walk_before _ _ _ _ _ _ _ (Z.to_nat i) MODEL ltac:(lia)) as (ya & yb & H1 & H2 & H3).
exists ya, yb. split; [exact H1|]. split; [exact H2|]. left. split; [lia | exact H3]. }
destruct RDS as (ya & yb & NYA & NYB & CASE).
pose proof (u8ro_read asegs m2 a la i ya _ STRA2 NYA ltac:(lia) eq_refl) as RD1.
pose proof (u8ro_read asegs m2 b lb i yb _ STRB2 NYB ltac:(lia) eq_refl) as RD2.
step. step. step. step.
step. rewrite zxb_eqb0.
destruct CASE as [(Hlt & NS) | (Hlast & -> & ->)].
- unfold cmp_stop in NS. apply orb_false_iff in NS. destruct NS as (NS1 & NS2). apply negb_false_iff in NS1.
rewrite NS2. cbv iota.
step. rewrite zxb_eqb, NS1. cbv [negb]. cbv iota.
step.
step. if_truex.
apply (IH (i + 1)); lia.
- destruct LAST as [(STOP & Ev) | (NSTOP & Hk & Ev)].
+ unfold cmp_stop in STOP.
destruct (bv_unsigned xa =? 0) eqn:E0; cbv iota.
* apply (POST i xa xb); [lia | lia | exact Ev].
* rewrite orb_false_r in STOP. apply negb_true_iff in STOP.
step. rewrite zxb_eqb, STOP. cbv [negb]. cbv iota.
apply (POST i xa xb); [lia | lia | exact Ev].
+ unfold cmp_stop in NSTOP. apply orb_false_iff in NSTOP. destruct NSTOP as (NS1 & NS2). apply negb_false_iff in NS1.
rewrite NS2. cbv iota.
step. rewrite zxb_eqb, NS1. cbv [negb]. cbv iota.
step.
step. if_falsex.
step. step.
apply (POST n xa xa); [lia | lia |].
rewrite Ev. unfold cmp_sign. rewrite Z.sub_diag. reflexivity. }
apply (LOOP k 0); lia. }
intros idx ya yb x10 Hidx Hmin Ev.
rewrite Ek in *.
assert (UPA2 : unpoisoned asegs m2 A_SB a (len + 1))
by (eapply unpoisoned_transport; [exact UPA | exact MU | intros a' k' Ha' Hk'; eapply (shadow_outside_stack A_SB a (len + 1)); try eassumption; unfold A_SB; lia]).
assert (UPB2 : unpoisoned asegs m2 A_SB b (len + 1))
by (eapply unpoisoned_transport; [exact UPB | exact MU | intros a' k' Ha' Hk'; eapply (shadow_outside_stack A_SB b (len + 1)); try eassumption; unfold A_SB; lia]).
clear UPA UPB.

assert (TAIL : forall (xra q0 q1 q2 w0 w1 y0 y1 y2 y3 y4 y5 y6 y7 w2 w3 w4 w5 w6 w7 w10 w11 q3 q4 q5 q6 : word),
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp q0 q1 q2 w0 w1 y0 y1 y2 y3 y4 y5 y6 y7
w2 w3 w4 w5 w6 w7 (zxb ya) (zxb yb) w10 w11 q3 q4 q5 q6)
F (Z_to_bv 64 0x506bc) fc None m2 (seg_rom asegs))).
{ intros xra q0 q1 q2 w0 w1 y0 y1 y2 y3 y4 y5 y6 y7 w2 w3 w4 w5 w6 w7 w10 w11 q3 q4 q5 q6.
step. step. step. rewrite sltu_sign, <- Ev.
do 5 step.
step. step.
step. step.
do 13 step.
step. step.
eapply K; [exact MU | exact WM | exact MI2 | exact STRA2 | exact STRB2 |].
assert (STm : stk asegs m2 lo (bv_unsigned sp + -104)) by (eapply stk_merge; [exact ST1' | exact ST2 | lia]).
release_frame FR STm (bv_unsigned sp). exact STm. }

assert (CHK2 : forall (xra q0 q1 q2 w0 w1 y0 y1 y2 y3 y4 y5 y6 y7 w3 w4 w6 w7 w10 w11 q3 q4 q5 q6 : word),
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp q0 q1 q2 w0 w1 y0 y1 y2 y3 y4 y5 y6 y7
(Z_to_bv 64 b) w3 w4 (Z_to_bv 64 (len + 1)) w6 w7 (zxb ya) (zxb yb) w10 w11 q3 q4 q5 q6)
F (Z_to_bv 64 0x50674) fc None m2 (seg_rom asegs))).
{ intros xra q0 q1 q2 w0 w1 y0 y1 y2 y3 y4 y5 y6 y7 w3 w4 w6 w7 w10 w11 q3 q4 q5 q6.
step. replace (len + 1 + -65) with (len + -64) by lia.
step.
step. replace (len + -64) with ((len + 1) + -65) by lia. rewrite size_test_n by lia. cbv iota.
assert (Hh : b / 8 <= (b + len) / 8 <= b / 8 + 8) by (Z.div_mod_to_equations; lia).
destruct (unpoisoned_word asegs _ _ _ _ (b / 8 + A_SB) UPB2 ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (v1 & Lv1 & V1c).
destruct (unpoisoned_word asegs _ _ _ _ ((b + len) / 8 + A_SB) UPB2 ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (v2 & Lv2 & V2c).
unfold A_SB in V1c, V2c.
assert (GS0 : forall j, 0 <= j -> b / 8 + j < (b + len) / 8 ->
ov_read_bytes asegs m2 (Z_to_bv 64 (b / 8 + 2147450880 + j)) 1 = Some [Z_to_bv 8 0]).
{ intros j Hj Hjl. apply ov_read1_of_ro.
replace (b / 8 + 2147450880 + j) with ((b / 8 + j) + A_SB) by (unfold A_SB; lia).
apply (unpoisoned_gran0 asegs _ _ _ _ _ UPB2). replace (b + (len + 1) - 1) with (b + len) by lia. lia. }
assert (HRL : exists v, ov_read_bytes asegs m2 (Z_to_bv 64 ((b + len) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 v]
/\ (v = 0 \/ (0 < v < 8 /\ (b + len) mod 8 < v))).
{ destruct (unpoisoned_last asegs _ _ _ _ UPB2) as (v0 & Hro & Hv). replace (b + (len + 1) - 1) with (b + len) in Hro, Hv by lia.
exists v0. split; [| exact Hv]. apply ov_read1_of_ro. unfold A_SB in Hro. exact Hro. }
do 2 step.
step.
step.
step.
step. replace (b + (len + 1) + -1) with (b + len) by lia.
step. do 2 step. do 2 step.
sh_norm.
replace (2147450880 + b / 8) with (b / 8 + 2147450880) by lia.
replace (2147450880 + (b + len) / 8) with ((b + len) / 8 + 2147450880) by lia.
rewrite (unsigned_lit (b / 8 + 2147450880)) by lia. rewrite (unsigned_lit ((b + len) / 8 + 2147450880)) by lia.
rewrite !land_m8_64 by lia.
do 2 step. step.

assert (LOOPG : forall (Kn : nat) (i : Z) (y3' y4' : word),
Z.to_nat ((b + len) / 8 - b / 8 - i) = Kn -> 0 <= i -> b / 8 + i < (b + len) / 8 ->
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp q0 q1 q2 w0 w1 (Z_to_bv 64 (b / 8 + 2147450880 + i)) (Z_to_bv 64 ((b + len) / 8 + 2147450880)) (Z_to_bv 64 0) y3' y4' y5 y6 y7
(Z_to_bv 64 b) w3 w4 (Z_to_bv 64 (len + 1)) w6 w7 (zxb ya) (zxb yb) w10 w11 q3 q4 q5 q6)
F (Z_to_bv 64 0x50920) fc None m2 (seg_rom asegs))).
{ clear Hh V1c V2c HRL.
induction Kn as [|Kn IH]; intros i y3' y4' HK Hi Hig; [lia|].
pose proof (GS0 i Hi Hig) as HR.
step. rewrite ?zxb_zero. clear HR.
step. step. rewrite ?(unsigned_lit 0) by lia. change (Z.lor 0 0) with 0.
step.
destruct (Z.eq_dec (b / 8 + i + 1) ((b + len) / 8)) as [Heq|Hne].
- if_falsex. step. step. if_true. apply TAIL.
- if_truex. replace (b / 8 + 2147450880 + i + 1) with (b / 8 + 2147450880 + (i + 1)) by lia. apply (IH (i + 1)); lia. }
step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd end.
2: { apply TAIL. }
destruct HRL as (vv & HR & Hv).
assert (Hv8 : 0 <= vv < 128) by (destruct Hv as [->|(? & ?)]; lia).
clear V1c V2c.
step. rewrite (sxb_small vv) by lia. clear HR.
step. rewrite (unsigned_lit (b + len)) by lia. rewrite land7_mod8 by lia.
step. step. step. step.
destruct Hv as [-> | (Hk & Hlast)].
- rewrite (v_sltu_0' (Z_to_bv 64 0) (Z_to_bv 64 0)) by (rewrite !unsigned_lit by lia; lia).
rewrite (unsigned_lit 0) by lia. rewrite Z.land_0_l.
step.
destruct (Z.eq_dec (b / 8) ((b + len) / 8)) as [Heq1|Hne1].
+ if_truex. step. step. if_true. apply TAIL.
+ if_falsex. replace (b / 8 + 2147450880) with (b / 8 + 2147450880 + 0) by lia.
apply (LOOPG (Z.to_nat ((b + len) / 8 - b / 8 - 0)) 0); lia.
- rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 vv)) by (rewrite !unsigned_lit by lia; lia).
rewrite (v_slt_1 (Z_to_bv 64 ((b + len) mod 8)) (Z_to_bv 64 vv)) by (rewrite !signed_lit by lia; clear Hh; Z.div_mod_to_equations; lia).
rewrite !(unsigned_lit 1) by lia. change (Z.lxor 1 1) with 0. rewrite Z.land_0_r.
step.
destruct (Z.eq_dec (b / 8) ((b + len) / 8)) as [Heq1|Hne1].
+ if_truex. step. step. if_true. apply TAIL.
+ if_falsex. replace (b / 8 + 2147450880) with (b / 8 + 2147450880 + 0) by lia.
apply (LOOPG (Z.to_nat ((b + len) / 8 - b / 8 - 0)) 0); lia. }

assert (NEXT1 : forall (xra q0 q1 q2 w0 y0 y1 y2 y3 y4 y5 y6 y7 w4 w5 w6 w7 w10 q3 q4 q5 q6 : word),
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp q0 q1 q2 w0 (Z_to_bv 64 n) y0 y1 y2 y3 y4 y5 y6 y7
(Z_to_bv 64 b) (Z_to_bv 64 a) w4 w5 w6 w7 (zxb ya) (zxb yb) w10 (Z_to_bv 64 idx) q3 q4 q5 q6)
F (Z_to_bv 64 0x50664) fc None m2 (seg_rom asegs))).
{ intros xra q0 q1 q2 w0 y0 y1 y2 y3 y4 y5 y6 y7 w4 w5 w6 w7 w10 q3 q4 q5 q6.
step.
step.
destruct (Z_lt_ge_dec (idx + 1) n) as [Hlt | Hge].
- if_falsex. replace (idx + 1) with (len + 1) by lia.
step. step. rewrite (unsigned_lit b) by lia. rewrite (lxor_ones64 b) by lia. if_falsex.
apply CHK2.
- if_truex.
step. replace n with (len + 1) at 2 by lia.
step. step. rewrite (unsigned_lit b) by lia. rewrite (lxor_ones64 b) by lia. if_truex.
apply CHK2. }
assert (CHK1 : forall (xra q0 q1 q2 w0 y0 y1 y2 y3 y4 y5 y6 y7 w4 w6 w7 w10 q3 q4 q5 q6 : word),
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp q0 q1 q2 w0 (Z_to_bv 64 n) y0 y1 y2 y3 y4 y5 y6 y7
(Z_to_bv 64 b) (Z_to_bv 64 a) w4 (Z_to_bv 64 (len + 1)) w6 w7 (zxb ya) (zxb yb) w10 (Z_to_bv 64 idx) q3 q4 q5 q6)
F (Z_to_bv 64 0x5061c) fc None m2 (seg_rom asegs))).
{ intros xra q0 q1 q2 w0 y0 y1 y2 y3 y4 y5 y6 y7 w4 w6 w7 w10 q3 q4 q5 q6.
step. replace (len + 1 + -65) with (len + -64) by lia.
step.
step. replace (len + -64) with ((len + 1) + -65) by lia. rewrite size_test_n by lia. cbv iota.
assert (Hh : a / 8 <= (a + len) / 8 <= a / 8 + 8) by (Z.div_mod_to_equations; lia).
destruct (unpoisoned_word asegs _ _ _ _ (a / 8 + A_SB) UPA2 ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (v1 & Lv1 & V1c).
destruct (unpoisoned_word asegs _ _ _ _ ((a + len) / 8 + A_SB) UPA2 ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (v2 & Lv2 & V2c).
unfold A_SB in V1c, V2c.
assert (GS0 : forall j, 0 <= j -> a / 8 + j < (a + len) / 8 ->
ov_read_bytes asegs m2 (Z_to_bv 64 (a / 8 + 2147450880 + j)) 1 = Some [Z_to_bv 8 0]).
{ intros j Hj Hjl. apply ov_read1_of_ro.
replace (a / 8 + 2147450880 + j) with ((a / 8 + j) + A_SB) by (unfold A_SB; lia).
apply (unpoisoned_gran0 asegs _ _ _ _ _ UPA2). replace (a + (len + 1) - 1) with (a + len) by lia. lia. }
assert (HRL : exists v, ov_read_bytes asegs m2 (Z_to_bv 64 ((a + len) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 v]
/\ (v = 0 \/ (0 < v < 8 /\ (a + len) mod 8 < v))).
{ destruct (unpoisoned_last asegs _ _ _ _ UPA2) as (v0 & Hro & Hv). replace (a + (len + 1) - 1) with (a + len) in Hro, Hv by lia.
exists v0. split; [| exact Hv]. apply ov_read1_of_ro. unfold A_SB in Hro. exact Hro. }
do 2 step.
step.
step.
step.
step. replace (a + (len + 1) + -1) with (a + len) by lia.
step. do 2 step. do 2 step.
sh_norm.
replace (2147450880 + a / 8) with (a / 8 + 2147450880) by lia.
replace (2147450880 + (a + len) / 8) with ((a + len) / 8 + 2147450880) by lia.
rewrite (unsigned_lit (a / 8 + 2147450880)) by lia. rewrite (unsigned_lit ((a + len) / 8 + 2147450880)) by lia.
rewrite !land_m8_64 by lia.
do 2 step. step.

assert (LOOPG : forall (Kn : nat) (i : Z) (y3' y4' : word),
Z.to_nat ((a + len) / 8 - a / 8 - i) = Kn -> 0 <= i -> a / 8 + i < (a + len) / 8 ->
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp q0 q1 q2 w0 (Z_to_bv 64 n) (Z_to_bv 64 (a / 8 + 2147450880 + i)) (Z_to_bv 64 ((a + len) / 8 + 2147450880)) (Z_to_bv 64 0) y3' y4' y5 y6 y7
(Z_to_bv 64 b) (Z_to_bv 64 a) w4 (Z_to_bv 64 (len + 1)) w6 w7 (zxb ya) (zxb yb) w10 (Z_to_bv 64 idx) q3 q4 q5 q6)
F (Z_to_bv 64 0x50858) fc None m2 (seg_rom asegs))).
{ clear Hh V1c V2c HRL.
induction Kn as [|Kn IH]; intros i y3' y4' HK Hi Hig; [lia|].
pose proof (GS0 i Hi Hig) as HR.
step. rewrite ?zxb_zero. clear HR.
step. step. rewrite ?(unsigned_lit 0) by lia. change (Z.lor 0 0) with 0.
step.
destruct (Z.eq_dec (a / 8 + i + 1) ((a + len) / 8)) as [Heq|Hne].
- if_falsex. step. step. if_true. apply NEXT1.
- if_truex. replace (a / 8 + 2147450880 + i + 1) with (a / 8 + 2147450880 + (i + 1)) by lia. apply (IH (i + 1)); lia. }
step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd end.
2: { apply NEXT1. }
destruct HRL as (vv & HR & Hv).
assert (Hv8 : 0 <= vv < 128) by (destruct Hv as [->|(? & ?)]; lia).
clear V1c V2c.
step. rewrite (sxb_small vv) by lia. clear HR.
step. rewrite (unsigned_lit (a + len)) by lia. rewrite land7_mod8 by lia.
step. step. step. step.
destruct Hv as [-> | (Hk & Hlast)].
- rewrite (v_sltu_0' (Z_to_bv 64 0) (Z_to_bv 64 0)) by (rewrite !unsigned_lit by lia; lia).
rewrite (unsigned_lit 0) by lia. rewrite Z.land_0_l.
step.
destruct (Z.eq_dec (a / 8) ((a + len) / 8)) as [Heq1|Hne1].
+ if_truex. step. step. if_true. apply NEXT1.
+ if_falsex. replace (a / 8 + 2147450880) with (a / 8 + 2147450880 + 0) by lia.
apply (LOOPG (Z.to_nat ((a + len) / 8 - a / 8 - 0)) 0); lia.
- rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 vv)) by (rewrite !unsigned_lit by lia; lia).
rewrite (v_slt_1 (Z_to_bv 64 ((a + len) mod 8)) (Z_to_bv 64 vv)) by (rewrite !signed_lit by lia; clear Hh; Z.div_mod_to_equations; lia).
rewrite !(unsigned_lit 1) by lia. change (Z.lxor 1 1) with 0. rewrite Z.land_0_r.
step.
destruct (Z.eq_dec (a / 8) ((a + len) / 8)) as [Heq1|Hne1].
+ if_truex. step. step. if_true. apply NEXT1.
+ if_falsex. replace (a / 8 + 2147450880) with (a / 8 + 2147450880 + 0) by lia.
apply (LOOPG (Z.to_nat ((a + len) / 8 - a / 8 - 0)) 0); lia. }

step.
destruct (Z_lt_ge_dec idx n) as [Hlt | Hge].
-
if_falsex.
do 2 step.
step. rewrite ?zxb_zero.
step.
step. change (Z.land (bv_unsigned (Z_to_bv 64 0)) 1) with 0.
step. if_true.
step.
step.
destruct (Z_lt_ge_dec (idx + 1) n) as [Hlt1 | Hge1].
+ if_falsex. replace (idx + 1) with (len + 1) by lia.
step. step. step.
step. rewrite (unsigned_lit a) by lia. rewrite (lxor_ones64 a) by lia. if_falsex.
apply CHK1.
+ if_truex.
step. replace n with (len + 1) at 2 by lia.
step. step. step.
step. rewrite (unsigned_lit a) by lia. rewrite (lxor_ones64 a) by lia. if_truex.
apply CHK1.
-
if_truex.
step.
step. if_falsex.
step. replace n with (len + 1) at 2 by lia.
step. step. step.
step. rewrite (unsigned_lit a) by lia. rewrite (lxor_ones64 a) by lia. if_truex.
apply CHK1.
Qed.
End RC__1.
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup.
Import QRjH.
Import QHnV QCcH Q0Ek.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QpNt.Mq8 QJZd.Mqa QJZd.Mqb QJZd.Mqc Q6oO.Mq1 Q6oO.Mq2. Import QRBl.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section C.
Variable HIx : heap_iface_A A4L.
Definition json_object_new_boolean_A := QJZd.Mqa.json_object_new_boolean_A_cps HIx (amemset_A HIx).
Definition json_object_new_int64_A   := QJZd.Mqb.json_object_new_int64_A_cps HIx (amemset_A HIx).
Definition json_object_new_uint64_A  := QJZd.Mqc.json_object_new_uint64_A_cps HIx (amemset_A HIx).
Definition json_object_new_double_A  := Q6oO.Mq1.json_object_new_double_A_cps HIx (amemset_A HIx).
Definition json_object_new_string_len_A := Q6oO.Mq2.json_object_new_string_len_A_cps HIx (amemset_A HIx) (amemcpy_any_A HIx).
End C.
End RC__1.
End Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ. Import QTEu. Import Qsw7 QJjn QRUw QKQo.
Import Q6WR Q6WR.Mq0.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqh QlKV.Mqj QsKa.Mqg QJZd.Mqd QW22.Mq6.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section MF2.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud) (lo : Z) (errv : word)
(s : jshape) (BS : list blk) (x rc : Z) (T : TSet).

Lemma mf_strA : forall (h : bool)
(x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x20 x21 x22 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud),
s = Sstr h ->
HEAPAx A (BS ++ LB) LM FRS B m md ->
jval asegs A4F s m BS x 0 ->
mf_frameA ra sp s0 s1 s2 s3 s4 s5 s6 m ->
stk asegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -64 - 16 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> bv_unsigned ra mod 2 = 0 ->
model_vm_only (cfg_model md0) (cfg_model md) -> heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m -> fsaved F F1 -> (frm0 fc -> frm0 fc1) -> rc = 1 ->
bD B0 <= bD B -> bB B0 <= bB B -> 512 * Z.of_nat (length BS) <= bB B ->
KPOSTA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo errv s BS x rc T ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 x) x9 a0 a1 a2 a3 a4 a5 a6 a7
x18 (Z_to_bv 64 A_SB) x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x9c30c) fc1 None m (seg_rom asegs)).
Proof.
intros until B. intros Hs HP J FR ST LO LOS SPA HT ERR RA VM0 HPR FS FRM Hrc BD BB0 BB K.
pose proof FR as FR0. unfold mf_frameA in FR. unfold_consts. unfold A_SB, A_TP, A_ERRNO in *. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP) as [HB00 HD00].
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [] m) as MU.
subst s. destruct h.
-
destruct J as (pb & PBS & REST & EBS & OPB & len & pd & pdn & str & junk2 & ER & HL & HS & HPD & HDR & HD). subst REST BS.
cbn [app] in HP.
blk_factsA A4L HIx HP x 56 Hxal Hxlo Hxhi Hximg.
blk_factsA A4L HIx HP pd pdn Hpal Hplo Hphi Hpimg.
assert (Hxpd : x <> pd).
{ intros E. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. cbn in ND. inversion ND as [|y l Hni Hnd]. apply Hni. left. symmetry. exact E. }
shadow_nowA A4L HIx HP x 56 SHx.
a4l. clear HD.
unfold jhdr_cells in HDR. cbn [app] in HDR.
cbn [length app] in BB. rewrite ?Nat2Z.inj_succ in BB.
reenterA asegs A4L HIx asegs_wx HP.
asan_chk0.
bstep. norm_w32. bstep. bstep. if_truex.
bstep.
asan_chkA.
bstep.
bstep. if_falsex.
bstep.
asan_chkA.
bstep. bstep.

clear SHx.
alloc_callA (hiA_free A4L HIx) blk pd uw UWptr A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists pdn. right; left. reflexivity. }
all: try (cbn [uw_pre uw_ok uw_key uw_cost]; intros _; split; [left; lia | unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (destruct (Z.eqb_spec pd 0); cbn [bB bD charge uw_cost] in *; lia).
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. a4l.
rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in HPR3 by lia.
rewrite lb_remove_other in HPR3, HP3 by (cbn; lia). rewrite lb_remove_head in HPR3, HP3.
replace (if pd =? 0 then 0 else uw_cost UWptr) with 0 in HP3 by (destruct (Z.eqb_spec pd 0); reflexivity).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in HDR; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]].
assert (OPB3 : opt_pbuf asegs m3 PBS pb).
{ eapply opt_pbuf_agree; [exact OPB | | apply incl_refl].
eapply (agree_of_heap_pres asegs A4H); [exact HPR3 | reflexivity | intros b Hb; apply in_or_app; left; right; apply in_or_app; left; exact Hb]. }
assert (HPRb : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m3).
{ eapply heap_pres_trans; [exact HPR|].
eapply heap_pres_weaken; [exact HPR3 | lia | intros b Hb; cbn; right; apply in_or_app; apply in_app_or in Hb; destruct Hb; [left; apply in_or_app; right; assumption | right; assumption]]. }
replace (ret_pc (Z_to_bv 64 0x9c3b8)) with (Z_to_bv 64 0x9c3b8) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
a4l.
eapply (mf_genA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo errv (Sstr true) ((x, 56) :: (pd, pdn) :: PBS) x rc T);
[ exact HP3 | lia | unfold jhdr_cells; cbn [app]; exact HDR | exact OPB3 | unfold mf_frameA; exact FR | exact ST3 | clia | clia | exact SPA | exact HT
| exact ERR3 | exact RA | eapply model_vm_only_trans; [exact VM0 | exact VM3] | exact HPRb | exact FS | exact FRM | exact Hrc
| cbn [bD charge] in *; lia | cbn [bB charge length app] in *; rewrite ?Nat2Z.inj_succ in *; lia | cbn [bB charge length app] in *; rewrite ?Nat2Z.inj_succ in *; lia | exact K ].
-
destruct J as (pb & PBS & REST & EBS & OPB & len & str & junk & ER & HL & HS & HDR). subst REST BS.
cbn [app] in HP.
blk_factsA A4L HIx HP x (str_objsize len) Hxal Hxlo Hxhi Hximg.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ x (str_objsize len) HP ltac:(left; reflexivity)) as SHx. unfold shad in SHx. a4l.
assert (SH : ro_cells asegs m (x / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ rewrite (shadow_bytes_split (str_objsize len) 6) in SHx by (unfold str_objsize; lia).
apply bytes_at_app in SHx as [SH6 _]. split; [cbn; repeat split; exact I | cbn [cells_bytes cbytes app]; exact SH6]. }
clear SHx. unfold str_objsize in *.
pose proof HDR as HDR0. unfold jhdr_cells in HDR. cbn [app] in HDR.
cbn [length app] in BB. rewrite ?Nat2Z.inj_succ in BB.
reenterA asegs A4L HIx asegs_wx HP.
asan_chk0.
bstep. norm_w32. bstep. bstep. if_truex.
bstep.
asan_chkA.
bstep.
bstep. if_truex.
evt_done5.
eapply (mf_genA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo errv (Sstr false) ((x, 49 + Z.max len 8) :: PBS) x rc T);
[ exact HP | lia | exact HDR0 | exact OPB | exact FR0 | exact ST | clia | clia | exact SPA | exact HT
| exact ERR | exact RA | exact VM0 | exact HPR | exact FS | exact FRM | exact Hrc
| exact BD | cbn [length app] in *; rewrite ?Nat2Z.inj_succ in *; lia | cbn [length app] in *; rewrite ?Nat2Z.inj_succ in *; lia | exact K ].
Qed.
End MF2.
End RC__1.
End Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfub.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QbFI. Import QRBl.
Import QZsi Qhd4.Mq1.
Import QCKW.Mq5 Qfub.
Import QsRG.Mq0 Qnhz.Mq0 QsRG QBxa.Mq0 QRjH QsV0 Qn1e QMz4 Q9ox.Mq0 QSpR.Mq2.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.
Import Qe4Y.
Import QHnV QCcH QfLs Qsw7 QJjn QRUw.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqg QJZd.Mqg QpNt.Mq7.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.

Definition A_IGETRANDOM : Z := 0x4fdc8.

Lemma size_test_w : forall n, 0 < n <= 64 -> bv_ltu (Z_to_bv 64 (n + -65)) (Z_to_bv 64 (-64)) = false.
Proof.
intros n Hn. unfold bv_ltu. rewrite !unsigned_lit_wrap.
replace ((-64) mod 2^64) with (2^64 - 64) by reflexivity.
replace ((n + -65) mod 2^64) with (2^64 + n - 65) by (Z.div_mod_to_equations; lia).
apply Z.ltb_ge. lia.
Qed.

Lemma zext32_flag : forall f, 0 <= f < 2^32 ->
Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 f)) 32))) 32) = Z_to_bv 64 f.
Proof.
intros f Hf. rewrite (unsigned_lit f) by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite unsigned_lit by lia.
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.

Section MIgetrandom.
Context {RC__ : Q6q3.RunConsts}.
Variable J : aj_base asegs.
Hypothesis SYSG : forall (F : FPF) (fc : FPC), @aj_getrandom_stmt F fc asegs J.

Definition igetrandom_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (K : TSet)
(buf len lo : Z) (junk : list byte),
CK J c ->
unpoisoned asegs m A_SB buf len -> asan_rt_ok m ->
1 <= len <= 64 -> 0x647000 <= buf -> app_mem buf len -> buf + len <= 2^47 ->
a0 = Z_to_bv 64 buf -> a1 = Z_to_bv 64 len -> (a2 = Z_to_bv 64 0 \/ a2 = Z_to_bv 64 GRND_NONBLOCK) ->
rw_cells asegs m buf [CB (Z.to_nat len) junk] ->
(buf + len <= lo \/ bv_unsigned sp <= buf) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 ->
bv_unsigned sp <= 2^47 -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte) (c' : config) (bs : list byte),
Z.of_nat (length bs) = len ->
munch [(buf, buf + len); (lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) ->
rw_cells asegs m' buf [CB (Z.to_nat len) bs] ->
CNEXT J c c' -> m_fds (cfg_model c') = m_fds (cfg_model c) -> m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJ J K c'
(MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 len) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
AJ J K c (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_IGETRANDOM) fc None m (seg_rom asegs)).

End MIgetrandom.
End Mq7.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.
Import QgoP.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqg Qw5U QJZd.Mqg QsKa.Mq9 QpNt.Mq7.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Ltac rt_cell RT c H :=
pose proof (proj1 (Forall_forall _ _) RT c
ltac:(unfold a4_rt_cells, a4_rt_consts; cbn [app]; repeat (first [left; reflexivity | right]))) as H;
cbn [fst snd] in H.

Lemma lower_word : forall x : byte,
Z_to_bv 64 (bv_unsigned (zxb x) + Z.shiftl (bv_unsigned (v_sltiu (Z_to_bv 64 (bv_unsigned (zxb x) + -65)) 26)) 5)
= Z_to_bv 64 (lower8 (bv_unsigned x)).
Proof.
intros x. pose proof (byte_rng x) as R. unfold zxb. rewrite (unsigned_lit (bv_unsigned x)) by lia.
unfold v_sltiu, lower8. rewrite unsigned_lit_wrap. change (bv_wrap 64 26) with 26.
destruct ((65 <=? bv_unsigned x) && (bv_unsigned x <=? 90))%bool eqn:E.
- apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1, E2.
rewrite Z.mod_small by lia. replace (bv_unsigned x + -65 <? 26) with true by (symmetry; apply Z.ltb_lt; lia).
rewrite (unsigned_lit 1) by lia. reflexivity.
- replace ((bv_unsigned x + -65) mod 2 ^ 64 <? 26) with false.
+ rewrite (unsigned_lit 0) by lia. change (Z.shiftl 0 5) with 0. rewrite Z.add_0_r. reflexivity.
+ symmetry. apply Z.ltb_ge. apply andb_false_iff in E. destruct E as [E|E]; [apply Z.leb_gt in E | apply Z.leb_gt in E].
* replace ((bv_unsigned x + -65) mod 2 ^ 64) with (bv_unsigned x + -65 + 2^64) by (apply Z.mod_unique with (q := -1); lia). lia.
* rewrite Z.mod_small by lia. lia.
Qed.

Lemma lit_eqb : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma istrncasecmp_sound_U : istrncasecmp_spec_U.
Proof.
unfold istrncasecmp_spec_U, istrn_spec_U.
intros until Q. intros MODEL UPA UPB RT Ha Ha47 Hb Hb47 HaLo HbLo Ea0 Ea1 Ea2 Hn STRA STRB ST LO LOS SPA MI RA K.
subst a0 a1 a2. unfold_consts. word_range sp SPR.
rt_cell RT (0xf2e98, [Z_to_bv 8 1]) INITED. apply ro_C1_of_bytes_at in INITED.
rt_cell RT (0xe81a8, le8 (Z_to_bv 64 0x183ce8)) GOTFL. apply ro_C8_of_bytes_at in GOTFL.
rt_cell RT (0x183ddd, [Z_to_bv 8 0]) STRICT. apply ro_C1_of_bytes_at in STRICT.
rt_cell RT (A_GOT_SB, le8 (Z_to_bv 64 A_SB_CELL)) GOT. apply ro_C8_of_bytes_at in GOT.
rt_cell RT (A_SB_CELL, le8 (Z_to_bv 64 A_SB)) CELL. apply ro_C8_of_bytes_at in CELL.
unfold A_GOT_SB, A_SB_CELL, A_SB in GOT, CELL. unfold A_SB_CELL in GOT.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
stash STRA. stash STRB.
unfold A_ISTRNCASECMP. carve_frame 104%nat ST.
step.
do 14 step.
do 6 step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with STc : stk asegs mc lo ?hi |- _ =>
destruct (stk_split asegs mc lo (bv_unsigned sp - 2176) hi STc ltac:(lia)) as [ST1 ST2]; clear STc end end.
eapply try_asan_init_spec; [exact MI | assumption | rewrite unsigned_lit by lia; exact ST1 | rewrite unsigned_lit by lia; lia
| lia | rewrite unsigned_lit by lia; reflexivity |].
rewrite ?unsigned_lit by lia.
intros a1x m2 MU2 WM2 MI2 ST1'.
lazymatch type of MU2 with munch _ ?mc _ =>
transport_after_call asegs mc m2 MU2 WM2; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU2 WM2 end.
replace (ret_pc (Z_to_bv 64 0x50e74)) with (Z_to_bv 64 0x50e74) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. if_false.
step. if_falsex.
step.

unfold istrncasecmp_model in MODEL.
destruct (icmp_walk_nread _ _ _ _ _ _ _ MODEL) as (Kf & Kl & Kr).
pose proof (icmp_walk_pos _ _ _ _ _ _ _ MODEL ltac:(lia)) as Kpos.
destruct (icmp_walk_last _ _ _ _ _ _ _ MODEL Kpos) as (xa & xb & NA & NB & LAST).
unstash STRA. unstash STRB.
assert (STRA2 : bytes_at asegs m2 a la)
by (eapply bytes_at_transport; [exact STRA | eassumption | cbn [disjoint_from]; lia]).
assert (STRB2 : bytes_at asegs m2 b lb)
by (eapply bytes_at_transport; [exact STRB | eassumption | cbn [disjoint_from]; lia]).
remember (Z.of_nat k - 1) as len eqn:Elen.
assert (Ek : Z.of_nat k = len + 1) by lia.
assert (Hlen : 0 <= len < n) by lia.

assert (POST : forall (idx : Z) (ya yb : byte) (x10 x11 : word),
0 <= idx <= n -> Z.min (idx + 1) n = len + 1 -> v = casecmp_val ya yb ->
evt asegs Q (MS (mkR (Z_to_bv 64 0x50e74) (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp t0 t1 t2 sp (Z_to_bv 64 n) x10 x11 (Z_to_bv 64 n) a3 a4 a5 a6 a7
(Z_to_bv 64 b) (Z_to_bv 64 a) ra s5 s6 s7 (zxb yb) (zxb ya) s10 (Z_to_bv 64 idx) t3 t4 t5 t6)
F (Z_to_bv 64 0x50ec4) fc None m2 (seg_rom asegs))).
2: {
assert (LOOP : forall (Kn : nat) (i : Z) (x10 x11 x24 x25 : word),
Z.to_nat (Z.of_nat k - i) = Kn -> 0 <= i < Z.of_nat k ->
evt asegs Q (MS (mkR (Z_to_bv 64 0x50e74) (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp t0 t1 t2 sp (Z_to_bv 64 n) x10 x11 (Z_to_bv 64 n) a3 a4 a5 a6 a7
(Z_to_bv 64 b) (Z_to_bv 64 a) ra s5 s6 s7 x24 x25 s10 (Z_to_bv 64 i) t3 t4 t5 t6)
F (Z_to_bv 64 0x50e80) fc None m2 (seg_rom asegs))).
{ induction Kn as [|Kn IH]; intros i x10 x11 x24 x25 HK Hi; [lia|].
assert (RDS : exists ya yb, nth_error la (Z.to_nat i) = Some ya /\ nth_error lb (Z.to_nat i) = Some yb /\
((i + 1 < Z.of_nat k /\ casecmp_stop ya yb = false) \/ (i + 1 = Z.of_nat k /\ ya = xa /\ yb = xb))).
{ destruct (Z.eq_dec (i + 1) (Z.of_nat k)) as [E|NE].
- exists xa, xb. replace (Z.to_nat i) with (k - 1)%nat by lia. split; [exact NA|]. split; [exact NB|]. right. auto.
- destruct (icmp_walk_before _ _ _ _ _ _ _ (Z.to_nat i) MODEL ltac:(lia)) as (ya & yb & H1 & H2 & H3).
exists ya, yb. split; [exact H1|]. split; [exact H2|]. left. split; [lia | exact H3]. }
destruct RDS as (ya & yb & NYA & NYB & CASE).
pose proof (u8ro_read asegs m2 a la i ya _ STRA2 NYA ltac:(lia) eq_refl) as RD1.
pose proof (u8ro_read asegs m2 b lb i yb _ STRB2 NYB ltac:(lia) eq_refl) as RD2.
pose proof (byte_rng ya) as RYA. pose proof (byte_rng yb) as RYB.
pose proof (lower8_range _ RYA) as LYA. pose proof (lower8_range _ RYB) as LYB.
step. step. step. step.
step. rewrite zxb_eqb0.
destruct CASE as [(Hlt & NS) | (Hlast & -> & ->)].
- unfold casecmp_stop in NS. apply orb_false_iff in NS. destruct NS as (NS1 & NS2). apply negb_false_iff in NS1.
rewrite NS2. cbv iota.
do 8 step. rewrite !lower_word.
step. rewrite lit_eqb by lia. rewrite NS1. cbv [negb]. cbv iota.
step.
step. if_truex.
apply (IH (i + 1)); lia.
- destruct LAST as [(STOP & Ev) | (NSTOP & Hk & Ev)].
+ unfold casecmp_stop in STOP.
destruct (bv_unsigned xa =? 0) eqn:E0; cbv iota.
* apply (POST i xa xb); [lia | lia | exact Ev].
* rewrite orb_false_r in STOP. apply negb_true_iff in STOP.
do 8 step. rewrite !lower_word.
step. rewrite lit_eqb by lia. rewrite STOP. cbv [negb]. cbv iota.
apply (POST i xa xb); [lia | lia | exact Ev].
+ unfold casecmp_stop in NSTOP. apply orb_false_iff in NSTOP. destruct NSTOP as (NS1 & NS2). apply negb_false_iff in NS1.
rewrite NS2. cbv iota.
do 8 step. rewrite !lower_word.
step. rewrite lit_eqb by lia. rewrite NS1. cbv [negb]. cbv iota.
step.
step. if_falsex.
step.
apply (POST n xa xb); [lia | lia |].
rewrite Ev. unfold casecmp_val. apply Z.eqb_eq in NS1. lia. }
apply (LOOP k 0); lia. }
intros idx ya yb x10 x11 Hidx Hmin Ev.
rewrite Ek in *.
assert (UPA2 : unpoisoned asegs m2 A_SB a (len + 1))
by (eapply unpoisoned_transport; [exact UPA | exact MU | intros a' k' Ha' Hk'; eapply (shadow_outside_stack A_SB a (len + 1)); try eassumption; unfold A_SB; lia]).
assert (UPB2 : unpoisoned asegs m2 A_SB b (len + 1))
by (eapply unpoisoned_transport; [exact UPB | exact MU | intros a' k' Ha' Hk'; eapply (shadow_outside_stack A_SB b (len + 1)); try eassumption; unfold A_SB; lia]).
clear UPA UPB.

assert (TAIL : forall (xra q0 q1 q2 w0 w1 y0 y1 y2 y3 y4 y5 y6 y7 w2 w3 w4 w5 w6 w7 w10 w11 q3 q4 q5 q6 : word),
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp q0 q1 q2 w0 w1 y0 y1 y2 y3 y4 y5 y6 y7
w2 w3 w4 w5 w6 w7 (zxb yb) (zxb ya) w10 w11 q3 q4 q5 q6)
F (Z_to_bv 64 0x51038) fc None m2 (seg_rom asegs))).
{ intros xra q0 q1 q2 w0 w1 y0 y1 y2 y3 y4 y5 y6 y7 w2 w3 w4 w5 w6 w7 w10 w11 q3 q4 q5 q6.
pose proof (byte_rng ya) as RYA. pose proof (byte_rng yb) as RYB.
pose proof (lower8_range _ RYA) as LYA. pose proof (lower8_range _ RYB) as LYB.
do 8 step. rewrite !lower_word.
step. rewrite !unsigned_lit by lia. fold (casecmp_val ya yb). rewrite <- Ev.
do 5 step.
step. step.
step. step.
do 13 step.
step. step.
eapply K; [exact MU | exact WM | exact MI2 | exact STRA2 | exact STRB2 |].
assert (STm : stk asegs m2 lo (bv_unsigned sp + -104)) by (eapply stk_merge; [exact ST1' | exact ST2 | lia]).
release_frame FR STm (bv_unsigned sp). exact STm. }

assert (CHK2 : forall (xra q0 q1 q2 w0 w1 y0 y1 y2 y3 y4 y5 y6 y7 w3 w4 w6 w7 w10 w11 q3 q4 q5 q6 : word),
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp q0 q1 q2 w0 w1 y0 y1 y2 y3 y4 y5 y6 y7
(Z_to_bv 64 b) w3 w4 (Z_to_bv 64 (len + 1)) w6 w7 (zxb yb) (zxb ya) w10 w11 q3 q4 q5 q6)
F (Z_to_bv 64 0x50ff0) fc None m2 (seg_rom asegs))).
{ intros xra q0 q1 q2 w0 w1 y0 y1 y2 y3 y4 y5 y6 y7 w3 w4 w6 w7 w10 w11 q3 q4 q5 q6.
step. replace (len + 1 + -65) with (len + -64) by lia.
step.
step. replace (len + -64) with ((len + 1) + -65) by lia. rewrite size_test_n by lia. cbv iota.
assert (Hh : b / 8 <= (b + len) / 8 <= b / 8 + 8) by (Z.div_mod_to_equations; lia).
destruct (unpoisoned_word asegs _ _ _ _ (b / 8 + A_SB) UPB2 ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (v1 & Lv1 & V1c).
destruct (unpoisoned_word asegs _ _ _ _ ((b + len) / 8 + A_SB) UPB2 ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (v2 & Lv2 & V2c).
unfold A_SB in V1c, V2c.
assert (GS0 : forall j, 0 <= j -> b / 8 + j < (b + len) / 8 ->
ov_read_bytes asegs m2 (Z_to_bv 64 (b / 8 + 2147450880 + j)) 1 = Some [Z_to_bv 8 0]).
{ intros j Hj Hjl. apply ov_read1_of_ro.
replace (b / 8 + 2147450880 + j) with ((b / 8 + j) + A_SB) by (unfold A_SB; lia).
apply (unpoisoned_gran0 asegs _ _ _ _ _ UPB2). replace (b + (len + 1) - 1) with (b + len) by lia. lia. }
assert (HRL : exists v, ov_read_bytes asegs m2 (Z_to_bv 64 ((b + len) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 v]
/\ (v = 0 \/ (0 < v < 8 /\ (b + len) mod 8 < v))).
{ destruct (unpoisoned_last asegs _ _ _ _ UPB2) as (v0 & Hro & Hv). replace (b + (len + 1) - 1) with (b + len) in Hro, Hv by lia.
exists v0. split; [| exact Hv]. apply ov_read1_of_ro. unfold A_SB in Hro. exact Hro. }
do 2 step.
step.
step.
step.
step. replace (b + (len + 1) + -1) with (b + len) by lia.
step. do 2 step. do 2 step.
sh_norm.
replace (2147450880 + b / 8) with (b / 8 + 2147450880) by lia.
replace (2147450880 + (b + len) / 8) with ((b + len) / 8 + 2147450880) by lia.
rewrite (unsigned_lit (b / 8 + 2147450880)) by lia. rewrite (unsigned_lit ((b + len) / 8 + 2147450880)) by lia.
rewrite !land_m8_64 by lia.
do 2 step. step.

assert (LOOPG : forall (Kn : nat) (i : Z) (y3' y4' : word),
Z.to_nat ((b + len) / 8 - b / 8 - i) = Kn -> 0 <= i -> b / 8 + i < (b + len) / 8 ->
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp q0 q1 q2 w0 w1 (Z_to_bv 64 (b / 8 + 2147450880 + i)) (Z_to_bv 64 ((b + len) / 8 + 2147450880)) (Z_to_bv 64 0) y3' y4' y5 y6 y7
(Z_to_bv 64 b) w3 w4 (Z_to_bv 64 (len + 1)) w6 w7 (zxb yb) (zxb ya) w10 w11 q3 q4 q5 q6)
F (Z_to_bv 64 0x512b4) fc None m2 (seg_rom asegs))).
{ clear Hh V1c V2c HRL.
induction Kn as [|Kn IH]; intros i y3' y4' HK Hi Hig; [lia|].
pose proof (GS0 i Hi Hig) as HR.
step. rewrite ?zxb_zero. clear HR.
step. step. rewrite ?(unsigned_lit 0) by lia. change (Z.lor 0 0) with 0.
step.
destruct (Z.eq_dec (b / 8 + i + 1) ((b + len) / 8)) as [Heq|Hne].
- if_falsex. step. step. if_true. apply TAIL.
- if_truex. replace (b / 8 + 2147450880 + i + 1) with (b / 8 + 2147450880 + (i + 1)) by lia. apply (IH (i + 1)); lia. }
step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd end.
2: { apply TAIL. }
destruct HRL as (vv & HR & Hv).
assert (Hv8 : 0 <= vv < 128) by (destruct Hv as [->|(? & ?)]; lia).
clear V1c V2c.
step. rewrite (sxb_small vv) by lia. clear HR.
step. rewrite (unsigned_lit (b + len)) by lia. rewrite land7_mod8 by lia.
step. step. step. step.
destruct Hv as [-> | (Hk & Hlast)].
- rewrite (v_sltu_0' (Z_to_bv 64 0) (Z_to_bv 64 0)) by (rewrite !unsigned_lit by lia; lia).
rewrite (unsigned_lit 0) by lia. rewrite Z.land_0_l.
step.
destruct (Z.eq_dec (b / 8) ((b + len) / 8)) as [Heq1|Hne1].
+ if_truex. step. step. if_true. apply TAIL.
+ if_falsex. replace (b / 8 + 2147450880) with (b / 8 + 2147450880 + 0) by lia.
apply (LOOPG (Z.to_nat ((b + len) / 8 - b / 8 - 0)) 0); lia.
- rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 vv)) by (rewrite !unsigned_lit by lia; lia).
rewrite (v_slt_1 (Z_to_bv 64 ((b + len) mod 8)) (Z_to_bv 64 vv)) by (rewrite !signed_lit by lia; clear Hh; Z.div_mod_to_equations; lia).
rewrite !(unsigned_lit 1) by lia. change (Z.lxor 1 1) with 0. rewrite Z.land_0_r.
step.
destruct (Z.eq_dec (b / 8) ((b + len) / 8)) as [Heq1|Hne1].
+ if_truex. step. step. if_true. apply TAIL.
+ if_falsex. replace (b / 8 + 2147450880) with (b / 8 + 2147450880 + 0) by lia.
apply (LOOPG (Z.to_nat ((b + len) / 8 - b / 8 - 0)) 0); lia. }

assert (NEXT1 : forall (xra q0 q1 q2 w0 y0 y1 y2 y3 y4 y5 y6 y7 w4 w5 w6 w7 w10 q3 q4 q5 q6 : word),
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp q0 q1 q2 w0 (Z_to_bv 64 n) y0 y1 y2 y3 y4 y5 y6 y7
(Z_to_bv 64 b) (Z_to_bv 64 a) w4 w5 w6 w7 (zxb yb) (zxb ya) w10 (Z_to_bv 64 idx) q3 q4 q5 q6)
F (Z_to_bv 64 0x50fe0) fc None m2 (seg_rom asegs))).
{ intros xra q0 q1 q2 w0 y0 y1 y2 y3 y4 y5 y6 y7 w4 w5 w6 w7 w10 q3 q4 q5 q6.
step.
step.
destruct (Z_lt_ge_dec (idx + 1) n) as [Hlt | Hge].
- if_falsex. replace (idx + 1) with (len + 1) by lia.
step. step. rewrite (unsigned_lit b) by lia. rewrite (lxor_ones64 b) by lia. if_falsex.
apply CHK2.
- if_truex.
step. replace n with (len + 1) at 2 by lia.
step. step. rewrite (unsigned_lit b) by lia. rewrite (lxor_ones64 b) by lia. if_truex.
apply CHK2. }
assert (CHK1 : forall (xra q0 q1 q2 w0 y0 y1 y2 y3 y4 y5 y6 y7 w4 w6 w7 w10 q3 q4 q5 q6 : word),
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp q0 q1 q2 w0 (Z_to_bv 64 n) y0 y1 y2 y3 y4 y5 y6 y7
(Z_to_bv 64 b) (Z_to_bv 64 a) w4 (Z_to_bv 64 (len + 1)) w6 w7 (zxb yb) (zxb ya) w10 (Z_to_bv 64 idx) q3 q4 q5 q6)
F (Z_to_bv 64 0x50f98) fc None m2 (seg_rom asegs))).
{ intros xra q0 q1 q2 w0 y0 y1 y2 y3 y4 y5 y6 y7 w4 w6 w7 w10 q3 q4 q5 q6.
step. replace (len + 1 + -65) with (len + -64) by lia.
step.
step. replace (len + -64) with ((len + 1) + -65) by lia. rewrite size_test_n by lia. cbv iota.
assert (Hh : a / 8 <= (a + len) / 8 <= a / 8 + 8) by (Z.div_mod_to_equations; lia).
destruct (unpoisoned_word asegs _ _ _ _ (a / 8 + A_SB) UPA2 ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (v1 & Lv1 & V1c).
destruct (unpoisoned_word asegs _ _ _ _ ((a + len) / 8 + A_SB) UPA2 ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (v2 & Lv2 & V2c).
unfold A_SB in V1c, V2c.
assert (GS0 : forall j, 0 <= j -> a / 8 + j < (a + len) / 8 ->
ov_read_bytes asegs m2 (Z_to_bv 64 (a / 8 + 2147450880 + j)) 1 = Some [Z_to_bv 8 0]).
{ intros j Hj Hjl. apply ov_read1_of_ro.
replace (a / 8 + 2147450880 + j) with ((a / 8 + j) + A_SB) by (unfold A_SB; lia).
apply (unpoisoned_gran0 asegs _ _ _ _ _ UPA2). replace (a + (len + 1) - 1) with (a + len) by lia. lia. }
assert (HRL : exists v, ov_read_bytes asegs m2 (Z_to_bv 64 ((a + len) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 v]
/\ (v = 0 \/ (0 < v < 8 /\ (a + len) mod 8 < v))).
{ destruct (unpoisoned_last asegs _ _ _ _ UPA2) as (v0 & Hro & Hv). replace (a + (len + 1) - 1) with (a + len) in Hro, Hv by lia.
exists v0. split; [| exact Hv]. apply ov_read1_of_ro. unfold A_SB in Hro. exact Hro. }
do 2 step.
step.
step.
step.
step. replace (a + (len + 1) + -1) with (a + len) by lia.
step. do 2 step. do 2 step.
sh_norm.
replace (2147450880 + a / 8) with (a / 8 + 2147450880) by lia.
replace (2147450880 + (a + len) / 8) with ((a + len) / 8 + 2147450880) by lia.
rewrite (unsigned_lit (a / 8 + 2147450880)) by lia. rewrite (unsigned_lit ((a + len) / 8 + 2147450880)) by lia.
rewrite !land_m8_64 by lia.
do 2 step. step.

assert (LOOPG : forall (Kn : nat) (i : Z) (y3' y4' : word),
Z.to_nat ((a + len) / 8 - a / 8 - i) = Kn -> 0 <= i -> a / 8 + i < (a + len) / 8 ->
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp q0 q1 q2 w0 (Z_to_bv 64 n) (Z_to_bv 64 (a / 8 + 2147450880 + i)) (Z_to_bv 64 ((a + len) / 8 + 2147450880)) (Z_to_bv 64 0) y3' y4' y5 y6 y7
(Z_to_bv 64 b) (Z_to_bv 64 a) w4 (Z_to_bv 64 (len + 1)) w6 w7 (zxb yb) (zxb ya) w10 (Z_to_bv 64 idx) q3 q4 q5 q6)
F (Z_to_bv 64 0x511ec) fc None m2 (seg_rom asegs))).
{ clear Hh V1c V2c HRL.
induction Kn as [|Kn IH]; intros i y3' y4' HK Hi Hig; [lia|].
pose proof (GS0 i Hi Hig) as HR.
step. rewrite ?zxb_zero. clear HR.
step. step. rewrite ?(unsigned_lit 0) by lia. change (Z.lor 0 0) with 0.
step.
destruct (Z.eq_dec (a / 8 + i + 1) ((a + len) / 8)) as [Heq|Hne].
- if_falsex. step. step. if_true. apply NEXT1.
- if_truex. replace (a / 8 + 2147450880 + i + 1) with (a / 8 + 2147450880 + (i + 1)) by lia. apply (IH (i + 1)); lia. }
step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd end.
2: { apply NEXT1. }
destruct HRL as (vv & HR & Hv).
assert (Hv8 : 0 <= vv < 128) by (destruct Hv as [->|(? & ?)]; lia).
clear V1c V2c.
step. rewrite (sxb_small vv) by lia. clear HR.
step. rewrite (unsigned_lit (a + len)) by lia. rewrite land7_mod8 by lia.
step. step. step. step.
destruct Hv as [-> | (Hk & Hlast)].
- rewrite (v_sltu_0' (Z_to_bv 64 0) (Z_to_bv 64 0)) by (rewrite !unsigned_lit by lia; lia).
rewrite (unsigned_lit 0) by lia. rewrite Z.land_0_l.
step.
destruct (Z.eq_dec (a / 8) ((a + len) / 8)) as [Heq1|Hne1].
+ if_truex. step. step. if_true. apply NEXT1.
+ if_falsex. replace (a / 8 + 2147450880) with (a / 8 + 2147450880 + 0) by lia.
apply (LOOPG (Z.to_nat ((a + len) / 8 - a / 8 - 0)) 0); lia.
- rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 vv)) by (rewrite !unsigned_lit by lia; lia).
rewrite (v_slt_1 (Z_to_bv 64 ((a + len) mod 8)) (Z_to_bv 64 vv)) by (rewrite !signed_lit by lia; clear Hh; Z.div_mod_to_equations; lia).
rewrite !(unsigned_lit 1) by lia. change (Z.lxor 1 1) with 0. rewrite Z.land_0_r.
step.
destruct (Z.eq_dec (a / 8) ((a + len) / 8)) as [Heq1|Hne1].
+ if_truex. step. step. if_true. apply NEXT1.
+ if_falsex. replace (a / 8 + 2147450880) with (a / 8 + 2147450880 + 0) by lia.
apply (LOOPG (Z.to_nat ((a + len) / 8 - a / 8 - 0)) 0); lia. }

step.
destruct (Z_lt_ge_dec idx n) as [Hlt | Hge].
-
if_falsex.
do 2 step.
step. rewrite ?zxb_zero.
step.
step. change (Z.land (bv_unsigned (Z_to_bv 64 0)) 1) with 0.
step. if_true.
step.
step.
destruct (Z_lt_ge_dec (idx + 1) n) as [Hlt1 | Hge1].
+ if_falsex. replace (idx + 1) with (len + 1) by lia.
step. step. step.
step. rewrite (unsigned_lit a) by lia. rewrite (lxor_ones64 a) by lia. if_falsex.
apply CHK1.
+ if_truex.
step. replace n with (len + 1) at 2 by lia.
step. step. step.
step. rewrite (unsigned_lit a) by lia. rewrite (lxor_ones64 a) by lia. if_truex.
apply CHK1.
-
if_truex.
step.
step. if_falsex.
step. replace n with (len + 1) at 2 by lia.
step. step. step.
step. rewrite (unsigned_lit a) by lia. rewrite (lxor_ones64 a) by lia. if_truex.
apply CHK1.
Qed.
End RC__1.
End Mq8.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgoP.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qw5U. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJZd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJZd.Mqg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpNt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpNt.Mq7.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Ltac rt_cell RT c H :=
pose proof (proj1 (Forall_forall _ _) RT c
ltac:(unfold a4_rt_cells, a4_rt_consts; cbn [app]; repeat (first [left; reflexivity | right]))) as H;
cbn [fst snd] in H.

Lemma istrncmp_sound_U : istrncmp_spec_U.
Proof.
unfold istrncmp_spec_U, istrn_spec_U.
intros until Q. intros MODEL UPA UPB RT Ha Ha47 Hb Hb47 HaLo HbLo Ea0 Ea1 Ea2 Hn STRA STRB ST LO LOS SPA MI RA K.
subst a0 a1 a2. unfold_consts. word_range sp SPR.
rt_cell RT (0xf2e98, [Z_to_bv 8 1]) INITED. apply ro_C1_of_bytes_at in INITED.
rt_cell RT (0xe81a8, le8 (Z_to_bv 64 0x183ce8)) GOTFL. apply ro_C8_of_bytes_at in GOTFL.
rt_cell RT (0x183ddd, [Z_to_bv 8 0]) STRICT. apply ro_C1_of_bytes_at in STRICT.
rt_cell RT (A_GOT_SB, le8 (Z_to_bv 64 A_SB_CELL)) GOT. apply ro_C8_of_bytes_at in GOT.
rt_cell RT (A_SB_CELL, le8 (Z_to_bv 64 A_SB)) CELL. apply ro_C8_of_bytes_at in CELL.
unfold A_GOT_SB, A_SB_CELL, A_SB in GOT, CELL. unfold A_SB_CELL in GOT.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
stash STRA. stash STRB.
unfold A_ISTRNCMP. carve_frame 104%nat ST.
step.
do 14 step.
do 6 step.
step.
apply asan_inited_spec; [exact MI | assumption |].
replace (ret_pc (Z_to_bv 64 0x50898)) with (Z_to_bv 64 0x50898) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. if_false.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with STc : stk asegs mc lo ?hi |- _ =>
destruct (stk_split asegs mc lo (bv_unsigned sp - 2176) hi STc ltac:(lia)) as [ST1 ST2]; clear STc end end.
eapply try_asan_init_spec; [exact MI | assumption | rewrite unsigned_lit by lia; exact ST1 | rewrite unsigned_lit by lia; lia
| lia | rewrite unsigned_lit by lia; reflexivity |].
rewrite ?unsigned_lit by lia.
intros a1x m2 MU2 WM2 MI2 ST1'.
lazymatch type of MU2 with munch _ ?mc _ =>
transport_after_call asegs mc m2 MU2 WM2; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU2 WM2 end.
replace (ret_pc (Z_to_bv 64 0x508a0)) with (Z_to_bv 64 0x508a0) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. if_false.
step. if_falsex.
step.

unfold istrncmp_model in MODEL.
destruct (icmp_walk_nread _ _ _ _ _ _ _ MODEL) as (Kf & Kl & Kr).
pose proof (icmp_walk_pos _ _ _ _ _ _ _ MODEL ltac:(lia)) as Kpos.
destruct (icmp_walk_last _ _ _ _ _ _ _ MODEL Kpos) as (xa & xb & NA & NB & LAST).
unstash STRA. unstash STRB.
assert (STRA2 : bytes_at asegs m2 a la)
by (eapply bytes_at_transport; [exact STRA | eassumption | cbn [disjoint_from]; lia]).
assert (STRB2 : bytes_at asegs m2 b lb)
by (eapply bytes_at_transport; [exact STRB | eassumption | cbn [disjoint_from]; lia]).
remember (Z.of_nat k - 1) as len eqn:Elen.
assert (Ek : Z.of_nat k = len + 1) by lia.
assert (Hlen : 0 <= len < n) by lia.

assert (POST : forall (idx : Z) (ya yb : byte) (x10 : word),
0 <= idx <= n -> Z.min (idx + 1) n = len + 1 -> v = cmp_sign ya yb ->
evt asegs Q (MS (mkR (Z_to_bv 64 0x508a0) (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp t0 t1 t2 sp (Z_to_bv 64 n) x10 a1x (Z_to_bv 64 n) a3 a4 a5 a6 a7
(Z_to_bv 64 b) (Z_to_bv 64 a) ra s5 s6 s7 (zxb ya) (zxb yb) s10 (Z_to_bv 64 idx) t3 t4 t5 t6)
F (Z_to_bv 64 0x508d4) fc None m2 (seg_rom asegs))).
2: {
assert (LOOP : forall (Kn : nat) (i : Z) (x10 x24 x25 : word),
Z.to_nat (Z.of_nat k - i) = Kn -> 0 <= i < Z.of_nat k ->
evt asegs Q (MS (mkR (Z_to_bv 64 0x508a0) (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp t0 t1 t2 sp (Z_to_bv 64 n) x10 a1x (Z_to_bv 64 n) a3 a4 a5 a6 a7
(Z_to_bv 64 b) (Z_to_bv 64 a) ra s5 s6 s7 x24 x25 s10 (Z_to_bv 64 i) t3 t4 t5 t6)
F (Z_to_bv 64 0x508ac) fc None m2 (seg_rom asegs))).
{ induction Kn as [|Kn IH]; intros i x10 x24 x25 HK Hi; [lia|].
assert (RDS : exists ya yb, nth_error la (Z.to_nat i) = Some ya /\ nth_error lb (Z.to_nat i) = Some yb /\
((i + 1 < Z.of_nat k /\ cmp_stop ya yb = false) \/ (i + 1 = Z.of_nat k /\ ya = xa /\ yb = xb))).
{ destruct (Z.eq_dec (i + 1) (Z.of_nat k)) as [E|NE].
- exists xa, xb. replace (Z.to_nat i) with (k - 1)%nat by lia. split; [exact NA|]. split; [exact NB|]. right. auto.
- destruct (icmp_walk_before _ _ _ _ _ _ _ (Z.to_nat i) MODEL ltac:(lia)) as (ya & yb & H1 & H2 & H3).
exists ya, yb. split; [exact H1|]. split; [exact H2|]. left. split; [lia | exact H3]. }
destruct RDS as (ya & yb & NYA & NYB & CASE).
pose proof (u8ro_read asegs m2 a la i ya _ STRA2 NYA ltac:(lia) eq_refl) as RD1.
pose proof (u8ro_read asegs m2 b lb i yb _ STRB2 NYB ltac:(lia) eq_refl) as RD2.
step. step. step. step.
step. rewrite zxb_eqb0.
destruct CASE as [(Hlt & NS) | (Hlast & -> & ->)].
- unfold cmp_stop in NS. apply orb_false_iff in NS. destruct NS as (NS1 & NS2). apply negb_false_iff in NS1.
rewrite NS2. cbv iota.
step. rewrite zxb_eqb, NS1. cbv [negb]. cbv iota.
step.
step. if_truex.
apply (IH (i + 1)); lia.
- destruct LAST as [(STOP & Ev) | (NSTOP & Hk & Ev)].
+ unfold cmp_stop in STOP.
destruct (bv_unsigned xa =? 0) eqn:E0; cbv iota.
* apply (POST i xa xb); [lia | lia | exact Ev].
* rewrite orb_false_r in STOP. apply negb_true_iff in STOP.
step. rewrite zxb_eqb, STOP. cbv [negb]. cbv iota.
apply (POST i xa xb); [lia | lia | exact Ev].
+ unfold cmp_stop in NSTOP. apply orb_false_iff in NSTOP. destruct NSTOP as (NS1 & NS2). apply negb_false_iff in NS1.
rewrite NS2. cbv iota.
step. rewrite zxb_eqb, NS1. cbv [negb]. cbv iota.
step.
step. if_falsex.
step. step.
apply (POST n xa xa); [lia | lia |].
rewrite Ev. unfold cmp_sign. rewrite Z.sub_diag. reflexivity. }
apply (LOOP k 0); lia. }
intros idx ya yb x10 Hidx Hmin Ev.
rewrite Ek in *.
assert (UPA2 : unpoisoned asegs m2 A_SB a (len + 1))
by (eapply unpoisoned_transport; [exact UPA | exact MU | intros a' k' Ha' Hk'; eapply (shadow_outside_stack A_SB a (len + 1)); try eassumption; unfold A_SB; lia]).
assert (UPB2 : unpoisoned asegs m2 A_SB b (len + 1))
by (eapply unpoisoned_transport; [exact UPB | exact MU | intros a' k' Ha' Hk'; eapply (shadow_outside_stack A_SB b (len + 1)); try eassumption; unfold A_SB; lia]).
clear UPA UPB.

assert (TAIL : forall (xra q0 q1 q2 w0 w1 y0 y1 y2 y3 y4 y5 y6 y7 w2 w3 w4 w5 w6 w7 w10 w11 q3 q4 q5 q6 : word),
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp q0 q1 q2 w0 w1 y0 y1 y2 y3 y4 y5 y6 y7
w2 w3 w4 w5 w6 w7 (zxb ya) (zxb yb) w10 w11 q3 q4 q5 q6)
F (Z_to_bv 64 0x50a94) fc None m2 (seg_rom asegs))).
{ intros xra q0 q1 q2 w0 w1 y0 y1 y2 y3 y4 y5 y6 y7 w2 w3 w4 w5 w6 w7 w10 w11 q3 q4 q5 q6.
step. step. step. rewrite sltu_sign, <- Ev.
do 5 step.
step. step.
step. step.
do 13 step.
step. step.
eapply K; [exact MU | exact WM | exact MI2 | exact STRA2 | exact STRB2 |].
assert (STm : stk asegs m2 lo (bv_unsigned sp + -104)) by (eapply stk_merge; [exact ST1' | exact ST2 | lia]).
release_frame FR STm (bv_unsigned sp). exact STm. }

assert (CHK2 : forall (xra q0 q1 q2 w0 w1 y0 y1 y2 y3 y4 y5 y6 y7 w3 w4 w6 w7 w10 w11 q3 q4 q5 q6 : word),
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp q0 q1 q2 w0 w1 y0 y1 y2 y3 y4 y5 y6 y7
(Z_to_bv 64 b) w3 w4 (Z_to_bv 64 (len + 1)) w6 w7 (zxb ya) (zxb yb) w10 w11 q3 q4 q5 q6)
F (Z_to_bv 64 0x50a4c) fc None m2 (seg_rom asegs))).
{ intros xra q0 q1 q2 w0 w1 y0 y1 y2 y3 y4 y5 y6 y7 w3 w4 w6 w7 w10 w11 q3 q4 q5 q6.
step. replace (len + 1 + -65) with (len + -64) by lia.
step.
step. replace (len + -64) with ((len + 1) + -65) by lia. rewrite size_test_n by lia. cbv iota.
assert (Hh : b / 8 <= (b + len) / 8 <= b / 8 + 8) by (Z.div_mod_to_equations; lia).
destruct (unpoisoned_word asegs _ _ _ _ (b / 8 + A_SB) UPB2 ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (v1 & Lv1 & V1c).
destruct (unpoisoned_word asegs _ _ _ _ ((b + len) / 8 + A_SB) UPB2 ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (v2 & Lv2 & V2c).
unfold A_SB in V1c, V2c.
assert (GS0 : forall j, 0 <= j -> b / 8 + j < (b + len) / 8 ->
ov_read_bytes asegs m2 (Z_to_bv 64 (b / 8 + 2147450880 + j)) 1 = Some [Z_to_bv 8 0]).
{ intros j Hj Hjl. apply ov_read1_of_ro.
replace (b / 8 + 2147450880 + j) with ((b / 8 + j) + A_SB) by (unfold A_SB; lia).
apply (unpoisoned_gran0 asegs _ _ _ _ _ UPB2). replace (b + (len + 1) - 1) with (b + len) by lia. lia. }
assert (HRL : exists v, ov_read_bytes asegs m2 (Z_to_bv 64 ((b + len) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 v]
/\ (v = 0 \/ (0 < v < 8 /\ (b + len) mod 8 < v))).
{ destruct (unpoisoned_last asegs _ _ _ _ UPB2) as (v0 & Hro & Hv). replace (b + (len + 1) - 1) with (b + len) in Hro, Hv by lia.
exists v0. split; [| exact Hv]. apply ov_read1_of_ro. unfold A_SB in Hro. exact Hro. }
do 2 step.
step.
step.
step.
step. replace (b + (len + 1) + -1) with (b + len) by lia.
step. do 2 step. do 2 step.
sh_norm.
replace (2147450880 + b / 8) with (b / 8 + 2147450880) by lia.
replace (2147450880 + (b + len) / 8) with ((b + len) / 8 + 2147450880) by lia.
rewrite (unsigned_lit (b / 8 + 2147450880)) by lia. rewrite (unsigned_lit ((b + len) / 8 + 2147450880)) by lia.
rewrite !land_m8_64 by lia.
do 2 step. step.

assert (LOOPG : forall (Kn : nat) (i : Z) (y3' y4' : word),
Z.to_nat ((b + len) / 8 - b / 8 - i) = Kn -> 0 <= i -> b / 8 + i < (b + len) / 8 ->
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp q0 q1 q2 w0 w1 (Z_to_bv 64 (b / 8 + 2147450880 + i)) (Z_to_bv 64 ((b + len) / 8 + 2147450880)) (Z_to_bv 64 0) y3' y4' y5 y6 y7
(Z_to_bv 64 b) w3 w4 (Z_to_bv 64 (len + 1)) w6 w7 (zxb ya) (zxb yb) w10 w11 q3 q4 q5 q6)
F (Z_to_bv 64 0x50cf8) fc None m2 (seg_rom asegs))).
{ clear Hh V1c V2c HRL.
induction Kn as [|Kn IH]; intros i y3' y4' HK Hi Hig; [lia|].
pose proof (GS0 i Hi Hig) as HR.
step. rewrite ?zxb_zero. clear HR.
step. step. rewrite ?(unsigned_lit 0) by lia. change (Z.lor 0 0) with 0.
step.
destruct (Z.eq_dec (b / 8 + i + 1) ((b + len) / 8)) as [Heq|Hne].
- if_falsex. step. step. if_true. apply TAIL.
- if_truex. replace (b / 8 + 2147450880 + i + 1) with (b / 8 + 2147450880 + (i + 1)) by lia. apply (IH (i + 1)); lia. }
step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd end.
2: { apply TAIL. }
destruct HRL as (vv & HR & Hv).
assert (Hv8 : 0 <= vv < 128) by (destruct Hv as [->|(? & ?)]; lia).
clear V1c V2c.
step. rewrite (sxb_small vv) by lia. clear HR.
step. rewrite (unsigned_lit (b + len)) by lia. rewrite land7_mod8 by lia.
step. step. step. step.
destruct Hv as [-> | (Hk & Hlast)].
- rewrite (v_sltu_0' (Z_to_bv 64 0) (Z_to_bv 64 0)) by (rewrite !unsigned_lit by lia; lia).
rewrite (unsigned_lit 0) by lia. rewrite Z.land_0_l.
step.
destruct (Z.eq_dec (b / 8) ((b + len) / 8)) as [Heq1|Hne1].
+ if_truex. step. step. if_true. apply TAIL.
+ if_falsex. replace (b / 8 + 2147450880) with (b / 8 + 2147450880 + 0) by lia.
apply (LOOPG (Z.to_nat ((b + len) / 8 - b / 8 - 0)) 0); lia.
- rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 vv)) by (rewrite !unsigned_lit by lia; lia).
rewrite (v_slt_1 (Z_to_bv 64 ((b + len) mod 8)) (Z_to_bv 64 vv)) by (rewrite !signed_lit by lia; clear Hh; Z.div_mod_to_equations; lia).
rewrite !(unsigned_lit 1) by lia. change (Z.lxor 1 1) with 0. rewrite Z.land_0_r.
step.
destruct (Z.eq_dec (b / 8) ((b + len) / 8)) as [Heq1|Hne1].
+ if_truex. step. step. if_true. apply TAIL.
+ if_falsex. replace (b / 8 + 2147450880) with (b / 8 + 2147450880 + 0) by lia.
apply (LOOPG (Z.to_nat ((b + len) / 8 - b / 8 - 0)) 0); lia. }

assert (NEXT1 : forall (xra q0 q1 q2 w0 y0 y1 y2 y3 y4 y5 y6 y7 w4 w5 w6 w7 w10 q3 q4 q5 q6 : word),
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp q0 q1 q2 w0 (Z_to_bv 64 n) y0 y1 y2 y3 y4 y5 y6 y7
(Z_to_bv 64 b) (Z_to_bv 64 a) w4 w5 w6 w7 (zxb ya) (zxb yb) w10 (Z_to_bv 64 idx) q3 q4 q5 q6)
F (Z_to_bv 64 0x50a3c) fc None m2 (seg_rom asegs))).
{ intros xra q0 q1 q2 w0 y0 y1 y2 y3 y4 y5 y6 y7 w4 w5 w6 w7 w10 q3 q4 q5 q6.
step.
step.
destruct (Z_lt_ge_dec (idx + 1) n) as [Hlt | Hge].
- if_falsex. replace (idx + 1) with (len + 1) by lia.
step. step. rewrite (unsigned_lit b) by lia. rewrite (lxor_ones64 b) by lia. if_falsex.
apply CHK2.
- if_truex.
step. replace n with (len + 1) at 2 by lia.
step. step. rewrite (unsigned_lit b) by lia. rewrite (lxor_ones64 b) by lia. if_truex.
apply CHK2. }
assert (CHK1 : forall (xra q0 q1 q2 w0 y0 y1 y2 y3 y4 y5 y6 y7 w4 w6 w7 w10 q3 q4 q5 q6 : word),
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp q0 q1 q2 w0 (Z_to_bv 64 n) y0 y1 y2 y3 y4 y5 y6 y7
(Z_to_bv 64 b) (Z_to_bv 64 a) w4 (Z_to_bv 64 (len + 1)) w6 w7 (zxb ya) (zxb yb) w10 (Z_to_bv 64 idx) q3 q4 q5 q6)
F (Z_to_bv 64 0x509f4) fc None m2 (seg_rom asegs))).
{ intros xra q0 q1 q2 w0 y0 y1 y2 y3 y4 y5 y6 y7 w4 w6 w7 w10 q3 q4 q5 q6.
step. replace (len + 1 + -65) with (len + -64) by lia.
step.
step. replace (len + -64) with ((len + 1) + -65) by lia. rewrite size_test_n by lia. cbv iota.
assert (Hh : a / 8 <= (a + len) / 8 <= a / 8 + 8) by (Z.div_mod_to_equations; lia).
destruct (unpoisoned_word asegs _ _ _ _ (a / 8 + A_SB) UPA2 ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (v1 & Lv1 & V1c).
destruct (unpoisoned_word asegs _ _ _ _ ((a + len) / 8 + A_SB) UPA2 ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (v2 & Lv2 & V2c).
unfold A_SB in V1c, V2c.
assert (GS0 : forall j, 0 <= j -> a / 8 + j < (a + len) / 8 ->
ov_read_bytes asegs m2 (Z_to_bv 64 (a / 8 + 2147450880 + j)) 1 = Some [Z_to_bv 8 0]).
{ intros j Hj Hjl. apply ov_read1_of_ro.
replace (a / 8 + 2147450880 + j) with ((a / 8 + j) + A_SB) by (unfold A_SB; lia).
apply (unpoisoned_gran0 asegs _ _ _ _ _ UPA2). replace (a + (len + 1) - 1) with (a + len) by lia. lia. }
assert (HRL : exists v, ov_read_bytes asegs m2 (Z_to_bv 64 ((a + len) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 v]
/\ (v = 0 \/ (0 < v < 8 /\ (a + len) mod 8 < v))).
{ destruct (unpoisoned_last asegs _ _ _ _ UPA2) as (v0 & Hro & Hv). replace (a + (len + 1) - 1) with (a + len) in Hro, Hv by lia.
exists v0. split; [| exact Hv]. apply ov_read1_of_ro. unfold A_SB in Hro. exact Hro. }
do 2 step.
step.
step.
step.
step. replace (a + (len + 1) + -1) with (a + len) by lia.
step. do 2 step. do 2 step.
sh_norm.
replace (2147450880 + a / 8) with (a / 8 + 2147450880) by lia.
replace (2147450880 + (a + len) / 8) with ((a + len) / 8 + 2147450880) by lia.
rewrite (unsigned_lit (a / 8 + 2147450880)) by lia. rewrite (unsigned_lit ((a + len) / 8 + 2147450880)) by lia.
rewrite !land_m8_64 by lia.
do 2 step. step.

assert (LOOPG : forall (Kn : nat) (i : Z) (y3' y4' : word),
Z.to_nat ((a + len) / 8 - a / 8 - i) = Kn -> 0 <= i -> a / 8 + i < (a + len) / 8 ->
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp q0 q1 q2 w0 (Z_to_bv 64 n) (Z_to_bv 64 (a / 8 + 2147450880 + i)) (Z_to_bv 64 ((a + len) / 8 + 2147450880)) (Z_to_bv 64 0) y3' y4' y5 y6 y7
(Z_to_bv 64 b) (Z_to_bv 64 a) w4 (Z_to_bv 64 (len + 1)) w6 w7 (zxb ya) (zxb yb) w10 (Z_to_bv 64 idx) q3 q4 q5 q6)
F (Z_to_bv 64 0x50c30) fc None m2 (seg_rom asegs))).
{ clear Hh V1c V2c HRL.
induction Kn as [|Kn IH]; intros i y3' y4' HK Hi Hig; [lia|].
pose proof (GS0 i Hi Hig) as HR.
step. rewrite ?zxb_zero. clear HR.
step. step. rewrite ?(unsigned_lit 0) by lia. change (Z.lor 0 0) with 0.
step.
destruct (Z.eq_dec (a / 8 + i + 1) ((a + len) / 8)) as [Heq|Hne].
- if_falsex. step. step. if_true. apply NEXT1.
- if_truex. replace (a / 8 + 2147450880 + i + 1) with (a / 8 + 2147450880 + (i + 1)) by lia. apply (IH (i + 1)); lia. }
step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd end.
2: { apply NEXT1. }
destruct HRL as (vv & HR & Hv).
assert (Hv8 : 0 <= vv < 128) by (destruct Hv as [->|(? & ?)]; lia).
clear V1c V2c.
step. rewrite (sxb_small vv) by lia. clear HR.
step. rewrite (unsigned_lit (a + len)) by lia. rewrite land7_mod8 by lia.
step. step. step. step.
destruct Hv as [-> | (Hk & Hlast)].
- rewrite (v_sltu_0' (Z_to_bv 64 0) (Z_to_bv 64 0)) by (rewrite !unsigned_lit by lia; lia).
rewrite (unsigned_lit 0) by lia. rewrite Z.land_0_l.
step.
destruct (Z.eq_dec (a / 8) ((a + len) / 8)) as [Heq1|Hne1].
+ if_truex. step. step. if_true. apply NEXT1.
+ if_falsex. replace (a / 8 + 2147450880) with (a / 8 + 2147450880 + 0) by lia.
apply (LOOPG (Z.to_nat ((a + len) / 8 - a / 8 - 0)) 0); lia.
- rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 vv)) by (rewrite !unsigned_lit by lia; lia).
rewrite (v_slt_1 (Z_to_bv 64 ((a + len) mod 8)) (Z_to_bv 64 vv)) by (rewrite !signed_lit by lia; clear Hh; Z.div_mod_to_equations; lia).
rewrite !(unsigned_lit 1) by lia. change (Z.lxor 1 1) with 0. rewrite Z.land_0_r.
step.
destruct (Z.eq_dec (a / 8) ((a + len) / 8)) as [Heq1|Hne1].
+ if_truex. step. step. if_true. apply NEXT1.
+ if_falsex. replace (a / 8 + 2147450880) with (a / 8 + 2147450880 + 0) by lia.
apply (LOOPG (Z.to_nat ((a + len) / 8 - a / 8 - 0)) 0); lia. }

step.
destruct (Z_lt_ge_dec idx n) as [Hlt | Hge].
-
if_falsex.
do 2 step.
step. rewrite ?zxb_zero.
step.
step. change (Z.land (bv_unsigned (Z_to_bv 64 0)) 1) with 0.
step. if_true.
step.
step.
destruct (Z_lt_ge_dec (idx + 1) n) as [Hlt1 | Hge1].
+ if_falsex. replace (idx + 1) with (len + 1) by lia.
step. step. step.
step. rewrite (unsigned_lit a) by lia. rewrite (lxor_ones64 a) by lia. if_falsex.
apply CHK1.
+ if_truex.
step. replace n with (len + 1) at 2 by lia.
step. step. step.
step. rewrite (unsigned_lit a) by lia. rewrite (lxor_ones64 a) by lia. if_truex.
apply CHK1.
-
if_truex.
step.
step. if_falsex.
step. replace n with (len + 1) at 2 by lia.
step. step. step.
step. rewrite (unsigned_lit a) by lia. rewrite (lxor_ones64 a) by lia. if_truex.
apply CHK1.
Qed.
End RC__1.
