(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Q5Rg Lib.GwApply QRjH QHnV QCcH QfLs Q0Ek QTEu Qsw7 QJjn QnCn QZCq Q7UD Qhd4 Qwm6 QlKV QsKa Q30W Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek. Import QTEu. Import Qsw7 QJjn.
Import QnCn.Mq0. Import QZCq.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mq7 QlKV.Mqa QsKa.Mq7 QsKa.Mq3 Q30W.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section AAlFree.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Definition array_list_free_A_entry : Z := 0xa0488.

Lemma al_free_loopA :
forall (k : nat) (i : Z) (x1 x2 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x25 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a arr len size : Z) (ps : list Z),
Z.of_nat k = len - 1 - i -> 0 <= i < len -> len = Z.of_nat (length ps) -> 8 * len < 2^64 -> len <= size ->
Forall (fun p => p = 0) ps ->
mem_inv asegs m -> 0 < a -> a mod 8 = 0 -> a + AL_SZ <= alloc_ceiling -> 0 < arr -> arr mod 8 = 0 -> arr + 8 * size <= alloc_ceiling ->
rw_cells asegs m a [C8 (Z_to_bv 64 arr); C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 (fn_arr_entry_free A4F))] ->
u64arr asegs m arr (wl ps) ->
ro_cells asegs m (a / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
bytes_at asegs m (arr / 8 + A_SB) (shadow_bytes (8 * size)) ->
evt asegs (eq (MS (mkR x1 x2 gp tp t0 t1 t2 (Z_to_bv 64 a) (Z_to_bv 64 (a + 8)) (Z_to_bv 64 len) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (a + 24)) (Z_to_bv 64 A_SB) (Z_to_bv 64 (a / 8 + 2147450881))  (Z_to_bv 64 (a / 8)) (Z_to_bv 64 (8 * len)) (Z_to_bv 64 len)
(Z_to_bv 64 (a / 8 + A_SB)) x25 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa0550) fc None m (seg_rom asegs)))
(MS (mkR x1 x2 gp tp t0 t1 t2 (Z_to_bv 64 a) (Z_to_bv 64 (a + 8)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (a + 24)) (Z_to_bv 64 A_SB) (Z_to_bv 64 (a / 8 + 2147450881)) (Z_to_bv 64 (a / 8)) (Z_to_bv 64 (8 * i)) (Z_to_bv 64 i)
(Z_to_bv 64 (a / 8 + A_SB)) x25 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa0500) fc None m (seg_rom asegs)).
Proof.
induction k as [|k IH]; intros until ps; intros Hk Hi Hlen H64 Hls NUL MI Ha0 Ha8 Hah Hr0 Hr8 Hrh HDR ARR SHa SHr; unfold A_SB in *;
pose proof (u64arr_bound asegs m arr (wl ps) ARR) as AB; rewrite wl_length in AB;
pose proof (munch_refl [] m) as MU; pose proof (wmono_refl asegs m) as WM;
pose proof (ov_read1_of_ro asegs _ _ _ (shadow_granule0 asegs m (arr / 8 + 2147450880) (8 * size) i ltac:(lia) ltac:(lia) SHr)) as HR.
- step. rewrite ?zxb_zero. step. if_false.
step. step.
step. step. sh_norm.
replace ((arr + 8 * i) / 8 + 2147450880) with (arr / 8 + 2147450880 + i) by (Z.div_mod_to_equations; lia).
step. rewrite ?zxb_zero. clear HR. step. if_false.
pose proof (al_slot_read asegs m arr ps i (wa (arr + 8 * i)) ARR ltac:(lia) eq_refl) as RD.
rewrite (al_nth_null ps i NUL) in RD.
step. step. if_true.
step. rewrite ?zxb_zero. step. if_false.
step. step. step. step. if_falsex.
apply evt_done. replace (i + 1) with len by lia. replace (8 * i + 8) with (8 * len) by lia. reflexivity.
- step. rewrite ?zxb_zero. step. if_false.
step. step.
step. step. sh_norm.
replace ((arr + 8 * i) / 8 + 2147450880) with (arr / 8 + 2147450880 + i) by (Z.div_mod_to_equations; lia).
step. rewrite ?zxb_zero. clear HR. step. if_false.
pose proof (al_slot_read asegs m arr ps i (wa (arr + 8 * i)) ARR ltac:(lia) eq_refl) as RD.
rewrite (al_nth_null ps i NUL) in RD.
step. step. if_true.
step. rewrite ?zxb_zero. step. if_false.
step. step. step. step. if_truex.
replace (8 * i + 8) with (8 * (i + 1)) by lia.
eapply (IH (i + 1)); [ | | exact Hlen | | | exact NUL | exact MI | | | | | | | exact HDR | exact ARR | exact SHa | exact SHr]; lia.
Qed.

Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud) (lo a : Z) (T : TSet).

Definition array_list_free_A_post (u : uwd) (errv : word) (ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : word) (B' : bud),
ret_statew A4H ra sp gp (Z_to_bv 64 A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' /\
model_vm_only (cfg_model md0) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m' /\
rw_cells asegs m' A_ERRNO [C4 errv] /\
bB B0 - 1024 <= bB B' /\ bD B0 - uw_cost u <= bD B' /\
HEAPAx A' LB LM FRS B' m' md'.

Lemma al_free_tailA :
forall (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x20 x22 x23 x24 x25 t3 t4 t5 t6 : word)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (arr len size : Z) (errv : word) (fjunk : list byte) (u : uwd),
HEAPAx A ((a, AL_SZ) :: (arr, 8 * size) :: LB) LM FRS B0 m md ->
uw_at (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok A4L (hl_free A4H) ra u ->
al_hdr asegs A4F m a arr len size ->
stk asegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -96 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m (bv_unsigned sp + -96) [CB 8 fjunk; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs m A_ERRNO [C4 errv] ->
bv_unsigned ra mod 2 = 0 ->
model_vm_only (cfg_model md0) (cfg_model md) -> heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m ->
1024 <= bB B0 -> uw_cost u <= bD B0 ->
(forall ms' md' A', array_list_free_A_post u errv ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 a) x9 a0 a1 a2 a3 a4 a5 a6 a7
x18 (Z_to_bv 64 A_SB) x20 (Z_to_bv 64 (a / 8)) x22 x23 x24 x25 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa0550) fc None m (seg_rom asegs)).
Proof.
intros until u. intros HP UW UWK HDR ST LO LOS SPA HT FR ERR RA VM0 HPR BB BD K.
unfold al_hdr in HDR. unfold_consts. unfold A_SB, A_TP, A_ERRNO in *. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
blk_factsA A4L HIx HP a 32 Hal Hlo Hhi Himg.
blk_factsA A4L HIx HP arr (8 * size) Hral Hrlo Hrhi Hrimg.
assert (Hne : a <> arr).
{ intros E. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. cbn in ND. inversion ND as [|x l Hni Hnd]; subst. apply Hni. left. reflexivity. }
shadow_nowA A4L HIx HP a 32 SHa.
a4l.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp)] m) as MU.
reenterA asegs A4L HIx asegs_wx HP.
step.
try replace (a / 8 + 2147450880) with (a / 8 + 2147450880) by lia.
step. rewrite ?zxb_zero. step. if_false.
step. step.

clear SHa.
alloc_callA (hiA_free A4L HIx) blk arr uw UWptr A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists (8 * size). right; left. reflexivity. }
all: try (cbn [uw_pre uw_ok uw_key uw_cost]; intros _; split; [left; lia | unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (destruct (Z.eqb_spec arr 0); destruct u; cbn [bB bD charge uw_cost] in *; lia).
intros ms2 m2 md2 A2 r2 RS VM2 ST2 HPR2 ERR2 HP2. open_ret RS. a4l.
rewrite lb_remove_other in HPR2, HP2 by (cbn; lia). rewrite lb_remove_head in HPR2, HP2.
replace (if arr =? 0 then 0 else uw_cost UWptr) with 0 in HP2 by (destruct (Z.eqb_spec arr 0); reflexivity).
assert (UW2 : uw_at (hiA_top A4L HIx) m2 (bv_unsigned sp) (bv_unsigned s0) u).
{ eapply uw_at_heap_pres; [| exact HPR2 | lia]. eapply (uw_at_mono _ _ _ _ _ _ _ _ UW MU); [| lia].
apply Forall_cons; [cbn; lia | apply Forall_nil]. }
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST HDR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
do 13 step.
release_frame FR ST2 (bv_unsigned sp).
step.
alloc_callA (hiA_free A4L HIx) blk a uw u A4L HIx HP2 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists 32. left. reflexivity. }
all: try (eapply uw_at_pre0; [exact UW2 | lia]). all: try exact UWK.
all: try (intros _; split; [eapply uw_at_pre0; [exact UW2 | lia] | exact UWK]).
all: try (destruct (Z.eqb_spec a 0); destruct u; cbn [bB bD charge uw_cost] in *; lia).
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. a4l.
rewrite lb_remove_head in HP3, HPR3.
replace (if a =? 0 then 0 else uw_cost u) with (uw_cost u) in HP3 by (destruct (Z.eqb_spec a 0); [lia | reflexivity]).
extend_presA A4L HIx HPR MU WM HP2 HPR3.
apply K. unfold array_list_free_A_post.
exists m3, r3, (charge (charge B0 512 0) 512 (uw_cost u)).
split; [apply ret_statew_same|]. split; [eapply model_vm_only_trans; [exact VM0|]; eapply model_vm_only_trans; eassumption|].
split; [exact ST3|]. split; [exact HPR|]. split; [exact ERR3|]. split; [cbn [bB charge]; lia|]. split; [cbn [bD charge]; lia|]. exact HP3.
Qed.

Lemma array_list_free_A_cps :
forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
(A : ASA A4L HIx) (BS : list blk) (ps : list Z) (errv : word) (u : uwd),
HEAPAx A (BS ++ LB) LM FRS B0 m0 md0 ->
uw_at (hiA_top A4L HIx) m0 (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok A4L (hl_free A4H) ra u ->
alist asegs A4F m0 BS a ps -> Forall (fun p => p = 0) ps ->
stk asegs m0 lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m0 A_ERRNO [C4 errv] ->
bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 a ->
1024 <= bB B0 -> uw_cost u <= bD B0 ->
(forall ms' md' A', array_list_free_A_post u errv ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md0
(MS (mkR ra sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 array_list_free_A_entry) fc None m0 (seg_rom asegs)).
Proof.
intros until u. intros HP UW UWK AL NUL ST LO LOS SPA HT ERR RA A0 BB BD K.
destruct (alist_open asegs A4F m0 BS a ps AL) as (arr & size & junk & -> & HDR & ARR & JK & Hlen & Hsz).
cbn [app] in HP. unfold al_hdr in HDR.
unfold_consts. unfold A_SB, A_TP, A_ERRNO, array_list_free_A_entry in *. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
blk_factsA A4L HIx HP a 32 Hal Hlo Hhi Himg.
blk_factsA A4L HIx HP arr (8 * size) Hral Hrlo Hrhi Hrimg.
shadow_nowA A4L HIx HP a 32 SHa.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ arr (8 * size) HP ltac:(right; left; reflexivity)) as SHr. unfold shad in SHr.
a4l.
pose proof (u64arr_bound asegs m0 arr (wl ps) ARR) as AB. rewrite wl_length in AB.
pose proof (wl_length ps) as WL.
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0) as HPR.
pose proof (wmono_refl asegs m0) as WM.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m0) as MU.
apply slots_of_u64arr in ARR. stash SHr. stash ARR. clear JK.
reenterA asegs A4L HIx asegs_wx HP. subst a0.
carve_frame 96%nat ST.
do 12 step.
step. step. step.
step. step.
asan_chkA.
step.
step. sh_norm.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.

assert (HP1 : HEAPAx A ((a, 32) :: (arr, 8 * size) :: LB) LM FRS B0 m1 md0) by heap_nowA A4L HIx HP MU WM MI.
assert (UW1 : uw_at (hiA_top A4L HIx) m1 (bv_unsigned sp) (bv_unsigned s0) u).
{ eapply (uw_at_mono _ _ _ _ _ _ _ _ UW MU); [| lia]. apply Forall_cons; [cbn; lia | apply Forall_nil]. }
assert (HPR1 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m1).
{ eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; right; right; exact Hb | clia | solve_clientWA A4L HIx HP]. }
step.
destruct (Z.eq_dec (Z.of_nat (length ps)) 0) as [Z0|NZ].
- rewrite Z0. if_true.
evt_done5.
eapply (al_free_tailA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 md0 A arr 0 size errv _ u);
[exact HP1 | exact UW1 | exact UWK | unfold al_hdr; rewrite <- Z0; assumption | exact ST | clia | clia | exact SPA | exact HT
| exact FR | assumption | exact RA | apply model_vm_only_refl | exact HPR1 | exact BB | exact BD | exact K].
- if_falsex.
step. step. step.
step. step. step. sh_norm.
unstash SHr. unstash ARR.
eapply (rw_cells_transport asegs _ m0 m1) in ARR; [| exact MU | exact WM | cbn [disjoint_from]; rewrite slots_size; lia].
eapply (bytes_at_transport asegs _ m0 m1) in SHr; [| exact MU | cbn [disjoint_from]; rewrite shadow_bytes_length8 by lia; lia].
eapply evt_cut.
{ replace (Z_to_bv 64 0) with (Z_to_bv 64 (8 * 0)) by reflexivity.
eapply (al_free_loopA (Z.to_nat (Z.of_nat (length ps) - 1)) 0);
[ | | reflexivity | | exact Hlen | exact NUL | assumption | | | | | |
| exact HDR | apply u64arr_of_slots; exact ARR | unfold A_SB; eassumption | unfold A_SB; exact SHr ]; clia. }
intros ms' <-.
evt_done5.
eapply (al_free_tailA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 md0 A arr (Z.of_nat (length ps)) size errv _ u);
[exact HP1 | exact UW1 | exact UWK | unfold al_hdr; assumption | exact ST | clia | clia | exact SPA | exact HT
| exact FR | assumption | exact RA | apply model_vm_only_refl | exact HPR1 | exact BB | exact BD | exact K].
Qed.
End AAlFree.
End RC__1.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnCn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnCn.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZCq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZCq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRBl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q30W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q30W.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section AAlFree.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Definition array_list_free_A_entry : Z := 0xa2370.

Lemma al_free_loopA :
forall (k : nat) (i : Z) (x1 x2 gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x24 x25 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a arr len size : Z) (ps : list Z),
Z.of_nat k = len - 1 - i -> 0 <= i < len -> len = Z.of_nat (length ps) -> 8 * len < 2^64 -> len <= size ->
Forall (fun p => p = 0) ps ->
mem_inv asegs m -> 0 < a -> a mod 8 = 0 -> a + AL_SZ <= alloc_ceiling -> 0 < arr -> arr mod 8 = 0 -> arr + 8 * size <= alloc_ceiling ->
rw_cells asegs m a [C8 (Z_to_bv 64 arr); C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 (fn_arr_entry_free A4F))] ->
u64arr asegs m arr (wl ps) ->
ro_cells asegs m (a / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
bytes_at asegs m (arr / 8 + A_SB) (shadow_bytes (8 * size)) ->
evt asegs (eq (MS (mkR x1 x2 gp tp t0 t1 t2 (Z_to_bv 64 a) (Z_to_bv 64 (a + 8)) (Z_to_bv 64 arr) (Z_to_bv 64 len) (Z_to_bv 64 0) (Z_to_bv 64 0) a4 a5 a6 a7
(Z_to_bv 64 (a + 24)) (Z_to_bv 64 A_SB) (Z_to_bv 64 (a / 8 + 2147450881)) (Z_to_bv 64 (a / 8 + A_SB)) (Z_to_bv 64 (8 * len)) (Z_to_bv 64 len)
x24 x25 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa2474) fc None m (seg_rom asegs)))
(MS (mkR x1 x2 gp tp t0 t1 t2 (Z_to_bv 64 a) (Z_to_bv 64 (a + 8)) (Z_to_bv 64 arr) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (a + 24)) (Z_to_bv 64 A_SB) (Z_to_bv 64 (a / 8 + 2147450881)) (Z_to_bv 64 (a / 8 + A_SB)) (Z_to_bv 64 (8 * i)) (Z_to_bv 64 i)
x24 x25 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa23fc) fc None m (seg_rom asegs)).
Proof.
induction k as [|k IH]; intros until ps; intros Hk Hi Hlen H64 Hls NUL MI Ha0 Ha8 Hah Hr0 Hr8 Hrh HDR ARR SHa SHr; unfold A_SB in *;
pose proof (u64arr_bound asegs m arr (wl ps) ARR) as AB; rewrite wl_length in AB;
pose proof (munch_refl [] m) as MU; pose proof (wmono_refl asegs m) as WM;
pose proof (ov_read1_of_ro asegs _ _ _ (shadow_granule0 asegs m (arr / 8 + 2147450880) (8 * size) i ltac:(lia) ltac:(lia) SHr)) as HR;
pose proof (al_slot_read asegs m arr ps i (wa (arr + 8 * i)) ARR ltac:(lia) eq_refl) as RD; rewrite (al_nth_null ps i NUL) in RD.
- step.
step. step. step. ub_resolve.
step. step. ub_resolve.
step. ub_resolve.
step. ub_resolve.
step. step. step. ub_resolve.
step. step. sh_norm.
replace ((arr + 8 * i) / 8 + 2147450880) with (arr / 8 + 2147450880 + i) by (Z.div_mod_to_equations; lia).
step. rewrite ?zxb_zero. clear HR. step. if_false.
step. step. if_true.
step. rewrite ?zxb_zero. step. if_false.
step. rewrite ?zxb_zero. step. if_false.
step. step. step. step. step. if_falsex.
ub_cmp_norm.
apply evt_done. replace (i + 1) with len by lia. replace (8 * i + 8) with (8 * len) by lia. reflexivity.
- step.
step. step. step. ub_resolve.
step. step. ub_resolve.
step. ub_resolve.
step. ub_resolve.
step. step. step. ub_resolve.
step. step. sh_norm.
replace ((arr + 8 * i) / 8 + 2147450880) with (arr / 8 + 2147450880 + i) by (Z.div_mod_to_equations; lia).
step. rewrite ?zxb_zero. clear HR. step. if_false.
step. step. if_true.
step. rewrite ?zxb_zero. step. if_false.
step. rewrite ?zxb_zero. step. if_false.
step. step. step. step. step. if_truex.
replace (8 * i + 8) with (8 * (i + 1)) by lia.
eapply (IH (i + 1)); [ | | exact Hlen | | | exact NUL | exact MI | | | | | | | exact HDR | exact ARR | exact SHa | exact SHr]; lia.
Qed.

Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud) (lo a : Z) (T : TSet).

Definition array_list_free_A_post (u : uwd) (errv : word) (ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : word) (B' : bud),
ret_statew A4H ra sp gp (Z_to_bv 64 A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' /\
model_vm_only (cfg_model md0) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m' /\
rw_cells asegs m' A_ERRNO [C4 errv] /\
bB B0 - 1024 <= bB B' /\ bD B0 - uw_cost u <= bD B' /\
HEAPAx A' LB LM FRS B' m' md'.

Lemma al_free_tailA :
forall (x1 t0 t1 t2 x9 a1 a2 a3 a4 a5 a6 a7 x18 x20 x21 x22 x23 x24 t3 t4 t5 t6 : word)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (arr len size : Z) (errv : word) (u : uwd),
HEAPAx A ((a, AL_SZ) :: (arr, 8 * size) :: LB) LM FRS B0 m md ->
uw_at (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok A4L (hl_free A4H) ra u ->
al_hdr asegs A4F m a arr len size ->
stk asegs m lo (bv_unsigned sp + -80) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -80 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m (bv_unsigned sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs m A_ERRNO [C4 errv] ->
bv_unsigned ra mod 2 = 0 ->
model_vm_only (cfg_model md0) (cfg_model md) -> heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m ->
1024 <= bB B0 -> uw_cost u <= bD B0 ->
(forall ms' md' A', array_list_free_A_post u errv ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 a) x9 (Z_to_bv 64 arr) a1 a2 a3 a4 a5 a6 a7
x18 (Z_to_bv 64 A_SB) x20 x21 x22 x23 x24 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa2474) fc None m (seg_rom asegs)).
Proof.
intros until u. intros HP UW UWK HDR ST LO LOS SPA HT FR ERR RA VM0 HPR BB BD K.
unfold al_hdr in HDR. unfold_consts. unfold A_SB, A_TP, A_ERRNO in *. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
blk_factsA A4L HIx HP a 32 Hal Hlo Hhi Himg.
blk_factsA A4L HIx HP arr (8 * size) Hral Hrlo Hrhi Hrimg.
assert (Hne : a <> arr).
{ intros E. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. cbn in ND. inversion ND as [|x l Hni Hnd]; subst. apply Hni. left. reflexivity. }
a4l.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -80, bv_unsigned sp)] m) as MU.
reenterA asegs A4L HIx asegs_wx HP.
step.

alloc_callA (hiA_free A4L HIx) blk arr uw UWptr A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists (8 * size). right; left. reflexivity. }
all: try (cbn [uw_pre uw_ok uw_key uw_cost]; intros _; split; [left; lia | unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (destruct (Z.eqb_spec arr 0); destruct u; cbn [bB bD charge uw_cost] in *; lia).
intros ms2 m2 md2 A2 r2 RS VM2 ST2 HPR2 ERR2 HP2. open_ret RS. a4l.
rewrite lb_remove_other in HPR2, HP2 by (cbn; lia). rewrite lb_remove_head in HPR2, HP2.
replace (if arr =? 0 then 0 else uw_cost UWptr) with 0 in HP2 by (destruct (Z.eqb_spec arr 0); reflexivity).
assert (UW2 : uw_at (hiA_top A4L HIx) m2 (bv_unsigned sp) (bv_unsigned s0) u).
{ eapply uw_at_heap_pres; [| exact HPR2 | lia]. eapply (uw_at_mono _ _ _ _ _ _ _ _ UW MU); [| lia].
apply Forall_cons; [cbn; lia | apply Forall_nil]. }
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST HDR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
pose proof (munch_refl [(bv_unsigned sp + -80, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
do 12 step.
release_frame FR ST2 (bv_unsigned sp).
step.
alloc_callA (hiA_free A4L HIx) blk a uw u A4L HIx HP2 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists 32. left. reflexivity. }
all: try (eapply uw_at_pre0; [exact UW2 | lia]). all: try exact UWK.
all: try (intros _; split; [eapply uw_at_pre0; [exact UW2 | lia] | exact UWK]).
all: try (destruct (Z.eqb_spec a 0); destruct u; cbn [bB bD charge uw_cost] in *; lia).
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. a4l.
rewrite lb_remove_head in HP3, HPR3.
replace (if a =? 0 then 0 else uw_cost u) with (uw_cost u) in HP3 by (destruct (Z.eqb_spec a 0); [lia | reflexivity]).
extend_presA A4L HIx HPR MU WM HP2 HPR3.
apply K. unfold array_list_free_A_post.
exists m3, r3, (charge (charge B0 512 0) 512 (uw_cost u)).
split; [apply ret_statew_same|]. split; [eapply model_vm_only_trans; [exact VM0|]; eapply model_vm_only_trans; eassumption|].
split; [exact ST3|]. split; [exact HPR|]. split; [exact ERR3|]. split; [cbn [bB charge]; lia|]. split; [cbn [bD charge]; lia|]. exact HP3.
Qed.

Lemma array_list_free_A_cps :
forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
(A : ASA A4L HIx) (BS : list blk) (ps : list Z) (errv : word) (u : uwd),
HEAPAx A (BS ++ LB) LM FRS B0 m0 md0 ->
uw_at (hiA_top A4L HIx) m0 (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok A4L (hl_free A4H) ra u ->
alist asegs A4F m0 BS a ps -> Forall (fun p => p = 0) ps ->
stk asegs m0 lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m0 A_ERRNO [C4 errv] ->
bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 a ->
1024 <= bB B0 -> uw_cost u <= bD B0 ->
(forall ms' md' A', array_list_free_A_post u errv ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md0
(MS (mkR ra sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 array_list_free_A_entry) fc None m0 (seg_rom asegs)).
Proof.
intros until u. intros HP UW UWK AL NUL ST LO LOS SPA HT ERR RA A0 BB BD K.
destruct (alist_open asegs A4F m0 BS a ps AL) as (arr & size & junk & -> & HDR & ARR & JK & Hlen & Hsz).
cbn [app] in HP. unfold al_hdr in HDR.
unfold_consts. unfold A_SB, A_TP, A_ERRNO, array_list_free_A_entry in *. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
blk_factsA A4L HIx HP a 32 Hal Hlo Hhi Himg.
blk_factsA A4L HIx HP arr (8 * size) Hral Hrlo Hrhi Hrimg.
shadow_nowA A4L HIx HP a 32 SHa.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ arr (8 * size) HP ltac:(right; left; reflexivity)) as SHr. unfold shad in SHr.
a4l.
pose proof (u64arr_bound asegs m0 arr (wl ps) ARR) as AB. rewrite wl_length in AB.
pose proof (wl_length ps) as WL.
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0) as HPR.
pose proof (wmono_refl asegs m0) as WM.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m0) as MU.
apply slots_of_u64arr in ARR. stash SHr. stash ARR. clear JK.
reenterA asegs A4L HIx asegs_wx HP. subst a0.
carve_frame 80%nat ST.
do 11 step.
step. ub_resolve.
step. step. step. ub_resolve.
step. step. step.
step.
asan_chkA.
step. sh_norm.
step. step. rewrite ?zxb_zero. step. if_false.
step. step.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.

assert (HP1 : HEAPAx A ((a, 32) :: (arr, 8 * size) :: LB) LM FRS B0 m1 md0) by heap_nowA A4L HIx HP MU WM MI.
assert (UW1 : uw_at (hiA_top A4L HIx) m1 (bv_unsigned sp) (bv_unsigned s0) u).
{ eapply (uw_at_mono _ _ _ _ _ _ _ _ UW MU); [| lia]. apply Forall_cons; [cbn; lia | apply Forall_nil]. }
assert (HPR1 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m1).
{ eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; right; right; exact Hb | clia | solve_clientWA A4L HIx HP]. }
step.
destruct (Z.eq_dec (Z.of_nat (length ps)) 0) as [Z0|NZ].
- rewrite Z0. if_true.
evt_done5.
eapply (al_free_tailA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 md0 A arr 0 size errv u);
[exact HP1 | exact UW1 | exact UWK | unfold al_hdr; rewrite <- Z0; assumption | exact ST | clia | clia | exact SPA | exact HT
| exact FR | assumption | exact RA | apply model_vm_only_refl | exact HPR1 | exact BB | exact BD | exact K].
- if_falsex.
step. step. step.
step. step. sh_norm.
unstash SHr. unstash ARR.
eapply (rw_cells_transport asegs _ m0 m1) in ARR; [| exact MU | exact WM | cbn [disjoint_from]; rewrite slots_size; lia].
eapply (bytes_at_transport asegs _ m0 m1) in SHr; [| exact MU | cbn [disjoint_from]; rewrite shadow_bytes_length8 by lia; lia].
eapply evt_cut.
{ replace (Z_to_bv 64 0) with (Z_to_bv 64 (8 * 0)) by reflexivity.
eapply (al_free_loopA (Z.to_nat (Z.of_nat (length ps) - 1)) 0);
[ | | reflexivity | | exact Hlen | exact NUL | assumption | | | | | |
| exact HDR | apply u64arr_of_slots; exact ARR | unfold A_SB; eassumption | unfold A_SB; exact SHr ]; clia. }
intros ms' <-.
evt_done5.
eapply (al_free_tailA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 md0 A arr (Z.of_nat (length ps)) size errv u);
[exact HP1 | exact UW1 | exact UWK | unfold al_hdr; assumption | exact ST | clia | clia | exact SPA | exact HT
| exact FR | assumption | exact RA | apply model_vm_only_refl | exact HPR1 | exact BB | exact BD | exact K].
Qed.
End AAlFree.
End RC__1.
