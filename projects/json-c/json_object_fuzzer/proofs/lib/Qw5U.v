(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Qfw3_c1 QRjH QHnV QCcH QfLs Q7UD Qhd4 Qwm6 QlKV QsKa Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Qfw3_c1.Mq2.
Import QRjH.
Import QHnV QCcH QfLs.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa.

Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition stack_malloc_full_stmt (HIx : heap_iface_A A4L) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FR : list frame) (B : bud) (k bytes lo : Z),
HEAPA A4L HIx A LB LM FR B m c ->
(0 <= k <= 2 \/ (k = 3 /\ hl_stack_malloc A4L 3 <> 0 /\ Z.of_nat (length FR) < 2048)) -> 1 <= bytes <= fr_size k -> bytes mod 8 = 0 ->
(Z.of_nat (length FR) < 4096) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A A4L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top A4L HIx + 64 ->
tp = Z_to_bv 64 (hl_tp A4L) ->
a0 = Z_to_bv 64 bytes ->
(forall ms' m' c' (A' : ASA A4L HIx) (Fr : Z),
ret_state A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 Fr) m' ms' ->
model_vm_only (cfg_model c) (cfg_model c') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FR) (bv_unsigned sp) m m' ->
Fr <> 0 ->
(exists junk, rw_cells asegs m' Fr [CB (Z.to_nat (fr_size k - 8)) junk]) ->
bytes_at asegs m' (shad A4L Fr) (repeat (Z_to_bv 8 0) (Z.to_nat (fr_shadow_len k))) ->
HEAPA A4L HIx A' LB LM ((Fr, k) :: FR) B m' c' ->
AJ5 A4L HIx A' T c' ms') ->
AJ5 A4L HIx A T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_stack_malloc A4L k)) fc None m (seg_rom asegs)).

Lemma stack_malloc_full : forall HIx : heap_iface_A A4L, stack_malloc_full_stmt HIx.
Proof. intros HIx. unfold stack_malloc_full_stmt. exact (hiA_stack_malloc A4L HIx). Qed.

Lemma frame_above_img : forall (HIx : heap_iface_A A4L) A LB LM FR B m md F k, HEAPA A4L HIx A LB LM FR B m md -> In (F, k) FR -> hl_img_hi A4H <= F.
Proof. intros HIx A LB LM FR B m md F k HP Hin. exact (heapA_frame_above A4L HIx _ _ _ _ _ _ _ _ _ HP Hin). Qed.

Lemma rtc_cell : forall (HIx : heap_iface_A A4L) A LB LM FR B m md a bs,
HEAPA A4L HIx A LB LM FR B m md -> In (a, bs) a4_rt_consts -> bytes_at asegs m a bs.
Proof.
intros HIx A LB LM FR B m md a bs HP Hin. pose proof (heapA_rtc A4L HIx _ _ _ _ _ _ _ HP) as R. rewrite Forall_forall in R.
exact (R (a, bs) Hin).
Qed.

Lemma bytes_at_subG : forall segs m a (bs : list byte) k j, bytes_at segs m a bs -> (k + j <= length bs)%nat ->
bytes_at segs m (a + Z.of_nat k) (firstn j (skipn k bs)).
Proof.
intros segs m a bs k j (Ha & Hl & H) Hkj. split; [lia|]. split; [rewrite length_firstn, length_skipn; lia|].
intros i Hi. rewrite length_firstn, length_skipn in Hi.
replace (a + Z.of_nat k + Z.of_nat i) with (a + Z.of_nat (k + i)) by lia. rewrite (H (k + i)%nat) by lia.
rewrite nth_error_firstn. replace (i <? j)%nat with true by (symmetry; apply Nat.ltb_lt; lia). rewrite nth_error_skipn. reflexivity.
Qed.

Lemma unpoisoned_gran8 : forall segs m SB E (wb : list byte),
E mod 8 = 0 -> 0 <= E -> 0 <= SB ->
length wb = 8%nat ->
bytes_at segs m ((E / 8 + SB) / 8 * 8) wb ->
nth_error wb (Z.to_nat ((E / 8 + SB) mod 8)) = Some (Z_to_bv 8 0) ->
unpoisoned segs m SB E 8.
Proof.
intros segs m SB E wb HE8 HE0 HSB HL HB HN.
split; [lia|]. split; [intros g Hg; exfalso; Z.div_mod_to_equations; lia|]. split.
- exists 0. split; [| left; reflexivity].
pose proof (bytes_at_subG segs m _ wb (Z.to_nat ((E / 8 + SB) mod 8)) 1 HB ltac:(rewrite HL; Z.div_mod_to_equations; lia)) as X.
replace ((E / 8 + SB) / 8 * 8 + Z.of_nat (Z.to_nat ((E / 8 + SB) mod 8))) with ((E + 8 - 1) / 8 + SB) in X by (Z.div_mod_to_equations; lia).
assert (EQ : firstn 1 (skipn (Z.to_nat ((E / 8 + SB) mod 8)) wb) = [Z_to_bv 8 0]).
{ clear X HB. apply nth_error_split in HN as (l1 & l2 & -> & Hl1). rewrite <- Hl1. rewrite skipn_app, Nat.sub_diag, skipn_all. reflexivity. }
rewrite EQ in X. exact X.
- intros w Hw. exists wb. split; [exact HL|]. replace (w * 8) with ((E / 8 + SB) / 8 * 8) by (Z.div_mod_to_equations; lia). exact HB.
Qed.

Lemma unpoisoned8_cell : forall segs m SB E, unpoisoned segs m SB E 8 -> E mod 8 = 0 -> ro_cells segs m (E / 8 + SB) [C1 (Z_to_bv 8 0)].
Proof.
intros segs m SB E (_ & _ & (v & Hv & Hr) & _) HE. apply QsKa.Mq1.ro_C1_of_bytes_at.
replace ((E + 8 - 1) / 8) with (E / 8) in Hv by (Z.div_mod_to_equations; lia).
destruct Hr as [-> | [Hv1 Hv2]]; [exact Hv|]. exfalso. Z.div_mod_to_equations. lia.
Qed.

Section WithIface.
Variable HIx : heap_iface_A A4L.

Lemma own_frame_fresh : forall F0 k0 (LBall LB0 LM : list blk) FRS B A m md,
HEAPA A4L HIx A LBall LM ((F0, k0) :: FRS) B m md -> incl LB0 LBall ->
~ In (F0, fr_size k0 - 8) (LB0 ++ LM ++ fr_ivs A4L FRS) /\ ~ In (shad A4L F0, fr_shadow_len k0) (LB0 ++ LM ++ fr_ivs A4L FRS).
Proof.
intros F0 k0 LBall LB0 LM FRS B A m md HP Hincl.
assert (INF : In (F0, k0) ((F0, k0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (Hk0 & HFal & HF0 & HFc & _).
pose proof (proj1 (stdpp.base.NoDup_ListNoDup _) (heapA_frame_nodup A4L HIx _ _ _ _ _ _ _ HP)) as ND. cbn in ND. apply List.NoDup_cons_iff in ND as [Hni ND].
assert (SUB : forall b, In b (LB0 ++ LM) -> In b (LBall ++ LM)).
{ intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply Hincl; exact Hb | right; exact Hb]. }
assert (K0 : k0 = 0 \/ k0 = 1 \/ k0 = 2 \/ k0 = 3) by lia.
assert (PW : forall kg, 0 <= kg <= 3 -> kg = 0 \/ kg = 1 \/ kg = 2 \/ kg = 3) by (intros; lia).
split; intros Hin; rewrite app_assoc in Hin; apply in_app_or in Hin as [Hin | Hin].
- exact (QlKV.Mq8.blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP (SUB _ Hin) (fr_ivs_frame _ _ _ _ INF)).
- apply in_fr_ivs in Hin as (G & kg & HG & [E|E]).
+ injection E as EG _. apply Hni. cbn [fr_base fst]. rewrite EG. exact (in_map fr_base _ _ HG).
+ injection E as EG EK. pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP ltac:(right; exact HG)) as (Hkg & _).
destruct K0 as [-> | [-> | [-> | ->]]]; destruct (PW kg Hkg) as [-> | [-> | [-> | ->]]]; vm_compute in EK; discriminate EK.
- exact (QlKV.Mq8.blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP (SUB _ Hin) (fr_ivs_shadow _ _ _ _ INF)).
- apply in_fr_ivs in Hin as (G & kg & HG & [E|E]).
+ injection E as EG EK. pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP ltac:(right; exact HG)) as (Hkg & _).
destruct K0 as [-> | [-> | [-> | ->]]]; destruct (PW kg Hkg) as [-> | [-> | [-> | ->]]]; vm_compute in EK; discriminate EK.
+ injection E as EG _. pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP ltac:(right; exact HG)) as (Hkg & HGal & HG0 & _).
assert (HF8 : F0 mod 8 = 0) by (destruct K0 as [-> | [-> | [-> | ->]]]; [change (fr_size 0) with 64 in HFal | change (fr_size 1) with 128 in HFal | change (fr_size 2) with 256 in HFal | change (fr_size 3) with 512 in HFal]; Z.div_mod_to_equations; lia).
assert (HG8 : G mod 8 = 0) by (destruct (PW kg Hkg) as [-> | [-> | [-> | ->]]]; [change (fr_size 0) with 64 in HGal | change (fr_size 1) with 128 in HGal | change (fr_size 2) with 256 in HGal | change (fr_size 3) with 512 in HGal]; Z.div_mod_to_equations; lia).
apply Hni. replace F0 with G; [exact (in_map fr_base _ _ HG)|]. unfold shad in EG. Z.div_mod_to_equations. lia.
Qed.
End WithIface.

Lemma fr_size_0 : fr_size 0 = 64. Proof. reflexivity. Qed.
Lemma fr_size_1 : fr_size 1 = 128. Proof. reflexivity. Qed.
Lemma fr_shadow_len_0 : fr_shadow_len 0 = 8. Proof. reflexivity. Qed.
Lemma fr_shadow_len_1 : fr_shadow_len 1 = 16. Proof. reflexivity. Qed.
End RC__1.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Qc3B.
Import QCcH.
Import Q7UD Qwm6.Mq0 QlKV.Mqa.

Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition app_range (a n : Z) : Prop := a + n <= A_SB \/ A_HMB <= a.

Lemma unpoisoned_keep : forall W m m' s n,
unpoisoned asegs m A_SB s n -> munch W m m' -> 0 <= s -> s + n <= 2^47 ->
Forall (fun iv => snd iv <= A_SB \/ A_HMB <= fst iv) W ->
unpoisoned asegs m' A_SB s n.
Proof.
intros W m m' s n U MU Hs Hn HW. eapply unpoisoned_transport; [exact U | exact MU |].
intros a k Ha Hk. pose proof U as (Hn0 & _). clear U MU. unfold shadow_span_lo in Ha. unfold shadow_span_hi in Hk. unfold A_SB in Ha, Hk.
induction W as [|[lo hi] W IH]; cbn [disjoint_from]; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. cbn [fst snd] in H1. split; [| apply IH; exact HW].
unfold A_SB, A_HMB in H1. Z.div_mod_to_equations. lia.
Qed.

Lemma unpoisoned_al8_ro : forall m s n x,
unpoisoned asegs m A_SB s n -> s <= x -> x + 8 <= s + n -> x mod 8 = 0 ->
ro_cells asegs m (x / 8 + 2147450880) [C1 (Z_to_bv 8 0)].
Proof.
intros m s n x U H1 H2 Hx.
pose proof (QsKa.Mq1.unpoisoned_sub_any asegs m A_SB s n x 8 U H1 H2 ltac:(lia)) as U8.
destruct (unpoisoned_last asegs _ _ _ _ U8) as (v & Hc & Hv).
replace ((x + 8 - 1) / 8) with (x / 8) in Hc by (Z.div_mod_to_equations; lia). unfold A_SB in Hc.
destruct Hv as [-> | [Hv Hm]]; [exact Hc|]. exfalso. replace ((x + 8 - 1) mod 8) with 7 in Hm by (Z.div_mod_to_equations; lia). lia.
Qed.

Lemma unpoisoned_byte_ro : forall m s n x,
unpoisoned asegs m A_SB s n -> s <= x < s + n ->
exists v, ro_cells asegs m (x / 8 + 2147450880) [C1 (Z_to_bv 8 v)] /\ (v = 0 \/ (0 < v < 8 /\ x mod 8 < v)).
Proof.
intros m s n x U Hx.
pose proof (QsKa.Mq1.unpoisoned_sub_any asegs m A_SB s n x 1 U ltac:(lia) ltac:(lia) ltac:(lia)) as U1.
destruct (unpoisoned_last asegs _ _ _ _ U1) as (v & Hc & Hv).
replace (x + 1 - 1) with x in Hc, Hv by lia. unfold A_SB in Hc. exists v. split; [exact Hc | exact Hv].
Qed.

Definition CRLS_STK_A : Z := 80 + 4096.
Definition crls_WA (sp S P lo : Z) : list (Z * Z) := [(lo, sp); (S, S + 24); (P, P + 16)].

Definition crls_postA (maxlen : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(S P ptr rem lo : Z) (data : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte)
(n k : Z) (str rest : list byte),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch (crls_WA (bv_unsigned sp) S P lo) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ 0 <= n <= maxlen /\ Z.of_nat (length str) <= n /\ ~ In (Z_to_bv 8 0) str
/\ rw_cells asegs m' S [C1 (Z_to_bv 8 (2 * n)); CB 23 (str ++ Z_to_bv 8 0 :: rest)]
/\ 0 <= k <= rem
/\ rw_cells asegs m' P [C8 (Z_to_bv 64 (ptr + k)); C8 (Z_to_bv 64 (rem - k))]
/\ bytes_at asegs m' ptr data
/\ stk asegs m' lo (bv_unsigned sp).

Definition crls_A_stmt (entry : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
(S P ptr rem lo maxlen : Z) (junk data : list byte),
a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 P -> a2 = Z_to_bv 64 maxlen -> 1 <= maxlen <= 20 ->
asan_rt_ok m ->

rw_cells asegs m S [CB 24 junk] -> unpoisoned asegs m A_SB S 24 -> S mod 8 = 0 -> 0x645000 <= S -> app_range S 24 ->

rw_cells asegs m P [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 rem)] -> unpoisoned asegs m A_SB P 16 -> P mod 8 = 0 ->

bytes_at asegs m ptr data -> Z.of_nat (length data) = rem -> 0 < ptr -> (0 < rem -> unpoisoned asegs m A_SB ptr rem) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - CRLS_STK_A -> bv_unsigned sp mod 16 = 0 ->

S + 24 <= lo -> ptr + rem <= lo -> (rem = 0 \/ S + 24 <= ptr \/ ptr + rem <= S) -> bv_unsigned sp <= P -> P + 16 <= 2^47 ->
mem_inv asegs m ->
evt asegs (crls_postA maxlen ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S P ptr rem lo data m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Definition fdp_WSA (stkb sp P : Z) : list (Z * Z) := [(sp - stkb, sp); (P + 8, P + 16)].
Definition fdp_postFA (stkb kmax : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(P ptr rem lo : Z) (data : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom asegs)
/\ fsaved F F' /\ frm0 fc'
/\ munch (fdp_WSA stkb (bv_unsigned sp) P) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' P [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (Z.max (rem - kmax) 0))]
/\ bytes_at asegs m' ptr data
/\ stk asegs m' lo (bv_unsigned sp).

Definition cfp_A_stmt (entry : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P ptr rem lo : Z) (data : list byte),
a0 = Z_to_bv 64 P ->
asan_rt_ok m ->
rw_cells asegs m P [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 rem)] -> unpoisoned asegs m A_SB P 16 -> P mod 8 = 0 ->
bytes_at asegs m ptr data -> Z.of_nat (length data) = rem -> 0 < ptr -> (0 < rem -> unpoisoned asegs m A_SB ptr rem) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 ->
bv_unsigned sp <= P -> P + 16 <= 2^47 -> ptr + rem <= lo ->
mem_inv asegs m ->
Sem.reg_get F (Z_to_bv 5 10) = Z_to_bv 64 0xFFEFFFFFFFFFFFFF ->
Sem.reg_get F (Z_to_bv 5 11) = Z_to_bv 64 0x7FEFFFFFFFFFFFFF ->
frm0 fc ->
evt asegs (fdp_postFA 16 9 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P ptr rem lo data m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
End RC__1.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QgoP.
Import QsKa.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Lemma first_nul_splitA : forall (pre post : list byte),
exists str rest, pre ++ [Z_to_bv 8 0] ++ post = str ++ b0 :: rest /\ ~ In b0 str /\ (length str <= length pre)%nat.
Proof.
induction pre as [|b pre IH]; intros post.
- exists [], post. split; [reflexivity|]. split; [intros H; exact H | cbn; lia].
- destruct (Z.eq_dec (bv_unsigned b) 0) as [E|NE].
+ exists [], (pre ++ [Z_to_bv 8 0] ++ post). split; [| split; [intros H; exact H | cbn; lia]].
cbn [app]. f_equal. apply bv_eq. rewrite E. reflexivity.
+ destruct (IH post) as (str & rest & E2 & Hn & Hl). exists (b :: str), rest.
split; [cbn [app] in *; rewrite E2; reflexivity|].
split; [| cbn; lia]. intros [H|H]; [| exact (Hn H)]. apply NE. rewrite H. reflexivity.
Qed.

Section Walk.
Variable stop : byte -> byte -> bool.
Variable value : byte -> byte -> Z.
Hypothesis stop_l0 : forall a b, bv_unsigned a = 0 -> stop a b = true.
Hypothesis stop_r0 : forall a b, bv_unsigned b = 0 -> bv_unsigned a <> 0 -> stop a b = true.
Hypothesis value_range : forall a b, -300 <= value a b <= 300.

Lemma icmp_walk_cstr : forall ls rs rest k, exists j v, icmp_walk stop value (ls ++ [b0]) (rs ++ b0 :: rest) k = Some (j, v).
Proof.
induction ls as [|a ls IH]; intros rs rest k.
- destruct k as [|k]; [exists 0%nat, 0; reflexivity|]. cbn [app icmp_walk].
destruct (rs ++ b0 :: rest) as [|b r] eqn:E; [destruct rs; discriminate E|].
rewrite (stop_l0 b0 b) by reflexivity. eexists _, _; reflexivity.
- destruct k as [|k]; [exists 0%nat, 0; reflexivity|]. cbn [app icmp_walk].
destruct rs as [|b rs]; cbn [app].
+ destruct (Z.eq_dec (bv_unsigned a) 0) as [E|NE].
* rewrite (stop_l0 a b0 E). eexists _, _; reflexivity.
* rewrite (stop_r0 a b0) by (first [reflexivity | exact NE]). eexists _, _; reflexivity.
+ destruct (stop a b); [eexists _, _; reflexivity|].
destruct (IH rs rest k) as (j & v & E). rewrite E. eexists _, _; reflexivity.
Qed.

Lemma icmp_walk_range : forall l r k j v, icmp_walk stop value l r k = Some (j, v) -> -300 <= v <= 300.
Proof.
intros l r k. revert l r. induction k as [|k IH]; intros l r j v H; cbn in H.
- injection H as <- <-. lia.
- destruct l as [|a l]; [discriminate|]. destruct r as [|b r]; [discriminate|].
destruct (stop a b).
+ injection H as <- <-. apply value_range.
+ destruct (icmp_walk stop value l r k) as [[j' v']|] eqn:E; [|discriminate]. injection H as <- <-. eapply IH; exact E.
Qed.
End Walk.

Lemma lower8_zero : forall c, 0 <= c < 256 -> lower8 c = 0 -> c = 0.
Proof. intros c Hc. unfold lower8. destruct (_ && _)%bool eqn:E; [| intros; assumption]. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. lia. Qed.
Lemma lower8_pos : forall c, 0 <= c < 256 -> c <> 0 -> lower8 c <> 0.
Proof. intros c Hc Hn E. apply Hn. apply lower8_zero; assumption. Qed.

Lemma byte_range256 : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia. Qed.

Lemma cmp_stop_l0 : forall a b, bv_unsigned a = 0 -> cmp_stop a b = true.
Proof. intros a b E. unfold cmp_stop. rewrite E. rewrite Bool.orb_true_r. reflexivity. Qed.
Lemma cmp_stop_r0 : forall a b, bv_unsigned b = 0 -> bv_unsigned a <> 0 -> cmp_stop a b = true.
Proof. intros a b E N. unfold cmp_stop. rewrite E. replace (bv_unsigned a =? 0) with false by (symmetry; apply Z.eqb_neq; exact N). reflexivity. Qed.
Lemma cmp_sign_range : forall a b, -300 <= cmp_sign a b <= 300.
Proof. intros a b. unfold cmp_sign. pose proof (byte_range256 a). pose proof (byte_range256 b). destruct (Z.sgn_spec (bv_unsigned a - bv_unsigned b)) as [[_ ->] | [[_ ->] | [_ ->]]]; lia. Qed.
Lemma casecmp_stop_l0 : forall a b, bv_unsigned a = 0 -> casecmp_stop a b = true.
Proof. intros a b E. unfold casecmp_stop. rewrite E. rewrite Bool.orb_true_r. reflexivity. Qed.
Lemma casecmp_stop_r0 : forall a b, bv_unsigned b = 0 -> bv_unsigned a <> 0 -> casecmp_stop a b = true.
Proof.
intros a b E N. unfold casecmp_stop. rewrite E. change (lower8 0) with 0.
replace (lower8 (bv_unsigned a) =? 0) with false by (symmetry; apply Z.eqb_neq; apply lower8_pos; [apply byte_range256 | exact N]). reflexivity.
Qed.
Lemma casecmp_val_range : forall a b, -300 <= casecmp_val a b <= 300.
Proof. intros a b. unfold casecmp_val. pose proof (lower8_range _ (byte_range256 a)). pose proof (lower8_range _ (byte_range256 b)). lia. Qed.

Lemma istrncmp_total : forall ls pre post n, exists j v, istrncmp_model (ls ++ [b0]) (pre ++ [Z_to_bv 8 0] ++ post) n = Some (j, v) /\ -300 <= v <= 300.
Proof.
intros ls pre post n. destruct (first_nul_splitA pre post) as (str & rest & E & _ & _). rewrite E. unfold istrncmp_model.
destruct (icmp_walk_cstr cmp_stop cmp_sign cmp_stop_l0 cmp_stop_r0 ls str rest (Z.to_nat n)) as (j & v & H). exists j, v. split; [exact H|].
exact (icmp_walk_range cmp_stop cmp_sign cmp_sign_range _ _ _ _ _ H).
Qed.
Lemma istrncasecmp_total : forall ls pre post n, exists j v, istrncasecmp_model (ls ++ [b0]) (pre ++ [Z_to_bv 8 0] ++ post) n = Some (j, v) /\ -300 <= v <= 300.
Proof.
intros ls pre post n. destruct (first_nul_splitA pre post) as (str & rest & E & _ & _). rewrite E. unfold istrncasecmp_model.
destruct (icmp_walk_cstr casecmp_stop casecmp_val casecmp_stop_l0 casecmp_stop_r0 ls str rest (Z.to_nat n)) as (j & v & H). exists j, v. split; [exact H|].
exact (icmp_walk_range casecmp_stop casecmp_val casecmp_val_range _ _ _ _ _ H).
Qed.

Lemma eqb64_small_0 : forall v, -300 <= v <= 300 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
intros v Hv. destruct (Z.eqb_spec v 0) as [-> | Hn]; [reflexivity|].
unfold bv_eqb. apply Z.eqb_neq. rewrite (unsigned_lit 0) by lia.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. intros E. apply Hn.
destruct (Z.lt_ge_cases v 0); [| rewrite Z.mod_small in E by (cbn; lia); exact E].
replace v with ((v + 2^64) - 1 * 2^64) in E by lia. cbn in E. lia.
Qed.

Lemma istrn_nread : forall stop value la lb n j v, icmp_walk stop value la lb (Z.to_nat n) = Some (j, v) ->
(j <= Z.to_nat n)%nat /\ (j <= length la)%nat /\ (j <= length lb)%nat /\ (0 < n -> (1 <= j)%nat).
Proof.
intros stop value la lb n j v H. destruct (icmp_walk_nread stop value _ _ _ _ _ H) as (H1 & H2 & H3).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. intros Hn. eapply icmp_walk_pos; [exact H | lia].
Qed.
Lemma istrncmp_nread : forall la lb n j v, istrncmp_model la lb n = Some (j, v) ->
(j <= Z.to_nat n)%nat /\ (j <= length la)%nat /\ (j <= length lb)%nat /\ (0 < n -> (1 <= j)%nat).
Proof. intros. eapply istrn_nread; eassumption. Qed.
Lemma istrncasecmp_nread : forall la lb n j v, istrncasecmp_model la lb n = Some (j, v) ->
(j <= Z.to_nat n)%nat /\ (j <= length la)%nat /\ (j <= length lb)%nat /\ (0 < n -> (1 <= j)%nat).
Proof. intros. eapply istrn_nread; eassumption. Qed.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek QZAi Qx2n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek.
Import QZAi.Mq1 Qx2n.
Import Q7UD Qhd4 Qwm6 Qwm6.Mq0 QsKa.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition A_STRTOD : Z := 0xda5f4.
Definition ASTRTOD_DEPTH : Z := 8928.

Definition astrtod_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(T PE : Z) (txt : list Z) (npre bits used lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte) (ev' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp); (PE, PE + 8); (A_TP - 164, A_TP - 160)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ frm0 fc'
/\ (forall k : bv 5, bv_unsigned k <> 10 -> bv_unsigned k <> 14 -> bv_unsigned k <> 15 -> reg_get F' k = reg_get F k)
/\ reg_get F' 10 = Z_to_bv 64 bits
/\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' PE [C8 (Z_to_bv 64 (T + used))]
/\ bytes_at asegs m' T (map (Z_to_bv 8) txt)
/\ rw_cells asegs m' (A_TP - 164) [C4 ev']
/\ 0 <= used <= npre.

Definition astrtod_total_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
(T PE : Z) (txt pre post : list Z) (bits used : Z) (ejunk : word) (lo : Z) (canary ev : word),
bytes_at asegs m T (map (Z_to_bv 8) txt) -> Forall (fun c => 0 <= c < 256) txt ->
txt = pre ++ 0 :: post -> zlength pre < 2^31 -> zlength txt <= 2^40 ->
rw_cells asegs m PE [C8 ejunk] ->
scan_strtod_h txt = Some (bits, used) ->
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ASTRTOD_DEPTH -> 0x645000 <= lo -> bv_unsigned sp <= 2^47 ->
0 < T -> T + zlength txt <= 2^47 ->
(((T + zlength txt <= 0x10000 \/ 0x645000 <= T) /\ T + zlength txt <= lo) \/ bv_unsigned sp <= T) ->
0x645000 <= PE -> PE + 8 <= 2^47 ->
(PE + 8 <= lo \/ bv_unsigned sp <= PE) ->
(PE + 8 <= T \/ T + zlength txt <= PE) ->
bytes_at asegs m A_GOT_GUARD (le8 (Z_to_bv 64 A_GUARD)) -> bytes_at asegs m A_GUARD (le8 canary) ->
rw_cells asegs m (A_TP - 164) [C4 ev] ->
mem_inv asegs m -> frm0 fc ->
tp = Z_to_bv 64 A_TP -> a0 = Z_to_bv 64 T -> a1 = Z_to_bv 64 PE ->
evt asegs (astrtod_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F T PE txt (zlength pre) bits used lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_STRTOD) fc None m (seg_rom asegs)).

Definition scan_total_stmtA : Prop :=
forall l, Forall (fun c => 0 <= c < 256) l -> exists bits used, scan_strtod_h (l ++ [0]) = Some (bits, used) /\ 0 <= used.

Section Rtc.
Variable HIx : heap_iface_A A4L.
Definition A_LCONV : Z := 0xe5c50.
Definition A_DPSTR : Z := 0x1485d.
Definition A_SERTBL_DBL : Z := 0xe2810.
Definition rtc_lconv_stmt : Prop :=
forall A LB LM FR B m md, HEAPA A4L HIx A LB LM FR B m md -> bytes_at asegs m A_LCONV (le8 (Z_to_bv 64 A_DPSTR)).
Definition rtc_sertbl_stmt : Prop :=
forall A LB LM FR B m md, HEAPA A4L HIx A LB LM FR B m md -> bytes_at asegs m A_SERTBL_DBL (le8 (Z_to_bv 64 (fn_dbl_to_json_string A4F))).
End Rtc.
End RC__1.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7 QJjn QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition region_cells (m : word -> option byte) : Prop :=
ro_cells asegs m 0xe5db8 [C8 (Z_to_bv 64 0xefaf8)] /\ ro_cells asegs m 0xefaf8 [C8 (Z_to_bv 64 A_SB)]
/\ ro_cells asegs m 0xe5dc0 [C8 (Z_to_bv 64 0xf07e8)] /\ ro_cells asegs m 0xf07e8 [C8 (Z_to_bv 64 0)]
/\ ro_cells asegs m 0xe5dc8 [C8 (Z_to_bv 64 0xf07f0)] /\ ro_cells asegs m 0xf07f0 [C8 (Z_to_bv 64 0)]
/\ ro_cells asegs m 0xe5dd0 [C8 (Z_to_bv 64 0xf07e0)] /\ ro_cells asegs m 0xf07e0 [C8 (Z_to_bv 64 0x7fffffffffff)].

Lemma region_cells_of_rt : forall m, asan_rt_ok m -> region_cells m.
Proof.
intros m RT. unfold asan_rt_ok, a4_rt_cells, a4_rt_consts in RT. cbn [app] in RT.
do 8 (apply Forall_cons_iff in RT as [_ RT]).
apply Forall_cons_iff in RT as [GMB RT]. apply Forall_cons_iff in RT as [KMB RT].
apply Forall_cons_iff in RT as [GME RT]. apply Forall_cons_iff in RT as [KME RT].
apply Forall_cons_iff in RT as [GHE RT]. apply Forall_cons_iff in RT as [KHE RT].
do 47 (apply Forall_cons_iff in RT as [_ RT]).
apply Forall_cons_iff in RT as [GOT RT]. apply Forall_cons_iff in RT as [CELL _].
cbn [fst snd] in GMB, KMB, GME, KME, GHE, KHE, GOT, CELL. unfold A_GOT_SB, A_SB_CELL in GOT, CELL.
unfold region_cells.
split; [apply ro_C8_of_bytes_at; exact GOT|]. split; [apply ro_C8_of_bytes_at; exact CELL|].
split; [apply ro_C8_of_bytes_at; exact GMB|]. split; [apply ro_C8_of_bytes_at; exact KMB|].
split; [apply ro_C8_of_bytes_at; exact GME|]. split; [apply ro_C8_of_bytes_at; exact KME|].
split; [apply ro_C8_of_bytes_at; exact GHE|]. apply ro_C8_of_bytes_at; exact KHE.
Qed.

Lemma mem_to_shadow_spec :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p : Z) (Q : machine_state -> Prop),
a0 = Z_to_bv 64 p -> ((0 <= p /\ p + 1 <= A_SB) \/ (A_HMB <= p /\ p + 1 <= 2^47)) ->
region_cells m -> mem_inv asegs m ->
(forall (a1' a2' a3' a4' a5' a6' a7' t0' : word),
evt asegs Q (MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 (p / 8 + A_SB)) a1' a2' a3' a4' a5' a6' a7'
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x64d20) fc None m (seg_rom asegs)).
Proof.
intros until Q. intros Ha0 Hp (GOT & CELL & GMB & KMB & GME & KME & GHE & KHE) MI K.
subst a0. unfold A_SB, A_HMB in *.
do 3 step.
step.
step.
rewrite (v_sltu_0' (Z_to_bv 64 2147450880) (Z_to_bv 64 2147450879)) by (rewrite !unsigned_lit by lia; lia).
step. step.
step.
destruct Hp as [(Hp0 & HpL) | (HpH & Hp47)].
- if_truex.
step. step. sh_norm.
replace (2147450880 + p / 8) with (p / 8 + 2147450880) by lia.
step. eapply K.
- if_falsex.
do 6 step.
step.
step. if_truex.
do 3 step.
step. step. sh_norm.
step. if_falsex.
step. if_falsex.
step. step. sh_norm.
replace (2147450880 + p / 8) with (p / 8 + 2147450880) by lia.
step. eapply K.
Qed.

Lemma mem_is_zero_spec :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b sz lo : Z) (Q : machine_state -> Prop),
a0 = Z_to_bv 64 b -> a1 = Z_to_bv 64 sz -> 0 <= b -> 0 <= sz <= 2^40 -> b + sz + 16 <= lo ->
(forall i, 0 <= i < sz -> bytes_at asegs m (b + i) [Z_to_bv 8 0]) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp mod 16 = 0 ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (a1' a2' a3' a4' a5' a6' : word) m',
munch [(lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x754a0) fc None m (seg_rom asegs)).
Proof.
intros until Q. intros Ha0 Ha1 Hb Hsz Hblo Z0 ST LO LOS SPA MI RA K.
subst a0 a1. word_range sp SPR.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
set (AB := (b + 7) / 8 * 8). set (AE := (b + sz) / 8 * 8).
assert (HAB : b <= AB <= b + 7 /\ AB mod 8 = 0) by (subst AB; Z.div_mod_to_equations; lia).
assert (HAE : b + sz - 7 <= AE <= b + sz /\ AE mod 8 = 0) by (subst AE; Z.div_mod_to_equations; lia).
carve_frame 16%nat ST.
step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (B0 : forall i, 0 <= i < sz -> bytes_at asegs mc (b + i) [Z_to_bv 8 0]);
[ intros i Hi; eapply bytes_at_transport; [apply Z0; exact Hi | exact MU | cbn; split; [left; lia | exact I]] |];
assert (HB : forall i, 0 <= i < sz -> ov_read_bytes asegs mc (Z_to_bv 64 (b + i)) 1 = Some [Z_to_bv 8 0]);
[ intros i Hi; apply ov_read1_of_ro; split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; apply B0; exact Hi] |];
assert (HW : forall j, 0 <= j -> AB + 8 * j + 8 <= AE -> ov_read_bytes asegs mc (Z_to_bv 64 (AB + 8 * j)) 8 = Some (le8 (Z_to_bv 64 0)));
[ intros j Hj Hje; apply ov_read8_of_ro; rewrite le8_zero; apply ro_CB8_of_bytes_at; [reflexivity|];
apply bytes_at_zero_run; [lia | cbn; lia |]; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.of_nat]; intros i Hi;
replace (AB + 8 * j + i) with (b + (AB + 8 * j + i - b)) by lia; apply B0; lia |]
end.
clear Z0 B0.
step.
step. step. step.
try match goal with |- context [Z_to_bv 64 (Z.shiftl ?x ?y + 1)] =>
replace (Z_to_bv 64 (Z.shiftl x y + 1)) with (Z_to_bv 64 1099511627777) by (apply bv_eq; vm_compute; reflexivity) end.
try match goal with |- context [Z_to_bv 64 (Z.shiftl ?x ?y)] =>
replace (Z_to_bv 64 (Z.shiftl x y)) with (Z_to_bv 64 1099511627776) by (apply bv_eq; vm_compute; reflexivity) end.
step. if_falsex.
step.
step.
try replace (sz + b) with (b + sz) by lia.
step. step.
rewrite (unsigned_lit (b + 7)) by lia. rewrite land_m8_64 by lia. fold AB.
step.
rewrite (unsigned_lit (b + sz)) by lia. rewrite land_m8_64 by lia. fold AE.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (EPI : forall (x3 x5 x6 : word),
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 b) (Z_to_bv 64 0) (Z_to_bv 64 AE)
x3 (Z_to_bv 64 (b + sz)) x5 x6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x7550c) fc None mc (seg_rom asegs)))
end.
{ intros x3 x5 x6.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (EXIT : forall (y0 y2 y4 : word),
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 y0 (Z_to_bv 64 0) y2
x3 y4 x5 x6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x7552c) fc None mc (seg_rom asegs)))
end.
{ intros y0 y2 y4.
step.
rewrite (v_sltiu_1 (Z_to_bv 64 0) 1) by (rewrite ?unsigned_lit by lia; lia).
do 3 step.
eapply K; [exact MU | exact WM | assumption | release_frame FR ST (bv_unsigned sp); exact ST]. }
step.
destruct (Z.lt_ge_cases AE b) as [Hlt | Hge].
- if_truex. apply EXIT.
- if_falsex.
step.
destruct (Z.eq_dec AE (b + sz)) as [Heq | Hne].
+ if_truex. apply EXIT.
+ if_falsex.
step.
rewrite (unsigned_lit (b + sz)), (unsigned_lit AE) by lia.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (ELOOP : forall (Kn : nat) (i : Z) (y0 : word),
Z.to_nat (b + sz - AE - i) = Kn -> 0 <= i -> AE + i < b + sz ->
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 y0 (Z_to_bv 64 0) (Z_to_bv 64 (AE + i))
x3 (Z_to_bv 64 (b + sz - AE - i)) x5 x6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x75518) fc None mc (seg_rom asegs)))
end.
{ induction Kn as [|Kn IH]; intros i y0 HK Hi Hie; [lia|].
pose proof (HB (AE + i - b) ltac:(lia)) as HR. replace (b + (AE + i - b)) with (AE + i) in HR by lia.
step. rewrite ?zxb_zero. clear HR.
step.
step. rewrite ?(unsigned_lit 0) by lia. change (Z.lor 0 0) with 0.
step.
step.
destruct (Z.eq_dec (AE + i + 1) (b + sz)) as [Hlast | Hmore].
- if_falsex. apply EXIT.
- if_truex.
replace (AE + i + 1) with (AE + (i + 1)) by lia.
replace (b + sz - AE - i + -1) with (b + sz - AE - (i + 1)) by lia.
apply (IH (i + 1)); lia. }
replace (Z_to_bv 64 AE) with (Z_to_bv 64 (AE + 0)) by (f_equal; lia).
replace (b + sz - AE) with (b + sz - AE - 0) by lia.
apply (ELOOP (Z.to_nat (b + sz - AE - 0)) 0); lia. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (MID : forall (x3 x6 : word),
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 b) (Z_to_bv 64 0) (Z_to_bv 64 AE)
x3 (Z_to_bv 64 (b + sz)) (Z_to_bv 64 AB) x6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x754f8) fc None mc (seg_rom asegs)))
end.
{ intros x3 x6.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (WLOOP : forall (Kn : nat) (j : Z) (y3 : word),
Z.to_nat ((AE - AB) / 8 - j) = Kn -> 0 <= j -> AB + 8 * j < AE ->
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 b) (Z_to_bv 64 0) (Z_to_bv 64 AE)
y3 (Z_to_bv 64 (b + sz)) (Z_to_bv 64 (AB + 8 * j)) x6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x754fc) fc None mc (seg_rom asegs)))
end.
{ induction Kn as [|Kn IH]; intros j y3 HK Hj Hje; [Z.div_mod_to_equations; lia|].
assert (Hje8 : AB + 8 * j + 8 <= AE) by (Z.div_mod_to_equations; lia).
pose proof (HW j Hj Hje8) as HR.
step. clear HR.
step.
step. rewrite ?(unsigned_lit 0) by lia. change (Z.lor 0 0) with 0.
step.
destruct (Z.eq_dec (AB + 8 * j + 8) AE) as [Hlast | Hmore].
- if_falsex. apply EPI.
- if_truex.
replace (AB + 8 * j + 8) with (AB + 8 * (j + 1)) by lia.
apply (IH (j + 1)); [Z.div_mod_to_equations; lia | lia | lia]. }
step.
destruct (Z.lt_ge_cases AB AE) as [Hlt | Hge].
- if_falsex. replace (Z_to_bv 64 AB) with (Z_to_bv 64 (AB + 8 * 0)) by (f_equal; lia).
apply (WLOOP (Z.to_nat ((AE - AB) / 8 - 0)) 0); lia.
- if_truex. apply EPI. }

step.
destruct (Z.eq_dec b AB) as [Hal | Hnal].
- if_truex. apply MID.
- if_falsex.
step.
destruct (Z.eq_dec sz 0) as [Hz0 | Hnz].
+ if_truex. apply MID.
+ if_falsex.
step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (PLOOP : forall (Kn : nat) (i : Z) (y6 : word),
Z.to_nat (sz - i) = Kn -> 0 <= i -> i < sz -> b + i < AB ->
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 b) (Z_to_bv 64 0) (Z_to_bv 64 AE)
(Z_to_bv 64 (b + i + 1)) (Z_to_bv 64 (b + sz)) (Z_to_bv 64 AB) y6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x754e0) fc None mc (seg_rom asegs)))
end.
{ induction Kn as [|Kn IH]; intros i y6 HK Hi His Hia; [lia|].
pose proof (HB i ltac:(lia)) as HR.
step.
step. rewrite ?zxb_zero. clear HR.
step. rewrite ?(unsigned_lit 0) by lia. change (Z.lor 0 0) with 0.
step.
destruct (Z.eq_dec (b + i + 1) AB) as [Hx | Hcont].
- if_truex. apply MID.
- if_falsex.
step.
step.
destruct (Z.eq_dec (b + i + 1) (b + sz)) as [Hend | Hmore].
+ if_falsex. apply MID.
+ if_truex.
replace (b + i + 2) with (b + (i + 1) + 1) by lia.
apply (IH (i + 1)); lia. }
replace (b + 1) with (b + 0 + 1) by lia.
apply (PLOOP (Z.to_nat (sz - 0)) 0); lia.
Qed.

Section MuslARegion.

Lemma region_is_poisoned_sound_U : region_is_poisoned_spec_U.
Proof.
unfold region_is_poisoned_spec_U.
intros until Q. intros UP RT AM Hn Hslo Ha0 Ha1 ST LO LOS SPA MI RA K.
subst a0 a1. unfold_consts. word_range sp SPR.
unfold app_mem, A_SB, A_HMB in AM. destruct AM as (Hs0 & AM).
assert (Hs47 : s + n + 8 <= 2^47) by lia.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold A_REGION_IS_POISONED. carve_frame 64%nat ST.
do 8 step.
step. if_falsex.
step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (UP1 : unpoisoned asegs mc A_SB s n)
by (eapply unpoisoned_transport; [exact UP | exact MU | intros a k Ha Hk; eapply (shadow_outside_stack A_SB s n); try eassumption; unfold A_SB; lia]);
assert (RC1 : region_cells mc)
by (apply region_cells_of_rt; eapply asan_rt_ok_transport; [exact RT | exact MU |
intros c Hc; pose proof (a4_rt_cells_in_img c Hc); cbn; split; [left; lia | exact I]])
end.
destruct RC1 as (GOT & CELL & GMB & KMB & GME & KME & GHE & KHE). unfold A_SB in CELL.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HRL : exists v, ov_read_bytes asegs mc (Z_to_bv 64 ((s + n - 1) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 v]
/\ (v = 0 \/ (0 < v < 8 /\ (s + n - 1) mod 8 < v)))
by (destruct (unpoisoned_last asegs _ _ _ _ UP1) as (v & Hro & Hv); exists v; split; [| exact Hv];
apply ov_read1_of_ro; unfold A_SB in Hro; exact Hro);
assert (GR0 : forall g, s / 8 <= g < (s + n - 1) / 8 ->
ov_read_bytes asegs mc (Z_to_bv 64 (g + 2147450880)) 1 = Some [Z_to_bv 8 0])
by (intros g Hg; apply ov_read1_of_ro; apply (unpoisoned_gran0 asegs _ A_SB s n g UP1); exact Hg);
assert (GZ : forall g, (s + 7) / 8 <= g < (s + n) / 8 -> bytes_at asegs mc (g + 2147450880) [Z_to_bv 8 0])
end.
{ intros g Hg. destruct UP1 as (_ & Ha & (v & Hb & Hv) & _). unfold A_SB in Ha, Hb.
destruct (Z.lt_ge_cases g ((s + n - 1) / 8)) as [Hlt | Hge].
- apply Ha. Z.div_mod_to_equations. lia.
- assert (Eg : g = (s + n - 1) / 8) by (Z.div_mod_to_equations; lia).
assert (Hv0 : v = 0) by (Z.div_mod_to_equations; lia).
subst g v. exact Hb. }
set (AB := (s + 7) / 8 * 8). set (AE := (s + n) / 8 * 8).
assert (HAB : s <= AB <= s + 7 /\ AB mod 8 = 0 /\ AB / 8 = (s + 7) / 8) by (subst AB; Z.div_mod_to_equations; lia).
assert (HAE : s + n - 7 <= AE <= s + n /\ AE mod 8 = 0 /\ AE / 8 = (s + n) / 8) by (subst AE; Z.div_mod_to_equations; lia).

assert (J5 : forall (xra x0 y0 y1 y2 y3 y4 y5 y6 y7 z2 z3 z4 : word) (j8 : list byte) mz,
munch [(lo, bv_unsigned sp)] m mz -> wmono asegs m mz -> mem_inv asegs mz ->
stk asegs mz lo (bv_unsigned sp + -64) ->
rw_cells asegs mz (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x0 t1 t2 (Z_to_bv 64 s) (Z_to_bv 64 n) y0 y1 y2 y3 y4 y5 y6 y7
z2 z3 z4 (Z_to_bv 64 981752) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x65324) fc None mz (seg_rom asegs))).
{ intros xra x0 y0 y1 y2 y3 y4 y5 y6 y7 z2 z3 z4 j8 mz MUz WMz MIz STz FRz.
clear HRL GR0 GZ GOT CELL GMB KMB GME KME GHE KHE FR ST MU WM MI.
do 11 step.
eapply K; [exact MUz | exact WMz | exact MIz | release_frame FRz STz (bv_unsigned sp); exact STz
| eapply unpoisoned_transport; [exact UP | exact MUz | intros a k Ha Hk; eapply (shadow_outside_stack A_SB s n); try eassumption; unfold A_SB; lia]
| eapply asan_rt_ok_transport; [exact RT | exact MUz | intros c Hc; pose proof (a4_rt_cells_in_img c Hc); cbn; split; [left; lia | exact I]] ]. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (J4 : forall (x0 y1 y2 y3 y4 y5 y6 y7 : word),
evt asegs Q (MS (mkR (Z_to_bv 64 0x652a0) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x0 t1 t2 (Z_to_bv 64 s) (Z_to_bv 64 n)
(Z_to_bv 64 (AE / 8 + 2147450880)) y1 y2 y3 y4 y5 y6 y7
(Z_to_bv 64 (s + n - 1)) (Z_to_bv 64 (AB / 8 + 2147450880)) (Z_to_bv 64 AE) (Z_to_bv 64 981752) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x65310) fc None mc (seg_rom asegs)))
end.
{ intros x0 y1 y2 y3 y4 y5 y6 y7. clear HRL GR0.
step.
destruct (Z.lt_ge_cases (AB / 8) (AE / 8)) as [Hlt | Hge].
- if_falsex.
step.
rewrite (unsigned_lit (AE / 8 + 2147450880)), (unsigned_lit (AB / 8 + 2147450880)) by lia.
step. step.
eapply mem_is_zero_spec with (b := AB / 8 + 2147450880) (sz := AE / 8 + 2147450880 - (AB / 8 + 2147450880)) (lo := lo);
[ reflexivity | reflexivity | lia | lia | unfold alloc_ceiling in LO; lia
| intros i Hi; replace (AB / 8 + 2147450880 + i) with ((AB / 8 + i) + 2147450880) by lia; apply GZ; lia
| rewrite unsigned_lit by lia; exact ST | exact LO | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| exact MI | rewrite unsigned_lit by lia; reflexivity | ].
rewrite ?unsigned_lit by lia.
intros z1 z2 z3 z4 z5 z6 m2 MU2 WM2 MI2 ST2.
lazymatch type of MU2 with munch _ ?mc _ =>
transport_after_call asegs mc m2 MU2 WM2; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU2 WM2 end.
replace (ret_pc (Z_to_bv 64 0x65320)) with (Z_to_bv 64 0x65320) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. if_false.
eapply J5; [exact MU | exact WM | exact MI2 | exact ST2 | exact FR].
- if_truex. eapply J5; [exact MU | exact WM | exact MI | exact ST | exact FR]. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (J3 : forall (x0 y2 y3 y4 y5 y6 y7 : word),
evt asegs Q (MS (mkR (Z_to_bv 64 0x652a0) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x0 t1 t2 (Z_to_bv 64 s) (Z_to_bv 64 n)
(Z_to_bv 64 (AE / 8 + 2147450880)) (Z_to_bv 64 2147450880) y2 y3 y4 y5 y6 y7
(Z_to_bv 64 (s + n)) (Z_to_bv 64 (AB / 8 + 2147450880)) (Z_to_bv 64 AE) (Z_to_bv 64 981752) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x652bc) fc None mc (seg_rom asegs)))
end.
{ intros x0 y2 y3 y4 y5 y6 y7. clear GZ GR0.
destruct HRL as (v & HR & Hv).
assert (Hv8 : 0 <= v < 128) by (destruct Hv as [->|(? & ?)]; lia).
step.
replace (s + n + -1) with (s + n - 1) by lia.
step. step. sh_norm.
replace (2147450880 + (s + n - 1) / 8) with ((s + n - 1) / 8 + 2147450880) by lia.
step. rewrite (sxb_small v) by lia. clear HR.
step.
destruct Hv as [-> | (Hk & Hlast)].
- if_true. apply J4.
- if_falsex.
step. rewrite (unsigned_lit (s + n - 1)) by lia. rewrite land7_mod8 by lia.
step. if_truex.
apply J4. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (J2 : forall (x0 y1 y2 y3 y4 y5 y6 y7 : word),
evt asegs Q (MS (mkR (Z_to_bv 64 0x652a0) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x0 t1 t2 (Z_to_bv 64 s) (Z_to_bv 64 n)
(Z_to_bv 64 (AE / 8 + 2147450880)) y1 y2 y3 y4 y5 y6 y7
(Z_to_bv 64 (s + n)) (Z_to_bv 64 (AB / 8 + 2147450880)) (Z_to_bv 64 AE) (Z_to_bv 64 981752) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x652a0) fc None mc (seg_rom asegs)))
end.
{ intros x0 y1 y2 y3 y4 y5 y6 y7. clear GZ.
step.
step. step. sh_norm.
replace (2147450880 + s / 8) with (s / 8 + 2147450880) by lia.
destruct (Z.lt_ge_cases (s / 8) ((s + n - 1) / 8)) as [Hlt | Hge].
- pose proof (GR0 (s / 8) ltac:(lia)) as HR.
step. rewrite ?sxb_zero. clear HR.
step. if_true. apply J3.
- destruct HRL as (v & HR & Hv).
assert (Hv8 : 0 <= v < 128) by (destruct Hv as [->|(? & ?)]; lia).
assert (Eg : s / 8 = (s + n - 1) / 8) by lia.
rewrite Eg. step. rewrite (sxb_small v) by lia. clear HR.
step.
destruct Hv as [-> | (Hk & Hlast)].
+ if_true. apply J3.
+ if_falsex.
step. rewrite (unsigned_lit s) by lia. rewrite land7_mod8 by lia.
step. if_falsex.
apply J3. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (J1 : forall (x0 y2 y3 y4 y5 y6 y7 : word),
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x0 t1 t2 (Z_to_bv 64 s) (Z_to_bv 64 n)
(Z_to_bv 64 2147450879) (Z_to_bv 64 2147450880) y2 y3 y4 y5 y6 y7
(Z_to_bv 64 (s + n)) s3 s4 (Z_to_bv 64 981752) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x65280) fc None mc (seg_rom asegs)))
end.
{ intros x0 y2 y3 y4 y5 y6 y7. clear GZ GR0 HRL.
step. if_falsex.
step. step.
rewrite (unsigned_lit (s + 7)) by lia. rewrite land_m8_64 by lia. fold AB.
step.
rewrite (unsigned_lit (s + n)) by lia. rewrite land_m8_64 by lia. fold AE.
step.
eapply mem_to_shadow_spec with (p := AB);
[ reflexivity | unfold A_SB, A_HMB; lia | exact (conj GOT (conj CELL (conj GMB (conj KMB (conj GME (conj KME (conj GHE KHE))))))) | exact MI | ].
intros z1 z2 z3 z4 z5 z6 z7 z8.
replace (ret_pc (Z_to_bv 64 0x65294)) with (Z_to_bv 64 0x65294) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. step. step.
eapply mem_to_shadow_spec with (p := AE);
[ reflexivity | unfold A_SB, A_HMB; lia | exact (conj GOT (conj CELL (conj GMB (conj KMB (conj GME (conj KME (conj GHE KHE))))))) | exact MI | ].
intros w1 w2 w3 w4 w5 w6 w7 w8.
replace (ret_pc (Z_to_bv 64 0x652a0)) with (Z_to_bv 64 0x652a0) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
apply J2. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (J0 : forall (x0 y3 y4 y5 y6 y7 : word),
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x0 t1 t2 (Z_to_bv 64 s) (Z_to_bv 64 n)
(Z_to_bv 64 2147450879) (Z_to_bv 64 2147450880) (Z_to_bv 64 2147450879) y3 y4 y5 y6 y7
s2 s3 s4 (Z_to_bv 64 981752) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x65238) fc None mc (seg_rom asegs)))
end.
{ intros x0 y3 y4 y5 y6 y7. clear GZ GR0 HRL.
step.
try replace (n + s) with (s + n) by lia.
step.
destruct AM as [AML | (AMH1 & AMH2)].
- if_truex. apply J1.
- if_falsex.
do 6 step.
step.
step. if_truex.
do 3 step.
step. step. sh_norm.
step. if_falsex.
step. if_falsex.
apply J1. }

clear GZ GR0 HRL.
do 3 step.
step. step.
rewrite (v_sltu_0' (Z_to_bv 64 2147450880) (Z_to_bv 64 2147450879)) by (rewrite !unsigned_lit by lia; lia).
step. step.
step.
destruct AM as [AML | (AMH1 & AMH2)].
- if_truex. apply J0.
- if_falsex.
do 6 step.
step.
step. if_truex.
do 3 step.
step. step. sh_norm.
step. if_falsex.
step. if_falsex.
apply J0.
Qed.
End MuslARegion.
End RC__1.
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Qfw3_c1.Mq2.
Import QRjH.
Import QHnV QCcH QfLs.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj.

Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition stack_malloc_full_stmt (HIx : heap_iface_A A4L) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FR : list frame) (B : bud) (k bytes lo : Z),
HEAPA A4L HIx A LB LM FR B m c ->
(0 <= k <= 2 \/ (k = 3 /\ hl_stack_malloc A4L 3 <> 0 /\ Z.of_nat (length FR) < 2048)) -> 1 <= bytes <= fr_size k -> bytes mod 8 = 0 ->
(Z.of_nat (length FR) < 4096) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A A4L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top A4L HIx + 64 ->
tp = Z_to_bv 64 (hl_tp A4L) ->
a0 = Z_to_bv 64 bytes ->
(forall ms' m' c' (A' : ASA A4L HIx) (Fr : Z),
ret_state A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 Fr) m' ms' ->
model_vm_only (cfg_model c) (cfg_model c') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FR) (bv_unsigned sp) m m' ->
Fr <> 0 ->
(exists junk, rw_cells asegs m' Fr [CB (Z.to_nat (fr_size k - 8)) junk]) ->
bytes_at asegs m' (shad A4L Fr) (repeat (Z_to_bv 8 0) (Z.to_nat (fr_shadow_len k))) ->
HEAPA A4L HIx A' LB LM ((Fr, k) :: FR) B m' c' ->
AJ5 A4L HIx A' T c' ms') ->
AJ5 A4L HIx A T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_stack_malloc A4L k)) fc None m (seg_rom asegs)).

Lemma stack_malloc_full : forall HIx : heap_iface_A A4L, stack_malloc_full_stmt HIx.
Proof. intros HIx. unfold stack_malloc_full_stmt. exact (hiA_stack_malloc A4L HIx). Qed.

Lemma frame_above_img : forall (HIx : heap_iface_A A4L) A LB LM FR B m md F k, HEAPA A4L HIx A LB LM FR B m md -> In (F, k) FR -> hl_img_hi A4H <= F.
Proof. intros HIx A LB LM FR B m md F k HP Hin. exact (heapA_frame_above A4L HIx _ _ _ _ _ _ _ _ _ HP Hin). Qed.

Lemma rtc_cell : forall (HIx : heap_iface_A A4L) A LB LM FR B m md a bs,
HEAPA A4L HIx A LB LM FR B m md -> In (a, bs) a4_rt_consts -> bytes_at asegs m a bs.
Proof.
intros HIx A LB LM FR B m md a bs HP Hin. pose proof (heapA_rtc A4L HIx _ _ _ _ _ _ _ HP) as R. rewrite Forall_forall in R.
exact (R (a, bs) Hin).
Qed.

Lemma bytes_at_subG : forall segs m a (bs : list byte) k j, bytes_at segs m a bs -> (k + j <= length bs)%nat ->
bytes_at segs m (a + Z.of_nat k) (firstn j (skipn k bs)).
Proof.
intros segs m a bs k j (Ha & Hl & H) Hkj. split; [lia|]. split; [rewrite length_firstn, length_skipn; lia|].
intros i Hi. rewrite length_firstn, length_skipn in Hi.
replace (a + Z.of_nat k + Z.of_nat i) with (a + Z.of_nat (k + i)) by lia. rewrite (H (k + i)%nat) by lia.
rewrite nth_error_firstn. replace (i <? j)%nat with true by (symmetry; apply Nat.ltb_lt; lia). rewrite nth_error_skipn. reflexivity.
Qed.

Lemma unpoisoned_gran8 : forall segs m SB E (wb : list byte),
E mod 8 = 0 -> 0 <= E -> 0 <= SB ->
length wb = 8%nat ->
bytes_at segs m ((E / 8 + SB) / 8 * 8) wb ->
nth_error wb (Z.to_nat ((E / 8 + SB) mod 8)) = Some (Z_to_bv 8 0) ->
unpoisoned segs m SB E 8.
Proof.
intros segs m SB E wb HE8 HE0 HSB HL HB HN.
split; [lia|]. split; [intros g Hg; exfalso; Z.div_mod_to_equations; lia|]. split.
- exists 0. split; [| left; reflexivity].
pose proof (bytes_at_subG segs m _ wb (Z.to_nat ((E / 8 + SB) mod 8)) 1 HB ltac:(rewrite HL; Z.div_mod_to_equations; lia)) as X.
replace ((E / 8 + SB) / 8 * 8 + Z.of_nat (Z.to_nat ((E / 8 + SB) mod 8))) with ((E + 8 - 1) / 8 + SB) in X by (Z.div_mod_to_equations; lia).
assert (EQ : firstn 1 (skipn (Z.to_nat ((E / 8 + SB) mod 8)) wb) = [Z_to_bv 8 0]).
{ clear X HB. apply nth_error_split in HN as (l1 & l2 & -> & Hl1). rewrite <- Hl1. rewrite skipn_app, Nat.sub_diag, skipn_all. reflexivity. }
rewrite EQ in X. exact X.
- intros w Hw. exists wb. split; [exact HL|]. replace (w * 8) with ((E / 8 + SB) / 8 * 8) by (Z.div_mod_to_equations; lia). exact HB.
Qed.

Lemma unpoisoned8_cell : forall segs m SB E, unpoisoned segs m SB E 8 -> E mod 8 = 0 -> ro_cells segs m (E / 8 + SB) [C1 (Z_to_bv 8 0)].
Proof.
intros segs m SB E (_ & _ & (v & Hv & Hr) & _) HE. apply QsKa.Mqa.ro_C1_of_bytes_at.
replace ((E + 8 - 1) / 8) with (E / 8) in Hv by (Z.div_mod_to_equations; lia).
destruct Hr as [-> | [Hv1 Hv2]]; [exact Hv|]. exfalso. Z.div_mod_to_equations. lia.
Qed.

Section WithIface.
Variable HIx : heap_iface_A A4L.

Lemma own_frame_fresh : forall F0 k0 (LBall LB0 LM : list blk) FRS B A m md,
HEAPA A4L HIx A LBall LM ((F0, k0) :: FRS) B m md -> incl LB0 LBall ->
~ In (F0, fr_size k0 - 8) (LB0 ++ LM ++ fr_ivs A4L FRS) /\ ~ In (shad A4L F0, fr_shadow_len k0) (LB0 ++ LM ++ fr_ivs A4L FRS).
Proof.
intros F0 k0 LBall LB0 LM FRS B A m md HP Hincl.
assert (INF : In (F0, k0) ((F0, k0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (Hk0 & HFal & HF0 & HFc & _).
pose proof (proj1 (stdpp.base.NoDup_ListNoDup _) (heapA_frame_nodup A4L HIx _ _ _ _ _ _ _ HP)) as ND. cbn in ND. apply List.NoDup_cons_iff in ND as [Hni ND].
assert (SUB : forall b, In b (LB0 ++ LM) -> In b (LBall ++ LM)).
{ intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply Hincl; exact Hb | right; exact Hb]. }
assert (K0 : k0 = 0 \/ k0 = 1 \/ k0 = 2 \/ k0 = 3) by lia.
assert (PW : forall kg, 0 <= kg <= 3 -> kg = 0 \/ kg = 1 \/ kg = 2 \/ kg = 3) by (intros; lia).
split; intros Hin; rewrite app_assoc in Hin; apply in_app_or in Hin as [Hin | Hin].
- exact (QlKV.Mqi.blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP (SUB _ Hin) (fr_ivs_frame _ _ _ _ INF)).
- apply in_fr_ivs in Hin as (G & kg & HG & [E|E]).
+ injection E as EG _. apply Hni. cbn [fr_base fst]. rewrite EG. exact (in_map fr_base _ _ HG).
+ injection E as EG EK. pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP ltac:(right; exact HG)) as (Hkg & _).
destruct K0 as [-> | [-> | [-> | ->]]]; destruct (PW kg Hkg) as [-> | [-> | [-> | ->]]]; vm_compute in EK; discriminate EK.
- exact (QlKV.Mqi.blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP (SUB _ Hin) (fr_ivs_shadow _ _ _ _ INF)).
- apply in_fr_ivs in Hin as (G & kg & HG & [E|E]).
+ injection E as EG EK. pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP ltac:(right; exact HG)) as (Hkg & _).
destruct K0 as [-> | [-> | [-> | ->]]]; destruct (PW kg Hkg) as [-> | [-> | [-> | ->]]]; vm_compute in EK; discriminate EK.
+ injection E as EG _. pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP ltac:(right; exact HG)) as (Hkg & HGal & HG0 & _).
assert (HF8 : F0 mod 8 = 0) by (destruct K0 as [-> | [-> | [-> | ->]]]; [change (fr_size 0) with 64 in HFal | change (fr_size 1) with 128 in HFal | change (fr_size 2) with 256 in HFal | change (fr_size 3) with 512 in HFal]; Z.div_mod_to_equations; lia).
assert (HG8 : G mod 8 = 0) by (destruct (PW kg Hkg) as [-> | [-> | [-> | ->]]]; [change (fr_size 0) with 64 in HGal | change (fr_size 1) with 128 in HGal | change (fr_size 2) with 256 in HGal | change (fr_size 3) with 512 in HGal]; Z.div_mod_to_equations; lia).
apply Hni. replace F0 with G; [exact (in_map fr_base _ _ HG)|]. unfold shad in EG. Z.div_mod_to_equations. lia.
Qed.
End WithIface.

Lemma fr_size_0 : fr_size 0 = 64. Proof. reflexivity. Qed.
Lemma fr_size_1 : fr_size 1 = 128. Proof. reflexivity. Qed.
Lemma fr_shadow_len_0 : fr_shadow_len 0 = 8. Proof. reflexivity. Qed.
Lemma fr_shadow_len_1 : fr_shadow_len 1 = 16. Proof. reflexivity. Qed.
End RC__1.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Qc3B.
Import QCcH.
Import QbFI Qwm6.Mq4 QlKV.Mqj.

Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition app_range (a n : Z) : Prop := a + n <= A_SB \/ A_HMB <= a.

Lemma unpoisoned_keep : forall W m m' s n,
unpoisoned asegs m A_SB s n -> munch W m m' -> 0 <= s -> s + n <= 2^47 ->
Forall (fun iv => snd iv <= A_SB \/ A_HMB <= fst iv) W ->
unpoisoned asegs m' A_SB s n.
Proof.
intros W m m' s n U MU Hs Hn HW. eapply unpoisoned_transport; [exact U | exact MU |].
intros a k Ha Hk. pose proof U as (Hn0 & _). clear U MU. unfold shadow_span_lo in Ha. unfold shadow_span_hi in Hk. unfold A_SB in Ha, Hk.
induction W as [|[lo hi] W IH]; cbn [disjoint_from]; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. cbn [fst snd] in H1. split; [| apply IH; exact HW].
unfold A_SB, A_HMB in H1. Z.div_mod_to_equations. lia.
Qed.

Lemma unpoisoned_al8_ro : forall m s n x,
unpoisoned asegs m A_SB s n -> s <= x -> x + 8 <= s + n -> x mod 8 = 0 ->
ro_cells asegs m (x / 8 + 2147450880) [C1 (Z_to_bv 8 0)].
Proof.
intros m s n x U H1 H2 Hx.
pose proof (QsKa.Mqa.unpoisoned_sub_any asegs m A_SB s n x 8 U H1 H2 ltac:(lia)) as U8.
destruct (unpoisoned_last asegs _ _ _ _ U8) as (v & Hc & Hv).
replace ((x + 8 - 1) / 8) with (x / 8) in Hc by (Z.div_mod_to_equations; lia). unfold A_SB in Hc.
destruct Hv as [-> | [Hv Hm]]; [exact Hc|]. exfalso. replace ((x + 8 - 1) mod 8) with 7 in Hm by (Z.div_mod_to_equations; lia). lia.
Qed.

Lemma unpoisoned_byte_ro : forall m s n x,
unpoisoned asegs m A_SB s n -> s <= x < s + n ->
exists v, ro_cells asegs m (x / 8 + 2147450880) [C1 (Z_to_bv 8 v)] /\ (v = 0 \/ (0 < v < 8 /\ x mod 8 < v)).
Proof.
intros m s n x U Hx.
pose proof (QsKa.Mqa.unpoisoned_sub_any asegs m A_SB s n x 1 U ltac:(lia) ltac:(lia) ltac:(lia)) as U1.
destruct (unpoisoned_last asegs _ _ _ _ U1) as (v & Hc & Hv).
replace (x + 1 - 1) with x in Hc, Hv by lia. unfold A_SB in Hc. exists v. split; [exact Hc | exact Hv].
Qed.

Definition CRLS_STK_A : Z := 80 + 4096.
Definition crls_WA (sp S P lo : Z) : list (Z * Z) := [(lo, sp); (S, S + 24); (P, P + 16)].

Definition crls_postA (maxlen : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(S P ptr rem lo : Z) (data : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte)
(n k : Z) (str rest : list byte),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch (crls_WA (bv_unsigned sp) S P lo) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ 0 <= n <= maxlen /\ Z.of_nat (length str) <= n /\ ~ In (Z_to_bv 8 0) str
/\ rw_cells asegs m' S [C1 (Z_to_bv 8 (2 * n)); CB 23 (str ++ Z_to_bv 8 0 :: rest)]
/\ 0 <= k <= rem
/\ rw_cells asegs m' P [C8 (Z_to_bv 64 (ptr + k)); C8 (Z_to_bv 64 (rem - k))]
/\ bytes_at asegs m' ptr data
/\ stk asegs m' lo (bv_unsigned sp).

Definition crls_A_stmt (entry : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
(S P ptr rem lo maxlen : Z) (junk data : list byte),
a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 P -> a2 = Z_to_bv 64 maxlen -> 1 <= maxlen <= 20 ->
asan_rt_ok m ->

rw_cells asegs m S [CB 24 junk] -> unpoisoned asegs m A_SB S 24 -> S mod 8 = 0 -> 0x647000 <= S -> app_range S 24 ->

rw_cells asegs m P [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 rem)] -> unpoisoned asegs m A_SB P 16 -> P mod 8 = 0 ->

bytes_at asegs m ptr data -> Z.of_nat (length data) = rem -> 0 < ptr -> (0 < rem -> unpoisoned asegs m A_SB ptr rem) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - CRLS_STK_A -> bv_unsigned sp mod 16 = 0 ->

S + 24 <= lo -> ptr + rem <= lo -> (rem = 0 \/ S + 24 <= ptr \/ ptr + rem <= S) -> bv_unsigned sp <= P -> P + 16 <= 2^47 ->
mem_inv asegs m ->
evt asegs (crls_postA maxlen ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S P ptr rem lo data m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Definition fdp_WSA (stkb sp P : Z) : list (Z * Z) := [(sp - stkb, sp); (P + 8, P + 16)].
Definition fdp_postFA (stkb kmax : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(P ptr rem lo : Z) (data : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom asegs)
/\ fsaved F F' /\ frm0 fc'
/\ munch (fdp_WSA stkb (bv_unsigned sp) P) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' P [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (Z.max (rem - kmax) 0))]
/\ bytes_at asegs m' ptr data
/\ stk asegs m' lo (bv_unsigned sp).

Definition cfp_A_stmt (entry : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P ptr rem lo : Z) (data : list byte),
a0 = Z_to_bv 64 P ->
asan_rt_ok m ->
rw_cells asegs m P [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 rem)] -> unpoisoned asegs m A_SB P 16 -> P mod 8 = 0 ->
bytes_at asegs m ptr data -> Z.of_nat (length data) = rem -> 0 < ptr -> (0 < rem -> unpoisoned asegs m A_SB ptr rem) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 ->
bv_unsigned sp <= P -> P + 16 <= 2^47 -> ptr + rem <= lo ->
mem_inv asegs m ->
Sem.reg_get F (Z_to_bv 5 10) = Z_to_bv 64 0xFFEFFFFFFFFFFFFF ->
Sem.reg_get F (Z_to_bv 5 11) = Z_to_bv 64 0x7FEFFFFFFFFFFFFF ->
frm0 fc ->
evt asegs (fdp_postFA 16 9 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P ptr rem lo data m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
End RC__1.
End Mq6.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QgoP.
Import QsKa.Mq9.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Lemma first_nul_splitA : forall (pre post : list byte),
exists str rest, pre ++ [Z_to_bv 8 0] ++ post = str ++ b0 :: rest /\ ~ In b0 str /\ (length str <= length pre)%nat.
Proof.
induction pre as [|b pre IH]; intros post.
- exists [], post. split; [reflexivity|]. split; [intros H; exact H | cbn; lia].
- destruct (Z.eq_dec (bv_unsigned b) 0) as [E|NE].
+ exists [], (pre ++ [Z_to_bv 8 0] ++ post). split; [| split; [intros H; exact H | cbn; lia]].
cbn [app]. f_equal. apply bv_eq. rewrite E. reflexivity.
+ destruct (IH post) as (str & rest & E2 & Hn & Hl). exists (b :: str), rest.
split; [cbn [app] in *; rewrite E2; reflexivity|].
split; [| cbn; lia]. intros [H|H]; [| exact (Hn H)]. apply NE. rewrite H. reflexivity.
Qed.

Section Walk.
Variable stop : byte -> byte -> bool.
Variable value : byte -> byte -> Z.
Hypothesis stop_l0 : forall a b, bv_unsigned a = 0 -> stop a b = true.
Hypothesis stop_r0 : forall a b, bv_unsigned b = 0 -> bv_unsigned a <> 0 -> stop a b = true.
Hypothesis value_range : forall a b, -300 <= value a b <= 300.

Lemma icmp_walk_cstr : forall ls rs rest k, exists j v, icmp_walk stop value (ls ++ [b0]) (rs ++ b0 :: rest) k = Some (j, v).
Proof.
induction ls as [|a ls IH]; intros rs rest k.
- destruct k as [|k]; [exists 0%nat, 0; reflexivity|]. cbn [app icmp_walk].
destruct (rs ++ b0 :: rest) as [|b r] eqn:E; [destruct rs; discriminate E|].
rewrite (stop_l0 b0 b) by reflexivity. eexists _, _; reflexivity.
- destruct k as [|k]; [exists 0%nat, 0; reflexivity|]. cbn [app icmp_walk].
destruct rs as [|b rs]; cbn [app].
+ destruct (Z.eq_dec (bv_unsigned a) 0) as [E|NE].
* rewrite (stop_l0 a b0 E). eexists _, _; reflexivity.
* rewrite (stop_r0 a b0) by (first [reflexivity | exact NE]). eexists _, _; reflexivity.
+ destruct (stop a b); [eexists _, _; reflexivity|].
destruct (IH rs rest k) as (j & v & E). rewrite E. eexists _, _; reflexivity.
Qed.

Lemma icmp_walk_range : forall l r k j v, icmp_walk stop value l r k = Some (j, v) -> -300 <= v <= 300.
Proof.
intros l r k. revert l r. induction k as [|k IH]; intros l r j v H; cbn in H.
- injection H as <- <-. lia.
- destruct l as [|a l]; [discriminate|]. destruct r as [|b r]; [discriminate|].
destruct (stop a b).
+ injection H as <- <-. apply value_range.
+ destruct (icmp_walk stop value l r k) as [[j' v']|] eqn:E; [|discriminate]. injection H as <- <-. eapply IH; exact E.
Qed.
End Walk.

Lemma lower8_zero : forall c, 0 <= c < 256 -> lower8 c = 0 -> c = 0.
Proof. intros c Hc. unfold lower8. destruct (_ && _)%bool eqn:E; [| intros; assumption]. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. lia. Qed.
Lemma lower8_pos : forall c, 0 <= c < 256 -> c <> 0 -> lower8 c <> 0.
Proof. intros c Hc Hn E. apply Hn. apply lower8_zero; assumption. Qed.

Lemma byte_range256 : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia. Qed.

Lemma cmp_stop_l0 : forall a b, bv_unsigned a = 0 -> cmp_stop a b = true.
Proof. intros a b E. unfold cmp_stop. rewrite E. rewrite Bool.orb_true_r. reflexivity. Qed.
Lemma cmp_stop_r0 : forall a b, bv_unsigned b = 0 -> bv_unsigned a <> 0 -> cmp_stop a b = true.
Proof. intros a b E N. unfold cmp_stop. rewrite E. replace (bv_unsigned a =? 0) with false by (symmetry; apply Z.eqb_neq; exact N). reflexivity. Qed.
Lemma cmp_sign_range : forall a b, -300 <= cmp_sign a b <= 300.
Proof. intros a b. unfold cmp_sign. pose proof (byte_range256 a). pose proof (byte_range256 b). destruct (Z.sgn_spec (bv_unsigned a - bv_unsigned b)) as [[_ ->] | [[_ ->] | [_ ->]]]; lia. Qed.
Lemma casecmp_stop_l0 : forall a b, bv_unsigned a = 0 -> casecmp_stop a b = true.
Proof. intros a b E. unfold casecmp_stop. rewrite E. rewrite Bool.orb_true_r. reflexivity. Qed.
Lemma casecmp_stop_r0 : forall a b, bv_unsigned b = 0 -> bv_unsigned a <> 0 -> casecmp_stop a b = true.
Proof.
intros a b E N. unfold casecmp_stop. rewrite E. change (lower8 0) with 0.
replace (lower8 (bv_unsigned a) =? 0) with false by (symmetry; apply Z.eqb_neq; apply lower8_pos; [apply byte_range256 | exact N]). reflexivity.
Qed.
Lemma casecmp_val_range : forall a b, -300 <= casecmp_val a b <= 300.
Proof. intros a b. unfold casecmp_val. pose proof (lower8_range _ (byte_range256 a)). pose proof (lower8_range _ (byte_range256 b)). lia. Qed.

Lemma istrncmp_total : forall ls pre post n, exists j v, istrncmp_model (ls ++ [b0]) (pre ++ [Z_to_bv 8 0] ++ post) n = Some (j, v) /\ -300 <= v <= 300.
Proof.
intros ls pre post n. destruct (first_nul_splitA pre post) as (str & rest & E & _ & _). rewrite E. unfold istrncmp_model.
destruct (icmp_walk_cstr cmp_stop cmp_sign cmp_stop_l0 cmp_stop_r0 ls str rest (Z.to_nat n)) as (j & v & H). exists j, v. split; [exact H|].
exact (icmp_walk_range cmp_stop cmp_sign cmp_sign_range _ _ _ _ _ H).
Qed.
Lemma istrncasecmp_total : forall ls pre post n, exists j v, istrncasecmp_model (ls ++ [b0]) (pre ++ [Z_to_bv 8 0] ++ post) n = Some (j, v) /\ -300 <= v <= 300.
Proof.
intros ls pre post n. destruct (first_nul_splitA pre post) as (str & rest & E & _ & _). rewrite E. unfold istrncasecmp_model.
destruct (icmp_walk_cstr casecmp_stop casecmp_val casecmp_stop_l0 casecmp_stop_r0 ls str rest (Z.to_nat n)) as (j & v & H). exists j, v. split; [exact H|].
exact (icmp_walk_range casecmp_stop casecmp_val casecmp_val_range _ _ _ _ _ H).
Qed.

Lemma eqb64_small_0 : forall v, -300 <= v <= 300 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
intros v Hv. destruct (Z.eqb_spec v 0) as [-> | Hn]; [reflexivity|].
unfold bv_eqb. apply Z.eqb_neq. rewrite (unsigned_lit 0) by lia.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. intros E. apply Hn.
destruct (Z.lt_ge_cases v 0); [| rewrite Z.mod_small in E by (cbn; lia); exact E].
replace v with ((v + 2^64) - 1 * 2^64) in E by lia. cbn in E. lia.
Qed.

Lemma istrn_nread : forall stop value la lb n j v, icmp_walk stop value la lb (Z.to_nat n) = Some (j, v) ->
(j <= Z.to_nat n)%nat /\ (j <= length la)%nat /\ (j <= length lb)%nat /\ (0 < n -> (1 <= j)%nat).
Proof.
intros stop value la lb n j v H. destruct (icmp_walk_nread stop value _ _ _ _ _ H) as (H1 & H2 & H3).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. intros Hn. eapply icmp_walk_pos; [exact H | lia].
Qed.
Lemma istrncmp_nread : forall la lb n j v, istrncmp_model la lb n = Some (j, v) ->
(j <= Z.to_nat n)%nat /\ (j <= length la)%nat /\ (j <= length lb)%nat /\ (0 < n -> (1 <= j)%nat).
Proof. intros. eapply istrn_nread; eassumption. Qed.
Lemma istrncasecmp_nread : forall la lb n j v, istrncasecmp_model la lb n = Some (j, v) ->
(j <= Z.to_nat n)%nat /\ (j <= length la)%nat /\ (j <= length lb)%nat /\ (0 < n -> (1 <= j)%nat).
Proof. intros. eapply istrn_nread; eassumption. Qed.
End Mq7.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek.
Import QZAi.Mq1 Qx2n.
Import QbFI. Import Qhd4 Qwm6. Import Qwm6.Mq4 QsKa.Mq9.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition A_STRTOD : Z := 0xdccb8.
Definition ASTRTOD_DEPTH : Z := 8928.

Definition astrtod_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(T PE : Z) (txt : list Z) (npre bits used lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte) (ev' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp); (PE, PE + 8); (A_TP - 164, A_TP - 160)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ frm0 fc'
/\ (forall k : bv 5, bv_unsigned k <> 10 -> bv_unsigned k <> 14 -> bv_unsigned k <> 15 -> reg_get F' k = reg_get F k)
/\ reg_get F' 10 = Z_to_bv 64 bits
/\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' PE [C8 (Z_to_bv 64 (T + used))]
/\ bytes_at asegs m' T (map (Z_to_bv 8) txt)
/\ rw_cells asegs m' (A_TP - 164) [C4 ev']
/\ 0 <= used <= npre.

Definition astrtod_total_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
(T PE : Z) (txt pre post : list Z) (bits used : Z) (ejunk : word) (lo : Z) (canary ev : word),
bytes_at asegs m T (map (Z_to_bv 8) txt) -> Forall (fun c => 0 <= c < 256) txt ->
txt = pre ++ 0 :: post -> zlength pre < 2^31 -> zlength txt <= 2^40 ->
rw_cells asegs m PE [C8 ejunk] ->
scan_strtod_h txt = Some (bits, used) ->
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ASTRTOD_DEPTH -> 0x647000 <= lo -> bv_unsigned sp <= 2^47 ->
0 < T -> T + zlength txt <= 2^47 ->
(((T + zlength txt <= 0x10000 \/ 0x647000 <= T) /\ T + zlength txt <= lo) \/ bv_unsigned sp <= T) ->
0x647000 <= PE -> PE + 8 <= 2^47 ->
(PE + 8 <= lo \/ bv_unsigned sp <= PE) ->
(PE + 8 <= T \/ T + zlength txt <= PE) ->
bytes_at asegs m A_GOT_GUARD (le8 (Z_to_bv 64 A_GUARD)) -> bytes_at asegs m A_GUARD (le8 canary) ->
rw_cells asegs m (A_TP - 164) [C4 ev] ->
mem_inv asegs m -> frm0 fc ->
tp = Z_to_bv 64 A_TP -> a0 = Z_to_bv 64 T -> a1 = Z_to_bv 64 PE ->
evt asegs (astrtod_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F T PE txt (zlength pre) bits used lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_STRTOD) fc None m (seg_rom asegs)).

Definition scan_total_stmtA : Prop :=
forall l, Forall (fun c => 0 <= c < 256) l -> exists bits used, scan_strtod_h (l ++ [0]) = Some (bits, used) /\ 0 <= used.

Section Rtc.
Variable HIx : heap_iface_A A4L.
Definition A_LCONV : Z := 0xe8050.
Definition A_DPSTR : Z := 0x1499c.
Definition A_SERTBL_DBL : Z := 0xe4ed0.
Definition rtc_lconv_stmt : Prop :=
forall A LB LM FR B m md, HEAPA A4L HIx A LB LM FR B m md -> bytes_at asegs m A_LCONV (le8 (Z_to_bv 64 A_DPSTR)).
Definition rtc_sertbl_stmt : Prop :=
forall A LB LM FR B m md, HEAPA A4L HIx A LB LM FR B m md -> bytes_at asegs m A_SERTBL_DBL (le8 (Z_to_bv 64 (fn_dbl_to_json_string A4F))).
End Rtc.
End RC__1.
End Mq8.

From Stdlib Require Import ZArith NArith List Lia Bool.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqg.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition region_cells (m : word -> option byte) : Prop :=
ro_cells asegs m 0xe81b8 [C8 (Z_to_bv 64 0xf21b8)] /\ ro_cells asegs m 0xf21b8 [C8 (Z_to_bv 64 A_SB)]
/\ ro_cells asegs m 0xe81c0 [C8 (Z_to_bv 64 0xf2ea8)] /\ ro_cells asegs m 0xf2ea8 [C8 (Z_to_bv 64 0)]
/\ ro_cells asegs m 0xe81c8 [C8 (Z_to_bv 64 0xf2eb0)] /\ ro_cells asegs m 0xf2eb0 [C8 (Z_to_bv 64 0)]
/\ ro_cells asegs m 0xe81d0 [C8 (Z_to_bv 64 0xf2ea0)] /\ ro_cells asegs m 0xf2ea0 [C8 (Z_to_bv 64 0x7fffffffffff)].

Lemma region_cells_of_rt : forall m, asan_rt_ok m -> region_cells m.
Proof.
intros m RT. unfold asan_rt_ok, a4_rt_cells, a4_rt_consts in RT. cbn [app] in RT.
do 8 (apply Forall_cons_iff in RT as [_ RT]).
apply Forall_cons_iff in RT as [GMB RT]. apply Forall_cons_iff in RT as [KMB RT].
apply Forall_cons_iff in RT as [GME RT]. apply Forall_cons_iff in RT as [KME RT].
apply Forall_cons_iff in RT as [GHE RT]. apply Forall_cons_iff in RT as [KHE RT].
do 50 (apply Forall_cons_iff in RT as [_ RT]).
apply Forall_cons_iff in RT as [GOT RT]. apply Forall_cons_iff in RT as [CELL _].
cbn [fst snd] in GMB, KMB, GME, KME, GHE, KHE, GOT, CELL. unfold A_GOT_SB, A_SB_CELL in GOT, CELL.
unfold region_cells.
split; [apply ro_C8_of_bytes_at; exact GOT|]. split; [apply ro_C8_of_bytes_at; exact CELL|].
split; [apply ro_C8_of_bytes_at; exact GMB|]. split; [apply ro_C8_of_bytes_at; exact KMB|].
split; [apply ro_C8_of_bytes_at; exact GME|]. split; [apply ro_C8_of_bytes_at; exact KME|].
split; [apply ro_C8_of_bytes_at; exact GHE|]. apply ro_C8_of_bytes_at; exact KHE.
Qed.

Lemma mem_to_shadow_spec :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p : Z) (Q : machine_state -> Prop),
a0 = Z_to_bv 64 p -> ((0 <= p /\ p + 1 <= A_SB) \/ (A_HMB <= p /\ p + 1 <= 2^47)) ->
region_cells m -> mem_inv asegs m ->
(forall (a1' a2' a3' a4' a5' a6' a7' t0' : word),
evt asegs Q (MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 (p / 8 + A_SB)) a1' a2' a3' a4' a5' a6' a7'
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x650f8) fc None m (seg_rom asegs)).
Proof.
intros until Q. intros Ha0 Hp (GOT & CELL & GMB & KMB & GME & KME & GHE & KHE) MI K.
subst a0. unfold A_SB, A_HMB in *.
do 3 step.
step.
step.
rewrite (v_sltu_0' (Z_to_bv 64 2147450880) (Z_to_bv 64 2147450879)) by (rewrite !unsigned_lit by lia; lia).
step. step.
step.
destruct Hp as [(Hp0 & HpL) | (HpH & Hp47)].
- if_truex.
step. step. sh_norm.
replace (2147450880 + p / 8) with (p / 8 + 2147450880) by lia.
step. eapply K.
- if_falsex.
do 6 step.
step.
step. if_truex.
do 3 step.
step. step. sh_norm.
step. if_falsex.
step. if_falsex.
step. step. sh_norm.
replace (2147450880 + p / 8) with (p / 8 + 2147450880) by lia.
step. eapply K.
Qed.

Lemma mem_is_zero_spec :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b sz lo : Z) (Q : machine_state -> Prop),
a0 = Z_to_bv 64 b -> a1 = Z_to_bv 64 sz -> 0 <= b -> 0 <= sz <= 2^40 -> b + sz + 16 <= lo ->
(forall i, 0 <= i < sz -> bytes_at asegs m (b + i) [Z_to_bv 8 0]) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp mod 16 = 0 ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (a1' a2' a3' a4' a5' a6' : word) m',
munch [(lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x75878) fc None m (seg_rom asegs)).
Proof.
intros until Q. intros Ha0 Ha1 Hb Hsz Hblo Z0 ST LO LOS SPA MI RA K.
subst a0 a1. word_range sp SPR.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
set (AB := (b + 7) / 8 * 8). set (AE := (b + sz) / 8 * 8).
assert (HAB : b <= AB <= b + 7 /\ AB mod 8 = 0) by (subst AB; Z.div_mod_to_equations; lia).
assert (HAE : b + sz - 7 <= AE <= b + sz /\ AE mod 8 = 0) by (subst AE; Z.div_mod_to_equations; lia).
carve_frame 16%nat ST.
step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (B0 : forall i, 0 <= i < sz -> bytes_at asegs mc (b + i) [Z_to_bv 8 0]);
[ intros i Hi; eapply bytes_at_transport; [apply Z0; exact Hi | exact MU | cbn; split; [left; lia | exact I]] |];
assert (HB : forall i, 0 <= i < sz -> ov_read_bytes asegs mc (Z_to_bv 64 (b + i)) 1 = Some [Z_to_bv 8 0]);
[ intros i Hi; apply ov_read1_of_ro; split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; apply B0; exact Hi] |];
assert (HW : forall j, 0 <= j -> AB + 8 * j + 8 <= AE -> ov_read_bytes asegs mc (Z_to_bv 64 (AB + 8 * j)) 8 = Some (le8 (Z_to_bv 64 0)));
[ intros j Hj Hje; apply ov_read8_of_ro; rewrite le8_zero; apply ro_CB8_of_bytes_at; [reflexivity|];
apply bytes_at_zero_run; [lia | cbn; lia |]; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.of_nat]; intros i Hi;
replace (AB + 8 * j + i) with (b + (AB + 8 * j + i - b)) by lia; apply B0; lia |]
end.
clear Z0 B0.
step.
step. step. step.
try match goal with |- context [Z_to_bv 64 (Z.shiftl ?x ?y + 1)] =>
replace (Z_to_bv 64 (Z.shiftl x y + 1)) with (Z_to_bv 64 1099511627777) by (apply bv_eq; vm_compute; reflexivity) end.
try match goal with |- context [Z_to_bv 64 (Z.shiftl ?x ?y)] =>
replace (Z_to_bv 64 (Z.shiftl x y)) with (Z_to_bv 64 1099511627776) by (apply bv_eq; vm_compute; reflexivity) end.
step. if_falsex.
step.
step.
try replace (sz + b) with (b + sz) by lia.
step. step.
rewrite (unsigned_lit (b + 7)) by lia. rewrite land_m8_64 by lia. fold AB.
step.
rewrite (unsigned_lit (b + sz)) by lia. rewrite land_m8_64 by lia. fold AE.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (EPI : forall (x3 x5 x6 : word),
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 b) (Z_to_bv 64 0) (Z_to_bv 64 AE)
x3 (Z_to_bv 64 (b + sz)) x5 x6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x758e4) fc None mc (seg_rom asegs)))
end.
{ intros x3 x5 x6.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (EXIT : forall (y0 y2 y4 : word),
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 y0 (Z_to_bv 64 0) y2
x3 y4 x5 x6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x75904) fc None mc (seg_rom asegs)))
end.
{ intros y0 y2 y4.
step.
rewrite (v_sltiu_1 (Z_to_bv 64 0) 1) by (rewrite ?unsigned_lit by lia; lia).
do 3 step.
eapply K; [exact MU | exact WM | assumption | release_frame FR ST (bv_unsigned sp); exact ST]. }
step.
destruct (Z.lt_ge_cases AE b) as [Hlt | Hge].
- if_truex. apply EXIT.
- if_falsex.
step.
destruct (Z.eq_dec AE (b + sz)) as [Heq | Hne].
+ if_truex. apply EXIT.
+ if_falsex.
step.
rewrite (unsigned_lit (b + sz)), (unsigned_lit AE) by lia.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (ELOOP : forall (Kn : nat) (i : Z) (y0 : word),
Z.to_nat (b + sz - AE - i) = Kn -> 0 <= i -> AE + i < b + sz ->
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 y0 (Z_to_bv 64 0) (Z_to_bv 64 (AE + i))
x3 (Z_to_bv 64 (b + sz - AE - i)) x5 x6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x758f0) fc None mc (seg_rom asegs)))
end.
{ induction Kn as [|Kn IH]; intros i y0 HK Hi Hie; [lia|].
pose proof (HB (AE + i - b) ltac:(lia)) as HR. replace (b + (AE + i - b)) with (AE + i) in HR by lia.
step. rewrite ?zxb_zero. clear HR.
step.
step. rewrite ?(unsigned_lit 0) by lia. change (Z.lor 0 0) with 0.
step.
step.
destruct (Z.eq_dec (AE + i + 1) (b + sz)) as [Hlast | Hmore].
- if_falsex. apply EXIT.
- if_truex.
replace (AE + i + 1) with (AE + (i + 1)) by lia.
replace (b + sz - AE - i + -1) with (b + sz - AE - (i + 1)) by lia.
apply (IH (i + 1)); lia. }
replace (Z_to_bv 64 AE) with (Z_to_bv 64 (AE + 0)) by (f_equal; lia).
replace (b + sz - AE) with (b + sz - AE - 0) by lia.
apply (ELOOP (Z.to_nat (b + sz - AE - 0)) 0); lia. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (MID : forall (x3 x6 : word),
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 b) (Z_to_bv 64 0) (Z_to_bv 64 AE)
x3 (Z_to_bv 64 (b + sz)) (Z_to_bv 64 AB) x6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x758d0) fc None mc (seg_rom asegs)))
end.
{ intros x3 x6.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (WLOOP : forall (Kn : nat) (j : Z) (y3 : word),
Z.to_nat ((AE - AB) / 8 - j) = Kn -> 0 <= j -> AB + 8 * j < AE ->
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 b) (Z_to_bv 64 0) (Z_to_bv 64 AE)
y3 (Z_to_bv 64 (b + sz)) (Z_to_bv 64 (AB + 8 * j)) x6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x758d4) fc None mc (seg_rom asegs)))
end.
{ induction Kn as [|Kn IH]; intros j y3 HK Hj Hje; [Z.div_mod_to_equations; lia|].
assert (Hje8 : AB + 8 * j + 8 <= AE) by (Z.div_mod_to_equations; lia).
pose proof (HW j Hj Hje8) as HR.
step. clear HR.
step.
step. rewrite ?(unsigned_lit 0) by lia. change (Z.lor 0 0) with 0.
step.
destruct (Z.eq_dec (AB + 8 * j + 8) AE) as [Hlast | Hmore].
- if_falsex. apply EPI.
- if_truex.
replace (AB + 8 * j + 8) with (AB + 8 * (j + 1)) by lia.
apply (IH (j + 1)); [Z.div_mod_to_equations; lia | lia | lia]. }
step.
destruct (Z.lt_ge_cases AB AE) as [Hlt | Hge].
- if_falsex. replace (Z_to_bv 64 AB) with (Z_to_bv 64 (AB + 8 * 0)) by (f_equal; lia).
apply (WLOOP (Z.to_nat ((AE - AB) / 8 - 0)) 0); lia.
- if_truex. apply EPI. }

step.
destruct (Z.eq_dec b AB) as [Hal | Hnal].
- if_truex. apply MID.
- if_falsex.
step.
destruct (Z.eq_dec sz 0) as [Hz0 | Hnz].
+ if_truex. apply MID.
+ if_falsex.
step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (PLOOP : forall (Kn : nat) (i : Z) (y6 : word),
Z.to_nat (sz - i) = Kn -> 0 <= i -> i < sz -> b + i < AB ->
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 b) (Z_to_bv 64 0) (Z_to_bv 64 AE)
(Z_to_bv 64 (b + i + 1)) (Z_to_bv 64 (b + sz)) (Z_to_bv 64 AB) y6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x758b8) fc None mc (seg_rom asegs)))
end.
{ induction Kn as [|Kn IH]; intros i y6 HK Hi His Hia; [lia|].
pose proof (HB i ltac:(lia)) as HR.
step.
step. rewrite ?zxb_zero. clear HR.
step. rewrite ?(unsigned_lit 0) by lia. change (Z.lor 0 0) with 0.
step.
destruct (Z.eq_dec (b + i + 1) AB) as [Hx | Hcont].
- if_truex. apply MID.
- if_falsex.
step.
step.
destruct (Z.eq_dec (b + i + 1) (b + sz)) as [Hend | Hmore].
+ if_falsex. apply MID.
+ if_truex.
replace (b + i + 2) with (b + (i + 1) + 1) by lia.
apply (IH (i + 1)); lia. }
replace (b + 1) with (b + 0 + 1) by lia.
apply (PLOOP (Z.to_nat (sz - 0)) 0); lia.
Qed.

Section MuslARegion.

Lemma region_is_poisoned_sound_U : region_is_poisoned_spec_U.
Proof.
unfold region_is_poisoned_spec_U.
intros until Q. intros UP RT AM Hn Hslo Ha0 Ha1 ST LO LOS SPA MI RA K.
subst a0 a1. unfold_consts. word_range sp SPR.
unfold app_mem, A_SB, A_HMB in AM. destruct AM as (Hs0 & AM).
assert (Hs47 : s + n + 8 <= 2^47) by lia.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold A_REGION_IS_POISONED. carve_frame 64%nat ST.
do 8 step.
step. if_falsex.
step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (UP1 : unpoisoned asegs mc A_SB s n)
by (eapply unpoisoned_transport; [exact UP | exact MU | intros a k Ha Hk; eapply (shadow_outside_stack A_SB s n); try eassumption; unfold A_SB; lia]);
assert (RC1 : region_cells mc)
by (apply region_cells_of_rt; eapply asan_rt_ok_transport; [exact RT | exact MU |
intros c Hc; pose proof (a4_rt_cells_in_img c Hc); cbn; split; [left; lia | exact I]])
end.
destruct RC1 as (GOT & CELL & GMB & KMB & GME & KME & GHE & KHE). unfold A_SB in CELL.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HRL : exists v, ov_read_bytes asegs mc (Z_to_bv 64 ((s + n - 1) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 v]
/\ (v = 0 \/ (0 < v < 8 /\ (s + n - 1) mod 8 < v)))
by (destruct (unpoisoned_last asegs _ _ _ _ UP1) as (v & Hro & Hv); exists v; split; [| exact Hv];
apply ov_read1_of_ro; unfold A_SB in Hro; exact Hro);
assert (GR0 : forall g, s / 8 <= g < (s + n - 1) / 8 ->
ov_read_bytes asegs mc (Z_to_bv 64 (g + 2147450880)) 1 = Some [Z_to_bv 8 0])
by (intros g Hg; apply ov_read1_of_ro; apply (unpoisoned_gran0 asegs _ A_SB s n g UP1); exact Hg);
assert (GZ : forall g, (s + 7) / 8 <= g < (s + n) / 8 -> bytes_at asegs mc (g + 2147450880) [Z_to_bv 8 0])
end.
{ intros g Hg. destruct UP1 as (_ & Ha & (v & Hb & Hv) & _). unfold A_SB in Ha, Hb.
destruct (Z.lt_ge_cases g ((s + n - 1) / 8)) as [Hlt | Hge].
- apply Ha. Z.div_mod_to_equations. lia.
- assert (Eg : g = (s + n - 1) / 8) by (Z.div_mod_to_equations; lia).
assert (Hv0 : v = 0) by (Z.div_mod_to_equations; lia).
subst g v. exact Hb. }
set (AB := (s + 7) / 8 * 8). set (AE := (s + n) / 8 * 8).
assert (HAB : s <= AB <= s + 7 /\ AB mod 8 = 0 /\ AB / 8 = (s + 7) / 8) by (subst AB; Z.div_mod_to_equations; lia).
assert (HAE : s + n - 7 <= AE <= s + n /\ AE mod 8 = 0 /\ AE / 8 = (s + n) / 8) by (subst AE; Z.div_mod_to_equations; lia).

assert (J5 : forall (xra x0 y0 y1 y2 y3 y4 y5 y6 y7 z2 z3 z4 : word) (j8 : list byte) mz,
munch [(lo, bv_unsigned sp)] m mz -> wmono asegs m mz -> mem_inv asegs mz ->
stk asegs mz lo (bv_unsigned sp + -64) ->
rw_cells asegs mz (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x0 t1 t2 (Z_to_bv 64 s) (Z_to_bv 64 n) y0 y1 y2 y3 y4 y5 y6 y7
z2 z3 z4 (Z_to_bv 64 991672) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x656fc) fc None mz (seg_rom asegs))).
{ intros xra x0 y0 y1 y2 y3 y4 y5 y6 y7 z2 z3 z4 j8 mz MUz WMz MIz STz FRz.
clear HRL GR0 GZ GOT CELL GMB KMB GME KME GHE KHE FR ST MU WM MI.
do 11 step.
eapply K; [exact MUz | exact WMz | exact MIz | release_frame FRz STz (bv_unsigned sp); exact STz
| eapply unpoisoned_transport; [exact UP | exact MUz | intros a k Ha Hk; eapply (shadow_outside_stack A_SB s n); try eassumption; unfold A_SB; lia]
| eapply asan_rt_ok_transport; [exact RT | exact MUz | intros c Hc; pose proof (a4_rt_cells_in_img c Hc); cbn; split; [left; lia | exact I]] ]. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (J4 : forall (x0 y1 y2 y3 y4 y5 y6 y7 : word),
evt asegs Q (MS (mkR (Z_to_bv 64 0x65678) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x0 t1 t2 (Z_to_bv 64 s) (Z_to_bv 64 n)
(Z_to_bv 64 (AE / 8 + 2147450880)) y1 y2 y3 y4 y5 y6 y7
(Z_to_bv 64 (s + n - 1)) (Z_to_bv 64 (AB / 8 + 2147450880)) (Z_to_bv 64 AE) (Z_to_bv 64 991672) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x656e8) fc None mc (seg_rom asegs)))
end.
{ intros x0 y1 y2 y3 y4 y5 y6 y7. clear HRL GR0.
step.
destruct (Z.lt_ge_cases (AB / 8) (AE / 8)) as [Hlt | Hge].
- if_falsex.
step.
rewrite (unsigned_lit (AE / 8 + 2147450880)), (unsigned_lit (AB / 8 + 2147450880)) by lia.
step. step.
eapply mem_is_zero_spec with (b := AB / 8 + 2147450880) (sz := AE / 8 + 2147450880 - (AB / 8 + 2147450880)) (lo := lo);
[ reflexivity | reflexivity | lia | lia | unfold alloc_ceiling in LO; lia
| intros i Hi; replace (AB / 8 + 2147450880 + i) with ((AB / 8 + i) + 2147450880) by lia; apply GZ; lia
| rewrite unsigned_lit by lia; exact ST | exact LO | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| exact MI | rewrite unsigned_lit by lia; reflexivity | ].
rewrite ?unsigned_lit by lia.
intros z1 z2 z3 z4 z5 z6 m2 MU2 WM2 MI2 ST2.
lazymatch type of MU2 with munch _ ?mc _ =>
transport_after_call asegs mc m2 MU2 WM2; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU2 WM2 end.
replace (ret_pc (Z_to_bv 64 0x656f8)) with (Z_to_bv 64 0x656f8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. if_false.
eapply J5; [exact MU | exact WM | exact MI2 | exact ST2 | exact FR].
- if_truex. eapply J5; [exact MU | exact WM | exact MI | exact ST | exact FR]. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (J3 : forall (x0 y2 y3 y4 y5 y6 y7 : word),
evt asegs Q (MS (mkR (Z_to_bv 64 0x65678) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x0 t1 t2 (Z_to_bv 64 s) (Z_to_bv 64 n)
(Z_to_bv 64 (AE / 8 + 2147450880)) (Z_to_bv 64 2147450880) y2 y3 y4 y5 y6 y7
(Z_to_bv 64 (s + n)) (Z_to_bv 64 (AB / 8 + 2147450880)) (Z_to_bv 64 AE) (Z_to_bv 64 991672) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x65694) fc None mc (seg_rom asegs)))
end.
{ intros x0 y2 y3 y4 y5 y6 y7. clear GZ GR0.
destruct HRL as (v & HR & Hv).
assert (Hv8 : 0 <= v < 128) by (destruct Hv as [->|(? & ?)]; lia).
step.
replace (s + n + -1) with (s + n - 1) by lia.
step. step. sh_norm.
replace (2147450880 + (s + n - 1) / 8) with ((s + n - 1) / 8 + 2147450880) by lia.
step. rewrite (sxb_small v) by lia. clear HR.
step.
destruct Hv as [-> | (Hk & Hlast)].
- if_true. apply J4.
- if_falsex.
step. rewrite (unsigned_lit (s + n - 1)) by lia. rewrite land7_mod8 by lia.
step. if_truex.
apply J4. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (J2 : forall (x0 y1 y2 y3 y4 y5 y6 y7 : word),
evt asegs Q (MS (mkR (Z_to_bv 64 0x65678) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x0 t1 t2 (Z_to_bv 64 s) (Z_to_bv 64 n)
(Z_to_bv 64 (AE / 8 + 2147450880)) y1 y2 y3 y4 y5 y6 y7
(Z_to_bv 64 (s + n)) (Z_to_bv 64 (AB / 8 + 2147450880)) (Z_to_bv 64 AE) (Z_to_bv 64 991672) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x65678) fc None mc (seg_rom asegs)))
end.
{ intros x0 y1 y2 y3 y4 y5 y6 y7. clear GZ.
step.
step. step. sh_norm.
replace (2147450880 + s / 8) with (s / 8 + 2147450880) by lia.
destruct (Z.lt_ge_cases (s / 8) ((s + n - 1) / 8)) as [Hlt | Hge].
- pose proof (GR0 (s / 8) ltac:(lia)) as HR.
step. rewrite ?sxb_zero. clear HR.
step. if_true. apply J3.
- destruct HRL as (v & HR & Hv).
assert (Hv8 : 0 <= v < 128) by (destruct Hv as [->|(? & ?)]; lia).
assert (Eg : s / 8 = (s + n - 1) / 8) by lia.
rewrite Eg. step. rewrite (sxb_small v) by lia. clear HR.
step.
destruct Hv as [-> | (Hk & Hlast)].
+ if_true. apply J3.
+ if_falsex.
step. rewrite (unsigned_lit s) by lia. rewrite land7_mod8 by lia.
step. if_falsex.
apply J3. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (J1 : forall (x0 y2 y3 y4 y5 y6 y7 : word),
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x0 t1 t2 (Z_to_bv 64 s) (Z_to_bv 64 n)
(Z_to_bv 64 2147450879) (Z_to_bv 64 2147450880) y2 y3 y4 y5 y6 y7
(Z_to_bv 64 (s + n)) s3 s4 (Z_to_bv 64 991672) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x65658) fc None mc (seg_rom asegs)))
end.
{ intros x0 y2 y3 y4 y5 y6 y7. clear GZ GR0 HRL.
step. if_falsex.
step. step.
rewrite (unsigned_lit (s + 7)) by lia. rewrite land_m8_64 by lia. fold AB.
step.
rewrite (unsigned_lit (s + n)) by lia. rewrite land_m8_64 by lia. fold AE.
step.
eapply mem_to_shadow_spec with (p := AB);
[ reflexivity | unfold A_SB, A_HMB; lia | exact (conj GOT (conj CELL (conj GMB (conj KMB (conj GME (conj KME (conj GHE KHE))))))) | exact MI | ].
intros z1 z2 z3 z4 z5 z6 z7 z8.
replace (ret_pc (Z_to_bv 64 0x6566c)) with (Z_to_bv 64 0x6566c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. step. step.
eapply mem_to_shadow_spec with (p := AE);
[ reflexivity | unfold A_SB, A_HMB; lia | exact (conj GOT (conj CELL (conj GMB (conj KMB (conj GME (conj KME (conj GHE KHE))))))) | exact MI | ].
intros w1 w2 w3 w4 w5 w6 w7 w8.
replace (ret_pc (Z_to_bv 64 0x65678)) with (Z_to_bv 64 0x65678) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
apply J2. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (J0 : forall (x0 y3 y4 y5 y6 y7 : word),
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x0 t1 t2 (Z_to_bv 64 s) (Z_to_bv 64 n)
(Z_to_bv 64 2147450879) (Z_to_bv 64 2147450880) (Z_to_bv 64 2147450879) y3 y4 y5 y6 y7
s2 s3 s4 (Z_to_bv 64 991672) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x65610) fc None mc (seg_rom asegs)))
end.
{ intros x0 y3 y4 y5 y6 y7. clear GZ GR0 HRL.
step.
try replace (n + s) with (s + n) by lia.
step.
destruct AM as [AML | (AMH1 & AMH2)].
- if_truex. apply J1.
- if_falsex.
do 6 step.
step.
step. if_truex.
do 3 step.
step. step. sh_norm.
step. if_falsex.
step. if_falsex.
apply J1. }

clear GZ GR0 HRL.
do 3 step.
step. step.
rewrite (v_sltu_0' (Z_to_bv 64 2147450880) (Z_to_bv 64 2147450879)) by (rewrite !unsigned_lit by lia; lia).
step. step.
step.
destruct AM as [AML | (AMH1 & AMH2)].
- if_truex. apply J0.
- if_falsex.
do 6 step.
step.
step. if_truex.
do 3 step.
step. step. sh_norm.
step. if_falsex.
step. if_falsex.
apply J0.
Qed.
End MuslARegion.
End RC__1.
