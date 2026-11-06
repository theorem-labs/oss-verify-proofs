(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply Lib.SepCache QWxq_c1 Qfw3_c1 Qc3B QRjH QHnV QCcH QfLs Q0Ek QjDH QmZZ Qsw7 QJjn QYIF QgoP Q7UD QXUB Qhd4 Qwm6 QlKV QsKa Q9O6 Qekr QJZd Qw5U Q1Ey Q2y2 QOmG Ql4f Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun QWxq_c1.Mq0 Qfw3_c1.Mq2 Qc3B.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn.
Import QYIF.
Import QgoP.
Import Q7UD QXUB.Mq0 Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq5 QsKa.Mq4 QlKV.Mq5 Q9O6.Mq0 Qekr.Mq0 QlKV.Mqa QsKa.Mq0 QJZd.Mq0 QsKa.Mq8 Qw5U.Mq0.

Import QsKa.Mq6.

Import QlKV.Mq2.
Import Q2y2.
Import QOmG Qw5U.Mq1 Ql4f.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac QlEo_c1.solve_load ::= QrJ1.Mq0.mkr__solve_load_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition SHB0 : list byte := map (Z_to_bv 8)
[0xf1;0xf1;0xf1;0xf1; 0xf8;0xf8;0xf8;0xf2; 0xf2;0xf2;0xf2;0xf2; 0xf8;0xf8;0xf8;0xf2; 0xf2;0xf2;0xf2;0xf2; 0xf8;0xf8;0xf8;0xf2; 0xf2;0xf2;0xf2;0xf2; 0xf8;0xf3;0xf3;0xf3].

Section AHarnJo1.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Lemma window_bytesG : forall (LBa : list blk) (data0 size : Z) m m' ptr rem data,
(size = 0 \/ In (data0, size) LBa) ->
bytes_at asegs m ptr data -> Z.of_nat (length data) = rem -> data0 <= ptr -> ptr + rem <= data0 + size ->
(forall a, 0 <= a < 2^64 -> in_block LBa a -> m' (wa a) = m (wa a)) ->
bytes_at asegs m' ptr data.
Proof.
intros LBa data0 size m m' ptr rem data INB B L P1 P2 E.
destruct INB as [Z0 | INB'].
- assert (data = []) as -> by (destruct data; [reflexivity | cbn in L; lia]).
destruct B as (B0' & B1 & _). split; [exact B0'|]. split; [exact B1|]. intros i Hi. cbn in Hi. lia.
- destruct B as (B0' & B1 & BB). split; [exact B0'|]. split; [exact B1|].
intros i Hi. rewrite <- (BB i Hi). unfold mrd. rewrite (E (ptr + Z.of_nat i)); [reflexivity | lia |].
exists (data0, size). split; [exact INB' | cbn; lia].
Qed.

Lemma cells_size_C1 : forall l : list byte, cells_size (map C1 l) = length l.
Proof. induction l as [|b l IH]; [reflexivity | cbn [map cells_size csize]; rewrite IH; reflexivity]. Qed.

Lemma GA_jo_pointwise : forall m m', GA_jo m -> lh_globA m' -> (forall a, 0xea500 <= a < 0xea528 -> m' (wa a) = m (wa a)) -> GA_jo m'.
Proof.
intros m m' (G1 & G2 & G3) L E. split; [exact L|]. split.
- unfold jhex_A in *. eapply bytes_at_pointwiseA; [exact G2|]. intros a Ha. rewrite length_le8 in Ha. apply E. lia.
- unfold utf8rep_A in *. eapply bytes_at_pointwiseA; [exact G3|]. intros a Ha. cbn [length] in Ha. apply E. lia.
Qed.
Lemma GA_jo_munch : forall m m' W, GA_jo m -> munch W m m' -> wmono asegs m m' -> Forall (fun iv : Z * Z => snd iv <= 0xea500 \/ 0xea568 <= fst iv) W -> GA_jo m'.
Proof.
intros m m' W G MU WM HW. eapply GA_jo_pointwise; [exact G | |].
- eapply lh_globA_frame; [exact (proj1 G) | exact MU | exact WM |]. eapply Forall_impl; [| exact HW]. intros [a b] H. cbn [fst snd] in *. unfold GHASHA, GSEEDA. lia.
- intros a Ha. apply MU. rewrite wa_unsigned by lia. clear - HW Ha. induction W as [|[u v] W IH]; cbn [outside]; [exact I|].
apply Forall_cons_iff in HW as [H HW]. cbn [fst snd] in H. split; [lia | apply IH; exact HW].
Qed.
Lemma GA_jo_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA_jo m -> GA_jo m'.
Proof.
intros LB SP m m' HPR G. eapply GA_jo_pointwise; [exact G | exact (lh_globA_client _ _ _ _ HPR (proj1 G)) |].
intros a Ha. apply (HPR a); [lia|]. right; left. cbn [hl_client_static A4H]. unfold a4_client_static. lia.
Qed.

Section Ctx.

Variables (sp0 : word) (sp1 lo Fr : Z) (LB0 LM : list blk) (m0 : word -> option byte) (md0 : config) (F0 : bvmap 5 word) (B0 : bud).
Variables (data0 size : Z) (payload : list byte).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= sp1 - (2^20 - 144).
Hypothesis SPA1 : sp1 mod 32 = 0.
Hypothesis SP10 : sp1 + 32 <= bv_unsigned sp0.
Hypothesis HT : bv_unsigned sp0 + 32 <= hiA_top A4L HIx.
Hypothesis HBOT : hiA_bot A4L HIx <= lo.
Hypothesis PLEN : Z.of_nat (length payload) = size.
Hypothesis SZ : 0 <= size < 2^26.
Hypothesis D0 : 0 < data0.
Hypothesis DCE : data0 + size <= alloc_ceiling.
Hypothesis INB : size = 0 \/ In (data0, size) LB0.

Hypothesis FRAL : Fr mod 256 = 0.
Hypothesis FRLO : 6574080 <= Fr.
Hypothesis FRHI : Fr + 256 <= alloc_ceiling.
Hypothesis FRAPP : Fr + 256 + 8 <= A_SB \/ A_HMB <= Fr.

Collection CtxAll := RC__ HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP.

Notation XT := (xtgt_A (bv_unsigned sp0)).

Definition HINVA (shb : list byte) (m : word -> option byte) (md : config) (F : bvmap 5 word) (fc : bv 32) (ptr rem : Z) (data : list byte) : Prop :=
heap_presx A4H XT (LB0 ++ LM) (sp1 + 32) m0 m /\
model_vm_only (cfg_model md0) (cfg_model md) /\ fsaved F0 F /\ frm0 fc /\
rw_cells asegs m T_LOCCELL_A [C8 (Z_to_bv 64 T_GLOBLOC_A)] /\ rw_cells asegs m T_LOCALE_LOCK_A [C4 (Z_to_bv 64 0)] /\ GA_jo m /\
stk asegs m lo sp1 /\
(exists j8, rw_cells asegs m sp1 [CB 8 j8; C8 (Z_to_bv 64 Fr)]) /\
rw_cells asegs m (sp1 + 16) [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 rem)] /\
(exists fj, rw_cells asegs m Fr [CB 248 fj]) /\
rw_cells asegs m (Fr / 8 + 2147450880) (map C1 shb) /\ length shb = 32%nat /\
bytes_at asegs m ptr data /\ Z.of_nat (length data) = rem /\ 0 < ptr /\ data0 <= ptr /\ ptr + rem <= data0 + size.

#[using="CtxAll"] Lemma HINVA_call : forall shb m m' md md' F F' fc fc' ptr rem data LBx,
HINVA shb m md F fc ptr rem data ->
heap_pres A4H (LBx ++ LM ++ fr_ivs A4L [(Fr, 2)]) sp1 m m' -> incl LB0 LBx ->
model_vm_only (cfg_model md) (cfg_model md') -> fsaved F F' -> frm0 fc' ->
stk asegs m' lo sp1 ->
HINVA shb m' md' F' fc' ptr rem data.
Proof.
intros shb m m' md md' F F' fc fc' ptr rem data LBx
(PX & VM & FS & FRM & LOC & LCK & G & ST & [j8 SL] & FD & [fj FF] & FSH & LSH & BY & L & P0 & P1 & P2) HPR Hi VM' FS' FRM' ST'.
assert (INF : In (Fr, 2) [(Fr, 2)]) by (left; reflexivity).
assert (SUB : forall b, In b (LB0 ++ LM) -> In b (LBx ++ LM ++ fr_ivs A4L [(Fr, 2)])).
{ intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply Hi; exact Hb | right; apply in_or_app; left; exact Hb]. }
assert (INBm : forall a, 0 <= a < 2^64 -> in_block LB0 a -> m' (wa a) = m (wa a)).
{ intros a Ha (b & Hb & Hr). apply (HPR a Ha). right; right. exists b. split; [apply in_or_app; left; apply Hi; exact Hb | exact Hr]. }
assert (LOCcs : forall a, 6434400 - 48 <= a < 6434400 - 48 + 8 -> hl_client_static A4H a) by (intros a Ha; cbn [hl_client_static A4H]; unfold a4_client_static; lia).
assert (LCKcs : forall a, 0x6431d0 <= a < 0x6431d0 + 4 -> hl_client_static A4H a) by (intros a Ha; cbn [hl_client_static A4H]; unfold a4_client_static; lia).
split. { eapply heap_presx_trans; [exact PX|]. apply heap_pres_presx. eapply heap_pres_weaken; [exact HPR | lia | exact SUB]. }
split. { eapply model_vm_only_trans; [exact VM | exact VM']. }
split. { eapply fsaved_trans; [exact FS | exact FS']. }
split. { exact FRM'. }
split. { eapply (heap_pres_rw_cells A4H); [exact HPR | exact LOC |]. right; left. cbn. intros z Hz. apply LOCcs. unfold T_LOCCELL_A, A_TP in Hz. lia. }
split. { eapply (heap_pres_rw_cells A4H); [exact HPR | exact LCK |]. right; left. cbn. intros z Hz. apply LCKcs. unfold T_LOCALE_LOCK_A in Hz. lia. }
split. { exact (GA_jo_pres _ _ _ _ HPR G). }
split. { exact ST'. }
split. { exists j8. eapply (heap_pres_rw_cells A4H); [exact HPR | exact SL |]. left. lia. }
split. { eapply (heap_pres_rw_cells A4H); [exact HPR | exact FD |]. left. lia. }
split. { exists fj. eapply (heap_pres_rw_cells A4H); [exact HPR | exact FF |].
eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; apply (Q1Ey.fr_ivs_frame _ _ _ INF) | lia | cbn; rewrite Q1Ey.fr_size_2; lia]. }
split. { eapply (heap_pres_rw_cells A4H); [exact HPR | exact FSH |].
eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; apply (Q1Ey.fr_ivs_shadow _ _ _ INF) | unfold shad; cbn [hl_sb A4L]; unfold A_SB; lia | rewrite cells_size_C1, LSH; cbn [blk_addr blk_size fst snd]; rewrite Q1Ey.fr_shadow_len_2; unfold shad; cbn [hl_sb A4L]; unfold A_SB; lia]. }
split. { exact LSH. }
split. { eapply (window_bytesG LB0 data0 size); [exact INB | exact BY | exact L | exact P1 | exact P2 | exact INBm]. }
repeat split; assumption.
Qed.

#[using="CtxAll"] Lemma fdp_evidenceA : forall A LBx B m md ptr rem,
HEAPAx A LBx LM [(Fr, 2)] B m md -> incl LB0 LBx -> data0 <= ptr -> ptr + rem <= data0 + size ->
asan_rt_ok m /\ unpoisoned asegs m A_SB (sp1 + 16) 16 /\ (0 < rem -> unpoisoned asegs m A_SB ptr rem).
Proof.
intros A LBx B m md ptr rem HP Hi P1 P2. pose proof alloc_ceiling_range as ACR. pose proof (hiA_top_le A4L HIx) as HT47.
split; [exact (asan_rt_ok_of_HEAPA HIx _ _ _ _ _ _ _ HP)|]. split.
- pose proof (heapA_shadow_stack A4L HIx _ _ _ _ _ _ _ (sp1 - 32) 96 HP ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as SHS.
unfold shad in SHS. cbn [hl_sb A4L] in SHS.
replace (Z.to_nat ((sp1 - 32 + 96 - 1) / 8 - (sp1 - 32) / 8 + 1)) with 12%nat in SHS by (clear - SPA1; Z.div_mod_to_equations; lia).
eapply (unpoisoned_of_run m ((sp1 - 32) / 8) 12); [exact SHS | clear - LO LOS ACR; Z.div_mod_to_equations; lia | lia | clear - SPA1; Z.div_mod_to_equations; lia | clear - SPA1; Z.div_mod_to_equations; lia].
- intros Hr. destruct INB as [Z0 | INB']; [lia|].
eapply (unpoisoned_of_blk HIx _ _ _ _ _ _ _ data0 size ptr rem HP (Hi _ INB')); lia.
Qed.

Lemma cells_bytes_C1 : forall l : list byte, cells_bytes (map C1 l) = l.
Proof. induction l as [|b l IH]; [reflexivity | cbn [map cells_bytes cbytes app]; rewrite IH; reflexivity]. Qed.

#[using="CtxAll"] Lemma fslot_evidenceA : forall m (shb : list byte) (g0 g1 : nat),
rw_cells asegs m (Fr / 8 + 2147450880) (map C1 shb) -> length shb = 32%nat -> (g0 < g1)%nat -> (g1 <= 32)%nat ->
forallb (fun b => bv_unsigned b =? 0) (firstn (g1 - g0) (skipn g0 shb)) = true ->
unpoisoned asegs m A_SB (Fr + 8 * Z.of_nat g0) (8 * Z.of_nat (g1 - g0)).
Proof.
intros m shb g0 g1 FSH L Hg Hg1 Z0. pose proof (rw_cells_bytes_at asegs _ _ _ FSH) as SB. rewrite cells_bytes_C1 in SB.
eapply (unpoisoned_of_fshadow m Fr shb g0 g1); [unfold A_SB; exact SB | exact L | exact FRAL | lia | exact Hg | exact Hg1 | exact Z0].
Qed.

Definition own_iv (iv : Z * Z) : Prop :=
(lo <= fst iv /\ snd iv <= sp1 + 32) \/ (Fr <= fst iv /\ snd iv <= Fr + 248) \/ (Fr / 8 + 2147450880 <= fst iv /\ snd iv <= Fr / 8 + 2147450880 + 32).

#[using="CtxAll"] Lemma own_writesA : forall A LBx B m mX md W,
HEAPAx A LBx LM [(Fr, 2)] B m md -> incl LB0 LBx ->
munch W m mX -> wmono asegs m mX -> mem_inv asegs mX -> Forall own_iv W ->
HEAPAx A LBx LM [(Fr, 2)] B mX md /\ heap_presx A4H XT (LB0 ++ LM) (sp1 + 32) m mX /\ agree_on asegs (LBx ++ LM) m mX.
Proof.
intros A LBx B m mX md W HP Hi MU WM MI HW. pose proof alloc_ceiling_range as ACR. pose proof (hiA_top_le A4L HIx) as HT47.
assert (INF : In (Fr, 2) [(Fr, 2)]) by (left; reflexivity).
destruct (own_frame_fresh HIx Fr 2 LBx LB0 LM [] B A m md HP Hi) as [OFF OFS]. cbn [fr_ivs flat_map app] in OFF, OFS. rewrite app_nil_r in OFF, OFS.
split; [| split].
- eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MI]. eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP MU).
eapply Forall_impl; [| exact HW]. intros [a b] [H | [H | H]]; cbn [fst snd] in *.
+ left. lia.
+ right; right; right. exists Fr, 2. split; [exact INF|]. left. rewrite Q1Ey.fr_size_2. lia.
+ right; right; right. exists Fr, 2. split; [exact INF|]. right. unfold shad. cbn [hl_sb A4L]. rewrite Q1Ey.fr_shadow_len_2. unfold A_SB. lia.
- eapply (presx_ownA HIx XT _ _ _ _ _ _ _ _ _ _ _ HP MU WM).
+ intros b Hb. left. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply Hi; exact Hb | right; exact Hb].
+ lia.
+ eapply Forall_impl; [| exact HW]. intros [a b] [H | [H | H]]; cbn [fst snd] in *.
* left. lia.
* right; right; right. exists Fr, 2. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. rewrite Q1Ey.fr_size_2. lia.
* right; right; right. exists Fr, 2. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. right. unfold shad. cbn [hl_sb A4L]. rewrite Q1Ey.fr_shadow_len_2. unfold A_SB. lia.
- eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros a n Hin.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a n HP Hin) as (_ & _ & Ha0 & Hac & _).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF Hin) as DF. rewrite Q1Ey.fr_size_2 in DF.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ a n HP Hin) as APP. cbn [hl_sb A4L] in APP. unfold A_SB in APP.
change ((2 ^ 47 - 1) / 8 + 2147450880 + 1) with 17594333495296 in APP.
clear - HW Ha0 Hac DF APP LO FRLO FRHI ACR. induction W as [|[u v] W IH]; cbn [disjoint_from]; [exact I|].
apply Forall_cons_iff in HW as [H HW]. split; [| apply IH; exact HW]. destruct H as [H | [H | H]]; cbn [fst snd] in H; Z.div_mod_to_equations; lia.
Qed.

#[using="CtxAll"] Lemma GA_jo_own : forall m mX W, GA_jo m -> munch W m mX -> wmono asegs m mX -> Forall own_iv W -> GA_jo mX.
Proof.
intros m mX W G MU WM HW. pose proof alloc_ceiling_range as ACR.
eapply GA_jo_munch; [exact G | exact MU | exact WM |]. eapply Forall_impl; [| exact HW].
intros [a b] [H | [H | H]]; cbn [fst snd] in *; right; [lia | lia | Z.div_mod_to_equations; lia].
Qed.

Section Getters.
Variables (p : Z) (s11 : word) (T : TSet).
Hypothesis BB0 : TGT_BB_A_jo <= bB B0.
Hypothesis BD0 : TGT_BD_A_jo <= bD B0.

Definition hstateA (s10v : word) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (pc : Z) (fc : bv 32) (m : word -> option byte) :=
MS (mkR x1 (Z_to_bv 64 sp1) gp (Z_to_bv 64 A_TP) t0 t1 t2 sp0 (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 Fr) (Z_to_bv 64 (Fr + 160)) (Z_to_bv 64 p) (Z_to_bv 64 (Fr + 224)) (Z_to_bv 64 (Fr + 96)) (Z_to_bv 64 (Fr / 8 + 2147450880))
(Z_to_bv 64 Fr) (Z_to_bv 64 2147450880) s10v s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom asegs).
Notation gstateA := (hstateA (Z_to_bv 64 (-8))).

Definition GINVA (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (F : bvmap 5 word) (fc : bv 32)
(ptr rem : Z) (data : list byte) (s : option jshape) (BS LK : list blk) (sb sd : Z) : Prop :=
HINVA SHB0 m md F fc ptr rem data /\ HEAPAx A (BS ++ LK ++ LB0) LM [(Fr, 2)] B m md /\ jopt asegs A4F s m BS p /\ odepth s <= 32 /\
bB B0 - sb <= bB B /\ bD B0 - sd <= bD B.

Definition KGA (k : Z) (s : option jshape) (BS : list blk) (sb sd : Z) : Prop :=
forall m' md' (A' : ASA A4L HIx) B' F' fc' ptr' rem' data' LK' (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
GINVA m' md' A' B' F' fc' ptr' rem' data' s BS LK' sb sd ->
AJ5 A4L HIx A' T md' (gstateA x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' k fc' m').

#[using="CtxAll p s11 T BB0 BD0"] Lemma sp1_16 : sp1 mod 16 = 0.
Proof. clear - SPA1. Z.div_mod_to_equations. lia. Qed.

#[using="CtxAll p s11 T BB0 BD0"] Lemma pure_callA : forall (pc f : Z) m md (A : ASA A4L HIx) B F fc ptr rem data s BS LK sb sd
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
jo_get_pure_A_stmt HIx f ->
(pc = 0x91c78 /\ f = 0x9c0e4 \/ pc = 0x91ca8 /\ f = 0x9e810 \/ pc = 0x91cb0 /\ f = 0x9bdf0 \/ pc = 0x91cb8 /\ f = 0x9ec44 \/ pc = 0x91cc0 /\ f = 0x9ae00) ->
GINVA m md A B F fc ptr rem data s BS LK sb sd ->
KGA (pc + 8) s BS sb sd ->
AJ5 A4L HIx A T md (gstateA x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F pc fc m).
Proof.
intros pc f m md A B F fc ptr rem data s BS LK sb sd x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 GP Hpc (INV & HP & JO & OD & BB & BD) K.
pose proof INV as (PX & VM & FS & FRM & LOC & LCK & G & ST & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. change (hl_segs A4L) with asegs in MI.
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP) as (errv & ERR).
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof sp1_16 as SP16. pose proof alloc_ceiling_range as ACR. pose proof (hiA_top_le A4L HIx) as HT47.
pose proof (bv_unsigned_in_range 64 sp0) as SP0R. change (bv_modulus 64) with (2^64) in SP0R.
unfold hstateA.
reenterA asegs A4L HIx asegs_wx HP.
unfold A_TP in *. cbn [hl_tp hl_segs A4L A4H hla_base] in ERR.
destruct Hpc as [[-> ->] | [[-> ->] | [[-> ->] | [[-> ->] | [-> ->]]]]].
all: (step; step; evt_done5;
eapply GP with (BS := BS) (LB := LK ++ LB0) (s := s) (lo := lo) (errv := errv);
[ split; [exact HP|]; rewrite unsigned_lit by lia;
split; [exact ST|]; split; [exact LO|]; split; [lia|]; split; [exact SP16|]; split; [lia|];
split; [exact ERR|]; split; [reflexivity | vm_compute; reflexivity]
| exact JO | exact FRM | reflexivity |]).
all: (intros ms' md' m' rv (RS & VM' & ST' & HPR' & [errv' ERR']) ERRk JO' HP';
destruct RS as (xt0 & xt1 & xt2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & F' & fc' & -> & FS' & FRM');
rewrite unsigned_lit in ST', HPR' by lia;
lazymatch goal with |- AJ5of _ _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end;
lazymatch type of K with KGA ?e _ _ _ _ => let v := eval vm_compute in e in change e with v in K end;
unfold KGA, hstateA in K; eapply K; split;
[ eapply (HINVA_call SHB0 m m' md md' F F' fc fc' ptr rem data (LK ++ LB0) INV HPR' ltac:(intros b Hb; apply in_or_app; right; exact Hb) VM' FS' (FRM' FRM) ST')
| split; [exact HP' | split; [exact JO' | split; [exact OD | split; [exact BB | exact BD]]]]]).
Qed.

Ltac callA_open INV HP m :=
pose proof INV as (PX & VM & FS & FRM & LOC & LCK & G & ST & _);
pose proof (heapA_mem_inv _ HIx _ _ _ _ _ _ _ HP) as MI; change (hl_segs _) with asegs in MI;
destruct (heapA_errno _ HIx _ _ _ _ _ _ _ HP) as (errv & ERR);
pose proof (munch_refl [] m) as MU; pose proof (wmono_refl asegs m) as WM;
pose proof sp1_16 as SP16; pose proof alloc_ceiling_range as ACR; pose proof (hiA_top_le _ HIx) as HT47;
pose proof (bv_unsigned_in_range 64 sp0) as SP0R; change (bv_modulus 64) with (2^64) in SP0R;
unfold hstateA;
(let L := constr:(A4L) in reenterA asegs L HIx asegs_wx HP);
unfold A_TP in *; cbn [hl_tp hl_segs A4L A4H hla_base] in ERR.
Ltac preA_solve HP ST ERR :=
split; [exact HP|]; rewrite unsigned_lit by lia;
split; [exact ST|]; split; [exact LO|]; split; [unfold TGT_STACK_A_jo in *; lia|]; split; [exact sp1_16|]; split; [lia|];
split; [exact ERR|]; split; [reflexivity | vm_compute; reflexivity].
Ltac ret_norm :=
lazymatch goal with |- AJ5of _ _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end.

#[using="CtxAll p s11 T BB0 BD0"] Lemma num_callA : forall (pc f : Z) m md (A : ASA A4L HIx) B F fc ptr rem data s BS LK sb sd
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
jo_get_num_A_stmt HIx f JO_GETNUM_STK_A ->
(pc = 0x91c88 /\ f = 0x9c460 \/ pc = 0x91c90 /\ f = 0x9cb08 \/ pc = 0x91c98 /\ f = 0x9cf10) ->
GINVA m md A B F fc ptr rem data s BS LK sb sd ->
KGA (pc + 8) s BS sb sd ->
AJ5 A4L HIx A T md (gstateA x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F pc fc m).
Proof.
intros pc f m md A B F fc ptr rem data s BS LK sb sd x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 GN Hpc (INV & HP & JO & OD & BB & BD) K.
callA_open INV HP m. unfold JO_GETNUM_STK_A in GN.
destruct Hpc as [[-> ->] | [[-> ->] | [-> ->]]].
all: (step; step; evt_done5;
eapply GN with (A := A) (BS := BS) (LB := LK ++ LB0) (s := s) (lo := lo) (errv := errv);
[ preA_solve HP ST ERR | exact JO | cbn [length]; lia | rewrite unsigned_lit by lia; exact SPA1 | exact FRM | reflexivity |];
intros ms' md' m' r A' (RS & VM' & ST' & HPR' & [errv' ERR']) JO' HP';
destruct RS as (xt0 & xt1 & xt2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & F' & fc' & -> & FS' & FRM');
rewrite unsigned_lit in ST', HPR' by lia; ret_norm;
lazymatch type of K with KGA ?e _ _ _ _ => let v := eval vm_compute in e in change e with v in K end;
unfold KGA, hstateA in K; eapply K; split;
[ eapply (HINVA_call SHB0 m m' md md' F F' fc fc' ptr rem data (LK ++ LB0) INV HPR' ltac:(intros b Hb; apply in_or_app; right; exact Hb) VM' FS' (FRM' FRM) ST')
| split; [exact HP' | split; [exact JO' | split; [exact OD | split; [exact BB | exact BD]]]]]).
Qed.

#[using="CtxAll p s11 T BB0 BD0"] Lemma dbl_callA : forall m md (A : ASA A4L HIx) B F fc ptr rem data s BS LK sb sd
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
jo_get_double_A_stmt HIx JO_GET_DOUBLE_A JO_GETDBL_STK_A JO_GETDBL_COSTB_A JO_GETDBL_COSTD_A ->
sb + JO_GETDBL_COSTB_A <= TGT_BB_A_jo -> sd + JO_GETDBL_COSTD_A <= TGT_BD_A_jo ->
GINVA m md A B F fc ptr rem data s BS LK sb sd ->
KGA 0x91c88 s BS (sb + JO_GETDBL_COSTB_A) (sd + JO_GETDBL_COSTD_A) ->
AJ5 A4L HIx A T md (gstateA x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x91c80 fc m).
Proof.
intros m md A B F fc ptr rem data s BS LK sb sd x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 GD CB CD (INV & HP & JO & OD & BB & BD) K.
callA_open INV HP m. unfold JO_GET_DOUBLE_A, JO_GETDBL_STK_A, JO_GETDBL_COSTB_A, JO_GETDBL_COSTD_A in *.
step. step. evt_done5.
eapply GD with (A := A) (BS := BS) (LB := LK ++ LB0) (s := s) (lo := lo) (errv := errv);
[ preA_solve HP ST ERR | exact JO | cbn [length]; lia | lia | lia | rewrite unsigned_lit by lia; exact SPA1 | exact FRM | reflexivity |].
intros ms' md' m' r A' B' (RS & VM' & ST' & HPR' & [errv' ERR']) [CHB CHD] JO' HP'.
destruct RS as (xt0 & xt1 & xt2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & F' & fc' & -> & FS' & FRM').
rewrite unsigned_lit in ST', HPR' by lia. ret_norm.
unfold KGA, hstateA in K. eapply K. split;
[ eapply (HINVA_call SHB0 m m' md md' F F' fc fc' ptr rem data (LK ++ LB0) INV HPR' ltac:(intros b Hb; apply in_or_app; right; exact Hb) VM' FS' (FRM' FRM) ST')
| split; [exact HP' | split; [exact JO' | split; [exact OD | split; lia]]]].
Qed.

#[using="CtxAll p s11 T BB0 BD0"] Lemma visit_callA : forall m md (A : ASA A4L HIx) B F fc ptr rem data s BS LK sb sd
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
jo_visit_A_stmt HIx JO_VISIT_A JO_EMIT_A JO_VISIT_STK0_A JO_VISIT_STK1_A ->
GINVA m md A B F fc ptr rem data s BS LK sb sd ->
KGA 0x91ce0 s BS sb sd ->
AJ5 A4L HIx A T md (gstateA x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x91cc8 fc m).
Proof.
intros m md A B F fc ptr rem data s BS LK sb sd x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 VI (INV & HP & JO & OD & BB & BD) K.
callA_open INV HP m. unfold JO_VISIT_A, JO_EMIT_A, JO_VISIT_STK0_A, JO_VISIT_STK1_A in *.
assert (OD0 : 0 <= odepth s) by (destruct s as [sh|]; cbn [odepth]; [pose proof (Q0Ek.sdepth_nonneg sh) | ]; lia).
step. step. step. step. step. step. evt_done5.
eapply VI with (A := A) (BS := BS) (LB := LK ++ LB0) (s := s) (lo := lo) (errv := errv);
[ preA_solve HP ST ERR | exact JO | cbn [length]; lia | reflexivity | reflexivity | reflexivity | reflexivity |].
intros ms' md' m' r A' (RS & VM' & ST' & HPR' & [errv' ERR']) -> JO' HP'.
destruct RS as (xt0 & xt1 & xt2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & F' & fc' & -> & FS' & FRM').
rewrite unsigned_lit in ST', HPR' by lia. ret_norm.
unfold KGA, hstateA in K. eapply K. split;
[ eapply (HINVA_call SHB0 m m' md md' F F' fc fc' ptr rem data (LK ++ LB0) INV HPR' ltac:(intros b Hb; apply in_or_app; right; exact Hb) VM' FS' (FRM' FRM) ST')
| split; [exact HP' | split; [exact JO' | split; [exact OD | split; [exact BB | exact BD]]]]].
Qed.

#[using="CtxAll p s11 T BB0 BD0"] Lemma str_callA : forall (gsS : jshape -> Z) (gsB : Z -> Z) m md (A : ASA A4L HIx) B F fc ptr rem data s BS LK sb sd (gc : Z)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
jo_get_string_A_stmt HIx JO_GET_STRING_A gsS gsB -> jo_get_string_null_A_stmt HIx JO_GET_STRING_A JO_GETSTR_STK0_A ->
0 <= gc -> sb + gc <= TGT_BB_A_jo ->
(forall sh, s = Some sh -> exists w, jtx sh BS = Some (w, []) /\ w < 2^27 /\ gsS sh <= 2^20 - 144 /\ gsB w <= gc) ->
GINVA m md A B F fc ptr rem data s BS LK sb sd ->
(forall BS', (forall sh w, s = Some sh -> jtx sh BS = Some (w, []) -> exists PT, jtx sh BS' = Some (w, PT)) -> KGA 0x91ca8 s BS' (sb + gc) sd) ->
AJ5 A4L HIx A T md (gstateA x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x91ca0 fc m).
Proof.
intros gsS gsB m md A B F fc ptr rem data s BS LK sb sd gc x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 GS GS0 GC0 CBT CST (INV & HP & JO & OD & BB & BD) K.
pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP) as [_ BD00].
callA_open INV HP m. unfold JO_GET_STRING_A, JO_GETSTR_STK0_A in *.
step. step. evt_done5.
destruct s as [sh|].
- destruct JO as [Hp J]. cbn [odepth] in OD. destruct (CST sh eq_refl) as (w & JTX & W27 & C1 & C2).
eapply GS with (A := A) (BS := BS) (LB := LK ++ LB0) (s := sh) (lo := lo) (errv := errv) (rc := 1) (w := w);
[ preA_solve HP ST ERR | exact J | lia | exact (proj1 (proj2 G)) | exact JTX | exact W27 | cbn [length]; lia | lia | exact BD00 | exact FRM | reflexivity |].
intros ms' md' m' A' B' r errv' BS' PT' RS VM' ST' HPR' ERR' [CHB CHD] HP' J' JTX' PTL.
destruct RS as (xt0 & xt1 & xt2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & F' & fc' & -> & FS' & FRM').
rewrite unsigned_lit in ST', HPR' by lia. ret_norm.
pose proof (K BS' ltac:(intros sh0 w0 E JT; injection E as <-; rewrite JTX in JT; injection JT as <-; exists PT'; exact JTX')) as K0. unfold KGA, hstateA in K0. eapply K0. split;
[ eapply (HINVA_call SHB0 m m' md md' F F' fc fc' ptr rem data (LK ++ LB0) INV HPR' ltac:(intros b Hb; apply in_or_app; right; exact Hb) VM' FS' (FRM' FRM) ST')
| split; [exact HP' | split; [split; [exact Hp | exact J'] | split; [exact OD | split; lia]]]].
- destruct JO as [Hp EBS]. rewrite Hp. subst BS. cbn [app] in HP.
eapply GS0 with (lo := lo) (errv := errv); [ preA_solve HP ST ERR |].
intros ms' md' m' rv (RS & VM' & ST' & HPR' & [errv' ERR']) ERRk HP'.
destruct RS as (xt0 & xt1 & xt2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & F' & fc' & -> & FS' & FRM').
rewrite unsigned_lit in ST', HPR' by lia. ret_norm.
pose proof (K [] ltac:(intros sh0 w0 E JT; discriminate E)) as K0. unfold KGA, hstateA in K0. rewrite <- Hp. eapply K0. split;
[ eapply (HINVA_call SHB0 m m' md md' F F' fc fc' ptr rem data (LK ++ LB0) INV HPR' ltac:(intros b Hb; apply in_or_app; right; exact Hb) VM' FS' (FRM' FRM) ST')
| split; [exact HP' | split; [split; [exact Hp | reflexivity] | split; [exact OD | split; [lia | exact BD]]]]].
Qed.
Variables (tpB tpD : Z -> Z) (dcB dcD : Z -> Z) (gsS : jshape -> Z) (gsB : Z -> Z).
Hypothesis CA : jo_callees_A HIx tpB tpD dcB dcD gsS gsB.

#[using="CtxAll p s11 T BB0 BD0 tpB tpD dcB dcD gsS gsB CA"] Lemma seg_gettersA : forall m md (A : ASA A4L HIx) B F fc ptr rem data s BS LK sb sd (gc : Z)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
0 <= gc ->
(forall sh, s = Some sh -> exists w, jtx sh BS = Some (w, []) /\ w < 2^27 /\ gsS sh <= 2^20 - 144 /\ gsB w <= gc) ->
sb + JO_GETDBL_COSTB_A + gc <= TGT_BB_A_jo -> sd + JO_GETDBL_COSTD_A <= TGT_BD_A_jo ->
GINVA m md A B F fc ptr rem data s BS LK sb sd ->
(forall BS', (forall sh w, s = Some sh -> jtx sh BS = Some (w, []) -> exists PT, jtx sh BS' = Some (w, PT)) -> KGA 0x91ce0 s BS' (sb + JO_GETDBL_COSTB_A + gc) (sd + JO_GETDBL_COSTD_A)) ->
AJ5 A4L HIx A T md (gstateA x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x91c78 fc m).
Proof.
intros m md A B F fc ptr rem data s BS LK sb sd gc x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 GC0 CST CB CD GI K.
Ltac kga_next := unfold KGA; intros;
lazymatch goal with |- AJ5of _ _ _ _ _ (hstateA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?pc _ _) =>
let v := eval vm_compute in pc in change pc with v end.
Ltac pc_pick := (repeat first [ left; split; reflexivity | right ]; try (split; reflexivity)).
eapply (pure_callA 0x91c78 0x9c0e4); [exact (ca_GETB _ _ _ _ _ _ _ CA) | pc_pick | exact GI |]. kga_next.
assert (CB1 : sb + JO_GETDBL_COSTB_A <= TGT_BB_A_jo) by lia.
eapply dbl_callA; [exact (ca_GETD _ _ _ _ _ _ _ CA) | exact CB1 | exact CD | eassumption |]. kga_next.
eapply (num_callA 0x91c88 0x9c460); [exact (ca_GETI _ _ _ _ _ _ _ CA) | pc_pick | eassumption |]. kga_next.
eapply (num_callA 0x91c90 0x9cb08); [exact (ca_GETI64 _ _ _ _ _ _ _ CA) | pc_pick | eassumption |]. kga_next.
eapply (num_callA 0x91c98 0x9cf10); [exact (ca_GETU64 _ _ _ _ _ _ _ CA) | pc_pick | eassumption |]. kga_next.
eapply (str_callA gsS gsB) with (gc := gc); [exact (ca_GETS _ _ _ _ _ _ _ CA) | exact (ca_GETS0 _ _ _ _ _ _ _ CA) | exact GC0 | exact CB | exact CST | eassumption |].
kga_next.
eapply (pure_callA 0x91ca8 0x9e810); [exact (ca_GETSL _ _ _ _ _ _ _ CA) | pc_pick | eassumption |]. kga_next.
eapply (pure_callA 0x91cb0 0x9bdf0); [exact (ca_GETO _ _ _ _ _ _ _ CA) | pc_pick | eassumption |]. kga_next.
eapply (pure_callA 0x91cb8 0x9ec44); [exact (ca_GETA _ _ _ _ _ _ _ CA) | pc_pick | eassumption |]. kga_next.
eapply (pure_callA 0x91cc0 0x9ae00); [exact (ca_GETT _ _ _ _ _ _ _ CA) | pc_pick | eassumption |]. kga_next.
eapply visit_callA; [exact (ca_VISIT _ _ _ _ _ _ _ CA) | eassumption | apply K; assumption].
Qed.
End Getters.
End Ctx.
End AHarnJo1.
End RC__1.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qtgi QRUw QkMG QG8z Qdyh QLbz QrQv QEUF QdGy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QCcH Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QRUw.Mq0 QkMG. Import QG8z Qdyh.Mq2 QLbz.
Import Q7UD QlKV.Mq2 QrQv.Mq2 QEUF.Mq1 QdGy.Mq3.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma JL_lvl : forall ts ts' l l' g g' a a' w',
nth_error (t_levels ts) (t_depth ts) = Some l ->
t_levels ts' = lupd (t_levels ts) (t_depth ts) l' -> t_depth ts' = t_depth ts -> t_objs ts' = t_objs ts -> t_objbs ts' = t_objbs ts ->
lw l' = Some w' -> zin (tl_st l') [ST_array_add; ST_ovadd] = zin (tl_st l) [ST_array_add; ST_ovadd] ->
JL ts g a ->
(forall w0, lw l = Some w0 -> 0 <= w0 ->
w' + jtext (tl_st l') g' + jpi (tl_st l') (tl_ss l') <= w0 + jtext (tl_st l) g + jpi (tl_st l) (tl_ss l) + JC1 * (a' - a)) ->
JL ts' g' a'.
Proof.
intros [d lv co pb pbs x o os obs] [d' lv' co' pb' pbs' x' o' os' obs'] l l' g g' a a' w'. cbn [t_levels t_depth t_objs t_objbs].
intros Hl -> -> -> -> Lw Hz J H.
eapply (JL_upd d lv l l' co pb pbs x o os obs co' pb' pbs' x' g g' a a' w' Hl Lw Hz) in J; [| exact H].
destruct J as (W & E & L). exists W. split; [| exact L].
rewrite <- E. unfold jw. cbn [t_levels t_depth t_objs t_objbs]. reflexivity.
Qed.

Lemma JL_lvl_restate : forall ts ts' l l' g g' a a',
nth_error (t_levels ts) (t_depth ts) = Some l ->
t_levels ts' = lupd (t_levels ts) (t_depth ts) l' -> t_depth ts' = t_depth ts -> t_objs ts' = t_objs ts -> t_objbs ts' = t_objbs ts ->
tl_cs l' = tl_cs l -> tl_cbs l' = tl_cbs l -> tl_nbs l' = tl_nbs l ->
zin (tl_st l') [ST_array_add; ST_ovadd] = zin (tl_st l) [ST_array_add; ST_ovadd] ->
JL ts g a ->
jtext (tl_st l') g' + jpi (tl_st l') (tl_ss l') <= jtext (tl_st l) g + jpi (tl_st l) (tl_ss l) + JC1 * (a' - a) ->
JL ts' g' a'.
Proof.
intros ts ts' l l' g g' a a' Hl E1 E2 E3 E4 C1 C2 C3 Hz J H.
destruct (JL_jw _ _ _ J) as (W & EW).
assert (Lw : exists w0, lw l = Some w0).
{ destruct ts as [d lv co pb pbs x o os obs]. cbn [t_levels t_depth] in Hl. unfold jw in EW. cbn [t_levels t_depth] in EW.
destruct (jwl lv (S d)) as [A|] eqn:EA; [| discriminate EW]. exact (jwl_nth lv (S d) d l A EA Hl ltac:(lia)). }
destruct Lw as (w0 & Lw0).
eapply (JL_lvl ts ts' l l' g g' a a' w0 Hl E1 E2 E3 E4); [rewrite (lw_restate l l' C1 C2 C3); exact Lw0 | exact Hz | exact J |].
intros w1 Lw1 _. rewrite Lw0 in Lw1. injection Lw1 as <-. lia.
Qed.

Lemma JL_keep : forall ts ts' g g' a a', t_levels ts' = t_levels ts -> t_depth ts' = t_depth ts -> t_objs ts' = t_objs ts -> t_objbs ts' = t_objbs ts ->
g' <= g -> a <= a' -> JL ts g a -> JL ts' g' a'.
Proof.
intros ts ts' g g' a a' E1 E2 E3 E4 Hg Ha J. eapply (JL_same ts ts'); [exact E1 | exact E2 | intros _; split; [exact E3 | exact E4] |].
eapply JL_mono; [exact Hg | exact Ha | exact J].
Qed.

Lemma lw_attach : forall st' ss' r sh BS nm w, jfresh sh BS w -> lw (TL st' ss' r (Some sh) BS nm []) = Some w.
Proof. intros st' ss' r sh BS nm w H. unfold lw. cbn [tl_cs tl_cbs tl_nbs]. rewrite (vw_fresh _ _ _ H). cbn [nw]. f_equal. lia. Qed.
Lemma lw_value : forall l, (exists w0, lw l = Some w0) -> exists v, vw (tl_cs l) (tl_cbs l) = Some v /\ lw l = Some (v + nw (tl_nbs l)).
Proof. intros l (w0 & H). unfold lw in *. destruct (vw (tl_cs l) (tl_cbs l)) as [v|]; [| discriminate H]. exists v. split; reflexivity. Qed.
Lemma lw_rename : forall l st' ss' nm' nbs' v, vw (tl_cs l) (tl_cbs l) = Some v -> lw (TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) nm' nbs') = Some (v + nw nbs').
Proof. intros l st' ss' nm' nbs' v H. unfold lw. cbn [tl_cs tl_cbs tl_nbs]. rewrite H. reflexivity. Qed.
Lemma lw_arr : forall l kids, tl_cs l = Some (Sarr kids) -> forall w0, lw l = Some w0 -> exists w, jtx (Sarr kids) (tl_cbs l) = Some (w, []) /\ w0 = w + nw (tl_nbs l).
Proof.
intros l kids E w0 H. unfold lw in H. rewrite E in H. cbn [vw] in H. destruct (jtx (Sarr kids) (tl_cbs l)) as [[w [|? ?]]|] eqn:J; try discriminate H.
injection H as <-. exists w. split; reflexivity.
Qed.
Lemma lw_obj : forall l kids, tl_cs l = Some (Sobj kids) -> forall w0, lw l = Some w0 -> exists w, jtx (Sobj kids) (tl_cbs l) = Some (w, []) /\ w0 = w + nw (tl_nbs l).
Proof.
intros l kids E w0 H. unfold lw in H. rewrite E in H. cbn [vw] in H. destruct (jtx (Sobj kids) (tl_cbs l)) as [[w [|? ?]]|] eqn:J; try discriminate H.
injection H as <-. exists w. split; reflexivity.
Qed.
Lemma lw_container : forall st' ss' cur s cbs nm nbs w, jtx s cbs = Some (w, []) -> lw (TL st' ss' cur (Some s) cbs nm nbs) = Some (w + nw nbs).
Proof. intros st' ss' cur s cbs nm nbs w H. unfold lw. cbn [tl_cs tl_cbs tl_nbs vw]. rewrite H. reflexivity. Qed.

Lemma vw_kid : forall os obs b, vw os obs = Some b -> (os = None -> obs = []) -> exists wv, jtx_opt os obs = Some (wv, []) /\ wv <= b + NULL_W.
Proof.
intros [s|] obs b H Hn; cbn [vw jtx_opt] in *.
- destruct (jtx s obs) as [[w [|? ?]]|]; try discriminate H. injection H as <-. exists w. split; [reflexivity | unfold NULL_W; lia].
- injection H as <-. rewrite (Hn eq_refl). exists NULL_W. split; [reflexivity | lia].
Qed.

Lemma JL_add : forall ts ts' l l' g g' a a' w',
nth_error (t_levels ts) (t_depth ts) = Some l ->
t_levels ts' = lupd (t_levels ts) (t_depth ts) l' -> t_depth ts' = t_depth ts ->
lw l' = Some w' -> zin (tl_st l) [ST_array_add; ST_ovadd] = true -> zin (tl_st l') [ST_array_add; ST_ovadd] = false ->
JL ts g a ->
(forall w0 b, lw l = Some w0 -> vw (t_objs ts) (t_objbs ts) = Some b ->
w' + jtext (tl_st l') g' + jpi (tl_st l') (tl_ss l') <= w0 + b + jtext (tl_st l) g + jpi (tl_st l) (tl_ss l) + JC1 * (a' - a)) ->
JL ts' g' a'.
Proof.
intros [d lv co pb pbs x o os obs] [d' lv' co' pb' pbs' x' o' os' obs'] l l' g g' a a' w'. cbn [t_levels t_depth t_objs t_objbs].
intros Hl -> -> Lw Hz Hz' (W & E & L) H.
destruct (jw_upd_add d lv l l' co pb pbs x o os obs co' pb' pbs' x' o' os' obs' W w' Hl E Lw Hz Hz') as (w0 & b & Lw0 & Eb & E').
exists (W - w0 - b + w'). split; [exact E'|].
rewrite (cur_st_updJ _ _ l), (cur_ss_updJ _ _ l) by exact Hl. rewrite (cur_st_ofJ _ _ l), (cur_ss_ofJ _ _ l) in L by exact Hl.
specialize (H w0 b Lw0 Eb). lia.
Qed.

Lemma JL_pop : forall ts dp l lp g a,
t_depth ts = S dp -> nth_error (t_levels ts) (S dp) = Some l -> nth_error (t_levels ts) dp = Some lp ->
zin (tl_st l) [ST_array_add; ST_ovadd] = false -> zin (tl_st lp) [ST_array_add; ST_ovadd] = true ->
JL ts g a ->
jpi (tl_st lp) (tl_ss lp) <= jtext (tl_st l) g + jpi (tl_st l) (tl_ss l) ->
JL (TST dp (lupd (t_levels ts) (S dp) (TL ST_eatws ST_start 0 None [] 0 [])) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (tl_cur l) (tl_cs l) (tl_cbs l)) g a.
Proof.
intros [d lv co pb pbs x o os obs] dp l lp g a. cbn [t_levels t_depth t_co t_pb t_pbs t_x]. intros -> Hl Hlp Hz Hzp (W & E & L) H.
destruct (jw_pop dp lv l lp co pb pbs x o os obs W Hl Hlp Hz Hzp E) as (W' & E' & LW). exists W'. split; [exact E'|].
rewrite (cur_st_ofJ _ _ l), (cur_ss_ofJ _ _ l) in L by exact Hl.
assert (Ec : cur_st (TST dp (lupd lv (S dp) (TL ST_eatws ST_start 0 None [] 0 [])) co pb pbs x (tl_cur l) (tl_cs l) (tl_cbs l)) = tl_st lp)
by (unfold cur_st; cbn [t_levels t_depth]; rewrite nth_error_lupd_neq by lia; rewrite Hlp; reflexivity).
assert (Es : cur_ss (TST dp (lupd lv (S dp) (TL ST_eatws ST_start 0 None [] 0 [])) co pb pbs x (tl_cur l) (tl_cs l) (tl_cbs l)) = tl_ss lp)
by (unfold cur_ss; cbn [t_levels t_depth]; rewrite nth_error_lupd_neq by lia; rewrite Hlp; reflexivity).
rewrite Ec, Es. assert (Elive : jtext (tl_st lp) g = 0).
{ unfold jtext, jlive. cbn [zin existsb] in Hzp |- *. apply orb_prop in Hzp. destruct Hzp as [Hq | Hq]; [| apply orb_prop in Hq; destruct Hq as [Hq | Hq]; [| discriminate Hq]];
apply Z.eqb_eq in Hq; rewrite Hq; reflexivity. }
rewrite Elive. lia.
Qed.

Lemma JL_push : forall ts l lp g g' a a',
nth_error (t_levels ts) (t_depth ts) = Some l -> (S (t_depth ts) < length (t_levels ts))%nat ->
tl_cs lp = tl_cs l -> tl_cbs lp = tl_cbs l -> tl_nbs lp = tl_nbs l ->
zin (tl_st l) [ST_array_add; ST_ovadd] = false ->
JL ts g a ->
26 <= jtext (tl_st l) g + jpi (tl_st l) (tl_ss l) + JC1 * (a' - a) ->
JL (ts_push ts lp) g' a'.
Proof.
intros [d lv co pb pbs x o os obs] l lp g g' a a'. unfold ts_push. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs]. intros Hl Hlen C1 C2 C3 Hz (W & E & L) H.
pose proof (jw_push d lv l lp co pb pbs x o os obs W Hl Hlen E (lw_restate l lp C1 C2 C3) Hz) as E'.
exists W. split; [exact E'|].
rewrite (cur_st_ofJ _ _ l), (cur_ss_ofJ _ _ l) in L by exact Hl.
assert (Ec : cur_st (TST (S d) (lupd (lupd lv d lp) (S d) (TL ST_eatws ST_start 0 None [] 0 [])) co pb pbs x o os obs) = ST_eatws)
by (unfold cur_st; cbn [t_levels t_depth]; rewrite nth_error_lupd_eq by (rewrite lupd_length; exact Hlen); reflexivity).
assert (Es : cur_ss (TST (S d) (lupd (lupd lv d lp) (S d) (TL ST_eatws ST_start 0 None [] 0 [])) co pb pbs x o os obs) = ST_start)
by (unfold cur_ss; cbn [t_levels t_depth]; rewrite nth_error_lupd_eq by (rewrite lupd_length; exact Hlen); reflexivity).
rewrite Ec, Es. change (jtext ST_eatws g') with 0. change (jpi ST_eatws ST_start) with 26. lia.
Qed.

End RC__1.
End Mq1.
From Stdlib Require Permutation.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPZI Qiiq Q4v2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QRUw.Mq2 QmZZ. Import QPZI.Mq4. Import QkMG. Import QG8z Qdyh.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq4 Qiiq.Mq0 QsKa.Mq6 Q4v2.Mq0 QlKV.Mq5 QlKV.Mq7 Q1Ey Ql4f.Mq1 QsKa.Mq8 QrQv.Mq2 QEUF QdGy.Mq6.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section WithIface.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.

Definition lvl_nameless (m : word -> option byte) (l : tlevel) : Prop :=
0 <= tl_st l <= 26 /\ 0 <= tl_ss l <= 26 /\ jopt asegs A4F (tl_cs l) m (tl_cbs l) (tl_cur l) /\ tl_nbs l = [].

Definition PE_NWIN (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (XS : list blk)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) : Prop :=
PE_CORE_A pf pa q m ts cb nb pj sv /\
PE_BASE_A HIx GA pf pa LB0 LM FRS payload me lo m md A B (pe_blocksA pf q LB0 (tsF ts XS)) errv /\
(forall i li, nth_error (t_levels ts) i = Some li -> i <> t_depth ts -> lvl_cur asegs A4F m (t_depth ts) i li) /\
(exists l, nth_error (t_levels ts) (t_depth ts) = Some l /\ lvl_nameless m l) /\
t_objbs ts = [].

Lemma PE_NWIN_open : forall pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv l,
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> t_objbs ts = [] ->
PE_NWIN pf pa q LB0 LM FRS payload me lo m md A B (ts_lvl ts (TL (tl_st l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) [])) (tl_nbs l) cb nb pj sv errv.
Proof.
intros pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv l [CORE REST] Hl Eobj.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
apply PE_REST_A_base in REST as (BASE & LV & OBJ & BUD).
set (lw := TL (tl_st l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) []).
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
pose proof (LV _ _ Hl) as (R1 & R2 & JO & _).
split; [| split; [| split; [| split]]].
- unfold PE_CORE_A, ts_lvl; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOK|]. split; [exact PB|]. split; [exact Hpb|]. split; [| exact FR].
eapply tstack_lupd_srec; [exact TSK | exact Hl |]. reflexivity.
- destruct BASE as (HP & BASE'). split; [| exact BASE'].
eapply (heapA_perm A4L HIx); [exact HP | | apply Permutation_refl | apply Permutation_refl].
eapply Permutation_trans; [apply (pe_blocksA_cur_perm2 pf q LB0 ts l Hl)|]. apply Permutation_sym.
eapply Permutation_trans; [apply (pe_blocksA_lvl_obj_perm pf q LB0 ts l lw 0 None (tl_nbs l) Hl)|].
unfold lvl_blocks, lw; cbn [tl_cbs tl_nbs app]. rewrite Eobj, app_nil_r. cbn [app]. rewrite <- app_assoc. apply Permutation_refl.
- unfold ts_lvl; cbn [t_levels t_depth]. intros i li Hli Hne. rewrite nth_error_lupd_neq in Hli by congruence. exact (LV i li Hli).
- exists lw. split; [unfold ts_lvl; cbn [t_levels t_depth]; apply nth_error_lupd_eq; exact Hd|].
unfold lvl_nameless, lw; cbn [tl_st tl_ss tl_cs tl_cbs tl_cur tl_nbs]. split; [exact R1|]. split; [exact R2|]. split; [exact JO | reflexivity].
- exact Eobj.
Qed.

Lemma PE_NWIN_write : forall pf pa q LB0 LM FRS payload me lo m mc md A B ts XS cb nb pj sv errv W l l' cb' nb' pj',
PE_STATIC_A HIx pf pa lo ->
PE_NWIN pf pa q LB0 LM FRS payload me lo m md A B ts XS cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l ->
munch W m mc -> wmono asegs m mc -> mem_inv asegs mc -> Forall (pe_wtqA pf pa q) W ->
rw_cells asegs mc (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat (t_depth ts)) q (t_x ts)) ->
tstack asegs mc q (lupd (t_levels ts) (t_depth ts) l') ->
pe_frameA asegs mc pf pa cb' nb' pj' sv ->
0 <= tl_st l' <= 26 -> 0 <= tl_ss l' <= 26 -> tl_cur l' = tl_cur l -> tl_cs l' = tl_cs l -> tl_cbs l' = tl_cbs l -> tl_nbs l' = [] ->
PE_NWIN pf pa q LB0 LM FRS payload me lo mc md A B (ts_lvl ts l') XS cb' nb' pj' sv errv
/\ (forall b, PBOKat m ts b -> PBOKat mc (ts_lvl ts l') b)
/\ agree_on asegs XS m mc.
Proof.
intros pf pa q LB0 LM FRS payload me lo m mc md A B ts XS cb nb pj sv errv W l l' cb' nb' pj' STC (CORE & BASE & LVo & (l0 & Hl0 & NL) & Eobj) Hl MU WM MI HW TOKc TSKc FRc R1' R2' Ecur Ecs Ecbs Enbs.
rewrite Hl in Hl0. injection Hl0 as <-. destruct NL as (R1 & R2 & JO & Enbs0).
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
destruct (PE_BASE_A_private_write HIx GA GA_outside pf pa q LB0 LM FRS payload me lo m mc md A B (tsF ts XS) errv W STC BASE MU WM MI (pe_wtqA_private _ _ _ _ _ HW)) as [BASEc AG].
unfold tsF in AG; cbn [t_objbs t_levels] in AG.
assert (Eb : lvl_blocks l' = lvl_blocks l) by (unfold lvl_blocks; rewrite Ecbs, Enbs, Enbs0; reflexivity).
split; [| split].
2:{ intros b PBK. eapply PBOKat_same with (ts := ts); [reflexivity | reflexivity |].
eapply PBOKat_agree; [exact PBK | | apply incl_refl].
eapply (agree_wtqA HIx) with (ts := tsF ts XS); [exact STC | exact (proj1 BASE) | exact MU | exact WM | exact HW |].
intros a n Hin. assert (HinL : In (a, n) (pe_blocksA pf q LB0 (tsF ts XS) ++ LM)) by (unfold pe_blocksA, tstate_blocks, tsF; cbn [t_pbs]; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hin).
split; [exact HinL|].
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ (proj1 BASE)) as ND. unfold pe_blocksA in ND. rewrite <- app_assoc in ND. split.
+ intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks, tsF; cbn [t_pbs]; apply in_or_app; left; exact Hin | left; reflexivity].
+ intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks, tsF; cbn [t_pbs]; apply in_or_app; left; exact Hin | right; left; reflexivity]. }
2:{ eapply (agree_on_incl asegs); [exact AG | intros b Hb; apply in_or_app; left; exact Hb]. }
split; [| split; [| split; [| split]]].
- unfold PE_CORE_A, ts_lvl; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOKc|]. split; [| split; [exact Hpb | split; [exact TSKc | exact FRc]]].
eapply (pbuf_wtqA HIx) with (ts := tsF ts XS); [exact STC | exact (proj1 BASE) | exact PB | exact MU | exact WM | exact HW].
- rewrite (pe_blocksA_tsF_lvl pf q LB0 ts XS l l' Hl Eb). exact BASEc.
- unfold ts_lvl; cbn [t_levels t_depth]. intros i li Hli Hne. rewrite nth_error_lupd_neq in Hli by congruence.
eapply (lvl_cur_agree asegs A4F); [exact (LVo i li Hli Hne) | exact AG |].
intros b Hb. apply in_or_app; right. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map. eapply nth_error_In; exact Hli.
- exists l'. split; [unfold ts_lvl; cbn [t_levels t_depth]; apply nth_error_lupd_eq; exact Hd|].
split; [exact R1'|]. split; [exact R2'|]. split; [| exact Enbs].
rewrite Ecs, Ecbs, Ecur. eapply (jopt_agree asegs A4F); [exact JO | exact AG |].
intros b Hb. apply in_or_app; right. apply in_concat. exists (lvl_blocks l). split; [apply in_map; eapply nth_error_In; exact Hl | unfold lvl_blocks; apply in_or_app; left; exact Hb].
- exact Eobj.
Qed.

Lemma PE_NWIN_callG : forall pf pa q LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 ts XS XS2 cb nb pj sv errv errv2,
PE_STATIC_A HIx pf pa lo ->
PE_NWIN pf pa q LB0 LM FRS payload me lo m1 md A B ts XS cb nb pj sv errv ->
model_vm_only (cfg_model md) (cfg_model md2) ->
heap_pres A4H (pe_blocksA pf q LB0 ts ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m1 m2 ->
HEAPA A4L HIx A2 (pe_blocksA pf q LB0 (tsF ts XS2)) LM ((pa_F pa, 2) :: FRS) B2 m2 md2 ->
stk asegs m2 lo (pf_spf pf) -> rw_cells asegs m2 A_ERRNO [C4 errv2] ->
PE_NWIN pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts XS2 cb nb pj sv errv2.
Proof.
intros pf pa q LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 ts XS XS2 cb nb pj sv errv errv2 STC (CORE & BASE & LVo & (l & Hl & NL) & Eobj) VM HPR HP2 ST2 ERR2.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR).
set (RB := pe_blocksA pf q LB0 ts) in *.
assert (INtk : In (pf_tk pf, 72) RB) by (unfold RB, pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * pf_mxd pf) RB) by (unfold RB, pe_blocksA; apply in_or_app; right; right; left; reflexivity).
assert (LB0R : incl LB0 RB) by (unfold RB, pe_blocksA; intros b Hb; apply in_or_app; right; right; right; exact Hb).
assert (AG : agree_on asegs RB m1 m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPR | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
assert (FR2 : pe_frameA asegs m2 pf pa cb nb pj sv).
{ eapply pe_frameA_pres; [exact HPR | lia | exact GEO | | | exact FR].
- apply in_or_app; right. apply in_or_app; right. change 248 with (fr_size 2 - 8). apply fr_ivs_frame. left; reflexivity.
- apply in_or_app; right. apply in_or_app; right. rewrite <- fr_shadow_len_2. change (shA (pa_F pa)) with (shad A4L (pa_F pa)). apply fr_ivs_shadow. left; reflexivity. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR) in TOK; [| eapply client_range_block; [apply in_or_app; left; exact INtk | lia | unfold tok_cells_g; cbn; lia]]. cbn [hl_segs hla_base A4L A4H] in TOK.
apply (tstack_pres_g A4H _ _ _ _ _ _ HPR (in_or_app _ _ _ (or_introl INq))) in TSK; [| exact LEN32]. cbn [hl_segs hla_base A4L A4H] in TSK.
assert (INl : forall i li, nth_error (t_levels ts) i = Some li -> incl (lvl_blocks li) RB).
{ intros i li Hli b Hb. unfold RB, pe_blocksA, tstate_blocks. apply in_or_app; left. apply in_or_app; right. apply in_or_app; right. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map. eapply nth_error_In; exact Hli. }
split; [| split; [| split; [| split; [| exact Eobj]]]].
- split; [exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|]. split; [exact TOK|]. split; [| split; [exact Hpb | split; [exact TSK | exact FR2]]].
eapply pbuf_agree; [exact PB | exact AG |]. unfold RB, pe_blocksA, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb.
- eapply (PE_BASE_A_callG HIx GA GA_pres pf pa LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 _ _ errv errv2 RB); [exact STC | exact BASE | exact VM | exact HPR | exact LB0R | exact HP2 | exact ST2 | exact ERR2].
- intros i li Hli Hne. eapply (lvl_cur_agree asegs A4F); [exact (LVo i li Hli Hne) | exact AG | exact (INl i li Hli)].
- exists l. split; [exact Hl|]. destruct NL as (R1 & R2 & JO & Enbs). split; [exact R1|]. split; [exact R2|]. split; [| exact Enbs].
eapply (jopt_agree asegs A4F); [exact JO | exact AG |]. intros b Hb. apply (INl _ l Hl). unfold lvl_blocks. apply in_or_app; left. exact Hb.
Qed.

Lemma PE_NWIN_close : forall pf pa q LB0 LM FRS payload me lo m md A B ts XS cb nb pj sv errv l c hn,
PE_NWIN pf pa q LB0 LM FRS payload me lo m md A B ts XS cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l ->
lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) -> cls_ok c (tl_cs l) ->
name_ok asegs m hn (TL (tl_st l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) XS) ->
zin (tl_st l) [ST_array_add; ST_ovadd] = false ->
PE_BUD pf pa (ts_lvl ts (TL (tl_st l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) XS)) B ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B (ts_lvl ts (TL (tl_st l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) XS)) cb nb pj sv errv.
Proof.
intros pf pa q LB0 LM FRS payload me lo m md A B ts XS cb nb pj sv errv l c hn (CORE & BASE & LVo & (l0 & Hl0 & NL) & Eobj) Hl Hm CLS NM Hz BUD.
rewrite Hl in Hl0. injection Hl0 as <-. destruct NL as (R1 & R2 & JO & Enbs).
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
set (l' := TL (tl_st l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) XS) in *.
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
split.
- unfold PE_CORE_A, ts_lvl; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOK|]. split; [exact PB|]. split; [exact Hpb|]. split; [| exact FR].
eapply tstack_lupd_srec; [exact TSK | exact Hl |]. reflexivity.
- apply PE_REST_A_of_base; [| | | exact BUD].
+ destruct BASE as (HP & BASE'). split; [| exact BASE'].
eapply (heapA_perm A4L HIx); [exact HP | | apply Permutation_refl | apply Permutation_refl].
eapply Permutation_trans; [apply (perm_blocks_tsF pf q LB0 ts XS Eobj)|]. apply Permutation_sym.
eapply Permutation_trans; [apply (pe_blocksA_lvl_perm pf q LB0 ts l l' Hl)|].
unfold lvl_blocks at 1, l'; cbn [tl_cbs tl_nbs].
eapply Permutation_trans; [| apply Permutation_app_head; apply Permutation_sym; apply (pe_blocksA_cur_perm pf q LB0 ts l Hl)].
unfold lvl_blocks. rewrite Enbs, app_nil_r. rewrite <- app_assoc. apply Permutation_app_swap_app.
+ unfold ts_lvl; cbn [t_levels t_depth]. intros i li Hli.
destruct (PeanoNat.Nat.eq_dec i (t_depth ts)) as [-> | Hne].
* rewrite nth_error_lupd_eq in Hli by exact Hd. injection Hli as <-. split; [exact R1|]. split; [exact R2|]. split; [exact JO|].
rewrite Nat.ltb_irrefl, Nat.eqb_refl. exists c, hn. split; [exact Hm|]. split; [exact CLS | exact NM].
* rewrite nth_error_lupd_neq in Hli by congruence. exact (LVo i li Hli Hne).
+ unfold cur_st, ts_lvl; cbn [t_levels t_depth t_objs t_objbs t_obj]. rewrite nth_error_lupd_eq by exact Hd. cbn [tl_st l']. rewrite Hz. exact Eobj.
Qed.
End WithIface.
End RC__1.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QIsM Qa8x Q1Y6 QW22 QYZ0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z Qdyh.Mq0 Qdyh.Mq3 Qdyh.Mq4 QIsM.Mq2 Qa8x.Mq2.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq4 Qiiq.Mq0 QsKa.Mq6 Q4v2.Mq0 QlKV.Mq5 Q1Ey Ql4f.Mq1 Q1Y6.Mq2 QsKa.Mq8 QrQv.Mq2 QEUF QW22.Mq3 QdGy.Mq2 QYZ0.Mq3.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QlKV.Mq2 QEUF.Mq0 QdGy.Mq3.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma lvl_mode_start3 : forall ss c hn, 0 <= ss <= 26 -> lvl_mode ST_start ss = Some (c, hn) -> c = CNone /\ hn = false /\ ss = ST_start.
Proof.
intros ss c hn R H. assert (CASES : exists k : nat, (k <= 26)%nat /\ ss = Z.of_nat k) by (exists (Z.to_nat ss); split; lia).
destruct CASES as (k & Hk & ->). clear R.
do 27 (destruct k as [|k]; [vm_compute in H; first [discriminate H | injection H as <- <-; split; [reflexivity | split; reflexivity]] |]); exfalso; lia.
Qed.

Section PeSStartQA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.

Ltac pe_openA STC INV :=
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR); pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk);
destruct INV as [CORE REST];
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR);
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).

Ltac reopen_inv INVx TSx ts0 PF q LB0 tk mxd depth l Hl bse Hbse mX :=
pose proof INVx as [CORE2 REST2];
destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK & FR);
pose proof REST2 as (HP & _); clear REST2;
try unfold TSx in TOK, TSK; try unfold ts_pbs, ts_lvl, ts_set_x in TOK, TSK; try unfold ts0 in TOK, TSK;
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK, TSK;
unfold tok_cells_g in TOK; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK;
unfold pe_frameA in FR; destruct FR as (SLOTS & _ & _ & _ & _); unfold pe_slotsA in SLOTS; cbn zeta in SLOTS;
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS;
assert (INtk : In (tk, 72) (pe_blocksA PF q LB0 TSx)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity);
assert (INq : In (q, 32 * mxd) (pe_blocksA PF q LB0 TSx)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity);
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI;
pose proof (wmono_refl asegs mX) as WM;
pose proof (TSK depth l Hl) as Ld; rewrite <- Hbse in Ld; unfold srec_cells in Ld;
clear TSK.

Lemma start_quote_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 t1 t2 a1 a3 a4 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_start ->

(forall m' a1' a2' a3' a4',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B
(ts_set_x (ts_lvl ts (TL ST_string (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts) (TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) cb)) cb nb pj sv errv ->
PBOKat m' (ts_set_x (ts_lvl ts (TL ST_string (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts) (TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) cb)) 0 ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_ADV (t_co ts) gp t0 t1 t2 (Z_to_bv 64 (bv_unsigned cb)) a1' a2' a3' a4' a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F fc m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x974dc (t_co ts) gp t0 t1 t2
(Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a1
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3 a4 a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC INV Hl Hst Kadv. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 0 HP INq ltac:(lia) ltac:(lia)) as SHQ.
replace (q / 8 + 4 * Z.of_nat depth + 0 + A_SB) with (q / 8 + 4 * Z.of_nat depth + A_SB) in SHQ by lia.
assert (Hb8 : bse mod 8 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
assert (SHQ4 : ro_cells asegs m (bse / 8 + A_SB) [C1 (Z_to_bv 8 0)]).
{ replace (bse / 8) with (q / 8 + 4 * Z.of_nat depth) by (subst bse; rewrite div8_add_mul32 by lia; lia). exact SHQ. }
pose proof (munch_refl [(bse, bse + 32)] m) as MU.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT1c & SEPT1q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT1t & _).
cbn [hl_sb A4L] in SEPT1c, SEPT1q, SEPT1t. assert (EQx : tk / 8 + A_SB + 1 = tk / 8 + 2147450881) by (unfold A_SB; lia). rewrite EQx in SEPT1c, SEPT1q, SEPT1t. clear EQx.
unfold APE_BREAK, APE_ADV, APE_REDO, APE_OUT, APE_ERRMEM, APE_ERRST, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_T1_L : csep (tk / 8 + 2147450881) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPT1q HbseR; lia).
clear Hdtq SEPT1q SEPT1t SEPT1c.
destruct (lvl_mode_start3 _ _ _ SS26 ltac:(rewrite <- Hst; exact Hmode)) as (Ec0 & Ehn0 & Ess). subst c0 hn0.
stash Himg_t. stash Himg_q. stash Kadv. clear PB REST TSK LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ4.
reenterA asegs A4L HIx asegs_wx HP.
replace (q + 32 * Z.of_nat depth) with bse by lia.
asan_rechkA.
clear SHQ.
step.
stepz.
step.
asan_chkA.
step. step.
set (l1 := TL ST_string (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
pose proof MUc as MUc'; pose proof Lc as Lc'; rewrite Hbse in MUc', Lc';
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv l ST_string (tl_ss l) CNone false CNone STC INV0 Hl MUc' WMc MIc TOKc Lc' Hmode
ltac:(rewrite Ess; vm_compute; reflexivity) ltac:(unfold ST_string; lia) SS26 (or_introl eq_refl)
ltac:(rewrite Hst; vm_compute; reflexivity)) as [INV1 _]; clear MUc' Lc'
end end.
set (ts1 := ts_lvl ts0 l1) in *.
eapply (pe_pbreset HIx GA GA_pres (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md A B ts1 cb nb pj sv errv);
[exact STC | exact INV1 | rewrite unsigned_lit by lia; reflexivity |].
intros mr2 a1' a2' a3' a4' INV2 PBK2 PBC2.
cbn [pf_spf] in *. unfold A_TP in *.
repeat match goal with H : rw_cells asegs _ _ _ |- _ => clear H | H : ro_cells asegs _ _ _ |- _ => clear H | H : munch _ _ _ |- _ => clear H | H : wmono asegs _ _ |- _ => clear H | H : mem_inv asegs _ |- _ => clear H end.
clear Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk INtk INq INV0 INV1 HP cs_tk_L cs_L_tk cs_T1_L.
assert (Hl1 : nth_error (t_levels ts1) (t_depth ts1) = Some l1) by (unfold ts1, ts_lvl, ts0; cbn [t_levels t_depth]; apply nth_error_lupd_eq; apply nth_error_Some; rewrite Hl; discriminate).
pose proof INV2 as ((_ & _ & _ & _ & _ & _ & _ & _ & FRq) & _). unfold pe_frameA in FRq. destruct FRq as (_ & _ & _ & FF & _). unfold ff_cellsA in FF.
cbn [pa_F] in FF.
reopen_inv INV2 ts1 ts0 (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 tk mxd depth l1 Hl1 bse Hbse mr2.
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 6 HP INtk ltac:(lia)) as SHT6.
replace (tk / 8 + 6 + A_SB) with (tk / 8 + 2147450886) in SHT6 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 6 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT6c & SEPT6q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 6 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT6t & _).
cbn [hl_sb A4L] in SEPT6c, SEPT6q, SEPT6t. assert (EQx : tk / 8 + A_SB + 6 = tk / 8 + 2147450886) by (unfold A_SB; lia). rewrite EQx in SEPT6c, SEPT6q, SEPT6t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT4c & SEPT4q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4c, SEPT4q, SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4c, SEPT4q, SEPT4t. clear EQx.
pose proof (munch_refl [(tk, tk + 72)] mr2) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_T4_T : csep (tk / 8 + 2147450884) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPT4t; lia).
clear SEPT6q SEPT6t SEPT6c SEPT4q SEPT4t SEPT4c.
assert (LE1 : le1 (zxb cb) = [cb]).
{ unfold le1, zxb. cbn [Z_to_le_bytes pf_mxd]. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
pose proof (bv_unsigned_in_range 8 cb) as CBR8; unfold bv_modulus in CBR8; cbn in CBR8.
change (bv_modulus 8) with 256%Z. change (bv_modulus 64) with 18446744073709551616%Z. Z.div_mod_to_equations. nia. }
stash Himg_t2. clear Ld.
lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
step.
asan_chkM 3.
clear SHT6 FF.
step.
rewrite LE1. mem_after_store.
do 4 step.
asan_rechkA.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ mr2 mc, WMc : wmono asegs mr2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
destruct (PE_INV_A_tokw1 HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mr2 mc md A B ts1
cb nb pj sv errv co (TS isd stpos (Z_to_bv 64 co) err ucs high cb) STC INV2 MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as [INV3 PBT3];
unstash Kadv; eapply (Kadv mc); [exact INV3 | exact (PBT3 _ (PBOKat_of_pbufc_nil _ _ PBC2))]
end end.
Qed.

Lemma start_squote_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 t1 t2 a1 a3 a4 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> pf_fl pf = 0 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_start ->

(forall m' a1' a2' a3' a4',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B
(ts_set_x (ts_lvl ts (TL ST_string (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts) (TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) cb)) cb nb pj sv errv ->
PBOKat m' (ts_set_x (ts_lvl ts (TL ST_string (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts) (TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) cb)) 0 ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_ADV (t_co ts) gp t0 t1 t2 (Z_to_bv 64 (bv_unsigned cb)) a1' a2' a3' a4' a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F fc m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x974c4 (t_co ts) gp t0 t1 t2
(Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a1
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3 a4 a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC FL0 INV Hl Hst Kadv. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *. subst fl.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd 0) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd 0) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 0 HP INq ltac:(lia) ltac:(lia)) as SHQ.
replace (q / 8 + 4 * Z.of_nat depth + 0 + A_SB) with (q / 8 + 4 * Z.of_nat depth + A_SB) in SHQ by lia.
assert (Hb8 : bse mod 8 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
assert (SHQ4 : ro_cells asegs m (bse / 8 + A_SB) [C1 (Z_to_bv 8 0)]).
{ replace (bse / 8) with (q / 8 + 4 * Z.of_nat depth) by (subst bse; rewrite div8_add_mul32 by lia; lia). exact SHQ. }
pose proof (munch_refl [(bse, bse + 32)] m) as MU.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
unfold APE_BREAK, APE_REDO, APE_OUT, APE_ERRMEM, APE_ERRST, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
pose proof (tok_flags_byteA mxd 0 m tk pb (Z.of_nat depth) q (TS isd stpos (Z_to_bv 64 co) err ucs high quote) TOK) as RDF.
stash Himg_t. stash Himg_q. clear PB REST TSK LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin Ld MU.
reenterA asegs A4L HIx asegs_wx HP.
asan_rechkA.
step.
rewrite ?zxb_zero.
step.
step.
if_true.
evt_done5.
eapply (start_quote_A (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 l cb nb pj sv errv T); [exact STC | exact INV0 | exact Hl | exact Hst | exact Kadv].
Qed.
End PeSStartQA.
End RC__1.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QRUw.Mq2 QmZZ. Import QPZI.Mq4. Import QkMG. Import QG8z Qdyh.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq4 Qiiq.Mq0 QsKa.Mq6 Q4v2.Mq0 QlKV.Mq5 QlKV.Mq1 QlKV.Mq7 Q1Ey Ql4f.Mq1 QsKa.Mq8 QrQv.Mq2 QEUF QnDr.Mq2 QdGy.Mq6.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSWinCallA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.

Lemma pe_get_w :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (p : Z) (s : option jshape) (BS : list blk)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (Q : machine_state -> Prop)
(ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts p s BS 1 cb nb pj sv errv ->
(forall m2 (a1' a2' a3' : word),
PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m2 md A B ts p s BS 2 cb nb pj sv errv ->
(forall b, PBOKat m ts b -> PBOKat m2 ts b) ->
evt asegs Q (MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1' a2' a3' a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m2 (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9a734) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC WIN K.
pose proof WIN as (CORE & BASE & LVo & CUR & Eobj & PP). pose proof BASE as (HP & ST & ERR & _).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof alloc_ceiling_range as ACR.
assert (PBT : forall m2, agree_on asegs (pe_blocksA pf q LB0 ts) m m2 -> forall b, PBOKat m ts b -> PBOKat m2 ts b).
{ intros m2 AG b PBK. eapply PBOKat_agree; [exact PBK | exact AG |]. unfold pe_blocksA, tstate_blocks. intros x Hx. apply in_or_app; left. apply in_or_app; left. exact Hx. }
destruct s as [s'|].
- destruct PP as (Hp & _ & J).
set (LBall := pe_blocksA pf q LB0 (tsF ts BS)) in *.
pose proof (perm_blocks_tsF pf q LB0 ts BS Eobj) as PERM. fold LBall in PERM.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND.
assert (NDp : List.NoDup (map blk_addr ((BS ++ pe_blocksA pf q LB0 ts) ++ LM))).
{ eapply Permutation_NoDup; [| exact ND]. apply Permutation_map. apply Permutation_app_tail. exact PERM. }
assert (NDbs : List.NoDup (map blk_addr BS)).
{ rewrite <- app_assoc, map_app in NDp. exact (NoDup_app_remove_r _ _ NDp). }
destruct (jval_hdr asegs A4F s' m BS p 1 J NDbs) as (n & tojs & pb' & udel & ud & rest & INc & SZ & N48 & HDR & CLOSE).
assert (INall : forall a k, In (a, k) BS -> In (a, k) LBall).
{ intros a k Hin. eapply Permutation_in; [apply Permutation_sym; exact PERM | apply in_or_app; left; exact Hin]. }
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p n HP (in_or_app _ LM _ (or_introl (INall p n INc)))) as (Hn0 & Hpal & Hp0 & Hphi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ p n HP (in_or_app _ LM _ (or_introl (INall p n INc)))) as Himg_p. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Himg_p.
destruct (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as (GOT & CELL).
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ p n HP (INall p n INc)) as SHB. unfold shad in SHB. cbn [hl_sb A4L] in SHB.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ p n ((n + 7) / 8 - 1) p n HP (INall p n INc) ltac:(clear - N48; Z.div_mod_to_equations; lia) (in_or_app _ LM _ (or_introl (INall p n INc)))) as (SEPc & _ & _).
cbn [hl_sb A4L] in SEPc.
destruct (proj1 (rw_cells_app asegs m p _ _) HDR) as [HDRh HDRr]. cbn [cells_size csize jhdr_cells Nat.add] in HDRr.
assert (SZr : 40 + Z.of_nat (cells_size rest) = n) by (rewrite cells_size_app, Nat2Z.inj_add in SZ; cbn [cells_size csize jhdr_cells Nat.add] in SZ; lia).
assert (Hsbc : 65536 <= hl_sb_cell A4L /\ hl_sb_cell A4L + 8 <= 6574080) by (vm_compute; split; intros X; discriminate X).
assert (SPF : lo <= pf_spf pf - 16 /\ 0 <= pf_spf pf < 2^62) by lia.
eapply evt_cut.
{ eapply (jo_get_A) with (lo := lo) (n := n) (sbcell := hl_sb_cell A4L);
[ exact HDRh | exact Hp0 | lia | exact Hpal | lia | lia | exact MI | rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; lia | exact LO | lia
| exact GOT | exact CELL | lia | lia | lia | | lia | exact SHB ].
clear - SEPc. lia. }
intros ms1 (m2 & (w & x & y & ->) & MU & WM & MI2 & HDR2 & ST2).
rewrite (unsigned_lit (pf_spf pf)) in MU, ST2 by lia.
assert (PP2 : put_pre A4H A4F (Some s') m2 BS p 2).
{ split; [exact Hp|]. split; [lia|]. apply (CLOSE m2 2).
- apply (proj2 (rw_cells_app asegs m2 p _ _)). split; [exact HDR2|]. cbn [cells_size csize jhdr_cells Nat.add].
eapply rw_cells_transport; [exact HDRr | exact MU | exact WM |]. cbn [disjoint_from fst snd]. lia.
- eapply (agree_others_gen asegs); [exact MU | exact WM |]. intros a k Hin Hne.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a k p n HP (in_or_app _ LM _ (or_introl (INall a k Hin))) (in_or_app _ LM _ (or_introl (INall p n INc))) Hne) as DJ.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP (in_or_app _ LM _ (or_introl (INall a k Hin)))) as (Hk0 & _ & _ & Hahi & _).
cbn [disjoint_from fst snd]. lia. }
destruct (PE_WIN_munchG HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md A B ts p (Some s') BS 1 2 cb nb pj sv errv _ STC WIN MU WM MI2
ltac:(apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_cons; [right; exists p, n; split; [exact INc | cbn [fst snd]; lia] | apply Forall_nil]]) ST2 PP2) as [WIN2 AG].
exact (K m2 w x y WIN2 (PBT m2 AG)).
- destruct PP as (Ep & EBS). subst p BS.
assert (SPF : lo <= pf_spf pf - 16 /\ 0 <= pf_spf pf < 2^62) by lia.
eapply evt_cut.
{ eapply (jo_get_null_A) with (lo := lo); [exact MI | rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; lia]. }
intros ms1 (m2 & (w & x & y & ->) & MU & WM & MI2 & ST2).
rewrite (unsigned_lit (pf_spf pf)) in MU, ST2 by lia.
destruct (PE_WIN_munchG HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md A B ts 0 None [] 1 2 cb nb pj sv errv _ STC WIN MU WM MI2
ltac:(apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]) ST2 ltac:(split; reflexivity)) as [WIN2 AG].
exact (K m2 w x y WIN2 (PBT m2 AG)).
Qed.

Hypothesis PUT : put_stmt_A HIx.

Lemma pe_put_w :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (p : Z) (s : option jshape) (BS : list blk)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (tsO : tstate) (nB : nat)
(ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts p s BS 2 cb nb pj sv errv ->
PBOKat m ts kP -> BOK pf pa tsO B nB ->
bv_unsigned ra mod 2 = 0 ->
(forall m2 md2 A2 B2 (r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) F2 fc2,
PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts p s BS 1 cb nb pj sv errv ->
PBOKat m2 ts kP -> BOK pf pa tsO B2 nB ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 s0 s1 r w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F2 (ret_pc ra) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9a78c) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC WIN PBK BK RA K.
pose proof WIN as (CORE & BASE & LVo & CUR & Eobj & PP). pose proof BASE as (HP1 & ST1 & ERR1 & _).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
assert (SPF : lo <= pf_spf pf - put_stk_A /\ pf_spf pf mod 16 = 0 /\ pf_spf pf <= hiA_top A4L HIx /\ 0 <= pf_spf pf < 2^62).
{ unfold put_stk_A. clear - LOS HT Gle Gspf SP0. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; lia. }
destruct SPF as (SPF1 & SPF2 & SPF3 & SPF4).
set (RB := pe_blocksA pf q LB0 ts) in *.
pose proof (perm_blocks_tsF pf q LB0 ts BS Eobj) as PERM. fold RB in PERM.
assert (HPp : HEAPA A4L HIx A (BS ++ RB) LM ((pa_F pa, 2) :: FRS) B m md) by (eapply (heapA_perm A4L HIx); [exact HP1 | exact PERM | apply Permutation_refl | apply Permutation_refl]).
assert (COST : put_costA s 2 BS = 0) by (destruct s; reflexivity).
eapply PUT with (LB := RB) (BS := BS) (s := s) (p := p) (rc := 2) (lo := lo) (errv := errv);
[ exact HPp | exact PP | reflexivity | rewrite unsigned_lit by lia; exact ST1 | exact LO | rewrite unsigned_lit by lia; exact SPF1
| rewrite unsigned_lit by lia; exact SPF2 | rewrite unsigned_lit by lia; exact SPF3 | exact ERR1 | reflexivity | exact RA
| rewrite COST; exact (proj1 (heapA_budget A4L HIx _ _ _ _ _ _ _ HP1)) | ].
intros ms2 md2 A2 (m2 & r & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & HB2 & HD2 & OUT2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
rewrite COST in HB2.
cbn [hl_segs hl_tp hla_base A4L A4H] in *. rewrite ?(unsigned_lit (pf_spf pf)) in ST2 by lia. rewrite ?(unsigned_lit (pf_spf pf)) in HPR2 by lia.
assert (HPP2 : HEAPA A4L HIx A2 (pe_blocksA pf q LB0 (tsF ts BS)) LM ((pa_F pa, 2) :: FRS) B2 m2 md2 /\ put_pre A4H A4F s m2 BS p 1).
{ destruct OUT2 as [([Es | Erc] & H) | (s' & Es & _ & J' & H)]; [| exfalso; lia |].
- subst s. destruct PP as (Ep & EBS). subst BS. split; [| split; [exact Ep | reflexivity]].
eapply (heapA_perm A4L HIx); [exact H | apply Permutation_sym; exact PERM | apply Permutation_refl | apply Permutation_refl].
- subst s. destruct PP as (Hp & _ & _). split; [| split; [exact Hp | split; [lia | replace 1 with (2 - 1) by reflexivity; exact J']]].
eapply (heapA_perm A4L HIx); [exact H | apply Permutation_sym; exact PERM | apply Permutation_refl | apply Permutation_refl]. }
destruct HPP2 as [HP2 PP2].
pose proof (PE_WIN_callG HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B B2 ts p s BS 2 1 cb nb pj sv errv errv STC WIN VM2 HPR2 HP2 ST2 ERR2 PP2) as WIN2.
assert (AG : agree_on asegs RB m m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPR2 | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
eapply (K m2 md2 A2 B2 r); [exact WIN2 | | eapply BOK_mono; [| | exact BK]; lia | exact FS2 | exact FRM2].
eapply PBOKat_agree; [exact PBK | exact AG |]. unfold RB, pe_blocksA, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb.
Qed.

Lemma pe_free_null_w :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (p : Z) (s : option jshape) (BS : list blk) (rc : Z)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (tsO : tstate) (nB : nat)
(ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts p s BS rc cb nb pj sv errv ->
PBOKat m ts kP -> BOK pf pa tsO B (S (Z.to_nat 512 + nB)) ->
bv_unsigned ra mod 2 = 0 ->
(forall m2 md2 A2 B2 (r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word),
PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts p s BS rc cb nb pj sv errv ->
PBOKat m2 ts kP -> BOK pf pa tsO B2 nB ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 s0 s1 r w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F (ret_pc ra) fc None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x632c4) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC BSL WIN PBK BK RA K.
pose proof WIN as (CORE & BASE & LVo & CUR & Eobj & PP). pose proof BASE as (HP1 & ST1 & ERR1 & _).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
assert (SPF : lo <= pf_spf pf - 4096 /\ pf_spf pf mod 16 = 0 /\ pf_spf pf < hiA_top A4L HIx + 64 /\ 0 <= pf_spf pf < 2^62).
{ clear - LOS HT Gle Gspf SP0. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; lia. }
destruct SPF as (SPF1 & SPF2 & SPF3 & SPF4).
assert (COST : 512 <= bB B).
{ pose proof (BOK_ledger_nonneg _ _ _ _ _ BK) as L0. pose proof BK as (H1 & _ & H3 & _). unfold bneed in H1.
pose proof (K_ev_pos pf). pose proof (Zle_0_nat (length (tstate_blocks tsO))).
replace (K_ev pf * Z.of_nat (S (Z.to_nat 512 + nB))) with (K_ev pf * Z.of_nat nB + 513) in H1 by (unfold K_ev; lia).
pose proof (Z.mul_nonneg_nonneg (K_ev pf) (Z.of_nat nB) ltac:(lia) ltac:(lia)). unfold K_free, K_exit in *. lia. }
set (LBall := pe_blocksA pf q LB0 (tsF ts BS)) in *. set (RB := pe_blocksA pf q LB0 ts) in *.
eapply (hiA_free A4L HIx) with (p := 0) (u := UWpaid) (lo := lo) (errv := errv);
[ exact HP1 | left; reflexivity | rewrite unsigned_lit by lia; exact ST1 | exact LO | rewrite unsigned_lit by lia; cbn [hl_stack_A A4L]; exact SPF1
| rewrite unsigned_lit by lia; exact SPF2 | rewrite unsigned_lit by lia; exact SPF3 | exact ERR1 | reflexivity | reflexivity
| split; cbn; exact I  | exact COST | cbn; pose proof (proj2 (heapA_budget A4L HIx _ _ _ _ _ _ _ HP1)); lia | ].
intros ms2 m2 md2 A2 r RS2 VM2 ST2 HPR2 ERR2 HP2.
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & ->).
cbn [hl_segs hl_tp hla_base A4L A4H Z.eqb] in *. rewrite ?(unsigned_lit (pf_spf pf)) in ST2 by lia. rewrite ?(unsigned_lit (pf_spf pf)) in HPR2 by lia.
assert (Enot : forall n, ~ In (0, n) LBall).
{ intros n Hin. pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ 0 n HP1 (in_or_app _ LM _ (or_introl Hin))) as (_ & _ & H0 & _). lia. }
rewrite (lb_remove_notinS 0 _ Enot) in HPR2, HP2.
set (B2 := charge B 512 0) in *.
assert (AGall : agree_on asegs LBall m m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPR2 | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
assert (HPRc : heap_pres A4H (RB ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m m2).
{ eapply (heap_pres_weaken A4H); [exact HPR2 | lia |]. intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; apply (incl_blocks_tsF pf q LB0 ts BS Eobj); exact Hb | apply in_or_app; right; exact Hb]. }
assert (PP2 : put_pre A4H A4F s m2 BS p rc).
{ unfold put_pre in *. destruct s as [s'|]; [| exact PP]. destruct PP as (Hp & Hrc & J). split; [exact Hp|]. split; [exact Hrc|].
eapply jval_agree; [exact J | exact AGall |]. intros b Hb. unfold LBall, pe_blocksA, tstate_blocks, tsF; cbn [t_pbs t_objbs t_levels].
apply in_or_app; left. apply in_or_app; right. apply in_or_app; left. exact Hb. }
pose proof (PE_WIN_callG HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B B2 ts p s BS rc rc cb nb pj sv errv errv STC WIN VM2 HPRc HP2 ST2 ERR2 PP2) as WIN2.
eapply (K m2 md2 A2 B2 r); [exact WIN2 | | eapply (BOK_pay pf pa tsO B B2 nB 512); [exact BK | pose proof (K_ev_pos pf); lia | cbn; lia | cbn; lia]].
eapply PBOKat_agree; [exact PBK | exact AGall |]. unfold LBall, pe_blocksA, tstate_blocks, tsF; cbn [t_pbs t_objbs t_levels]. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb.
Qed.

Hypothesis NEWARR : jo_new_array_A3 HIx.

Lemma pe_new_array_w :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP v2 ra2 : Z)
(ra gp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts 0 None [] 1 cb nb pj sv errv ->
PBOKat m ts kP -> new_array_costA <= bB B ->
pe_s0 sv = Z_to_bv 64 v2 -> pe_ra sv = Z_to_bv 64 ra2 ->
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64 ->
uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9eb50) (UWfp ra2 v2) ->
bv_unsigned ra mod 2 = 0 ->
(forall m2 md2 A2 B2 errv2 (r : Z) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) F2 fc2,
((r = 0 /\ PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts 0 None [] 1 cb nb pj sv errv2) \/
(r <> 0 /\ exists BS, arr_capA BS = 32 /\ length BS = 3%nat /\ 0 < r < 2^62 /\ PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts r (Some (Sarr [])) BS 1 cb nb pj sv errv2)) ->
PBOKat m2 ts kP -> bB B - new_array_costA <= bB B2 -> bD B <= bD B2 ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 r) w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F2 (ret_pc ra) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9eb2c) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC WIN PBK COST S0V RAV HV UWK RA K.
pose proof WIN as (CORE & BASE & LVo & CUR & Eobj & PP). pose proof BASE as (HP1 & ST1 & ERR1 & _).
pose proof CORE as (_ & _ & _ & _ & _ & _ & _ & _ & FR1).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
assert (SPF : lo <= pf_spf pf - (32 + 32 + 4096) /\ pf_spf pf mod 16 = 0 /\ pf_spf pf <= hiA_top A4L HIx /\ 0 <= pf_spf pf < 2^62 /\ 0 <= pa_sp0 pa < 2^63).
{ clear - LOS HT Gle Gspf SP0. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; lia. }
destruct SPF as (SPF1 & SPF2 & SPF3 & SPF4 & SPF5).
set (RB := pe_blocksA pf q LB0 ts) in *.
assert (Eq0 : pe_blocksA pf q LB0 (tsF ts []) = RB) by (unfold RB, pe_blocksA, tstate_blocks, tsF; cbn [t_pbs t_objbs t_levels]; rewrite Eobj; reflexivity).
rewrite Eq0 in HP1.
pose proof (pe_uw_at HIx pf pa lo m cb nb pj sv v2 ra2 STC FR1 S0V RAV (proj1 HV) (proj2 HV)) as UWA.
unfold jo_new_array_A3, jo_new_container_A_stmt in NEWARR.
eapply NEWARR with (LB := RB) (lo := lo) (errv := errv) (u := UWfp ra2 v2);
[ split; [exact HP1|]; split; [rewrite unsigned_lit by lia; exact ST1|]; split; [exact LO|]; split; [rewrite unsigned_lit by lia; exact SPF1|];
split; [rewrite unsigned_lit by lia; exact SPF2|]; split; [rewrite unsigned_lit by lia; exact SPF3|]; split; [exact ERR1|]; split; [reflexivity | exact RA]
| exact I | rewrite !unsigned_lit by lia; exact UWA | exact UWK | exact COST | cbn [uw_cost]; pose proof (proj2 (heapA_budget A4L HIx _ _ _ _ _ _ _ HP1)); lia | ].
intros ms2 md2 m2 r A2 B2 (RS2 & VM2 & ST2 & HPR2 & (errv2 & ERR2)) HB2 HD2 OUT2.
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp hla_base A4L A4H uw_cost] in *. rewrite ?(unsigned_lit (pf_spf pf)) in ST2 by lia. rewrite ?(unsigned_lit (pf_spf pf)) in HPR2 by lia.
assert (HPRc : heap_pres A4H (RB ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m m2) by exact HPR2.
assert (AG : agree_on asegs RB m m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPRc | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
eapply (K m2 md2 A2 B2 errv2 r); [| | lia | lia | exact FS2 | exact FRM2].
- destruct OUT2 as [(-> & HP2) | (Hr & BS & J2 & (CAP & LEN3) & HP2)].
+ left. split; [reflexivity|].
eapply (PE_WIN_callG2 HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B B2 ts 0 None [] 1 0 None [] 1 cb nb pj sv errv errv2);
[exact STC | exact WIN | exact VM2 | exact HPRc | rewrite Eq0; exact HP2 | exact ST2 | exact ERR2 | split; reflexivity].
+ right. split; [exact Hr|]. exists BS. split; [exact CAP|]. split; [exact LEN3|].
split.
{ destruct (arr_capA_jval _ _ _ _ _ J2) as (a0' & arr0 & rest0 & EBS & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r 48 HP2 ltac:(apply in_or_app; left; apply in_or_app; left; rewrite EBS; left; reflexivity)) as (_ & _ & Hr0 & Hrhi & _).
pose proof alloc_ceiling_range. lia. }
eapply (PE_WIN_callG2 HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B B2 ts 0 None [] 1 r (Some (Sarr [])) BS 1 cb nb pj sv errv errv2);
[exact STC | exact WIN | exact VM2 | exact HPRc | | exact ST2 | exact ERR2 | split; [exact Hr | split; [lia | exact J2]]].
eapply (heapA_perm A4L HIx); [exact HP2 | apply Permutation_sym; apply (perm_blocks_tsF pf q LB0 ts BS Eobj) | apply Permutation_refl | apply Permutation_refl].
- eapply PBOKat_agree; [exact PBK | exact AG |]. unfold RB, pe_blocksA, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb.
Qed.
End PeSWinCallA.
End RC__1.
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qmgs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QRUw.Mq2 QmZZ. Import QPZI.Mq4. Import QkMG. Import QG8z Qdyh.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq4 Qiiq.Mq0 QsKa.Mq6 Q4v2.Mq0 QlKV.Mq5 QlKV.Mq1 QlKV.Mq7 QsKa.Mq5 Q1Ey Ql4f.Mq1 QsKa.Mq8 QrQv.Mq2 QEUF Qmgs QdGy.Mq6.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSWinCallOA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis GA_lh : forall m, GA m -> lh_globA m.
Hypothesis NEWOBJ : jo_new_object_A3_stmt HIx.

Lemma pe_new_object_w :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP v2 ra2 : Z)
(ra gp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts 0 None [] 1 cb nb pj sv errv ->
PBOKat m ts kP -> newobj_costB <= bB B ->
pe_s0 sv = Z_to_bv 64 v2 -> pe_ra sv = Z_to_bv 64 ra2 ->
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64 ->
uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9bbfc) (UWfp ra2 v2) ->
bv_unsigned ra mod 2 = 0 ->
(forall m2 md2 A2 B2 errv2 (r : Z) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) F2 fc2,
((r = 0 /\ PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts 0 None [] 1 cb nb pj sv errv2) \/
(r <> 0 /\ exists BS, obj_capA BS = 16 /\ length BS = 3%nat /\ 0 < r < 2^62 /\ PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts r (Some (Sobj [])) BS 1 cb nb pj sv errv2)) ->
PBOKat m2 ts kP -> bB B - newobj_costB <= bB B2 -> bD B <= bD B2 ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 r) w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F2 (ret_pc ra) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9bbd4) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC WIN PBK COST S0V RAV HV UWK RA K.
pose proof WIN as (CORE & BASE & LVo & CUR & Eobj & PP). pose proof BASE as (HP1 & ST1 & ERR1 & _ & _ & _ & _ & _ & G1).
pose proof CORE as (_ & _ & _ & _ & _ & _ & _ & _ & FR1).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
assert (SPF : lo <= pf_spf pf - 32 - 48 - 4096 /\ pf_spf pf mod 16 = 0 /\ pf_spf pf <= hiA_top A4L HIx /\ 0 <= pf_spf pf < 2^62 /\ 0 <= pa_sp0 pa < 2^63).
{ clear - LOS HT Gle Gspf SP0. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; lia. }
destruct SPF as (SPF1 & SPF2 & SPF3 & SPF4 & SPF5).
set (RB := pe_blocksA pf q LB0 ts) in *.
assert (Eq0 : pe_blocksA pf q LB0 (tsF ts []) = RB) by (unfold RB, pe_blocksA, tstate_blocks, tsF; cbn [t_pbs t_objbs t_levels]; rewrite Eobj; reflexivity).
rewrite Eq0 in HP1.
pose proof (pe_uw_at HIx pf pa lo m cb nb pj sv v2 ra2 STC FR1 S0V RAV (proj1 HV) (proj2 HV)) as UWA.
unfold jo_new_object_A3_stmt in NEWOBJ.
eapply NEWOBJ with (LB := RB) (lo := lo) (errv := errv) (u := UWfp ra2 v2);
[ exact HP1 | exact (GA_lh _ G1) | rewrite !unsigned_lit by lia; exact UWA | exact UWK | rewrite unsigned_lit by lia; exact ST1 | exact LO | rewrite unsigned_lit by lia; exact SPF1
| rewrite unsigned_lit by lia; exact SPF2 | rewrite unsigned_lit by lia; exact SPF3 | exact ERR1 | reflexivity | exact RA | exact COST
| cbn [uw_cost]; exact (proj2 (heapA_budget A4L HIx _ _ _ _ _ _ _ HP1)) | ].
intros ms2 md2 A2 (m2 & r & errv2 & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & G2 & HB2 & HD2 & OUT2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp hla_base A4L A4H uw_cost] in *. rewrite ?(unsigned_lit (pf_spf pf)) in ST2 by lia. rewrite ?(unsigned_lit (pf_spf pf)) in HPR2 by lia.
assert (HPRc : heap_pres A4H (RB ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m m2) by exact HPR2.
assert (AG : agree_on asegs RB m m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPRc | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
eapply (K m2 md2 A2 B2 errv2 r); [| | lia | cbn [uw_cost] in HD2; lia | exact FS2 | exact FRM2].
- destruct OUT2 as [(-> & HP2) | (Hr & BS & J2 & LEN3 & CAP & HP2)].
+ left. split; [reflexivity|].
eapply (PE_WIN_callG2 HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B B2 ts 0 None [] 1 0 None [] 1 cb nb pj sv errv errv2);
[exact STC | exact WIN | exact VM2 | exact HPRc | rewrite Eq0; exact HP2 | exact ST2 | exact ERR2 | split; reflexivity].
+ right. split; [exact Hr|]. exists BS. split; [exact CAP|]. split; [exact LEN3|].
split.
{ assert (NDb : List.NoDup (map blk_addr BS)).
{ pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP2) as ND. rewrite <- app_assoc, map_app in ND. exact (NoDup_app_remove_r _ _ ND). }
destruct (jval_hdr asegs A4F _ _ _ _ _ J2 NDb) as (n0 & _ & _ & _ & _ & _ & INr & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r n0 HP2 ltac:(apply in_or_app; left; apply in_or_app; left; exact INr)) as (Hn0 & _ & Hr0 & Hrhi & _).
pose proof alloc_ceiling_range. lia. }
eapply (PE_WIN_callG2 HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B B2 ts 0 None [] 1 r (Some (Sobj [])) BS 1 cb nb pj sv errv errv2);
[exact STC | exact WIN | exact VM2 | exact HPRc | | exact ST2 | exact ERR2 | split; [exact Hr | split; [lia | exact J2]]].
eapply (heapA_perm A4L HIx); [exact HP2 | apply Permutation_sym; apply (perm_blocks_tsF pf q LB0 ts BS Eobj) | apply Permutation_refl | apply Permutation_refl].
- eapply PBOKat_agree; [exact PBK | exact AG |]. unfold RB, pe_blocksA, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb.
Qed.
End PeSWinCallOA.
End RC__1.
End Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6oO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QRUw.Mq2 QmZZ. Import QPZI.Mq4. Import QkMG. Import QG8z Qdyh.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq4 Qiiq.Mq0 QsKa.Mq6 Q4v2.Mq0 QlKV.Mq5 QlKV.Mq1 QlKV.Mq7 Q6oO QJZd.Mq1 Q1Ey Ql4f.Mq1 QsKa.Mq8 QrQv.Mq2 QEUF QdGy.Mq6.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QlKV.Mq2 QEUF.Mq0.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma jval_scalar_blocks : forall s m BS p rc, jval asegs A4F s m BS p rc -> s = Sbool \/ s = Sdouble false ->
In (p, 48) BS /\ (length BS <= 3)%nat.
Proof.
intros s m BS p rc J Hs.
assert (X : exists pb PBS, BS = [(p, 48)] ++ PBS /\ opt_pbuf asegs m PBS pb).
{ destruct Hs as [-> | ->]; cbn [jval] in J; destruct J as (pb & PBS & REST & E & OP & J).
- destruct J as (b & junk & -> & _). exists pb, PBS. split; [exact E | exact OP].
- destruct J as (bits & -> & _). exists pb, PBS. split; [exact E | exact OP]. }
destruct X as (pb & PBS & -> & OP). split; [left; reflexivity|].
destruct OP as [[_ ->] | [_ (buf & bpos & size & content & -> & _)]]; cbn; lia.
Qed.

Definition jo_new_double_A_stmt (HIx : heap_iface_A A4L) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word) (u : uwd),
HEAPA A4L HIx A LB LM FRS B m md ->
uw_at (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9d9cc) u ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP ->
bv_unsigned ra mod 2 = 0 ->
newdbl_costB <= bB B -> uw_cost u <= bD B ->
dbl_special (Sem.reg_get F (Z_to_bv 5 10)) ->
(forall ms' md' A', Q6oO.new_obj_A_post HIx (Sdouble false) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo u ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 json_object_new_double_A_entry) fc None m (seg_rom asegs)).

Definition jo_new_boolean_A_stmt (HIx : heap_iface_A A4L) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word),
HEAPA A4L HIx A LB LM FRS B m md ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP ->
bv_unsigned ra mod 2 = 0 ->
bv_unsigned a0 <= 1 ->
newbool_costB <= bB B -> 0 <= bD B ->
(forall ms' md' A', QJZd.Mq1.new_obj_A_post HIx Sbool ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 json_object_new_boolean_A_entry) fc None m (seg_rom asegs)).

Definition new_scalar_costA : Z := 16 * 48 + 512.

Section PeSWinCallSA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis NEWDBL : jo_new_double_A_stmt HIx.
Hypothesis NEWBOOL : jo_new_boolean_A_stmt HIx.

Lemma pe_new_double_w :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP v2 ra2 : Z)
(ra gp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts 0 None [] 1 cb nb pj sv errv ->
PBOKat m ts kP -> new_scalar_costA <= bB B ->
pe_s0 sv = Z_to_bv 64 v2 -> pe_ra sv = Z_to_bv 64 ra2 ->
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64 ->
uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9d9cc) (UWfp ra2 v2) ->
dbl_special (Sem.reg_get F (Z_to_bv 5 10)) ->
bv_unsigned ra mod 2 = 0 ->
(forall m2 md2 A2 B2 errv2 (r : Z) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) F2 fc2,
((r = 0 /\ PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts 0 None [] 1 cb nb pj sv errv2) \/
(r <> 0 /\ exists BS, (length BS <= 3)%nat /\ jfresh (Sdouble false) BS 9 /\ 0 < r < 2^62 /\ PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts r (Some (Sdouble false)) BS 1 cb nb pj sv errv2)) ->
PBOKat m2 ts kP -> bB B - new_scalar_costA <= bB B2 -> bD B <= bD B2 ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 r) w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F2 (ret_pc ra) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 json_object_new_double_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC WIN PBK COST S0V RAV HV UWK DBL RA K.
pose proof WIN as (CORE & BASE & LVo & CUR & Eobj & PP). pose proof BASE as (HP1 & ST1 & ERR1 & _).
pose proof CORE as (_ & _ & _ & _ & _ & _ & _ & _ & FR1).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
assert (SPF : lo <= pf_spf pf - 48 - 4096 /\ pf_spf pf mod 16 = 0 /\ pf_spf pf <= hiA_top A4L HIx /\ 0 <= pf_spf pf < 2^62 /\ 0 <= pa_sp0 pa < 2^63).
{ clear - LOS HT Gle Gspf SP0. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; lia. }
destruct SPF as (SPF1 & SPF2 & SPF3 & SPF4 & SPF5).
set (RB := pe_blocksA pf q LB0 ts) in *.
assert (Eq0 : pe_blocksA pf q LB0 (tsF ts []) = RB) by (unfold RB, pe_blocksA, tstate_blocks, tsF; cbn [t_pbs t_objbs t_levels]; rewrite Eobj; reflexivity).
rewrite Eq0 in HP1.
pose proof (pe_uw_at HIx pf pa lo m cb nb pj sv v2 ra2 STC FR1 S0V RAV (proj1 HV) (proj2 HV)) as UWA.
eapply (NEWDBL ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m md T A RB LM ((pa_F pa, 2) :: FRS) B lo errv (UWfp ra2 v2));
[ exact HP1 | rewrite !unsigned_lit by lia; exact UWA | exact UWK | rewrite unsigned_lit by lia; exact ST1 | exact LO | rewrite unsigned_lit by lia; exact SPF1
| rewrite unsigned_lit by lia; exact SPF2 | rewrite unsigned_lit by lia; exact SPF3 | exact ERR1 | reflexivity | exact RA
| unfold newdbl_costB; unfold new_scalar_costA in COST; exact COST | cbn [uw_cost]; pose proof (proj2 (heapA_budget A4L HIx _ _ _ _ _ _ _ HP1)); lia | exact DBL | ].
intros ms2 md2 A2 (m2 & r & errv2 & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & HB2 & HD2 & OUT2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp hla_base A4L A4H uw_cost] in *. rewrite ?(unsigned_lit (pf_spf pf)) in ST2 by lia. rewrite ?(unsigned_lit (pf_spf pf)) in HPR2 by lia.
assert (HPRc : heap_pres A4H (RB ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m m2) by exact HPR2.
assert (AG : agree_on asegs RB m m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPRc | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
eapply (K m2 md2 A2 B2 errv2 r); [| | unfold newdbl_costB in HB2; unfold new_scalar_costA; lia | lia | exact FS2 | exact FRM2].
- destruct OUT2 as [(-> & HP2) | (Hr & BS & J2 & HP2 & L1)].
+ left. split; [reflexivity|].
eapply (PE_WIN_callG2 HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B B2 ts 0 None [] 1 0 None [] 1 cb nb pj sv errv errv2);
[exact STC | exact WIN | exact VM2 | exact HPRc | rewrite Eq0; exact HP2 | exact ST2 | exact ERR2 | split; reflexivity].
+ right. split; [exact Hr|]. exists BS.
destruct (jval_scalar_blocks _ _ _ _ _ J2 (or_intror eq_refl)) as [INr LEN3].
split; [exact LEN3|]. split; [exact (jfresh_dbl asegs A4F _ _ _ _ J2 L1)|]. split.
{ pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r 48 HP2 ltac:(apply in_or_app; left; apply in_or_app; left; exact INr)) as (_ & _ & Hr0 & Hrhi & _).
pose proof alloc_ceiling_range. lia. }
eapply (PE_WIN_callG2 HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B B2 ts 0 None [] 1 r (Some (Sdouble false)) BS 1 cb nb pj sv errv errv2);
[exact STC | exact WIN | exact VM2 | exact HPRc | | exact ST2 | exact ERR2 | split; [exact Hr | split; [lia | exact J2]]].
eapply (heapA_perm A4L HIx); [exact HP2 | apply Permutation_sym; apply (perm_blocks_tsF pf q LB0 ts BS Eobj) | apply Permutation_refl | apply Permutation_refl].
- eapply PBOKat_agree; [exact PBK | exact AG |]. unfold RB, pe_blocksA, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb.
Qed.

Lemma pe_new_boolean_w :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP bval : Z)
(ra gp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts 0 None [] 1 cb nb pj sv errv ->
PBOKat m ts kP -> new_scalar_costA <= bB B ->
0 <= bval <= 1 ->
bv_unsigned ra mod 2 = 0 ->
(forall m2 md2 A2 B2 errv2 (r : Z) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) F2 fc2,
((r = 0 /\ PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts 0 None [] 1 cb nb pj sv errv2) \/
(r <> 0 /\ exists BS, (length BS <= 3)%nat /\ jfresh Sbool BS 8 /\ 0 < r < 2^62 /\ PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts r (Some Sbool) BS 1 cb nb pj sv errv2)) ->
PBOKat m2 ts kP -> bB B - new_scalar_costA <= bB B2 -> bD B <= bD B2 ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 r) w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F2 (ret_pc ra) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 bval) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 json_object_new_boolean_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC WIN PBK COST HB01 RA K.
pose proof WIN as (CORE & BASE & LVo & CUR & Eobj & PP). pose proof BASE as (HP1 & ST1 & ERR1 & _).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
assert (SPF : lo <= pf_spf pf - 32 - 4096 /\ pf_spf pf mod 16 = 0 /\ pf_spf pf <= hiA_top A4L HIx /\ 0 <= pf_spf pf < 2^62 /\ 0 <= pa_sp0 pa < 2^63).
{ clear - LOS HT Gle Gspf SP0. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; lia. }
destruct SPF as (SPF1 & SPF2 & SPF3 & SPF4 & SPF5).
set (RB := pe_blocksA pf q LB0 ts) in *.
assert (Eq0 : pe_blocksA pf q LB0 (tsF ts []) = RB) by (unfold RB, pe_blocksA, tstate_blocks, tsF; cbn [t_pbs t_objbs t_levels]; rewrite Eobj; reflexivity).
rewrite Eq0 in HP1.
eapply (NEWBOOL ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 bval) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m md T A RB LM ((pa_F pa, 2) :: FRS) B lo errv);
[ exact HP1 | rewrite unsigned_lit by lia; exact ST1 | exact LO | rewrite unsigned_lit by lia; exact SPF1
| rewrite unsigned_lit by lia; exact SPF2 | rewrite unsigned_lit by lia; exact SPF3 | exact ERR1 | reflexivity | exact RA
| rewrite unsigned_lit by lia; lia
| unfold newbool_costB; unfold new_scalar_costA in COST; exact COST | pose proof (proj2 (heapA_budget A4L HIx _ _ _ _ _ _ _ HP1)); lia | ].
intros ms2 md2 A2 (m2 & r & errv2 & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & HB2 & HD2 & OUT2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp hla_base A4L A4H] in *. rewrite ?(unsigned_lit (pf_spf pf)) in ST2 by lia. rewrite ?(unsigned_lit (pf_spf pf)) in HPR2 by lia.
assert (HPRc : heap_pres A4H (RB ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m m2) by exact HPR2.
assert (AG : agree_on asegs RB m m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPRc | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
eapply (K m2 md2 A2 B2 errv2 r); [| | unfold newbool_costB in HB2; unfold new_scalar_costA; lia | lia | exact FS2 | exact FRM2].
- destruct OUT2 as [(-> & HP2) | (Hr & BS & J2 & HP2 & L1)].
+ left. split; [reflexivity|].
eapply (PE_WIN_callG2 HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B B2 ts 0 None [] 1 0 None [] 1 cb nb pj sv errv errv2);
[exact STC | exact WIN | exact VM2 | exact HPRc | rewrite Eq0; exact HP2 | exact ST2 | exact ERR2 | split; reflexivity].
+ right. split; [exact Hr|]. exists BS.
destruct (jval_scalar_blocks _ _ _ _ _ J2 (or_introl eq_refl)) as [INr LEN3].
split; [exact LEN3|]. split; [exact (jfresh_bool asegs A4F _ _ _ _ J2 L1)|]. split.
{ pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r 48 HP2 ltac:(apply in_or_app; left; apply in_or_app; left; exact INr)) as (_ & _ & Hr0 & Hrhi & _).
pose proof alloc_ceiling_range. lia. }
eapply (PE_WIN_callG2 HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B B2 ts 0 None [] 1 r (Some Sbool) BS 1 cb nb pj sv errv errv2);
[exact STC | exact WIN | exact VM2 | exact HPRc | | exact ST2 | exact ERR2 | split; [exact Hr | split; [lia | exact J2]]].
eapply (heapA_perm A4L HIx); [exact HP2 | apply Permutation_sym; apply (perm_blocks_tsF pf q LB0 ts BS Eobj) | apply Permutation_refl | apply Permutation_refl].
- eapply PBOKat_agree; [exact PBK | exact AG |]. unfold RB, pe_blocksA, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb.
Qed.
End PeSWinCallSA.
End RC__1.
End Mq6.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QRUw.Mq2 QmZZ. Import QPZI.Mq4. Import QkMG. Import QG8z Qdyh.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq4 Qiiq.Mq0 QsKa.Mq6 Q4v2.Mq0 QlKV.Mq5 QlKV.Mq1 QlKV.Mq7 Q6oO.Mq0 Q1Ey Ql4f.Mq1 QsKa.Mq8 QrQv.Mq2 QEUF QdGy.Mq6.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition jo_new_string_len_A_stmt (HIx : heap_iface_A A4L) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (sb nsb s len lo : Z) (src : list byte) (errv : word) (u : uwd),
HEAPA A4L HIx A LB LM FRS B m md ->
uw_at (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9e570) u ->
In (sb, nsb) LB -> sb <= s -> s + len <= sb + nsb ->
bytes_at asegs m s src -> Z.of_nat (length src) = len -> 0 <= len < 2^31 ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 len ->
newstr_costB len <= bB B -> uw_cost u <= bD B ->
(forall ms' md' A', Q6oO.Mq0.new_str_A_post HIx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B len lo u ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 json_object_new_string_len_A_entry) fc None m (seg_rom asegs)).

Section PeSWinCallTA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis NEWSTR : jo_new_string_len_A_stmt HIx.

Lemma pe_new_string_w :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP v2 ra2 buf cap bpos : Z) (content : list byte)
(ra gp t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts 0 None [] 1 cb nb pj sv errv ->
PBOKat m ts kP ->
t_pbs ts = [(t_pb ts, PB_SZ); (buf, cap)] -> pbuf_core asegs m (t_pb ts) buf bpos cap content ->
newstr_costB bpos <= bB B ->
pe_s0 sv = Z_to_bv 64 v2 -> pe_ra sv = Z_to_bv 64 ra2 ->
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64 ->
uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9e570) (UWfp ra2 v2) ->
bv_unsigned ra mod 2 = 0 ->
(forall m2 md2 A2 B2 errv2 (r : Z) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) F2 fc2,
((r = 0 /\ PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts 0 None [] 1 cb nb pj sv errv2) \/
(r <> 0 /\ 0 < r < 2^62 /\ PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts r (Some (Sstr false)) [(r, str_objsize bpos)] 1 cb nb pj sv errv2)) ->
PBOKat m2 ts kP -> bB B - newstr_costB bpos <= bB B2 -> bD B <= bD B2 ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 r) w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F2 (ret_pc ra) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 buf) (Z_to_bv 64 bpos) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 json_object_new_string_len_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC WIN PBK Epbs PBC COST S0V RAV HV UWK RA K.
pose proof WIN as (CORE & BASE & LVo & CUR & Eobj & PP). pose proof BASE as (HP1 & ST1 & ERR1 & _).
pose proof CORE as (_ & _ & _ & _ & _ & _ & _ & _ & FR1).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
assert (SPF : lo <= pf_spf pf - 48 - 4096 /\ pf_spf pf mod 16 = 0 /\ pf_spf pf <= hiA_top A4L HIx /\ 0 <= pf_spf pf < 2^62 /\ 0 <= pa_sp0 pa < 2^63).
{ clear - LOS HT Gle Gspf SP0. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; lia. }
destruct SPF as (SPF1 & SPF2 & SPF3 & SPF4 & SPF5).
set (RB := pe_blocksA pf q LB0 ts) in *.
assert (Eq0 : pe_blocksA pf q LB0 (tsF ts []) = RB) by (unfold RB, pe_blocksA, tstate_blocks, tsF; cbn [t_pbs t_objbs t_levels]; rewrite Eobj; reflexivity).
rewrite Eq0 in HP1.
pose proof (pe_uw_at HIx pf pa lo m cb nb pj sv v2 ra2 STC FR1 S0V RAV (proj1 HV) (proj2 HV)) as UWA.
destruct PBC as (Hbp & Hcap & Hlen & _ & BUFC).
pose proof (rw_cells_bytes_at' _ _ _ _ BUFC) as BUFB. cbn [cells_bytes cbytes] in BUFB. rewrite app_nil_r in BUFB.
pose proof (bytes_at_sub A4H m buf content 0%nat (Z.to_nat bpos) BUFB ltac:(lia)) as SRC. cbn [hl_segs hla_base A4L A4H skipn Z.of_nat] in SRC. rewrite Z.add_0_r in SRC.
assert (INbuf : In (buf, cap) RB) by (unfold RB, pe_blocksA, tstate_blocks; rewrite Epbs; apply in_or_app; left; cbn [app]; right; left; reflexivity).
eapply (NEWSTR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 buf) (Z_to_bv 64 bpos) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m md T A RB LM ((pa_F pa, 2) :: FRS) B buf cap buf bpos lo (firstn (Z.to_nat bpos) content) errv (UWfp ra2 v2));
[ exact HP1 | rewrite !unsigned_lit by lia; exact UWA | exact UWK | exact INbuf | lia | lia | exact SRC | rewrite length_firstn; lia | lia
| rewrite unsigned_lit by lia; exact ST1 | exact LO | rewrite unsigned_lit by lia; exact SPF1
| rewrite unsigned_lit by lia; exact SPF2 | rewrite unsigned_lit by lia; exact SPF3 | exact ERR1 | reflexivity | exact RA | reflexivity | reflexivity
| exact COST | cbn [uw_cost]; pose proof (proj2 (heapA_budget A4L HIx _ _ _ _ _ _ _ HP1)); lia | ].
intros ms2 md2 A2 (m2 & r & errv2 & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & HB2 & HD2 & OUT2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp hla_base A4L A4H uw_cost] in *. rewrite ?(unsigned_lit (pf_spf pf)) in ST2 by lia. rewrite ?(unsigned_lit (pf_spf pf)) in HPR2 by lia.
assert (HPRc : heap_pres A4H (RB ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m m2) by exact HPR2.
assert (AG : agree_on asegs RB m m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPRc | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
eapply (K m2 md2 A2 B2 errv2 r); [| | lia | lia | exact FS2 | exact FRM2].
- destruct OUT2 as [(-> & HP2) | (Hr & J2 & HP2)].
+ left. split; [reflexivity|].
eapply (PE_WIN_callG2 HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B B2 ts 0 None [] 1 0 None [] 1 cb nb pj sv errv errv2);
[exact STC | exact WIN | exact VM2 | exact HPRc | rewrite Eq0; exact HP2 | exact ST2 | exact ERR2 | split; reflexivity].
+ right. split; [exact Hr|]. split.
{ pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r (str_objsize bpos) HP2 ltac:(apply in_or_app; left; left; reflexivity)) as (_ & _ & Hr0 & Hrhi & _).
pose proof alloc_ceiling_range. unfold str_objsize in Hrhi. lia. }
eapply (PE_WIN_callG2 HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B B2 ts 0 None [] 1 r (Some (Sstr false)) [(r, str_objsize bpos)] 1 cb nb pj sv errv errv2);
[exact STC | exact WIN | exact VM2 | exact HPRc | | exact ST2 | exact ERR2 | split; [exact Hr | split; [lia | exact J2]]].
eapply (heapA_perm A4L HIx); [exact HP2 | apply Permutation_sym; apply (perm_blocks_tsF pf q LB0 ts [(r, str_objsize bpos)] Eobj) | apply Permutation_refl | apply Permutation_refl].
- eapply PBOKat_agree; [exact PBK | exact AG |]. unfold RB, pe_blocksA, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb.
Qed.
End PeSWinCallTA.
End RC__1.
End Mq7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg QTEu QnCn Q30W QgHv Q4xz QL3k Q228 QnPO QpNt QkXq QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun Qfw3_c1.Mq2.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0.
Import QnCn.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7 QsKa.Mq3 Q30W.Mq0 Q4v2.Mq0 QgHv.Mq0 Q1Y6.Mq1 QsKa.Mq6 Q4xz QlKV.Mq2 QsKa Q9O6.Mq2 QL3k.Mq1 Q228.Mq4 Qwm6.Mq1 QnPO.Mq0 Q228.Mq6 Q228.Mq0 QlKV QpNt.Mq4 QkXq.Mq1.
Import QWxq_c1 QsjA.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).

Ltac post_callS segs m :=
let ms' := fresh "ms'" in let PO := fresh "POST" in
intros ms' PO;
destruct_exs PO;
let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
destruct PO as [E [MUc [WMc PO]]];
first [ destruct PO as [MIc PO] | rename PO into MIc ];
subst ms';
rewrite ?unsigned_lit in MUc by lia; try rewrite ?unsigned_lit in PO by lia;
lazymatch type of MUc with
| munch _ m ?m' =>
transport_after_call segs m m' MUc WMc;
clear MUc WMc;
try match goal with H : mem_inv segs m |- _ => clear H end;
try clear m
end;
try destruct_ands PO;
try (lazymatch goal with
| |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
end).
Tactic Notation "callS" uconstr(SPEC) :=
lazymatch goal with
| |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | post_callS segs m ]
end.

Ltac if_rw E b :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b by (rewrite E; vm_compute; reflexivity)
end; cbv iota.

Lemma land1_cases : forall fl, 0 <= fl -> Z.land fl 1 = 0 \/ Z.land fl 1 = 1.
Proof.
intros fl H. change 1 with (Z.ones 1) at 1. change 1 with (Z.ones 1) at 2. rewrite !Z.land_ones by lia.
change (2^1) with 2. pose proof (Z.mod_pos_bound fl 2 ltac:(lia)). lia.
Qed.
Lemma land58_bit : forall fl b, Z.land fl 58 = 0 -> Z.land 58 b = b -> Z.land fl b = 0.
Proof. intros fl b H Hb. rewrite <- Hb. rewrite Z.land_assoc, H. reflexivity. Qed.
Lemma land3_of_58 : forall fl, Z.land fl 58 = 0 -> Z.land fl 3 = Z.land fl 1.
Proof.
intros fl H. change 3 with (Z.lor 1 2). rewrite Z.land_lor_distr_r. rewrite (land58_bit fl 2 H eq_refl). apply Z.lor_0_r.
Qed.

Definition LIT_LBRACE : list byte := Eval vm_compute in lit_bytesA 0x23420 1.
Definition LIT_RBRACE : list byte := Eval vm_compute in lit_bytesA 0x23580 1.
Definition LIT_SP_RBRACE : list byte := Eval vm_compute in lit_bytesA 0x23560 2.
Definition LIT_COLON_SP : list byte := Eval vm_compute in lit_bytesA 0x23500 2.
Definition LIT_COLON : list byte := Eval vm_compute in lit_bytesA 0x23520 1.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section ObjK.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Lemma blk_gran_at : forall A LBx LMx FR B m md a n x, HEAPAx A LBx LMx FR B m md -> In (a, n) LBx -> a <= x -> x + 8 <= a + n -> x mod 8 = 0 ->
ro_cells asegs m (x / 8 + 2147450880) [C1 (Z_to_bv 8 0)].
Proof.
intros A LBx LMx FR B m md a n x HP Hin Hax Hxn Hx8.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a n HP ltac:(apply in_or_app; left; exact Hin)) as (_ & Hal & _).
pose proof (blk_granS HIx _ _ _ _ _ _ _ a n ((x - a) / 8) HP Hin ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia)) as SH.
replace (a / 8 + 2147450880 + (x - a) / 8) with (x / 8 + 2147450880) in SH by (Z.div_mod_to_equations; lia). exact SH.
Qed.
End ObjK.

Section Obj.
Variable HIx : heap_iface_A A4L.
Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.
Hypothesis ESC : esc_specA HIx.

Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud).
Variables (pb lo p rc pb0 lv fl t tbl size bpos0 cap0 w : Z).
Variables (es : list oent) (KBS : list (list blk)) (kids : list (option jshape)) (T : TSet) (Y R : list blk).
Let usp := bv_unsigned sp.
Let TBS : list blk := (t, 56) :: (tbl, 40 * size) :: map (fun e => (oe_k e, oe_kn e)) es.
Hypothesis KIDS : forall s', In (Some s') kids -> ser_specA HIx (afn_of s') s'.
Hypothesis FL : aflags_ok fl.
Hypothesis Hlv : 0 <= lv.
Hypothesis Hlvd : lv + sdepth (Sobj kids) <= 1000.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= usp - ser_budgetA (Sobj kids).
Hypothesis SPA : usp mod 16 = 0.
Hypothesis HT : usp <= hiA_top A4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis CAP0 : 32 <= cap0 < 2^30.
Hypothesis TXT : bpos0 + w < 2^28.
Hypothesis NEED : ser_need cap0 bpos0 w <= bB B0.
Hypothesis JHEX0 : JHEX_A m0.
Hypothesis FRSN : Z.of_nat (length FRS) + 1 < 4096.
Hypothesis INCL : incl ((p, 48) :: TBS ++ concat KBS) LB.
Hypothesis NODE0 : rw_cells asegs m0 p (jhdr_cells JT_OBJECT rc (fn_obj_to_json_string A4F) pb0 0 0 ++ [C8 (wz t)]).
Hypothesis OT0 : otab asegs m0 TBS t es.
Hypothesis KOK : kids_okv asegs A4F m0 kids (map (fun e => (oe_k e, oe_v e)) es) KBS.
Hypothesis JTX : jtxk_obj kids (map (fun e => (oe_k e, oe_kn e)) es) (concat KBS ++ Y) 24 = Some (w, R).
Hypothesis K : forall ms' md' A', ser_postA HIx ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 pb cap0 bpos0 w lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms'.

Notation ser_memx := (ser_memA HIx sp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w).
Let LEN := Z.of_nat (length es).
Definition savedR : list cell := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma facts :
0 <= usp < 2^64 /\ In (p, 48) LB /\ 0 <= fl < 2^31 /\
Z.land fl 2 = 0 /\ Z.land fl 8 = 0 /\ Z.land fl 32 = 0 /\ Z.land fl 3 = Z.land fl 1 /\ (Z.land fl 1 = 0 \/ Z.land fl 1 = 1) /\
0 <= kdepth kids /\ lo <= usp - 192 - 256 * kdepth kids - 16384 - 64 /\
length es = length kids /\ length KBS = length kids /\ incl TBS LB.
Proof.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
assert (INp : In (p, 48) LB) by (apply INCL; left; reflexivity).
destruct FL as [Rfl FL58].
pose proof (kdepth_nonneg kids) as KD. unfold ser_budgetA, ASER_LEVEL, ASER_LEAF in LOS. rewrite sdepth_obj in LOS.
destruct (kids_okv_len _ _ _ _ _ _ KOK) as [L1 L2]. rewrite length_map in L1.
split; [exact SPR|]. split; [exact INp|]. split; [exact Rfl|].
split; [exact (land58_bit fl 2 FL58 eq_refl)|]. split; [exact (land58_bit fl 8 FL58 eq_refl)|]. split; [exact (land58_bit fl 32 FL58 eq_refl)|].
split; [exact (land3_of_58 fl FL58)|]. split; [apply land1_cases; lia|].
split; [exact KD|]. split; [unfold usp in *; lia|].
split; [exact L1|]. split; [exact L2|].
intros b Hb. apply INCL. right. apply in_or_app. left. exact Hb.
Qed.

Lemma factsM : forall A FA CH e m md, ser_memx A FRS FA CH e m md ->
0 < p /\ p + 48 <= alloc_ceiling /\ p mod 8 = 0 /\
rw_cells asegs m p (jhdr_cells JT_OBJECT rc (fn_obj_to_json_string A4F) pb0 0 0 ++ [C8 (wz t)]) /\
ro_cells asegs m (p / 8 + 2147450880) [C1 (Z_to_bv 8 0)] /\ ro_cells asegs m (p / 8 + 2147450885) [C1 (Z_to_bv 8 0)] /\
otab asegs m TBS t es /\
kids_okv asegs A4F m kids (map (fun e => (oe_k e, oe_v e)) es) KBS.
Proof.
intros A FA CH e m md (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & _).
pose proof facts as (SPR & INp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & INT).
assert (INp' : In (p, 48) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; exact INp).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p 48 HP ltac:(apply in_or_app; left; exact INp')) as (_ & Hpal & Hplo & Hphi & _).
assert (AG : agree_on asegs LB m0 m).
{ eapply (agree_of_heap_pres asegs A4H); [exact HPR | reflexivity |]. intros b Hb. apply in_or_app. left. exact Hb. }
split; [exact Hplo|]. split; [exact Hphi|]. split; [clear - Hpal; Z.div_mod_to_equations; lia|].
split. { eapply (heap_pres_rw_cells A4H); [exact HPR | exact NODE0 |]. eapply client_range_block; [apply in_or_app; left; exact INp | lia | cbn; lia]. }
split. { pose proof (blk_granS HIx _ _ _ _ _ _ _ p 48 0 HP INp' ltac:(lia) ltac:(lia)) as SH0. rewrite Z.add_0_r in SH0. exact SH0. }
split. { pose proof (blk_granS HIx _ _ _ _ _ _ _ p 48 5 HP INp' ltac:(lia) ltac:(lia)) as SH5.
replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SH5 by lia. exact SH5. }
split. { eapply (otab_agree asegs); [exact OT0 | exact AG | exact INT]. }
eapply (kids_okv_agree asegs A4F); [exact KOK | exact AG |]. intros b Hb. apply INCL. right. apply in_or_app. right. exact Hb.
Qed.

Lemma entryM : forall A FA CH e0 m md j e, ser_memx A FRS FA CH e0 m md -> nth_error es j = Some e ->
0 < oe_a e /\ oe_a e + 32 <= alloc_ceiling /\ oe_a e mod 8 = 0 /\
(exists pad : word, rw_cells asegs m (oe_a e) [C8 (wz (oe_k e)); C4 (wz 0); C4 pad; C8 (wz (oe_v e)); C8 (wz (ohd (skipn (S j) es)))]) /\
ro_cells asegs m (oe_a e / 8 + 2147450880) [C1 (Z_to_bv 8 0)] /\ ro_cells asegs m (oe_a e / 8 + 2147450882) [C1 (Z_to_bv 8 0)] /\
ro_cells asegs m (oe_a e / 8 + 2147450883) [C1 (Z_to_bv 8 0)] /\
cstr asegs m (oe_k e) (oe_kn e) (oe_ks e) /\ In (oe_k e, oe_kn e) LB /\ oe_kn e <= 2^31.
Proof.
intros A FA CH e0 m md j e INV Hj.
pose proof (factsM _ _ _ _ _ _ INV) as (_ & _ & _ & _ & _ & _ & OT & _).
destruct INV as (buf & cap & bpos & content & errv & B & HP & _).
pose proof facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & INT).
destruct OT as (_ & _ & ENT). destruct (ENT j e Hj) as (A0 & AL8 & (a & kk & Hin & Ha1 & Ha2) & RW & CS & INk & KN).
assert (Hin' : In (a, kk) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; apply INT; exact Hin).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a kk HP ltac:(apply in_or_app; left; exact Hin')) as (_ & _ & _ & Hhi & _).
split; [exact A0|]. split; [lia|]. split; [exact AL8|]. split; [exact RW|].
split; [exact (blk_gran_at HIx _ _ _ _ _ _ _ a kk (oe_a e) HP Hin' ltac:(lia) ltac:(lia) AL8)|].
split. { pose proof (blk_gran_at HIx _ _ _ _ _ _ _ a kk (oe_a e + 16) HP Hin' ltac:(lia) ltac:(lia) ltac:(clear - AL8; Z.div_mod_to_equations; lia)) as X.
replace ((oe_a e + 16) / 8 + 2147450880) with (oe_a e / 8 + 2147450882) in X by (clear - AL8; Z.div_mod_to_equations; lia). exact X. }
split. { pose proof (blk_gran_at HIx _ _ _ _ _ _ _ a kk (oe_a e + 24) HP Hin' ltac:(lia) ltac:(lia) ltac:(clear - AL8; Z.div_mod_to_equations; lia)) as X.
replace ((oe_a e + 24) / 8 + 2147450880) with (oe_a e / 8 + 2147450883) in X by (clear - AL8; Z.div_mod_to_equations; lia). exact X. }
split; [exact CS|]. split; [apply INT; exact INk | exact KN].
Qed.

Lemma obj_failA :
forall (x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) F' fc' m md A (PRE : list cell) e,
ser_memx A FRS (usp + -192) [(usp + -192, PRE ++ savedR)] e m md -> cells_size PRE = 88%nat ->
0 <= e <= w ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md (MS (mkR x1 (wz (usp + -192)) gp (wz A_TP) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F' (wz 0x9b500) fc' None m (seg_rom asegs)).
Proof.
intros until e. intros INV HPRE He FS' FR'.
pose proof facts as (SPR & INp & Rfl & FL2 & FL8 & FL32 & FL3 & FC1 & KD & LOS' & _).
destruct INV as (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & Hbp & Hcap & HBB & HBD).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
apply Forall_inv in CHm. cbn [fst snd] in CHm.
apply (proj1 (rw_cells_app asegs _ _ PRE _)) in CHm. destruct CHm as [PREc SAVc]. rewrite HPRE in SAVc. change (Z.of_nat 88) with 88 in SAVc.
replace (usp + -192 + 88) with (usp + -104) in SAVc by lia.
unfold savedR in SAVc. unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl (@nil (Z * Z)) m) as MU.
assert (STU : stk asegs m lo (bv_unsigned sp)).
{ pose proof (stk_release asegs m lo (bv_unsigned sp + -192) _ ST PREc ltac:(lia)) as S1. rewrite HPRE in S1. change (Z.of_nat 88) with 88 in S1.
replace (bv_unsigned sp + -192 + 88) with (bv_unsigned sp + -104) in S1 by lia.
pose proof (stk_release asegs m lo (bv_unsigned sp + -104) _ S1 SAVc ltac:(lia)) as S2. cbn [cells_size csize Nat.add] in S2.
replace (bv_unsigned sp + -104 + Z.of_nat 104) with (bv_unsigned sp) in S2 by lia. exact S2. }
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. do 13 step. step. step.
evt_done5. apply K. unfold ser_postA.
eexists m, _, errv, buf, cap, bpos, content, B.
split; [apply ret_statew_intro; [exact FS' | intros _; exact FR']|].
split; [exact VM|]. split; [exact STU|]. split; [exact HPR|]. split; [exact ERR|]. split; [exact HP|]. split; [exact PB|].
split; [lia|]. split; [exact Hcap|]. split; [exact HBB | exact HBD].
Qed.

Lemma obj_closeA :
forall (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) F' fc' m md A (PRE : list cell) e,
ser_memx A FRS (usp + -192) [(usp + -192, PRE ++ savedR)] e m md -> cells_size PRE = 88%nat ->
0 <= e -> e + 2 <= w ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md (MS (mkR x1 (wz (usp + -192)) gp (wz A_TP) t0 t1 t2 (wz pb) x9 a0 a1 a2 a3 a4 a5 a6 a7
(wz fl) x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F' (wz 0x9b4e4) fc' None m (seg_rom asegs)).
Proof.
intros until e. intros INV HPRE He Hew FS' FR'.
pose proof facts as (SPR & INp & Rfl & FL2 & FL8 & FL32 & FL3 & FC1 & KD & LOS' & _).
destruct INV as (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & Hbp & Hcap & HBB & HBD).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
apply Forall_inv in CHm. cbn [fst snd] in CHm.
apply (proj1 (rw_cells_app asegs _ _ PRE _)) in CHm. destruct CHm as [PREc SAVc]. rewrite HPRE in SAVc. change (Z.of_nat 88) with 88 in SAVc.
replace (usp + -192 + 88) with (usp + -104) in SAVc by lia.
unfold savedR in SAVc. unfold usp in *. unfold_consts.
pose proof PB as (Hbp0 & Hcap0 & Hlen & PBS & PBUF).
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl (@nil (Z * Z)) m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. rewrite (unsigned_lit fl) by lia. rewrite FL3.
step. step.
assert (STU : stk asegs m lo (bv_unsigned sp)).
{ pose proof (stk_release asegs m lo (bv_unsigned sp + -192) _ ST PREc ltac:(lia)) as S1. rewrite HPRE in S1. change (Z.of_nat 88) with 88 in S1.
replace (bv_unsigned sp + -192 + 88) with (bv_unsigned sp + -104) in S1 by lia.
pose proof (stk_release asegs m lo (bv_unsigned sp + -104) _ S1 SAVc ltac:(lia)) as S2. cbn [cells_size csize Nat.add] in S2.
replace (bv_unsigned sp + -104 + Z.of_nat 104) with (bv_unsigned sp) in S2 by lia. exact S2. }
assert (INVU : ser_memx A FRS (bv_unsigned sp) [] e m md).
{ exists buf, cap, bpos, content, errv, B.
split; [exact HP|]. split; [exact PB|]. split; [constructor|]. split; [constructor|]. split; [exact FSUB|].
split; [exact ERR|]. split; [exact STU|]. split; [exact HPR|]. split; [exact VM|].
split; [exact Hbp|]. split; [exact Hcap|]. split; [exact HBB | exact HBD]. }
assert (TAILK : forall (lit k : Z) (bs : list byte) (t0_ t1_ t2_ a3_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ : word),
ro_bytes_b asegs lit bs = true -> Z.of_nat (length bs) = k -> src_ro_chk lit k = true -> 0 < k <= 2 -> 0 <= lit -> lit + k < 2^32 ->
evt asegs (AJ5e A4L HIx A T md)
(MS (mkR ra sp gp (Z_to_bv 64 6434400) t0_ t1_ t2_ s0 s1 (Z_to_bv 64 pb) (Z_to_bv 64 lit) (Z_to_bv 64 k) a3_ a4_ a5_ a6_ a7_
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3_ t4_ t5_ t6_)
F' (Z_to_bv 64 0x9a0ac) fc' None m (seg_rom asegs))).
{ intros lit k bs t0_ t1_ t2_ a3_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ RB BL CHK Hk Hl Hlk.
evt_done5.
rewrite <- (Z_to_bv_bv_unsigned ra) at 1. rewrite <- (Z_to_bv_bv_unsigned sp) at 1.
eapply (ser_litA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w LO HT CAP0 TXT NEED OBL_REALLOC_NF lit k bs RB BL CHK ltac:(lia) Hl Hlk) with (F := F) (e := e);
[ exact INVU | exact He | lia | lia | exact SPA | lia | lia | reflexivity | word_range ra RAR; lia | exact RA | exact FS' | exact FR' | ].
intros A2 m2 md2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 INV2 FS2 FR2.
pose proof INV2 as (buf2 & cap2 & bpos2 & content2 & errv2 & B2 & HP2 & PB2 & _ & _ & _ & ERR2 & ST2 & HPR2 & VM2 & Hb2 & Hc2 & HB2 & HD2).
apply K. unfold ser_postA.
exists m2, a0', errv2, buf2, cap2, bpos2, content2, B2.
rewrite !Z_to_bv_bv_unsigned.
assert (ERA : ra = ret_pc ra).
{ word_range ra RAR. rewrite <- (Z_to_bv_bv_unsigned ra) at 2. rewrite ret_pc_even by (try exact RA; lia). rewrite Z_to_bv_bv_unsigned. reflexivity. }
split; [unfold ret_statew; do 16 eexists; split; [rewrite <- ERA; reflexivity|]; split; [exact FS2 | intros _; exact FR2]|].
split; [exact VM2|]. split; [exact ST2|]. split; [exact HPR2|]. split; [exact ERR2|]. split; [exact HP2|]. split; [exact PB2|].
split; [lia|]. split; [exact Hc2|]. split; [exact HB2 | exact HD2]. }
destruct FC1 as [E1 | E1]; rewrite E1.
-
if_lit. step. step. step. step. do 13 step. step. step. fold_mkR.
eapply (TAILK 0x23580 1 LIT_RBRACE); [vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | lia | lia | lia].
-
if_lit. step. step. step. step. step. do 13 step. step. step. fold_mkR.
eapply (TAILK 0x23560 2 LIT_SP_RBRACE); [vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | lia | lia | lia].
Qed.

Lemma obj_exitA :
forall (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) F' fc' m md A (c0 : word) (PRE : list cell) e,
ser_memx A FRS (usp + -192) [(usp + -192, (C8 c0 :: PRE) ++ savedR)] e m md -> cells_size PRE = 80%nat ->
0 <= e -> e + 2 <= w ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md (MS (mkR x1 (wz (usp + -192)) gp (wz A_TP) t0 t1 t2 (wz pb) x9 a0 a1 a2 a3 a4 a5 a6 a7
(wz fl) x19 x20 (wz 0) x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F' (wz 0x9b4dc) fc' None m (seg_rom asegs)).
Proof.
intros until e. intros INV HPRE He Hew FS' FR'.
pose proof facts as (SPR & _).
pose proof INV as (buf & cap & bpos & content & errv & B & HP & PB & CHm & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
apply Forall_inv in CHm. cbn [fst snd] in CHm. cbn [app] in CHm.
apply (proj1 (rw_cells_app asegs _ _ [C8 c0] _)) in CHm. destruct CHm as [C0c RESTc]. stash RESTc. stash INV.
unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl (@nil (Z * Z)) m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. step. if_lit.
evt_done5. unstash INV.
eapply obj_closeA; [exact INV | cbn [cells_size csize Nat.add]; rewrite HPRE; reflexivity | exact He | exact Hew | exact FS' | exact FR'].
Qed.

Lemma kid_callO : forall (s' : jshape) (v pbk : Z) (RESTk : list blk)
(x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x19 x21 x22 x23 x25 x27 t3 t4 t5 t6 : word) F' fc' A CH e m md,
ser_memx A FRS (usp + -192) CH e m md -> jnode asegs A4F s' m RESTk v 1 pbk -> incl RESTk LB ->
(AJ5 A4L HIx A T md (MS (mkR (wz 0x9b3c8) (wz (usp + -192)) gp (wz A_TP) t0 t1 t2 (wz pb) x9 (wz v) (wz pb) (wz (lv + 1)) (wz fl) (wz (afn_of s')) a5 a6 a7
(wz fl) x19 (wz (lv + 1)) x21 x22 x23 (wz v) x25 (wz 2147450880) x27 t3 t4 t5 t6) F' (wz (afn_of s')) fc' None m (seg_rom asegs))) ->
AJ5 A4L HIx A T md (MS (mkR x1 (wz (usp + -192)) gp (wz A_TP) t0 t1 t2 (wz pb) x9 a0 a1 a2 a3 a4 a5 a6 a7
(wz fl) x19 (wz (lv + 1)) x21 x22 x23 (wz v) x25 (wz 2147450880) x27 t3 t4 t5 t6) F' (wz 0x9b39c) fc' None m (seg_rom asegs)).
Proof.
intros until md. intros INV JN INCLk KONT.
pose proof facts as (SPR & _ & Rfl & _).
pose proof INV as (buf & cap & bpos & content & errv & B & HP & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
destruct (jnode_hdr asegs A4F _ _ _ _ _ _ JN) as (n & ty & udel & ud & cs & rest & ER & Hn & HDR).
assert (INv : In (v, n) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; apply INCLk; rewrite ER; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ v n HP ltac:(apply in_or_app; left; exact INv)) as (_ & Hval & Hvlo & Hvhi & _).
pose proof (blk_granS HIx _ _ _ _ _ _ _ v n 1 HP INv ltac:(lia) ltac:(lia)) as SHv.
replace (v / 8 + 2147450880 + 1) with (v / 8 + 2147450881) in SHv by lia.
apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _; _; _] cs)) in HDR. destruct HDR as [HDR _].
clear INV JN.
unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl (@nil (Z * Z)) m) as MU.
a4l.
unfold afn_of in KONT.
reenterA asegs A4L HIx asegs_wx HP.
step. asan_chkA.
destruct s' as [|[|]| |[|]|kids'|kids'];
(lazymatch type of HDR with context [fn_ofF A4F ?s] => let fv := eval vm_compute in (fn_ofF A4F s) in change (fn_ofF A4F s) with fv in HDR, KONT end);
step; do 4 step; step; fold_mkR; evt_done5; exact KONT.
Qed.

Definition objFR : list cell :=
[C8 (wz lv); C8 (wz 0x23540); C8 (wz 0x23480); C8 (wz (2 * (lv + 1))); C8 (wz 0x23440); C8 (wz 0x23460); C8 (wz 0x234a0); C8 (wz 0x23500); C8 (wz 0x23520);
C8 (wz 0); C8 (wz 0x23360)] ++ savedR.
Notation keyblks := (map (fun e => (oe_k e, oe_kn e)) es).

Definition st_obj (pc : Z) (x9 x19 x24 : word) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m : word -> option byte) : machine_state :=
MS (mkR x1 (wz (usp + -192)) gp (wz A_TP) t0 t1 t2 (wz pb) x9 a0 a1 a2 a3 a4 a5 a6 a7
(wz fl) x19 (wz (lv + 1)) (wz 0) (wz (Z.land fl 1)) (wz 0x234c0) x24 (wz 0) (wz 2147450880) (wz 0x234e0) t3 t4 t5 t6)
F' (wz pc) fc' None m (seg_rom asegs).

Definition loopK (bound : Z) : Prop :=
forall (j : nat) (e : oent) (f acc : Z) (P : list blk) (x9 x24 : word) (x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' m md A,
nth_error es j = Some e -> LEN - Z.of_nat j <= bound -> (f = 0 \/ f = 1) ->
pbtail P -> jtxk_obj (skipn j kids) (skipn j keyblks) (P ++ concat (skipn j KBS) ++ Y) acc = Some (w, R) -> 24 <= acc ->
ser_memx A FRS (usp + -192) [(usp + -192, objFR)] (acc - 2) m md ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md (st_obj 0x9b2e8 x9 (wz (oe_a e)) x24 x1 t0 t1 t2 a0 (wz f) a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m).

Section Iter.
Variable bound : Z.
Hypothesis IH : loopK bound.

Lemma obj_nextA :
forall (j : nat) (e : oent) (acc : Z) (P : list blk) (x9 x24 : word) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' m md A,
nth_error es j = Some e -> LEN - Z.of_nat j <= bound + 1 ->
pbtail P -> jtxk_obj (skipn (S j) kids) (skipn (S j) keyblks) (P ++ concat (skipn (S j) KBS) ++ Y) acc = Some (w, R) -> 24 <= acc ->
ser_memx A FRS (usp + -192) [(usp + -192, objFR)] (acc - 2) m md ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md (st_obj 0x9b4c0 x9 (wz (oe_a e)) x24 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m).
Proof.
intros until A. intros Hj Hb HP0 JT Hacc INV FS' FR'.
pose proof facts as (SPR & INp & Rfl & FL2 & FL8 & FL32 & FL3 & FC1 & KD & LOS' & LESk & LKBS & INT).
destruct (entryM _ _ _ _ _ _ _ _ INV Hj) as (Ha0 & Hah & Ha8 & (pad & ENT) & SHe0 & SHe2 & SHe3 & _ & _ & _).
pose proof INV as (buf & cap & bpos & content & errv & B & HP & PB & CHm & _ & _ & _ & ST & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
apply Forall_inv in CHm. cbn [fst snd] in CHm. unfold objFR, savedR in CHm. cbn [app] in CHm.
unfold st_obj. unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl (@nil (Z * Z)) m) as MU.
stash INV.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. asan_chkA.
step. step.
rewrite (ohd_skipn es (S j)).
destruct (nth_error es (S j)) as [e'|] eqn:Hj'.
- unstash INV.
destruct (entryM _ _ _ _ _ _ _ _ INV Hj') as (Ha0' & Hah' & _).
unfold_consts.
if_truex. fold_mkR. evt_done5.
pose proof (nth_error_Some es (S j)) as NS. rewrite Hj' in NS.
unfold loopK, st_obj in IH.
eapply (IH (S j) e' 0 acc P); [exact Hj' | unfold LEN in *; lia | left; reflexivity | exact HP0 | exact JT | exact Hacc | exact INV | exact FS' | exact FR'].
- if_lit. fold_mkR. evt_done5. unstash INV.
apply nth_error_None in Hj'.
assert (Ew : w = acc) by (eapply (jtxk_obj_done kids (S j)); [lia | exact JT]).
eapply obj_exitA with (c0 := Z_to_bv 64 lv) (e := acc - 2)
(PRE := [C8 (Z_to_bv 64 0x23540); C8 (Z_to_bv 64 0x23480); C8 (Z_to_bv 64 (2 * (lv + 1))); C8 (Z_to_bv 64 0x23440); C8 (Z_to_bv 64 0x23460); C8 (Z_to_bv 64 0x234a0);
C8 (Z_to_bv 64 0x23500); C8 (Z_to_bv 64 0x23520); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x23360)]);
[exact INV | reflexivity | lia | lia | exact FS' | exact FR'].
Qed.

Lemma obj_ret_kidA :
forall (j : nat) (e : oent) (acc : Z) (P : list blk) (x9 x24 : word) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' m md A,
nth_error es j = Some e -> LEN - Z.of_nat j <= bound + 1 ->
pbtail P -> jtxk_obj (skipn (S j) kids) (skipn (S j) keyblks) (P ++ concat (skipn (S j) KBS) ++ Y) acc = Some (w, R) -> 24 <= acc -> acc <= w ->
ser_memx A FRS (usp + -192) [(usp + -192, objFR)] (acc - 2) m md ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md (st_obj 0x9b3c8 x9 (wz (oe_a e)) x24 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m).
Proof.
intros until A. intros Hj Hb HP0 JT Hacc Haw INV FS' FR'.
pose proof facts as (SPR & _).
pose proof INV as (buf & cap & bpos & content & errv & B & HP & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
unfold st_obj. unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl (@nil (Z * Z)) m) as MU.
stash INV.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. if_cases NEG; fold_mkR.
- evt_done5. unstash INV.
eapply (obj_nextA j e acc P); [exact Hj | exact Hb | exact HP0 | exact JT | exact Hacc | exact INV | exact FS' | exact FR'].
- step. fold_mkR. evt_done5. unstash INV.
eapply obj_failA with (e := acc - 2)
(PRE := [C8 (Z_to_bv 64 lv); C8 (Z_to_bv 64 0x23540); C8 (Z_to_bv 64 0x23480); C8 (Z_to_bv 64 (2 * (lv + 1))); C8 (Z_to_bv 64 0x23440); C8 (Z_to_bv 64 0x23460); C8 (Z_to_bv 64 0x234a0);
C8 (Z_to_bv 64 0x23500); C8 (Z_to_bv 64 0x23520); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x23360)]);
[exact INV | reflexivity | lia | exact FS' | exact FR'].
Qed.

Lemma obj_nullA :
forall (j : nat) (e : oent) (acc : Z) (P : list blk) (x9 x24 : word) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' m md A,
nth_error es j = Some e -> LEN - Z.of_nat j <= bound + 1 ->
pbtail P -> jtxk_obj (skipn (S j) kids) (skipn (S j) keyblks) (P ++ concat (skipn (S j) KBS) ++ Y) acc = Some (w, R) -> 24 <= acc -> acc <= w ->
ser_memx A FRS (usp + -192) [(usp + -192, objFR)] (acc - 6) m md ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md (st_obj 0x9b488 x9 (wz (oe_a e)) x24 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m).
Proof.
intros until A. intros Hj Hb HP0 JT Hacc Haw INV FS' FR'.
pose proof facts as (SPR & INp & Rfl & FL2 & FL8 & FL32 & FL3 & FC1 & KD & LOS' & _).
pose proof INV as (buf & cap & bpos & content & errv & B & HP & PB & CHm & _ & _ & _ & ST & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
apply Forall_inv in CHm. cbn [fst snd] in CHm. unfold objFR, savedR in CHm. cbn [app] in CHm.
unfold st_obj. unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl (@nil (Z * Z)) m) as MU.
stash INV.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. step. if_lit. step. step. step. fold_mkR.
evt_done5. unstash INV.
eapply (ser_litA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w LO HT CAP0 TXT NEED OBL_REALLOC_NF 0x23360 4 LIT_NULL) with (F := F) (e := acc - 6);
[ vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | lia | lia | lia
| exact INV | lia | lia | lia | clear - SPA; Z.div_mod_to_equations; lia | lia | lia | reflexivity | lia | reflexivity | exact FS' | exact FR' | ].
intros A3 m3 md3 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F3 fc3 INV3 FS3 FR3.
eapply (obj_nextA j e acc P); [exact Hj | exact Hb | exact HP0 | exact JT | exact Hacc | | exact FS3 | exact FR3].
replace (acc - 6 + 4) with (acc - 2) in INV3 by lia. exact INV3.
Qed.

Lemma obj_valA :
forall (pc0 : Z) (j : nat) (e : oent) (acc : Z) (P : list blk) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' m md A,
pc0 = 0x9b398 \/ pc0 = 0x9b484 ->
nth_error es j = Some e -> LEN - Z.of_nat j <= bound + 1 ->
pbtail P -> jtxk_obj (skipn j kids) (skipn j keyblks) (P ++ concat (skipn j KBS) ++ Y) acc = Some (w, R) -> 24 <= acc ->
ser_memx A FRS (usp + -192) [(usp + -192, objFR)] (acc + 6 * Z.of_nat (length (oe_ks e)) + 4) m md ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md (st_obj pc0 (wz (oe_k e)) (wz (oe_a e)) (wz (oe_v e)) x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m).
Proof.
intros until A. intros PCS Hj Hb HP0 JT Hacc INV FS' FR'.
pose proof facts as (SPR & INp & Rfl & FL2 & FL8 & FL32 & FL3 & FC1 & KD & LOS' & LESk & LKBS & INT).
pose proof (factsM _ _ _ _ _ _ INV) as (_ & _ & _ & _ & _ & _ & _ & KOKm).
destruct (entryM _ _ _ _ _ _ _ _ INV Hj) as (_ & _ & _ & _ & _ & _ & _ & CS & INk & KN).
pose proof INV as (buf & cap & bpos & content & errv & B & HP & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
destruct (key_stringA HIx _ _ _ _ _ _ _ (oe_k e) (oe_kn e) (oe_ks e) HP ltac:(right; right; exact INk) CS) as (_ & _ & _ & _ & _ & KLEN & _).
set (klen := Z.of_nat (length (oe_ks e))) in *.
assert (KW : 6 * klen + 14 <= key_w (oe_kn e)) by (unfold key_w; lia).
assert (Hkv : nth_error (map (fun e0 => (oe_k e0, oe_v e0)) es) j = Some (oe_k e, oe_v e)) by (rewrite nth_error_map, Hj; reflexivity).
assert (Hkb : nth_error keyblks j = Some (oe_k e, oe_kn e)) by (rewrite nth_error_map, Hj; reflexivity).
assert (Hjl : (j < length es)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
destruct (nth_error kids j) as [k|] eqn:NTHk; [| apply nth_error_None in NTHk; lia].
unfold st_obj. unfold usp in *.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl (@nil (Z * Z)) m) as MU.
destruct k as [s'|].
-
destruct (kids_okv_nth asegs A4F _ _ _ _ _ _ KOKm NTHk) as (kk & v & bs & Hv & Hbs & _).
rewrite Hkv in Hv. injection Hv as <- <-.
destruct (jtxk_obj_step_some asegs A4F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KOKm NTHk Hkv Hbs Hkb HP0 JT) as (Hvnz & JV & pbk & PBSk & RESTk & wi & P' & Ebs & JN & Hwi & Haw & JTXk & HP' & JT').
cbn [snd] in Haw, JT'.
assert (INk' : In (Some s') kids) by (eapply nth_error_In; exact NTHk).
assert (INCLk : incl RESTk LB).
{ intros bq Hbq. apply INCL. right. apply in_or_app. right. apply in_concat. exists bs. split; [eapply nth_error_In; exact Hbs | rewrite Ebs; apply in_or_app; left; exact Hbq]. }
pose proof (kdepth_in _ _ INk') as KDk.
destruct (jnode_hdr asegs A4F _ _ _ _ _ _ JN) as (n & ty & udel & ud & cs & rest & ER & Hn & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ (oe_v e) n HP ltac:(apply in_or_app; left; right; right; apply INCLk; rewrite ER; left; reflexivity)) as (_ & _ & Hvlo & Hvhi & _).
unfold_consts.
assert (TOKID : forall (x1_ t0_ t1_ t2_ a0_ a1_ a2_ a3_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ : word),
AJ5 A4L HIx A T md (MS (mkR x1_ (Z_to_bv 64 (bv_unsigned sp + -192)) gp (Z_to_bv 64 A_TP) t0_ t1_ t2_ (Z_to_bv 64 pb) (Z_to_bv 64 (oe_k e)) a0_ a1_ a2_ a3_ a4_ a5_ a6_ a7_
(Z_to_bv 64 fl) (Z_to_bv 64 (oe_a e)) (Z_to_bv 64 (lv + 1)) (Z_to_bv 64 0) (Z_to_bv 64 (Z.land fl 1)) (Z_to_bv 64 0x234c0) (Z_to_bv 64 (oe_v e))
(Z_to_bv 64 0) (Z_to_bv 64 2147450880) (Z_to_bv 64 0x234e0) t3_ t4_ t5_ t6_) F' (Z_to_bv 64 0x9b39c) fc' None m (seg_rom asegs))).
{ intros. eapply (kid_callO s' (oe_v e) pbk RESTk); [exact INV | exact JN | exact INCLk |].
eapply (ser_childA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w LO HT CAP0 TXT NEED JHEX0 (afn_of s') s' (KIDS s' INk')) with (F := F) (e := acc + 6 * klen + 4);
[ exact INV | exact JN | exact INCLk | exact JTXk | lia | lia | exact FL | lia | rewrite sdepth_obj in Hlvd; lia | exact FRSN
| unfold ser_budgetA, ASER_LEVEL, ASER_LEAF; lia | clear - SPA; Z.div_mod_to_equations; lia | lia | lia | reflexivity | lia | reflexivity | exact FS' | exact FR' | ].
intros A3 m3 md3 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F3 fc3 INV3 FS3 FR3.
eapply (obj_ret_kidA j e (acc + (key_w (oe_kn e) + wi)) P'); [exact Hj | exact Hb | exact HP' | exact JT' | lia | lia | | exact FS3 | exact FR3].
eapply ser_memA_weaken_e; [| exact INV3]. lia. }
stash INV. a4l. reenterA asegs A4L HIx asegs_wx HP.
destruct PCS as [-> | ->].
+ step. if_falsex. fold_mkR. evt_done5. apply TOKID.
+ step. if_truex. fold_mkR. evt_done5. apply TOKID.
-
destruct (jtxk_obj_step_none asegs A4F _ _ _ _ _ _ _ _ _ _ _ _ KOKm NTHk Hkb HP0 JT) as ((kk & Hv0) & Haw & JT').
rewrite Hkv in Hv0. injection Hv0 as _ Hv0. cbn [snd] in Haw, JT'.
assert (TONULL : forall (x1_ t0_ t1_ t2_ a0_ a1_ a2_ a3_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ : word),
AJ5 A4L HIx A T md (MS (mkR x1_ (Z_to_bv 64 (bv_unsigned sp + -192)) gp (Z_to_bv 64 A_TP) t0_ t1_ t2_ (Z_to_bv 64 pb) (Z_to_bv 64 (oe_k e)) a0_ a1_ a2_ a3_ a4_ a5_ a6_ a7_
(Z_to_bv 64 fl) (Z_to_bv 64 (oe_a e)) (Z_to_bv 64 (lv + 1)) (Z_to_bv 64 0) (Z_to_bv 64 (Z.land fl 1)) (Z_to_bv 64 0x234c0) (Z_to_bv 64 (oe_v e))
(Z_to_bv 64 0) (Z_to_bv 64 2147450880) (Z_to_bv 64 0x234e0) t3_ t4_ t5_ t6_) F' (Z_to_bv 64 0x9b488) fc' None m (seg_rom asegs))).
{ intros. eapply (obj_nullA j e (acc + (key_w (oe_kn e) + 4)) P); [exact Hj | exact Hb | exact HP0 | exact JT' | lia | lia | | exact FS' | exact FR'].
eapply ser_memA_weaken_e; [| exact INV]. lia. }
stash INV. a4l. reenterA asegs A4L HIx asegs_wx HP.
destruct PCS as [-> | ->].
+ step. if_rw Hv0 true. fold_mkR. evt_done5. apply TONULL.
+ step. if_rw Hv0 false. fold_mkR. evt_done5. apply TONULL.
Qed.

Lemma obj_keyA :
forall (j : nat) (e : oent) (acc : Z) (P : list blk) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' m md A,
nth_error es j = Some e -> LEN - Z.of_nat j <= bound + 1 ->
pbtail P -> jtxk_obj (skipn j kids) (skipn j keyblks) (P ++ concat (skipn j KBS) ++ Y) acc = Some (w, R) -> 24 <= acc ->
ser_memx A FRS (usp + -192) [(usp + -192, objFR)] acc m md ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md (st_obj 0x9b344 (wz (oe_k e)) (wz (oe_a e)) (wz (oe_v e)) x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m).
Proof.
intros until A. intros Hj Hb HP0 JT Hacc INV FS' FR'.
pose proof facts as (SPR & INp & Rfl & FL2 & FL8 & FL32 & FL3 & FC1 & KD & LOS' & LESk & LKBS & INT).
destruct (entryM _ _ _ _ _ _ _ _ INV Hj) as (_ & _ & _ & _ & _ & _ & _ & CS & INk & KN).
pose proof INV as (buf & cap & bpos & content & errv & B & HP & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
destruct (key_stringA HIx _ _ _ _ _ _ _ (oe_k e) (oe_kn e) (oe_ks e) HP ltac:(right; right; exact INk) CS) as (_ & _ & _ & _ & _ & KLEN & _).

assert (Hjl : (j < length es)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
assert (Hkb : nth_error keyblks j = Some (oe_k e, oe_kn e)) by (rewrite nth_error_map, Hj; reflexivity).
assert (KWW : acc + key_w (oe_kn e) <= w).
{ destruct (nth_error kids j) as [k|] eqn:NTHk; [| apply nth_error_None in NTHk; lia].
rewrite (skipn_nth_cons _ _ _ NTHk), (skipn_nth_cons _ _ _ Hkb) in JT. cbn [jtxk_obj] in JT. destruct k as [s'|].
- destruct (jtx s' _) as [[wi R1]|] eqn:E; [|discriminate]. pose proof (jtx_nonneg _ _ _ _ E).
pose proof (jtxk_obj_acc _ (fun s0' _ bs0 w0 r0 H0 => jtx_nonneg _ _ _ _ H0) _ _ _ _ _ JT). lia.
- pose proof (jtxk_obj_acc _ (fun s0' _ bs0 w0 r0 H0 => jtx_nonneg _ _ _ _ H0) _ _ _ _ _ JT). unfold NULL_W in *. lia. }
set (klen := Z.of_nat (length (oe_ks e))) in *.
assert (KW : 6 * klen + 14 <= key_w (oe_kn e)) by (unfold key_w; lia).
clear CS.
unfold st_obj. unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl (@nil (Z * Z)) m) as MU.
stash INV.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. if_lit.
step. step. step. step. fold_mkR.
evt_done5. unstash INV.
eapply (ser_litA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w LO HT CAP0 TXT NEED OBL_REALLOC_NF 0x234c0 1 LIT_QUOTE) with (F := F) (e := acc);
[ vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | lia | lia | lia
| exact INV | lia | lia | lia | clear - SPA; Z.div_mod_to_equations; lia | lia | lia | reflexivity | lia | reflexivity | exact FS' | exact FR' | ].
intros A1 m1 md1 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F1 fc1 INV1 FS1 FR1.
clear INV HP MI WM MU.

destruct (entryM _ _ _ _ _ _ _ _ INV1 Hj) as (_ & _ & _ & _ & _ & _ & _ & CS1 & _ & _).
pose proof INV1 as (buf1 & cap1 & bpos1 & content1 & errv1 & B1 & HP1 & _ & CHm & _ & _ & _ & ST1 & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1. cbn [hl_segs hla_base A4L A4H] in MI1.
assert (INkF : In (oe_k e, oe_kn e) ((pb, PB_SZ) :: (buf1, cap1) :: LB)) by (right; right; exact INk).
destruct (key_stringA HIx _ _ _ _ _ _ _ (oe_k e) (oe_kn e) (oe_ks e) HP1 INkF CS1) as (slack & STR & PAD & NN & UAL & UL & UPOS & UHI & USL).
clear CS1.
apply Forall_inv in CHm. cbn [fst snd] in CHm. unfold objFR, savedR in CHm. cbn [app] in CHm.
pose proof (wmono_refl asegs m1) as WM.
pose proof (munch_refl [(lo, bv_unsigned sp)] m1) as MU.
unfold_consts.
stash INV1.
a4l. reenterA asegs A4L HIx asegs_wx HP1.
step. step. fold_mkR.
eapply (astrlen_any_A HIx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 md1 A1 _ LM FRS B1 (oe_k e) (oe_kn e) (oe_k e) lo (oe_ks e) slack);
a4l_goal; rewrite ?unsigned_lit by lia;
first [exact HP1 | exact INkF | exact NN | exact STR | exact PAD | exact USL | exact ST1 | exact LO | exact MI1 | reflexivity | lia
| clear - SPA; Z.div_mod_to_equations; lia | idtac].
intros x0 x1' x2 y1' y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 m3 MU3 WM3 MI3 STR3 ST3.
stash STR3.
transport_after_call asegs m1 m3 MU3 WM3; try match goal with H : mem_inv asegs m1 |- _ => clear H end.
unstash STR3. unstash INV1.
rewrite ?unsigned_lit in ST3 by lia.
assert (INV3 : ser_memx A1 FRS (bv_unsigned sp + -192) [(bv_unsigned sp + -192, objFR)] (acc + 1) m3 md1).
{ eapply (ser_memA_stackW HIx sp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w HT); [exact INV1 | exact MU | exact WM | exact MI3 | | | | exact ST3 | lia].
- constructor; [cbn [fst snd]; split; lia | constructor].
- constructor; [exact CHm | constructor].
- constructor; [left; cbn [fst]; lia | constructor]. }
replace (ret_pc (Z_to_bv 64 635744)) with (Z_to_bv 64 635744) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
fold klen.
assert (Hkl31 : 0 <= klen < 2^31) by (unfold klen in *; lia).
step. step. step. step. step. fold_mkR.
assert (SRC3 : bytes_at asegs m3 (oe_k e) (oe_ks e)).
{ replace (oe_ks e ++ Z_to_bv 8 0 :: slack) with (oe_ks e ++ (Z_to_bv 8 0 :: slack)) in STR3 by reflexivity. apply bytes_at_app in STR3. exact (proj1 STR3). }
evt_done5.
eapply (ser_escapeA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w LO HT CAP0 TXT NEED JHEX0 ESC) with (F := F) (src := oe_ks e) (e := acc + 1) (sa := oe_k e) (sk := oe_kn e);
[ exact INV3 | exact INk | lia | fold klen; lia | exact SRC3 | reflexivity | fold klen; lia | lia | fold klen; lia
| exact FL | exact FRSN | unfold AESC_STACK; lia | clear - SPA; Z.div_mod_to_equations; lia
| lia | lia | reflexivity | lia | reflexivity | exact FS1 | exact FR1 | ].
intros A4 m4 md4 t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F4 fc4 INV4 FS4 FR4.
fold klen in INV4.
clear INV1 INV3 HP1 MI3 WM MU CHm ST3 STR3 SRC3 STR.
pose proof INV4 as (buf4 & cap4 & bpos4 & content4 & errv4 & B4 & HP4 & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI4. cbn [hl_segs hla_base A4L A4H] in MI4.
pose proof (wmono_refl asegs m4) as WM.
pose proof (munch_refl (@nil (Z * Z)) m4) as MU.
stash INV4.
a4l. reenterA asegs A4L HIx asegs_wx HP4.
step. step. step. step. fold_mkR.
evt_done5. unstash INV4.
eapply (ser_litA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w LO HT CAP0 TXT NEED OBL_REALLOC_NF 0x234c0 1 LIT_QUOTE) with (F := F) (e := acc + 1 + 6 * klen);
[ vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | lia | lia | lia
| exact INV4 | lia | lia | lia | clear - SPA; Z.div_mod_to_equations; lia | lia | lia | reflexivity | lia | reflexivity | exact FS4 | exact FR4 | ].
intros A5 m5 md5 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F5 fc5 INV5 FS5 FR5.
clear INV4 HP4 MI4 WM MU.
pose proof INV5 as (buf5 & cap5 & bpos5 & content5 & errv5 & B5 & HP5 & _ & CHm & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI5. cbn [hl_segs hla_base A4L A4H] in MI5.
apply Forall_inv in CHm. cbn [fst snd] in CHm. unfold objFR, savedR in CHm. cbn [app] in CHm.
pose proof (wmono_refl asegs m5) as WM.
pose proof (munch_refl (@nil (Z * Z)) m5) as MU.
stash INV5.
a4l. reenterA asegs A4L HIx asegs_wx HP5.
step.
destruct FC1 as [E1 | E1].
-
if_rw E1 true. step. step. step. step. fold_mkR.
evt_done5. unstash INV5.
eapply (ser_litA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w LO HT CAP0 TXT NEED OBL_REALLOC_NF 0x23520 1 LIT_COLON) with (F := F) (e := acc + 1 + 6 * klen + 1);
[ vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | lia | lia | lia
| exact INV5 | lia | lia | lia | clear - SPA; Z.div_mod_to_equations; lia | lia | lia | reflexivity | lia | reflexivity | exact FS5 | exact FR5 | ].
intros A6 m6 md6 v0 v1 v2 c0 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F6 fc6 INV6 FS6 FR6.
eapply (obj_valA 0x9b484 j e acc P); [right; reflexivity | exact Hj | exact Hb | exact HP0 | exact JT | exact Hacc | | exact FS6 | exact FR6].
fold klen. eapply ser_memA_weaken_e; [| exact INV6]. lia.
-
if_rw E1 false. step. step. step. step. fold_mkR.
evt_done5. unstash INV5.
eapply (ser_litA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w LO HT CAP0 TXT NEED OBL_REALLOC_NF 0x23500 2 LIT_COLON_SP) with (F := F) (e := acc + 1 + 6 * klen + 1);
[ vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | lia | lia | lia
| exact INV5 | lia | lia | lia | clear - SPA; Z.div_mod_to_equations; lia | lia | lia | reflexivity | lia | reflexivity | exact FS5 | exact FR5 | ].
intros A6 m6 md6 v0 v1 v2 c0 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F6 fc6 INV6 FS6 FR6.
eapply (obj_valA 0x9b398 j e acc P); [left; reflexivity | exact Hj | exact Hb | exact HP0 | exact JT | exact Hacc | | exact FS6 | exact FR6].
fold klen. eapply ser_memA_weaken_e; [| exact INV6]. lia.
Qed.

Lemma obj_sepA :
forall (j : nat) (e : oent) (acc : Z) (P : list blk) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' m md A,
nth_error es j = Some e -> LEN - Z.of_nat j <= bound + 1 ->
pbtail P -> jtxk_obj (skipn j kids) (skipn j keyblks) (P ++ concat (skipn j KBS) ++ Y) acc = Some (w, R) -> 24 <= acc ->
ser_memx A FRS (usp + -192) [(usp + -192, objFR)] (acc - 1) m md ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md (st_obj 0x9b32c (wz (oe_k e)) (wz (oe_a e)) (wz (oe_v e)) x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m).
Proof.
intros until A. intros Hj Hb HP0 JT Hacc INV FS' FR'.
pose proof facts as (SPR & INp & Rfl & FL2 & FL8 & FL32 & FL3 & FC1 & KD & LOS' & LESk & LKBS & INT).
assert (Hjl : (j < length es)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
assert (Hkb : nth_error keyblks j = Some (oe_k e, oe_kn e)) by (rewrite nth_error_map, Hj; reflexivity).
assert (KWW : acc + key_w (oe_kn e) <= w).
{ destruct (nth_error kids j) as [k|] eqn:NTHk; [| apply nth_error_None in NTHk; lia].
rewrite (skipn_nth_cons _ _ _ NTHk), (skipn_nth_cons _ _ _ Hkb) in JT. cbn [jtxk_obj] in JT. destruct k as [s'|].
- destruct (jtx s' _) as [[wi R1]|] eqn:E; [|discriminate]. pose proof (jtx_nonneg _ _ _ _ E).
pose proof (jtxk_obj_acc _ (fun s0' _ bs0 w0 r0 H0 => jtx_nonneg _ _ _ _ H0) _ _ _ _ _ JT). lia.
- pose proof (jtxk_obj_acc _ (fun s0' _ bs0 w0 r0 H0 => jtx_nonneg _ _ _ _ H0) _ _ _ _ _ JT). unfold NULL_W in *. lia. }
assert (KW : 14 <= key_w (oe_kn e)) by (unfold key_w; lia).
pose proof INV as (buf & cap & bpos & content & errv & B & HP & _ & CHm & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
apply Forall_inv in CHm. cbn [fst snd] in CHm. unfold objFR, savedR in CHm. cbn [app] in CHm.
unfold st_obj. unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl (@nil (Z * Z)) m) as MU.
stash INV.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. if_lit.
step.
destruct FC1 as [E1 | E1].
- if_rw E1 true. fold_mkR. evt_done5. unstash INV.
eapply (obj_keyA j e acc P); [exact Hj | exact Hb | exact HP0 | exact JT | exact Hacc | | exact FS' | exact FR'].
eapply ser_memA_weaken_e; [| exact INV]. lia.
- if_rw E1 false. step. step. step. step. fold_mkR.
evt_done5. unstash INV.
eapply (ser_litA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w LO HT CAP0 TXT NEED OBL_REALLOC_NF 0x23480 1 LIT_SPACE) with (F := F) (e := acc - 1);
[ vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | lia | lia | lia
| exact INV | lia | lia | lia | clear - SPA; Z.div_mod_to_equations; lia | lia | lia | reflexivity | lia | reflexivity | exact FS' | exact FR' | ].
intros A3 m3 md3 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F3 fc3 INV3 FS3 FR3.
eapply (obj_keyA j e acc P); [exact Hj | exact Hb | exact HP0 | exact JT | exact Hacc | | exact FS3 | exact FR3].
replace (acc - 1 + 1) with acc in INV3 by lia. exact INV3.
Qed.

Lemma obj_iter : loopK (bound + 1).
Proof.
unfold loopK. intros until A. intros Hj Hb Hf HP0 JT Hacc INV FS' FR'.
pose proof facts as (SPR & INp & Rfl & FL2 & FL8 & FL32 & FL3 & FC1 & KD & LOS' & LESk & LKBS & INT).
destruct (entryM _ _ _ _ _ _ _ _ INV Hj) as (Ha0 & Hah & Ha8 & (pad & ENT) & SHe0 & SHe2 & SHe3 & _ & _ & _).
assert (Hjl : (j < length es)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
assert (Hkb : nth_error keyblks j = Some (oe_k e, oe_kn e)) by (rewrite nth_error_map, Hj; reflexivity).
assert (KWW : acc + key_w (oe_kn e) <= w).
{ destruct (nth_error kids j) as [k|] eqn:NTHk; [| apply nth_error_None in NTHk; lia].
rewrite (skipn_nth_cons _ _ _ NTHk), (skipn_nth_cons _ _ _ Hkb) in JT. cbn [jtxk_obj] in JT. destruct k as [s'|].
- destruct (jtx s' _) as [[wi R1]|] eqn:E; [|discriminate]. pose proof (jtx_nonneg _ _ _ _ E).
pose proof (jtxk_obj_acc _ (fun s0' _ bs0 w0 r0 H0 => jtx_nonneg _ _ _ _ H0) _ _ _ _ _ JT). lia.
- pose proof (jtxk_obj_acc _ (fun s0' _ bs0 w0 r0 H0 => jtx_nonneg _ _ _ _ H0) _ _ _ _ _ JT). unfold NULL_W in *. lia. }
assert (KW : 14 <= key_w (oe_kn e)) by (unfold key_w; lia).
pose proof INV as (buf & cap & bpos & content & errv & B & HP & _ & CHm & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
apply Forall_inv in CHm. cbn [fst snd] in CHm. unfold objFR, savedR in CHm. cbn [app] in CHm.
unfold st_obj. unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl (@nil (Z * Z)) m) as MU.
stash INV.
a4l. reenterA asegs A4L HIx asegs_wx HP.
asan_chk0.
step. asan_chkA.
step. step. step.
step.
destruct Hf as [-> | ->].
-
if_lit. step. step. step. step. fold_mkR.
evt_done5. unstash INV.
eapply (ser_litA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w LO HT CAP0 TXT NEED OBL_REALLOC_NF 0x23440 1 LIT_COMMA) with (F := F) (e := acc - 2);
[ vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | lia | lia | lia
| exact INV | lia | lia | lia | clear - SPA; Z.div_mod_to_equations; lia | lia | lia | reflexivity | lia | reflexivity | exact FS' | exact FR' | ].
intros A3 m3 md3 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F3 fc3 INV3 FS3 FR3.
eapply (obj_sepA j e acc P); [exact Hj | exact Hb | exact HP0 | exact JT | exact Hacc | | exact FS3 | exact FR3].
replace (acc - 2 + 1) with (acc - 1) in INV3 by lia. exact INV3.
-
if_lit. fold_mkR. evt_done5. unstash INV.
eapply (obj_sepA j e acc P); [exact Hj | exact Hb | exact HP0 | exact JT | exact Hacc | | exact FS' | exact FR'].
eapply ser_memA_weaken_e; [| exact INV]. lia.
Qed.
End Iter.

Lemma obj_loop : forall n, loopK (Z.of_nat n).
Proof.
induction n as [|n IH].
- unfold loopK. intros until A. intros Hj Hb. assert ((j < length es)%nat) by (apply nth_error_Some; rewrite Hj; discriminate). unfold LEN in *. lia.
- replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia. apply obj_iter. exact IH.
Qed.

Lemma obj_startA :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x21 x22 x23 x24 x25 x27 t3 t4 t5 t6 : word) (j88 : list byte) F' fc' m md A,
ser_memx A FRS (usp + -192) [(usp + -192, [CB 88 j88] ++ savedR)] 1 m md ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md
(MS (mkR x1 (wz (usp + -192)) gp (wz A_TP) t0 t1 t2 (wz pb) (wz p) a0 a1 a2 a3 a4 a5 a6 a7
(wz fl) x19 (wz lv) x21 x22 x23 x24 x25 (wz 2147450880) x27 t3 t4 t5 t6)
F' (wz 0x9b20c) fc' None m (seg_rom asegs)).
Proof.
intros until A. intros INV FS' FR'.
pose proof facts as (SPR & INp & Rfl & FL2 & FL8 & FL32 & FL3 & FC1 & KD & LOS' & LESk & LKBS & INT).
pose proof (factsM _ _ _ _ _ _ INV) as (Hp0 & Hph & Hp8 & NODE & SH0 & SH5 & (_ & HEAD & _) & _).
pose proof INV as (buf & cap & bpos & content & errv & B & HP & _ & CHm & _ & _ & _ & ST & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
assert (INt : In (t, 56) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; apply INT; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ t 56 HP ltac:(apply in_or_app; left; exact INt)) as (_ & Htal & Htlo & Hthi & _).
pose proof (blk_granS HIx _ _ _ _ _ _ _ t 56 1 HP INt ltac:(lia) ltac:(lia)) as SHt1.
replace (t / 8 + 2147450880 + 1) with (t / 8 + 2147450881) in SHt1 by lia.
apply Forall_inv in CHm. cbn [fst snd] in CHm. unfold savedR in CHm. cbn [app] in CHm.
unfold jhdr_cells in NODE. cbn [app] in NODE.
assert (Hw3 : 24 <= w) by (eapply jtxk_obj_acc; [intros s0' _ bs0 w0 r0 H0; exact (jtx_nonneg _ _ _ _ H0) | exact JTX]).
assert (Hlv1 : lv <= 999) by (rewrite sdepth_obj in Hlvd; lia).
unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -192, bv_unsigned sp)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
asan_chk0.
step. asan_chkA.
step. step. asan_chkA.
step. step.
pose proof (ohd_skipn es 0) as OH. change (skipn 0 es) with es in OH. rewrite OH. clear OH.
destruct (nth_error es 0) as [e0|] eqn:Hj0.
- destruct (entryM _ _ _ _ _ _ _ _ INV Hj0) as (Ha0 & Hah & _).
unfold_consts.
if_falsex.
step. rewrite (unsigned_lit fl) by lia. rewrite FL2.
step. rewrite (unsigned_lit fl) by lia.
step.
step. norm_w32.
step. rewrite (unsigned_lit fl) by lia. rewrite FL8.
stepz.
step. rewrite (unsigned_lit fl) by lia. rewrite FL32.
step. do 10 step.
step. norm_w32.
rewrite (Z.shiftl_mul_pow2 (lv + 1) 1) by lia. change (2^1) with 2. rewrite (swrap32_id ((lv + 1) * 2)) by lia. replace ((lv + 1) * 2) with (2 * (lv + 1)) by lia.
step.
step. stepz. step. step. stepz. step. stepz. step. stepz. step. step. stepz. step. stepz. step. stepz. step. stepz.
fold_mkR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
match goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
assert (INV3 : ser_memx A FRS (bv_unsigned sp + -192) [(bv_unsigned sp + -192, objFR)] 1 m3 md).
{ eapply (ser_memA_stackW HIx sp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w HT); [exact INV | exact MU | exact WM | exact MI3 | | | | exact ST | lia].
- constructor; [cbn [fst snd]; split; lia | constructor].
- constructor; [exact CHm | constructor].
- constructor; [left; cbn [fst]; lia | constructor]. }
evt_done5.
pose proof (obj_loop (length es)) as LK. unfold loopK, st_obj in LK.
eapply (LK 0%nat e0 1 24 []); [exact Hj0 | unfold LEN; lia | right; reflexivity | exact pbtail_nil | exact JTX | lia | | exact FS' | exact FR'].
eapply ser_memA_weaken_e; [| exact INV3]. lia.
-
if_lit. fold_mkR. evt_done5.
eapply obj_closeA with (e := 1) (PRE := [CB 88 j88]); [exact INV | reflexivity | lia | lia | exact FS' | exact FR'].
Qed.
End Obj.

Section Top.
Variable HIx : heap_iface_A A4L.
Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.
Hypothesis ESC : esc_specA HIx.

Theorem ser_objA : forall kids, (forall s', In (Some s') kids -> ser_specA HIx (afn_of s') s') -> ser_specA HIx ASER_OBJ (Sobj kids).
Proof.
intros kids KIDS. unfold ser_specA. intros until errv. intros HP PB JN INCL JTX CAP TXT NEED FL Hlv Hlvd FRSN ST LO LOS SPA HT ERR JHX TP' RA FRM A0 A1 A2 A3 K.
destruct JN as (t & TBS & kvs & KBS & EREST & NODE & LT & L1 & L2 & KOK).
assert (POS : forall a n, In (a, n) TBS -> 0 < a /\ a mod 16 = 0).
{ intros a n Hin. pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a n HP ltac:(apply in_or_app; left; right; right; apply INCL; rewrite EREST; right; apply in_or_app; left; exact Hin)) as (_ & Hal & Hlo & _). split; assumption. }
destruct (lhtab_otab asegs A4F _ _ _ _ LT POS) as (es & OT & Ekvs & tbl & size & ETBS).
subst a0 a1 a2 a3 tp REST kvs TBS.
cbn [app] in JTX. rewrite jtx_obj_eq in JTX. cbn [snd] in JTX. change (48 =? 48) with true in JTX. change (56 =? 56) with true in JTX. cbn [andb] in JTX.
rewrite length_map in L1.
assert (LK : length (map (fun e => (oe_k e, oe_kn e)) es) = length kids) by (rewrite length_map; exact L1).
match type of JTX with context [(?x <=? ?y)%nat] => destruct (Nat.leb_spec x y) as [_|GT]; [| exfalso; rewrite !length_app, length_map in GT; clear - GT L1; lia] end.
rewrite <- app_assoc in JTX. rewrite (firstn_app_exact _ _ _ LK), (skipn_app_exact _ _ _ LK) in JTX.
pose proof NODE as NODE0. pose proof JHX as JHX0.
assert (LOS0 : lo <= bv_unsigned sp - 192 - 4096 - 112) by (unfold ser_budgetA, ASER_LEVEL, ASER_LEAF in LOS; rewrite sdepth_obj in LOS; pose proof (kdepth_nonneg kids); lia).
stash NODE0. stash JHX0. stash OT. stash KOK. stash LOS. stash POS.
word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ pb PB_SZ HP ltac:(apply in_or_app; left; left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(apply in_or_app; left; right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
unfold ASER_OBJ. unfold_consts.
pose proof PB as (Hbp & Hcap & Hlen & PBS & PBUF).
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 192, bv_unsigned sp)] m) as MU.
pose proof alloc_ceiling_range as ACR.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 192%nat ST.
do 14 step. do 3 step. do 3 step. step. do 4 step. step. fold_mkR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
lazymatch type of FR with rw_cells _ _ _ ?frc =>
assert (INV1 : ser_memA HIx sp m md LB LM FRS B pb lo bpos cap w A FRS (bv_unsigned sp + -192) [(bv_unsigned sp + -192, frc)] 0 m1 md) end.
{ exists buf, cap, bpos, content, errv, B.
split; [heap_nowA A4L HIx HP MU WM MI1|].
split; [split; [lia|]; split; [lia|]; split; [exact Hlen|]; split; [exact PBS | exact PBUF]|].
split; [constructor; [exact FR | constructor]|].
split; [constructor; [left; cbn [fst]; lia | constructor]|].
split; [intros bb Hbb; exact Hbb|].
split; [exact ERR|]. split; [exact ST|].
split. { eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros bb Hbb; apply in_app_or in Hbb; apply in_or_app; destruct Hbb as [Hbb|Hbb]; [left; right; right; exact Hbb | right; exact Hbb] | lia | solve_clientWA A4L HIx HP]. }
split; [apply model_vm_only_refl|].
split; [lia|]. split; [unfold ser_capb; lia|]. split; lia. }
assert (Hw3 : 24 <= w) by (eapply jtxk_obj_acc; [intros s0' _ bs0 w0 r0 H0; exact (jtx_nonneg _ _ _ _ H0) | exact JTX]).
evt_done5.
eapply (ser_litA HIx sp gp m md LB LM FRS B pb lo bpos cap w LO HT CAP TXT NEED OBL_REALLOC_NF 0x23420 1 LIT_LBRACE) with (F := F) (e := 0);
[ vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | lia | lia | lia
| exact INV1 | lia | lia | lia | clear - SPA; Z.div_mod_to_equations; lia | lia | lia | reflexivity | lia | reflexivity | apply fsaved_refl | exact FRM | ].
intros A3 m3 md3 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F3 fc3 INV3 FS3 FR3.
unstash NODE0. unstash JHX0. unstash OT. unstash KOK. unstash LOS.
lazymatch type of INV3 with context [[(_, [CB 88 ?jj; _; _; _; _; _; _; _; _; _; _; _; _; _])]] =>
eapply (obj_startA HIx OBL_REALLOC_NF ESC ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B pb lo p rc pb0 lv fl t tbl size bpos cap w
es KBS kids T Y R KIDS FL Hlv Hlvd LO LOS SPA HT RA CAP TXT NEED JHX0 FRSN INCL NODE0 OT KOK JTX K
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ jj); [exact INV3 | exact FS3 | exact FR3] end.
Qed.
End Top.
End RC__1.
End Mq8.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI QRBl QSHS QupI QC6R.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq9.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun QWxq_c1.Mq0 Qfw3_c1.Mq2 Qc3B.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn.
Import QYIF.
Import QgoP.
Import QbFI QXUB. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QsKa.Mqe QsKa.Mqd QlKV.Mqf Q9O6.Mq4 Qekr QlKV.Mqj QsKa.Mq9 QJZd.Mq9 QsKa.Mqh Qw5U.Mq5.

Import QsKa.Mqf.

Import QlKV.Mq2.
Import QupI.
Import QC6R Qw5U.Mq6 Ql4f.Mq3.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac QlEo_c1.solve_load ::= QrJ1.mkr__solve_load_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition SHB0 : list byte := map (Z_to_bv 8)
([0xf1;0xf1;0xf1;0xf1; 0;0;0xf2;0xf2; 0xf8;0xf8;0xf8;0xf2; 0xf2;0xf2;0xf2;0xf2; 0xf8;0xf8;0xf8;0xf2; 0xf2;0xf2;0xf2;0xf2; 0xf8;0xf8;0xf8;0xf2; 0xf2;0xf2;0xf2;0xf2; 0xf8;0xf3;0xf3;0xf3]
++ repeat 0 28).
Lemma fr_size_3 : fr_size 3 = 512. Proof. reflexivity. Qed.
Lemma fr_shadow_len_3 : fr_shadow_len 3 = 64. Proof. reflexivity. Qed.

Lemma unpoisoned_of_fshadow3 : forall m Fr (shb : list byte) (g0 g1 : nat),
bytes_at asegs m (Fr / 8 + A_SB) shb -> length shb = 64%nat -> Fr mod 512 = 0 -> 0 <= Fr ->
(g0 < g1)%nat -> (g1 <= 64)%nat ->
forallb (fun b => bv_unsigned b =? 0) (firstn (g1 - g0) (skipn g0 shb)) = true ->
unpoisoned asegs m A_SB (Fr + 8 * Z.of_nat g0) (8 * Z.of_nat (g1 - g0)).
Proof.
intros m Fr shb g0 g1 SH L AL F0 Hg Hg1 Z0.
assert (GZ : forall g : nat, (g0 <= g < g1)%nat -> bytes_at asegs m (Fr / 8 + A_SB + Z.of_nat g) [Z_to_bv 8 0]).
{ intros g Hgg. pose proof (Ql4f.Mq3.bytes_at_sub asegs m _ shb g 1 SH ltac:(lia)) as X.
assert (E : firstn 1 (skipn g shb) = [Z_to_bv 8 0]); [| rewrite E in X; exact X].
rewrite forallb_forall in Z0.
destruct (nth_error shb g) as [b|] eqn:Hb; [| apply nth_error_None in Hb; lia].
assert (Hin : In b (firstn (g1 - g0) (skipn g0 shb))).
{ apply (nth_error_In _ (g - g0)). rewrite nth_error_firstn. destruct (Nat.ltb_spec (g - g0) (g1 - g0)); [| lia]. rewrite nth_error_skipn. replace (g0 + (g - g0))%nat with g by lia. exact Hb. }
specialize (Z0 b Hin). apply Z.eqb_eq in Z0.
pose proof (@nth_error_split _ shb g b Hb) as (l1 & l2 & E & Hl1). rewrite E. rewrite <- Hl1, skipn_app, skipn_all, Nat.sub_diag. cbn. f_equal. apply bv_eq. rewrite Z0. reflexivity. }
assert (E1 : (Fr + 8 * Z.of_nat g0) / 8 = Fr / 8 + Z.of_nat g0) by (Z.div_mod_to_equations; lia).
assert (E2 : (Fr + 8 * Z.of_nat g0 + 8 * Z.of_nat (g1 - g0) - 1) / 8 = Fr / 8 + Z.of_nat g1 - 1) by (Z.div_mod_to_equations; lia).
unfold unpoisoned. split; [lia|]. split; [| split].
- intros g Hgr. rewrite E1, E2 in Hgr. replace (g + A_SB) with (Fr / 8 + A_SB + Z.of_nat (Z.to_nat (g - Fr / 8))) by lia. apply GZ. lia.
- exists 0. split; [| left; reflexivity]. rewrite E2. replace (Fr / 8 + Z.of_nat g1 - 1 + A_SB) with (Fr / 8 + A_SB + Z.of_nat (g1 - 1)) by lia. apply GZ. lia.
- intros w Hw. rewrite E1, E2 in Hw.
assert (EW : exists j : nat, (j < 8)%nat /\ w * 8 = Fr / 8 + A_SB + Z.of_nat (8 * j)).
{ exists (Z.to_nat (w - (Fr / 8 + A_SB) / 8)). unfold A_SB in *. split; Z.div_mod_to_equations; lia. }
destruct EW as (j & Hj & ->). exists (firstn 8 (skipn (8 * j) shb)). split.
+ rewrite firstn_length_le; [reflexivity | rewrite length_skipn; lia].
+ apply Ql4f.Mq3.bytes_at_sub; [exact SH | lia].
Qed.

Section AHarnJo1.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Lemma window_bytesG : forall (LBa : list blk) (data0 size : Z) m m' ptr rem data,
(size = 0 \/ In (data0, size) LBa) ->
bytes_at asegs m ptr data -> Z.of_nat (length data) = rem -> data0 <= ptr -> ptr + rem <= data0 + size ->
(forall a, 0 <= a < 2^64 -> in_block LBa a -> m' (wa a) = m (wa a)) ->
bytes_at asegs m' ptr data.
Proof.
intros LBa data0 size m m' ptr rem data INB B L P1 P2 E.
destruct INB as [Z0 | INB'].
- assert (data = []) as -> by (destruct data; [reflexivity | cbn in L; lia]).
destruct B as (B0' & B1 & _). split; [exact B0'|]. split; [exact B1|]. intros i Hi. cbn in Hi. lia.
- destruct B as (B0' & B1 & BB). split; [exact B0'|]. split; [exact B1|].
intros i Hi. rewrite <- (BB i Hi). unfold mrd. rewrite (E (ptr + Z.of_nat i)); [reflexivity | lia |].
exists (data0, size). split; [exact INB' | cbn; lia].
Qed.

Lemma cells_size_C1 : forall l : list byte, cells_size (map C1 l) = length l.
Proof. induction l as [|b l IH]; [reflexivity | cbn [map cells_size csize]; rewrite IH; reflexivity]. Qed.

Lemma GA_jo_pointwise : forall m m', GA_jo m -> lh_globA m' -> (forall a, 0xec920 <= a < 0xec948 -> m' (wa a) = m (wa a)) -> GA_jo m'.
Proof.
intros m m' (G1 & G2 & G3) L E. split; [exact L|]. split.
- unfold jhex_A in *. eapply bytes_at_pointwiseA; [exact G2|]. intros a Ha. rewrite length_le8 in Ha. apply E. lia.
- unfold utf8rep_A in *. eapply bytes_at_pointwiseA; [exact G3|]. intros a Ha. cbn [length] in Ha. apply E. lia.
Qed.
Lemma GA_jo_munch : forall m m' W, GA_jo m -> munch W m m' -> wmono asegs m m' -> Forall (fun iv : Z * Z => snd iv <= 0xec920 \/ 0xec988 <= fst iv) W -> GA_jo m'.
Proof.
intros m m' W G MU WM HW. eapply GA_jo_pointwise; [exact G | |].
- eapply lh_globA_frame; [exact (proj1 G) | exact MU | exact WM |]. eapply Forall_impl; [| exact HW]. intros [a b] H. cbn [fst snd] in *. unfold GHASHA, GSEEDA. lia.
- intros a Ha. apply MU. rewrite wa_unsigned by lia. clear - HW Ha. induction W as [|[u v] W IH]; cbn [outside]; [exact I|].
apply Forall_cons_iff in HW as [H HW]. cbn [fst snd] in H. split; [lia | apply IH; exact HW].
Qed.
Lemma GA_jo_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA_jo m -> GA_jo m'.
Proof.
intros LB SP m m' HPR G. eapply GA_jo_pointwise; [exact G | exact (lh_globA_client _ _ _ _ HPR (proj1 G)) |].
intros a Ha. apply (HPR a); [lia|]. right; left. cbn [hl_client_static A4H]. unfold a4_client_static. lia.
Qed.

Section Ctx.

Variables (sp0 : word) (sp1 lo Fr : Z) (LB0 LM : list blk) (m0 : word -> option byte) (md0 : config) (F0 : bvmap 5 word) (B0 : bud).
Variables (data0 size : Z) (payload : list byte).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= sp1 - (2^20 - 144).
Hypothesis SPA1 : sp1 mod 32 = 0.
Hypothesis SP10 : sp1 + 96 <= bv_unsigned sp0.
Hypothesis HT : bv_unsigned sp0 + 32 <= hiA_top A4L HIx.
Hypothesis HBOT : hiA_bot A4L HIx <= lo.
Hypothesis PLEN : Z.of_nat (length payload) = size.
Hypothesis SZ : 0 <= size < 2^26.
Hypothesis D0 : 0 < data0.
Hypothesis DCE : data0 + size <= alloc_ceiling.
Hypothesis INB : size = 0 \/ In (data0, size) LB0.

Hypothesis FRAL : Fr mod 512 = 0.
Hypothesis FRLO : 6582272 <= Fr.
Hypothesis FRHI : Fr + 512 <= alloc_ceiling.
Hypothesis FRAPP : Fr + 512 + 8 <= A_SB \/ A_HMB <= Fr.

Collection CtxAll := RC__ HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP.

Notation XT := (xtgt_A (bv_unsigned sp0)).

Definition HINVA (shb : list byte) (m : word -> option byte) (md : config) (F : bvmap 5 word) (fc : bv 32) (ptr rem : Z) (data : list byte) : Prop :=
heap_presx A4H XT (LB0 ++ LM) (sp1 + 8) m0 m /\
model_vm_only (cfg_model md0) (cfg_model md) /\ fsaved F0 F /\ frm0 fc /\
rw_cells asegs m T_LOCCELL_A [C8 (Z_to_bv 64 T_GLOBLOC_A)] /\ rw_cells asegs m T_LOCALE_LOCK_A [C4 (Z_to_bv 64 0)] /\ GA_jo m /\
stk asegs m lo sp1 /\
rw_cells asegs m sp1 [C8 (Z_to_bv 64 Fr)] /\
rw_cells asegs m (Fr + 32) [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 rem)] /\
(exists fj0 fj1, rw_cells asegs m Fr [CB 32 fj0] /\ rw_cells asegs m (Fr + 48) [CB 456 fj1]) /\
rw_cells asegs m (Fr / 8 + 2147450880) (map C1 shb) /\ length shb = 64%nat /\
bytes_at asegs m ptr data /\ Z.of_nat (length data) = rem /\ 0 < ptr /\ data0 <= ptr /\ ptr + rem <= data0 + size.

#[using="CtxAll"] Lemma HINVA_call : forall shb m m' md md' F F' fc fc' ptr rem data LBx,
HINVA shb m md F fc ptr rem data ->
heap_pres A4H (LBx ++ LM ++ fr_ivs A4L [(Fr, 3)]) sp1 m m' -> incl LB0 LBx ->
model_vm_only (cfg_model md) (cfg_model md') -> fsaved F F' -> frm0 fc' ->
stk asegs m' lo sp1 ->
HINVA shb m' md' F' fc' ptr rem data.
Proof.
intros shb m m' md md' F F' fc fc' ptr rem data LBx
(PX & VM & FS & FRM & LOC & LCK & G & ST & SL & FD & (fj0 & fj1 & FF0 & FF1) & FSH & LSH & BY & L & P0 & P1 & P2) HPR Hi VM' FS' FRM' ST'.
assert (INF : In (Fr, 3) [(Fr, 3)]) by (left; reflexivity).
assert (SUB : forall b, In b (LB0 ++ LM) -> In b (LBx ++ LM ++ fr_ivs A4L [(Fr, 3)])).
{ intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply Hi; exact Hb | right; apply in_or_app; left; exact Hb]. }
assert (INBm : forall a, 0 <= a < 2^64 -> in_block LB0 a -> m' (wa a) = m (wa a)).
{ intros a Ha (b & Hb & Hr). apply (HPR a Ha). right; right. exists b. split; [apply in_or_app; left; apply Hi; exact Hb | exact Hr]. }
assert (LOCcs : forall a, 6444320 - 48 <= a < 6444320 - 48 + 8 -> hl_client_static A4H a) by (intros a Ha; cbn [hl_client_static A4H]; unfold a4_client_static; lia).
assert (LCKcs : forall a, 0x645890 <= a < 0x645890 + 4 -> hl_client_static A4H a) by (intros a Ha; cbn [hl_client_static A4H]; unfold a4_client_static; lia).
split. { eapply heap_presx_trans; [exact PX|]. apply heap_pres_presx. eapply heap_pres_weaken; [exact HPR | lia | exact SUB]. }
split. { eapply model_vm_only_trans; [exact VM | exact VM']. }
split. { eapply fsaved_trans; [exact FS | exact FS']. }
split. { exact FRM'. }
split. { eapply (heap_pres_rw_cells A4H); [exact HPR | exact LOC |]. right; left. cbn. intros z Hz. apply LOCcs. unfold T_LOCCELL_A, A_TP in Hz. lia. }
split. { eapply (heap_pres_rw_cells A4H); [exact HPR | exact LCK |]. right; left. cbn. intros z Hz. apply LCKcs. unfold T_LOCALE_LOCK_A in Hz. lia. }
split. { exact (GA_jo_pres _ _ _ _ HPR G). }
split. { exact ST'. }
split. { eapply (heap_pres_rw_cells A4H); [exact HPR | exact SL |]. left. lia. }
split. { eapply (heap_pres_rw_cells A4H); [exact HPR | exact FD |].
eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; apply (QSHS.fr_ivs_frame _ _ _ INF) | lia | cbn; rewrite fr_size_3; lia]. }
split. { exists fj0, fj1. split.
- eapply (heap_pres_rw_cells A4H); [exact HPR | exact FF0 |].
eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; apply (QSHS.fr_ivs_frame _ _ _ INF) | lia | cbn; rewrite fr_size_3; lia].
- eapply (heap_pres_rw_cells A4H); [exact HPR | exact FF1 |].
eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; apply (QSHS.fr_ivs_frame _ _ _ INF) | lia | cbn; rewrite fr_size_3; lia]. }
split. { eapply (heap_pres_rw_cells A4H); [exact HPR | exact FSH |].
eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; apply (QSHS.fr_ivs_shadow _ _ _ INF) | unfold shad; cbn [hl_sb A4L]; unfold A_SB; lia | rewrite cells_size_C1, LSH; cbn [blk_addr blk_size fst snd]; rewrite fr_shadow_len_3; unfold shad; cbn [hl_sb A4L]; unfold A_SB; lia]. }
split. { exact LSH. }
split. { eapply (window_bytesG LB0 data0 size); [exact INB | exact BY | exact L | exact P1 | exact P2 | exact INBm]. }
repeat split; assumption.
Qed.
Lemma cells_bytes_C1 : forall l : list byte, cells_bytes (map C1 l) = l.
Proof. induction l as [|b l IH]; [reflexivity | cbn [map cells_bytes cbytes app]; rewrite IH; reflexivity]. Qed.

#[using="CtxAll"] Lemma fdp_evidenceA : forall A LBx B m md (shb : list byte) ptr rem,
HEAPAx A LBx LM [(Fr, 3)] B m md -> incl LB0 LBx ->
rw_cells asegs m (Fr / 8 + 2147450880) (map C1 shb) -> length shb = 64%nat -> forallb (fun b => bv_unsigned b =? 0) (firstn 2 (skipn 4 shb)) = true ->
data0 <= ptr -> ptr + rem <= data0 + size ->
asan_rt_ok m /\ unpoisoned asegs m A_SB (Fr + 32) 16 /\ (0 < rem -> unpoisoned asegs m A_SB ptr rem).
Proof.
intros A LBx B m md shb ptr rem HP Hi FSH L Z45 P1 P2. pose proof alloc_ceiling_range as ACR. pose proof (hiA_top_le A4L HIx) as HT47.
split; [exact (asan_rt_ok_of_HEAPA HIx _ _ _ _ _ _ _ HP)|]. split.
- pose proof (rw_cells_bytes_at asegs _ _ _ FSH) as SB. rewrite cells_bytes_C1 in SB.
pose proof (unpoisoned_of_fshadow3 m Fr shb 4 6 ltac:(unfold A_SB; exact SB) L FRAL ltac:(lia) ltac:(lia) ltac:(lia) Z45) as U.
change (Fr + 8 * Z.of_nat 4) with (Fr + 32) in U. change (8 * Z.of_nat (6 - 4)) with 16 in U. exact U.
- intros Hr. destruct INB as [Z0 | INB']; [lia|].
eapply (unpoisoned_of_blk HIx _ _ _ _ _ _ _ data0 size ptr rem HP (Hi _ INB')); lia.
Qed.

#[using="CtxAll"] Lemma fslot_evidenceA : forall m (shb : list byte) (g0 g1 : nat),
rw_cells asegs m (Fr / 8 + 2147450880) (map C1 shb) -> length shb = 64%nat -> (g0 < g1)%nat -> (g1 <= 64)%nat ->
forallb (fun b => bv_unsigned b =? 0) (firstn (g1 - g0) (skipn g0 shb)) = true ->
unpoisoned asegs m A_SB (Fr + 8 * Z.of_nat g0) (8 * Z.of_nat (g1 - g0)).
Proof.
intros m shb g0 g1 FSH L Hg Hg1 Z0. pose proof (rw_cells_bytes_at asegs _ _ _ FSH) as SB. rewrite cells_bytes_C1 in SB.
eapply (unpoisoned_of_fshadow3 m Fr shb g0 g1); [unfold A_SB; exact SB | exact L | exact FRAL | lia | exact Hg | exact Hg1 | exact Z0].
Qed.

Definition own_iv (iv : Z * Z) : Prop :=
(lo <= fst iv /\ snd iv <= sp1 + 8) \/ (Fr <= fst iv /\ snd iv <= Fr + 504) \/ (Fr / 8 + 2147450880 <= fst iv /\ snd iv <= Fr / 8 + 2147450880 + 64).

#[using="CtxAll"] Lemma own_writesA : forall A LBx B m mX md W,
HEAPAx A LBx LM [(Fr, 3)] B m md -> incl LB0 LBx ->
munch W m mX -> wmono asegs m mX -> mem_inv asegs mX -> Forall own_iv W ->
HEAPAx A LBx LM [(Fr, 3)] B mX md /\ heap_presx A4H XT (LB0 ++ LM) (sp1 + 8) m mX /\ agree_on asegs (LBx ++ LM) m mX.
Proof.
intros A LBx B m mX md W HP Hi MU WM MI HW. pose proof alloc_ceiling_range as ACR. pose proof (hiA_top_le A4L HIx) as HT47.
assert (INF : In (Fr, 3) [(Fr, 3)]) by (left; reflexivity).
destruct (own_frame_fresh HIx Fr 3 LBx LB0 LM [] B A m md HP Hi) as [OFF OFS]. cbn [fr_ivs flat_map app] in OFF, OFS. rewrite app_nil_r in OFF, OFS.
split; [| split].
- eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MI]. eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP MU).
eapply Forall_impl; [| exact HW]. intros [a b] [H | [H | H]]; cbn [fst snd] in *.
+ left. lia.
+ right; right; right. exists Fr, 3. split; [exact INF|]. left. rewrite fr_size_3. lia.
+ right; right; right. exists Fr, 3. split; [exact INF|]. right. unfold shad. cbn [hl_sb A4L]. rewrite fr_shadow_len_3. unfold A_SB. lia.
- eapply (presx_ownA HIx XT _ _ _ _ _ _ _ _ _ _ _ HP MU WM).
+ intros b Hb. left. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply Hi; exact Hb | right; exact Hb].
+ lia.
+ eapply Forall_impl; [| exact HW]. intros [a b] [H | [H | H]]; cbn [fst snd] in *.
* left. lia.
* right; right; right. exists Fr, 3. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. rewrite fr_size_3. lia.
* right; right; right. exists Fr, 3. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. right. unfold shad. cbn [hl_sb A4L]. rewrite fr_shadow_len_3. unfold A_SB. lia.
- eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros a n Hin.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a n HP Hin) as (_ & _ & Ha0 & Hac & _).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF Hin) as DF. rewrite fr_size_3 in DF.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ a n HP Hin) as APP. cbn [hl_sb A4L] in APP. unfold A_SB in APP.
change ((2 ^ 47 - 1) / 8 + 2147450880 + 1) with 17594333495296 in APP.
clear - HW Ha0 Hac DF APP LO FRLO FRHI ACR. induction W as [|[u v] W IH]; cbn [disjoint_from]; [exact I|].
apply Forall_cons_iff in HW as [H HW]. split; [| apply IH; exact HW]. destruct H as [H | [H | H]]; cbn [fst snd] in H; Z.div_mod_to_equations; lia.
Qed.

#[using="CtxAll"] Lemma GA_jo_own : forall m mX W, GA_jo m -> munch W m mX -> wmono asegs m mX -> Forall own_iv W -> GA_jo mX.
Proof.
intros m mX W G MU WM HW. pose proof alloc_ceiling_range as ACR.
eapply GA_jo_munch; [exact G | exact MU | exact WM |]. eapply Forall_impl; [| exact HW].
intros [a b] [H | [H | H]]; cbn [fst snd] in *; right; [lia | lia | Z.div_mod_to_equations; lia].
Qed.

Section Getters.
Variables (p : Z) (s10 s11 : word) (T : TSet).
Hypothesis BB0 : TGT_BB_A_jo <= bB B0.
Hypothesis BD0 : TGT_BD_A_jo <= bD B0.

Definition hstateA (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (pc : Z) (fc : bv 32) (m : word -> option byte) :=
MS (mkR x1 (Z_to_bv 64 sp1) gp (Z_to_bv 64 A_TP) t0 t1 t2 sp0 (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (Fr / 8 + 2147450880)) (Z_to_bv 64 Fr) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 p) (Z_to_bv 64 (Fr + 128)) (Z_to_bv 64 (Fr + 64))
(Z_to_bv 64 Fr) (Z_to_bv 64 2147450880) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom asegs).
Notation gstateA := hstateA.

Definition GINVA (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (F : bvmap 5 word) (fc : bv 32)
(ptr rem : Z) (data : list byte) (s : option jshape) (BS LK : list blk) (sb sd : Z) : Prop :=
HINVA SHB0 m md F fc ptr rem data /\ HEAPAx A (BS ++ LK ++ LB0) LM [(Fr, 3)] B m md /\ jopt asegs A4F s m BS p /\ odepth s <= 32 /\
bB B0 - sb <= bB B /\ bD B0 - sd <= bD B.

Definition KGA (k : Z) (s : option jshape) (BS : list blk) (sb sd : Z) : Prop :=
forall m' md' (A' : ASA A4L HIx) B' F' fc' ptr' rem' data' LK' (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
GINVA m' md' A' B' F' fc' ptr' rem' data' s BS LK' sb sd ->
AJ5 A4L HIx A' T md' (gstateA x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' k fc' m').

#[using="CtxAll p s10 s11 T BB0 BD0"] Lemma sp1_16 : sp1 mod 16 = 0.
Proof. clear - SPA1. Z.div_mod_to_equations. lia. Qed.

#[using="CtxAll p s10 s11 T BB0 BD0"] Lemma pure_callA : forall (pc f : Z) m md (A : ASA A4L HIx) B F fc ptr rem data s BS LK sb sd
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
jo_get_pure_A_stmt HIx f ->
(pc = 0x92058 /\ f = 0x9d978 \/ pc = 0x92088 /\ f = 0xa03f4 \/ pc = 0x92090 /\ f = 0x9d5e8 \/ pc = 0x92098 /\ f = 0xa08b4 \/ pc = 0x920a0 /\ f = 0x9c4b8) ->
GINVA m md A B F fc ptr rem data s BS LK sb sd ->
KGA (pc + 8) s BS sb sd ->
AJ5 A4L HIx A T md (gstateA x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F pc fc m).
Proof.
intros pc f m md A B F fc ptr rem data s BS LK sb sd x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 GP Hpc (INV & HP & JO & OD & BB & BD) K.
pose proof INV as (PX & VM & FS & FRM & LOC & LCK & G & ST & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. change (hl_segs A4L) with asegs in MI.
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP) as (errv & ERR).
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof sp1_16 as SP16. pose proof alloc_ceiling_range as ACR. pose proof (hiA_top_le A4L HIx) as HT47.
pose proof (bv_unsigned_in_range 64 sp0) as SP0R. change (bv_modulus 64) with (2^64) in SP0R.
unfold hstateA.
reenterA asegs A4L HIx asegs_wx HP.
unfold A_TP in *. cbn [hl_tp hl_segs A4L A4H hla_base] in ERR.
destruct Hpc as [[-> ->] | [[-> ->] | [[-> ->] | [[-> ->] | [-> ->]]]]].
all: (step; step; evt_done5;
eapply GP with (BS := BS) (LB := LK ++ LB0) (s := s) (lo := lo) (errv := errv);
[ split; [exact HP|]; rewrite unsigned_lit by lia;
split; [exact ST|]; split; [exact LO|]; split; [lia|]; split; [exact SP16|]; split; [lia|];
split; [exact ERR|]; split; [reflexivity | vm_compute; reflexivity]
| exact JO | exact FRM | reflexivity |]).
all: (intros ms' md' m' rv (RS & VM' & ST' & HPR' & [errv' ERR']) ERRk JO' HP';
destruct RS as (xt0 & xt1 & xt2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & F' & fc' & -> & FS' & FRM');
rewrite unsigned_lit in ST', HPR' by lia;
lazymatch goal with |- AJ5of _ _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end;
lazymatch type of K with KGA ?e _ _ _ _ => let v := eval vm_compute in e in change e with v in K end;
unfold KGA, hstateA in K; eapply K; split;
[ eapply (HINVA_call SHB0 m m' md md' F F' fc fc' ptr rem data (LK ++ LB0) INV HPR' ltac:(intros b Hb; apply in_or_app; right; exact Hb) VM' FS' (FRM' FRM) ST')
| split; [exact HP' | split; [exact JO' | split; [exact OD | split; [exact BB | exact BD]]]]]).
Qed.

Ltac callA_open INV HP m :=
pose proof INV as (PX & VM & FS & FRM & LOC & LCK & G & ST & _);
pose proof (heapA_mem_inv _ HIx _ _ _ _ _ _ _ HP) as MI; change (hl_segs _) with asegs in MI;
destruct (heapA_errno _ HIx _ _ _ _ _ _ _ HP) as (errv & ERR);
pose proof (munch_refl [] m) as MU; pose proof (wmono_refl asegs m) as WM;
pose proof sp1_16 as SP16; pose proof alloc_ceiling_range as ACR; pose proof (hiA_top_le _ HIx) as HT47;
pose proof (bv_unsigned_in_range 64 sp0) as SP0R; change (bv_modulus 64) with (2^64) in SP0R;
unfold hstateA;
(let L := constr:(A4L) in reenterA asegs L HIx asegs_wx HP);
unfold A_TP in *; cbn [hl_tp hl_segs A4L A4H hla_base] in ERR.
Ltac preA_solve HP ST ERR :=
split; [exact HP|]; rewrite unsigned_lit by lia;
split; [exact ST|]; split; [exact LO|]; split; [unfold TGT_STACK_A_jo in *; lia|]; split; [exact sp1_16|]; split; [lia|];
split; [exact ERR|]; split; [reflexivity | vm_compute; reflexivity].
Ltac ret_norm :=
lazymatch goal with |- AJ5of _ _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end.

#[using="CtxAll p s10 s11 T BB0 BD0"] Lemma num_callA : forall (pc f : Z) m md (A : ASA A4L HIx) B F fc ptr rem data s BS LK sb sd
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
jo_get_num_A_stmt HIx f JO_GETNUM_STK_A ->
(pc = 0x92068 /\ f = 0x9dd50 \/ pc = 0x92070 /\ f = 0x9e4a0 \/ pc = 0x92078 /\ f = 0x9e8d8) ->
GINVA m md A B F fc ptr rem data s BS LK sb sd ->
KGA (pc + 8) s BS sb sd ->
AJ5 A4L HIx A T md (gstateA x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F pc fc m).
Proof.
intros pc f m md A B F fc ptr rem data s BS LK sb sd x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 GN Hpc (INV & HP & JO & OD & BB & BD) K.
callA_open INV HP m. unfold JO_GETNUM_STK_A in GN.
destruct Hpc as [[-> ->] | [[-> ->] | [-> ->]]].
all: (step; step; evt_done5;
eapply GN with (A := A) (BS := BS) (LB := LK ++ LB0) (s := s) (lo := lo) (errv := errv);
[ preA_solve HP ST ERR | exact JO | cbn [length]; lia | rewrite unsigned_lit by lia; exact SPA1 | exact FRM | reflexivity |];
intros ms' md' m' r A' (RS & VM' & ST' & HPR' & [errv' ERR']) JO' HP';
destruct RS as (xt0 & xt1 & xt2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & F' & fc' & -> & FS' & FRM');
rewrite unsigned_lit in ST', HPR' by lia; ret_norm;
lazymatch type of K with KGA ?e _ _ _ _ => let v := eval vm_compute in e in change e with v in K end;
unfold KGA, hstateA in K; eapply K; split;
[ eapply (HINVA_call SHB0 m m' md md' F F' fc fc' ptr rem data (LK ++ LB0) INV HPR' ltac:(intros b Hb; apply in_or_app; right; exact Hb) VM' FS' (FRM' FRM) ST')
| split; [exact HP' | split; [exact JO' | split; [exact OD | split; [exact BB | exact BD]]]]]).
Qed.

#[using="CtxAll p s10 s11 T BB0 BD0"] Lemma dbl_callA : forall m md (A : ASA A4L HIx) B F fc ptr rem data s BS LK sb sd
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
jo_get_double_A_stmt HIx JO_GET_DOUBLE_A JO_GETDBL_STK_A JO_GETDBL_COSTB_A JO_GETDBL_COSTD_A ->
sb + JO_GETDBL_COSTB_A <= TGT_BB_A_jo -> sd + JO_GETDBL_COSTD_A <= TGT_BD_A_jo ->
GINVA m md A B F fc ptr rem data s BS LK sb sd ->
KGA 0x92068 s BS (sb + JO_GETDBL_COSTB_A) (sd + JO_GETDBL_COSTD_A) ->
AJ5 A4L HIx A T md (gstateA x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x92060 fc m).
Proof.
intros m md A B F fc ptr rem data s BS LK sb sd x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 GD CB CD (INV & HP & JO & OD & BB & BD) K.
callA_open INV HP m. unfold JO_GET_DOUBLE_A, JO_GETDBL_STK_A, JO_GETDBL_COSTB_A, JO_GETDBL_COSTD_A in *.
step. step. evt_done5.
eapply GD with (A := A) (BS := BS) (LB := LK ++ LB0) (s := s) (lo := lo) (errv := errv);
[ preA_solve HP ST ERR | exact JO | cbn [length]; lia | lia | lia | rewrite unsigned_lit by lia; exact SPA1 | exact FRM | reflexivity |].
intros ms' md' m' r A' B' (RS & VM' & ST' & HPR' & [errv' ERR']) [CHB CHD] JO' HP'.
destruct RS as (xt0 & xt1 & xt2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & F' & fc' & -> & FS' & FRM').
rewrite unsigned_lit in ST', HPR' by lia. ret_norm.
unfold KGA, hstateA in K. eapply K. split;
[ eapply (HINVA_call SHB0 m m' md md' F F' fc fc' ptr rem data (LK ++ LB0) INV HPR' ltac:(intros b Hb; apply in_or_app; right; exact Hb) VM' FS' (FRM' FRM) ST')
| split; [exact HP' | split; [exact JO' | split; [exact OD | split; lia]]]].
Qed.

#[using="CtxAll p s10 s11 T BB0 BD0"] Lemma visit_callA : forall m md (A : ASA A4L HIx) B F fc ptr rem data s BS LK sb sd
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
jo_visit_A_stmt HIx JO_VISIT_A JO_EMIT_A JO_VISIT_STK0_A JO_VISIT_STK1_A ->
GINVA m md A B F fc ptr rem data s BS LK sb sd ->
KGA 0x920c0 s BS sb sd ->
AJ5 A4L HIx A T md (gstateA x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x920a8 fc m).
Proof.
intros m md A B F fc ptr rem data s BS LK sb sd x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 VI (INV & HP & JO & OD & BB & BD) K.
callA_open INV HP m. unfold JO_VISIT_A, JO_EMIT_A, JO_VISIT_STK0_A, JO_VISIT_STK1_A in *.
assert (OD0 : 0 <= odepth s) by (destruct s as [sh|]; cbn [odepth]; [pose proof (Q0Ek.sdepth_nonneg sh) | ]; lia).
step. step. step. step. step. step. evt_done5.
eapply VI with (A := A) (BS := BS) (LB := LK ++ LB0) (s := s) (lo := lo) (errv := errv);
[ preA_solve HP ST ERR | exact JO | cbn [length]; lia | reflexivity | reflexivity | reflexivity | reflexivity |].
intros ms' md' m' r A' (RS & VM' & ST' & HPR' & [errv' ERR']) -> JO' HP'.
destruct RS as (xt0 & xt1 & xt2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & F' & fc' & -> & FS' & FRM').
rewrite unsigned_lit in ST', HPR' by lia. ret_norm.
unfold KGA, hstateA in K. eapply K. split;
[ eapply (HINVA_call SHB0 m m' md md' F F' fc fc' ptr rem data (LK ++ LB0) INV HPR' ltac:(intros b Hb; apply in_or_app; right; exact Hb) VM' FS' (FRM' FRM) ST')
| split; [exact HP' | split; [exact JO' | split; [exact OD | split; [exact BB | exact BD]]]]].
Qed.

#[using="CtxAll p s10 s11 T BB0 BD0"] Lemma str_callA : forall (gsS : jshape -> Z) (gsB : Z -> Z) m md (A : ASA A4L HIx) B F fc ptr rem data s BS LK sb sd (gc : Z)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
jo_get_string_A_stmt HIx JO_GET_STRING_A gsS gsB -> jo_get_string_null_A_stmt HIx JO_GET_STRING_A JO_GETSTR_STK0_A ->
0 <= gc -> sb + gc <= TGT_BB_A_jo ->
(forall sh, s = Some sh -> exists w, jtx sh BS = Some (w, []) /\ w < 2^27 /\ gsS sh <= 2^20 - 144 /\ gsB w <= gc) ->
GINVA m md A B F fc ptr rem data s BS LK sb sd ->
(forall BS', (forall sh w, s = Some sh -> jtx sh BS = Some (w, []) -> exists PT, jtx sh BS' = Some (w, PT)) -> KGA 0x92088 s BS' (sb + gc) sd) ->
AJ5 A4L HIx A T md (gstateA x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x92080 fc m).
Proof.
intros gsS gsB m md A B F fc ptr rem data s BS LK sb sd gc x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 GS GS0 GC0 CBT CST (INV & HP & JO & OD & BB & BD) K.
pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP) as [_ BD00].
callA_open INV HP m. unfold JO_GET_STRING_A, JO_GETSTR_STK0_A in *.
step. step. evt_done5.
destruct s as [sh|].
- destruct JO as [Hp J]. cbn [odepth] in OD. destruct (CST sh eq_refl) as (w & JTX & W27 & C1 & C2).
eapply GS with (A := A) (BS := BS) (LB := LK ++ LB0) (s := sh) (lo := lo) (errv := errv) (rc := 1) (w := w);
[ preA_solve HP ST ERR | exact J | lia | exact (proj1 (proj2 G)) | exact JTX | exact W27 | cbn [length]; lia | lia | exact BD00 | exact FRM | reflexivity |].
intros ms' md' m' A' B' r errv' BS' PT' RS VM' ST' HPR' ERR' [CHB CHD] HP' J' JTX' PTL.
destruct RS as (xt0 & xt1 & xt2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & F' & fc' & -> & FS' & FRM').
rewrite unsigned_lit in ST', HPR' by lia. ret_norm.
pose proof (K BS' ltac:(intros sh0 w0 E JT; injection E as <-; rewrite JTX in JT; injection JT as <-; exists PT'; exact JTX')) as K0. unfold KGA, hstateA in K0. eapply K0. split;
[ eapply (HINVA_call SHB0 m m' md md' F F' fc fc' ptr rem data (LK ++ LB0) INV HPR' ltac:(intros b Hb; apply in_or_app; right; exact Hb) VM' FS' (FRM' FRM) ST')
| split; [exact HP' | split; [split; [exact Hp | exact J'] | split; [exact OD | split; lia]]]].
- destruct JO as [Hp EBS]. rewrite Hp. subst BS. cbn [app] in HP.
eapply GS0 with (lo := lo) (errv := errv); [ preA_solve HP ST ERR |].
intros ms' md' m' rv (RS & VM' & ST' & HPR' & [errv' ERR']) ERRk HP'.
destruct RS as (xt0 & xt1 & xt2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & F' & fc' & -> & FS' & FRM').
rewrite unsigned_lit in ST', HPR' by lia. ret_norm.
pose proof (K [] ltac:(intros sh0 w0 E JT; discriminate E)) as K0. unfold KGA, hstateA in K0. rewrite <- Hp. eapply K0. split;
[ eapply (HINVA_call SHB0 m m' md md' F F' fc fc' ptr rem data (LK ++ LB0) INV HPR' ltac:(intros b Hb; apply in_or_app; right; exact Hb) VM' FS' (FRM' FRM) ST')
| split; [exact HP' | split; [split; [exact Hp | reflexivity] | split; [exact OD | split; [lia | exact BD]]]]].
Qed.
Variables (tpB tpD : Z -> Z) (dcB dcD : Z -> Z) (gsS : jshape -> Z) (gsB : Z -> Z).
Hypothesis CA : jo_callees_A HIx tpB tpD dcB dcD gsS gsB.

#[using="CtxAll p s10 s11 T BB0 BD0 tpB tpD dcB dcD gsS gsB CA"] Lemma seg_gettersA : forall m md (A : ASA A4L HIx) B F fc ptr rem data s BS LK sb sd (gc : Z)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
0 <= gc ->
(forall sh, s = Some sh -> exists w, jtx sh BS = Some (w, []) /\ w < 2^27 /\ gsS sh <= 2^20 - 144 /\ gsB w <= gc) ->
sb + JO_GETDBL_COSTB_A + gc <= TGT_BB_A_jo -> sd + JO_GETDBL_COSTD_A <= TGT_BD_A_jo ->
GINVA m md A B F fc ptr rem data s BS LK sb sd ->
(forall BS', (forall sh w, s = Some sh -> jtx sh BS = Some (w, []) -> exists PT, jtx sh BS' = Some (w, PT)) -> KGA 0x920c0 s BS' (sb + JO_GETDBL_COSTB_A + gc) (sd + JO_GETDBL_COSTD_A)) ->
AJ5 A4L HIx A T md (gstateA x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x92058 fc m).
Proof.
intros m md A B F fc ptr rem data s BS LK sb sd gc x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 GC0 CST CB CD GI K.
Ltac kga_next := unfold KGA; intros;
lazymatch goal with |- AJ5of _ _ _ _ _ (hstateA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?pc _ _) =>
let v := eval vm_compute in pc in change pc with v end.
Ltac pc_pick := (repeat first [ left; split; reflexivity | right ]; try (split; reflexivity)).
eapply (pure_callA 0x92058 0x9d978); [exact (ca_GETB _ _ _ _ _ _ _ CA) | pc_pick | exact GI |]. kga_next.
assert (CB1 : sb + JO_GETDBL_COSTB_A <= TGT_BB_A_jo) by lia.
eapply dbl_callA; [exact (ca_GETD _ _ _ _ _ _ _ CA) | exact CB1 | exact CD | eassumption |]. kga_next.
eapply (num_callA 0x92068 0x9dd50); [exact (ca_GETI _ _ _ _ _ _ _ CA) | pc_pick | eassumption |]. kga_next.
eapply (num_callA 0x92070 0x9e4a0); [exact (ca_GETI64 _ _ _ _ _ _ _ CA) | pc_pick | eassumption |]. kga_next.
eapply (num_callA 0x92078 0x9e8d8); [exact (ca_GETU64 _ _ _ _ _ _ _ CA) | pc_pick | eassumption |]. kga_next.
eapply (str_callA gsS gsB) with (gc := gc); [exact (ca_GETS _ _ _ _ _ _ _ CA) | exact (ca_GETS0 _ _ _ _ _ _ _ CA) | exact GC0 | exact CB | exact CST | eassumption |].
kga_next.
eapply (pure_callA 0x92088 0xa03f4); [exact (ca_GETSL _ _ _ _ _ _ _ CA) | pc_pick | eassumption |]. kga_next.
eapply (pure_callA 0x92090 0x9d5e8); [exact (ca_GETO _ _ _ _ _ _ _ CA) | pc_pick | eassumption |]. kga_next.
eapply (pure_callA 0x92098 0xa08b4); [exact (ca_GETA _ _ _ _ _ _ _ CA) | pc_pick | eassumption |]. kga_next.
eapply (pure_callA 0x920a0 0x9c4b8); [exact (ca_GETT _ _ _ _ _ _ _ CA) | pc_pick | eassumption |]. kga_next.
eapply visit_callA; [exact (ca_VISIT _ _ _ _ _ _ _ CA) | eassumption | apply K; assumption].
Qed.
End Getters.
End Ctx.
End AHarnJo1.
End RC__1.
End Mq9.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc5u QAzu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqa.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z QIsM.Mq2 Qa8x.Mq1.
Import Qhd4 Qwm6.
Import QbFI.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QSHS Ql4f.Mq4 Q1Y6.Mq4 QsKa.Mqh QrQv.Mq4 QEUF.Mq2 QdGy.Mq9.
Import Qc5u QAzu.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition APE_ERRMEMB : Z := 0x989dc.

Section PeSCendA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis MAPP : memappend_A_stmt2 HIx.

Lemma seg_cend_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (nB : nat)
(gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOK m ts 0 -> BOK pf pa ts B (S nB) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_comment_end ->
t_co ts < pf_len pf ->

(forall m' md' A' B' st' pbs' errv' t0' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc',
(bv_unsigned cb = 47 /\ st' = ST_eatws) \/ (bv_unsigned cb <> 47 /\ st' = ST_comment) ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_lvl (ts_pbs ts pbs') (TL st' (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv' ->
PBOK m' (ts_lvl (ts_pbs ts pbs') (TL st' (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) 1 ->
BOK pf pa (ts_lvl (ts_pbs ts pbs') (TL st' (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp t0' a0' a1' a2' a3' a4' a5' a6' a7' s3 (Z_to_bv 64 2) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' errv' x1' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msX asegs pf pa APE_ERR3 x1' gp t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s3 (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_comment_end) (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 0) (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5 (Z_to_bv 64 APE_JTAB) a7 s3 (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK BK Hl Hst Hco Kbreak Kerr16.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof INV as INV0. destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
unfold pe_msA, pe_msO, pe_msX in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
unfold APE_BREAK, APE_STBRK, APE_ERR3, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear PB TSK REST.
reenterA asegs A4L HIx asegs_wx HP. rewrite Hst. unfold ST_comment_end. cbn [pe_jtA].
step.
asan_chkB.
do 4 step.
evt_done5.
eapply (pe_memappend_c HIx GA GA_pres MAPP (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv T);
[exact STC | exact BSL | exact INV0 | exact PBK | exact BK | exact Hco | rewrite unsigned_lit by lia; reflexivity |].
intros m2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 OUT2 FS2 FRM2.
cbn [pf_spf] in *. unfold A_TP in *.

clear TOK SLOTS SHT1 Htal Htlo Hthi Himg_t INtk HP INV0 PBK BK.
set (ts2 := ts_pbs ts0 pbs2) in *.
pose proof INV2 as INV2'. destruct INV2' as [CORE2 REST2].
destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK & FR).
pose proof REST2 as (HP & LV & _).
unfold ts2, ts_pbs, ts0 in TOK, TSK, LV. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK, TSK, LV.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & FF & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS, FF.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts2)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts2)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m2) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 0 HP INq ltac:(lia) ltac:(lia)) as SHQ.
replace (q / 8 + 4 * Z.of_nat depth + 0 + A_SB) with (q / 8 + 4 * Z.of_nat depth + A_SB) in SHQ by lia.
assert (Hb8 : bse mod 8 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
assert (SHQ4 : ro_cells asegs m2 (bse / 8 + A_SB) [C1 (Z_to_bv 8 0)]).
{ replace (bse / 8) with (q / 8 + 4 * Z.of_nat depth) by (subst bse; rewrite div8_add_mul32 by lia; lia). exact SHQ. }
pose proof (munch_refl [(bse, bse + 32)] m2) as MU.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t. stash Himg_q. clear LV TSK.
reenterA asegs A4L HIx asegs_wx HP.
destruct OUT2 as [(-> & PBK2 & BK2) | [-> Epbs2]].
2:{ replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step.
if_false.
step.
step.
step. rewrite ?sxb_zero, ?zxb_zero. step. if_true.
step.
evt_done5.
eapply (Kerr16 m2 md2 A2 B2 errv2); [| exact FS2 | exact FRM2].
subst pbs2. exact INV2. }
step. if_true.
step. step. rewrite ?sxb_zero, ?zxb_zero. step. step. if_true.
step. step.
change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)).
step. rewrite ?sxb_zero, ?zxb_zero. do 4 step. step. if_true.
step. step.
norm_sx32.
do 4 step.
ub_bse q bse (Z.of_nat depth).
assert (BLO : 0 < bse < 2^63 /\ q <= bse) by (subst bse; lia).
do 7 step.
ub_lvl q bse (Z.of_nat depth).
step.
destruct (Z.eq_dec (bv_unsigned cb) 47) as [C47 | N47].
- if_falsex.
step. ub_if_lit.
step. if_truex.
step. ub_land Hb8. step. ub_if_lit.
step. step. sh_norm. step. rewrite ?sxb_zero, ?zxb_zero. step. step. if_true.
stepz.
step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m2 mc, WMc : wmono asegs m2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5; subst bse;
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 mc md2 A2 B2 ts2
cb nb pj sv errv2 l ST_eatws (tl_ss l) c0 hn0 c0 STC INV2 Hl MUc WMc MIc TOKc Lc Hmode
ltac:(rewrite <- Hmode; apply QIsM.Mq2.lvl_mode_ws_same; [rewrite Hst; reflexivity | reflexivity])
ltac:(unfold ST_eatws; lia) SS26 (or_introl eq_refl) ltac:(rewrite Hst; reflexivity)) as [INV3 PBK3];
eapply (Kbreak mc md2 A2 B2 ST_eatws pbs2 errv2); [left; split; [exact C47 | reflexivity] | exact INV3 | exact (PBK3 1 PBK2) | exact (BOK_lvl_restate _ _ ts2 B2 nB l ST_eatws (tl_ss l) Hl (lvl_closed_keep l ST_eatws _ _ _ _ _ eq_refl) (BOK_weaken _ _ _ _ _ nB (Nat.le_succ_diag_r nB) BK2)) | exact FS2 | exact FRM2]
end end.
- if_truex.
step. ub_if_lit.
step. if_truex.
step. ub_land Hb8. step. ub_if_lit.
step. step. sh_norm. step. rewrite ?sxb_zero, ?zxb_zero. step. step. if_true.
step. step.
stepz.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m2 mc, WMc : wmono asegs m2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5; subst bse;
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 mc md2 A2 B2 ts2
cb nb pj sv errv2 l ST_comment (tl_ss l) c0 hn0 c0 STC INV2 Hl MUc WMc MIc TOKc Lc Hmode
ltac:(rewrite <- Hmode; apply QIsM.Mq2.lvl_mode_ws_same; [rewrite Hst; reflexivity | reflexivity])
ltac:(unfold ST_comment; lia) SS26 (or_introl eq_refl) ltac:(rewrite Hst; reflexivity)) as [INV3 PBK3];
eapply (Kbreak mc md2 A2 B2 ST_comment pbs2 errv2); [right; split; [exact N47 | reflexivity] | exact INV3 | exact (PBK3 1 PBK2) | exact (BOK_lvl_restate _ _ ts2 B2 nB l ST_comment (tl_ss l) Hl (lvl_closed_keep l ST_comment _ _ _ _ _ eq_refl) (BOK_weaken _ _ _ _ _ nB (Nat.le_succ_diag_r nB) BK2)) | exact FS2 | exact FRM2]
end end.
Qed.
End PeSCendA.
End RC__1.
End Mqa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2EX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqb.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QCcH Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QRUw.Mq0 QkMG. Import QG8z Qdyh.Mq2 QLbz.
Import QbFI. Import QlKV.Mq2. Import QrQv.Mq4 Q2EX QdGy.Mqa.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma JL_lvl : forall ts ts' l l' g g' a a' w',
nth_error (t_levels ts) (t_depth ts) = Some l ->
t_levels ts' = lupd (t_levels ts) (t_depth ts) l' -> t_depth ts' = t_depth ts -> t_objs ts' = t_objs ts -> t_objbs ts' = t_objbs ts ->
lw l' = Some w' -> zin (tl_st l') [ST_array_add; ST_ovadd] = zin (tl_st l) [ST_array_add; ST_ovadd] ->
JL ts g a ->
(forall w0, lw l = Some w0 -> 0 <= w0 ->
w' + jtext (tl_st l') g' + jpi (tl_st l') (tl_ss l') <= w0 + jtext (tl_st l) g + jpi (tl_st l) (tl_ss l) + JC1 * (a' - a)) ->
JL ts' g' a'.
Proof.
intros [d lv co pb pbs x o os obs] [d' lv' co' pb' pbs' x' o' os' obs'] l l' g g' a a' w'. cbn [t_levels t_depth t_objs t_objbs].
intros Hl -> -> -> -> Lw Hz J H.
eapply (JL_upd d lv l l' co pb pbs x o os obs co' pb' pbs' x' g g' a a' w' Hl Lw Hz) in J; [| exact H].
destruct J as (W & E & L). exists W. split; [| exact L].
rewrite <- E. unfold jw. cbn [t_levels t_depth t_objs t_objbs]. reflexivity.
Qed.

Lemma JL_lvl_restate : forall ts ts' l l' g g' a a',
nth_error (t_levels ts) (t_depth ts) = Some l ->
t_levels ts' = lupd (t_levels ts) (t_depth ts) l' -> t_depth ts' = t_depth ts -> t_objs ts' = t_objs ts -> t_objbs ts' = t_objbs ts ->
tl_cs l' = tl_cs l -> tl_cbs l' = tl_cbs l -> tl_nbs l' = tl_nbs l ->
zin (tl_st l') [ST_array_add; ST_ovadd] = zin (tl_st l) [ST_array_add; ST_ovadd] ->
JL ts g a ->
jtext (tl_st l') g' + jpi (tl_st l') (tl_ss l') <= jtext (tl_st l) g + jpi (tl_st l) (tl_ss l) + JC1 * (a' - a) ->
JL ts' g' a'.
Proof.
intros ts ts' l l' g g' a a' Hl E1 E2 E3 E4 C1 C2 C3 Hz J H.
destruct (JL_jw _ _ _ J) as (W & EW).
assert (Lw : exists w0, lw l = Some w0).
{ destruct ts as [d lv co pb pbs x o os obs]. cbn [t_levels t_depth] in Hl. unfold jw in EW. cbn [t_levels t_depth] in EW.
destruct (jwl lv (S d)) as [A|] eqn:EA; [| discriminate EW]. exact (jwl_nth lv (S d) d l A EA Hl ltac:(lia)). }
destruct Lw as (w0 & Lw0).
eapply (JL_lvl ts ts' l l' g g' a a' w0 Hl E1 E2 E3 E4); [rewrite (lw_restate l l' C1 C2 C3); exact Lw0 | exact Hz | exact J |].
intros w1 Lw1 _. rewrite Lw0 in Lw1. injection Lw1 as <-. lia.
Qed.

Lemma JL_keep : forall ts ts' g g' a a', t_levels ts' = t_levels ts -> t_depth ts' = t_depth ts -> t_objs ts' = t_objs ts -> t_objbs ts' = t_objbs ts ->
g' <= g -> a <= a' -> JL ts g a -> JL ts' g' a'.
Proof.
intros ts ts' g g' a a' E1 E2 E3 E4 Hg Ha J. eapply (JL_same ts ts'); [exact E1 | exact E2 | intros _; split; [exact E3 | exact E4] |].
eapply JL_mono; [exact Hg | exact Ha | exact J].
Qed.

Lemma lw_attach : forall st' ss' r sh BS nm w, jfresh sh BS w -> lw (TL st' ss' r (Some sh) BS nm []) = Some w.
Proof. intros st' ss' r sh BS nm w H. unfold lw. cbn [tl_cs tl_cbs tl_nbs]. rewrite (vw_fresh _ _ _ H). cbn [nw]. f_equal. lia. Qed.
Lemma lw_value : forall l, (exists w0, lw l = Some w0) -> exists v, vw (tl_cs l) (tl_cbs l) = Some v /\ lw l = Some (v + nw (tl_nbs l)).
Proof. intros l (w0 & H). unfold lw in *. destruct (vw (tl_cs l) (tl_cbs l)) as [v|]; [| discriminate H]. exists v. split; reflexivity. Qed.
Lemma lw_rename : forall l st' ss' nm' nbs' v, vw (tl_cs l) (tl_cbs l) = Some v -> lw (TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) nm' nbs') = Some (v + nw nbs').
Proof. intros l st' ss' nm' nbs' v H. unfold lw. cbn [tl_cs tl_cbs tl_nbs]. rewrite H. reflexivity. Qed.
Lemma lw_arr : forall l kids, tl_cs l = Some (Sarr kids) -> forall w0, lw l = Some w0 -> exists w, jtx (Sarr kids) (tl_cbs l) = Some (w, []) /\ w0 = w + nw (tl_nbs l).
Proof.
intros l kids E w0 H. unfold lw in H. rewrite E in H. cbn [vw] in H. destruct (jtx (Sarr kids) (tl_cbs l)) as [[w [|? ?]]|] eqn:J; try discriminate H.
injection H as <-. exists w. split; reflexivity.
Qed.
Lemma lw_obj : forall l kids, tl_cs l = Some (Sobj kids) -> forall w0, lw l = Some w0 -> exists w, jtx (Sobj kids) (tl_cbs l) = Some (w, []) /\ w0 = w + nw (tl_nbs l).
Proof.
intros l kids E w0 H. unfold lw in H. rewrite E in H. cbn [vw] in H. destruct (jtx (Sobj kids) (tl_cbs l)) as [[w [|? ?]]|] eqn:J; try discriminate H.
injection H as <-. exists w. split; reflexivity.
Qed.
Lemma lw_container : forall st' ss' cur s cbs nm nbs w, jtx s cbs = Some (w, []) -> lw (TL st' ss' cur (Some s) cbs nm nbs) = Some (w + nw nbs).
Proof. intros st' ss' cur s cbs nm nbs w H. unfold lw. cbn [tl_cs tl_cbs tl_nbs vw]. rewrite H. reflexivity. Qed.

Lemma vw_kid : forall os obs b, vw os obs = Some b -> (os = None -> obs = []) -> exists wv, jtx_opt os obs = Some (wv, []) /\ wv <= b + NULL_W.
Proof.
intros [s|] obs b H Hn; cbn [vw jtx_opt] in *.
- destruct (jtx s obs) as [[w [|? ?]]|]; try discriminate H. injection H as <-. exists w. split; [reflexivity | unfold NULL_W; lia].
- injection H as <-. rewrite (Hn eq_refl). exists NULL_W. split; [reflexivity | lia].
Qed.

Lemma JL_add : forall ts ts' l l' g g' a a' w',
nth_error (t_levels ts) (t_depth ts) = Some l ->
t_levels ts' = lupd (t_levels ts) (t_depth ts) l' -> t_depth ts' = t_depth ts ->
lw l' = Some w' -> zin (tl_st l) [ST_array_add; ST_ovadd] = true -> zin (tl_st l') [ST_array_add; ST_ovadd] = false ->
JL ts g a ->
(forall w0 b, lw l = Some w0 -> vw (t_objs ts) (t_objbs ts) = Some b ->
w' + jtext (tl_st l') g' + jpi (tl_st l') (tl_ss l') <= w0 + b + jtext (tl_st l) g + jpi (tl_st l) (tl_ss l) + JC1 * (a' - a)) ->
JL ts' g' a'.
Proof.
intros [d lv co pb pbs x o os obs] [d' lv' co' pb' pbs' x' o' os' obs'] l l' g g' a a' w'. cbn [t_levels t_depth t_objs t_objbs].
intros Hl -> -> Lw Hz Hz' (W & E & L) H.
destruct (jw_upd_add d lv l l' co pb pbs x o os obs co' pb' pbs' x' o' os' obs' W w' Hl E Lw Hz Hz') as (w0 & b & Lw0 & Eb & E').
exists (W - w0 - b + w'). split; [exact E'|].
rewrite (cur_st_updJ _ _ l), (cur_ss_updJ _ _ l) by exact Hl. rewrite (cur_st_ofJ _ _ l), (cur_ss_ofJ _ _ l) in L by exact Hl.
specialize (H w0 b Lw0 Eb). lia.
Qed.

Lemma JL_pop : forall ts dp l lp g a,
t_depth ts = S dp -> nth_error (t_levels ts) (S dp) = Some l -> nth_error (t_levels ts) dp = Some lp ->
zin (tl_st l) [ST_array_add; ST_ovadd] = false -> zin (tl_st lp) [ST_array_add; ST_ovadd] = true ->
JL ts g a ->
jpi (tl_st lp) (tl_ss lp) <= jtext (tl_st l) g + jpi (tl_st l) (tl_ss l) ->
JL (TST dp (lupd (t_levels ts) (S dp) (TL ST_eatws ST_start 0 None [] 0 [])) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (tl_cur l) (tl_cs l) (tl_cbs l)) g a.
Proof.
intros [d lv co pb pbs x o os obs] dp l lp g a. cbn [t_levels t_depth t_co t_pb t_pbs t_x]. intros -> Hl Hlp Hz Hzp (W & E & L) H.
destruct (jw_pop dp lv l lp co pb pbs x o os obs W Hl Hlp Hz Hzp E) as (W' & E' & LW). exists W'. split; [exact E'|].
rewrite (cur_st_ofJ _ _ l), (cur_ss_ofJ _ _ l) in L by exact Hl.
assert (Ec : cur_st (TST dp (lupd lv (S dp) (TL ST_eatws ST_start 0 None [] 0 [])) co pb pbs x (tl_cur l) (tl_cs l) (tl_cbs l)) = tl_st lp)
by (unfold cur_st; cbn [t_levels t_depth]; rewrite nth_error_lupd_neq by lia; rewrite Hlp; reflexivity).
assert (Es : cur_ss (TST dp (lupd lv (S dp) (TL ST_eatws ST_start 0 None [] 0 [])) co pb pbs x (tl_cur l) (tl_cs l) (tl_cbs l)) = tl_ss lp)
by (unfold cur_ss; cbn [t_levels t_depth]; rewrite nth_error_lupd_neq by lia; rewrite Hlp; reflexivity).
rewrite Ec, Es. assert (Elive : jtext (tl_st lp) g = 0).
{ unfold jtext, jlive. cbn [zin existsb] in Hzp |- *. apply orb_prop in Hzp. destruct Hzp as [Hq | Hq]; [| apply orb_prop in Hq; destruct Hq as [Hq | Hq]; [| discriminate Hq]];
apply Z.eqb_eq in Hq; rewrite Hq; reflexivity. }
rewrite Elive. lia.
Qed.

Lemma JL_push : forall ts l lp g g' a a',
nth_error (t_levels ts) (t_depth ts) = Some l -> (S (t_depth ts) < length (t_levels ts))%nat ->
tl_cs lp = tl_cs l -> tl_cbs lp = tl_cbs l -> tl_nbs lp = tl_nbs l ->
zin (tl_st l) [ST_array_add; ST_ovadd] = false ->
JL ts g a ->
26 <= jtext (tl_st l) g + jpi (tl_st l) (tl_ss l) + JC1 * (a' - a) ->
JL (ts_push ts lp) g' a'.
Proof.
intros [d lv co pb pbs x o os obs] l lp g g' a a'. unfold ts_push. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs]. intros Hl Hlen C1 C2 C3 Hz (W & E & L) H.
pose proof (jw_push d lv l lp co pb pbs x o os obs W Hl Hlen E (lw_restate l lp C1 C2 C3) Hz) as E'.
exists W. split; [exact E'|].
rewrite (cur_st_ofJ _ _ l), (cur_ss_ofJ _ _ l) in L by exact Hl.
assert (Ec : cur_st (TST (S d) (lupd (lupd lv d lp) (S d) (TL ST_eatws ST_start 0 None [] 0 [])) co pb pbs x o os obs) = ST_eatws)
by (unfold cur_st; cbn [t_levels t_depth]; rewrite nth_error_lupd_eq by (rewrite lupd_length; exact Hlen); reflexivity).
assert (Es : cur_ss (TST (S d) (lupd (lupd lv d lp) (S d) (TL ST_eatws ST_start 0 None [] 0 [])) co pb pbs x o os obs) = ST_start)
by (unfold cur_ss; cbn [t_levels t_depth]; rewrite nth_error_lupd_eq by (rewrite lupd_length; exact Hlen); reflexivity).
rewrite Ec, Es. change (jtext ST_eatws g') with 0. change (jpi ST_eatws ST_start) with 26. lia.
Qed.

End RC__1.
End Mqb.

Module Mqc.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QRUw.Mq2 QmZZ. Import QPZI.Mq4. Import QkMG. Import QG8z Qdyh.Mq0.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QlKV.Mqf QlKV.Mqh QSHS Ql4f.Mq4 QsKa.Mqh QrQv.Mq4 QEUF.Mq2 QdGy.Mqe.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section WithIface.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.

Definition lvl_nameless (m : word -> option byte) (l : tlevel) : Prop :=
0 <= tl_st l <= 26 /\ 0 <= tl_ss l <= 26 /\ jopt asegs A4F (tl_cs l) m (tl_cbs l) (tl_cur l) /\ tl_nbs l = [].

Definition PE_NWIN (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (XS : list blk)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) : Prop :=
PE_CORE_A pf pa q m ts cb nb pj sv /\
PE_BASE_A HIx GA pf pa LB0 LM FRS payload me lo m md A B (pe_blocksA pf q LB0 (tsF ts XS)) errv /\
(forall i li, nth_error (t_levels ts) i = Some li -> i <> t_depth ts -> lvl_cur asegs A4F m (t_depth ts) i li) /\
(exists l, nth_error (t_levels ts) (t_depth ts) = Some l /\ lvl_nameless m l) /\
t_objbs ts = [].

Lemma PE_NWIN_open : forall pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv l,
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> t_objbs ts = [] ->
PE_NWIN pf pa q LB0 LM FRS payload me lo m md A B (ts_lvl ts (TL (tl_st l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) [])) (tl_nbs l) cb nb pj sv errv.
Proof.
intros pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv l [CORE REST] Hl Eobj.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
apply PE_REST_A_base in REST as (BASE & LV & OBJ & BUD).
set (lw := TL (tl_st l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) []).
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
pose proof (LV _ _ Hl) as (R1 & R2 & JO & _).
split; [| split; [| split; [| split]]].
- unfold PE_CORE_A, ts_lvl; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOK|]. split; [exact PB|]. split; [exact Hpb|]. split; [| exact FR].
eapply tstack_lupd_srec; [exact TSK | exact Hl |]. reflexivity.
- destruct BASE as (HP & BASE'). split; [| exact BASE'].
eapply (heapA_perm A4L HIx); [exact HP | | apply Permutation_refl | apply Permutation_refl].
eapply Permutation_trans; [apply (pe_blocksA_cur_perm2 pf q LB0 ts l Hl)|]. apply Permutation_sym.
eapply Permutation_trans; [apply (pe_blocksA_lvl_obj_perm pf q LB0 ts l lw 0 None (tl_nbs l) Hl)|].
unfold lvl_blocks, lw; cbn [tl_cbs tl_nbs app]. rewrite Eobj, app_nil_r. cbn [app]. rewrite <- app_assoc. apply Permutation_refl.
- unfold ts_lvl; cbn [t_levels t_depth]. intros i li Hli Hne. rewrite nth_error_lupd_neq in Hli by congruence. exact (LV i li Hli).
- exists lw. split; [unfold ts_lvl; cbn [t_levels t_depth]; apply nth_error_lupd_eq; exact Hd|].
unfold lvl_nameless, lw; cbn [tl_st tl_ss tl_cs tl_cbs tl_cur tl_nbs]. split; [exact R1|]. split; [exact R2|]. split; [exact JO | reflexivity].
- exact Eobj.
Qed.

Lemma PE_NWIN_write : forall pf pa q LB0 LM FRS payload me lo m mc md A B ts XS cb nb pj sv errv W l l' cb' nb' pj',
PE_STATIC_A HIx pf pa lo ->
PE_NWIN pf pa q LB0 LM FRS payload me lo m md A B ts XS cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l ->
munch W m mc -> wmono asegs m mc -> mem_inv asegs mc -> Forall (pe_wtqA pf pa q) W ->
rw_cells asegs mc (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat (t_depth ts)) q (t_x ts)) ->
tstack asegs mc q (lupd (t_levels ts) (t_depth ts) l') ->
pe_frameA asegs mc pf pa cb' nb' pj' sv ->
0 <= tl_st l' <= 26 -> 0 <= tl_ss l' <= 26 -> tl_cur l' = tl_cur l -> tl_cs l' = tl_cs l -> tl_cbs l' = tl_cbs l -> tl_nbs l' = [] ->
PE_NWIN pf pa q LB0 LM FRS payload me lo mc md A B (ts_lvl ts l') XS cb' nb' pj' sv errv
/\ (forall b, PBOKat m ts b -> PBOKat mc (ts_lvl ts l') b)
/\ agree_on asegs XS m mc.
Proof.
intros pf pa q LB0 LM FRS payload me lo m mc md A B ts XS cb nb pj sv errv W l l' cb' nb' pj' STC (CORE & BASE & LVo & (l0 & Hl0 & NL) & Eobj) Hl MU WM MI HW TOKc TSKc FRc R1' R2' Ecur Ecs Ecbs Enbs.
rewrite Hl in Hl0. injection Hl0 as <-. destruct NL as (R1 & R2 & JO & Enbs0).
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
destruct (PE_BASE_A_private_write HIx GA GA_outside pf pa q LB0 LM FRS payload me lo m mc md A B (tsF ts XS) errv W STC BASE MU WM MI (pe_wtqA_private _ _ _ _ _ HW)) as [BASEc AG].
unfold tsF in AG; cbn [t_objbs t_levels] in AG.
assert (Eb : lvl_blocks l' = lvl_blocks l) by (unfold lvl_blocks; rewrite Ecbs, Enbs, Enbs0; reflexivity).
split; [| split].
2:{ intros b PBK. eapply PBOKat_same with (ts := ts); [reflexivity | reflexivity |].
eapply PBOKat_agree; [exact PBK | | apply incl_refl].
eapply (agree_wtqA HIx) with (ts := tsF ts XS); [exact STC | exact (proj1 BASE) | exact MU | exact WM | exact HW |].
intros a n Hin. assert (HinL : In (a, n) (pe_blocksA pf q LB0 (tsF ts XS) ++ LM)) by (unfold pe_blocksA, tstate_blocks, tsF; cbn [t_pbs]; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hin).
split; [exact HinL|].
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ (proj1 BASE)) as ND. unfold pe_blocksA in ND. rewrite <- app_assoc in ND. split.
+ intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks, tsF; cbn [t_pbs]; apply in_or_app; left; exact Hin | left; reflexivity].
+ intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks, tsF; cbn [t_pbs]; apply in_or_app; left; exact Hin | right; left; reflexivity]. }
2:{ eapply (agree_on_incl asegs); [exact AG | intros b Hb; apply in_or_app; left; exact Hb]. }
split; [| split; [| split; [| split]]].
- unfold PE_CORE_A, ts_lvl; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOKc|]. split; [| split; [exact Hpb | split; [exact TSKc | exact FRc]]].
eapply (pbuf_wtqA HIx) with (ts := tsF ts XS); [exact STC | exact (proj1 BASE) | exact PB | exact MU | exact WM | exact HW].
- rewrite (pe_blocksA_tsF_lvl pf q LB0 ts XS l l' Hl Eb). exact BASEc.
- unfold ts_lvl; cbn [t_levels t_depth]. intros i li Hli Hne. rewrite nth_error_lupd_neq in Hli by congruence.
eapply (lvl_cur_agree asegs A4F); [exact (LVo i li Hli Hne) | exact AG |].
intros b Hb. apply in_or_app; right. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map. eapply nth_error_In; exact Hli.
- exists l'. split; [unfold ts_lvl; cbn [t_levels t_depth]; apply nth_error_lupd_eq; exact Hd|].
split; [exact R1'|]. split; [exact R2'|]. split; [| exact Enbs].
rewrite Ecs, Ecbs, Ecur. eapply (jopt_agree asegs A4F); [exact JO | exact AG |].
intros b Hb. apply in_or_app; right. apply in_concat. exists (lvl_blocks l). split; [apply in_map; eapply nth_error_In; exact Hl | unfold lvl_blocks; apply in_or_app; left; exact Hb].
- exact Eobj.
Qed.

Lemma PE_NWIN_callG : forall pf pa q LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 ts XS XS2 cb nb pj sv errv errv2,
PE_STATIC_A HIx pf pa lo ->
PE_NWIN pf pa q LB0 LM FRS payload me lo m1 md A B ts XS cb nb pj sv errv ->
model_vm_only (cfg_model md) (cfg_model md2) ->
heap_pres A4H (pe_blocksA pf q LB0 ts ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m1 m2 ->
HEAPA A4L HIx A2 (pe_blocksA pf q LB0 (tsF ts XS2)) LM ((pa_F pa, 2) :: FRS) B2 m2 md2 ->
stk asegs m2 lo (pf_spf pf) -> rw_cells asegs m2 A_ERRNO [C4 errv2] ->
PE_NWIN pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts XS2 cb nb pj sv errv2.
Proof.
intros pf pa q LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 ts XS XS2 cb nb pj sv errv errv2 STC (CORE & BASE & LVo & (l & Hl & NL) & Eobj) VM HPR HP2 ST2 ERR2.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR).
set (RB := pe_blocksA pf q LB0 ts) in *.
assert (INtk : In (pf_tk pf, 72) RB) by (unfold RB, pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * pf_mxd pf) RB) by (unfold RB, pe_blocksA; apply in_or_app; right; right; left; reflexivity).
assert (LB0R : incl LB0 RB) by (unfold RB, pe_blocksA; intros b Hb; apply in_or_app; right; right; right; exact Hb).
assert (AG : agree_on asegs RB m1 m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPR | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
assert (FR2 : pe_frameA asegs m2 pf pa cb nb pj sv).
{ eapply pe_frameA_pres; [exact HPR | lia | exact GEO | | | exact FR].
- apply in_or_app; right. apply in_or_app; right. change 248 with (fr_size 2 - 8). apply fr_ivs_frame. left; reflexivity.
- apply in_or_app; right. apply in_or_app; right. rewrite <- fr_shadow_len_2. change (shA (pa_F pa)) with (shad A4L (pa_F pa)). apply fr_ivs_shadow. left; reflexivity. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR) in TOK; [| eapply client_range_block; [apply in_or_app; left; exact INtk | lia | unfold tok_cells_g; cbn; lia]]. cbn [hl_segs hla_base A4L A4H] in TOK.
apply (tstack_pres_g A4H _ _ _ _ _ _ HPR (in_or_app _ _ _ (or_introl INq))) in TSK; [| exact LEN32]. cbn [hl_segs hla_base A4L A4H] in TSK.
assert (INl : forall i li, nth_error (t_levels ts) i = Some li -> incl (lvl_blocks li) RB).
{ intros i li Hli b Hb. unfold RB, pe_blocksA, tstate_blocks. apply in_or_app; left. apply in_or_app; right. apply in_or_app; right. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map. eapply nth_error_In; exact Hli. }
split; [| split; [| split; [| split; [| exact Eobj]]]].
- split; [exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|]. split; [exact TOK|]. split; [| split; [exact Hpb | split; [exact TSK | exact FR2]]].
eapply pbuf_agree; [exact PB | exact AG |]. unfold RB, pe_blocksA, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb.
- eapply (PE_BASE_A_callG HIx GA GA_pres pf pa LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 _ _ errv errv2 RB); [exact STC | exact BASE | exact VM | exact HPR | exact LB0R | exact HP2 | exact ST2 | exact ERR2].
- intros i li Hli Hne. eapply (lvl_cur_agree asegs A4F); [exact (LVo i li Hli Hne) | exact AG | exact (INl i li Hli)].
- exists l. split; [exact Hl|]. destruct NL as (R1 & R2 & JO & Enbs). split; [exact R1|]. split; [exact R2|]. split; [| exact Enbs].
eapply (jopt_agree asegs A4F); [exact JO | exact AG |]. intros b Hb. apply (INl _ l Hl). unfold lvl_blocks. apply in_or_app; left. exact Hb.
Qed.

Lemma PE_NWIN_close : forall pf pa q LB0 LM FRS payload me lo m md A B ts XS cb nb pj sv errv l c hn,
PE_NWIN pf pa q LB0 LM FRS payload me lo m md A B ts XS cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l ->
lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) -> cls_ok c (tl_cs l) ->
name_ok asegs m hn (TL (tl_st l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) XS) ->
zin (tl_st l) [ST_array_add; ST_ovadd] = false ->
PE_BUD pf pa (ts_lvl ts (TL (tl_st l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) XS)) B ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B (ts_lvl ts (TL (tl_st l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) XS)) cb nb pj sv errv.
Proof.
intros pf pa q LB0 LM FRS payload me lo m md A B ts XS cb nb pj sv errv l c hn (CORE & BASE & LVo & (l0 & Hl0 & NL) & Eobj) Hl Hm CLS NM Hz BUD.
rewrite Hl in Hl0. injection Hl0 as <-. destruct NL as (R1 & R2 & JO & Enbs).
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
set (l' := TL (tl_st l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) XS) in *.
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
split.
- unfold PE_CORE_A, ts_lvl; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOK|]. split; [exact PB|]. split; [exact Hpb|]. split; [| exact FR].
eapply tstack_lupd_srec; [exact TSK | exact Hl |]. reflexivity.
- apply PE_REST_A_of_base; [| | | exact BUD].
+ destruct BASE as (HP & BASE'). split; [| exact BASE'].
eapply (heapA_perm A4L HIx); [exact HP | | apply Permutation_refl | apply Permutation_refl].
eapply Permutation_trans; [apply (perm_blocks_tsF pf q LB0 ts XS Eobj)|]. apply Permutation_sym.
eapply Permutation_trans; [apply (pe_blocksA_lvl_perm pf q LB0 ts l l' Hl)|].
unfold lvl_blocks at 1, l'; cbn [tl_cbs tl_nbs].
eapply Permutation_trans; [| apply Permutation_app_head; apply Permutation_sym; apply (pe_blocksA_cur_perm pf q LB0 ts l Hl)].
unfold lvl_blocks. rewrite Enbs, app_nil_r. rewrite <- app_assoc. apply Permutation_app_swap_app.
+ unfold ts_lvl; cbn [t_levels t_depth]. intros i li Hli.
destruct (PeanoNat.Nat.eq_dec i (t_depth ts)) as [-> | Hne].
* rewrite nth_error_lupd_eq in Hli by exact Hd. injection Hli as <-. split; [exact R1|]. split; [exact R2|]. split; [exact JO|].
rewrite Nat.ltb_irrefl, Nat.eqb_refl. exists c, hn. split; [exact Hm|]. split; [exact CLS | exact NM].
* rewrite nth_error_lupd_neq in Hli by congruence. exact (LVo i li Hli Hne).
+ unfold cur_st, ts_lvl; cbn [t_levels t_depth t_objs t_objbs t_obj]. rewrite nth_error_lupd_eq by exact Hd. cbn [tl_st l']. rewrite Hz. exact Eobj.
Qed.
End WithIface.
End RC__1.
End Mqc.

Module Mqd.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z Qdyh.Mq0 Qdyh.Mq3 Qdyh.Mq4 QIsM.Mq2 Qa8x.Mq2.
Import Qhd4 Qwm6.
Import QbFI.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QlKV.Mqf QSHS Ql4f.Mq4 Q1Y6.Mq4 QsKa.Mqh QrQv.Mq4 QEUF.Mq2 QW22.Mq8 QdGy.Mq9 QYZ0.Mq8.
Import Qc5u QAzu.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QlKV.Mq2.
Import QEUF.Mq3 QdGy.Mqa.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma lvl_mode_start3 : forall ss c hn, 0 <= ss <= 26 -> lvl_mode ST_start ss = Some (c, hn) -> c = CNone /\ hn = false /\ ss = ST_start.
Proof.
intros ss c hn R H. assert (CASES : exists k : nat, (k <= 26)%nat /\ ss = Z.of_nat k) by (exists (Z.to_nat ss); split; lia).
destruct CASES as (k & Hk & ->). clear R.
do 27 (destruct k as [|k]; [vm_compute in H; first [discriminate H | injection H as <- <-; split; [reflexivity | split; reflexivity]] |]); exfalso; lia.
Qed.

Section PeSStartQA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.

Ltac pe_openA STC INV :=
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR); pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk);
destruct INV as [CORE REST];
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR);
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).

Ltac reopen_inv INVx TSx ts0 PF q LB0 tk mxd depth l Hl bse Hbse mX :=
pose proof INVx as [CORE2 REST2];
destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK & FR);
pose proof REST2 as (HP & _); clear REST2;
try unfold TSx in TOK, TSK; try unfold ts_pbs, ts_lvl, ts_set_x in TOK, TSK; try unfold ts0 in TOK, TSK;
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK, TSK;
unfold tok_cells_g in TOK; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK;
unfold pe_frameA in FR; destruct FR as (SLOTS & _ & _ & _ & _); unfold pe_slotsA in SLOTS; cbn zeta in SLOTS;
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS;
assert (INtk : In (tk, 72) (pe_blocksA PF q LB0 TSx)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity);
assert (INq : In (q, 32 * mxd) (pe_blocksA PF q LB0 TSx)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity);
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI;
pose proof (wmono_refl asegs mX) as WM;
pose proof (TSK depth l Hl) as Ld; rewrite <- Hbse in Ld; unfold srec_cells in Ld;
clear TSK.

Lemma start_quote_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 a1 a2 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_start ->

(forall m' a0' a1' a2' a3' a4',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B
(ts_set_x (ts_lvl ts (TL ST_string (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts) (TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) cb)) cb nb pj sv errv ->
PBOKat m' (ts_set_x (ts_lvl ts (TL ST_string (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts) (TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) cb)) 0 ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp t0 a0' a1' a2' a3' a4' a5 a6 a7 s3 (Z_to_bv 64 2) s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x98a00 (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a1 a2 (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC INV Hl Hst Kadv. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 0 HP INq ltac:(lia) ltac:(lia)) as SHQ.
replace (q / 8 + 4 * Z.of_nat depth + 0 + A_SB) with (q / 8 + 4 * Z.of_nat depth + A_SB) in SHQ by lia.
assert (Hb8 : bse mod 8 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
assert (SHQ4 : ro_cells asegs m (bse / 8 + A_SB) [C1 (Z_to_bv 8 0)]).
{ replace (bse / 8) with (q / 8 + 4 * Z.of_nat depth) by (subst bse; rewrite div8_add_mul32 by lia; lia). exact SHQ. }
pose proof (munch_refl [(bse, bse + 32)] m) as MU.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT1c & SEPT1q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT1t & _).
cbn [hl_sb A4L] in SEPT1c, SEPT1q, SEPT1t. assert (EQx : tk / 8 + A_SB + 1 = tk / 8 + 2147450881) by (unfold A_SB; lia). rewrite EQx in SEPT1c, SEPT1q, SEPT1t. clear EQx.
unfold APE_BREAK, APE_REDO, APE_OUT, APE_ERRMEM, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_T1_L : csep (tk / 8 + 2147450881) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPT1q HbseR; lia).
clear Hdtq SEPT1q SEPT1t SEPT1c.
destruct (lvl_mode_start3 _ _ _ SS26 ltac:(rewrite <- Hst; exact Hmode)) as (Ec0 & Ehn0 & Ess). subst c0 hn0.
stash Himg_t. stash Himg_q. stash Kadv. clear PB REST TSK LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ4.
reenterA asegs A4L HIx asegs_wx HP.
replace (q + 32 * Z.of_nat depth) with bse by lia.
step.
step. if_true.
asan_rechkB.
clear SHQ.
step.
stepz.
step.
asan_chkMB 1.
step. step.
set (l1 := TL ST_string (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
pose proof MUc as MUc'; pose proof Lc as Lc'; rewrite Hbse in MUc', Lc';
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv l ST_string (tl_ss l) CNone false CNone STC INV0 Hl MUc' WMc MIc TOKc Lc' Hmode
ltac:(rewrite Ess; vm_compute; reflexivity) ltac:(unfold ST_string; lia) SS26 (or_introl eq_refl)
ltac:(rewrite Hst; vm_compute; reflexivity)) as [INV1 _]; clear MUc' Lc'
end end.
set (ts1 := ts_lvl ts0 l1) in *.
eapply (pe_pbreset HIx GA GA_pres (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md A B ts1 cb nb pj sv errv);
[exact STC | exact INV1 | rewrite unsigned_lit by lia; reflexivity |].
intros mr2 a1' a2' a3' a4' INV2 PBK2 PBC2.
cbn [pf_spf] in *. unfold A_TP in *.
repeat match goal with H : rw_cells asegs _ _ _ |- _ => clear H | H : ro_cells asegs _ _ _ |- _ => clear H | H : munch _ _ _ |- _ => clear H | H : wmono asegs _ _ |- _ => clear H | H : mem_inv asegs _ |- _ => clear H end.
clear Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk INtk INq INV0 INV1 HP cs_tk_L cs_L_tk cs_T1_L.
assert (Hl1 : nth_error (t_levels ts1) (t_depth ts1) = Some l1) by (unfold ts1, ts_lvl, ts0; cbn [t_levels t_depth]; apply nth_error_lupd_eq; apply nth_error_Some; rewrite Hl; discriminate).
pose proof INV2 as ((_ & _ & _ & _ & _ & _ & _ & _ & FRq) & _). unfold pe_frameA in FRq. destruct FRq as (_ & _ & _ & FF & _). unfold ff_cellsA in FF.
cbn [pa_F] in FF.
reopen_inv INV2 ts1 ts0 (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 tk mxd depth l1 Hl1 bse Hbse mr2.
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 6 HP INtk ltac:(lia)) as SHT6.
replace (tk / 8 + 6 + A_SB) with (tk / 8 + 2147450886) in SHT6 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 6 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT6c & SEPT6q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 6 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT6t & _).
cbn [hl_sb A4L] in SEPT6c, SEPT6q, SEPT6t. assert (EQx : tk / 8 + A_SB + 6 = tk / 8 + 2147450886) by (unfold A_SB; lia). rewrite EQx in SEPT6c, SEPT6q, SEPT6t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT4c & SEPT4q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4c, SEPT4q, SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4c, SEPT4q, SEPT4t. clear EQx.
pose proof (munch_refl [(tk, tk + 72)] mr2) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_T4_T : csep (tk / 8 + 2147450884) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPT4t; lia).
clear SEPT6q SEPT6t SEPT6c SEPT4q SEPT4t SEPT4c.
assert (LE1 : le1 (zxb cb) = [cb]).
{ unfold le1, zxb. cbn [Z_to_le_bytes pf_mxd]. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
pose proof (bv_unsigned_in_range 8 cb) as CBR8; unfold bv_modulus in CBR8; cbn in CBR8.
change (bv_modulus 8) with 256%Z. change (bv_modulus 64) with 18446744073709551616%Z. Z.div_mod_to_equations. nia. }
stash Himg_t2. clear Ld.
lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
step.
asan_chkMB 2.
clear SHT6 FF.
step.
rewrite LE1. mem_after_store.
do 4 step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ mr2 mc, WMc : wmono asegs mr2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
destruct (PE_INV_A_tokw1 HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mr2 mc md A B ts1
cb nb pj sv errv co (TS isd stpos (Z_to_bv 64 co) err ucs high cb) STC INV2 MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as [INV3 PBT3];
unstash Kadv; eapply (Kadv mc); [exact INV3 | exact (PBT3 _ (PBOKat_of_pbufc_nil _ _ PBC2))]
end end.
Qed.

Lemma start_squote_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 a1 a2 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> pf_fl pf = 0 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_start ->

(forall m' a0' a1' a2' a3' a4',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B
(ts_set_x (ts_lvl ts (TL ST_string (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts) (TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) cb)) cb nb pj sv errv ->
PBOKat m' (ts_set_x (ts_lvl ts (TL ST_string (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts) (TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) cb)) 0 ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp t0 a0' a1' a2' a3' a4' a5 a6 a7 s3 (Z_to_bv 64 2) s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x989e0 (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a1 a2 (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC FL0 INV Hl Hst Kadv. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *. subst fl.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd 0) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd 0) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 0 HP INq ltac:(lia) ltac:(lia)) as SHQ.
replace (q / 8 + 4 * Z.of_nat depth + 0 + A_SB) with (q / 8 + 4 * Z.of_nat depth + A_SB) in SHQ by lia.
assert (Hb8 : bse mod 8 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
assert (SHQ4 : ro_cells asegs m (bse / 8 + A_SB) [C1 (Z_to_bv 8 0)]).
{ replace (bse / 8) with (q / 8 + 4 * Z.of_nat depth) by (subst bse; rewrite div8_add_mul32 by lia; lia). exact SHQ. }
pose proof (munch_refl [(bse, bse + 32)] m) as MU.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
unfold APE_BREAK, APE_REDO, APE_OUT, APE_ERRMEM, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
pose proof (tok_flags_byteA mxd 0 m tk pb (Z.of_nat depth) q (TS isd stpos (Z_to_bv 64 co) err ucs high quote) TOK) as RDF.
stash Himg_t. stash Himg_q. clear PB REST TSK LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin Ld MU.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_rechkB.
step. step.
rewrite ?zxb_zero.
step.
step.
if_true.
evt_done5.
eapply (start_quote_A (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 l cb nb pj sv errv T); [exact STC | exact INV0 | exact Hl | exact Hst | exact Kadv].
Qed.
End PeSStartQA.
End RC__1.
End Mqd.

Module Mqe.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QRUw.Mq2 QmZZ. Import QPZI.Mq4. Import QkMG. Import QG8z Qdyh.Mq0.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QlKV.Mqf QlKV.Mqc QlKV.Mqh QSHS Ql4f.Mq4 QsKa.Mqh QrQv.Mq4 QEUF.Mq2 QnDr.Mq5 QdGy.Mqe.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSWinCallA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.

Lemma pe_get_w :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (p : Z) (s : option jshape) (BS : list blk)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (Q : machine_state -> Prop)
(ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts p s BS 1 cb nb pj sv errv ->
(forall m2 (a1' a2' a3' : word),
PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m2 md A B ts p s BS 2 cb nb pj sv errv ->
(forall b, PBOKat m ts b -> PBOKat m2 ts b) ->
evt asegs Q (MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1' a2' a3' a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m2 (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9bd5c) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC WIN K.
pose proof WIN as (CORE & BASE & LVo & CUR & Eobj & PP). pose proof BASE as (HP & ST & ERR & _).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof alloc_ceiling_range as ACR.
assert (PBT : forall m2, agree_on asegs (pe_blocksA pf q LB0 ts) m m2 -> forall b, PBOKat m ts b -> PBOKat m2 ts b).
{ intros m2 AG b PBK. eapply PBOKat_agree; [exact PBK | exact AG |]. unfold pe_blocksA, tstate_blocks. intros x Hx. apply in_or_app; left. apply in_or_app; left. exact Hx. }
destruct s as [s'|].
- destruct PP as (Hp & _ & J).
set (LBall := pe_blocksA pf q LB0 (tsF ts BS)) in *.
pose proof (perm_blocks_tsF pf q LB0 ts BS Eobj) as PERM. fold LBall in PERM.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND.
assert (NDp : List.NoDup (map blk_addr ((BS ++ pe_blocksA pf q LB0 ts) ++ LM))).
{ eapply Permutation_NoDup; [| exact ND]. apply Permutation_map. apply Permutation_app_tail. exact PERM. }
assert (NDbs : List.NoDup (map blk_addr BS)).
{ rewrite <- app_assoc, map_app in NDp. exact (NoDup_app_remove_r _ _ NDp). }
destruct (jval_hdr asegs A4F s' m BS p 1 J NDbs) as (n & tojs & pb' & udel & ud & rest & INc & SZ & N48 & HDR & CLOSE).
assert (INall : forall a k, In (a, k) BS -> In (a, k) LBall).
{ intros a k Hin. eapply Permutation_in; [apply Permutation_sym; exact PERM | apply in_or_app; left; exact Hin]. }
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p n HP (in_or_app _ LM _ (or_introl (INall p n INc)))) as (Hn0 & Hpal & Hp0 & Hphi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ p n HP (in_or_app _ LM _ (or_introl (INall p n INc)))) as Himg_p. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Himg_p.
destruct (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as (GOT & CELL).
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ p n HP (INall p n INc)) as SHB. unfold shad in SHB. cbn [hl_sb A4L] in SHB.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ p n ((n + 7) / 8 - 1) p n HP (INall p n INc) ltac:(clear - N48; Z.div_mod_to_equations; lia) (in_or_app _ LM _ (or_introl (INall p n INc)))) as (SEPc & _ & _).
cbn [hl_sb A4L] in SEPc.
destruct (proj1 (rw_cells_app asegs m p _ _) HDR) as [HDRh HDRr]. cbn [cells_size csize jhdr_cells Nat.add] in HDRr.
assert (SZr : 40 + Z.of_nat (cells_size rest) = n) by (rewrite cells_size_app, Nat2Z.inj_add in SZ; cbn [cells_size csize jhdr_cells Nat.add] in SZ; lia).
assert (Hsbc : 65536 <= hl_sb_cell A4L /\ hl_sb_cell A4L + 8 <= 6582272) by (vm_compute; split; intros X; discriminate X).
assert (SPF : lo <= pf_spf pf - 16 /\ 0 <= pf_spf pf < 2^62) by lia.
eapply evt_cut.
{ eapply (jo_get_A) with (lo := lo) (n := n) (sbcell := hl_sb_cell A4L);
[ exact HDRh | exact Hp0 | lia | exact Hpal | lia | lia | exact MI | rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; lia | exact LO | lia
| exact GOT | exact CELL | lia | lia | lia | | lia | exact SHB ].
clear - SEPc. lia. }
intros ms1 (m2 & (w & x & y & ->) & MU & WM & MI2 & HDR2 & ST2).
rewrite (unsigned_lit (pf_spf pf)) in MU, ST2 by lia.
assert (PP2 : put_pre A4H A4F (Some s') m2 BS p 2).
{ split; [exact Hp|]. split; [lia|]. apply (CLOSE m2 2).
- apply (proj2 (rw_cells_app asegs m2 p _ _)). split; [exact HDR2|]. cbn [cells_size csize jhdr_cells Nat.add].
eapply rw_cells_transport; [exact HDRr | exact MU | exact WM |]. cbn [disjoint_from fst snd]. lia.
- eapply (agree_others_gen asegs); [exact MU | exact WM |]. intros a k Hin Hne.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a k p n HP (in_or_app _ LM _ (or_introl (INall a k Hin))) (in_or_app _ LM _ (or_introl (INall p n INc))) Hne) as DJ.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP (in_or_app _ LM _ (or_introl (INall a k Hin)))) as (Hk0 & _ & _ & Hahi & _).
cbn [disjoint_from fst snd]. lia. }
destruct (PE_WIN_munchG HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md A B ts p (Some s') BS 1 2 cb nb pj sv errv _ STC WIN MU WM MI2
ltac:(apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_cons; [right; exists p, n; split; [exact INc | cbn [fst snd]; lia] | apply Forall_nil]]) ST2 PP2) as [WIN2 AG].
exact (K m2 w x y WIN2 (PBT m2 AG)).
- destruct PP as (Ep & EBS). subst p BS.
assert (SPF : lo <= pf_spf pf - 16 /\ 0 <= pf_spf pf < 2^62) by lia.
eapply evt_cut.
{ eapply (jo_get_null_A) with (lo := lo); [exact MI | rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; lia]. }
intros ms1 (m2 & (w & x & y & ->) & MU & WM & MI2 & ST2).
rewrite (unsigned_lit (pf_spf pf)) in MU, ST2 by lia.
destruct (PE_WIN_munchG HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md A B ts 0 None [] 1 2 cb nb pj sv errv _ STC WIN MU WM MI2
ltac:(apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]) ST2 ltac:(split; reflexivity)) as [WIN2 AG].
exact (K m2 w x y WIN2 (PBT m2 AG)).
Qed.

Hypothesis PUT : put_stmt_A HIx.

Hypothesis NEWARR : jo_new_array_A3 HIx.

Lemma pe_new_array_w :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP v2 ra2 : Z)
(ra gp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts 0 None [] 1 cb nb pj sv errv ->
PBOKat m ts kP -> new_array_costA <= bB B ->
pe_s0 sv = Z_to_bv 64 v2 -> pe_ra sv = Z_to_bv 64 ra2 ->
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64 ->
uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0xa0770) (UWfp ra2 v2) ->
bv_unsigned ra mod 2 = 0 ->
(forall m2 md2 A2 B2 errv2 (r : Z) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) F2 fc2,
((r = 0 /\ PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts 0 None [] 1 cb nb pj sv errv2) \/
(r <> 0 /\ exists BS, arr_capA BS = 32 /\ length BS = 3%nat /\ 0 < r < 2^62 /\ PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts r (Some (Sarr [])) BS 1 cb nb pj sv errv2)) ->
PBOKat m2 ts kP -> bB B - new_array_costA <= bB B2 -> bD B <= bD B2 ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 r) w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F2 (ret_pc ra) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xa074c) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC WIN PBK COST S0V RAV HV UWK RA K.
pose proof WIN as (CORE & BASE & LVo & CUR & Eobj & PP). pose proof BASE as (HP1 & ST1 & ERR1 & _).
pose proof CORE as (_ & _ & _ & _ & _ & _ & _ & _ & FR1).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
assert (SPF : lo <= pf_spf pf - (32 + 32 + 4096) /\ pf_spf pf mod 16 = 0 /\ pf_spf pf <= hiA_top A4L HIx /\ 0 <= pf_spf pf < 2^62 /\ 0 <= pa_sp0 pa < 2^63).
{ clear - LOS HT Gle Gspf SP0. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; lia. }
destruct SPF as (SPF1 & SPF2 & SPF3 & SPF4 & SPF5).
set (RB := pe_blocksA pf q LB0 ts) in *.
assert (Eq0 : pe_blocksA pf q LB0 (tsF ts []) = RB) by (unfold RB, pe_blocksA, tstate_blocks, tsF; cbn [t_pbs t_objbs t_levels]; rewrite Eobj; reflexivity).
rewrite Eq0 in HP1.
pose proof (pe_uw_at HIx pf pa lo m cb nb pj sv v2 ra2 STC FR1 S0V RAV (proj1 HV) (proj2 HV)) as UWA.
unfold jo_new_array_A3, jo_new_container_A_stmt in NEWARR.
eapply NEWARR with (LB := RB) (lo := lo) (errv := errv) (u := UWfp ra2 v2);
[ split; [exact HP1|]; split; [rewrite unsigned_lit by lia; exact ST1|]; split; [exact LO|]; split; [rewrite unsigned_lit by lia; exact SPF1|];
split; [rewrite unsigned_lit by lia; exact SPF2|]; split; [rewrite unsigned_lit by lia; exact SPF3|]; split; [exact ERR1|]; split; [reflexivity | exact RA]
| exact I | rewrite !unsigned_lit by lia; exact UWA | exact UWK | exact COST | cbn [uw_cost]; pose proof (proj2 (heapA_budget A4L HIx _ _ _ _ _ _ _ HP1)); lia | ].
intros ms2 md2 m2 r A2 B2 (RS2 & VM2 & ST2 & HPR2 & (errv2 & ERR2)) HB2 HD2 OUT2.
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp hla_base A4L A4H uw_cost] in *. rewrite ?(unsigned_lit (pf_spf pf)) in ST2 by lia. rewrite ?(unsigned_lit (pf_spf pf)) in HPR2 by lia.
assert (HPRc : heap_pres A4H (RB ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m m2) by exact HPR2.
assert (AG : agree_on asegs RB m m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPRc | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
eapply (K m2 md2 A2 B2 errv2 r); [| | lia | lia | exact FS2 | exact FRM2].
- destruct OUT2 as [(-> & HP2) | (Hr & BS & J2 & (CAP & LEN3) & HP2)].
+ left. split; [reflexivity|].
eapply (PE_WIN_callG2 HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B B2 ts 0 None [] 1 0 None [] 1 cb nb pj sv errv errv2);
[exact STC | exact WIN | exact VM2 | exact HPRc | rewrite Eq0; exact HP2 | exact ST2 | exact ERR2 | split; reflexivity].
+ right. split; [exact Hr|]. exists BS. split; [exact CAP|]. split; [exact LEN3|].
split.
{ destruct (arr_capA_jval _ _ _ _ _ J2) as (a0' & arr0 & rest0 & EBS & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r 48 HP2 ltac:(apply in_or_app; left; apply in_or_app; left; rewrite EBS; left; reflexivity)) as (_ & _ & Hr0 & Hrhi & _).
pose proof alloc_ceiling_range. lia. }
eapply (PE_WIN_callG2 HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B B2 ts 0 None [] 1 r (Some (Sarr [])) BS 1 cb nb pj sv errv errv2);
[exact STC | exact WIN | exact VM2 | exact HPRc | | exact ST2 | exact ERR2 | split; [exact Hr | split; [lia | exact J2]]].
eapply (heapA_perm A4L HIx); [exact HP2 | apply Permutation_sym; apply (perm_blocks_tsF pf q LB0 ts BS Eobj) | apply Permutation_refl | apply Permutation_refl].
- eapply PBOKat_agree; [exact PBK | exact AG |]. unfold RB, pe_blocksA, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb.
Qed.
End PeSWinCallA.
End RC__1.
End Mqe.

Module Mqf.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QRUw.Mq2 QmZZ. Import QPZI.Mq4. Import QkMG. Import QG8z Qdyh.Mq0.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QlKV.Mqf QlKV.Mqc QlKV.Mqh QsKa.Mqe QSHS Ql4f.Mq4 QsKa.Mqh QrQv.Mq4 QEUF.Mq2 Qmgs.Mq0 QdGy.Mqe.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSWinCallOA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis GA_lh : forall m, GA m -> lh_globA m.
Hypothesis NEWOBJ : jo_new_object_A3_stmt HIx.

Lemma pe_new_object_w :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP v2 ra2 : Z)
(ra gp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts 0 None [] 1 cb nb pj sv errv ->
PBOKat m ts kP -> newobj_costB <= bB B ->
pe_s0 sv = Z_to_bv 64 v2 -> pe_ra sv = Z_to_bv 64 ra2 ->
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64 ->
uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9d38c) (UWfp ra2 v2) ->
bv_unsigned ra mod 2 = 0 ->
(forall m2 md2 A2 B2 errv2 (r : Z) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) F2 fc2,
((r = 0 /\ PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts 0 None [] 1 cb nb pj sv errv2) \/
(r <> 0 /\ exists BS, obj_capA BS = 16 /\ length BS = 3%nat /\ 0 < r < 2^62 /\ PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts r (Some (Sobj [])) BS 1 cb nb pj sv errv2)) ->
PBOKat m2 ts kP -> bB B - newobj_costB <= bB B2 -> bD B <= bD B2 ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 r) w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F2 (ret_pc ra) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9d360) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC WIN PBK COST S0V RAV HV UWK RA K.
pose proof WIN as (CORE & BASE & LVo & CUR & Eobj & PP). pose proof BASE as (HP1 & ST1 & ERR1 & _ & _ & _ & _ & _ & G1).
pose proof CORE as (_ & _ & _ & _ & _ & _ & _ & _ & FR1).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
assert (SPF : lo <= pf_spf pf - 48 - 48 - 4096 /\ pf_spf pf mod 16 = 0 /\ pf_spf pf <= hiA_top A4L HIx /\ 0 <= pf_spf pf < 2^62 /\ 0 <= pa_sp0 pa < 2^63).
{ clear - LOS HT Gle Gspf SP0. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; lia. }
destruct SPF as (SPF1 & SPF2 & SPF3 & SPF4 & SPF5).
set (RB := pe_blocksA pf q LB0 ts) in *.
assert (Eq0 : pe_blocksA pf q LB0 (tsF ts []) = RB) by (unfold RB, pe_blocksA, tstate_blocks, tsF; cbn [t_pbs t_objbs t_levels]; rewrite Eobj; reflexivity).
rewrite Eq0 in HP1.
pose proof (pe_uw_at HIx pf pa lo m cb nb pj sv v2 ra2 STC FR1 S0V RAV (proj1 HV) (proj2 HV)) as UWA.
unfold jo_new_object_A3_stmt in NEWOBJ.
eapply NEWOBJ with (LB := RB) (lo := lo) (errv := errv) (u := UWfp ra2 v2);
[ exact HP1 | exact (GA_lh _ G1) | rewrite !unsigned_lit by lia; exact UWA | exact UWK | rewrite unsigned_lit by lia; exact ST1 | exact LO | rewrite unsigned_lit by lia; exact SPF1
| rewrite unsigned_lit by lia; exact SPF2 | rewrite unsigned_lit by lia; exact SPF3 | exact ERR1 | reflexivity | exact RA | exact COST
| cbn [uw_cost]; exact (proj2 (heapA_budget A4L HIx _ _ _ _ _ _ _ HP1)) | ].
intros ms2 md2 A2 (m2 & r & errv2 & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & G2 & HB2 & HD2 & OUT2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp hla_base A4L A4H uw_cost] in *. rewrite ?(unsigned_lit (pf_spf pf)) in ST2 by lia. rewrite ?(unsigned_lit (pf_spf pf)) in HPR2 by lia.
assert (HPRc : heap_pres A4H (RB ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m m2) by exact HPR2.
assert (AG : agree_on asegs RB m m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPRc | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
eapply (K m2 md2 A2 B2 errv2 r); [| | lia | cbn [uw_cost] in HD2; lia | exact FS2 | exact FRM2].
- destruct OUT2 as [(-> & HP2) | (Hr & BS & J2 & LEN3 & CAP & HP2)].
+ left. split; [reflexivity|].
eapply (PE_WIN_callG2 HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B B2 ts 0 None [] 1 0 None [] 1 cb nb pj sv errv errv2);
[exact STC | exact WIN | exact VM2 | exact HPRc | rewrite Eq0; exact HP2 | exact ST2 | exact ERR2 | split; reflexivity].
+ right. split; [exact Hr|]. exists BS. split; [exact CAP|]. split; [exact LEN3|].
split.
{ assert (NDb : List.NoDup (map blk_addr BS)).
{ pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP2) as ND. rewrite <- app_assoc, map_app in ND. exact (NoDup_app_remove_r _ _ ND). }
destruct (jval_hdr asegs A4F _ _ _ _ _ J2 NDb) as (n0 & _ & _ & _ & _ & _ & INr & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r n0 HP2 ltac:(apply in_or_app; left; apply in_or_app; left; exact INr)) as (Hn0 & _ & Hr0 & Hrhi & _).
pose proof alloc_ceiling_range. lia. }
eapply (PE_WIN_callG2 HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B B2 ts 0 None [] 1 r (Some (Sobj [])) BS 1 cb nb pj sv errv errv2);
[exact STC | exact WIN | exact VM2 | exact HPRc | | exact ST2 | exact ERR2 | split; [exact Hr | split; [lia | exact J2]]].
eapply (heapA_perm A4L HIx); [exact HP2 | apply Permutation_sym; apply (perm_blocks_tsF pf q LB0 ts BS Eobj) | apply Permutation_refl | apply Permutation_refl].
- eapply PBOKat_agree; [exact PBK | exact AG |]. unfold RB, pe_blocksA, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb.
Qed.
End PeSWinCallOA.
End RC__1.
End Mqf.

Module Mqg.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QRUw.Mq2 QmZZ. Import QPZI.Mq4. Import QkMG. Import QG8z Qdyh.Mq0.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QlKV.Mqf QlKV.Mqc QlKV.Mqh Q6oO.Mq1 QJZd.Mqa QSHS Ql4f.Mq4 QsKa.Mqh QrQv.Mq4 QEUF.Mq2 QdGy.Mqe.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QlKV.Mq2. Import QEUF.Mq3.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma jval_scalar_blocks : forall s m BS p rc, jval asegs A4F s m BS p rc -> s = Sbool \/ s = Sdouble false ->
In (p, 48) BS /\ (length BS <= 3)%nat.
Proof.
intros s m BS p rc J Hs.
assert (X : exists pb PBS, BS = [(p, 48)] ++ PBS /\ opt_pbuf asegs m PBS pb).
{ destruct Hs as [-> | ->]; cbn [jval] in J; destruct J as (pb & PBS & REST & E & OP & J).
- destruct J as (b & junk & -> & _). exists pb, PBS. split; [exact E | exact OP].
- destruct J as (bits & -> & _). exists pb, PBS. split; [exact E | exact OP]. }
destruct X as (pb & PBS & -> & OP). split; [left; reflexivity|].
destruct OP as [[_ ->] | [_ (buf & bpos & size & content & -> & _)]]; cbn; lia.
Qed.

Definition jo_new_double_A_stmt (HIx : heap_iface_A A4L) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word) (u : uwd),
HEAPA A4L HIx A LB LM FRS B m md ->
uw_at (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9f3fc) u ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP ->
bv_unsigned ra mod 2 = 0 ->
newdbl_costB <= bB B -> uw_cost u <= bD B ->
dbl_special (Sem.reg_get F (Z_to_bv 5 10)) ->
(forall ms' md' A', Q6oO.Mq1.new_obj_A_post HIx (Sdouble false) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo u ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 json_object_new_double_A_entry) fc None m (seg_rom asegs)).

Definition jo_new_boolean_A_stmt (HIx : heap_iface_A A4L) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word),
HEAPA A4L HIx A LB LM FRS B m md ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP ->
bv_unsigned ra mod 2 = 0 ->
bv_unsigned a0 <= 1 ->
newbool_costB <= bB B -> 0 <= bD B ->
(forall ms' md' A', QJZd.Mqa.new_obj_A_post HIx Sbool ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 json_object_new_boolean_A_entry) fc None m (seg_rom asegs)).

Definition new_scalar_costA : Z := 16 * 48 + 512.

Section PeSWinCallSA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis NEWDBL : jo_new_double_A_stmt HIx.
Hypothesis NEWBOOL : jo_new_boolean_A_stmt HIx.

Lemma pe_new_double_w :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP v2 ra2 : Z)
(ra gp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts 0 None [] 1 cb nb pj sv errv ->
PBOKat m ts kP -> new_scalar_costA <= bB B ->
pe_s0 sv = Z_to_bv 64 v2 -> pe_ra sv = Z_to_bv 64 ra2 ->
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64 ->
uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9f3fc) (UWfp ra2 v2) ->
dbl_special (Sem.reg_get F (Z_to_bv 5 10)) ->
bv_unsigned ra mod 2 = 0 ->
(forall m2 md2 A2 B2 errv2 (r : Z) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) F2 fc2,
((r = 0 /\ PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts 0 None [] 1 cb nb pj sv errv2) \/
(r <> 0 /\ exists BS, (length BS <= 3)%nat /\ jfresh (Sdouble false) BS 9 /\ 0 < r < 2^62 /\ PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts r (Some (Sdouble false)) BS 1 cb nb pj sv errv2)) ->
PBOKat m2 ts kP -> bB B - new_scalar_costA <= bB B2 -> bD B <= bD B2 ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 r) w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F2 (ret_pc ra) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 json_object_new_double_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC WIN PBK COST S0V RAV HV UWK DBL RA K.
pose proof WIN as (CORE & BASE & LVo & CUR & Eobj & PP). pose proof BASE as (HP1 & ST1 & ERR1 & _).
pose proof CORE as (_ & _ & _ & _ & _ & _ & _ & _ & FR1).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
assert (SPF : lo <= pf_spf pf - 48 - 4096 /\ pf_spf pf mod 16 = 0 /\ pf_spf pf <= hiA_top A4L HIx /\ 0 <= pf_spf pf < 2^62 /\ 0 <= pa_sp0 pa < 2^63).
{ clear - LOS HT Gle Gspf SP0. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; lia. }
destruct SPF as (SPF1 & SPF2 & SPF3 & SPF4 & SPF5).
set (RB := pe_blocksA pf q LB0 ts) in *.
assert (Eq0 : pe_blocksA pf q LB0 (tsF ts []) = RB) by (unfold RB, pe_blocksA, tstate_blocks, tsF; cbn [t_pbs t_objbs t_levels]; rewrite Eobj; reflexivity).
rewrite Eq0 in HP1.
pose proof (pe_uw_at HIx pf pa lo m cb nb pj sv v2 ra2 STC FR1 S0V RAV (proj1 HV) (proj2 HV)) as UWA.
eapply (NEWDBL ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m md T A RB LM ((pa_F pa, 2) :: FRS) B lo errv (UWfp ra2 v2));
[ exact HP1 | rewrite !unsigned_lit by lia; exact UWA | exact UWK | rewrite unsigned_lit by lia; exact ST1 | exact LO | rewrite unsigned_lit by lia; exact SPF1
| rewrite unsigned_lit by lia; exact SPF2 | rewrite unsigned_lit by lia; exact SPF3 | exact ERR1 | reflexivity | exact RA
| unfold newdbl_costB; unfold new_scalar_costA in COST; exact COST | cbn [uw_cost]; pose proof (proj2 (heapA_budget A4L HIx _ _ _ _ _ _ _ HP1)); lia | exact DBL | ].
intros ms2 md2 A2 (m2 & r & errv2 & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & HB2 & HD2 & OUT2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp hla_base A4L A4H uw_cost] in *. rewrite ?(unsigned_lit (pf_spf pf)) in ST2 by lia. rewrite ?(unsigned_lit (pf_spf pf)) in HPR2 by lia.
assert (HPRc : heap_pres A4H (RB ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m m2) by exact HPR2.
assert (AG : agree_on asegs RB m m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPRc | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
eapply (K m2 md2 A2 B2 errv2 r); [| | unfold newdbl_costB in HB2; unfold new_scalar_costA; lia | lia | exact FS2 | exact FRM2].
- destruct OUT2 as [(-> & HP2) | (Hr & BS & J2 & HP2 & L1)].
+ left. split; [reflexivity|].
eapply (PE_WIN_callG2 HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B B2 ts 0 None [] 1 0 None [] 1 cb nb pj sv errv errv2);
[exact STC | exact WIN | exact VM2 | exact HPRc | rewrite Eq0; exact HP2 | exact ST2 | exact ERR2 | split; reflexivity].
+ right. split; [exact Hr|]. exists BS.
destruct (jval_scalar_blocks _ _ _ _ _ J2 (or_intror eq_refl)) as [INr LEN3].
split; [exact LEN3|]. split; [exact (jfresh_dbl asegs A4F _ _ _ _ J2 L1)|]. split.
{ pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r 48 HP2 ltac:(apply in_or_app; left; apply in_or_app; left; exact INr)) as (_ & _ & Hr0 & Hrhi & _).
pose proof alloc_ceiling_range. lia. }
eapply (PE_WIN_callG2 HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B B2 ts 0 None [] 1 r (Some (Sdouble false)) BS 1 cb nb pj sv errv errv2);
[exact STC | exact WIN | exact VM2 | exact HPRc | | exact ST2 | exact ERR2 | split; [exact Hr | split; [lia | exact J2]]].
eapply (heapA_perm A4L HIx); [exact HP2 | apply Permutation_sym; apply (perm_blocks_tsF pf q LB0 ts BS Eobj) | apply Permutation_refl | apply Permutation_refl].
- eapply PBOKat_agree; [exact PBK | exact AG |]. unfold RB, pe_blocksA, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb.
Qed.

Lemma pe_new_boolean_w :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP bval : Z)
(ra gp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts 0 None [] 1 cb nb pj sv errv ->
PBOKat m ts kP -> new_scalar_costA <= bB B ->
0 <= bval <= 1 ->
bv_unsigned ra mod 2 = 0 ->
(forall m2 md2 A2 B2 errv2 (r : Z) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) F2 fc2,
((r = 0 /\ PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts 0 None [] 1 cb nb pj sv errv2) \/
(r <> 0 /\ exists BS, (length BS <= 3)%nat /\ jfresh Sbool BS 8 /\ 0 < r < 2^62 /\ PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts r (Some Sbool) BS 1 cb nb pj sv errv2)) ->
PBOKat m2 ts kP -> bB B - new_scalar_costA <= bB B2 -> bD B <= bD B2 ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 r) w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F2 (ret_pc ra) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 bval) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 json_object_new_boolean_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC WIN PBK COST HB01 RA K.
pose proof WIN as (CORE & BASE & LVo & CUR & Eobj & PP). pose proof BASE as (HP1 & ST1 & ERR1 & _).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
assert (SPF : lo <= pf_spf pf - 32 - 4096 /\ pf_spf pf mod 16 = 0 /\ pf_spf pf <= hiA_top A4L HIx /\ 0 <= pf_spf pf < 2^62 /\ 0 <= pa_sp0 pa < 2^63).
{ clear - LOS HT Gle Gspf SP0. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; lia. }
destruct SPF as (SPF1 & SPF2 & SPF3 & SPF4 & SPF5).
set (RB := pe_blocksA pf q LB0 ts) in *.
assert (Eq0 : pe_blocksA pf q LB0 (tsF ts []) = RB) by (unfold RB, pe_blocksA, tstate_blocks, tsF; cbn [t_pbs t_objbs t_levels]; rewrite Eobj; reflexivity).
rewrite Eq0 in HP1.
eapply (NEWBOOL ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 bval) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m md T A RB LM ((pa_F pa, 2) :: FRS) B lo errv);
[ exact HP1 | rewrite unsigned_lit by lia; exact ST1 | exact LO | rewrite unsigned_lit by lia; exact SPF1
| rewrite unsigned_lit by lia; exact SPF2 | rewrite unsigned_lit by lia; exact SPF3 | exact ERR1 | reflexivity | exact RA
| rewrite unsigned_lit by lia; lia
| unfold newbool_costB; unfold new_scalar_costA in COST; exact COST | pose proof (proj2 (heapA_budget A4L HIx _ _ _ _ _ _ _ HP1)); lia | ].
intros ms2 md2 A2 (m2 & r & errv2 & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & HB2 & HD2 & OUT2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp hla_base A4L A4H] in *. rewrite ?(unsigned_lit (pf_spf pf)) in ST2 by lia. rewrite ?(unsigned_lit (pf_spf pf)) in HPR2 by lia.
assert (HPRc : heap_pres A4H (RB ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m m2) by exact HPR2.
assert (AG : agree_on asegs RB m m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPRc | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
eapply (K m2 md2 A2 B2 errv2 r); [| | unfold newbool_costB in HB2; unfold new_scalar_costA; lia | lia | exact FS2 | exact FRM2].
- destruct OUT2 as [(-> & HP2) | (Hr & BS & J2 & HP2 & L1)].
+ left. split; [reflexivity|].
eapply (PE_WIN_callG2 HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B B2 ts 0 None [] 1 0 None [] 1 cb nb pj sv errv errv2);
[exact STC | exact WIN | exact VM2 | exact HPRc | rewrite Eq0; exact HP2 | exact ST2 | exact ERR2 | split; reflexivity].
+ right. split; [exact Hr|]. exists BS.
destruct (jval_scalar_blocks _ _ _ _ _ J2 (or_introl eq_refl)) as [INr LEN3].
split; [exact LEN3|]. split; [exact (jfresh_bool asegs A4F _ _ _ _ J2 L1)|]. split.
{ pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r 48 HP2 ltac:(apply in_or_app; left; apply in_or_app; left; exact INr)) as (_ & _ & Hr0 & Hrhi & _).
pose proof alloc_ceiling_range. lia. }
eapply (PE_WIN_callG2 HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B B2 ts 0 None [] 1 r (Some Sbool) BS 1 cb nb pj sv errv errv2);
[exact STC | exact WIN | exact VM2 | exact HPRc | | exact ST2 | exact ERR2 | split; [exact Hr | split; [lia | exact J2]]].
eapply (heapA_perm A4L HIx); [exact HP2 | apply Permutation_sym; apply (perm_blocks_tsF pf q LB0 ts BS Eobj) | apply Permutation_refl | apply Permutation_refl].
- eapply PBOKat_agree; [exact PBK | exact AG |]. unfold RB, pe_blocksA, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb.
Qed.
End PeSWinCallSA.
End RC__1.
End Mqg.

Module Mqh.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QRUw.Mq2 QmZZ. Import QPZI.Mq4. Import QkMG. Import QG8z Qdyh.Mq0.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QlKV.Mqf QlKV.Mqc QlKV.Mqh Q6oO.Mq2 QSHS Ql4f.Mq4 QsKa.Mqh QrQv.Mq4 QEUF.Mq2 QdGy.Mqe.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition jo_new_string_len_A_stmt (HIx : heap_iface_A A4L) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (sb nsb s len lo : Z) (src : list byte) (errv : word) (u : uwd),
HEAPA A4L HIx A LB LM FRS B m md ->
uw_at (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0xa00d4) u ->
In (sb, nsb) LB -> sb <= s -> s + len <= sb + nsb ->
bytes_at asegs m s src -> Z.of_nat (length src) = len -> 0 <= len < 2^31 ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 len ->
newstr_costB len <= bB B -> uw_cost u <= bD B ->
(forall ms' md' A', Q6oO.Mq2.new_str_A_post HIx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B len lo u ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 json_object_new_string_len_A_entry) fc None m (seg_rom asegs)).

Section PeSWinCallTA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis NEWSTR : jo_new_string_len_A_stmt HIx.

Lemma pe_new_string_w :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP v2 ra2 buf cap bpos : Z) (content : list byte)
(ra gp t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts 0 None [] 1 cb nb pj sv errv ->
PBOKat m ts kP ->
t_pbs ts = [(t_pb ts, PB_SZ); (buf, cap)] -> pbuf_core asegs m (t_pb ts) buf bpos cap content ->
newstr_costB bpos <= bB B ->
pe_s0 sv = Z_to_bv 64 v2 -> pe_ra sv = Z_to_bv 64 ra2 ->
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64 ->
uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0xa00d4) (UWfp ra2 v2) ->
bv_unsigned ra mod 2 = 0 ->
(forall m2 md2 A2 B2 errv2 (r : Z) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) F2 fc2,
((r = 0 /\ PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts 0 None [] 1 cb nb pj sv errv2) \/
(r <> 0 /\ 0 < r < 2^62 /\ PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts r (Some (Sstr false)) [(r, str_objsize bpos)] 1 cb nb pj sv errv2)) ->
PBOKat m2 ts kP -> bB B - newstr_costB bpos <= bB B2 -> bD B <= bD B2 ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 r) w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F2 (ret_pc ra) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 buf) (Z_to_bv 64 bpos) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 json_object_new_string_len_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC WIN PBK Epbs PBC COST S0V RAV HV UWK RA K.
pose proof WIN as (CORE & BASE & LVo & CUR & Eobj & PP). pose proof BASE as (HP1 & ST1 & ERR1 & _).
pose proof CORE as (_ & _ & _ & _ & _ & _ & _ & _ & FR1).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
assert (SPF : lo <= pf_spf pf - 48 - 4096 /\ pf_spf pf mod 16 = 0 /\ pf_spf pf <= hiA_top A4L HIx /\ 0 <= pf_spf pf < 2^62 /\ 0 <= pa_sp0 pa < 2^63).
{ clear - LOS HT Gle Gspf SP0. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; lia. }
destruct SPF as (SPF1 & SPF2 & SPF3 & SPF4 & SPF5).
set (RB := pe_blocksA pf q LB0 ts) in *.
assert (Eq0 : pe_blocksA pf q LB0 (tsF ts []) = RB) by (unfold RB, pe_blocksA, tstate_blocks, tsF; cbn [t_pbs t_objbs t_levels]; rewrite Eobj; reflexivity).
rewrite Eq0 in HP1.
pose proof (pe_uw_at HIx pf pa lo m cb nb pj sv v2 ra2 STC FR1 S0V RAV (proj1 HV) (proj2 HV)) as UWA.
destruct PBC as (Hbp & Hcap & Hlen & _ & BUFC).
pose proof (rw_cells_bytes_at' _ _ _ _ BUFC) as BUFB. cbn [cells_bytes cbytes] in BUFB. rewrite app_nil_r in BUFB.
pose proof (bytes_at_sub A4H m buf content 0%nat (Z.to_nat bpos) BUFB ltac:(lia)) as SRC. cbn [hl_segs hla_base A4L A4H skipn Z.of_nat] in SRC. rewrite Z.add_0_r in SRC.
assert (INbuf : In (buf, cap) RB) by (unfold RB, pe_blocksA, tstate_blocks; rewrite Epbs; apply in_or_app; left; cbn [app]; right; left; reflexivity).
eapply (NEWSTR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 buf) (Z_to_bv 64 bpos) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m md T A RB LM ((pa_F pa, 2) :: FRS) B buf cap buf bpos lo (firstn (Z.to_nat bpos) content) errv (UWfp ra2 v2));
[ exact HP1 | rewrite !unsigned_lit by lia; exact UWA | exact UWK | exact INbuf | lia | lia | exact SRC | rewrite length_firstn; lia | lia
| rewrite unsigned_lit by lia; exact ST1 | exact LO | rewrite unsigned_lit by lia; exact SPF1
| rewrite unsigned_lit by lia; exact SPF2 | rewrite unsigned_lit by lia; exact SPF3 | exact ERR1 | reflexivity | exact RA | reflexivity | reflexivity
| exact COST | cbn [uw_cost]; pose proof (proj2 (heapA_budget A4L HIx _ _ _ _ _ _ _ HP1)); lia | ].
intros ms2 md2 A2 (m2 & r & errv2 & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & HB2 & HD2 & OUT2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp hla_base A4L A4H uw_cost] in *. rewrite ?(unsigned_lit (pf_spf pf)) in ST2 by lia. rewrite ?(unsigned_lit (pf_spf pf)) in HPR2 by lia.
assert (HPRc : heap_pres A4H (RB ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m m2) by exact HPR2.
assert (AG : agree_on asegs RB m m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPRc | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
eapply (K m2 md2 A2 B2 errv2 r); [| | lia | lia | exact FS2 | exact FRM2].
- destruct OUT2 as [(-> & HP2) | (Hr & J2 & HP2)].
+ left. split; [reflexivity|].
eapply (PE_WIN_callG2 HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B B2 ts 0 None [] 1 0 None [] 1 cb nb pj sv errv errv2);
[exact STC | exact WIN | exact VM2 | exact HPRc | rewrite Eq0; exact HP2 | exact ST2 | exact ERR2 | split; reflexivity].
+ right. split; [exact Hr|]. split.
{ pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r (str_objsize bpos) HP2 ltac:(apply in_or_app; left; left; reflexivity)) as (_ & _ & Hr0 & Hrhi & _).
pose proof alloc_ceiling_range. unfold str_objsize in Hrhi. lia. }
eapply (PE_WIN_callG2 HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B B2 ts 0 None [] 1 r (Some (Sstr false)) [(r, str_objsize bpos)] 1 cb nb pj sv errv errv2);
[exact STC | exact WIN | exact VM2 | exact HPRc | | exact ST2 | exact ERR2 | split; [exact Hr | split; [lia | exact J2]]].
eapply (heapA_perm A4L HIx); [exact HP2 | apply Permutation_sym; apply (perm_blocks_tsF pf q LB0 ts [(r, str_objsize bpos)] Eobj) | apply Permutation_refl | apply Permutation_refl].
- eapply PBOKat_agree; [exact PBK | exact AG |]. unfold RB, pe_blocksA, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb.
Qed.
End PeSWinCallTA.
End RC__1.
End Mqh.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUrr Q60A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqi.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun Qfw3_c1.Mq2.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0.
Import QnCn.Mq0.
Import QbFI.  Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqg QsKa.Mqc Q30W.Mq4 Q4v2 QgHv Q1Y6 QsKa.Mqf QUrr. Import QlKV.Mq2 QsKa. Import Q9O6.Mq5 QL3k.Mq4 Q228.Mqc. Import Qwm6.Mq1. Import QnPO.Mq4 Q228.Mqe Q228.Mq9. Import QlKV. Import QpNt.Mq8 Q60A.
Import QWxq_c1 QsjA.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).

Ltac post_callS segs m :=
let ms' := fresh "ms'" in let PO := fresh "POST" in
intros ms' PO;
destruct_exs PO;
let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
destruct PO as [E [MUc [WMc PO]]];
first [ destruct PO as [MIc PO] | rename PO into MIc ];
subst ms';
rewrite ?unsigned_lit in MUc by lia; try rewrite ?unsigned_lit in PO by lia;
lazymatch type of MUc with
| munch _ m ?m' =>
transport_after_call segs m m' MUc WMc;
clear MUc WMc;
try match goal with H : mem_inv segs m |- _ => clear H end;
try clear m
end;
try destruct_ands PO;
try (lazymatch goal with
| |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
end).
Tactic Notation "callS" uconstr(SPEC) :=
lazymatch goal with
| |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | post_callS segs m ]
end.

Ltac if_rw E b :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b by (rewrite E; vm_compute; reflexivity)
end; cbv iota.

Lemma land1_cases : forall fl, 0 <= fl -> Z.land fl 1 = 0 \/ Z.land fl 1 = 1.
Proof.
intros fl H. change 1 with (Z.ones 1) at 1. change 1 with (Z.ones 1) at 2. rewrite !Z.land_ones by lia.
change (2^1) with 2. pose proof (Z.mod_pos_bound fl 2 ltac:(lia)). lia.
Qed.
Lemma land58_bit : forall fl b, Z.land fl 58 = 0 -> Z.land 58 b = b -> Z.land fl b = 0.
Proof. intros fl b H Hb. rewrite <- Hb. rewrite Z.land_assoc, H. reflexivity. Qed.
Lemma land3_of_58 : forall fl, Z.land fl 58 = 0 -> Z.land fl 3 = Z.land fl 1.
Proof.
intros fl H. change 3 with (Z.lor 1 2). rewrite Z.land_lor_distr_r. rewrite (land58_bit fl 2 H eq_refl). apply Z.lor_0_r.
Qed.

Definition LIT_LBRACE : list byte := Eval vm_compute in lit_bytesA 0x23480 1.
Definition LIT_RBRACE : list byte := Eval vm_compute in lit_bytesA 0x235e0 1.
Definition LIT_SP_RBRACE : list byte := Eval vm_compute in lit_bytesA 0x235c0 2.
Definition LIT_COLON_SP : list byte := Eval vm_compute in lit_bytesA 0x23560 2.
Definition LIT_COLON : list byte := Eval vm_compute in lit_bytesA 0x23580 1.

Lemma land7_of_mod8S : forall p, 0 <= p -> p mod 8 = 0 -> Z.land p 7 = 0.
Proof. intros p Hp H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8. exact H. Qed.
Ltac ubsan_align8 H :=
lazymatch type of H with ?p mod 8 = 0 => rewrite ?(unsigned_lit p) by lia; rewrite (land7_of_mod8S p ltac:(lia) H); if_false end.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section ObjK.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Lemma blk_gran_at : forall A LBx LMx FR B m md a n x, HEAPAx A LBx LMx FR B m md -> In (a, n) LBx -> a <= x -> x + 8 <= a + n -> x mod 8 = 0 ->
ro_cells asegs m (x / 8 + 2147450880) [C1 (Z_to_bv 8 0)].
Proof.
intros A LBx LMx FR B m md a n x HP Hin Hax Hxn Hx8.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a n HP ltac:(apply in_or_app; left; exact Hin)) as (_ & Hal & _).
pose proof (blk_granS HIx _ _ _ _ _ _ _ a n ((x - a) / 8) HP Hin ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia)) as SH.
replace (a / 8 + 2147450880 + (x - a) / 8) with (x / 8 + 2147450880) in SH by (Z.div_mod_to_equations; lia). exact SH.
Qed.
End ObjK.

Section Obj.
Variable HIx : heap_iface_A A4L.
Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.
Hypothesis ESC : esc_specA HIx.

Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud).
Variables (pb lo p rc pb0 lv fl t tbl size bpos0 cap0 w : Z).
Variables (es : list oent) (KBS : list (list blk)) (kids : list (option jshape)) (T : TSet) (Y R : list blk).
Let usp := bv_unsigned sp.
Let TBS : list blk := (t, 56) :: (tbl, 40 * size) :: map (fun e => (oe_k e, oe_kn e)) es.
Hypothesis KIDS : forall s', In (Some s') kids -> ser_specA HIx (afn_of s') s'.
Hypothesis FL : aflags_ok fl.
Hypothesis Hlv : 0 <= lv.
Hypothesis Hlvd : lv + sdepth (Sobj kids) <= 1000.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= usp - ser_budgetA (Sobj kids).
Hypothesis SPA : usp mod 16 = 0.
Hypothesis HT : usp <= hiA_top A4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis CAP0 : 32 <= cap0 < 2^30.
Hypothesis TXT : bpos0 + w < 2^28.
Hypothesis NEED : ser_need cap0 bpos0 w <= bB B0.
Hypothesis JHEX0 : JHEX_A m0.
Hypothesis FRSN : Z.of_nat (length FRS) + 1 < 4096.
Hypothesis INCL : incl ((p, 48) :: TBS ++ concat KBS) LB.
Hypothesis NODE0 : rw_cells asegs m0 p (jhdr_cells JT_OBJECT rc (fn_obj_to_json_string A4F) pb0 0 0 ++ [C8 (wz t)]).
Hypothesis OT0 : otab asegs m0 TBS t es.
Hypothesis KOK : kids_okv asegs A4F m0 kids (map (fun e => (oe_k e, oe_v e)) es) KBS.
Hypothesis JTX : jtxk_obj kids (map (fun e => (oe_k e, oe_kn e)) es) (concat KBS ++ Y) 24 = Some (w, R).
Hypothesis K : forall ms' md' A', ser_postA HIx ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 pb cap0 bpos0 w lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms'.

Notation ser_memx := (ser_memA HIx sp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w).
Let LEN := Z.of_nat (length es).
Definition savedR : list cell := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma facts :
0 <= usp < 2^64 /\ In (p, 48) LB /\ 0 <= fl < 2^31 /\
Z.land fl 2 = 0 /\ Z.land fl 8 = 0 /\ Z.land fl 32 = 0 /\ Z.land fl 3 = Z.land fl 1 /\ (Z.land fl 1 = 0 \/ Z.land fl 1 = 1) /\
0 <= kdepth kids /\ lo <= usp - 224 - 256 * kdepth kids - 16384 - 32 /\
length es = length kids /\ length KBS = length kids /\ incl TBS LB.
Proof.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
assert (INp : In (p, 48) LB) by (apply INCL; left; reflexivity).
destruct FL as [Rfl FL58].
pose proof (kdepth_nonneg kids) as KD. unfold ser_budgetA, ASER_LEVEL, ASER_LEAF in LOS. rewrite sdepth_obj in LOS.
destruct (kids_okv_len _ _ _ _ _ _ KOK) as [L1 L2]. rewrite length_map in L1.
split; [exact SPR|]. split; [exact INp|]. split; [exact Rfl|].
split; [exact (land58_bit fl 2 FL58 eq_refl)|]. split; [exact (land58_bit fl 8 FL58 eq_refl)|]. split; [exact (land58_bit fl 32 FL58 eq_refl)|].
split; [exact (land3_of_58 fl FL58)|]. split; [apply land1_cases; lia|].
split; [exact KD|]. split; [unfold usp in *; lia|].
split; [exact L1|]. split; [exact L2|].
intros b Hb. apply INCL. right. apply in_or_app. left. exact Hb.
Qed.

Lemma factsM : forall A FA CH e m md, ser_memx A FRS FA CH e m md ->
0 < p /\ p + 48 <= alloc_ceiling /\ p mod 8 = 0 /\
rw_cells asegs m p (jhdr_cells JT_OBJECT rc (fn_obj_to_json_string A4F) pb0 0 0 ++ [C8 (wz t)]) /\
ro_cells asegs m (p / 8 + 2147450880) [C1 (Z_to_bv 8 0)] /\ ro_cells asegs m (p / 8 + 2147450885) [C1 (Z_to_bv 8 0)] /\
otab asegs m TBS t es /\
kids_okv asegs A4F m kids (map (fun e => (oe_k e, oe_v e)) es) KBS.
Proof.
intros A FA CH e m md (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & _).
pose proof facts as (SPR & INp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & INT).
assert (INp' : In (p, 48) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; exact INp).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p 48 HP ltac:(apply in_or_app; left; exact INp')) as (_ & Hpal & Hplo & Hphi & _).
assert (AG : agree_on asegs LB m0 m).
{ eapply (agree_of_heap_pres asegs A4H); [exact HPR | reflexivity |]. intros b Hb. apply in_or_app. left. exact Hb. }
split; [exact Hplo|]. split; [exact Hphi|]. split; [clear - Hpal; Z.div_mod_to_equations; lia|].
split. { eapply (heap_pres_rw_cells A4H); [exact HPR | exact NODE0 |]. eapply client_range_block; [apply in_or_app; left; exact INp | lia | cbn; lia]. }
split. { pose proof (blk_granS HIx _ _ _ _ _ _ _ p 48 0 HP INp' ltac:(lia) ltac:(lia)) as SH0. rewrite Z.add_0_r in SH0. exact SH0. }
split. { pose proof (blk_granS HIx _ _ _ _ _ _ _ p 48 5 HP INp' ltac:(lia) ltac:(lia)) as SH5.
replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SH5 by lia. exact SH5. }
split. { eapply (otab_agree asegs); [exact OT0 | exact AG | exact INT]. }
eapply (kids_okv_agree asegs A4F); [exact KOK | exact AG |]. intros b Hb. apply INCL. right. apply in_or_app. right. exact Hb.
Qed.

Lemma entryM : forall A FA CH e0 m md j e, ser_memx A FRS FA CH e0 m md -> nth_error es j = Some e ->
0 < oe_a e /\ oe_a e + 32 <= alloc_ceiling /\ oe_a e mod 8 = 0 /\
(exists pad : word, rw_cells asegs m (oe_a e) [C8 (wz (oe_k e)); C4 (wz 0); C4 pad; C8 (wz (oe_v e)); C8 (wz (ohd (skipn (S j) es)))]) /\
ro_cells asegs m (oe_a e / 8 + 2147450880) [C1 (Z_to_bv 8 0)] /\ ro_cells asegs m (oe_a e / 8 + 2147450882) [C1 (Z_to_bv 8 0)] /\
ro_cells asegs m (oe_a e / 8 + 2147450883) [C1 (Z_to_bv 8 0)] /\
cstr asegs m (oe_k e) (oe_kn e) (oe_ks e) /\ In (oe_k e, oe_kn e) LB /\ oe_kn e <= 2^31.
Proof.
intros A FA CH e0 m md j e INV Hj.
pose proof (factsM _ _ _ _ _ _ INV) as (_ & _ & _ & _ & _ & _ & OT & _).
destruct INV as (buf & cap & bpos & content & errv & B & HP & _).
pose proof facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & INT).
destruct OT as (_ & _ & ENT). destruct (ENT j e Hj) as (A0 & AL8 & (a & kk & Hin & Ha1 & Ha2) & RW & CS & INk & KN).
assert (Hin' : In (a, kk) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; apply INT; exact Hin).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a kk HP ltac:(apply in_or_app; left; exact Hin')) as (_ & _ & _ & Hhi & _).
split; [exact A0|]. split; [lia|]. split; [exact AL8|]. split; [exact RW|].
split; [exact (blk_gran_at HIx _ _ _ _ _ _ _ a kk (oe_a e) HP Hin' ltac:(lia) ltac:(lia) AL8)|].
split. { pose proof (blk_gran_at HIx _ _ _ _ _ _ _ a kk (oe_a e + 16) HP Hin' ltac:(lia) ltac:(lia) ltac:(clear - AL8; Z.div_mod_to_equations; lia)) as X.
replace ((oe_a e + 16) / 8 + 2147450880) with (oe_a e / 8 + 2147450882) in X by (clear - AL8; Z.div_mod_to_equations; lia). exact X. }
split. { pose proof (blk_gran_at HIx _ _ _ _ _ _ _ a kk (oe_a e + 24) HP Hin' ltac:(lia) ltac:(lia) ltac:(clear - AL8; Z.div_mod_to_equations; lia)) as X.
replace ((oe_a e + 24) / 8 + 2147450880) with (oe_a e / 8 + 2147450883) in X by (clear - AL8; Z.div_mod_to_equations; lia). exact X. }
split; [exact CS|]. split; [apply INT; exact INk | exact KN].
Qed.

Lemma obj_failA :
forall (x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) F' fc' m md A (PRE : list cell) e,
ser_memx A FRS (usp + -224) [(usp + -224, PRE ++ savedR)] e m md -> cells_size PRE = 120%nat ->
0 <= e <= w ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md (MS (mkR x1 (wz (usp + -224)) gp (wz A_TP) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F' (wz 0x9cc80) fc' None m (seg_rom asegs)).
Proof.
intros until e. intros INV HPRE He FS' FR'.
pose proof facts as (SPR & INp & Rfl & FL2 & FL8 & FL32 & FL3 & FC1 & KD & LOS' & _).
destruct INV as (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & Hbp & Hcap & HBB & HBD).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
apply Forall_inv in CHm. cbn [fst snd] in CHm.
apply (proj1 (rw_cells_app asegs _ _ PRE _)) in CHm. destruct CHm as [PREc SAVc]. rewrite HPRE in SAVc. change (Z.of_nat 120) with 120 in SAVc.
replace (usp + -224 + 120) with (usp + -104) in SAVc by lia.
unfold savedR in SAVc. unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl (@nil (Z * Z)) m) as MU.
assert (STU : stk asegs m lo (bv_unsigned sp)).
{ pose proof (stk_release asegs m lo (bv_unsigned sp + -224) _ ST PREc ltac:(lia)) as S1. rewrite HPRE in S1. change (Z.of_nat 120) with 120 in S1.
replace (bv_unsigned sp + -224 + 120) with (bv_unsigned sp + -104) in S1 by lia.
pose proof (stk_release asegs m lo (bv_unsigned sp + -104) _ S1 SAVc ltac:(lia)) as S2. cbn [cells_size csize Nat.add] in S2.
replace (bv_unsigned sp + -104 + Z.of_nat 104) with (bv_unsigned sp) in S2 by lia. exact S2. }
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. do 13 step. step. step.
evt_done5. apply K. unfold ser_postA.
eexists m, _, errv, buf, cap, bpos, content, B.
split; [apply ret_statew_intro; [exact FS' | intros _; exact FR']|].
split; [exact VM|]. split; [exact STU|]. split; [exact HPR|]. split; [exact ERR|]. split; [exact HP|]. split; [exact PB|].
split; [lia|]. split; [exact Hcap|]. split; [exact HBB | exact HBD].
Qed.

Lemma obj_closeA :
forall (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) F' fc' m md A (PRE : list cell) e,
ser_memx A FRS (usp + -224) [(usp + -224, PRE ++ savedR)] e m md -> cells_size PRE = 120%nat ->
0 <= e -> e + 2 <= w ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md (MS (mkR x1 (wz (usp + -224)) gp (wz A_TP) t0 t1 t2 (wz pb) x9 a0 a1 a2 a3 a4 a5 a6 a7
(wz fl) x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F' (wz 0x9cc64) fc' None m (seg_rom asegs)).
Proof.
intros until e. intros INV HPRE He Hew FS' FR'.
pose proof facts as (SPR & INp & Rfl & FL2 & FL8 & FL32 & FL3 & FC1 & KD & LOS' & _).
destruct INV as (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & Hbp & Hcap & HBB & HBD).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
apply Forall_inv in CHm. cbn [fst snd] in CHm.
apply (proj1 (rw_cells_app asegs _ _ PRE _)) in CHm. destruct CHm as [PREc SAVc]. rewrite HPRE in SAVc. change (Z.of_nat 120) with 120 in SAVc.
replace (usp + -224 + 120) with (usp + -104) in SAVc by lia.
unfold savedR in SAVc. unfold usp in *. unfold_consts.
pose proof PB as (Hbp0 & Hcap0 & Hlen & PBS & PBUF).
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl (@nil (Z * Z)) m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. rewrite (unsigned_lit fl) by lia. rewrite FL3.
step. step.
assert (STU : stk asegs m lo (bv_unsigned sp)).
{ pose proof (stk_release asegs m lo (bv_unsigned sp + -224) _ ST PREc ltac:(lia)) as S1. rewrite HPRE in S1. change (Z.of_nat 120) with 120 in S1.
replace (bv_unsigned sp + -224 + 120) with (bv_unsigned sp + -104) in S1 by lia.
pose proof (stk_release asegs m lo (bv_unsigned sp + -104) _ S1 SAVc ltac:(lia)) as S2. cbn [cells_size csize Nat.add] in S2.
replace (bv_unsigned sp + -104 + Z.of_nat 104) with (bv_unsigned sp) in S2 by lia. exact S2. }
assert (INVU : ser_memx A FRS (bv_unsigned sp) [] e m md).
{ exists buf, cap, bpos, content, errv, B.
split; [exact HP|]. split; [exact PB|]. split; [constructor|]. split; [constructor|]. split; [exact FSUB|].
split; [exact ERR|]. split; [exact STU|]. split; [exact HPR|]. split; [exact VM|].
split; [exact Hbp|]. split; [exact Hcap|]. split; [exact HBB | exact HBD]. }
assert (TAILK : forall (lit k : Z) (bs : list byte) (t0_ t1_ t2_ a3_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ : word),
ro_bytes_b asegs lit bs = true -> Z.of_nat (length bs) = k -> src_ro_chk lit k = true -> 0 < k <= 2 -> 0 <= lit -> lit + k < 2^32 ->
evt asegs (AJ5e A4L HIx A T md)
(MS (mkR ra sp gp (Z_to_bv 64 6444320) t0_ t1_ t2_ s0 s1 (Z_to_bv 64 pb) (Z_to_bv 64 lit) (Z_to_bv 64 k) a3_ a4_ a5_ a6_ a7_
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3_ t4_ t5_ t6_)
F' (Z_to_bv 64 0x9b4fc) fc' None m (seg_rom asegs))).
{ intros lit k bs t0_ t1_ t2_ a3_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ RB BL CHK Hk Hl Hlk.
evt_done5.
rewrite <- (Z_to_bv_bv_unsigned ra) at 1. rewrite <- (Z_to_bv_bv_unsigned sp) at 1.
eapply (ser_litA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w LO HT CAP0 TXT NEED OBL_REALLOC_NF lit k bs RB BL CHK ltac:(lia) Hl Hlk) with (F := F) (e := e);
[ exact INVU | exact He | lia | lia | exact SPA | lia | lia | reflexivity | word_range ra RAR; lia | exact RA | exact FS' | exact FR' | ].
intros A2 m2 md2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 INV2 FS2 FR2.
pose proof INV2 as (buf2 & cap2 & bpos2 & content2 & errv2 & B2 & HP2 & PB2 & _ & _ & _ & ERR2 & ST2 & HPR2 & VM2 & Hb2 & Hc2 & HB2 & HD2).
apply K. unfold ser_postA.
exists m2, a0', errv2, buf2, cap2, bpos2, content2, B2.
rewrite !Z_to_bv_bv_unsigned.
assert (ERA : ra = ret_pc ra).
{ word_range ra RAR. rewrite <- (Z_to_bv_bv_unsigned ra) at 2. rewrite ret_pc_even by (try exact RA; lia). rewrite Z_to_bv_bv_unsigned. reflexivity. }
split; [unfold ret_statew; do 16 eexists; split; [rewrite <- ERA; reflexivity|]; split; [exact FS2 | intros _; exact FR2]|].
split; [exact VM2|]. split; [exact ST2|]. split; [exact HPR2|]. split; [exact ERR2|]. split; [exact HP2|]. split; [exact PB2|].
split; [lia|]. split; [exact Hc2|]. split; [exact HB2 | exact HD2]. }
destruct FC1 as [E1 | E1]; rewrite E1.
-
if_lit. step. step. step. step. do 13 step. step. step. fold_mkR.
eapply (TAILK 0x235e0 1 LIT_RBRACE); [vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | lia | lia | lia].
-
if_lit. step. step. step. step. step. do 13 step. step. step. fold_mkR.
eapply (TAILK 0x235c0 2 LIT_SP_RBRACE); [vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | lia | lia | lia].
Qed.

Lemma obj_exitA :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) F' fc' m md A (PRE : list cell) e,
ser_memx A FRS (usp + -224) [(usp + -224, PRE ++ savedR)] e m md -> cells_size PRE = 120%nat ->
0 <= e -> e + 2 <= w ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md (MS (mkR x1 (wz (usp + -224)) gp (wz A_TP) t0 t1 t2 (wz pb) (wz 0) a0 a1 a2 a3 a4 a5 a6 a7
(wz fl) x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F' (wz 0x9cc18) fc' None m (seg_rom asegs)).
Proof.
intros until e. intros INV HPRE He Hew FS' FR'.
pose proof facts as (SPR & _).
pose proof INV as (buf & cap & bpos & content & errv & B & HP & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
stash INV.
unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl (@nil (Z * Z)) m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. if_lit.
evt_done5. unstash INV.
eapply obj_closeA; [exact INV | exact HPRE | exact He | exact Hew | exact FS' | exact FR'].
Qed.

Lemma kid_callO : forall (s' : jshape) (v pbk : Z) (RESTk : list blk)
(x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x20 x21 x22 x24 x26 x27 t3 t4 t5 t6 : word) F' fc' A CH e m md,
ser_memx A FRS (usp + -224) CH e m md -> jnode asegs A4F s' m RESTk v 1 pbk -> incl RESTk LB ->
(AJ5 A4L HIx A T md (MS (mkR (wz 0x9caf8) (wz (usp + -224)) gp (wz A_TP) t0 t1 t2 (wz pb) x9 (wz v) (wz pb) (wz (lv + 1)) (wz fl) (wz (afn_of s')) a5 a6 a7
(wz fl) (wz (lv + 1)) x20 x21 x22 (wz v) x24 (wz 2147450880) x26 x27 t3 t4 t5 t6) F' (wz (afn_of s')) fc' None m (seg_rom asegs))) ->
AJ5 A4L HIx A T md (MS (mkR x1 (wz (usp + -224)) gp (wz A_TP) t0 t1 t2 (wz pb) x9 a0 a1 a2 a3 a4 a5 a6 a7
(wz fl) (wz (lv + 1)) x20 x21 x22 (wz v) x24 (wz 2147450880) x26 x27 t3 t4 t5 t6) F' (wz 0x9cacc) fc' None m (seg_rom asegs)).
Proof.
intros until md. intros INV JN INCLk KONT.
pose proof facts as (SPR & _ & Rfl & _).
pose proof INV as (buf & cap & bpos & content & errv & B & HP & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
destruct (jnode_hdr asegs A4F _ _ _ _ _ _ JN) as (n & ty & udel & ud & cs & rest & ER & Hn & HDR).
assert (INv : In (v, n) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; apply INCLk; rewrite ER; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ v n HP ltac:(apply in_or_app; left; exact INv)) as (_ & Hval & Hvlo & Hvhi & _).
pose proof (blk_granS HIx _ _ _ _ _ _ _ v n 1 HP INv ltac:(lia) ltac:(lia)) as SHv.
replace (v / 8 + 2147450880 + 1) with (v / 8 + 2147450881) in SHv by lia.
apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _; _; _] cs)) in HDR. destruct HDR as [HDR _].
clear INV JN.
unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl (@nil (Z * Z)) m) as MU.
a4l.
unfold afn_of in KONT.
reenterA asegs A4L HIx asegs_wx HP.
step. asan_chkA.
destruct s' as [|[|]| |[|]|kids'|kids'];
(lazymatch type of HDR with context [fn_ofF A4F ?s] => let fv := eval vm_compute in (fn_ofF A4F s) in change (fn_ofF A4F s) with fv in HDR, KONT end);
step; do 4 step; step; fold_mkR; evt_done5; exact KONT.
Qed.

Definition objFR (j0 : list byte) : list cell :=
[CB 8 j0; C8 (wz lv); C8 (wz (ohd es)); C8 (wz 0x235a0); C8 (wz (2 * (lv + 1))); C8 (wz (lv + 1073741825)); C8 (wz 0x234e0); C8 (wz 0x23500); C8 (wz 0x23560); C8 (wz 0x23580);
C8 (wz 0x234a0); C8 (wz 0x234c0); C8 (wz 0); C8 (wz 0x233c0); C8 (wz 0x23540)] ++ savedR.
Notation keyblks := (map (fun e => (oe_k e, oe_kn e)) es).

Definition st_obj (pc : Z) (x9 x19 x24 : word) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m : word -> option byte) : machine_state :=
MS (mkR x1 (wz (usp + -224)) gp (wz A_TP) t0 t1 t2 (wz pb) (wz 0) a0 a1 a2 a3 a4 a5 a6 a7
(wz fl) (wz (lv + 1)) (wz (Z.land fl 1)) x19 (wz 0x23520) x24 (wz 0) (wz 2147450880) (wz 0) x9 t3 t4 t5 t6)
F' (wz pc) fc' None m (seg_rom asegs).

Definition loopK (j0 : list byte) (bound : Z) : Prop :=
forall (j : nat) (e : oent) (f acc : Z) (P : list blk) (x9 x24 : word) (x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' m md A,
nth_error es j = Some e -> LEN - Z.of_nat j <= bound -> (f = 0 \/ f = 1) ->
pbtail P -> jtxk_obj (skipn j kids) (skipn j keyblks) (P ++ concat (skipn j KBS) ++ Y) acc = Some (w, R) -> 24 <= acc ->
ser_memx A FRS (usp + -224) [(usp + -224, objFR j0)] (acc - 2) m md ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md (st_obj 0x9ca0c x9 (wz (oe_a e)) x24 x1 t0 t1 t2 a0 (wz f) a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m).

Section Iter.
Variable j0 : list byte.
Variable bound : Z.
Hypothesis IH : loopK j0 bound.

Lemma obj_nextA :
forall (j : nat) (e : oent) (acc : Z) (P : list blk) (x9 x24 : word) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' m md A,
nth_error es j = Some e -> LEN - Z.of_nat j <= bound + 1 ->
pbtail P -> jtxk_obj (skipn (S j) kids) (skipn (S j) keyblks) (P ++ concat (skipn (S j) KBS) ++ Y) acc = Some (w, R) -> 24 <= acc ->
ser_memx A FRS (usp + -224) [(usp + -224, objFR j0)] (acc - 2) m md ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md (st_obj 0x9cbfc x9 (wz (oe_a e)) x24 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m).
Proof.
intros until A. intros Hj Hb HP0 JT Hacc INV FS' FR'.
pose proof facts as (SPR & INp & Rfl & FL2 & FL8 & FL32 & FL3 & FC1 & KD & LOS' & LESk & LKBS & INT).
destruct (entryM _ _ _ _ _ _ _ _ INV Hj) as (Ha0 & Hah & Ha8 & (pad & ENT) & SHe0 & SHe2 & SHe3 & _ & _ & _).
pose proof INV as (buf & cap & bpos & content & errv & B & HP & PB & CHm & _ & _ & _ & ST & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
apply Forall_inv in CHm. cbn [fst snd] in CHm. unfold objFR, savedR in CHm. cbn [app] in CHm.
unfold st_obj. unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl (@nil (Z * Z)) m) as MU.
stash INV.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. asan_chkA.
step. step.
rewrite (ohd_skipn es (S j)).
destruct (nth_error es (S j)) as [e'|] eqn:Hj'.
- unstash INV.
destruct (entryM _ _ _ _ _ _ _ _ INV Hj') as (Ha0' & Hah' & Ha8' & _).
unfold_consts.
if_truex.
step. step. ubsan_align8 Ha8'. fold_mkR. evt_done5.
pose proof (nth_error_Some es (S j)) as NS. rewrite Hj' in NS.
unfold loopK, st_obj in IH.
eapply (IH (S j) e' 0 acc P); [exact Hj' | unfold LEN in *; lia | left; reflexivity | exact HP0 | exact JT | exact Hacc | exact INV | exact FS' | exact FR'].
- if_lit. fold_mkR. evt_done5. unstash INV.
apply nth_error_None in Hj'.
assert (Ew : w = acc) by (eapply (jtxk_obj_done kids (S j)); [lia | exact JT]).
eapply obj_exitA with (e := acc - 2)
(PRE := [CB 8 j0; C8 (Z_to_bv 64 lv); C8 (Z_to_bv 64 (ohd es)); C8 (Z_to_bv 64 0x235a0); C8 (Z_to_bv 64 (2 * (lv + 1))); C8 (Z_to_bv 64 (lv + 1073741825)); C8 (Z_to_bv 64 0x234e0);
C8 (Z_to_bv 64 0x23500); C8 (Z_to_bv 64 0x23560); C8 (Z_to_bv 64 0x23580); C8 (Z_to_bv 64 0x234a0); C8 (Z_to_bv 64 0x234c0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x233c0); C8 (Z_to_bv 64 0x23540)]);
[exact INV | reflexivity | lia | lia | exact FS' | exact FR'].
Qed.

Lemma obj_ret_kidA :
forall (j : nat) (e : oent) (acc : Z) (P : list blk) (x9 x24 : word) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' m md A,
nth_error es j = Some e -> LEN - Z.of_nat j <= bound + 1 ->
pbtail P -> jtxk_obj (skipn (S j) kids) (skipn (S j) keyblks) (P ++ concat (skipn (S j) KBS) ++ Y) acc = Some (w, R) -> 24 <= acc -> acc <= w ->
ser_memx A FRS (usp + -224) [(usp + -224, objFR j0)] (acc - 2) m md ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md (st_obj 0x9caf8 x9 (wz (oe_a e)) x24 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m).
Proof.
intros until A. intros Hj Hb HP0 JT Hacc Haw INV FS' FR'.
pose proof facts as (SPR & _).
pose proof INV as (buf & cap & bpos & content & errv & B & HP & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
unfold st_obj. unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl (@nil (Z * Z)) m) as MU.
stash INV.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. if_cases NEG; fold_mkR.
- evt_done5. unstash INV.
eapply (obj_nextA j e acc P); [exact Hj | exact Hb | exact HP0 | exact JT | exact Hacc | exact INV | exact FS' | exact FR'].
- step. fold_mkR. evt_done5. unstash INV.
eapply obj_failA with (e := acc - 2)
(PRE := [CB 8 j0; C8 (Z_to_bv 64 lv); C8 (Z_to_bv 64 (ohd es)); C8 (Z_to_bv 64 0x235a0); C8 (Z_to_bv 64 (2 * (lv + 1))); C8 (Z_to_bv 64 (lv + 1073741825)); C8 (Z_to_bv 64 0x234e0);
C8 (Z_to_bv 64 0x23500); C8 (Z_to_bv 64 0x23560); C8 (Z_to_bv 64 0x23580); C8 (Z_to_bv 64 0x234a0); C8 (Z_to_bv 64 0x234c0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x233c0); C8 (Z_to_bv 64 0x23540)]);
[exact INV | reflexivity | lia | exact FS' | exact FR'].
Qed.

Lemma obj_nullA :
forall (j : nat) (e : oent) (acc : Z) (P : list blk) (x9 x24 : word) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' m md A,
nth_error es j = Some e -> LEN - Z.of_nat j <= bound + 1 ->
pbtail P -> jtxk_obj (skipn (S j) kids) (skipn (S j) keyblks) (P ++ concat (skipn (S j) KBS) ++ Y) acc = Some (w, R) -> 24 <= acc -> acc <= w ->
ser_memx A FRS (usp + -224) [(usp + -224, objFR j0)] (acc - 6) m md ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md (st_obj 0x9cbc4 x9 (wz (oe_a e)) x24 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m).
Proof.
intros until A. intros Hj Hb HP0 JT Hacc Haw INV FS' FR'.
pose proof facts as (SPR & INp & Rfl & FL2 & FL8 & FL32 & FL3 & FC1 & KD & LOS' & _).
pose proof INV as (buf & cap & bpos & content & errv & B & HP & PB & CHm & _ & _ & _ & ST & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
apply Forall_inv in CHm. cbn [fst snd] in CHm. unfold objFR, savedR in CHm. cbn [app] in CHm.
unfold st_obj. unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl (@nil (Z * Z)) m) as MU.
stash INV.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. step. if_lit. step. step. step. fold_mkR.
evt_done5. unstash INV.
eapply (ser_litA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w LO HT CAP0 TXT NEED OBL_REALLOC_NF 0x233c0 4 LIT_NULL) with (F := F) (e := acc - 6);
[ vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | lia | lia | lia
| exact INV | lia | lia | lia | clear - SPA; Z.div_mod_to_equations; lia | lia | lia | reflexivity | lia | reflexivity | exact FS' | exact FR' | ].
intros A3 m3 md3 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F3 fc3 INV3 FS3 FR3.
eapply (obj_nextA j e acc P); [exact Hj | exact Hb | exact HP0 | exact JT | exact Hacc | | exact FS3 | exact FR3].
replace (acc - 6 + 4) with (acc - 2) in INV3 by lia. exact INV3.
Qed.

Lemma obj_valA :
forall (pc0 : Z) (j : nat) (e : oent) (acc : Z) (P : list blk) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' m md A,
pc0 = 0x9cac0 \/ pc0 = 0x9cbc0 ->
nth_error es j = Some e -> LEN - Z.of_nat j <= bound + 1 ->
pbtail P -> jtxk_obj (skipn j kids) (skipn j keyblks) (P ++ concat (skipn j KBS) ++ Y) acc = Some (w, R) -> 24 <= acc ->
ser_memx A FRS (usp + -224) [(usp + -224, objFR j0)] (acc + 6 * Z.of_nat (length (oe_ks e)) + 4) m md ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md (st_obj pc0 (wz (oe_k e)) (wz (oe_a e)) (wz (oe_v e)) x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m).
Proof.
intros until A. intros PCS Hj Hb HP0 JT Hacc INV FS' FR'.
pose proof facts as (SPR & INp & Rfl & FL2 & FL8 & FL32 & FL3 & FC1 & KD & LOS' & LESk & LKBS & INT).
pose proof (factsM _ _ _ _ _ _ INV) as (_ & _ & _ & _ & _ & _ & _ & KOKm).
destruct (entryM _ _ _ _ _ _ _ _ INV Hj) as (_ & _ & _ & _ & _ & _ & _ & CS & INk & KN).
pose proof INV as (buf & cap & bpos & content & errv & B & HP & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
destruct (key_stringA HIx _ _ _ _ _ _ _ (oe_k e) (oe_kn e) (oe_ks e) HP ltac:(right; right; exact INk) CS) as (_ & _ & _ & _ & _ & KLEN & _).
set (klen := Z.of_nat (length (oe_ks e))) in *.
assert (KW : 6 * klen + 14 <= key_w (oe_kn e)) by (unfold key_w; lia).
assert (Hkv : nth_error (map (fun e0 => (oe_k e0, oe_v e0)) es) j = Some (oe_k e, oe_v e)) by (rewrite nth_error_map, Hj; reflexivity).
assert (Hkb : nth_error keyblks j = Some (oe_k e, oe_kn e)) by (rewrite nth_error_map, Hj; reflexivity).
assert (Hjl : (j < length es)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
destruct (nth_error kids j) as [k|] eqn:NTHk; [| apply nth_error_None in NTHk; lia].
unfold st_obj. unfold usp in *.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl (@nil (Z * Z)) m) as MU.
destruct k as [s'|].
-
destruct (kids_okv_nth asegs A4F _ _ _ _ _ _ KOKm NTHk) as (kk & v & bs & Hv & Hbs & _).
rewrite Hkv in Hv. injection Hv as <- <-.
destruct (jtxk_obj_step_some asegs A4F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KOKm NTHk Hkv Hbs Hkb HP0 JT) as (Hvnz & JV & pbk & PBSk & RESTk & wi & P' & Ebs & JN & Hwi & Haw & JTXk & HP' & JT').
cbn [snd] in Haw, JT'.
assert (INk' : In (Some s') kids) by (eapply nth_error_In; exact NTHk).
assert (INCLk : incl RESTk LB).
{ intros bq Hbq. apply INCL. right. apply in_or_app. right. apply in_concat. exists bs. split; [eapply nth_error_In; exact Hbs | rewrite Ebs; apply in_or_app; left; exact Hbq]. }
pose proof (kdepth_in _ _ INk') as KDk.
destruct (jnode_hdr asegs A4F _ _ _ _ _ _ JN) as (n & ty & udel & ud & cs & rest & ER & Hn & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ (oe_v e) n HP ltac:(apply in_or_app; left; right; right; apply INCLk; rewrite ER; left; reflexivity)) as (_ & Hval & Hvlo & Hvhi & _).
unfold_consts.
assert (TOKID : forall (x1_ t0_ t1_ t2_ a0_ a1_ a2_ a3_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ : word),
AJ5 A4L HIx A T md (MS (mkR x1_ (Z_to_bv 64 (bv_unsigned sp + -224)) gp (Z_to_bv 64 A_TP) t0_ t1_ t2_ (Z_to_bv 64 pb) (Z_to_bv 64 0) a0_ a1_ a2_ a3_ a4_ a5_ a6_ a7_
(Z_to_bv 64 fl) (Z_to_bv 64 (lv + 1)) (Z_to_bv 64 (Z.land fl 1)) (Z_to_bv 64 (oe_a e)) (Z_to_bv 64 0x23520) (Z_to_bv 64 (oe_v e))
(Z_to_bv 64 0) (Z_to_bv 64 2147450880) (Z_to_bv 64 0) (Z_to_bv 64 (oe_k e)) t3_ t4_ t5_ t6_) F' (Z_to_bv 64 0x9cacc) fc' None m (seg_rom asegs))).
{ intros. eapply (kid_callO s' (oe_v e) pbk RESTk); [exact INV | exact JN | exact INCLk |].
eapply (ser_childA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w LO HT CAP0 TXT NEED JHEX0 (afn_of s') s' (KIDS s' INk')) with (F := F) (e := acc + 6 * klen + 4);
[ exact INV | exact JN | exact INCLk | exact JTXk | lia | lia | exact FL | lia | rewrite sdepth_obj in Hlvd; lia | exact FRSN
| unfold ser_budgetA, ASER_LEVEL, ASER_LEAF; lia | clear - SPA; Z.div_mod_to_equations; lia | lia | lia | reflexivity | lia | reflexivity | exact FS' | exact FR' | ].
intros A3 m3 md3 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F3 fc3 INV3 FS3 FR3.
eapply (obj_ret_kidA j e (acc + (key_w (oe_kn e) + wi)) P'); [exact Hj | exact Hb | exact HP' | exact JT' | lia | lia | | exact FS3 | exact FR3].
eapply ser_memA_weaken_e; [| exact INV3]. lia. }
stash INV. a4l. reenterA asegs A4L HIx asegs_wx HP.
destruct PCS as [-> | ->].
+ step. if_falsex. step. step. ubsan_align Hval. fold_mkR. evt_done5. apply TOKID.
+ step. if_truex. step. step. ubsan_align Hval. fold_mkR. evt_done5. apply TOKID.
-
destruct (jtxk_obj_step_none asegs A4F _ _ _ _ _ _ _ _ _ _ _ _ KOKm NTHk Hkb HP0 JT) as ((kk & Hv0) & Haw & JT').
rewrite Hkv in Hv0. injection Hv0 as _ Hv0. cbn [snd] in Haw, JT'.
assert (TONULL : forall (x1_ t0_ t1_ t2_ a0_ a1_ a2_ a3_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ : word),
AJ5 A4L HIx A T md (MS (mkR x1_ (Z_to_bv 64 (bv_unsigned sp + -224)) gp (Z_to_bv 64 A_TP) t0_ t1_ t2_ (Z_to_bv 64 pb) (Z_to_bv 64 0) a0_ a1_ a2_ a3_ a4_ a5_ a6_ a7_
(Z_to_bv 64 fl) (Z_to_bv 64 (lv + 1)) (Z_to_bv 64 (Z.land fl 1)) (Z_to_bv 64 (oe_a e)) (Z_to_bv 64 0x23520) (Z_to_bv 64 (oe_v e))
(Z_to_bv 64 0) (Z_to_bv 64 2147450880) (Z_to_bv 64 0) (Z_to_bv 64 (oe_k e)) t3_ t4_ t5_ t6_) F' (Z_to_bv 64 0x9cbc4) fc' None m (seg_rom asegs))).
{ intros. eapply (obj_nullA j e (acc + (key_w (oe_kn e) + 4)) P); [exact Hj | exact Hb | exact HP0 | exact JT' | lia | lia | | exact FS' | exact FR'].
eapply ser_memA_weaken_e; [| exact INV]. lia. }
stash INV. a4l. reenterA asegs A4L HIx asegs_wx HP.
destruct PCS as [-> | ->].
+ step. if_rw Hv0 true. fold_mkR. evt_done5. apply TONULL.
+ step. if_rw Hv0 false. fold_mkR. evt_done5. apply TONULL.
Qed.

Lemma obj_keyA :
forall (j : nat) (e : oent) (acc : Z) (P : list blk) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' m md A,
nth_error es j = Some e -> LEN - Z.of_nat j <= bound + 1 ->
pbtail P -> jtxk_obj (skipn j kids) (skipn j keyblks) (P ++ concat (skipn j KBS) ++ Y) acc = Some (w, R) -> 24 <= acc ->
ser_memx A FRS (usp + -224) [(usp + -224, objFR j0)] acc m md ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md (st_obj 0x9ca68 (wz (oe_k e)) (wz (oe_a e)) (wz (oe_v e)) x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m).
Proof.
intros until A. intros Hj Hb HP0 JT Hacc INV FS' FR'.
pose proof facts as (SPR & INp & Rfl & FL2 & FL8 & FL32 & FL3 & FC1 & KD & LOS' & LESk & LKBS & INT).
destruct (entryM _ _ _ _ _ _ _ _ INV Hj) as (_ & _ & _ & _ & _ & _ & _ & CS & INk & KN).
pose proof INV as (buf & cap & bpos & content & errv & B & HP & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
destruct (key_stringA HIx _ _ _ _ _ _ _ (oe_k e) (oe_kn e) (oe_ks e) HP ltac:(right; right; exact INk) CS) as (_ & _ & _ & _ & _ & KLEN & _).

assert (Hjl : (j < length es)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
assert (Hkb : nth_error keyblks j = Some (oe_k e, oe_kn e)) by (rewrite nth_error_map, Hj; reflexivity).
assert (KWW : acc + key_w (oe_kn e) <= w).
{ destruct (nth_error kids j) as [k|] eqn:NTHk; [| apply nth_error_None in NTHk; lia].
rewrite (skipn_nth_cons _ _ _ NTHk), (skipn_nth_cons _ _ _ Hkb) in JT. cbn [jtxk_obj] in JT. destruct k as [s'|].
- destruct (jtx s' _) as [[wi R1]|] eqn:E; [|discriminate]. pose proof (jtx_nonneg _ _ _ _ E).
pose proof (jtxk_obj_acc _ (fun s0' _ bs0 w0 r0 H0 => jtx_nonneg _ _ _ _ H0) _ _ _ _ _ JT). lia.
- pose proof (jtxk_obj_acc _ (fun s0' _ bs0 w0 r0 H0 => jtx_nonneg _ _ _ _ H0) _ _ _ _ _ JT). unfold NULL_W in *. lia. }
set (klen := Z.of_nat (length (oe_ks e))) in *.
assert (KW : 6 * klen + 14 <= key_w (oe_kn e)) by (unfold key_w; lia).
clear CS.
unfold st_obj. unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl (@nil (Z * Z)) m) as MU.
stash INV.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. if_lit.
step. if_lit.
step. step. step. step. fold_mkR.
evt_done5. unstash INV.
eapply (ser_litA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w LO HT CAP0 TXT NEED OBL_REALLOC_NF 0x23520 1 LIT_QUOTE) with (F := F) (e := acc);
[ vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | lia | lia | lia
| exact INV | lia | lia | lia | clear - SPA; Z.div_mod_to_equations; lia | lia | lia | reflexivity | lia | reflexivity | exact FS' | exact FR' | ].
intros A1 m1 md1 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F1 fc1 INV1 FS1 FR1.
clear INV HP MI WM MU.

destruct (entryM _ _ _ _ _ _ _ _ INV1 Hj) as (_ & _ & _ & _ & _ & _ & _ & CS1 & _ & _).
pose proof INV1 as (buf1 & cap1 & bpos1 & content1 & errv1 & B1 & HP1 & _ & CHm & _ & _ & _ & ST1 & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1. cbn [hl_segs hla_base A4L A4H] in MI1.
assert (INkF : In (oe_k e, oe_kn e) ((pb, PB_SZ) :: (buf1, cap1) :: LB)) by (right; right; exact INk).
destruct (key_stringA HIx _ _ _ _ _ _ _ (oe_k e) (oe_kn e) (oe_ks e) HP1 INkF CS1) as (slack & STR & PAD & NN & UAL & UL & UPOS & UHI & USL).
clear CS1.
apply Forall_inv in CHm. cbn [fst snd] in CHm. unfold objFR, savedR in CHm. cbn [app] in CHm.
pose proof (wmono_refl asegs m1) as WM.
pose proof (munch_refl [(lo, bv_unsigned sp)] m1) as MU.
unfold_consts.
stash INV1.
a4l. reenterA asegs A4L HIx asegs_wx HP1.
step. step. fold_mkR.
eapply (astrlen_any_A HIx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 md1 A1 _ LM FRS B1 (oe_k e) (oe_kn e) (oe_k e) lo (oe_ks e) slack);
a4l_goal; rewrite ?unsigned_lit by lia;
first [exact HP1 | exact INkF | exact NN | exact STR | exact PAD | exact USL | exact ST1 | exact LO | exact MI1 | reflexivity | lia
| clear - SPA; Z.div_mod_to_equations; lia | idtac].
intros x0 x1' x2 y1' y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 m3 MU3 WM3 MI3 STR3 ST3.
stash STR3.
transport_after_call asegs m1 m3 MU3 WM3; try match goal with H : mem_inv asegs m1 |- _ => clear H end.
unstash STR3. unstash INV1.
rewrite ?unsigned_lit in ST3 by lia.
assert (INV3 : ser_memx A1 FRS (bv_unsigned sp + -224) [(bv_unsigned sp + -224, objFR j0)] (acc + 1) m3 md1).
{ eapply (ser_memA_stackW HIx sp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w HT); [exact INV1 | exact MU | exact WM | exact MI3 | | | | exact ST3 | lia].
- constructor; [cbn [fst snd]; split; lia | constructor].
- constructor; [exact CHm | constructor].
- constructor; [left; cbn [fst]; lia | constructor]. }
replace (ret_pc (Z_to_bv 64 641672)) with (Z_to_bv 64 641672) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
fold klen.
assert (Hkl31 : 0 <= klen < 2^31) by (unfold klen in *; lia).
step. step. step. step. step. fold_mkR.
assert (SRC3 : bytes_at asegs m3 (oe_k e) (oe_ks e)).
{ replace (oe_ks e ++ Z_to_bv 8 0 :: slack) with (oe_ks e ++ (Z_to_bv 8 0 :: slack)) in STR3 by reflexivity. apply bytes_at_app in STR3. exact (proj1 STR3). }
evt_done5.
eapply (ser_escapeA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w LO HT CAP0 TXT NEED JHEX0 ESC) with (F := F) (src := oe_ks e) (e := acc + 1) (sa := oe_k e) (sk := oe_kn e);
[ exact INV3 | exact INk | lia | fold klen; lia | exact SRC3 | reflexivity | fold klen; lia | lia | fold klen; lia
| exact FL | exact FRSN | unfold AESC_STACK; lia | clear - SPA; Z.div_mod_to_equations; lia
| lia | lia | reflexivity | lia | reflexivity | exact FS1 | exact FR1 | ].
intros A4 m4 md4 t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F4 fc4 INV4 FS4 FR4.
fold klen in INV4.
clear INV1 INV3 HP1 MI3 WM MU CHm ST3 STR3 SRC3 STR.
pose proof INV4 as (buf4 & cap4 & bpos4 & content4 & errv4 & B4 & HP4 & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI4. cbn [hl_segs hla_base A4L A4H] in MI4.
pose proof (wmono_refl asegs m4) as WM.
pose proof (munch_refl (@nil (Z * Z)) m4) as MU.
stash INV4.
a4l. reenterA asegs A4L HIx asegs_wx HP4.
step. step. step. step. fold_mkR.
evt_done5. unstash INV4.
eapply (ser_litA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w LO HT CAP0 TXT NEED OBL_REALLOC_NF 0x23520 1 LIT_QUOTE) with (F := F) (e := acc + 1 + 6 * klen);
[ vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | lia | lia | lia
| exact INV4 | lia | lia | lia | clear - SPA; Z.div_mod_to_equations; lia | lia | lia | reflexivity | lia | reflexivity | exact FS4 | exact FR4 | ].
intros A5 m5 md5 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F5 fc5 INV5 FS5 FR5.
clear INV4 HP4 MI4 WM MU.
pose proof INV5 as (buf5 & cap5 & bpos5 & content5 & errv5 & B5 & HP5 & _ & CHm & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI5. cbn [hl_segs hla_base A4L A4H] in MI5.
apply Forall_inv in CHm. cbn [fst snd] in CHm. unfold objFR, savedR in CHm. cbn [app] in CHm.
pose proof (wmono_refl asegs m5) as WM.
pose proof (munch_refl (@nil (Z * Z)) m5) as MU.
stash INV5.
a4l. reenterA asegs A4L HIx asegs_wx HP5.
step.
destruct FC1 as [E1 | E1].
-
if_rw E1 true. step. step. step. step. fold_mkR.
evt_done5. unstash INV5.
eapply (ser_litA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w LO HT CAP0 TXT NEED OBL_REALLOC_NF 0x23580 1 LIT_COLON) with (F := F) (e := acc + 1 + 6 * klen + 1);
[ vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | lia | lia | lia
| exact INV5 | lia | lia | lia | clear - SPA; Z.div_mod_to_equations; lia | lia | lia | reflexivity | lia | reflexivity | exact FS5 | exact FR5 | ].
intros A6 m6 md6 v0 v1 v2 c0 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F6 fc6 INV6 FS6 FR6.
eapply (obj_valA 0x9cbc0 j e acc P); [right; reflexivity | exact Hj | exact Hb | exact HP0 | exact JT | exact Hacc | | exact FS6 | exact FR6].
fold klen. eapply ser_memA_weaken_e; [| exact INV6]. lia.
-
if_rw E1 false. step. step. step. step. fold_mkR.
evt_done5. unstash INV5.
eapply (ser_litA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w LO HT CAP0 TXT NEED OBL_REALLOC_NF 0x23560 2 LIT_COLON_SP) with (F := F) (e := acc + 1 + 6 * klen + 1);
[ vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | lia | lia | lia
| exact INV5 | lia | lia | lia | clear - SPA; Z.div_mod_to_equations; lia | lia | lia | reflexivity | lia | reflexivity | exact FS5 | exact FR5 | ].
intros A6 m6 md6 v0 v1 v2 c0 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F6 fc6 INV6 FS6 FR6.
eapply (obj_valA 0x9cac0 j e acc P); [left; reflexivity | exact Hj | exact Hb | exact HP0 | exact JT | exact Hacc | | exact FS6 | exact FR6].
fold klen. eapply ser_memA_weaken_e; [| exact INV6]. lia.
Qed.

Lemma obj_sepA :
forall (j : nat) (e : oent) (acc : Z) (P : list blk) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' m md A,
nth_error es j = Some e -> LEN - Z.of_nat j <= bound + 1 ->
pbtail P -> jtxk_obj (skipn j kids) (skipn j keyblks) (P ++ concat (skipn j KBS) ++ Y) acc = Some (w, R) -> 24 <= acc ->
ser_memx A FRS (usp + -224) [(usp + -224, objFR j0)] (acc - 1) m md ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md (st_obj 0x9ca50 (wz (oe_k e)) (wz (oe_a e)) (wz (oe_v e)) x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m).
Proof.
intros until A. intros Hj Hb HP0 JT Hacc INV FS' FR'.
pose proof facts as (SPR & INp & Rfl & FL2 & FL8 & FL32 & FL3 & FC1 & KD & LOS' & LESk & LKBS & INT).
assert (Hjl : (j < length es)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
assert (Hkb : nth_error keyblks j = Some (oe_k e, oe_kn e)) by (rewrite nth_error_map, Hj; reflexivity).
assert (KWW : acc + key_w (oe_kn e) <= w).
{ destruct (nth_error kids j) as [k|] eqn:NTHk; [| apply nth_error_None in NTHk; lia].
rewrite (skipn_nth_cons _ _ _ NTHk), (skipn_nth_cons _ _ _ Hkb) in JT. cbn [jtxk_obj] in JT. destruct k as [s'|].
- destruct (jtx s' _) as [[wi R1]|] eqn:E; [|discriminate]. pose proof (jtx_nonneg _ _ _ _ E).
pose proof (jtxk_obj_acc _ (fun s0' _ bs0 w0 r0 H0 => jtx_nonneg _ _ _ _ H0) _ _ _ _ _ JT). lia.
- pose proof (jtxk_obj_acc _ (fun s0' _ bs0 w0 r0 H0 => jtx_nonneg _ _ _ _ H0) _ _ _ _ _ JT). unfold NULL_W in *. lia. }
assert (KW : 14 <= key_w (oe_kn e)) by (unfold key_w; lia).
pose proof INV as (buf & cap & bpos & content & errv & B & HP & _ & CHm & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
apply Forall_inv in CHm. cbn [fst snd] in CHm. unfold objFR, savedR in CHm. cbn [app] in CHm.
unfold st_obj. unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl (@nil (Z * Z)) m) as MU.
stash INV.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. if_lit.
step.
destruct FC1 as [E1 | E1].
- if_rw E1 true. fold_mkR. evt_done5. unstash INV.
eapply (obj_keyA j e acc P); [exact Hj | exact Hb | exact HP0 | exact JT | exact Hacc | | exact FS' | exact FR'].
eapply ser_memA_weaken_e; [| exact INV]. lia.
- if_rw E1 false. step. step. step. step. fold_mkR.
evt_done5. unstash INV.
eapply (ser_litA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w LO HT CAP0 TXT NEED OBL_REALLOC_NF 0x234e0 1 LIT_SPACE) with (F := F) (e := acc - 1);
[ vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | lia | lia | lia
| exact INV | lia | lia | lia | clear - SPA; Z.div_mod_to_equations; lia | lia | lia | reflexivity | lia | reflexivity | exact FS' | exact FR' | ].
intros A3 m3 md3 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F3 fc3 INV3 FS3 FR3.
eapply (obj_keyA j e acc P); [exact Hj | exact Hb | exact HP0 | exact JT | exact Hacc | | exact FS3 | exact FR3].
replace (acc - 1 + 1) with acc in INV3 by lia. exact INV3.
Qed.

Lemma obj_iter : loopK j0 (bound + 1).
Proof.
unfold loopK. intros until A. intros Hj Hb Hf HP0 JT Hacc INV FS' FR'.
pose proof facts as (SPR & INp & Rfl & FL2 & FL8 & FL32 & FL3 & FC1 & KD & LOS' & LESk & LKBS & INT).
destruct (entryM _ _ _ _ _ _ _ _ INV Hj) as (Ha0 & Hah & Ha8 & (pad & ENT) & SHe0 & SHe2 & SHe3 & _ & _ & _).
assert (Hjl : (j < length es)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
assert (Hkb : nth_error keyblks j = Some (oe_k e, oe_kn e)) by (rewrite nth_error_map, Hj; reflexivity).
assert (KWW : acc + key_w (oe_kn e) <= w).
{ destruct (nth_error kids j) as [k|] eqn:NTHk; [| apply nth_error_None in NTHk; lia].
rewrite (skipn_nth_cons _ _ _ NTHk), (skipn_nth_cons _ _ _ Hkb) in JT. cbn [jtxk_obj] in JT. destruct k as [s'|].
- destruct (jtx s' _) as [[wi R1]|] eqn:E; [|discriminate]. pose proof (jtx_nonneg _ _ _ _ E).
pose proof (jtxk_obj_acc _ (fun s0' _ bs0 w0 r0 H0 => jtx_nonneg _ _ _ _ H0) _ _ _ _ _ JT). lia.
- pose proof (jtxk_obj_acc _ (fun s0' _ bs0 w0 r0 H0 => jtx_nonneg _ _ _ _ H0) _ _ _ _ _ JT). unfold NULL_W in *. lia. }
assert (KW : 14 <= key_w (oe_kn e)) by (unfold key_w; lia).
pose proof INV as (buf & cap & bpos & content & errv & B & HP & _ & CHm & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
apply Forall_inv in CHm. cbn [fst snd] in CHm. unfold objFR, savedR in CHm. cbn [app] in CHm.
unfold st_obj. unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl (@nil (Z * Z)) m) as MU.
stash INV.
a4l. reenterA asegs A4L HIx asegs_wx HP.
asan_chk0.
step. asan_chkA.
step. step. step.
step.
destruct Hf as [-> | ->].
-
if_lit. step. step. step. step. fold_mkR.
evt_done5. unstash INV.
eapply (ser_litA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w LO HT CAP0 TXT NEED OBL_REALLOC_NF 0x234a0 1 LIT_COMMA) with (F := F) (e := acc - 2);
[ vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | lia | lia | lia
| exact INV | lia | lia | lia | clear - SPA; Z.div_mod_to_equations; lia | lia | lia | reflexivity | lia | reflexivity | exact FS' | exact FR' | ].
intros A3 m3 md3 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F3 fc3 INV3 FS3 FR3.
eapply (obj_sepA j e acc P); [exact Hj | exact Hb | exact HP0 | exact JT | exact Hacc | | exact FS3 | exact FR3].
replace (acc - 2 + 1) with (acc - 1) in INV3 by lia. exact INV3.
-
if_lit. fold_mkR. evt_done5. unstash INV.
eapply (obj_sepA j e acc P); [exact Hj | exact Hb | exact HP0 | exact JT | exact Hacc | | exact FS' | exact FR'].
eapply ser_memA_weaken_e; [| exact INV]. lia.
Qed.
End Iter.

Lemma obj_loop : forall j0 n, loopK j0 (Z.of_nat n).
Proof.
intros j0. induction n as [|n IH].
- unfold loopK. intros until A. intros Hj Hb. assert ((j < length es)%nat) by (apply nth_error_Some; rewrite Hj; discriminate). unfold LEN in *. lia.
- replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia. apply obj_iter. exact IH.
Qed.

Lemma obj_startA :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 x21 x22 x23 x24 x26 x27 t3 t4 t5 t6 : word) (j120 : list byte) F' fc' m md A,
ser_memx A FRS (usp + -224) [(usp + -224, [CB 120 j120] ++ savedR)] 1 m md ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md
(MS (mkR x1 (wz (usp + -224)) gp (wz A_TP) t0 t1 t2 (wz pb) (wz p) a0 a1 a2 a3 a4 a5 a6 a7
(wz fl) (wz lv) x20 x21 x22 x23 x24 (wz 2147450880) x26 x27 t3 t4 t5 t6)
F' (wz 0x9c8e0) fc' None m (seg_rom asegs)).
Proof.
intros until A. intros INV FS' FR'.
pose proof facts as (SPR & INp & Rfl & FL2 & FL8 & FL32 & FL3 & FC1 & KD & LOS' & LESk & LKBS & INT).
pose proof (factsM _ _ _ _ _ _ INV) as (Hp0 & Hph & Hp8 & NODE & SH0 & SH5 & (_ & HEAD & _) & _).
pose proof INV as (buf & cap & bpos & content & errv & B & HP & _ & CHm & _ & _ & _ & ST & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
assert (INt : In (t, 56) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; apply INT; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ t 56 HP ltac:(apply in_or_app; left; exact INt)) as (_ & Htal & Htlo & Hthi & _).
pose proof (blk_granS HIx _ _ _ _ _ _ _ t 56 1 HP INt ltac:(lia) ltac:(lia)) as SHt1.
replace (t / 8 + 2147450880 + 1) with (t / 8 + 2147450881) in SHt1 by lia.
apply Forall_inv in CHm. cbn [fst snd] in CHm. unfold savedR in CHm. cbn [app] in CHm.
unfold jhdr_cells in NODE. cbn [app] in NODE.
assert (Hw3 : 24 <= w) by (eapply jtxk_obj_acc; [intros s0' _ bs0 w0 r0 H0; exact (jtx_nonneg _ _ _ _ H0) | exact JTX]).
assert (Hlv1 : lv <= 999) by (rewrite sdepth_obj in Hlvd; lia).
unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -224, bv_unsigned sp)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
assert (Hpal : p mod 16 = 0).
{ pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p 48 HP ltac:(apply in_or_app; left; right; right; exact INp)) as (_ & Hpal & _). exact Hpal. }
step. if_falsex.
step. step. ubsan_align Hpal.
asan_chk0.
step. step. step. if_lit.
step. asan_chkA.
step.
step. if_falsex.
step. step. ubsan_align Htal.
stepz.
step. asan_chkA.
step.
step. rewrite (unsigned_lit fl) by lia. rewrite FL2.
step. rewrite (unsigned_lit fl) by lia. rewrite FL8.
stepz. stepz.
step.
pose proof (ohd_skipn es 0) as OH. change (skipn 0 es) with es in OH. rewrite OH.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
destruct (nth_error es 0) as [e0|] eqn:Hj0.
- destruct (entryM _ _ _ _ _ _ _ _ INV Hj0) as (Ha0 & Hah & Ha8 & _).
unfold_consts.
if_falsex.
step. rewrite (unsigned_lit fl) by lia.
step.
step. norm_w32.
step.
step. rewrite (unsigned_lit fl) by lia. rewrite FL32.
step. do 10 step.
step.
rewrite (v_slt_0 (Z_to_bv 64 (lv + 1)) (Z_to_bv 64 lv)) by (rewrite !signed_lit by lia; lia).
step.
step. norm_w32.
rewrite (Z.shiftl_mul_pow2 (lv + 1) 1) by lia. change (2^1) with 2. rewrite (swrap32_id ((lv + 1) * 2)) by lia. replace ((lv + 1) * 2) with (2 * (lv + 1)) by lia.
stepz.
step. stepz.
step.
step. stepz. step. stepz. step. stepz. step. stepz. step. stepz. step. stepz. step. stepz.
step. norm_w32. stepz.
step. stepz.
step.
rewrite OH; try rewrite Hj0; cbv iota.
step. step. ubsan_align8 Ha8.
fold_mkR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
match goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
lazymatch type of CHm with rw_cells _ _ _ (CB 8 ?jj :: _) =>
assert (INV3 : ser_memx A FRS (bv_unsigned sp + -224) [(bv_unsigned sp + -224, objFR jj)] 1 m3 md) end.
{ eapply (ser_memA_stackW HIx sp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w HT); [exact INV | exact MU | exact WM | exact MI3 | | | | exact ST | lia].
- constructor; [cbn [fst snd]; split; lia | constructor].
- constructor; [exact CHm | constructor].
- constructor; [left; cbn [fst]; lia | constructor]. }
evt_done5.
lazymatch type of INV3 with context [objFR ?jj] =>
pose proof (obj_loop jj (length es)) as LK; unfold loopK, st_obj in LK;
eapply (LK 0%nat e0 1 24 []); [exact Hj0 | unfold LEN; lia | right; reflexivity | exact pbtail_nil | exact JTX | lia | | exact FS' | exact FR'] end.
eapply ser_memA_weaken_e; [| exact INV3]. lia.
-
if_lit. fold_mkR.
lazymatch type of CHm with rw_cells _ _ _ ?frc =>
assert (INV2 : ser_memx A FRS (bv_unsigned sp + -224) [(bv_unsigned sp + -224, frc)] 1 m2 md) end.
{ eapply (ser_memA_stackW HIx sp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w HT); [exact INV | exact MU | exact WM | exact MI2 | | | | exact ST | lia].
- constructor; [cbn [fst snd]; split; lia | constructor].
- constructor; [exact CHm | constructor].
- constructor; [left; cbn [fst]; lia | constructor]. }
evt_done5.
lazymatch type of CHm with rw_cells _ _ _ ?frc =>
eapply obj_exitA with (e := 1) (PRE := firstn (length frc - 13) frc); [exact INV2 | reflexivity | lia | lia | exact FS' | exact FR'] end.
Qed.
End Obj.

Section Top.
Variable HIx : heap_iface_A A4L.
Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.
Hypothesis ESC : esc_specA HIx.

Theorem ser_objA : forall kids, (forall s', In (Some s') kids -> ser_specA HIx (afn_of s') s') -> ser_specA HIx ASER_OBJ (Sobj kids).
Proof.
intros kids KIDS. unfold ser_specA. intros until errv. intros HP PB JN INCL JTX CAP TXT NEED FL Hlv Hlvd FRSN ST LO LOS SPA HT ERR JHX TP' RA FRM A0 A1 A2 A3 K.
destruct JN as (t & TBS & kvs & KBS & EREST & NODE & LT & L1 & L2 & KOK).
assert (POS : forall a n, In (a, n) TBS -> 0 < a /\ a mod 16 = 0).
{ intros a n Hin. pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a n HP ltac:(apply in_or_app; left; right; right; apply INCL; rewrite EREST; right; apply in_or_app; left; exact Hin)) as (_ & Hal & Hlo & _). split; assumption. }
destruct (lhtab_otab asegs A4F _ _ _ _ LT POS) as (es & OT & Ekvs & tbl & size & ETBS).
subst a0 a1 a2 a3 tp REST kvs TBS.
cbn [app] in JTX. rewrite jtx_obj_eq in JTX. cbn [snd] in JTX. change (48 =? 48) with true in JTX. change (56 =? 56) with true in JTX. cbn [andb] in JTX.
rewrite length_map in L1.
assert (LK : length (map (fun e => (oe_k e, oe_kn e)) es) = length kids) by (rewrite length_map; exact L1).
match type of JTX with context [(?x <=? ?y)%nat] => destruct (Nat.leb_spec x y) as [_|GT]; [| exfalso; rewrite !length_app, length_map in GT; clear - GT L1; lia] end.
rewrite <- app_assoc in JTX. rewrite (firstn_app_exact _ _ _ LK), (skipn_app_exact _ _ _ LK) in JTX.
pose proof NODE as NODE0. pose proof JHX as JHX0.
assert (LOS0 : lo <= bv_unsigned sp - 224 - 4096 - 112) by (unfold ser_budgetA, ASER_LEVEL, ASER_LEAF in LOS; rewrite sdepth_obj in LOS; pose proof (kdepth_nonneg kids); lia).
stash NODE0. stash JHX0. stash OT. stash KOK. stash LOS. stash POS.
word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ pb PB_SZ HP ltac:(apply in_or_app; left; left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(apply in_or_app; left; right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
unfold ASER_OBJ. unfold_consts.
pose proof PB as (Hbp & Hcap & Hlen & PBS & PBUF).
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 224, bv_unsigned sp)] m) as MU.
pose proof alloc_ceiling_range as ACR.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 224%nat ST.
do 14 step. do 3 step. do 3 step. step. do 4 step. step. fold_mkR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
lazymatch type of FR with rw_cells _ _ _ ?frc =>
assert (INV1 : ser_memA HIx sp m md LB LM FRS B pb lo bpos cap w A FRS (bv_unsigned sp + -224) [(bv_unsigned sp + -224, frc)] 0 m1 md) end.
{ exists buf, cap, bpos, content, errv, B.
split; [heap_nowA A4L HIx HP MU WM MI1|].
split; [split; [lia|]; split; [lia|]; split; [exact Hlen|]; split; [exact PBS | exact PBUF]|].
split; [constructor; [exact FR | constructor]|].
split; [constructor; [left; cbn [fst]; lia | constructor]|].
split; [intros bb Hbb; exact Hbb|].
split; [exact ERR|]. split; [exact ST|].
split. { eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros bb Hbb; apply in_app_or in Hbb; apply in_or_app; destruct Hbb as [Hbb|Hbb]; [left; right; right; exact Hbb | right; exact Hbb] | lia | solve_clientWA A4L HIx HP]. }
split; [apply model_vm_only_refl|].
split; [lia|]. split; [unfold ser_capb; lia|]. split; lia. }
assert (Hw3 : 24 <= w) by (eapply jtxk_obj_acc; [intros s0' _ bs0 w0 r0 H0; exact (jtx_nonneg _ _ _ _ H0) | exact JTX]).
evt_done5.
eapply (ser_litA HIx sp gp m md LB LM FRS B pb lo bpos cap w LO HT CAP TXT NEED OBL_REALLOC_NF 0x23480 1 LIT_LBRACE) with (F := F) (e := 0);
[ vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | lia | lia | lia
| exact INV1 | lia | lia | lia | clear - SPA; Z.div_mod_to_equations; lia | lia | lia | reflexivity | lia | reflexivity | apply fsaved_refl | exact FRM | ].
intros A3 m3 md3 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F3 fc3 INV3 FS3 FR3.
unstash NODE0. unstash JHX0. unstash OT. unstash KOK. unstash LOS.
lazymatch type of INV3 with context [[(_, [CB 120 ?jj; _; _; _; _; _; _; _; _; _; _; _; _; _])]] =>
eapply (obj_startA HIx OBL_REALLOC_NF ESC ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B pb lo p rc pb0 lv fl t tbl size bpos cap w
es KBS kids T Y R KIDS FL Hlv Hlvd LO LOS SPA HT RA CAP TXT NEED JHX0 FRSN INCL NODE0 OT KOK JTX K
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ jj); [exact INV3 | exact FS3 | exact FR3] end.
Qed.
End Top.
End RC__1.
End Mqi.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qtgi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QG8z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QG8z. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QIsM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QIsM.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qa8x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qa8x.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7UD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qiiq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qiiq.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4v2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4v2.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1Ey.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1Ey. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql4f.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql4f.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1Y6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1Y6.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrQv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrQv.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEUF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEUF. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdGy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdGy.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition APE_ERRMEMB : Z := 0x98a04.

Section PeSCendA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis MAPP : memappend_A_stmt2 HIx.

Lemma seg_cend_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (nB : nat)
(gp t0 t1 t2 a3 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOK m ts 0 -> BOK pf pa ts B (S nB) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_comment_end ->
t_co ts < pf_len pf ->

(forall m' md' A' B' st' pbs' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
(bv_unsigned cb = 47 /\ st' = ST_eatws) \/ (bv_unsigned cb <> 47 /\ st' = ST_comment) ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_lvl (ts_pbs ts pbs') (TL st' (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv' ->
PBOK m' (ts_lvl (ts_pbs ts pbs') (TL st' (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) 1 ->
BOK pf pa (ts_lvl (ts_pbs ts pbs') (TL st' (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5'
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->

(forall m' md' A' B' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(Q1Y6.Mq2.pe_msE pf pa APE_ERRMEMB x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (pf_tk pf / 8 + SB2)) (Z_to_bv 64 (pf_tk pf + 20)) s5' (Z_to_bv 64 (pf_tk pf + 36)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa))
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pf_sb pf + t_co ts)) t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_comment_end) (t_co ts) gp t0 t1 t2
(Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l))
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3 (Z_to_bv 64 APE_JTAB) a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC BSL INV PBK BK Hl Hst Hco Kbreak Kerr16.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof INV as INV0. destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
unfold pe_msA, pe_msO, Q1Y6.Mq2.pe_msE in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
unfold APE_BREAK, APE_ERRMEMB, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear PB TSK REST.
reenterA asegs A4L HIx asegs_wx HP. rewrite Hst. unfold ST_comment_end. cbn [pe_jtA].
step.
asan_chkA.
do 4 step.
evt_done5.
eapply (pe_memappend_c HIx GA GA_pres MAPP (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv T);
[exact STC | exact BSL | exact INV0 | exact PBK | exact BK | exact Hco | rewrite unsigned_lit by lia; reflexivity |].
intros m2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 OUT2 FS2 FRM2.
cbn [pf_spf] in *. unfold A_TP in *.

clear TOK SLOTS SHT1 Htal Htlo Hthi Himg_t INtk HP INV0 PBK BK.
set (ts2 := ts_pbs ts0 pbs2) in *.
pose proof INV2 as INV2'. destruct INV2' as [CORE2 REST2].
destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK & FR).
pose proof REST2 as (HP & LV & _).
unfold ts2, ts_pbs, ts0 in TOK, TSK, LV. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK, TSK, LV.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & FF & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS, FF.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts2)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts2)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m2) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 0 HP INq ltac:(lia) ltac:(lia)) as SHQ.
replace (q / 8 + 4 * Z.of_nat depth + 0 + A_SB) with (q / 8 + 4 * Z.of_nat depth + A_SB) in SHQ by lia.
assert (Hb8 : bse mod 8 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
assert (SHQ4 : ro_cells asegs m2 (bse / 8 + A_SB) [C1 (Z_to_bv 8 0)]).
{ replace (bse / 8) with (q / 8 + 4 * Z.of_nat depth) by (subst bse; rewrite div8_add_mul32 by lia; lia). exact SHQ. }
pose proof (munch_refl [(bse, bse + 32)] m2) as MU.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t. stash Himg_q. clear LV TSK.
reenterA asegs A4L HIx asegs_wx HP.
destruct OUT2 as [(-> & PBK2 & BK2) | [-> Epbs2]].
2:{ replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step. step.
if_false.
step.
step.
asan_rechkA.
evt_done5.
eapply (Kerr16 m2 md2 A2 B2 errv2); [| exact FS2 | exact FRM2].
subst pbs2. exact INV2. }
step. step.
if_true.
step.
asan_rechkA.
step. step.
asan_rechkM 5.
step.
norm_sx32.
change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)).
step.
rewrite (unsigned_lit (Z.of_nat depth)) by lia.
rewrite Z.shiftl_mul_pow2 by lia.
change (2 ^ 5) with 32.
step.
replace (q + Z.of_nat depth * 32) with bse by lia.
do 3 step.
sh_norm.
step.
destruct (Z.eq_dec (bv_unsigned cb) 47) as [C47 | N47].
- if_falsex.
asan_rechkA.
stepz.
step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m2 mc, WMc : wmono asegs m2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5; subst bse;
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 mc md2 A2 B2 ts2
cb nb pj sv errv2 l ST_eatws (tl_ss l) c0 hn0 c0 STC INV2 Hl MUc WMc MIc TOKc Lc Hmode
ltac:(rewrite <- Hmode; apply QIsM.Mq2.lvl_mode_ws_same; [rewrite Hst; reflexivity | reflexivity])
ltac:(unfold ST_eatws; lia) SS26 (or_introl eq_refl) ltac:(rewrite Hst; reflexivity)) as [INV3 PBK3];
eapply (Kbreak mc md2 A2 B2 ST_eatws pbs2 errv2); [left; split; [exact C47 | reflexivity] | exact INV3 | exact (PBK3 1 PBK2) | exact (BOK_lvl_restate _ _ ts2 B2 nB l ST_eatws (tl_ss l) Hl (lvl_closed_keep l ST_eatws _ _ _ _ _ eq_refl) (BOK_weaken _ _ _ _ _ nB (Nat.le_succ_diag_r nB) BK2)) | exact FS2 | exact FRM2]
end end.
- if_truex.
asan_rechkA.
step. step.
stepz.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m2 mc, WMc : wmono asegs m2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5; subst bse;
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 mc md2 A2 B2 ts2
cb nb pj sv errv2 l ST_comment (tl_ss l) c0 hn0 c0 STC INV2 Hl MUc WMc MIc TOKc Lc Hmode
ltac:(rewrite <- Hmode; apply QIsM.Mq2.lvl_mode_ws_same; [rewrite Hst; reflexivity | reflexivity])
ltac:(unfold ST_comment; lia) SS26 (or_introl eq_refl) ltac:(rewrite Hst; reflexivity)) as [INV3 PBK3];
eapply (Kbreak mc md2 A2 B2 ST_comment pbs2 errv2); [right; split; [exact N47 | reflexivity] | exact INV3 | exact (PBK3 1 PBK2) | exact (BOK_lvl_restate _ _ ts2 B2 nB l ST_comment (tl_ss l) Hl (lvl_closed_keep l ST_comment _ _ _ _ _ eq_refl) (BOK_weaken _ _ _ _ _ nB (Nat.le_succ_diag_r nB) BK2)) | exact FS2 | exact FRM2]
end end.
Qed.
End PeSCendA.
End RC__1.
