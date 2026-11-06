(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmZZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYIF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYIF.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgoP.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXUB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXUB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRBl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqe. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9O6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9O6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qekr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qekr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJZd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJZd.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qw5U.Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqf.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSHS.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QupI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QupI.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC6R.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC6R. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qw5U.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql4f.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql4f.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q63E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q63E.Mq9.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnX9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpNt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

Ltac c1_bytes cs := lazymatch cs with | nil => constr:(@nil byte) | C1 ?b :: ?r => let r' := c1_bytes r in constr:(b :: r') end.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition SHB1 : list byte := firstn 8 SHB0 ++ map (Z_to_bv 8) [0; 0; 0] ++ skipn 11 SHB0.

Section AHarnJo3.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Variables (tpB tpD : Z -> Z) (dcB dcD : Z -> Z) (gsS : jshape -> Z) (gsB : Z -> Z).
Hypothesis CA : jo_callees_A HIx tpB tpD dcB dcD gsS gsB.

Lemma presB_rw_cells : forall S P L SP m m' A0 cs,
QnX9.crls_presB S P L SP m m' -> rw_cells asegs m A0 cs -> client_range A4H L SP A0 (Z.of_nat (cells_size cs)) ->
(A0 + Z.of_nat (cells_size cs) <= S \/ S + 24 <= A0) -> (A0 + Z.of_nat (cells_size cs) <= P \/ P + 16 <= A0) ->
rw_cells asegs m' A0 cs.
Proof.
intros S P L SP m m' A0 cs PR [[Hwf HB] HW] HR DS DP.
split; [split; [exact Hwf|]|].
- destruct HB as (B0 & B1 & HB'). split; [exact B0|]. split; [exact B1|].
intros i Hi. rewrite <- (HB' i Hi). unfold mrd.
rewrite (cells_bytes_length cs Hwf) in Hi. rewrite (cells_bytes_length cs Hwf) in B1.
destruct (PR (A0 + Z.of_nat i) ltac:(lia) ltac:(eapply client_range_addr; [exact HR | lia]) ltac:(lia) ltac:(lia)) as [E _].
rewrite E. reflexivity.
- destruct HB as (B0 & B1 & _). rewrite (cells_bytes_length cs Hwf) in B1.
destruct HW as (W0 & W1 & HWi). split; [exact W0|]. split; [exact W1|].
intros i Hi. destruct (PR (A0 + i) ltac:(lia) ltac:(eapply client_range_addr; [exact HR | lia]) ltac:(lia) ltac:(lia)) as [_ W].
apply W. apply HWi. exact Hi.
Qed.

Lemma seg_headA : forall (x1 gp t0 t1 t2 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 sp0 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet) (A : ASA A4L HIx) (LB LM : list blk) (B : bud)
(data size lo sp1 : Z) (payload j8 : list byte),
HEAPAx A LB LM [] B m md -> TGT_BB_A_jo <= bB B -> TGT_BD_A_jo <= bD B ->
bytes_at asegs m data payload -> Z.of_nat (length payload) = size -> 0 <= size < 2^26 -> 0 < data -> data + size <= alloc_ceiling ->
(size = 0 \/ In (data, size) LB) ->
rw_cells asegs m T_LOCCELL_A [C8 (Z_to_bv 64 T_GLOBLOC_A)] -> rw_cells asegs m T_LOCALE_LOCK_A [C4 (Z_to_bv 64 0)] -> GA_jo m ->
stk asegs m lo sp1 -> rw_cells asegs m sp1 [CB 8 j8] ->
alloc_ceiling <= lo -> lo <= sp1 - (2^20 - 144) -> hiA_bot A4L HIx <= lo -> sp1 mod 32 = 0 -> sp1 + 96 <= bv_unsigned sp0 -> bv_unsigned sp0 + 32 <= hiA_top A4L HIx ->
frm0 fc ->
Z.of_nat (length LM) < 8 ->
(forall n, 0 <= n <= 20 -> tpB n <= TGT_BB_A_jo /\ 1 + tpD n <= TGT_BD_A_jo) ->
(forall (Fr p n : Z) (s : option jshape) m' md' (A' : ASA A4L HIx) B' F' fc' ptr' rem' data' BS' LK' (y1 gp' y5 y6 y7 b0 b1 b2 b3 b4 b5 b6 b7 y28 y29 y30 y31 : word),
Fr mod 512 = 0 -> 6582272 <= Fr -> Fr + 512 <= alloc_ceiling -> (Fr + 512 + 8 <= A_SB \/ A_HMB <= Fr) -> 0 <= n <= 20 ->
(forall sh, s = Some sh -> exists w, jtx sh BS' = Some (w, []) /\ w <= 26 * (n + 1) + 64) ->
GINVA HIx sp0 sp1 lo Fr LB LM m md F B data size p m' md' A' B' F' fc' ptr' rem' data' s BS' LK' (tpB n) (1 + tpD n) ->
AJ5 A4L HIx A' T md' (hstateA sp0 sp1 Fr p s10 s11 y1 gp' y5 y6 y7 b0 b1 b2 b3 b4 b5 b6 b7 y28 y29 y30 y31 F' 0x92058 fc' m')) ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 sp1) gp (Z_to_bv 64 A_TP) t0 t1 t2 sp0 (Z_to_bv 64 sp1) (Z_to_bv 64 data) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x91eb0) fc None m (seg_rom asegs)).
Proof.
intros until j8. intros HP BB BD PAY PLEN SZ D0 DCE INB LOC LCK GA ST FDA LO LOS HBOT SPA1 SP10 HT FRM LML TPC K.
pose proof (bv_unsigned_in_range 64 sp0) as SP0R. change (bv_modulus 64) with (2^64) in SP0R.
pose proof alloc_ceiling_range as ACR. pose proof (hiA_top_le A4L HIx) as HT47.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. change (hl_segs A4L) with asegs in MI.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP) as (SB1 & SB2 & SB3 & SB4).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2. apply ro_C8_of_bytes_at in SB3.
assert (UARC : ro_cells asegs m (hl_uar_cell A4L) [C4 (Z_to_bv 64 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SB4]).
clear SB4. a4l.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(lo, sp1 + 8)] m) as MU.
unfold A_TP in *.
reenterA asegs A4L HIx asegs_wx HP.
step. step. step. step. step.
step. norm_sx32. step. step.
step. if_false.
step. step.
evt_done5.
eapply (stack_malloc_full HIx) with (k := 3) (bytes := 288) (lo := lo) (LB := LB) (LM := LM) (FR := @nil frame) (B := B);
[ exact HP | right; split; [reflexivity | split; [cbn; lia | cbn [length]; lia]] | .. ].
all: rewrite ?unsigned_lit by lia.
1: rewrite fr_size_3; lia.
1: reflexivity.
1: cbn [length]; lia.
1: exact ST.
1: exact LO.
1: cbn [hl_stack_A A4L]; lia.
1: clear - SPA1; Z.div_mod_to_equations; lia.
1: lia.
1: reflexivity.
1: reflexivity.
intros ms1 m1 md1 A1 Fr RS1 VM1 ST1 HPR1 FRNZ (jff & FF1) SHBZ HP1. open_ret RS1.
rewrite ?unsigned_lit in ST1, HPR1 by lia.

assert (INF : In (Fr, 3) [(Fr, 3)]) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as (_ & HFal & HF0 & HFc & HFimg & _ & HFshw & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFapp.
pose proof (frame_above_img HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFhi.
rewrite fr_size_3 in HFal, HFc, HFimg, HFapp. rewrite fr_shadow_len_3 in HFshw. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp, HFhi.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in FDA; [| left; cbn; lia].
assert (LOCcs : forall a, 6444320 - 48 <= a < 6444320 - 48 + 8 -> hl_client_static A4H a).
{ intros a Ha. cbn [hl_client_static A4H]. unfold a4_client_static. lia. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in LOC; [| right; left; cbn; intros z Hz; apply LOCcs; unfold T_LOCCELL_A, A_TP in Hz; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in LCK; [| right; left; cbn; intros z Hz; cbn [hl_client_static A4H]; unfold a4_client_static; unfold T_LOCALE_LOCK_A in Hz; lia].
assert (GA1 : GA_jo m1) by (eapply GA_jo_pres; [exact HPR1 | exact GA]).
assert (PAY1 : bytes_at asegs m1 data payload).
{ eapply (window_bytesG LB data size); [exact INB | exact PAY | exact PLEN | lia | lia |].
intros a Ha (b & Hb & Hr). apply (HPR1 a Ha). right; right. exists b. split; [apply in_or_app; left; exact Hb | exact Hr]. }
assert (PX1 : heap_presx A4H (xtgt_A (bv_unsigned sp0)) (LB ++ LM) (sp1 + 8) m m1).
{ apply heap_pres_presx. eapply heap_pres_weaken; [exact HPR1 | lia |]. intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; exact Hb | right; apply in_or_app; left; exact Hb]. }
clear SB1 SB2 SB3 UARC PAY GA. stash PAY1.
unfold T_LOCCELL_A, T_LOCALE_LOCK_A, A_TP in LOC, LCK.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP1) as (SB1 & SB2 & _ & _).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2. a4l.
assert (FSH1 : rw_cells asegs m1 (shad A4L Fr) [CB 64 (repeat (Z_to_bv 8 0) 64)]).
{ split; [split; [cbn; split; [reflexivity | exact I] | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SHBZ] | exact HFshw]. }
rewrite fr_size_3 in FF1. change (Z.to_nat (512 - 8)) with 504%nat in FF1.
unfold shad in FSH1. a4l.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 64 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1. change (hl_segs A4L) with asegs in MI1. clear MI.
clear MU WM. pose proof (wmono_refl asegs m1) as WM. pose proof (munch_refl [(lo, sp1 + 8); (Fr, Fr + 504); (sh, sh + 64)] m1) as MU.
unfold A_SB in HFapp.
reenterA asegs A4L HIx asegs_wx HP1.
step. step. step. step. if_truex.
stepz.
step. step.
step. step. step. step.
rewrite (unsigned_lit Fr) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
step. step. step. step.
stepz. stepz. stepz.
step. step.
fold sh.
do 4 stepz. step. do 28 stepz. step. do 4 stepz.
stepz. stepz.
do 3 stepz.
step. step. step. step.

assert (FRAL : Fr mod 512 = 0) by exact HFal.
assert (FRLO : 6582272 <= Fr) by exact HFhi.
assert (FRHI : Fr + 512 <= alloc_ceiling) by exact HFc.
assert (FRAPP : Fr + 512 + 8 <= A_SB \/ A_HMB <= Fr) by (unfold A_SB, A_HMB; clear - HFapp; change ((2 ^ 47 - 1) / 8 + 2147450880 + 1) with 17594333495296 in HFapp; lia).
pose proof (fdp_evidenceA HIx sp0 sp1 lo Fr LB LM m md F B data size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP) as EVD.
pose proof (fslot_evidenceA HIx sp0 sp1 lo Fr LB LM m md F B data size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP) as FSL.
pose proof (own_writesA HIx sp0 sp1 lo Fr LB LM m md F B data size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP) as OWN.
pose proof (GA_jo_own HIx sp0 sp1 lo Fr LB LM m md F B data size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP) as GAO.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m2 end.
lazymatch goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
assert (WOK : Forall (own_iv sp1 lo Fr) [(lo, sp1 + 8); (Fr, Fr + 504); (sh, sh + 64)]).
{ unfold own_iv, sh. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
destruct (OWN A1 LB B m1 m2 md1 _ HP1 (incl_refl _) MU WM MI2 WOK) as (HP2 & HPX2 & AG2).
unstash PAY1.
assert (PAY2 : bytes_at asegs m2 data payload).
{ eapply (window_bytesG LB data size); [exact INB | exact PAY1 | exact PLEN | lia | lia |].
intros a Ha (b & Hb & Hr). apply (AG2 a Ha). exists b. split; [apply in_or_app; left; exact Hb | exact Hr]. }
clear PAY1.

let cs := eval cbv in (map C1 SHB1) in
apply (rw_cells_recast asegs m2 sh _ cs) in FSH1; [| cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity].
assert (UNS2 : unpoisoned asegs m2 A_SB (Fr + 64) 24).
{ pose proof (FSL m2 SHB1 8%nat 11%nat FSH1 eq_refl ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)) as U.
change (Fr + 8 * Z.of_nat 8) with (Fr + 64) in U. change (8 * Z.of_nat (11 - 8)) with 24 in U. exact U. }
destruct (EVD A1 LB B m2 md1 SHB1 data size HP2 (incl_refl _) FSH1 eq_refl ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as (RT2 & UNP2 & UND2).

lazymatch type of FF1 with rw_cells _ _ _ [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6] =>
change [c0; c1; c2; c3; c4; c5; c6] with ([c0; c1; c2; c3] ++ ([c4; c5] ++ [c6])) in FF1 end.
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FF1 as [HDR FX]. cbn [cells_size csize Nat.add] in FX. replace (Fr + Z.of_nat 32) with (Fr + 32) in FX by lia.
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FX as [FDP BODY]. cbn [cells_size csize Nat.add] in BODY. replace (Fr + 32 + Z.of_nat 16) with (Fr + 48) in BODY by lia.
destruct (rw_cells_CB_cut asegs _ _ _ _ 16 BODY ltac:(lia)) as [G6 B1]. clear BODY. change (Z.of_nat 16) with 16 in B1. change (456 - 16)%nat with 440%nat in B1.
replace (Fr + 48 + 16) with (Fr + 64) in B1 by lia.
destruct (rw_cells_CB_cut asegs _ _ _ _ 24 B1 ltac:(lia)) as [S1 B2]. clear B1. change (Z.of_nat 24) with 24 in B2. change (440 - 24)%nat with 416%nat in B2.
replace (Fr + 64 + 24) with (Fr + 88) in B2 by lia.
assert (GA2 : GA_jo m2) by (exact (GAO m1 m2 _ GA1 MU WM WOK)).
assert (PX2 : heap_presx A4H (xtgt_A (bv_unsigned sp0)) (LB ++ LM) (sp1 + 8) m m2) by (eapply heap_presx_trans; [exact PX1 | exact HPX2]).
clear EVD HPX2 AG2 RT2 MU WM GA1 PX1.
stash HDR. stash G6. stash B2. stash LOC. stash LCK. stash FDA. stash SB1. stash SB2.
evt_done5.
eapply (QnX9.crls_A HIx) with (S := Fr + 64) (P := Fr + 32) (ptr := data) (rem := size) (lo := lo) (maxlen := 20) (data := payload) (LB := LB) (LM := LM) (FRS := [(Fr, 3)]) (B := B);
rewrite ?unsigned_lit by lia;
first [ reflexivity | exact HP2 | exact S1 | exact UNS2 | exact FDP | exact UNP2 | exact PAY2 | exact PLEN | exact D0 | exact LO | exact SPA1 | exact MI2
| lazymatch goal with H : stk asegs m2 lo sp1 |- stk _ _ _ _ => exact H end
| idtac ].
all: lazymatch goal with |- forall _, _ => idtac | |- _ => try solve [ lia | cbn [length]; lia | clear - FRAL; Z.div_mod_to_equations; lia | unfold QnX9.CRLS_STK_B; lia
| exists Fr, 3; split; [left; reflexivity | rewrite fr_size_3; lia]
| destruct INB as [Z0 | INB']; [left; exact Z0 | right; exists data, size; split; [exact INB' | lia]] ] end.
1,2: destruct INB as [Z0 | INB']; [left; exact Z0 | right];
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP2 INF (in_or_app _ _ _ (or_introl INB'))) as DF; rewrite fr_size_3 in DF; lia.
intros ms3 m3 md3 A3 n1 k1 str1 rest1 yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 -> VM3 ST3 PRES3 HP3 MI3 Hn1 Hstr1 NONUL1 STR3 Hk1 FD3 PAY3.
clear S1 FDP PAY2 UNP2 UND2 UNS2 MI2.
replace (ret_pc (Z_to_bv 64 0x92008)) with (Z_to_bv 64 0x92008) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

unstash HDR. unstash G6. unstash B2. unstash LOC. unstash LCK. unstash FDA. unstash SB1. unstash SB2.
assert (INFR : In (Fr, 504) (LB ++ LM ++ fr_ivs A4L [(Fr, 3)])) by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
assert (INSH : In (sh, 64) (LB ++ LM ++ fr_ivs A4L [(Fr, 3)])) by (apply in_or_app; right; apply in_or_app; right; right; left; reflexivity).
apply (presB_rw_cells _ _ _ _ _ _ _ _ PRES3) in HDR; [| right; right; exists (Fr, 504); split; [exact INFR | cbn; lia] | cbn; lia | cbn; lia].
apply (presB_rw_cells _ _ _ _ _ _ _ _ PRES3) in G6; [| right; right; exists (Fr, 504); split; [exact INFR | cbn; lia] | cbn; lia | cbn; lia].
apply (presB_rw_cells _ _ _ _ _ _ _ _ PRES3) in B2; [| right; right; exists (Fr, 504); split; [exact INFR | cbn; lia] | cbn; lia | cbn; lia].
pose proof FRAPP as FRAPPu. unfold A_SB, A_HMB in FRAPPu.
apply (presB_rw_cells _ _ _ _ _ _ _ _ PRES3) in FSH1; [| right; right; exists (sh, 64); split; [exact INSH | cbn; lia] | cbn; unfold sh; clear - FRAPPu FRLO; Z.div_mod_to_equations; lia | cbn; unfold sh; clear - FRAPPu FRLO; Z.div_mod_to_equations; lia].
apply (presB_rw_cells _ _ _ _ _ _ _ _ PRES3) in FDA; [| left; cbn; lia | cbn; lia | cbn; lia].
apply (presB_rw_cells _ _ _ _ _ _ _ _ PRES3) in LOC; [| right; left; cbn; intros z Hz; apply LOCcs; lia | cbn; lia | cbn; lia].
apply (presB_rw_cells _ _ _ _ _ _ _ _ PRES3) in LCK; [| right; left; cbn; intros z Hz; cbn [hl_client_static A4H]; unfold a4_client_static; lia | cbn; lia | cbn; lia].
assert (GA3 : GA_jo m3).
{ destruct (proj1 GA2) as (GH & [seed GS]).
apply (presB_rw_cells _ _ _ _ _ _ _ _ PRES3) in GH; [| right; left; cbn; intros z Hz; cbn [hl_client_static A4H]; unfold a4_client_static; unfold GHASHA in Hz; lia | cbn; unfold GHASHA; lia | cbn; unfold GHASHA; lia].
apply (presB_rw_cells _ _ _ _ _ _ _ _ PRES3) in GS; [| right; left; cbn; intros z Hz; cbn [hl_client_static A4H]; unfold a4_client_static; unfold GSEEDA in Hz; lia | cbn; unfold GSEEDA; lia | cbn; unfold GSEEDA; lia].
eapply GA_jo_pointwise; [exact GA2 | split; [exact GH | exists seed; exact GS] |].
intros a Ha. apply (PRES3 a); [lia | right; left; cbn [hl_client_static A4H]; unfold a4_client_static; lia | lia | lia]. }
assert (PX3 : heap_presx A4H (xtgt_A (bv_unsigned sp0)) (LB ++ LM) (sp1 + 8) m m3).
{ assert (INF3 : In (Fr, 3) [(Fr, 3)]) by (left; reflexivity).
intros a Ha CAx. destruct (PX2 a Ha CAx) as [E1 W1].
assert (NSP : ~ (Fr + 64 <= a < Fr + 64 + 24) /\ ~ (Fr + 32 <= a < Fr + 32 + 16)).
{ destruct CAx as [H | [[H _] | ((ba & bn) & Hb & Hr)]].
- clear - H LO LOS FRHI. lia.
- cbn [hl_client_static A4H] in H. unfold a4_client_static in H. clear - H FRLO. lia.
- pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP3 INF3 Hb) as DF. rewrite fr_size_3 in DF. cbn [blk_addr blk_size fst snd] in Hr. clear - DF Hr. lia. }
destruct NSP as [NS NP].
destruct (PRES3 a Ha ltac:(destruct CAx as [H | [[H _] | H]]; [left; clear - H; lia | right; left; exact H | right; right; unfold in_block in H |- *; destruct H as (b & Hb & Hr); exists b; split; [apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; exact Hb | right; apply in_or_app; left; exact Hb] | exact Hr]]) NS NP) as [E2 W2].
split; [rewrite E2; exact E1 | intros W; exact (W2 (W1 W))]. }

pose proof (wmono_refl asegs m3) as WM. pose proof (munch_refl [(lo, sp1 + 8); (Fr, Fr + 504); (sh, sh + 64)] m3) as MU.
stash PAY3. stash B2. stash G6. stash HDR.
reenterA asegs A4L HIx asegs_wx HP3.
step. step. rewrite short_flag0A by lia. step. if_false. step. step. step.
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP3) as (errv4 & ERR4). cbn [hl_tp hl_segs A4L A4H hla_base] in ERR4.
assert (LREST : Z.of_nat (length rest1) = 22 - Z.of_nat (length str1)).
{ destruct STR3 as [[WF _] _]. cbn in WF. rewrite length_app in WF. cbn [length] in WF. lia. }
pose proof STR3 as STRB. apply rw_cells_app with (cs1 := [_]) in STRB as [_ STRB]. cbn [cells_size csize Nat.add] in STRB.
pose proof (rw_cells_bytes_at asegs m3 _ _ STRB) as SB. cbn [cells_bytes cbytes app] in SB. rewrite app_nil_r in SB.
change (Fr + 64 + Z.of_nat 1) with (Fr + 64 + 1) in SB.
assert (UNS4 : unpoisoned asegs m3 A_SB (Fr + 64) 24).
{ pose proof (FSL m3 SHB1 8%nat 11%nat FSH1 eq_refl ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)) as U.
change (Fr + 8 * Z.of_nat 8) with (Fr + 64) in U. change (8 * Z.of_nat (11 - 8)) with 24 in U. exact U. }
pose proof (TPC (Z.of_nat (length str1)) ltac:(lia)) as CTP.
pose proof (ca_TOKPARSE _ _ _ _ _ _ _ CA) as TPA. unfold jo_tokparse_A_stmt, JO_TOKPARSE_A, JO_TOKPARSE_STK_A, JO_TOKPARSE_URA_A in TPA.
replace (str1 ++ Z_to_bv 8 0 :: rest1) with (str1 ++ Z_to_bv 8 0 :: rest1) in SB by reflexivity.
evt_done5.
eapply TPA with (A := A3) (LBc := LB) (FRS := [(Fr, 3)]) (B := B) (sb := Fr + 64 + 1) (lo := lo) (str0 := str1) (slack := rest1) (errv := errv4) (u := UWpaid).
- split; [exact HP3|]. rewrite unsigned_lit by lia.
split; [exact ST3|]. split; [exact LO|]. split; [lia|]. split; [clear - SPA1; Z.div_mod_to_equations; lia|]. split; [lia|].
split; [exact ERR4|]. split; [reflexivity | vm_compute; reflexivity].
- rewrite unsigned_lit by lia. exact SPA1.
- exact LML.
- split; [exact SB|]. split; [apply Forall_forall; intros b Hb E0; apply NONUL1; replace (Z_to_bv 8 0) with b by (apply bv_eq; rewrite E0; reflexivity); exact Hb|].
split; [rewrite LREST; clear - FRAL Hstr1 Hn1; Z.div_mod_to_equations; lia|].
split; [exists Fr, 3; split; [exact INF|]; rewrite fr_size_3; lia|].
eapply (QsKa.Mqa.unpoisoned_sub_any asegs _ A_SB (Fr + 64) 24); [exact UNS4 | lia | lia | lia].
- lia.
- split; [exact LOC|]. split; [exact LCK|]. split; [exact (proj1 GA3) | exact (proj2 (proj2 GA3))].
- exact I.
- exact I.
- cbn [length]. lia.
- destruct CTP; lia.
- cbn [uw_cost]. destruct CTP; lia.
- exact FRM.
- f_equal. lia.
- idtac.
intros ms5 md5 m5 A5 B5 gp5 r errv5 RBS LK RS5 VM5 ST5 ERR5 (LOC5 & LCK5 & LHG5 & UTF5) HPX5 [CHB5 CHD5] HP5 ROOT.
destruct RS5 as (xt0 & xt1 & xt2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & F5 & fc5 & -> & FS5 & FRM5).
rewrite unsigned_lit in ST5, HPX5 by lia.
unstash PAY3. unstash B2. unstash G6. unstash HDR.
apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPX5) in HDR; [| right; right; exists (Fr, 504); split; [exact INFR | cbn; lia]].
apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPX5) in G6; [| right; right; exists (Fr, 504); split; [exact INFR | cbn; lia]].
apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPX5) in STR3; [| right; right; exists (Fr, 504); split; [exact INFR | cbn; lia]].
apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPX5) in B2; [| right; right; exists (Fr, 504); split; [exact INFR | cbn; lia]].
apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPX5) in FD3; [| right; right; exists (Fr, 504); split; [exact INFR | cbn; lia]].
apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPX5) in FSH1; [| right; right; exists (sh, 64); split; [exact INSH | cbn; lia]].
apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPX5) in FDA; [| left; lia].
assert (PAY5 : bytes_at asegs m5 data payload).
{ eapply (window_bytesG LB data size); [exact INB | exact PAY3 | exact PLEN | lia | lia |].
intros a Ha (b & Hb & Hr). apply (HPX5 a Ha). right; right. exists b. split; [apply in_or_app; left; exact Hb | exact Hr]. }
assert (GA5 : GA_jo m5).
{ eapply GA_jo_pointwise; [exact GA3 | exact LHG5 |]. intros a Ha. apply (HPX5 a); [lia|]. right; left.
split; [cbn [hl_client_static A4H]; unfold a4_client_static; lia|]. unfold xlocA, a4_volatile, QlKV.Mqe.LOCCELL_A, A_TP. lia. }
clear PAY3 LOC LCK ERR4 STRB SB UNS4 HP3 MU WM MI3.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI5. change (hl_segs A4L) with asegs in MI5.
pose proof (wmono_refl asegs m5) as WM. pose proof (munch_refl [(lo, sp1 + 8); (Fr, Fr + 504); (sh, sh + 64)] m5) as MU.
unfold QlKV.Mqe.LOCCELL_A, QlKV.Mqe.LOCALE_LOCK_A, QlKV.Mqe.GLOBLOC_A, A_TP in LOC5, LCK5.
stash PAY5.
change (hl_segs A4H) with asegs in *.
reenterA asegs A4L HIx asegs_wx HP5. change (hl_segs A4H) with asegs.
step.
step. step. rewrite short_flag0A by lia. step. step. if_true.
step. do 3 stepz.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m6 end.
lazymatch goal with H : mem_inv asegs m6 |- _ => rename H into MI6 end.
lazymatch goal with H : munch _ m5 m6 |- _ => rename H into MU6 end.
lazymatch goal with H : wmono asegs m5 m6 |- _ => rename H into WM6 end.
assert (INCL5 : incl LB (RBS ++ LK ++ LB)) by (intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb).
destruct (OWN A5 (RBS ++ LK ++ LB) B5 m5 m6 md5 _ HP5 INCL5 MU6 WM6 MI6 WOK) as (HP6 & HPX6 & AG6).
assert (PX6 : heap_presx A4H (xtgt_A (bv_unsigned sp0)) (LB ++ LM) (sp1 + 8) m m6).
{ eapply heap_presx_trans; [| exact HPX6]. eapply heap_presx_trans; [exact PX3|].
eapply heap_presx_weaken; [exact HPX5 | lia | |].
- intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; exact Hb | right; apply in_or_app; left; exact Hb].
- intros a [Xa | Xa]; [left; exact Xa | right; left; unfold T_LOCCELL_A; exact Xa]. }
unstash PAY5.
assert (PAY6 : bytes_at asegs m6 data payload).
{ eapply (window_bytesG (RBS ++ LK ++ LB) data size); [destruct INB as [Z0|I1]; [left; exact Z0 | right; apply INCL5; exact I1] | exact PAY5 | exact PLEN | lia | lia |].
intros a Ha (b & Hb & Hr). apply (AG6 a Ha). exists b. split; [apply in_or_app; left; exact Hb | exact Hr]. }
pose proof (bytes_at_skipn asegs m6 data payload k1 PAY6 ltac:(lia)) as WIN6.
assert (GA6 : GA_jo m6) by (exact (GAO m5 m6 _ GA5 MU6 WM6 WOK)).

assert (FJ0 : exists fj0, rw_cells asegs m6 Fr [CB 32 fj0]).
{ lazymatch type of HDR with rw_cells _ _ _ ?cs => change (rw_cells asegs m6 Fr ([] ++ cs ++ [])) in HDR end.
apply rw_cells_merge in HDR. cbn [app] in HDR.
lazymatch type of HDR with rw_cells _ _ _ [CB ?n ?b] => exists b; let v := eval vm_compute in n in change n with v in HDR end. exact HDR. }
assert (FJ1 : exists fj1, rw_cells asegs m6 (Fr + 48) [CB 456 fj1]).
{ lazymatch type of STR3 with rw_cells _ _ _ ?c3 => lazymatch type of B2 with rw_cells _ _ _ ?c4 =>
assert (X1 : rw_cells asegs m6 (Fr + 64) (c3 ++ c4)) by (apply (proj2 (rw_cells_app asegs m6 (Fr + 64) c3 c4)); split; [exact STR3 | cbn [cells_size csize Nat.add]; replace (Fr + 64 + Z.of_nat 24) with (Fr + 88) by lia; exact B2]) end end.
lazymatch type of G6 with rw_cells _ _ _ ?c2 => lazymatch type of X1 with rw_cells _ _ _ ?c34 =>
assert (X2 : rw_cells asegs m6 (Fr + 48) (c2 ++ c34)) by (apply (proj2 (rw_cells_app asegs m6 (Fr + 48) c2 c34)); split; [exact G6 | cbn [cells_size csize Nat.add]; replace (Fr + 48 + Z.of_nat 16) with (Fr + 64) by lia; exact X1]) end end.
lazymatch type of X2 with rw_cells _ _ _ ?cs => change (rw_cells asegs m6 (Fr + 48) ([] ++ cs ++ [])) in X2 end.
apply rw_cells_merge in X2. cbn [app] in X2.
lazymatch type of X2 with rw_cells _ _ _ [CB ?n ?b] => exists b; let v := eval vm_compute in n in change n with v in X2 end. exact X2. }
destruct FJ0 as [fj0 FJ0]. destruct FJ1 as [fj1 FJ1].
assert (VM6 : model_vm_only (cfg_model md) (cfg_model md5)) by (eapply model_vm_only_trans; [exact VM1 | eapply model_vm_only_trans; [exact VM3 | exact VM5]]).
lazymatch goal with H : stk asegs m6 lo sp1 |- _ => rename H into ST6 end.
assert (HI6 : HINVA sp0 sp1 lo Fr LB LM m md F data size SHB0 m6 md5 F5 fc5 (data + k1) (size - k1) (skipn (Z.to_nat k1) payload)).
{ unfold HINVA. split; [exact PX6|]. split; [exact VM6|]. split; [exact FS5|]. split; [exact (FRM5 FRM)|].
split; [exact LOC5|]. split; [exact LCK5|]. split; [exact GA6|]. split; [exact ST6|].
split; [exact FDA|]. split; [exact FD3|]. split; [exists fj0, fj1; split; [exact FJ0 | exact FJ1]|]. split; [exact FSH1|]. split; [reflexivity|].
split; [exact WIN6|]. split; [rewrite length_skipn; lia|]. lia. }
assert (JO6 : exists s : option jshape, jopt asegs A4F s m6 RBS r /\ odepth s <= 32 /\
(forall sh, s = Some sh -> exists w, jtx sh RBS = Some (w, []) /\ w <= 26 * (Z.of_nat (length str1) + 1) + 64)).
{ destruct ROOT as [[-> ->] | (Hr & s & J & SD & w & JTX & WLE)].
- exists None. split; [split; reflexivity | split; [cbn; lia | intros sh0 E; discriminate]].
- exists (Some s). split; [| split; [exact SD | intros sh0 E; injection E as <-; exists w; split; [exact JTX | exact WLE]]]. split; [exact Hr|].
eapply (jval_agree asegs A4F s (RBS ++ LK ++ LB ++ LM)); [exact J | | intros b Hb; apply in_or_app; left; exact Hb].
eapply agree_on_incl; [exact AG6|]. intros b Hb. rewrite <- !app_assoc. exact Hb. }
destruct JO6 as (s & JO6 & OD6 & WT6).
unfold hstateA in K. unfold sh.
evt_done5.
eapply (K Fr r (Z.of_nat (length str1)) s m6 md5 A5 B5 F5 fc5 (data + k1) (size - k1) (skipn (Z.to_nat k1) payload) RBS LK); [exact FRAL | exact FRLO | exact FRHI | exact FRAPP | lia | exact WT6 |].
unfold GINVA. split; [exact HI6|]. split; [exact HP6|]. split; [exact JO6|]. split; [exact OD6|]. cbn [uw_cost] in CHD5. split; lia.
Qed.
End AHarnJo3.
End RC__1.
