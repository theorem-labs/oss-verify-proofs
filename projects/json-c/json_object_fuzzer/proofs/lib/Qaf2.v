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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPZI.Mq4.
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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QupI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QupI.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC6R.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC6R. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qw5U.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql4f.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql4f.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q63E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q63E.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpFy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpFy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKdU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKdU.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpNt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

Ltac c1_bytes cs := lazymatch cs with | nil => constr:(@nil byte) | C1 ?b :: ?r => let r' := c1_bytes r in constr:(b :: r') end.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section AHarnJo4.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Variables (tpB tpD : Z -> Z) (dcB dcD : Z -> Z) (gsS : jshape -> Z) (gsB : Z -> Z).
Hypothesis CA : jo_callees_A HIx tpB tpD dcB dcD gsS gsB.

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
Variables (p : Z) (s10 s11 : word) (T : TSet).
Hypothesis BB0 : TGT_BB_A_jo <= bB B0.
Hypothesis BD0 : TGT_BD_A_jo <= bD B0.
Variable wtx : Z.
Collection CtxAll := RC__ HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP p s10 s11 T BB0 BD0.

Notation HINVAc := (HINVA sp0 sp1 lo Fr LB0 LM m0 md0 F0 data0 size).
Notation sstateBc := (sstateB sp0 sp1 Fr p s10 s11).
Notation XT := (xtgt_A (bv_unsigned sp0)).
Let HINVA_callc := HINVA_call HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP.
Let OWNc := own_writesA HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP.
Let GAOc := GA_jo_own HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP.
Let FSLc := fslot_evidenceA HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP.

#[using="CtxAll"] Lemma HINVA_callD : forall shb m m' md md' (A : ASA A4L HIx) B F F' fc fc' ptr rem data LBh LBx (qv : word),
HINVAc shb m md F fc ptr rem data -> HEAPAx A LBh LM [(Fr, 3)] B m md -> incl LB0 LBx -> incl LBx LBh ->
heap_presxDA (Fr + 256) (LBx ++ LM ++ fr_ivs A4L [(Fr, 3)]) sp1 m m' ->
model_vm_only (cfg_model md) (cfg_model md') -> fsaved F F' -> frm0 fc' ->
stk asegs m' lo sp1 -> lh_globA m' -> rw_cells asegs m' (Fr + 256) [C8 qv] ->
HINVAc shb m' md' F' fc' ptr rem data.
Proof.
intros shb m m' md md' A B F F' fc fc' ptr rem data LBh LBx qv
(PX & VM & FS & FRM & LOC & LCK & G & ST & SL & FD & (fj0 & fj1 & FF0 & FF1) & FSH & LSH & BY & L & P0 & P1 & P2) HP Hi Hi2 HPD VM' FS' FRM' ST' LHG' DC'.
pose proof alloc_ceiling_range as ACR.
assert (INF : In (Fr, 3) [(Fr, 3)]) by (left; reflexivity).
assert (INFR : In (Fr, 504) (LBx ++ LM ++ fr_ivs A4L [(Fr, 3)])) by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
assert (INSH : In (Fr / 8 + 2147450880, 64) (LBx ++ LM ++ fr_ivs A4L [(Fr, 3)])) by (apply in_or_app; right; apply in_or_app; right; right; left; reflexivity).
pose proof FRAPP as FRAPPu. unfold A_SB, A_HMB in FRAPPu.

assert (NOTD : forall a, client_addrx A4H XT (LB0 ++ LM) (sp1 + 8) a -> ~ (Fr + 256 <= a < Fr + 256 + 8)).
{ intros a [Ha | [[Ha _] | (b & Hb & Hr)]] HD.
- lia.
- pose proof (hl_static_in_img A4L a Ha) as Hi'. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hi'. lia.
- destruct b as [ba bn]. cbn [blk_addr blk_size fst snd] in Hr.
assert (Hb' : In (ba, bn) (LBh ++ LM)) by (apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply Hi2; apply Hi; exact Hb | right; exact Hb]).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF Hb') as DF. rewrite fr_size_3 in DF. lia. }
assert (EQ : forall a, 0 <= a < 2^64 -> client_addrx A4H (hl_volatile A4H) (LBx ++ LM ++ fr_ivs A4L [(Fr, 3)]) sp1 a -> ~ (Fr + 256 <= a < Fr + 256 + 8) ->
m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None)) by (intros a Ha Hc Hd; exact (HPD a Ha Hc Hd)).
assert (LOCcs : forall a, T_LOCCELL_A <= a < T_LOCCELL_A + 8 -> hl_client_static A4H a /\ ~ hl_volatile A4H a).
{ intros a Ha. unfold T_LOCCELL_A, A_TP in Ha. cbn [hl_client_static hl_volatile A4H]. unfold a4_client_static, a4_volatile. lia. }
assert (LCKcs : forall a, T_LOCALE_LOCK_A <= a < T_LOCALE_LOCK_A + 4 -> hl_client_static A4H a /\ ~ hl_volatile A4H a).
{ intros a Ha. unfold T_LOCALE_LOCK_A in Ha. cbn [hl_client_static hl_volatile A4H]. unfold a4_client_static, a4_volatile. lia. }
pose proof (rw_cells_bound _ _ _ _ LOC) as LB1. pose proof (rw_cells_bound _ _ _ _ LCK) as LB2. pose proof (rw_cells_bound _ _ _ _ SL) as LB3.
pose proof (rw_cells_bound _ _ _ _ FD) as LB4. pose proof (rw_cells_bound _ _ _ _ FF0) as LB5. pose proof (rw_cells_bound _ _ _ _ FF1) as LB7. pose proof (rw_cells_bound _ _ _ _ FSH) as LB6.
cbn [cells_size csize Nat.add] in LB1, LB2, LB3, LB4, LB5, LB7. rewrite cells_size_C1, LSH in LB6.
unfold HINVA. split.
{ eapply heap_presx_trans; [exact PX|]. intros a Ha Hc. apply (EQ a Ha); [| exact (NOTD a Hc)].
destruct Hc as [Hc | [[Hc Hx] | (b & Hb & Hr)]]; [left; lia | right; left; split; [exact Hc | intros V; apply Hx; left; exact V] | right; right].
exists b. split; [| exact Hr]. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply Hi; exact Hb | right; apply in_or_app; left; exact Hb]. }
split; [eapply model_vm_only_trans; [exact VM | exact VM']|]. split; [eapply fsaved_trans; [exact FS | exact FS']|]. split; [exact FRM'|].
split. { eapply rw_cells_pointwiseA; [exact LOC|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. pose proof (LOCcs a ltac:(lia)) as Hs. unfold T_LOCCELL_A, A_TP in Ha. apply (EQ a); [lia | right; left; exact Hs | lia]. }
split. { eapply rw_cells_pointwiseA; [exact LCK|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. pose proof (LCKcs a ltac:(lia)) as Hs. unfold T_LOCALE_LOCK_A in Ha. apply (EQ a); [lia | right; left; exact Hs | lia]. }
split. { eapply GA_jo_pointwise; [exact G | exact LHG' |]. intros a Ha.
refine (proj1 (EQ a _ _ _)); [lia | right; left; cbn [hl_client_static hl_volatile A4H]; unfold a4_client_static, a4_volatile; lia | lia]. }
split; [exact ST'|].
split. { eapply rw_cells_pointwiseA; [exact SL|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply (EQ a); [lia | left; lia | lia]. }
split. { eapply rw_cells_pointwiseA; [exact FD|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply (EQ a); [lia | right; right; exists (Fr, 504); split; [exact INFR | cbn; lia] | lia]. }
split.
{ exists fj0.
destruct (rw_cells_CB_cut asegs _ _ _ _ 208 FF1 ltac:(lia)) as [FA FB']. change (Z.of_nat 208) with 208 in FB'. change (456 - 208)%nat with 248%nat in FB'.
destruct (rw_cells_CB_cut asegs _ _ _ _ 8 FB' ltac:(lia)) as [_ FB]. change (Z.of_nat 8) with 8 in FB. change (248 - 8)%nat with 240%nat in FB.
replace (Fr + 48 + 208 + 8) with (Fr + 264) in FB by lia. replace (Fr + 48 + 208) with (Fr + 256) in FA |- * by lia.
assert (FF0' : rw_cells asegs m' Fr [CB 32 fj0]).
{ eapply rw_cells_pointwiseA; [exact FF0|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply (EQ a); [lia | right; right; exists (Fr, 504); split; [exact INFR | cbn; lia] | lia]. }
assert (FA' : rw_cells asegs m' (Fr + 48) [CB 208 (firstn 208 fj1)]).
{ eapply rw_cells_pointwiseA; [exact FA|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply (EQ a); [lia | right; right; exists (Fr, 504); split; [exact INFR | cbn; lia] | lia]. }
assert (FBm : rw_cells asegs m' (Fr + 264) [CB 240 (skipn 8 (skipn 208 fj1))]).
{ eapply rw_cells_pointwiseA; [exact FB|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply (EQ a); [lia | right; right; exists (Fr, 504); split; [exact INFR | cbn; lia] | lia]. }
assert (X1 : rw_cells asegs m' (Fr + 256) ([C8 qv] ++ [CB 240 (skipn 8 (skipn 208 fj1))])) by (apply (proj2 (rw_cells_app asegs m' (Fr + 256) _ _)); split; [exact DC' | cbn [cells_size csize Nat.add]; replace (Fr + 256 + Z.of_nat 8) with (Fr + 264) by lia; exact FBm]).
assert (X3 : rw_cells asegs m' (Fr + 48) ([CB 208 (firstn 208 fj1)] ++ ([C8 qv] ++ [CB 240 (skipn 8 (skipn 208 fj1))]))) by (apply (proj2 (rw_cells_app asegs m' (Fr + 48) _ _)); split; [exact FA' | cbn [cells_size csize Nat.add]; replace (Fr + 48 + Z.of_nat 208) with (Fr + 256) by lia; exact X1]).
lazymatch type of X3 with rw_cells _ _ _ ?cs => change (rw_cells asegs m' (Fr + 48) ([] ++ cs ++ [])) in X3 end.
apply rw_cells_merge in X3. cbn [app] in X3.
lazymatch type of X3 with rw_cells _ _ _ [CB ?n ?b] => exists b; let v := eval vm_compute in n in change n with v in X3 end. split; [exact FF0' | exact X3]. }
split. { eapply rw_cells_pointwiseA; [exact FSH|]. intros a Ha. rewrite cells_size_C1, LSH in Ha. apply (EQ a); [lia | right; right; exists (Fr / 8 + 2147450880, 64); split; [exact INSH | cbn; lia] | clear - Ha FRAPPu FRLO FRHI ACR; Z.div_mod_to_equations; lia]. }
split; [exact LSH|].
split. { eapply (window_bytesG LB0 data0 size); [exact INB | exact BY | exact L | exact P1 | exact P2 |].
intros a Ha (b & Hb & Hr). apply (EQ a Ha).
- right; right. exists b. split; [apply in_or_app; left; apply Hi; exact Hb | exact Hr].
- destruct b as [ba bn]. cbn [blk_addr blk_size fst snd] in Hr.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF (in_or_app _ _ _ (or_introl (Hi2 _ (Hi _ Hb))))) as DF. rewrite fr_size_3 in DF. lia. }
repeat split; assumption.
Qed.
Lemma sp1_16t : sp1 mod 16 = 0.
Proof using SPA1. clear - SPA1. Z.div_mod_to_equations. lia. Qed.

Definition put_any_costB (d : jroot) (DBS : list blk) : Z :=
match d with JRnull => 0 | JRtree _ => 512 * Z.of_nat (length DBS) | _ => JO_PUTX_COSTB_A end.
Definition put_any_costD (d : jroot) : Z := match d with JRdblx _ | JRstrx => JO_PUTX_COSTD_A | _ => 0 end.

#[using="CtxAll CA"] Lemma put_anyA : forall (ret : Z) (d : jroot) (q : Z) m md (A : ASA A4L HIx) B (DBS LBx : list blk)
(gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
0 <= ret < 2^64 -> ret mod 2 = 0 ->
HEAPAx A (DBS ++ LBx) LM [(Fr, 3)] B m md -> jroot_rep A4H A4F d m DBS q ->
stk asegs m lo sp1 ->
put_any_costB d DBS <= bB B -> put_any_costD d <= bD B ->
(forall m' md' (A' : ASA A4L HIx) B' F' fc' (xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
model_vm_only (cfg_model md) (cfg_model md') -> fsaved F F' -> (frm0 fc -> frm0 fc') -> stk asegs m' lo sp1 ->
heap_pres A4H (LBx ++ LM ++ fr_ivs A4L [(Fr, 3)]) sp1 m m' -> HEAPAx A' LBx LM [(Fr, 3)] B' m' md' ->
bB B - put_any_costB d DBS <= bB B' -> bD B - put_any_costD d <= bD B' ->
AJ5 A4L HIx A' T md' (sstateBc (Fr + 256) (Fr + 192) (Z_to_bv 64 ret) gp xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 F' ret fc' m')) ->
AJ5 A4L HIx A T md (sstateBc (Fr + 256) (Fr + 192) (Z_to_bv 64 ret) gp t0 t1 t2 (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F put_entry_A fc m).
Proof.
intros ret d q m md A B DBS LBx gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc Hret Hret2 HP RR ST CBp CDp KQ.
pose proof sp1_16t as SP16. pose proof alloc_ceiling_range as ACR. pose proof (hiA_top_le A4L HIx) as HT47.
pose proof (bv_unsigned_in_range 64 sp0) as SP0R. change (bv_modulus 64) with (2^64) in SP0R.
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP) as (errv & ERR). cbn [hl_tp hl_segs A4L A4H hla_base] in ERR.
assert (TREE : forall s : option jshape, put_pre A4H A4F s m DBS q 1 -> put_costA s 1 DBS <= put_any_costB d DBS -> put_any_costD d = 0 ->
AJ5 A4L HIx A T md (sstateBc (Fr + 256) (Fr + 192) (Z_to_bv 64 ret) gp t0 t1 t2 (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F put_entry_A fc m)).
{ intros s PRE CLE CD0. pose proof (ca_PUT _ _ _ _ _ _ _ CA) as PU. unfold put_stmt_A, put_stmtA in PU. unfold sstateB.
eapply PU with (A := A) (BS := DBS) (LB := LBx) (FRS := [(Fr, 3)]) (B := B) (s := s) (lo := lo) (rc := 1) (errv := errv);
[ exact HP | exact PRE | reflexivity | rewrite unsigned_lit by lia; exact ST | exact LO
| rewrite unsigned_lit by lia; unfold put_stk_A; lia | rewrite unsigned_lit by lia; exact SP16
| rewrite unsigned_lit by lia; lia | exact ERR | reflexivity | rewrite unsigned_lit by lia; exact Hret2 | lia |].
intros ms' md' A' (m' & r' & B' & RS & VM' & ST' & HPR' & ERR' & CHB & CHD & OUT).
destruct RS as (xt0 & xt1 & xt2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & F' & fc' & -> & FS' & FRM').
rewrite unsigned_lit in ST', HPR' by lia.
replace (ret_pc (Z_to_bv 64 ret)) with (Z_to_bv 64 ret : word) by (symmetry; apply ret_pc_even; [lia | exact Hret2]).
destruct OUT as [[_ HP'] | (s' & _ & Hrc & _)]; [| lia].
unfold sstateB in KQ. eapply KQ; [exact VM' | exact FS' | exact FRM' | exact ST' | exact HPR' | exact HP' | lia | lia]. }
destruct d as [|s|tojs|].
- destruct RR as [-> ->]. apply (TREE None); [split; reflexivity | cbn; lia | reflexivity].
- destruct RR as [Hq J]. apply (TREE (Some s)); [split; [exact Hq|]; split; [lia | exact J] | cbn [put_costA put_any_costB]; change (1 =? 1) with true; cbv iota; lia | reflexivity].
- pose proof (ca_PUTX _ _ _ _ _ _ _ CA) as PX. unfold jo_put_xleaf_A_stmt in PX. cbn [put_any_costB put_any_costD] in CBp, CDp, KQ. unfold sstateB.
eapply PX with (A := A) (BS := DBS) (LB := LBx) (FRS := [(Fr, 3)]) (B := B) (r := JRdblx tojs) (lo := lo) (errv := errv);
[ split; [exact HP|]; rewrite unsigned_lit by lia;
split; [exact ST|]; split; [exact LO|]; split; [unfold put_stk_A; lia|]; split; [exact SP16|]; split; [lia|];
split; [exact ERR|]; split; [reflexivity | rewrite unsigned_lit by lia; exact Hret2]
| exact RR | exact I | exact CBp | exact CDp | reflexivity |].
intros ms' md' m' rv A' B' (RS & VM' & ST' & HPR' & [errv' ERR']) [CHB CHD] _ ERRx HP'.
destruct RS as (xt0 & xt1 & xt2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & F' & fc' & -> & FS' & FRM').
rewrite unsigned_lit in ST', HPR' by lia.
replace (ret_pc (Z_to_bv 64 ret)) with (Z_to_bv 64 ret : word) by (symmetry; apply ret_pc_even; [lia | exact Hret2]).
unfold sstateB in KQ. eapply KQ; [exact VM' | exact FS' | exact FRM' | exact ST' | exact HPR' | exact HP' | lia | lia].
- pose proof (ca_PUTX _ _ _ _ _ _ _ CA) as PX. unfold jo_put_xleaf_A_stmt in PX. cbn [put_any_costB put_any_costD] in CBp, CDp, KQ. unfold sstateB.
eapply PX with (A := A) (BS := DBS) (LB := LBx) (FRS := [(Fr, 3)]) (B := B) (r := JRstrx) (lo := lo) (errv := errv);
[ split; [exact HP|]; rewrite unsigned_lit by lia;
split; [exact ST|]; split; [exact LO|]; split; [unfold put_stk_A; lia|]; split; [exact SP16|]; split; [lia|];
split; [exact ERR|]; split; [reflexivity | rewrite unsigned_lit by lia; exact Hret2]
| exact RR | exact I | exact CBp | exact CDp | reflexivity |].
intros ms' md' m' rv A' B' (RS & VM' & ST' & HPR' & [errv' ERR']) [CHB CHD] _ ERRx HP'.
destruct RS as (xt0 & xt1 & xt2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & F' & fc' & -> & FS' & FRM').
rewrite unsigned_lit in ST', HPR' by lia.
replace (ret_pc (Z_to_bv 64 ret)) with (Z_to_bv 64 ret : word) by (symmetry; apply ret_pc_even; [lia | exact Hret2]).
unfold sstateB in KQ. eapply KQ; [exact VM' | exact FS' | exact FRM' | exact ST' | exact HPR' | exact HP' | lia | lia].
Qed.
Notation SINVAc := (SINVA HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size p wtx).

Lemma RTC_SCF : forall A LB LM' FR B m md, HEAPAx A LB LM' FR B m md -> bytes_at asegs m 0xe8e70 (le8 (Z_to_bv 64 0xa0a78)).
Proof.
intros A LB LM' FR B m md HP. apply (rtc_cell HIx _ _ _ _ _ _ _ _ _ HP). unfold a4_rt_consts.
repeat (first [left; reflexivity | right]).
Qed.

Definition SHB3D : list byte := firstn 32 SHB3 ++ [Z_to_bv 8 0] ++ skipn 33 SHB3.

Definition KTA (sbf sdf : Z) : Prop :=
forall m' md' (A' : ASA A4L HIx) B' F' fc' LKf (x1 gp t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s2x s3x s4x s5x s6x s7x s8x s9x t3 t4 t5 t6 : word),
heap_presx A4H XT (LB0 ++ LM) (sp1 + 8) m0 m' -> model_vm_only (cfg_model md0) (cfg_model md') -> fsaved F0 F' -> frm0 fc' ->
rw_cells asegs m' T_LOCCELL_A [C8 (Z_to_bv 64 T_GLOBLOC_A)] -> rw_cells asegs m' T_LOCALE_LOCK_A [C4 (Z_to_bv 64 0)] -> GA_jo m' ->
stk asegs m' lo sp1 -> rw_cells asegs m' sp1 [C8 (Z_to_bv 64 Fr)] ->
HEAPAx A' (LKf ++ LB0) LM [] B' m' md' -> bB B0 - sbf <= bB B' -> bD B0 - sdf <= bD B' ->
AJ5 A4L HIx A' T md'
(MS (mkR x1 (Z_to_bv 64 sp1) gp (Z_to_bv 64 A_TP) t0 t1 t2 sp0 s1x a0 a1 a2 a3 a4 a5 a6 a7 s2x s3x s4x s5x s6x s7x s8x s9x s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0x92368) fc' None m' (seg_rom asegs)).
#[using="CtxAll HINVA_callc OWNc GAOc FSLc CA"] Lemma seg_tailA : forall m md (A : ASA A4L HIx) B F fc ptr rem data r BS LK sb sd (wdc KPC KPR : Z)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
SINVAc SHB3 m md A B F fc ptr rem data r BS LK sb sd ->
(exists (n : Z) (sj23 : list byte), 0 <= n <= 10 /\ rw_cells asegs m (Fr + 192) [C1 (Z_to_bv 8 (2 * n)); CB 23 sj23]) ->
root_wA r m BS p wdc -> 0 <= wdc < 2^28 ->
0 <= dcB wdc -> 0 <= dcD wdc -> 0 <= KPC -> 0 <= KPR ->
(forall d CBS mX q, copy_ofA r d CBS wdc -> jroot_rep A4H A4F d mX CBS q -> put_any_costB d CBS <= KPC) ->
(forall BSx mX, jroot_rep A4H A4F r mX BSx p -> put_any_costB r BSx <= KPR) ->
sb + dcB wdc + KPC + KPR <= TGT_BB_A_jo -> sd + dcD wdc + 4 <= TGT_BD_A_jo ->
KTA (sb + dcB wdc + KPC + KPR) (sd + dcD wdc + 4) ->
AJ5 A4L HIx A T md (sstateBc (Fr + 32) (Fr + 192) x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x92248 fc m).
Proof.
intros m md A B F fc ptr rem data r BS LK sb sd wdc KPC KPR x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 SI (n3 & sj23 & Hn3 & STR3) RWA WDC DCB0 DCD0 KPC0 KPR0 PCC PCR CBT CDT K.
pose proof SI as ((PX & VM & FS & FRM & LOC & LCK & G & ST & SL & FD & (fj0 & fj1 & FF0 & FF1) & FSH & LSH & BY & L & P0 & P1 & P2) & HP & RR & RD & BB & BD & RWm).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. change (hl_segs A4L) with asegs in MI.
pose proof alloc_ceiling_range as ACR. pose proof (hiA_top_le A4L HIx) as HT47.
pose proof (bv_unsigned_in_range 64 sp0) as SP0R. change (bv_modulus 64) with (2^64) in SP0R.
unfold T_LOCCELL_A, T_LOCALE_LOCK_A, A_TP in LOC, LCK.
let cs := eval cbv in (map C1 SHB3) in change (map C1 SHB3) with cs in FSH.
assert (BYm : bytes_at asegs m ptr data /\ True) by (split; [exact BY | exact I]). clear BY.
pose proof FRAPP as FRAPPu. unfold A_SB, A_HMB in FRAPPu.
pose proof (RTC_SCF _ _ _ _ _ _ _ HP) as SCF. apply QsKa.Mqa.ro_C8_of_bytes_at in SCF.
unfold sstateB, A_TP.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 64 <= 17594333495296) by (unfold sh; clear - FRLO FRHI ACR; Z.div_mod_to_equations; lia).
assert (WOK : Forall (own_iv sp1 lo Fr) [(lo, sp1 + 8); (Fr, Fr + 504); (sh, sh + 64)]).
{ unfold own_iv, sh. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
pose proof (munch_refl [(lo, sp1 + 8); (Fr, Fr + 504); (sh, sh + 64)] m) as MU. pose proof (wmono_refl asegs m) as WM.
reenterA asegs A4L HIx asegs_wx HP.
bstep. bstepz. bstepz. bstep. bstep. bstep. bstep. bstep.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m2 end.
lazymatch goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
assert (INCL : incl LB0 (BS ++ LK ++ LB0)) by (intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb).
destruct (OWNc A (BS ++ LK ++ LB0) B m m2 md _ HP INCL MU WM MI2 WOK) as (HP2 & HPX2 & AG2).
assert (RR2 : jroot_rep A4H A4F r m2 BS p).
{ eapply (QrIB.Mq0.jroot_rep_agree A4H A4F r m m2 BS ((BS ++ LK ++ LB0) ++ LM)); [exact RR | exact AG2 | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb]. }
assert (GA2 : GA_jo m2) by (exact (GAOc m m2 _ G MU WM WOK)).

assert (RWA2 : root_wA r m2 BS p wdc).
{ destruct r as [|shq|tjq|]; cbn [root_wA] in RWA |- *; try exact RWA.
destruct RWA as (Lx & (lenx & BY40 & LR & LA) & LW). exists Lx. split; [| exact LW]. exists lenx. split; [| split; [exact LR | exact LA]].
eapply (bytes_at_agree asegs _ m m2); [exact BY40 | exact AG2 |].
destruct RR as (Hp0 & pb & PBS & DBS & cap & len' & str' & EBS & _ & Hcap & _).
exists p, (48 + cap). split; [rewrite EBS; apply in_or_app; left; apply in_or_app; left; left; reflexivity|].
rewrite length_le8. cbn. lia. }
assert (UND2 : unpoisoned asegs m2 A_SB (Fr + 256) 8).
{ lazymatch type of FSH with rw_cells _ _ _ ?cs => let l := c1_bytes cs in
exact (FSLc m2 l 32%nat 33%nat FSH eq_refl ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)) end. }

pose proof FF1 as FFv.
lazymatch type of FFv with rw_cells _ _ _ [?c0; ?c1; ?c2] => change [c0; c1; c2] with ([c0] ++ ([c1] ++ [c2])) in FFv end.
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FFv as [_ FFv]. apply (proj1 (rw_cells_app asegs _ _ _ _)) in FFv as [DC2 _].
cbn [cells_size csize Nat.add] in DC2. replace (Fr + 48 + Z.of_nat 208) with (Fr + 256) in DC2 by lia.
assert (FJ2 : exists fj0' fj2, rw_cells asegs m2 Fr [CB 32 fj0'] /\ rw_cells asegs m2 (Fr + 48) [CB 456 fj2]).
{ exists fj0. pose proof FF1 as X3. lazymatch type of X3 with rw_cells _ _ _ ?cs => change (rw_cells asegs m2 (Fr + 48) ([] ++ cs ++ [])) in X3 end.
apply rw_cells_merge in X3. cbn [app] in X3.
lazymatch type of X3 with rw_cells _ _ _ [CB ?n ?b] => exists b; let v := eval vm_compute in n in change n with v in X3 end. split; [exact FF0 | exact X3]. }
assert (BY2 : bytes_at asegs m2 ptr data).
{ eapply (window_bytesG (BS ++ LK ++ LB0) data0 size); [destruct INB as [Z0|I1]; [left; exact Z0 | right; apply INCL; exact I1] | exact (proj1 BYm) | exact L | exact P1 | exact P2 |].
intros a Ha (b & Hb & Hr). apply (AG2 a Ha). exists b. split; [apply in_or_app; left; exact Hb | exact Hr]. }
lazymatch goal with H : stk asegs m2 lo sp1 |- _ => rename H into ST2 end.
assert (HI2 : HINVAc SHB3D m2 md F fc ptr rem data).
{ unfold HINVA. split; [eapply heap_presx_trans; [exact PX | exact HPX2]|]. split; [exact VM|]. split; [exact FS|]. split; [exact FRM|].
split; [exact LOC|]. split; [exact LCK|]. split; [exact GA2|]. split; [exact ST2|]. split; [exact SL|]. split; [exact FD|].
split; [exact FJ2|]. split; [exact FSH|]. split; [reflexivity|]. split; [exact BY2|]. repeat split; assumption. }
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP2) as (errv2 & ERR2). cbn [hl_tp hl_segs A4L A4H hla_base] in ERR2. unfold A_TP in ERR2.
assert (RD0 : 0 <= rdepth r) by (destruct r as [|s| |]; cbn [rdepth]; [lia | apply Q0Ek.sdepth_nonneg | lia | lia]).
evt_done5.
pose proof (ca_DEEP _ _ _ _ _ _ _ CA) as DC. unfold jo_deep_copy_A_stmt, JO_DEEP_COPY_A, JO_SHALLOW_COPY_A, JO_DEEP_STK0_A, JO_DEEP_STK1_A in DC.
eapply DC with (A := A) (BS := BS) (LB := LK ++ LB0) (FRS := [(Fr, 3)]) (B := B) (lo := lo) (p := p) (D := Fr + 256) (r := r) (errv := errv2) (w := wdc).
- split; [exact HP2|]. rewrite unsigned_lit by lia.
split; [exact ST2|]. split; [exact LO|]. split; [lia|]. split; [exact sp1_16t|]. split; [lia|].
split; [exact ERR2|]. split; [reflexivity | vm_compute; reflexivity].
- rewrite unsigned_lit by lia. exact SPA1.
- exact (proj1 GA2).
- exact RR2.
- exact DC2.
- exists Fr, 3. split; [left; reflexivity|]. rewrite fr_size_3. lia.
- exact UND2.
- clear - FRAL. Z.div_mod_to_equations. lia.
- cbn [length]. lia.
- exact RWA2.
- lia.
- unfold TGT_BB_A_jo in *. lia.
- unfold TGT_BD_A_jo in *. lia.
- exact FRM.
- reflexivity.
- reflexivity.
- reflexivity.
- idtac.
intros ms3 md3 m3 rv3 A3 B3 (RS3 & VM3 & ST3 & HPD3 & [errv3 ERR3]) [CHB3 CHD3] LHG3 RR3 OUT3.
destruct RS3 as (xt0 & xt1 & xt2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & F3 & fc3 & -> & FS3 & FRM3).
rewrite unsigned_lit in ST3, HPD3 by lia.
replace (ret_pc (Z_to_bv 64 0x92268)) with (Z_to_bv 64 0x92268 : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

assert (STR4 : rw_cells asegs m3 (Fr + 192) [C1 (Z_to_bv 8 (2 * n3)); CB 23 sj23]).
{ eapply rw_cells_pointwiseA; [exact STR3|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply (HPD3 a); [lia | | lia].
right; right. exists (Fr, 504). split; [apply in_or_app; right; apply in_or_app; right; left; reflexivity | cbn; lia]. }

assert (OUT : exists (d : jroot) (q : Z) (CBS REM : list blk),
(copy_ofA r d CBS wdc \/ d = JRnull) /\ rw_cells asegs m3 (Fr + 256) [C8 (Z_to_bv 64 q)] /\ jroot_rep A4H A4F d m3 CBS q /\
HEAPAx A3 (CBS ++ BS ++ REM ++ LK ++ LB0) LM [(Fr, 3)] B3 m3 md3).
{ destruct OUT3 as [(_ & d & q & CBS & REM & CO & Hq & DC3 & RRd & HP3) | (_ & REM & DC3 & HP3)].
- exists d, q, CBS, REM. split; [left; exact CO|]. split; [exact DC3|]. split; [exact RRd|].
eapply (heapA_perm A4L HIx); [exact HP3 | | apply Permutation.Permutation_refl | apply Permutation.Permutation_refl].
rewrite !app_assoc. apply Permutation.Permutation_app_tail. apply Permutation.Permutation_app_tail. apply Permutation.Permutation_app_tail. apply Permutation.Permutation_app_comm.
- exists JRnull, 0, (@nil blk), REM. split; [right; reflexivity|]. split; [exact DC3|]. split; [split; reflexivity|]. cbn [app]. exact HP3. }
destruct OUT as (d & q & CBS & REM & COd & DC3 & RRd & HP3).
assert (HI3 : HINVAc SHB3D m3 md3 F3 fc3 ptr rem data).
{ eapply (HINVA_callD SHB3D m2 m3 md md3 A B F F3 fc fc3 ptr rem data (BS ++ LK ++ LB0) (LK ++ LB0) (Z_to_bv 64 q));
[ exact HI2 | exact HP2 | intros b Hb; apply in_or_app; right; exact Hb | intros b Hb; apply in_or_app; right; exact Hb
| exact HPD3 | exact VM3 | exact FS3 | exact (FRM3 FRM) | exact ST3 | exact LHG3 | exact DC3 ]. }
clear HI2 HP2 RR2 GA2 UND2 DC2 FJ2 BY2 STR3 MU WM MI2 FF1 FF0 FSH LOC LCK SL FD ST2 ERR2 SCF HPX2 AG2.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI3. change (hl_segs A4L) with asegs in MI3.
pose proof (munch_refl (@nil (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
change (hl_segs A4H) with asegs in *.
reenterA asegs A4L HIx asegs_wx HP3. change (hl_segs A4H) with asegs.
bstep. bstep.

evt_done5.
eapply (put_anyA 0x92270 d q m3 md3 A3 B3 CBS (BS ++ REM ++ LK ++ LB0)); [lia | reflexivity | exact HP3 | exact RRd | exact ST3 | | |].
{ destruct COd as [CO | ->]; [pose proof (PCC d CBS m3 q CO RRd) | cbn [put_any_costB]]; unfold TGT_BB_A_jo in *; lia. }
{ destruct d; cbn [put_any_costD]; unfold JO_PUTX_COSTD_A, TGT_BD_A_jo in *; lia. }
intros m4 md4 Ay4 B4 F4 fc4 yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 VM4 FS4 FRM4 ST4 HPR4 HP4 CHB4 CHD4.
assert (HI4 : HINVAc SHB3D m4 md4 F4 fc4 ptr rem data).
{ eapply HINVA_callc; [exact HI3 | exact HPR4 | intros b Hb; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb
| exact VM4 | exact FS4 | apply FRM4; exact (proj1 (proj2 (proj2 (proj2 HI3)))) | exact ST4]. }
assert (RR4 : jroot_rep A4H A4F r m4 BS p).
{ eapply (QrIB.Mq0.jroot_rep_agree A4H A4F r m3 m4 BS BS); [exact RR3 | | intros b Hb; exact Hb].
eapply (agree_of_heap_pres asegs A4H); [exact HPR4 | reflexivity | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb]. }
assert (STR5 : rw_cells asegs m4 (Fr + 192) [C1 (Z_to_bv 8 (2 * n3)); CB 23 sj23]).
{ eapply rw_cells_pointwiseA; [exact STR4|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply (HPR4 a); [lia|].
right; right. exists (Fr, 504). split; [apply in_or_app; right; apply in_or_app; right; left; reflexivity | cbn; lia]. }
assert (PCD : put_any_costD d <= 2) by (destruct d; cbn [put_any_costD]; unfold JO_PUTX_COSTD_A; lia).
assert (PCB : put_any_costB d CBS <= KPC) by (destruct COd as [CO | ->]; [exact (PCC d CBS m3 q CO RRd) | cbn [put_any_costB]; lia]).
clear HI3 RR3 STR4 RRd HP3 DC3 MI3 MU WM OUT3 HPD3 ERR3 LHG3 ST3.
unfold sstateB, A_TP.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI4. change (hl_segs A4L) with asegs in MI4.
pose proof (munch_refl (@nil (Z * Z)) m4) as MU. pose proof (wmono_refl asegs m4) as WM.
change (hl_segs A4H) with asegs in *.
reenterA asegs A4L HIx asegs_wx HP4. change (hl_segs A4H) with asegs.
bstep. bstep.

evt_done5.
eapply (put_anyA 0x92278 r p m4 md4 Ay4 B4 BS (REM ++ LK ++ LB0)); [lia | reflexivity | exact HP4 | exact RR4 | exact ST4 | | |].
{ pose proof (PCR BS m4 RR4). unfold TGT_BB_A_jo in *. lia. }
{ assert (put_any_costD r <= 2) by (destruct r; cbn [put_any_costD]; unfold JO_PUTX_COSTD_A; lia). unfold TGT_BD_A_jo in *. lia. }
intros m5 md5 Ay5 B5 F5 fc5 zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 VM5 FS5 FRM5 ST5 HPR5 HP5 CHB5 CHD5.
assert (HI5 : HINVAc SHB3D m5 md5 F5 fc5 ptr rem data).
{ eapply HINVA_callc; [exact HI4 | exact HPR5 | intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb
| exact VM5 | exact FS5 | apply FRM5; exact (proj1 (proj2 (proj2 (proj2 HI4)))) | exact ST5]. }
assert (STR6 : rw_cells asegs m5 (Fr + 192) [C1 (Z_to_bv 8 (2 * n3)); CB 23 sj23]).
{ eapply rw_cells_pointwiseA; [exact STR5|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply (HPR5 a); [lia|].
right; right. exists (Fr, 504). split; [apply in_or_app; right; apply in_or_app; right; left; reflexivity | cbn; lia]. }
assert (PCRB : put_any_costB r BS <= KPR) by (exact (PCR BS m4 RR4)).
assert (PCRD : put_any_costD r <= 2) by (destruct r; cbn [put_any_costD]; unfold JO_PUTX_COSTD_A; lia).

pose proof HI5 as (PX5 & VM5' & FS5' & FRM5' & LOC5 & LCK5 & G5 & _ & SL5 & FD5 & (fj05 & fj15 & FF05 & FF15) & FSH5 & _ & _).
unfold T_LOCCELL_A, T_LOCALE_LOCK_A, A_TP in LOC5, LCK5.
let cs := eval cbv in (map C1 SHB3D) in change (map C1 SHB3D) with cs in FSH5. fold sh in FSH5.
destruct (rw_cells_CB_cut asegs _ _ _ _ 8 FF05 ltac:(lia)) as [FM5 _]. clear FF05 FF15.
clear HI5 HI4 RR4 STR5 MU WM MI4 HP4.
unfold sstateB, A_TP.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI5. change (hl_segs A4L) with asegs in MI5.
pose proof (munch_refl [(lo, sp1 + 8); (Fr, Fr + 504); (sh, sh + 64)] m5) as MU. pose proof (wmono_refl asegs m5) as WM.
change (hl_segs A4H) with asegs in *.
reenterA asegs A4L HIx asegs_wx HP5. change (hl_segs A4H) with asegs.
fold sh.
bstep. bstepz.
bstep. bstep. rewrite short_flag0A by lia. bstep. if_true.
do 5 bstepz.
bstep. bstep. bstepz.
bstep. if_falsex.
bstep. bstep. bstep.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m6 end.
lazymatch goal with H : mem_inv asegs m6 |- _ => rename H into MI6 end.
assert (INCL5 : incl LB0 (REM ++ LK ++ LB0)) by (intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb).
destruct (OWNc Ay5 (REM ++ LK ++ LB0) B5 m5 m6 md5 _ HP5 INCL5 MU WM MI6 WOK) as (HP6 & HPX6 & AG6).
lazymatch type of FSH5 with rw_cells _ _ _ ?cs => let l := c1_bytes cs in
apply (rw_cells_recast asegs m6 sh _ [CB 64 l]) in FSH5; [| cbn; repeat split; try reflexivity; try exact I | reflexivity | reflexivity] end.
eapply evt_mono; [eapply (QKdU.set_shadow_f5_A HIx) with (dst := sh) (n := 64); [exact HP6 | reflexivity | reflexivity | lia | lia | lia | exact FSH5] |].
cbv beta. intros ms7 (wt0 & wt1 & wt2 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & wt3 & wt4 & wt5 & wt6 & m7 & -> & MU7 & WM7 & MI7 & FSH7).
replace (ret_pc (Z_to_bv 64 0x922cc)) with (Z_to_bv 64 0x922cc : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
assert (MU' : munch [(lo, sp1 + 8); (Fr, Fr + 504); (sh, sh + 64)] m5 m7).
{ eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU7]. intros x Hx. cbn [outside] in Hx |- *. lia. }
assert (WM' : wmono asegs m5 m7) by (eapply wmono_trans; [exact WM | exact WM7]).
clear MU WM. rename MU' into MU. rename WM' into WM.
destruct (OWNc Ay5 (REM ++ LK ++ LB0) B5 m5 m7 md5 _ HP5 INCL5 MU WM MI7 WOK) as (HP7 & HPX7 & AG7).
assert (GA7 : GA_jo m7) by (exact (GAOc m5 m7 _ G5 MU WM WOK)).
apply (rw_cells_transport asegs [(sh, sh + 64)] m6 m7) in LOC5; [| exact MU7 | exact WM7 | cbn [disjoint_from cells_size csize Nat.add]; lia].
apply (rw_cells_transport asegs [(sh, sh + 64)] m6 m7) in LCK5; [| exact MU7 | exact WM7 | cbn [disjoint_from cells_size csize Nat.add]; lia].
apply (rw_cells_transport asegs [(sh, sh + 64)] m6 m7) in SL5; [| exact MU7 | exact WM7 | cbn [disjoint_from cells_size csize Nat.add]; lia].
apply (rw_cells_transport asegs [(sh, sh + 64)] m6 m7) in FD5; [| exact MU7 | exact WM7 | cbn [disjoint_from cells_size csize Nat.add]; lia].
lazymatch goal with H : stk asegs m6 lo sp1 |- _ => rename H into ST6 end.
apply (stk_transport_disjoint asegs [(sh, sh + 64)] m6 m7) in ST6; [| exact MU7 | exact WM7 | cbn [disjoint_from]; lia].
clear HP6 HPX6 AG6 FSH5 FM5 STR6 MI6.

assert (INF : In (Fr, 3) [(Fr, 3)]) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP7 INF) as (_ & _ & _ & _ & _ & _ & _ & (fp & FPB & FPR & FPnc & FPimg & FPns & FPfr)).
rewrite fr_size_3 in FPB. replace (Fr + 512 - 8) with (Fr + 504) in FPB by lia.
pose proof (ro_C8_of_bytes_at asegs _ _ _ FPB) as FPC.
lazymatch goal with |- AJe ?L ?J ?A ?T ?c ?ms => refine (aj5_back L J _ A T c ms _ _); [gp5_solve|] end.
change (hl_segs A4H) with asegs in *.
reenterA asegs A4L HIx asegs_wx HP7. change (hl_segs A4H) with asegs.
bstep.
evt_done5.
eapply (hiA_frame_release A4L HIx) with (Fr := Fr) (k := 3) (fp := fp) (rX := Z_to_bv 5 10);
[exact HP7 | exact INF | rewrite fr_size_3; replace (Fr + 512 - 8) with (Fr + 504) by lia; exact FPB | lia | reflexivity | vm_compute; discriminate | | ].
1: vm_compute; split; reflexivity.
intros m8 md8 A8 VM8 HP8 Hoff Hwv.
cbn [fr_remove fr_base fst Z.eqb] in HP8. rewrite Z.eqb_refl in HP8.
assert (MUr : munch [(fp, fp + 1)] m7 m8).
{ intros x Hx. cbn [outside] in Hx. pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. cbn in XR.
rewrite <- (Z_to_bv_bv_unsigned x). change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)). apply Hoff; lia. }
assert (WMr : wmono asegs m7 m8) by exact Hwv.
assert (MI8 : mem_inv asegs m8).
{ intros y b Hb. destruct (Z.eq_dec (bv_unsigned y) fp) as [Ey | Ny].
- destruct (ro_addr asegs y) eqn:RO; [| reflexivity]. exfalso. apply ro_addr_asegs in RO. cbn [hl_img_lo hl_img_hi A4H hla_base A4L] in FPimg. lia.
- apply (MI7 y b). rewrite <- Hb. symmetry. rewrite <- (Z_to_bv_bv_unsigned y). change (Z_to_bv 64 (bv_unsigned y)) with (wa (bv_unsigned y)). apply Hoff; [| exact Ny].
pose proof (bv_unsigned_in_range 64 y) as YR. unfold bv_modulus in YR. cbn in YR. lia. }
assert (FPlow : fp < alloc_ceiling) by (destruct (Z.lt_ge_cases fp alloc_ceiling) as [Lt|Ge]; [exact Lt | exfalso; apply FPnc; left; exact Ge]).
assert (FPNC0 : forall a, client_addr A4H (LB0 ++ LM) (sp1 + 8) a -> a <> fp).
{ intros a Hc ->. apply FPnc. destruct Hc as [Hc | [Hc | (b & Hb & Hr)]]; [exfalso; lia | right; left; exact Hc | right; right].
exists b. split; [| exact Hr]. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply INCL5; exact Hb | right; exact Hb]. }
assert (HPX8 : heap_presx A4H XT (LB0 ++ LM) (sp1 + 8) m7 m8).
{ eapply (heap_presx_of_munch A4H XT (LB0 ++ LM) (sp1 + 8) [(fp, fp + 1)]); [exact MUr | exact WMr |].
intros a Ha Hc. cbn [outside]. pose proof (FPNC0 a Hc). split; [lia | exact I]. }
assert (FPst : ~ hl_client_static A4H fp) by (intros Hs; apply FPnc; right; left; exact Hs).
cbn [hl_client_static A4H] in FPst. unfold a4_client_static in FPst.
cbn [hl_img_lo hl_img_hi A4H hla_base A4L] in FPimg.
apply (rw_cells_transport asegs [(fp, fp + 1)] m7 m8) in LOC5; [| exact MUr | exact WMr | cbn [disjoint_from cells_size csize Nat.add]; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] m7 m8) in LCK5; [| exact MUr | exact WMr | cbn [disjoint_from cells_size csize Nat.add]; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] m7 m8) in SL5; [| exact MUr | exact WMr | cbn [disjoint_from cells_size csize Nat.add]; lia].
apply (stk_transport_disjoint asegs [(fp, fp + 1)] m7 m8) in ST6; [| exact MUr | exact WMr | cbn [disjoint_from]; lia].
assert (GA8 : GA_jo m8).
{ eapply GA_jo_munch; [exact GA7 | exact MUr | exact WMr |]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. lia. }
change (598736 + 4) with 598740.
clear FPC FD5 FSH7.
change (hl_segs A4L) with asegs.
reenterA asegs A4L HIx asegs_wx HP8. change (hl_segs A4H) with asegs.
bstep.
evt_done5.
unfold KTA in K. eapply (K m8 md8 A8 B5 F5 fc5 (REM ++ LK)).
+ eapply heap_presx_trans; [exact PX5 | eapply heap_presx_trans; [exact HPX7 | exact HPX8]].
+ eapply model_vm_only_trans; [exact VM5' | exact VM8].
+ exact FS5'.
+ exact FRM5'.
+ exact LOC5.
+ exact LCK5.
+ exact GA8.
+ exact ST6.
+ exact SL5.
+ rewrite <- app_assoc. exact HP8.
+ unfold TGT_BB_A_jo in *. lia.
+ unfold TGT_BD_A_jo in *. lia.
Qed.
End Ctx.
End AHarnJo4.
End RC__1.
