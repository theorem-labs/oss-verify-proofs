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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJZd.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q63E.Mq9.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpNt.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrIB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

Ltac c1_bytes cs := lazymatch cs with | nil => constr:(@nil byte) | C1 ?b :: ?r => let r' := c1_bytes r in constr:(b :: r') end.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition SHB2 : list byte := firstn 16 SHB0 ++ map (Z_to_bv 8) [0; 0; 0] ++ skipn 19 SHB0.
Definition SHB3 : list byte := firstn 24 SHB0 ++ map (Z_to_bv 8) [0; 0; 0] ++ skipn 27 SHB0.

Lemma presB_rw_cells_gen : forall (S P : Z) (L : list blk) (SP : Z) (m m' : word -> option byte) A0 cs,
(forall a, 0 <= a < 2^64 -> client_addr A4H L SP a -> ~ (S <= a < S + 24) -> ~ (P <= a < P + 16) ->
m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None)) ->
rw_cells asegs m A0 cs -> client_range A4H L SP A0 (Z.of_nat (cells_size cs)) ->
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

Section AHarnJoS.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
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
Let HINVA_callc := HINVA_call HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP.
Let OWNc := own_writesA HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP.
Let GAOc := GA_jo_own HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP.

Definition sstateB (s4v s6v : Z) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (pc : Z) (fc : bv 32) (m : word -> option byte) :=
MS (mkR x1 (Z_to_bv 64 sp1) gp (Z_to_bv 64 A_TP) t0 t1 t2 sp0 (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (Fr / 8 + 2147450880)) (Z_to_bv 64 Fr) (Z_to_bv 64 s4v) (Z_to_bv 64 p) (Z_to_bv 64 s6v) (Z_to_bv 64 (Fr + 64))
(Z_to_bv 64 Fr) (Z_to_bv 64 2147450880) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom asegs).

Definition rootWm (r : jroot) (BS : list blk) : Prop :=
match r with JRtree s => exists PT, jtx s BS = Some (wtx, PT) | _ => True end.

Definition SINVA (shb : list byte) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (F : bvmap 5 word) (fc : bv 32)
(ptr rem : Z) (data : list byte) (r : jroot) (BS LK : list blk) (sb sd : Z) : Prop :=
HINVAc shb m md F fc ptr rem data /\ HEAPAx A (BS ++ LK ++ LB0) LM [(Fr, 3)] B m md /\ jroot_rep A4H A4F r m BS p /\ rdepth r <= 32 /\
bB B0 - sb <= bB B /\ bD B0 - sd <= bD B /\ rootWm r BS.

Definition KSB (s4v s6v k : Z) (shb : list byte) (r : jroot) (sb sd : Z) : Prop :=
forall m' md' (A' : ASA A4L HIx) B' F' fc' ptr' rem' data' BS' LK' (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
SINVA shb m' md' A' B' F' fc' ptr' rem' data' r BS' LK' sb sd ->
AJ5 A4L HIx A' T md' (sstateB s4v s6v x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' k fc' m').

Definition KSFA (k : Z) (r : jroot) (sb sd : Z) : Prop :=
forall m' md' (A' : ASA A4L HIx) B' F' fc' ptr' rem' data' BS' LK' (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
SINVA SHB3 m' md' A' B' F' fc' ptr' rem' data' r BS' LK' sb sd ->
(exists (n : Z) (sj23 : list byte), 0 <= n <= 10 /\ rw_cells asegs m' (Fr + 192) [C1 (Z_to_bv 8 (2 * n)); CB 23 sj23]) ->
(is_string_root r = true -> exists n : Z, 0 <= n <= 10 /\ str_lenA m' p n) ->
AJ5 A4L HIx A' T md' (sstateB (Fr + 32) (Fr + 192) x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' k fc' m').
Definition setters_root (r : jroot) : jroot := set_string_root (set_string_root (set_double_root (fn_dbl_to_json_string A4F) r)).

Definition W0 : list (Z * Z) := [(lo, sp1 + 8); (Fr, Fr + 504); (Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 64)].

#[using="CtxAll"] Lemma sp1_16' : sp1 mod 16 = 0.
Proof. clear - SPA1. Z.div_mod_to_equations. lia. Qed.

#[using="CtxAll HINVA_callc"] Lemma SINVA_ret : forall shb m m' md md' A A' B B' F F' fc fc' ptr rem data r r' BS BS' LK LK' sb sd sb' sd',
SINVA shb m md A B F fc ptr rem data r BS LK sb sd ->
heap_pres A4H ((LK ++ LB0) ++ LM ++ fr_ivs A4L [(Fr, 3)]) sp1 m m' -> model_vm_only (cfg_model md) (cfg_model md') -> fsaved F F' -> frm0 fc' ->
stk asegs m' lo sp1 ->
HEAPAx A' (BS' ++ LK' ++ LB0) LM [(Fr, 3)] B' m' md' -> jroot_rep A4H A4F r' m' BS' p -> rdepth r' <= 32 ->
bB B0 - sb' <= bB B' -> bD B0 - sd' <= bD B' -> rootWm r' BS' ->
SINVA shb m' md' A' B' F' fc' ptr rem data r' BS' LK' sb' sd'.
Proof.
intros until sd'. intros (INV & HP & RR & RD & BB & BD & RW) HPR VM FS FRM ST HP' RR' RD' BB' BD' RW'.
split; [| split; [exact HP' | split; [exact RR' | split; [exact RD' | split; [exact BB' | split; [exact BD' | exact RW']]]]]].
eapply HINVA_callc; [exact INV | exact HPR | intros b Hb; apply in_or_app; right; exact Hb | exact VM | exact FS | exact FRM | exact ST].
Qed.

#[using="CtxAll HINVA_callc"] Lemma set_callA : forall (f ret s4v s6v : Z) m md (A : ASA A4L HIx) B F fc ptr rem data r BS LK sb sd
(gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
jo_set_scalar_A_stmt HIx f ->
0 <= ret < 2^64 -> ret mod 2 = 0 -> 0 <= s4v < 2^64 -> 0 <= s6v < 2^64 ->
SINVA SHB0 m md A B F fc ptr rem data r BS LK sb sd ->
KSB s4v s6v ret SHB0 r sb sd ->
AJ5 A4L HIx A T md (sstateB s4v s6v (Z_to_bv 64 ret) gp t0 t1 t2 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F f fc m).
Proof.
intros f ret s4v s6v m md A B F fc ptr rem data r BS LK sb sd gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ST_ Hret Hret2 H4 H6 SI K.
pose proof SI as ((PX & VM & FS & FRM & LOC & LCK & G & ST & _) & HP & RR & RD & BB & BD & RW).
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP) as (errv & ERR). cbn [hl_tp hl_segs A4L A4H hla_base] in ERR.
pose proof sp1_16' as SP16. pose proof alloc_ceiling_range as ACR. pose proof (hiA_top_le A4L HIx) as HT47.
pose proof (bv_unsigned_in_range 64 sp0) as SP0R. change (bv_modulus 64) with (2^64) in SP0R.
unfold sstateB.
eapply ST_ with (A := A) (BS := BS) (LB := LK ++ LB0) (r := r) (lo := lo) (errv := errv);
[ split; [exact HP|]; rewrite unsigned_lit by lia;
split; [exact ST|]; split; [exact LO|]; split; [lia|]; split; [exact SP16|]; split; [lia|];
split; [exact ERR|]; split; [reflexivity | rewrite unsigned_lit by lia; exact Hret2]
| exact RR | reflexivity |].
intros ms' md' m' rv (RS & VM' & ST' & HPR' & [errv' ERR']) ERRx RR' HP'.
destruct RS as (xt0 & xt1 & xt2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & F' & fc' & -> & FS' & FRM').
rewrite unsigned_lit in ST', HPR' by lia.
replace (ret_pc (Z_to_bv 64 ret)) with (Z_to_bv 64 ret : word) by (symmetry; apply ret_pc_even; [lia | exact Hret2]).
unfold KSB, sstateB in K. eapply K. eapply SINVA_ret; [exact SI | exact HPR' | exact VM' | exact FS' | exact (FRM' FRM) | exact ST' | exact HP' | exact RR' | exact RD | exact BB | exact BD | exact RW].
Qed.

#[using="CtxAll OWNc GAOc"] Lemma SINVA_own : forall shb shb' m mX md A B F F' fc fc' ptr rem data ptr' rem' data' r BS LK sb sd W,
SINVA shb m md A B F fc ptr rem data r BS LK sb sd ->
munch W m mX -> wmono asegs m mX -> mem_inv asegs mX -> Forall (own_iv sp1 lo Fr) W ->
fsaved F F' -> frm0 fc' ->
rw_cells asegs mX T_LOCCELL_A [C8 (Z_to_bv 64 T_GLOBLOC_A)] -> rw_cells asegs mX T_LOCALE_LOCK_A [C4 (Z_to_bv 64 0)] ->
stk asegs mX lo sp1 ->
rw_cells asegs mX sp1 [C8 (Z_to_bv 64 Fr)] ->
rw_cells asegs mX (Fr + 32) [C8 (Z_to_bv 64 ptr'); C8 (Z_to_bv 64 rem')] ->
(exists fj0 fj1, rw_cells asegs mX Fr [CB 32 fj0] /\ rw_cells asegs mX (Fr + 48) [CB 456 fj1]) ->
rw_cells asegs mX (Fr / 8 + 2147450880) (map C1 shb') -> length shb' = 64%nat ->
bytes_at asegs m ptr' data' -> Z.of_nat (length data') = rem' -> 0 < ptr' -> data0 <= ptr' -> ptr' + rem' <= data0 + size ->
SINVA shb' mX md A B F' fc' ptr' rem' data' r BS LK sb sd.
Proof.
intros until W. intros ((PX & VM & FS & FRM & LOC & LCK & G & ST & SL & FD & FF & FSH & LSH & BY & L & P0 & P1 & P2) & HP & RR & RD & BB & BD & RW)
MU WM MI HW FS' FRM' LOC' LCK' ST' SL' FD' FF' FSH' LSH' BY' L' P0' P1' P2'.
assert (INCL : incl LB0 (BS ++ LK ++ LB0)) by (intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb).
destruct (OWNc A (BS ++ LK ++ LB0) B m mX md W HP INCL MU WM MI HW) as (HP' & HPX & AG).
split; [| split; [exact HP' | split; [| split; [exact RD | split; [exact BB | split; [exact BD | exact RW]]]]]].
- unfold HINVA. split; [eapply heap_presx_trans; [exact PX | exact HPX]|]. split; [exact VM|]. split; [eapply fsaved_trans; [exact FS | exact FS']|]. split; [exact FRM'|].
split; [exact LOC'|]. split; [exact LCK'|]. split; [exact (GAOc m mX W G MU WM HW)|]. split; [exact ST'|]. split; [exact SL'|]. split; [exact FD'|].
split; [exact FF'|]. split; [exact FSH'|]. split; [exact LSH'|].
split; [eapply (window_bytesG (BS ++ LK ++ LB0) data0 size); [destruct INB as [Z0|I1]; [left; exact Z0 | right; apply INCL; exact I1] | exact BY' | exact L' | exact P1' | exact P2' |];
intros a Ha (b & Hb & Hr); apply (AG a Ha); exists b; split; [apply in_or_app; left; exact Hb | exact Hr]|]. split; [exact L'|]. split; [exact P0'|]. split; [exact P1' | exact P2'].
- eapply (QrIB.Mq0.jroot_rep_agree A4H A4F r m mX BS ((BS ++ LK ++ LB0) ++ LM)); [exact RR | exact AG | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb].
Qed.
End Ctx.
End AHarnJoS.
End RC__1.
