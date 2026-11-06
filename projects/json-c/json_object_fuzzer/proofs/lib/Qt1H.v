(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply Lib.SepCache QWxq_c1 Qfw3_c1 Qc3B QRjH QHnV QCcH QfLs Q0Ek QjDH QmZZ Qsw7 QJjn QYIF QgoP Q7UD QXUB Qhd4 Qwm6 QlKV QsKa Q9O6 Qekr QJZd Qw5U Q1Ey Q2y2 QOmG Ql4f Q63E QgoM QpNt QrIB Q6q3.
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
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq5 QsKa.Mq4 QlKV.Mq5 Q9O6.Mq0 Qekr.Mq0 QlKV.Mqa QsKa.Mq0 QJZd.Mq0 QlKV.Mq2 QsKa.Mq8 Qw5U.Mq0.

Import QsKa.Mq6.

Import Q2y2.
Import QOmG Qw5U.Mq1 Ql4f.Mq0 Q63E.Mq0.

Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac QlEo_c1.solve_load ::= QrJ1.Mq0.mkr__solve_load_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.

Ltac c1_bytes cs := lazymatch cs with | nil => constr:(@nil byte) | C1 ?b :: ?r => let r' := c1_bytes r in constr:(b :: r') end.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section AHarnJo2.
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
Variables (p : Z) (s11 : word) (T : TSet).
Hypothesis BB0 : TGT_BB_A_jo <= bB B0.
Hypothesis BD0 : TGT_BD_A_jo <= bD B0.
Variable wtx : Z.
Collection CtxAll := RC__ HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP p s11 T BB0 BD0.

Notation HINVAc := (HINVA sp0 sp1 lo Fr LB0 LM m0 md0 F0 data0 size).
Notation hstateAc := (hstateA sp0 sp1 Fr p s11).
Let HINVA_callc := HINVA_call HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP.
Let EVDc := fdp_evidenceA HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP.
Let FSLc := fslot_evidenceA HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP.
Let OWNc := own_writesA HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP.
Let GAOc := GA_jo_own HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP.

Definition rootWm (r : jroot) (BS : list blk) : Prop :=
match r with JRtree s => exists PT, jtx s BS = Some (wtx, PT) | _ => True end.

Definition SINVA (shb : list byte) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (F : bvmap 5 word) (fc : bv 32)
(ptr rem : Z) (data : list byte) (r : jroot) (BS LK : list blk) (sb sd : Z) : Prop :=
HINVAc shb m md F fc ptr rem data /\ HEAPAx A (BS ++ LK ++ LB0) LM [(Fr, 2)] B m md /\ jroot_rep A4H A4F r m BS p /\ rdepth r <= 32 /\
bB B0 - sb <= bB B /\ bD B0 - sd <= bD B /\ rootWm r BS.

Definition KSA (s10v : word) (k : Z) (r : jroot) (sb sd : Z) : Prop :=
forall m' md' (A' : ASA A4L HIx) B' F' fc' ptr' rem' data' BS' LK' (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
SINVA SHB0 m' md' A' B' F' fc' ptr' rem' data' r BS' LK' sb sd ->
AJ5 A4L HIx A' T md' (hstateAc s10v x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' k fc' m').

Definition KSAx (k : Z) (r : jroot) (sb sd : Z) : Prop := forall s10v, KSA s10v k r sb sd.
#[using="CtxAll"] Lemma sp1_16' : sp1 mod 16 = 0.
Proof. clear - SPA1. Z.div_mod_to_equations. lia. Qed.

#[using="CtxAll HINVA_callc"] Lemma SINVA_ret : forall shb m m' md md' A A' B B' F F' fc fc' ptr rem data r r' BS BS' LK LK' sb sd sb' sd',
SINVA shb m md A B F fc ptr rem data r BS LK sb sd ->
heap_pres A4H ((LK ++ LB0) ++ LM ++ fr_ivs A4L [(Fr, 2)]) sp1 m m' -> model_vm_only (cfg_model md) (cfg_model md') -> fsaved F F' -> frm0 fc' ->
stk asegs m' lo sp1 ->
HEAPAx A' (BS' ++ LK' ++ LB0) LM [(Fr, 2)] B' m' md' -> jroot_rep A4H A4F r' m' BS' p -> rdepth r' <= 32 ->
bB B0 - sb' <= bB B' -> bD B0 - sd' <= bD B' -> rootWm r' BS' ->
SINVA shb m' md' A' B' F' fc' ptr rem data r' BS' LK' sb' sd'.
Proof.
intros until sd'. intros (INV & HP & RR & RD & BB & BD & RW) HPR VM FS FRM ST HP' RR' RD' BB' BD' RW'.
split; [| split; [exact HP' | split; [exact RR' | split; [exact RD' | split; [exact BB' | split; [exact BD' | exact RW']]]]]].
eapply HINVA_callc; [exact INV | exact HPR | intros b Hb; apply in_or_app; right; exact Hb | exact VM | exact FS | exact FRM | exact ST].
Qed.

#[using="CtxAll HINVA_callc"] Lemma set_callA : forall (f ret : Z) (s10v : word) m md (A : ASA A4L HIx) B F fc ptr rem data r BS LK sb sd
(gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
jo_set_scalar_A_stmt HIx f ->
0 <= ret < 2^64 -> ret mod 2 = 0 ->
SINVA SHB0 m md A B F fc ptr rem data r BS LK sb sd ->
KSA s10v ret r sb sd ->
AJ5 A4L HIx A T md (hstateAc s10v (Z_to_bv 64 ret) gp t0 t1 t2 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F f fc m).
Proof.
intros f ret s10v m md A B F fc ptr rem data r BS LK sb sd gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ST_ Hret Hret2 SI K.
pose proof SI as ((PX & VM & FS & FRM & LOC & LCK & G & ST & _) & HP & RR & RD & BB & BD & RW).
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP) as (errv & ERR). cbn [hl_tp hl_segs A4L A4H hla_base] in ERR.
pose proof sp1_16' as SP16. pose proof alloc_ceiling_range as ACR. pose proof (hiA_top_le A4L HIx) as HT47.
pose proof (bv_unsigned_in_range 64 sp0) as SP0R. change (bv_modulus 64) with (2^64) in SP0R.
unfold hstateA.
eapply ST_ with (A := A) (BS := BS) (LB := LK ++ LB0) (r := r) (lo := lo) (errv := errv);
[ split; [exact HP|]; rewrite unsigned_lit by lia;
split; [exact ST|]; split; [exact LO|]; split; [lia|]; split; [exact SP16|]; split; [lia|];
split; [exact ERR|]; split; [reflexivity | rewrite unsigned_lit by lia; exact Hret2]
| exact RR | reflexivity |].
intros ms' md' m' rv (RS & VM' & ST' & HPR' & [errv' ERR']) ERRx RR' HP'.
destruct RS as (xt0 & xt1 & xt2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & F' & fc' & -> & FS' & FRM').
rewrite unsigned_lit in ST', HPR' by lia.
replace (ret_pc (Z_to_bv 64 ret)) with (Z_to_bv 64 ret : word) by (symmetry; apply ret_pc_even; [lia | exact Hret2]).
unfold KSA, hstateA in K. eapply K. eapply SINVA_ret; [exact SI | exact HPR' | exact VM' | exact FS' | exact (FRM' FRM) | exact ST' | exact HP' | exact RR' | exact RD | exact BB | exact BD | exact RW].
Qed.

#[using="CtxAll OWNc GAOc"] Lemma SINVA_own : forall shb shb' m mX md A B F F' fc fc' ptr rem data ptr' rem' data' r BS LK sb sd W,
SINVA shb m md A B F fc ptr rem data r BS LK sb sd ->
munch W m mX -> wmono asegs m mX -> mem_inv asegs mX -> Forall (own_iv sp1 lo Fr) W ->
fsaved F F' -> frm0 fc' ->
rw_cells asegs mX T_LOCCELL_A [C8 (Z_to_bv 64 T_GLOBLOC_A)] -> rw_cells asegs mX T_LOCALE_LOCK_A [C4 (Z_to_bv 64 0)] ->
stk asegs mX lo sp1 ->
(exists j8, rw_cells asegs mX sp1 [CB 8 j8; C8 (Z_to_bv 64 Fr)]) ->
rw_cells asegs mX (sp1 + 16) [C8 (Z_to_bv 64 ptr'); C8 (Z_to_bv 64 rem')] ->
(exists fj, rw_cells asegs mX Fr [CB 248 fj]) ->
rw_cells asegs mX (Fr / 8 + 2147450880) (map C1 shb') -> length shb' = 32%nat ->
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
Lemma bytes_at_firstn : forall segs m a (bs : list byte) (c : Z),
bytes_at segs m a bs -> 0 <= c <= Z.of_nat (length bs) -> bytes_at segs m a (firstn (Z.to_nat c) bs).
Proof.
intros segs m a bs c B Hc. pose proof (bytes_at_sub segs m a bs 0 (Z.to_nat c) B ltac:(lia)) as X.
change (Z.of_nat 0) with 0 in X. rewrite Z.add_0_r in X. exact X.
Qed.

Ltac seg_open SI m :=
pose proof SI as ((PX & VM & FS & FRM & LOC & LCK & G & ST & [j8 SL] & FD & [fj FF] & FSH & LSH & BY & L & P0 & P1 & P2) & HP & RR & RD & BB & BD & RW);
pose proof (heapA_mem_inv _ HIx _ _ _ _ _ _ _ HP) as MI; change (hl_segs _) with asegs in MI;
pose proof alloc_ceiling_range as ACR; pose proof (hiA_top_le _ HIx) as HT47;
pose proof (bv_unsigned_in_range 64 sp0) as SP0R; change (bv_modulus 64) with (2^64) in SP0R;
unfold T_LOCCELL_A, T_LOCALE_LOCK_A, A_TP in LOC, LCK; try unfold SHB0 in FSH; cbn [map] in FSH;
(lazymatch type of BY with bytes_at _ _ ?pp ?dd => assert (BYm : bytes_at asegs m pp dd /\ True) by (split; [exact BY | exact I]) end);
pose proof FRAPP as FRAPPu; unfold A_SB, A_HMB in FRAPPu;
unfold hstateA, A_TP;
set (sh := Fr / 8 + 2147450880) in *;
assert (SHR : 2147450880 <= sh /\ sh + 32 <= 17594333495296) by (unfold sh; clear - FRLO FRHI ACR; Z.div_mod_to_equations; lia).

#[using="CtxAll HINVA_callc EVDc OWNc GAOc CA"] Lemma seg_setintA : forall m md (A : ASA A4L HIx) B F fc ptr rem data r BS LK sb sd
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
SINVA SHB0 m md A B F fc ptr rem data r BS LK sb sd ->
KSAx 0x91d4c r sb sd ->
AJ5 A4L HIx A T md (hstateAc (Z_to_bv 64 (-8)) x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x91ce0 fc m).
Proof.
intros m md A B F fc ptr rem data r BS LK sb sd x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 SI K.
seg_open SI m.
assert (INCL : incl LB0 (BS ++ LK ++ LB0)) by (intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb).
destruct (EVDc A (BS ++ LK ++ LB0) B m md ptr rem HP INCL P1 P2) as (_ & _ & UND).
pose proof (bytes_at_bound _ _ _ _ BY) as DB.
assert (WAPP : Forall (fun iv : Z * Z => snd iv <= A_SB \/ A_HMB <= fst iv) [(sp1 + 24, sp1 + 32)]).
{ unfold A_SB, A_HMB. apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]. }
pose proof (munch_refl [(sp1 + 24, sp1 + 32)] m) as MU. pose proof (wmono_refl asegs m) as WM.
(let L := constr:(A4L) in reenterA asegs L HIx asegs_wx HP).
assert (EXITK : forall (mc : word -> option byte) (s10x ya0 acc ya2 ya3 ya4 ya5 ya6 : word) (c : Z),
rw_cells asegs mc (sp1 + 16) [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 c)] -> c = Z.max (rem - 4) 0 ->
munch [(sp1 + 24, sp1 + 32)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
evt asegs (AJ5e A4L HIx A T md)
(MS (mkR x1 (Z_to_bv 64 sp1) gp (Z_to_bv 64 6434400) t0 t1 t2 sp0 (Z_to_bv 64 sp1) ya0 acc ya2 ya3 ya4 ya5 ya6 a7
(Z_to_bv 64 Fr) (Z_to_bv 64 (Fr + 160)) (Z_to_bv 64 p) (Z_to_bv 64 (Fr + 224)) (Z_to_bv 64 (Fr + 96)) (Z_to_bv 64 sh)
(Z_to_bv 64 Fr) (Z_to_bv 64 2147450880) s10x s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x91d3c) fc None mc (seg_rom asegs))).
{ intros mc s10x ya0 acc ya2 ya3 ya4 ya5 ya6 c FDc Hc MUc WMc MIc.
clear FD MU WM. transport_after_call asegs m mc MUc WMc.
step. step. step. step.
evt_done5.
eapply (set_callA 0x9c88c 0x91d4c s10x); [exact (ca_SETI _ _ _ _ _ _ _ CA) | lia | reflexivity | | exact (K s10x)].
eapply (SINVA_own SHB0 SHB0 m mc) with (ptr' := ptr) (rem' := c) (data' := firstn (Z.to_nat c) data);
[ exact SI | exact MUc | exact WMc | exact MIc | apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil] | apply fsaved_refl | exact FRM
| exact LOC | exact LCK | exact ST | exists j8; exact SL | exact FDc | exists fj; exact FF | exact FSH | reflexivity
| apply bytes_at_firstn; [exact (proj1 BYm) | lia] | rewrite firstn_length_le by lia; lia | exact P0 | exact P1 | lia ]. }
assert (LOOPI : forall (fuel : nat) (i : Z) (mc : word -> option byte) (acc ya0 ya5 ya6 : word),
4 - i <= Z.of_nat fuel -> 0 <= i <= 3 -> i <= rem ->
rw_cells asegs mc (sp1 + 16) [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (rem - i))] ->
munch [(sp1 + 24, sp1 + 32)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
evt asegs (AJ5e A4L HIx A T md)
(MS (mkR x1 (Z_to_bv 64 sp1) gp (Z_to_bv 64 6434400) t0 t1 t2 sp0 (Z_to_bv 64 sp1) ya0 acc (Z_to_bv 64 (-1)) (Z_to_bv 64 (rem - i + -1)) (Z_to_bv 64 24) ya5 ya6 a7
(Z_to_bv 64 Fr) (Z_to_bv 64 (Fr + 160)) (Z_to_bv 64 p) (Z_to_bv 64 (Fr + 224)) (Z_to_bv 64 (Fr + 96)) (Z_to_bv 64 sh)
(Z_to_bv 64 Fr) (Z_to_bv 64 2147450880) (Z_to_bv 64 (8 * i + -8)) s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x91cf4) fc None mc (seg_rom asegs))).
{ induction fuel as [|fuel IH]; intros i mc acc ya0 ya5 ya6 Hfuel Hi Hir FDc MUc WMc MIc; [exfalso; lia|].
clear FD MU WM MI SL FF FSH LOC LCK ST.
step.
destruct (Z.eq_dec (rem - i) 0) as [E0 | N0].
{ replace (rem - i + -1) with (-1) by lia. if_true.
eapply EXITK with (c := rem - i); [exact FDc | lia | exact MUc | exact WMc | exact MIc]. }
lazymatch goal with |- context [bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (neq_wzA x y) by lia end. cbv beta iota.
step. step. step.
lazymatch goal with MUd : munch _ m ?md' |- evt _ _ (MS _ _ _ _ _ ?md' _) =>
assert (UNDd : unpoisoned asegs md' A_SB ptr rem) by (eapply unpoisoned_keep; [exact (UND ltac:(lia)) | exact MUd | lia | lia | exact WAPP]);
assert (BYd : bytes_at asegs md' ptr data) by (eapply bytes_at_transport; [exact BY | exact MUd | cbn [disjoint_from]; rewrite L; lia]);
destruct (unpoisoned_byte_ro md' ptr rem (ptr + (rem - i + -1)) UNDd ltac:(lia)) as (v1 & SHK & Hv1) end.
destruct (nth_error data (Z.to_nat (rem - i - 1))) as [b1|] eqn:Hb1; [| exfalso; apply nth_error_None in Hb1; lia].
pose proof (bv_unsigned_in_range 8 b1) as BR1. unfold bv_modulus in BR1. cbn in BR1.
step. step. sh_norm. step. step.
lazymatch goal with |- evt _ ?Q (MS _ _ _ _ _ ?mm _) =>
assert (B20 : forall (zx zy : word),
evt asegs Q (MS (mkR x1 (Z_to_bv 64 sp1) gp (Z_to_bv 64 6434400) t0 t1 t2 sp0 (Z_to_bv 64 sp1) (Z_to_bv 64 (ptr + (rem - i + -1))) acc (Z_to_bv 64 (-1)) (Z_to_bv 64 (rem - i + -1)) (Z_to_bv 64 24) zx zy a7
(Z_to_bv 64 Fr) (Z_to_bv 64 (Fr + 160)) (Z_to_bv 64 p) (Z_to_bv 64 (Fr + 224)) (Z_to_bv 64 (Fr + 96)) (Z_to_bv 64 sh)
(Z_to_bv 64 Fr) (Z_to_bv 64 2147450880) (Z_to_bv 64 (8 * i + -8)) s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x91d14) fc None mm (seg_rom asegs))) end.
2:{ destruct Hv1 as [-> | [Hv8 Hvm]].
- rewrite sxb_zero. if_false. apply B20.
- rewrite (QsKa.Mq1.sxb_small v1) by lia. if_truex. step. step.
rewrite (unsigned_lit (ptr + (rem - i + -1))) by lia. rewrite QsKa.Mq1.land7_mod8 by lia. if_truex. apply B20. }
intros zx zy. clear SHK v1 Hv1 UNDd.
pose proof (u8ro_read asegs _ ptr data (rem - i - 1) b1 _ BYd Hb1 ltac:(lia) eq_refl) as RD1.
replace (ptr + (rem - i - 1)) with (ptr + (rem - i + -1)) in RD1 by lia.
step. clear RD1.
step. step. step. step.
step.
lazymatch goal with H : rw_cells asegs ?mx (sp1 + 16) _ |- _ => rename H into FD3 end.
destruct (Z.eq_dec i 3) as [I3 | IN3].
- subst i. if_falsex. step.
eapply EXITK with (c := rem - 3 + -1); [exact FD3 | lia | eassumption | eassumption | eassumption].
- if_truex.
replace (rem - i + -2) with (rem - (i + 1) + -1) by lia.
replace (8 * i) with (8 * (i + 1) + -8) by lia.
replace (rem - i + -1) with (rem - (i + 1)) in FD3 by lia.
eapply (IH (i + 1)); [lia | lia | lia | exact FD3 | eassumption | eassumption | eassumption]. }
step. step. step. step. step.
replace (rem + -1) with (rem - 0 + -1) by lia.
replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 (8 * 0 + -8)) by reflexivity.
replace (Z_to_bv 64 rem) with (Z_to_bv 64 (rem - 0)) in FD by (rewrite Z.sub_0_r; reflexivity).
eapply (LOOPI 4%nat 0); [lia | lia | lia | exact FD | exact MU | exact WM | exact MI].
Qed.

#[using="CtxAll HINVA_callc EVDc OWNc GAOc CA"] Lemma seg_setint64A : forall m md (A : ASA A4L HIx) B F fc ptr rem data r BS LK sb sd (s10i : word)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
SINVA SHB0 m md A B F fc ptr rem data r BS LK sb sd ->
KSA (Z_to_bv 64 (-1)) 0x91dc0 r sb sd ->
AJ5 A4L HIx A T md (hstateAc s10i x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x91d4c fc m).
Proof.
intros m md A B F fc ptr rem data r BS LK sb sd s10i x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 SI K.
seg_open SI m.
assert (INCL : incl LB0 (BS ++ LK ++ LB0)) by (intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb).
destruct (EVDc A (BS ++ LK ++ LB0) B m md ptr rem HP INCL P1 P2) as (_ & _ & UND).
pose proof (bytes_at_bound _ _ _ _ BY) as DB.
assert (WAPP : Forall (fun iv : Z * Z => snd iv <= A_SB \/ A_HMB <= fst iv) [(sp1 + 24, sp1 + 32)]).
{ unfold A_SB, A_HMB. apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]. }
pose proof (munch_refl [(sp1 + 24, sp1 + 32)] m) as MU. pose proof (wmono_refl asegs m) as WM.
(let L := constr:(A4L) in reenterA asegs L HIx asegs_wx HP).
assert (EXITK : forall (mc : word -> option byte) (ya0 acc ya2 ya3 ya4 ya5 ya6 ya7 : word) (c : Z),
rw_cells asegs mc (sp1 + 16) [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 c)] -> c = Z.max (rem - 8) 0 ->
munch [(sp1 + 24, sp1 + 32)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
evt asegs (AJ5e A4L HIx A T md)
(MS (mkR x1 (Z_to_bv 64 sp1) gp (Z_to_bv 64 6434400) t0 t1 t2 sp0 (Z_to_bv 64 sp1) ya0 acc ya2 ya3 ya4 ya5 ya6 ya7
(Z_to_bv 64 Fr) (Z_to_bv 64 (Fr + 160)) (Z_to_bv 64 p) (Z_to_bv 64 (Fr + 224)) (Z_to_bv 64 (Fr + 96)) (Z_to_bv 64 sh)
(Z_to_bv 64 Fr) (Z_to_bv 64 2147450880) s10i s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x91dac) fc None mc (seg_rom asegs))).
{ intros mc ya0 acc ya2 ya3 ya4 ya5 ya6 ya7 c FDc Hc MUc WMc MIc.
clear FD MU WM. transport_after_call asegs m mc MUc WMc.
step. step. step. step. step.
evt_done5.
eapply (set_callA 0x9c930 0x91dc0 (Z_to_bv 64 (-1))); [exact (ca_SETI64 _ _ _ _ _ _ _ CA) | lia | reflexivity | | exact K].
eapply (SINVA_own SHB0 SHB0 m mc) with (ptr' := ptr) (rem' := c) (data' := firstn (Z.to_nat c) data);
[ exact SI | exact MUc | exact WMc | exact MIc | apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil] | apply fsaved_refl | exact FRM
| exact LOC | exact LCK | exact ST | exists j8; exact SL | exact FDc | exists fj; exact FF | exact FSH | reflexivity
| apply bytes_at_firstn; [exact (proj1 BYm) | lia] | rewrite firstn_length_le by lia; lia | exact P0 | exact P1 | lia ]. }
assert (LOOPI : forall (fuel : nat) (i : Z) (mc : word -> option byte) (acc ya0 ya6 ya7 : word),
8 - i <= Z.of_nat fuel -> 0 <= i <= 7 -> i <= rem ->
rw_cells asegs mc (sp1 + 16) [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (rem - i))] ->
munch [(sp1 + 24, sp1 + 32)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
evt asegs (AJ5e A4L HIx A T md)
(MS (mkR x1 (Z_to_bv 64 sp1) gp (Z_to_bv 64 6434400) t0 t1 t2 sp0 (Z_to_bv 64 sp1) ya0 acc (Z_to_bv 64 (8 * i + -8)) (Z_to_bv 64 (-1)) (Z_to_bv 64 (rem - i + -1)) (Z_to_bv 64 56) ya6 ya7
(Z_to_bv 64 Fr) (Z_to_bv 64 (Fr + 160)) (Z_to_bv 64 p) (Z_to_bv 64 (Fr + 224)) (Z_to_bv 64 (Fr + 96)) (Z_to_bv 64 sh)
(Z_to_bv 64 Fr) (Z_to_bv 64 2147450880) s10i s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x91d64) fc None mc (seg_rom asegs))).
{ induction fuel as [|fuel IH]; intros i mc acc ya0 ya6 ya7 Hfuel Hi Hir FDc MUc WMc MIc; [exfalso; lia|].
clear FD MU WM MI SL FF FSH LOC LCK ST.
step.
destruct (Z.eq_dec (rem - i) 0) as [E0 | N0].
{ replace (rem - i + -1) with (-1) by lia. if_true.
eapply EXITK with (c := rem - i); [exact FDc | lia | exact MUc | exact WMc | exact MIc]. }
lazymatch goal with |- context [bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (neq_wzA x y) by lia end. cbv beta iota.
step. step. step.
lazymatch goal with MUd : munch _ m ?md' |- evt _ _ (MS _ _ _ _ _ ?md' _) =>
assert (UNDd : unpoisoned asegs md' A_SB ptr rem) by (eapply unpoisoned_keep; [exact (UND ltac:(lia)) | exact MUd | lia | lia | exact WAPP]);
assert (BYd : bytes_at asegs md' ptr data) by (eapply bytes_at_transport; [exact BY | exact MUd | cbn [disjoint_from]; rewrite L; lia]);
destruct (unpoisoned_byte_ro md' ptr rem (ptr + (rem - i + -1)) UNDd ltac:(lia)) as (v1 & SHK & Hv1) end.
destruct (nth_error data (Z.to_nat (rem - i - 1))) as [b1|] eqn:Hb1; [| exfalso; apply nth_error_None in Hb1; lia].
pose proof (bv_unsigned_in_range 8 b1) as BR1. unfold bv_modulus in BR1. cbn in BR1.
step. step. sh_norm. step. step.
lazymatch goal with |- evt _ ?Q (MS _ _ _ _ _ ?mm _) =>
assert (B20 : forall (zx zy : word),
evt asegs Q (MS (mkR x1 (Z_to_bv 64 sp1) gp (Z_to_bv 64 6434400) t0 t1 t2 sp0 (Z_to_bv 64 sp1) (Z_to_bv 64 (ptr + (rem - i + -1))) acc (Z_to_bv 64 (8 * i + -8)) (Z_to_bv 64 (-1)) (Z_to_bv 64 (rem - i + -1)) (Z_to_bv 64 56) zx zy
(Z_to_bv 64 Fr) (Z_to_bv 64 (Fr + 160)) (Z_to_bv 64 p) (Z_to_bv 64 (Fr + 224)) (Z_to_bv 64 (Fr + 96)) (Z_to_bv 64 sh)
(Z_to_bv 64 Fr) (Z_to_bv 64 2147450880) s10i s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x91d84) fc None mm (seg_rom asegs))) end.
2:{ destruct Hv1 as [-> | [Hv8 Hvm]].
- rewrite sxb_zero. if_false. apply B20.
- rewrite (QsKa.Mq1.sxb_small v1) by lia. if_truex. step. step.
rewrite (unsigned_lit (ptr + (rem - i + -1))) by lia. rewrite QsKa.Mq1.land7_mod8 by lia. if_truex. apply B20. }
intros zx zy. clear SHK v1 Hv1 UNDd.
pose proof (u8ro_read asegs _ ptr data (rem - i - 1) b1 _ BYd Hb1 ltac:(lia) eq_refl) as RD1.
replace (ptr + (rem - i - 1)) with (ptr + (rem - i + -1)) in RD1 by lia.
step. clear RD1.
step. step. step. step.
step.
lazymatch goal with H : rw_cells asegs ?mx (sp1 + 16) _ |- _ => rename H into FD3 end.
destruct (Z.eq_dec i 7) as [I3 | IN3].
- subst i. if_falsex. step.
eapply EXITK with (c := rem - 7 + -1); [exact FD3 | lia | eassumption | eassumption | eassumption].
- if_truex.
replace (rem - i + -2) with (rem - (i + 1) + -1) by lia.
replace (8 * i) with (8 * (i + 1) + -8) by lia.
replace (rem - i + -1) with (rem - (i + 1)) in FD3 by lia.
eapply (IH (i + 1)); [lia | lia | lia | exact FD3 | eassumption | eassumption | eassumption]. }
step. step. step. step. step. step.
replace (rem + -1) with (rem - 0 + -1) by lia.
replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 (8 * 0 + -8)) by reflexivity.
replace (Z_to_bv 64 rem) with (Z_to_bv 64 (rem - 0)) in FD by (rewrite Z.sub_0_r; reflexivity).
eapply (LOOPI 8%nat 0); [lia | lia | lia | exact FD | exact MU | exact WM | exact MI].
Qed.

#[using="CtxAll HINVA_callc EVDc OWNc GAOc CA"] Lemma seg_setuint64A : forall m md (A : ASA A4L HIx) B F fc ptr rem data r BS LK sb sd
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
SINVA SHB0 m md A B F fc ptr rem data r BS LK sb sd ->
KSA (Z_to_bv 64 (-1)) 0x91e24 r sb sd ->
AJ5 A4L HIx A T md (hstateAc (Z_to_bv 64 (-1)) x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x91dc0 fc m).
Proof.
intros m md A B F fc ptr rem data r BS LK sb sd x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 SI K.
seg_open SI m.
assert (INCL : incl LB0 (BS ++ LK ++ LB0)) by (intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb).
destruct (EVDc A (BS ++ LK ++ LB0) B m md ptr rem HP INCL P1 P2) as (_ & _ & UND).
pose proof (bytes_at_bound _ _ _ _ BY) as DB.
assert (WAPP : Forall (fun iv : Z * Z => snd iv <= A_SB \/ A_HMB <= fst iv) [(sp1 + 24, sp1 + 32)]).
{ unfold A_SB, A_HMB. apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]. }
pose proof (munch_refl [(sp1 + 24, sp1 + 32)] m) as MU. pose proof (wmono_refl asegs m) as WM.
(let L := constr:(A4L) in reenterA asegs L HIx asegs_wx HP).
assert (EXITK : forall (mc : word -> option byte) (ya0 acc ya2 ya3 ya4 ya5 ya6 : word) (c : Z),
rw_cells asegs mc (sp1 + 16) [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 c)] -> c = Z.max (rem - 8) 0 ->
munch [(sp1 + 24, sp1 + 32)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
evt asegs (AJ5e A4L HIx A T md)
(MS (mkR x1 (Z_to_bv 64 sp1) gp (Z_to_bv 64 6434400) t0 t1 t2 sp0 (Z_to_bv 64 sp1) ya0 acc ya2 ya3 ya4 ya5 ya6 a7
(Z_to_bv 64 Fr) (Z_to_bv 64 (Fr + 160)) (Z_to_bv 64 p) (Z_to_bv 64 (Fr + 224)) (Z_to_bv 64 (Fr + 96)) (Z_to_bv 64 sh)
(Z_to_bv 64 Fr) (Z_to_bv 64 2147450880) (Z_to_bv 64 (-1)) s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x91e1c) fc None mc (seg_rom asegs))).
{ intros mc ya0 acc ya2 ya3 ya4 ya5 ya6 c FDc Hc MUc WMc MIc.
clear FD MU WM. transport_after_call asegs m mc MUc WMc.
step. step.
evt_done5.
eapply (set_callA 0x9d314 0x91e24 (Z_to_bv 64 (-1))); [exact (ca_SETU64 _ _ _ _ _ _ _ CA) | lia | reflexivity | | exact K].
eapply (SINVA_own SHB0 SHB0 m mc) with (ptr' := ptr) (rem' := c) (data' := firstn (Z.to_nat c) data);
[ exact SI | exact MUc | exact WMc | exact MIc | apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil] | apply fsaved_refl | exact FRM
| exact LOC | exact LCK | exact ST | exists j8; exact SL | exact FDc | exists fj; exact FF | exact FSH | reflexivity
| apply bytes_at_firstn; [exact (proj1 BYm) | lia] | rewrite firstn_length_le by lia; lia | exact P0 | exact P1 | lia ]. }
assert (LOOPI : forall (fuel : nat) (i : Z) (mc : word -> option byte) (acc ya0 ya5 ya6 : word),
8 - i <= Z.of_nat fuel -> 0 <= i <= 7 -> i <= rem ->
rw_cells asegs mc (sp1 + 16) [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (rem - i))] ->
munch [(sp1 + 24, sp1 + 32)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
evt asegs (AJ5e A4L HIx A T md)
(MS (mkR x1 (Z_to_bv 64 sp1) gp (Z_to_bv 64 6434400) t0 t1 t2 sp0 (Z_to_bv 64 sp1) ya0 acc (Z_to_bv 64 (8 * i + -8)) (Z_to_bv 64 (rem - i + -1)) (Z_to_bv 64 56) ya5 ya6 a7
(Z_to_bv 64 Fr) (Z_to_bv 64 (Fr + 160)) (Z_to_bv 64 p) (Z_to_bv 64 (Fr + 224)) (Z_to_bv 64 (Fr + 96)) (Z_to_bv 64 sh)
(Z_to_bv 64 Fr) (Z_to_bv 64 2147450880) (Z_to_bv 64 (-1)) s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x91dd4) fc None mc (seg_rom asegs))).
{ induction fuel as [|fuel IH]; intros i mc acc ya0 ya5 ya6 Hfuel Hi Hir FDc MUc WMc MIc; [exfalso; lia|].
clear FD MU WM MI SL FF FSH LOC LCK ST.
step.
destruct (Z.eq_dec (rem - i) 0) as [E0 | N0].
{ replace (rem - i + -1) with (-1) by lia. if_true.
eapply EXITK with (c := rem - i); [exact FDc | lia | exact MUc | exact WMc | exact MIc]. }
lazymatch goal with |- context [bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (neq_wzA x y) by lia end. cbv beta iota.
step. step. step.
lazymatch goal with MUd : munch _ m ?md' |- evt _ _ (MS _ _ _ _ _ ?md' _) =>
assert (UNDd : unpoisoned asegs md' A_SB ptr rem) by (eapply unpoisoned_keep; [exact (UND ltac:(lia)) | exact MUd | lia | lia | exact WAPP]);
assert (BYd : bytes_at asegs md' ptr data) by (eapply bytes_at_transport; [exact BY | exact MUd | cbn [disjoint_from]; rewrite L; lia]);
destruct (unpoisoned_byte_ro md' ptr rem (ptr + (rem - i + -1)) UNDd ltac:(lia)) as (v1 & SHK & Hv1) end.
destruct (nth_error data (Z.to_nat (rem - i - 1))) as [b1|] eqn:Hb1; [| exfalso; apply nth_error_None in Hb1; lia].
pose proof (bv_unsigned_in_range 8 b1) as BR1. unfold bv_modulus in BR1. cbn in BR1.
step. step. sh_norm. step. step.
lazymatch goal with |- evt _ ?Q (MS _ _ _ _ _ ?mm _) =>
assert (B20 : forall (zx zy : word),
evt asegs Q (MS (mkR x1 (Z_to_bv 64 sp1) gp (Z_to_bv 64 6434400) t0 t1 t2 sp0 (Z_to_bv 64 sp1) (Z_to_bv 64 (ptr + (rem - i + -1))) acc (Z_to_bv 64 (8 * i + -8)) (Z_to_bv 64 (rem - i + -1)) (Z_to_bv 64 56) zx zy a7
(Z_to_bv 64 Fr) (Z_to_bv 64 (Fr + 160)) (Z_to_bv 64 p) (Z_to_bv 64 (Fr + 224)) (Z_to_bv 64 (Fr + 96)) (Z_to_bv 64 sh)
(Z_to_bv 64 Fr) (Z_to_bv 64 2147450880) (Z_to_bv 64 (-1)) s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x91df4) fc None mm (seg_rom asegs))) end.
2:{ destruct Hv1 as [-> | [Hv8 Hvm]].
- rewrite sxb_zero. if_false. apply B20.
- rewrite (QsKa.Mq1.sxb_small v1) by lia. if_truex. step. step.
rewrite (unsigned_lit (ptr + (rem - i + -1))) by lia. rewrite QsKa.Mq1.land7_mod8 by lia. if_truex. apply B20. }
intros zx zy. clear SHK v1 Hv1 UNDd.
pose proof (u8ro_read asegs _ ptr data (rem - i - 1) b1 _ BYd Hb1 ltac:(lia) eq_refl) as RD1.
replace (ptr + (rem - i - 1)) with (ptr + (rem - i + -1)) in RD1 by lia.
step. clear RD1.
step. step. step. step.
step.
lazymatch goal with H : rw_cells asegs ?mx (sp1 + 16) _ |- _ => rename H into FD3 end.
destruct (Z.eq_dec i 7) as [I3 | IN3].
- subst i. if_falsex. step.
eapply EXITK with (c := rem - 7 + -1); [exact FD3 | lia | eassumption | eassumption | eassumption].
- if_truex.
replace (rem - i + -2) with (rem - (i + 1) + -1) by lia.
replace (8 * i) with (8 * (i + 1) + -8) by lia.
replace (rem - i + -1) with (rem - (i + 1)) in FD3 by lia.
eapply (IH (i + 1)); [lia | lia | lia | exact FD3 | eassumption | eassumption | eassumption]. }
step. step. step. step. step.
replace (rem + -1) with (rem - 0 + -1) by lia.
replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 (8 * 0 + -8)) by reflexivity.
replace (Z_to_bv 64 rem) with (Z_to_bv 64 (rem - 0)) in FD by (rewrite Z.sub_0_r; reflexivity).
eapply (LOOPI 8%nat 0); [lia | lia | lia | exact FD | exact MU | exact WM | exact MI].
Qed.
#[using="Type"] Lemma rdepth_set_double_rootA : forall d r, rdepth (set_double_root d r) <= rdepth r.
Proof. clear. intros d r. destruct r as [|s| |]; cbn; try lia. pose proof (Q0Ek.sdepth_nonneg s). destruct s; cbn in *; lia. Qed.
#[using="Type"] Lemma rdepth_set_string_rootA : forall r, rdepth (set_string_root r) <= rdepth r.
Proof. clear. intros r. destruct r as [|s| |]; cbn; try lia. pose proof (Q0Ek.sdepth_nonneg s). destruct s; cbn in *; lia. Qed.

Definition hjA_fp1 := Eval vm_compute in match image_bytes asegs 0x10338 8 with Some bs => bs | None => [] end.
Definition hjA_fp2 := Eval vm_compute in match image_bytes asegs 0x10328 8 with Some bs => bs | None => [] end.
Lemma hjA_ro : forall m, mem_inv asegs m -> ro_cells asegs m 0x10338 [CB 8 hjA_fp1] /\ ro_cells asegs m 0x10328 [CB 8 hjA_fp2].
Proof.
intros m MI. split.
- change 8%nat with (length hjA_fp1). apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ]. change (Z.of_nat (length hjA_fp1)) with 8%Z. lia.
- change 8%nat with (length hjA_fp2). apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ]. change (Z.of_nat (length hjA_fp2)) with 8%Z. lia.
Qed.

#[using="CtxAll HINVA_callc EVDc OWNc GAOc CA"] Lemma seg_setdoubleA : forall m md (A : ASA A4L HIx) B F fc ptr rem data r BS LK sb sd
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
SINVA SHB0 m md A B F fc ptr rem data r BS LK sb sd ->
sb + JO_SETDBL_COSTB_A <= TGT_BB_A_jo -> sd + JO_SETDBL_COSTD_A <= TGT_BD_A_jo ->
KSA (Z_to_bv 64 (-1)) 0x91e44 (set_double_root (fn_dbl_to_json_string A4F) r) (sb + JO_SETDBL_COSTB_A) (sd + JO_SETDBL_COSTD_A) ->
AJ5 A4L HIx A T md (hstateAc (Z_to_bv 64 (-1)) x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x91e24 fc m).
Proof.
intros m md A B F fc ptr rem data r BS LK sb sd x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 SI CB CD K.
seg_open SI m.
assert (INCL : incl LB0 (BS ++ LK ++ LB0)) by (intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb).
destruct (EVDc A (BS ++ LK ++ LB0) B m md ptr rem HP INCL P1 P2) as (RTm & UNPm & UND).
destruct (hjA_ro m MI) as [RO1 RO2].
pose proof (munch_refl (@nil (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
(let L := constr:(A4L) in reenterA asegs L HIx asegs_wx HP).
step. step. step. step. step. step. clear MU WM.
clear RO1 RO2.
eapply evt_cut.
{ eapply QpNt.Mq0.cfp_A with (P := sp1 + 16) (ptr := ptr) (rem := rem) (lo := lo) (data := data);
[ reflexivity | exact RTm | exact FD | exact UNPm | clear - SPA1; Z.div_mod_to_equations; lia | exact BY | exact L | exact P0 | exact UND
| rewrite unsigned_lit by lia; exact ST | exact LO | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | lia | lia | exact MI
| rewrite freg_get_same by reflexivity; vm_compute; reflexivity
| rewrite freg_get_other by (vm_compute; reflexivity); rewrite freg_get_same by reflexivity; vm_compute; reflexivity
| exact FRM ]. }
intros ms' (yt0 & yt1 & yt2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & yt3 & yt4 & yt5 & yt6 & F1 & fc1 & m1 & -> & FS1 & FRM1 & MU1 & WM1 & MI1 & FD1 & B1 & ST1).
unfold fdp_WSA in MU1. rewrite unsigned_lit in ST1, MU1 by lia.
replace (ret_pc (Z_to_bv 64 0x91e3c)) with (Z_to_bv 64 0x91e3c : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
replace (sp1 + 16 + 8) with (sp1 + 24) in MU1 by lia. replace (sp1 + 16 + 16) with (sp1 + 32) in MU1 by lia.
clear FD. transport_after_call asegs m m1 MU1 WM1.
assert (SI1 : SINVA SHB0 m1 md A B F1 fc1 ptr (Z.max (rem - 9) 0) (firstn (Z.to_nat (Z.max (rem - 9) 0)) data) r BS LK sb sd).
{ eapply (SINVA_own SHB0 SHB0 m m1) with (F := F);
[ exact SI | exact MU1 | exact WM1 | exact MI1 | apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]]
| | exact FRM1 | exact LOC | exact LCK | exact ST1 | exists j8; exact SL | exact FD1 | exists fj; exact FF | exact FSH | reflexivity
| apply bytes_at_firstn; [exact (proj1 BYm) | lia] | rewrite firstn_length_le by lia; lia | exact P0 | exact P1 | lia ].
eapply fsaved_trans; [| exact FS1]. intros k Hk. rewrite !freg_get_other; [reflexivity|..]; cbn [FSAVED In] in Hk;
repeat (destruct Hk as [<- | Hk]); try (vm_compute; reflexivity); destruct Hk. }
pose proof SI1 as ((_ & _ & _ & _ & _ & _ & _ & _) & HP1 & RR1 & _).
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP1) as (errv1 & ERR1). cbn [hl_tp hl_segs A4L A4H hla_base] in ERR1. unfold A_TP in ERR1.
clear MU1 WM1.
step. step. evt_done5.
pose proof (ca_SETD _ _ _ _ _ _ _ CA) as SD. unfold jo_set_double_A_stmt, JO_SET_DOUBLE_A, JO_SETDBL_STK_A in SD. unfold JO_SETDBL_COSTB_A, JO_SETDBL_COSTD_A in *.
eapply SD with (A := A) (BS := BS) (LB := LK ++ LB0) (r := r) (lo := lo) (errv := errv1);
[ split; [exact HP1|]; rewrite unsigned_lit by lia;
split; [exact ST1|]; split; [exact LO|]; split; [lia|]; split; [exact sp1_16'|]; split; [lia|];
split; [exact ERR1|]; split; [reflexivity | vm_compute; reflexivity]
| exact RR1 | lia | lia | reflexivity |].
intros ms' md' m' rv A' B' BS' (RS & VM' & ST' & HPR' & [errv' ERR']) [CHB CHD] ERRx RR' HP' BSEQ.
destruct RS as (xt0 & xt1 & xt2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & F' & fc' & -> & FS' & FRM').
rewrite unsigned_lit in ST', HPR' by lia.
replace (ret_pc (Z_to_bv 64 0x91e44)) with (Z_to_bv 64 0x91e44 : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unfold KSA, hstateA in K. eapply K.
eapply SINVA_ret; [exact SI1 | exact HPR' | exact VM' | exact FS' | exact (FRM' FRM1) | exact ST' | exact HP' | exact RR' | | lia | lia | (destruct r as [|shq|tjq|]; [exact I | destruct shq; cbn [rootWm set_double_root] in BSEQ |- *; first [exact I | rewrite BSEQ; exact RW] | exact I | exact I])].
pose proof (rdepth_set_double_rootA (fn_dbl_to_json_string A4F) r). lia.
Qed.

#[using="CtxAll HINVA_callc EVDc FSLc OWNc GAOc"] Lemma crls2_callA : forall (ret : Z) (s10v : word) shb m md (A : ASA A4L HIx) B F fc ptr rem data r BS LK sb sd
(gp t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
0 <= ret < 2^64 -> ret mod 2 = 0 ->
forallb (fun b => bv_unsigned b =? 0) (firstn 3 (skipn 12 shb)) = true ->
SINVA shb m md A B F fc ptr rem data r BS LK sb sd ->
(forall m' ptr' rem' data' (n : Z) (str rest : list byte) (xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
SINVA shb m' md A B F fc ptr' rem' data' r BS LK sb sd ->
rw_cells asegs m' (Fr + 96) [C1 (Z_to_bv 8 (2 * n)); CB 23 (str ++ Z_to_bv 8 0 :: rest)] ->
0 <= n <= 10 -> Z.of_nat (length str) <= n -> ~ In (Z_to_bv 8 0) str ->
AJ5 A4L HIx A T md (hstateAc s10v (Z_to_bv 64 ret) gp xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 F ret fc m')) ->
AJ5 A4L HIx A T md (hstateAc s10v (Z_to_bv 64 ret) gp t0 t1 t2 (Z_to_bv 64 (Fr + 96)) (Z_to_bv 64 (sp1 + 16)) (Z_to_bv 64 10) a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x922cc fc m).
Proof.
intros ret s10v shb m md A B F fc ptr rem data r BS LK sb sd gp t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Hret Hret2 SHZ SI K.
seg_open SI m.
assert (INCL : incl LB0 (BS ++ LK ++ LB0)) by (intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb).
destruct (EVDc A (BS ++ LK ++ LB0) B m md ptr rem HP INCL P1 P2) as (RTm & UNPm & UND).
assert (UNSm : unpoisoned asegs m A_SB (Fr + 96) 24) by (exact (FSLc m shb 12%nat 15%nat FSH LSH ltac:(lia) ltac:(lia) SHZ)).
assert (INF : In (Fr, 2) [(Fr, 2)]) by (left; reflexivity).
(let L := constr:(A4L) in reenterA asegs L HIx asegs_wx HP).

destruct (rw_cells_CB_cut asegs _ _ _ _ 96 FF ltac:(lia)) as [FA FB']. change (Z.of_nat 96) with 96 in FB'. change (248 - 96)%nat with 152%nat in FB'.
destruct (rw_cells_CB_cut asegs _ _ _ _ 24 FB' ltac:(lia)) as [S1 FB]. clear FB'. change (Z.of_nat 24) with 24 in FB. change (152 - 24)%nat with 128%nat in FB.
replace (Fr + 96 + 24) with (Fr + 120) in FB by lia.
clear FF.
eapply evt_cut; [eapply QgoM.Mq0.crls_A with (S := Fr + 96) (P := sp1 + 16) (ptr := ptr) (rem := rem) (lo := lo) (maxlen := 10) (data := data) |].
all: rewrite ?unsigned_lit by lia.
1: reflexivity.
1: reflexivity.
1: reflexivity.
1: lia.
1: exact RTm.
1: exact S1.
1: exact UNSm.
1: clear - FRAL; Z.div_mod_to_equations; lia.
1: lia.
1: unfold app_range, A_SB, A_HMB in *; lia.
1: exact FD.
1: exact UNPm.
1: clear - SPA1; Z.div_mod_to_equations; lia.
1: exact BY.
1: exact L.
1: exact P0.
1: exact UND.
1: exact ST.
1: exact LO.
1: unfold CRLS_STK_A; lia.
1: clear - SPA1; Z.div_mod_to_equations; lia.
1: lia.
1: lia.
1: { destruct (Z.eq_dec rem 0) as [R0 | RN]; [left; exact R0 | right]. destruct INB as [Z0 | INB']; [lia|].
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF (in_or_app _ _ _ (or_introl (INCL _ INB')))) as DF. rewrite Q1Ey.fr_size_2 in DF. lia. }
1: lia.
1: lia.
1: exact MI.
intros ms3 (yt0 & yt1 & yt2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & yt3 & yt4 & yt5 & yt6 & m3 & n1 & k1 & str1 & rest1 & -> & MU3 & WM3 & MI3 & Hn1 & Hstr1 & NONUL1 & STR3 & Hk1 & FD3 & PAY3 & ST3).
unfold crls_WA in MU3. rewrite unsigned_lit in MU3, ST3 by lia.
assert (FSH3 : rw_cells asegs m3 sh (map C1 shb)).
{ eapply rw_cells_transport; [exact FSH | exact MU3 | exact WM3 |]. rewrite cells_size_C1, LSH. cbn [disjoint_from]. unfold A_SB, A_HMB in FRAPP. change (Z.of_nat 32) with 32. lia. }
clear S1 FD BY ST FSH.
transport_after_call asegs m m3 MU3 WM3.
replace (ret_pc (Z_to_bv 64 ret)) with (Z_to_bv 64 ret : word) by (symmetry; apply ret_pc_even; [lia | exact Hret2]).

assert (FJ : exists fj', rw_cells asegs m3 Fr [CB 248 fj']).
{ lazymatch type of STR3 with rw_cells _ _ _ ?c3 => lazymatch type of FB with rw_cells _ _ _ ?c4 =>
assert (X1 : rw_cells asegs m3 (Fr + 96) (c3 ++ c4)) by (apply (proj2 (rw_cells_app asegs m3 (Fr + 96) c3 c4)); split; [exact STR3 | cbn [cells_size csize Nat.add]; replace (Fr + 96 + Z.of_nat 24) with (Fr + 120) by lia; exact FB]) end end.
lazymatch type of FA with rw_cells _ _ _ ?c1 => lazymatch type of X1 with rw_cells _ _ _ ?c34 =>
assert (X3 : rw_cells asegs m3 Fr (c1 ++ c34)) by (apply (proj2 (rw_cells_app asegs m3 Fr c1 c34)); split; [exact FA | cbn [cells_size csize Nat.add]; change (Z.of_nat 96) with 96; exact X1]) end end.
lazymatch type of X3 with rw_cells _ _ _ ?cs => change (rw_cells asegs m3 Fr ([] ++ cs ++ [])) in X3 end.
apply rw_cells_merge in X3. cbn [app] in X3.
lazymatch type of X3 with rw_cells _ _ _ [CB ?n ?b] => exists b; let v := eval vm_compute in n in change n with v in X3 end. exact X3. }
pose proof (bytes_at_skipn asegs m ptr data k1 (proj1 BYm) ltac:(lia)) as WIN3.
evt_done5.
eapply (K m3 (ptr + k1) (rem - k1) (skipn (Z.to_nat k1) data) n1 str1 rest1); [| exact STR3 | lia | exact Hstr1 | exact NONUL1].
eapply (SINVA_own shb shb m m3);
[ exact SI | exact MU3 | exact WM3 | exact MI3
| apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_cons; [right; left; cbn [fst snd]; lia | apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]]]
| apply fsaved_refl | exact FRM | exact LOC | exact LCK | exact ST3 | exists j8; exact SL | exact FD3 | exact FJ | exact FSH3 | exact LSH
| exact WIN3 | rewrite length_skipn; lia | lia | lia | lia ].
Qed.

#[using="CtxAll HINVA_callc EVDc FSLc OWNc GAOc"] Lemma crls3_callA : forall (ret : Z) (s10v : word) shb m md (A : ASA A4L HIx) B F fc ptr rem data r BS LK sb sd
(gp t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
0 <= ret < 2^64 -> ret mod 2 = 0 ->
forallb (fun b => bv_unsigned b =? 0) (firstn 3 (skipn 20 shb)) = true ->
SINVA shb m md A B F fc ptr rem data r BS LK sb sd ->
(forall m' ptr' rem' data' (n : Z) (str rest : list byte) (xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
SINVA shb m' md A B F fc ptr' rem' data' r BS LK sb sd ->
rw_cells asegs m' (Fr + 160) [C1 (Z_to_bv 8 (2 * n)); CB 23 (str ++ Z_to_bv 8 0 :: rest)] ->
0 <= n <= 10 -> Z.of_nat (length str) <= n -> ~ In (Z_to_bv 8 0) str ->
AJ5 A4L HIx A T md (hstateAc s10v (Z_to_bv 64 ret) gp xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 F ret fc m')) ->
AJ5 A4L HIx A T md (hstateAc s10v (Z_to_bv 64 ret) gp t0 t1 t2 (Z_to_bv 64 (Fr + 160)) (Z_to_bv 64 (sp1 + 16)) (Z_to_bv 64 10) a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x922cc fc m).
Proof.
intros ret s10v shb m md A B F fc ptr rem data r BS LK sb sd gp t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Hret Hret2 SHZ SI K.
seg_open SI m.
assert (INCL : incl LB0 (BS ++ LK ++ LB0)) by (intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb).
destruct (EVDc A (BS ++ LK ++ LB0) B m md ptr rem HP INCL P1 P2) as (RTm & UNPm & UND).
assert (UNSm : unpoisoned asegs m A_SB (Fr + 160) 24) by (exact (FSLc m shb 20%nat 23%nat FSH LSH ltac:(lia) ltac:(lia) SHZ)).
assert (INF : In (Fr, 2) [(Fr, 2)]) by (left; reflexivity).
(let L := constr:(A4L) in reenterA asegs L HIx asegs_wx HP).

destruct (rw_cells_CB_cut asegs _ _ _ _ 160 FF ltac:(lia)) as [FA FB']. change (Z.of_nat 160) with 160 in FB'. change (248 - 160)%nat with 88%nat in FB'.
destruct (rw_cells_CB_cut asegs _ _ _ _ 24 FB' ltac:(lia)) as [S1 FB]. clear FB'. change (Z.of_nat 24) with 24 in FB. change (88 - 24)%nat with 64%nat in FB.
replace (Fr + 160 + 24) with (Fr + 184) in FB by lia.
clear FF.
eapply evt_cut; [eapply QgoM.Mq0.crls_A with (S := Fr + 160) (P := sp1 + 16) (ptr := ptr) (rem := rem) (lo := lo) (maxlen := 10) (data := data) |].
all: rewrite ?unsigned_lit by lia.
1: reflexivity.
1: reflexivity.
1: reflexivity.
1: lia.
1: exact RTm.
1: exact S1.
1: exact UNSm.
1: clear - FRAL; Z.div_mod_to_equations; lia.
1: lia.
1: unfold app_range, A_SB, A_HMB in *; lia.
1: exact FD.
1: exact UNPm.
1: clear - SPA1; Z.div_mod_to_equations; lia.
1: exact BY.
1: exact L.
1: exact P0.
1: exact UND.
1: exact ST.
1: exact LO.
1: unfold CRLS_STK_A; lia.
1: clear - SPA1; Z.div_mod_to_equations; lia.
1: lia.
1: lia.
1: { destruct (Z.eq_dec rem 0) as [R0 | RN]; [left; exact R0 | right]. destruct INB as [Z0 | INB']; [lia|].
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF (in_or_app _ _ _ (or_introl (INCL _ INB')))) as DF. rewrite Q1Ey.fr_size_2 in DF. lia. }
1: lia.
1: lia.
1: exact MI.
intros ms3 (yt0 & yt1 & yt2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & yt3 & yt4 & yt5 & yt6 & m3 & n1 & k1 & str1 & rest1 & -> & MU3 & WM3 & MI3 & Hn1 & Hstr1 & NONUL1 & STR3 & Hk1 & FD3 & PAY3 & ST3).
unfold crls_WA in MU3. rewrite unsigned_lit in MU3, ST3 by lia.
assert (FSH3 : rw_cells asegs m3 sh (map C1 shb)).
{ eapply rw_cells_transport; [exact FSH | exact MU3 | exact WM3 |]. rewrite cells_size_C1, LSH. cbn [disjoint_from]. unfold A_SB, A_HMB in FRAPP. change (Z.of_nat 32) with 32. lia. }
clear S1 FD BY ST FSH.
transport_after_call asegs m m3 MU3 WM3.
replace (ret_pc (Z_to_bv 64 ret)) with (Z_to_bv 64 ret : word) by (symmetry; apply ret_pc_even; [lia | exact Hret2]).

assert (FJ : exists fj', rw_cells asegs m3 Fr [CB 248 fj']).
{ lazymatch type of STR3 with rw_cells _ _ _ ?c3 => lazymatch type of FB with rw_cells _ _ _ ?c4 =>
assert (X1 : rw_cells asegs m3 (Fr + 160) (c3 ++ c4)) by (apply (proj2 (rw_cells_app asegs m3 (Fr + 160) c3 c4)); split; [exact STR3 | cbn [cells_size csize Nat.add]; replace (Fr + 160 + Z.of_nat 24) with (Fr + 184) by lia; exact FB]) end end.
lazymatch type of FA with rw_cells _ _ _ ?c1 => lazymatch type of X1 with rw_cells _ _ _ ?c34 =>
assert (X3 : rw_cells asegs m3 Fr (c1 ++ c34)) by (apply (proj2 (rw_cells_app asegs m3 Fr c1 c34)); split; [exact FA | cbn [cells_size csize Nat.add]; change (Z.of_nat 160) with 160; exact X1]) end end.
lazymatch type of X3 with rw_cells _ _ _ ?cs => change (rw_cells asegs m3 Fr ([] ++ cs ++ [])) in X3 end.
apply rw_cells_merge in X3. cbn [app] in X3.
lazymatch type of X3 with rw_cells _ _ _ [CB ?n ?b] => exists b; let v := eval vm_compute in n in change n with v in X3 end. exact X3. }
pose proof (bytes_at_skipn asegs m ptr data k1 (proj1 BYm) ltac:(lia)) as WIN3.
evt_done5.
eapply (K m3 (ptr + k1) (rem - k1) (skipn (Z.to_nat k1) data) n1 str1 rest1); [| exact STR3 | lia | exact Hstr1 | exact NONUL1].
eapply (SINVA_own shb shb m m3);
[ exact SI | exact MU3 | exact WM3 | exact MI3
| apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_cons; [right; left; cbn [fst snd]; lia | apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]]]
| apply fsaved_refl | exact FRM | exact LOC | exact LCK | exact ST3 | exists j8; exact SL | exact FD3 | exact FJ | exact FSH3 | exact LSH
| exact WIN3 | rewrite length_skipn; lia | lia | lia | lia ].
Qed.

Definition SHB2 : list byte := map (Z_to_bv 8)
[0xf1;0xf1;0xf1;0xf1; 0xf8;0xf8;0xf8;0xf2; 0xf2;0xf2;0xf2;0xf2; 0;0;0;0xf2; 0xf2;0xf2;0xf2;0xf2; 0xf8;0xf8;0xf8;0xf2; 0xf2;0xf2;0xf2;0xf2; 0xf8;0xf3;0xf3;0xf3].
Definition SHB3 : list byte := map (Z_to_bv 8)
[0xf1;0xf1;0xf1;0xf1; 0xf8;0xf8;0xf8;0xf2; 0xf2;0xf2;0xf2;0xf2; 0xf8;0xf8;0xf8;0xf2; 0xf2;0xf2;0xf2;0xf2; 0;0;0;0xf2; 0xf2;0xf2;0xf2;0xf2; 0xf8;0xf3;0xf3;0xf3].
Definition W0 : list (Z * Z) := [(lo, sp1 + 32); (Fr, Fr + 248); (Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 32)].
#[using="CtxAll"] Lemma W0_own : Forall (own_iv sp1 lo Fr) W0.
Proof. unfold W0, own_iv. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. Qed.

#[using="CtxAll HINVA_callc EVDc FSLc OWNc GAOc CA"] Lemma seg_setstringA : forall m md (A : ASA A4L HIx) B F fc ptr rem data r BS LK sb sd
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
SINVA SHB0 m md A B F fc ptr rem data r BS LK sb sd ->
sb + 1200 <= TGT_BB_A_jo -> sd + JO_SETSTR_COSTD_A <= TGT_BD_A_jo ->
KSA (Z_to_bv 64 (-1)) 0x91eac (set_string_root r) (sb + 1200) (sd + JO_SETSTR_COSTD_A) ->
AJ5 A4L HIx A T md (hstateAc (Z_to_bv 64 (-1)) x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x91e44 fc m).
Proof.
intros m md A B F fc ptr rem data r BS LK sb sd x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 SI CB CD K.
seg_open SI m.
pose proof W0_own as WOK. unfold W0 in WOK. fold sh in WOK.
pose proof (munch_refl [(lo, sp1 + 32); (Fr, Fr + 248); (sh, sh + 32)] m) as MU. pose proof (wmono_refl asegs m) as WM.
(let L := constr:(A4L) in reenterA asegs L HIx asegs_wx HP).
do 3 stepz. step. step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m2 end.
lazymatch goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
assert (SI2 : SINVA SHB2 m2 md A B F fc ptr rem data r BS LK sb sd).
{ eapply (SINVA_own SHB0 SHB2 m m2);
[ exact SI | exact MU | exact WM | exact MI2 | exact WOK | apply fsaved_refl | exact FRM | exact LOC | exact LCK | eassumption | exists j8; eassumption | eassumption
| exists fj; eassumption | eassumption | reflexivity | exact (proj1 BYm) | exact L | exact P0 | exact P1 | exact P2 ]. }
evt_done5.
eapply (crls2_callA 0x91e60 (Z_to_bv 64 (-1)) SHB2 m2); [lia | reflexivity | vm_compute; reflexivity | exact SI2 |].
clear - K CB CD LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP BB0 BD0 CA HINVA_callc EVDc FSLc OWNc GAOc.
intros m3 ptr3 rem3 data3 n3 str3 rest3 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 SI3 STR3 Hn3 Hstr3 NONUL3.
pose proof SI3 as ((PX3 & VM3 & FS3 & FRM3 & LOC3 & LCK3 & G3 & ST3 & _ & _ & _ & FSH3 & LSH3 & _ & _ & _ & _ & _) & HP3 & RR3 & RD3 & BB3 & BD3 & RW3).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI3. change (hl_segs A4L) with asegs in MI3.
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP3) as (errv3 & ERR3). cbn [hl_tp hl_segs A4L A4H hla_base] in ERR3. unfold A_TP in ERR3.
pose proof alloc_ceiling_range as ACR. pose proof (hiA_top_le A4L HIx) as HT47.
pose proof (bv_unsigned_in_range 64 sp0) as SP0R. change (bv_modulus 64) with (2^64) in SP0R.
assert (UNS3 : unpoisoned asegs m3 A_SB (Fr + 96) 24) by (exact (FSLc m3 SHB2 12%nat 15%nat FSH3 LSH3 ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity))).
assert (LREST : Z.of_nat (length rest3) = 22 - Z.of_nat (length str3)).
{ destruct STR3 as [[WF _] _]. cbn in WF. rewrite length_app in WF. cbn [length] in WF. lia. }
pose proof STR3 as STRB. apply rw_cells_app with (cs1 := [_]) in STRB as [_ STRB]. cbn [cells_size csize Nat.add] in STRB.
pose proof (rw_cells_bytes_at asegs m3 _ _ STRB) as SB. cbn [cells_bytes cbytes app] in SB. rewrite app_nil_r in SB.
change (Fr + 96 + Z.of_nat 1) with (Fr + 96 + 1) in SB. clear STRB FSH3.
pose proof (munch_refl (@nil (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
unfold hstateA, A_TP.
reenterA asegs A4L HIx asegs_wx HP3.
step. step. rewrite short_flag0A by lia. step. if_false. step. step. step. step.
evt_done5.
pose proof (ca_SETS _ _ _ _ _ _ _ CA) as SS. unfold jo_set_string_A_stmt, JO_SET_STRING_A, JO_SETSTR_STK_A, jo_setstr_costB in SS. unfold JO_SETSTR_COSTD_A in *.
eapply SS with (A := A) (BS := BS) (LB := LK ++ LB0) (FRS := [(Fr, 2)]) (B := B) (lo := lo) (p := p) (S := Fr + 96 + 1) (sb := str3) (slack := rest3) (r := r) (errv := errv3).
- split; [exact HP3|]. rewrite unsigned_lit by lia.
split; [exact ST3|]. split; [exact LO|]. split; [lia|]. split; [exact sp1_16'|]. split; [lia|].
split; [exact ERR3|]. split; [reflexivity | vm_compute; reflexivity].
- exact RR3.
- split; [exact SB|]. split; [apply Forall_forall; intros b Hb E0; apply NONUL3; replace (Z_to_bv 8 0) with b by (apply bv_eq; rewrite E0; reflexivity); exact Hb|].
split; [rewrite LREST; clear - FRAL Hstr3 Hn3; Z.div_mod_to_equations; lia|].
split; [exists Fr, 2; split; [left; reflexivity|]; rewrite Q1Ey.fr_size_2; lia|].
eapply (QsKa.Mq1.unpoisoned_sub_any asegs _ A_SB (Fr + 96) 24); [exact UNS3 | lia | lia | lia].
- lia.
- lia.
- lia.
- reflexivity.
- f_equal. lia.
- unfold set_string_postA.
intros ms4 md4 m4 rv4 A4 B4 BS4 (RS4 & VM4 & ST4 & HPR4 & [errv4 ERR4]) [CHB4 CHD4] RR4 HP4 SLEN4 BSEQ4.
destruct RS4 as (zt0 & zt1 & zt2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 & F4 & fc4 & -> & FS4 & FRM4).
rewrite unsigned_lit in ST4, HPR4 by lia.
replace (ret_pc (Z_to_bv 64 0x91e80)) with (Z_to_bv 64 0x91e80 : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
assert (SI4 : SINVA SHB2 m4 md4 A4 B4 F4 fc4 ptr3 rem3 data3 (set_string_root r) BS4 LK (sb + 1200) (sd + 2)).
{ eapply SINVA_ret; [exact SI3 | exact HPR4 | exact VM4 | exact FS4 | exact (FRM4 FRM3) | exact ST4 | exact HP4 | exact RR4 | | lia | lia | (destruct r as [|shq|tjq|]; [exact I | destruct shq; cbn [rootWm set_string_root is_string_root] in BSEQ4 |- *; first [exact I | rewrite (BSEQ4 eq_refl); exact RW3] | exact I | exact I])].
pose proof (rdepth_set_string_rootA r). lia. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in STR3;
[| eapply (client_range_block A4H _ _ _ _ Fr 248); [apply in_or_app; right; apply in_or_app; right; left; reflexivity | lia | cbn [cells_size csize Nat.add]; lia]].
change (hl_segs A4H) with asegs in *.
clear SI3 HP3 RR3 SB UNS3 ERR3 MU WM MI3 PX3 VM3 FS3 LOC3 LCK3 G3 ST3.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI4. change (hl_segs A4L) with asegs in MI4.
pose proof (munch_refl (@nil (Z * Z)) m4) as MU. pose proof (wmono_refl asegs m4) as WM.
reenterA asegs A4L HIx asegs_wx HP4. change (hl_segs A4H) with asegs.
step. step. rewrite short_flag0A by lia. step. if_true.
step.
clear STR3 MU WM.
pose proof SI4 as ((_ & _ & _ & _ & LOC4 & LCK4 & _ & _ & [j84 SL4] & FD4 & [fj4 FF4] & FSH4 & _ & BY4 & L4 & P04 & P14 & P24) & _).
unfold T_LOCCELL_A, T_LOCALE_LOCK_A, A_TP in LOC4, LCK4. unfold SHB2 in FSH4. cbn [map] in FSH4.
fold sh in FSH4.
assert (SHR4 : 2147450880 <= sh /\ sh + 32 <= 17594333495296) by (unfold sh; clear - FRLO FRHI ACR; Z.div_mod_to_equations; lia).
pose proof FRAPP as FRAPPu. unfold A_SB, A_HMB in FRAPPu.
assert (BYm4 : bytes_at asegs m4 ptr3 data3 /\ True) by (split; [exact BY4 | exact I]). clear BY4.
pose proof W0_own as WOK. unfold W0 in WOK. fold sh in WOK.
pose proof (munch_refl [(lo, sp1 + 32); (Fr, Fr + 248); (sh, sh + 32)] m4) as MU. pose proof (wmono_refl asegs m4) as WM.
fold sh.
do 3 stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m5 end.
lazymatch goal with H : mem_inv asegs m5 |- _ => rename H into MI5 end.
evt_done5.
unfold KSA, hstateA in K. fold sh in K. eapply K.
eapply (SINVA_own SHB2 SHB0 m4 m5);
[ exact SI4 | exact MU | exact WM | exact MI5 | exact WOK | apply fsaved_refl | exact (FRM4 FRM3) | exact LOC4 | exact LCK4 | eassumption | exists j84; eassumption | eassumption
| exists fj4; eassumption | eassumption | reflexivity | exact (proj1 BYm4) | exact L4 | exact P04 | exact P14 | exact P24 ].
Qed.

#[using="CtxAll HINVA_callc EVDc OWNc GAOc CA"] Lemma seg_setboolA : forall m md (A : ASA A4L HIx) B F fc ptr rem data r BS LK sb sd
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
SINVA SHB0 m md A B F fc ptr rem data r BS LK sb sd ->
KSA (Z_to_bv 64 (-1)) 0x91eec r sb sd ->
AJ5 A4L HIx A T md (hstateAc (Z_to_bv 64 (-1)) x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x91eac fc m).
Proof.
intros m md A B F fc ptr rem data r BS LK sb sd x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 SI K.
seg_open SI m.
assert (INCL : incl LB0 (BS ++ LK ++ LB0)) by (intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb).
destruct (EVDc A (BS ++ LK ++ LB0) B m md ptr rem HP INCL P1 P2) as (_ & _ & UND).
pose proof (bytes_at_bound _ _ _ _ BY) as DB.
assert (WAPP : Forall (fun iv : Z * Z => snd iv <= A_SB \/ A_HMB <= fst iv) [(sp1 + 24, sp1 + 32)]).
{ unfold A_SB, A_HMB. apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]. }
pose proof (munch_refl [(sp1 + 24, sp1 + 32)] m) as MU. pose proof (wmono_refl asegs m) as WM.
(let L := constr:(A4L) in reenterA asegs L HIx asegs_wx HP).
assert (EXITK : forall (mc : word -> option byte) (ya0 ya1 ya2 : word) (c : Z),
rw_cells asegs mc (sp1 + 16) [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 c)] -> c = Z.max (rem - 1) 0 ->
munch [(sp1 + 24, sp1 + 32)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
evt asegs (AJ5e A4L HIx A T md)
(MS (mkR x1 (Z_to_bv 64 sp1) gp (Z_to_bv 64 6434400) t0 t1 t2 sp0 (Z_to_bv 64 sp1) ya0 ya1 ya2 a3 a4 a5 a6 a7
(Z_to_bv 64 Fr) (Z_to_bv 64 (Fr + 160)) (Z_to_bv 64 p) (Z_to_bv 64 (Fr + 224)) (Z_to_bv 64 (Fr + 96)) (Z_to_bv 64 sh)
(Z_to_bv 64 Fr) (Z_to_bv 64 2147450880) (Z_to_bv 64 (-1)) s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x91ee4) fc None mc (seg_rom asegs))).
{ intros mc ya0 ya1 ya2 c FDc Hc MUc WMc MIc.
clear FD MU WM. transport_after_call asegs m mc MUc WMc.
step. step.
evt_done5.
eapply (set_callA 0x9c2ac 0x91eec (Z_to_bv 64 (-1))); [exact (ca_SETB _ _ _ _ _ _ _ CA) | lia | reflexivity | | exact K].
eapply (SINVA_own SHB0 SHB0 m mc) with (ptr' := ptr) (rem' := c) (data' := firstn (Z.to_nat c) data);
[ exact SI | exact MUc | exact WMc | exact MIc | apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil] | apply fsaved_refl | exact FRM
| exact LOC | exact LCK | exact ST | exists j8; exact SL | exact FDc | exists fj; exact FF | exact FSH | reflexivity
| apply bytes_at_firstn; [exact (proj1 BYm) | lia] | rewrite firstn_length_le by lia; lia | exact P0 | exact P1 | lia ]. }
step. step.
destruct (Z.eq_dec rem 0) as [R0 | RN].
{ rewrite R0. if_true. step.
eapply EXITK with (c := rem); [exact FD | lia | exact MU | exact WM | exact MI]. }
if_falsex.
step. step. step. step.
lazymatch goal with MUd : munch _ m ?md' |- evt _ _ (MS _ _ _ _ _ ?md' _) =>
assert (UNDd : unpoisoned asegs md' A_SB ptr rem) by (eapply unpoisoned_keep; [exact (UND ltac:(lia)) | exact MUd | lia | lia | exact WAPP]);
pose proof BY as BYd;
destruct (unpoisoned_byte_ro md' ptr rem (ptr + (rem + -1)) UNDd ltac:(lia)) as (v1 & SHK & Hv1) end.
destruct (nth_error data (Z.to_nat (rem - 1))) as [b1|] eqn:Hb1; [| exfalso; apply nth_error_None in Hb1; lia].
pose proof (bv_unsigned_in_range 8 b1) as BR1. unfold bv_modulus in BR1. cbn in BR1.
step. step. sh_norm. step. step.
lazymatch goal with |- evt _ ?Q (MS _ _ _ _ _ ?mm _) =>
assert (BE0 : forall (za1 za2 : word),
evt asegs Q (MS (mkR x1 (Z_to_bv 64 sp1) gp (Z_to_bv 64 6434400) t0 t1 t2 sp0 (Z_to_bv 64 sp1) (Z_to_bv 64 (ptr + (rem + -1))) za1 za2 a3 a4 a5 a6 a7
(Z_to_bv 64 Fr) (Z_to_bv 64 (Fr + 160)) (Z_to_bv 64 p) (Z_to_bv 64 (Fr + 224)) (Z_to_bv 64 (Fr + 96)) (Z_to_bv 64 sh)
(Z_to_bv 64 Fr) (Z_to_bv 64 2147450880) (Z_to_bv 64 (-1)) s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x91ed4) fc None mm (seg_rom asegs))) end.
2:{ destruct Hv1 as [-> | [Hv8 Hvm]].
- rewrite sxb_zero. if_false. apply BE0.
- rewrite (QsKa.Mq1.sxb_small v1) by lia. if_truex. step. step.
rewrite (unsigned_lit (ptr + (rem + -1))) by lia. rewrite QsKa.Mq1.land7_mod8 by lia. if_truex. apply BE0. }
intros za1 za2. clear SHK v1 Hv1 UNDd.
pose proof (u8ro_read asegs _ ptr data (rem - 1) b1 _ BYd Hb1 ltac:(lia) eq_refl) as RD1.
replace (ptr + (rem - 1)) with (ptr + (rem + -1)) in RD1 by lia.
step. clear RD1.
step. step.
lazymatch goal with H : rw_cells asegs ?mx (sp1 + 16) _ |- _ => rename H into FD3 end.
eapply EXITK with (c := rem + -1); [exact FD3 | lia | eassumption | eassumption | eassumption].
Qed.

Definition KSFA (k : Z) (r : jroot) (sb sd : Z) : Prop :=
forall m' md' (A' : ASA A4L HIx) B' F' fc' ptr' rem' data' BS' LK' (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
SINVA SHB3 m' md' A' B' F' fc' ptr' rem' data' r BS' LK' sb sd ->
(exists (n : Z) (sj23 : list byte), 0 <= n <= 10 /\ rw_cells asegs m' (Fr + 160) [C1 (Z_to_bv 8 (2 * n)); CB 23 sj23]) ->
(is_string_root r = true -> exists n : Z, 0 <= n <= 10 /\ str_lenA m' p n) ->
AJ5 A4L HIx A' T md' (hstateAc (Z_to_bv 64 (-1)) x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' k fc' m').

#[using="CtxAll HINVA_callc EVDc FSLc OWNc GAOc CA"] Lemma seg_setstrlenA : forall m md (A : ASA A4L HIx) B F fc ptr rem data r BS LK sb sd
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
SINVA SHB0 m md A B F fc ptr rem data r BS LK sb sd ->
sb + 1200 <= TGT_BB_A_jo -> sd + JO_SETSTR_COSTD_A <= TGT_BD_A_jo ->
KSFA 0x91f34 (set_string_root r) (sb + 1200) (sd + JO_SETSTR_COSTD_A) ->
AJ5 A4L HIx A T md (hstateAc (Z_to_bv 64 (-1)) x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x91eec fc m).
Proof.
intros m md A B F fc ptr rem data r BS LK sb sd x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 SI CB CD K.
seg_open SI m.
pose proof W0_own as WOK. unfold W0 in WOK. fold sh in WOK.
pose proof (munch_refl [(lo, sp1 + 32); (Fr, Fr + 248); (sh, sh + 32)] m) as MU. pose proof (wmono_refl asegs m) as WM.
(let L := constr:(A4L) in reenterA asegs L HIx asegs_wx HP).
do 3 stepz. step. step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m2 end.
lazymatch goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
assert (SI2 : SINVA SHB3 m2 md A B F fc ptr rem data r BS LK sb sd).
{ eapply (SINVA_own SHB0 SHB3 m m2);
[ exact SI | exact MU | exact WM | exact MI2 | exact WOK | apply fsaved_refl | exact FRM | exact LOC | exact LCK | eassumption | exists j8; eassumption | eassumption
| exists fj; eassumption | eassumption | reflexivity | exact (proj1 BYm) | exact L | exact P0 | exact P1 | exact P2 ]. }
evt_done5.
eapply (crls3_callA 0x91f08 (Z_to_bv 64 (-1)) SHB3 m2); [lia | reflexivity | vm_compute; reflexivity | exact SI2 |].
clear - K CB CD LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP BB0 BD0 CA HINVA_callc EVDc FSLc OWNc GAOc.
intros m3 ptr3 rem3 data3 n3 str3 rest3 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 SI3 STR3 Hn3 Hstr3 NONUL3.
pose proof SI3 as ((PX3 & VM3 & FS3 & FRM3 & LOC3 & LCK3 & G3 & ST3 & _ & _ & _ & FSH3 & LSH3 & _ & _ & _ & _ & _) & HP3 & RR3 & RD3 & BB3 & BD3 & RW3).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI3. change (hl_segs A4L) with asegs in MI3.
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP3) as (errv3 & ERR3). cbn [hl_tp hl_segs A4L A4H hla_base] in ERR3. unfold A_TP in ERR3.
pose proof alloc_ceiling_range as ACR. pose proof (hiA_top_le A4L HIx) as HT47.
pose proof (bv_unsigned_in_range 64 sp0) as SP0R. change (bv_modulus 64) with (2^64) in SP0R.
assert (UNS3 : unpoisoned asegs m3 A_SB (Fr + 160) 24) by (exact (FSLc m3 SHB3 20%nat 23%nat FSH3 LSH3 ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity))).
assert (L23 : length (str3 ++ Z_to_bv 8 0 :: rest3) = 23%nat) by (destruct STR3 as [[WF _] _]; cbn in WF; lia).
pose proof STR3 as STRB. apply rw_cells_app with (cs1 := [_]) in STRB as [_ STRB]. cbn [cells_size csize Nat.add] in STRB.
pose proof (rw_cells_bytes_at asegs m3 _ _ STRB) as SB. cbn [cells_bytes cbytes app] in SB. rewrite app_nil_r in SB.
change (Fr + 160 + Z.of_nat 1) with (Fr + 160 + 1) in SB. clear STRB FSH3.
pose proof (bytes_at_firstn asegs m3 _ _ n3 SB ltac:(lia)) as SBn.
pose proof (munch_refl (@nil (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
unfold hstateA, A_TP.
reenterA asegs A4L HIx asegs_wx HP3.
step. step. rewrite short_flag0A by lia. step. if_false. step. step. rewrite short_sizeA by lia. step. step. step. step.
rewrite (unsigned_lit n3) by lia. rewrite Z.add_0_r. rewrite (swrap32_id n3) by lia.
evt_done5.
pose proof (ca_SETSL _ _ _ _ _ _ _ CA) as SS. unfold jo_set_string_len_A_stmt, JO_SET_STRING_LEN_A, JO_SETSTR_STK_A, jo_setstr_costB in SS. unfold JO_SETSTR_COSTD_A in *.
assert (LSB : Z.of_nat (length (firstn (Z.to_nat n3) (str3 ++ Z_to_bv 8 0 :: rest3))) = n3) by (rewrite firstn_length_le by lia; lia).
eapply SS with (A := A) (BS := BS) (LB := LK ++ LB0) (FRS := [(Fr, 2)]) (B := B) (lo := lo) (p := p) (S := Fr + 160 + 1) (sb := firstn (Z.to_nat n3) (str3 ++ Z_to_bv 8 0 :: rest3)) (r := r) (errv := errv3).
- split; [exact HP3|]. rewrite unsigned_lit by lia.
split; [exact ST3|]. split; [exact LO|]. split; [lia|]. split; [exact sp1_16'|]. split; [lia|].
split; [exact ERR3|]. split; [reflexivity | vm_compute; reflexivity].
- exact RR3.
- split; [exact SBn|]. split; [exists Fr, 2; split; [left; reflexivity|]; rewrite Q1Ey.fr_size_2; lia|].
intros NE. rewrite LSB. assert (0 < n3) by (destruct (Z.eq_dec n3 0) as [E|]; [| lia]; exfalso; apply NE; rewrite E; reflexivity).
eapply (QsKa.Mq1.unpoisoned_sub_any asegs _ A_SB (Fr + 160) 24); [exact UNS3 | lia | lia | lia].
- lia.
- rewrite LSB. lia.
- lia.
- reflexivity.
- f_equal. lia.
- rewrite LSB. reflexivity.
- unfold set_string_postA. rewrite LSB.
intros ms4 md4 m4 rv4 A4 B4 BS4 (RS4 & VM4 & ST4 & HPR4 & [errv4 ERR4]) [CHB4 CHD4] RR4 HP4 SLEN4 BSEQ4.
destruct RS4 as (zt0 & zt1 & zt2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 & F4 & fc4 & -> & FS4 & FRM4).
rewrite unsigned_lit in ST4, HPR4 by lia.
replace (ret_pc (Z_to_bv 64 0x91f34)) with (Z_to_bv 64 0x91f34 : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
assert (SI4 : SINVA SHB3 m4 md4 A4 B4 F4 fc4 ptr3 rem3 data3 (set_string_root r) BS4 LK (sb + 1200) (sd + 2)).
{ eapply SINVA_ret; [exact SI3 | exact HPR4 | exact VM4 | exact FS4 | exact (FRM4 FRM3) | exact ST4 | exact HP4 | exact RR4 | | lia | lia | (destruct r as [|shq|tjq|]; [exact I | destruct shq; cbn [rootWm set_string_root is_string_root] in BSEQ4 |- *; first [exact I | rewrite (BSEQ4 eq_refl); exact RW3] | exact I | exact I])].
pose proof (rdepth_set_string_rootA r). lia. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in STR3;
[| eapply (client_range_block A4H _ _ _ _ Fr 248); [apply in_or_app; right; apply in_or_app; right; left; reflexivity | lia | cbn [cells_size csize Nat.add]; lia]].
change (hl_segs A4H) with asegs in *.
unfold KSFA, hstateA in K.
assert (ISR : is_string_root (set_string_root r) = is_string_root r) by (destruct r as [|shq|tjq|]; [reflexivity | destruct shq; reflexivity | reflexivity | reflexivity]).
eapply K; [exact SI4| | intros HS; first [exists n3; split; [clear - Hn3; lia | apply SLEN4; rewrite <- ISR; exact HS] | exists (Z.of_nat (length str3)); split; [clear - Hn3 Hstr3; lia | apply SLEN4; rewrite <- ISR; exact HS]]].
exists n3, (str3 ++ Z_to_bv 8 0 :: rest3). split; [lia | exact STR3].
Qed.

Definition setters_root (r : jroot) : jroot := set_string_root (set_string_root (set_double_root (fn_dbl_to_json_string A4F) r)).
#[using="CtxAll HINVA_callc EVDc FSLc OWNc GAOc CA"] Lemma seg_settersA : forall m md (A : ASA A4L HIx) B F fc ptr rem data r BS LK sb sd
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
SINVA SHB0 m md A B F fc ptr rem data r BS LK sb sd ->
sb + 2912 <= TGT_BB_A_jo -> sd + 5 <= TGT_BD_A_jo ->
KSFA 0x91f34 (setters_root r) (sb + 2912) (sd + 5) ->
AJ5 A4L HIx A T md (hstateAc (Z_to_bv 64 (-8)) x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x91ce0 fc m).
Proof.
intros m md A B F fc ptr rem data r BS LK sb sd x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 SI CB CD K.
unfold JO_SETDBL_COSTB_A, JO_SETDBL_COSTD_A, JO_SETSTR_COSTD_A in *.
eapply seg_setintA; [exact SI|]. intros s10v. unfold KSA. intros.
eapply seg_setint64A; [eassumption|]. unfold KSA. intros.
eapply seg_setuint64A; [eassumption|]. unfold KSA. intros.
eapply seg_setdoubleA; [eassumption | unfold JO_SETDBL_COSTB_A; lia | unfold JO_SETDBL_COSTD_A; lia |]. unfold KSA, JO_SETDBL_COSTB_A, JO_SETDBL_COSTD_A. intros.
eapply seg_setstringA; [eassumption | lia | unfold JO_SETSTR_COSTD_A; lia |]. unfold KSA, JO_SETSTR_COSTD_A. intros.
eapply seg_setboolA; [eassumption|]. unfold KSA. intros.
eapply seg_setstrlenA; [eassumption | lia | unfold JO_SETSTR_COSTD_A; lia |]. unfold JO_SETSTR_COSTD_A.
unfold KSFA in *. intros. unfold setters_root in K.
eapply K; [| eassumption | eassumption].
replace (sb + 2912) with (sb + 512 + 1200 + 1200) by lia. replace (sd + 5) with (sd + 1 + 2 + 2) by lia. eassumption.
Qed.
End Ctx.
End AHarnJo2.
End RC__1.
End Mq0.

Module Mq1.

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
Import QOmG Qw5U.Mq1 Ql4f.Mq0 Q63E.Mq0.

Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac QlEo_c1.solve_load ::= QrJ1.Mq0.mkr__solve_load_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.

Ltac c1_bytes cs := lazymatch cs with | nil => constr:(@nil byte) | C1 ?b :: ?r => let r' := c1_bytes r in constr:(b :: r') end.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section AHarnJo3.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Variables (tpB tpD : Z -> Z) (dcB dcD : Z -> Z) (gsS : jshape -> Z) (gsB : Z -> Z).
Hypothesis CA : jo_callees_A HIx tpB tpD dcB dcD gsS gsB.

Lemma seg_headA : forall (x1 gp t0 t1 t2 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 sp0 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet) (A : ASA A4L HIx) (LB LM : list blk) (B : bud)
(data size lo sp1 : Z) (payload j32 : list byte),
HEAPAx A LB LM [] B m md -> TGT_BB_A_jo <= bB B -> TGT_BD_A_jo <= bD B ->
bytes_at asegs m data payload -> Z.of_nat (length payload) = size -> 0 <= size < 2^26 -> 0 < data -> data + size <= alloc_ceiling ->
(size = 0 \/ In (data, size) LB) ->
rw_cells asegs m T_LOCCELL_A [C8 (Z_to_bv 64 T_GLOBLOC_A)] -> rw_cells asegs m T_LOCALE_LOCK_A [C4 (Z_to_bv 64 0)] -> GA_jo m ->
stk asegs m lo sp1 -> rw_cells asegs m sp1 [CB 32 j32] ->
alloc_ceiling <= lo -> lo <= sp1 - (2^20 - 144) -> hiA_bot A4L HIx <= lo -> sp1 mod 32 = 0 -> sp1 + 32 <= bv_unsigned sp0 -> bv_unsigned sp0 + 32 <= hiA_top A4L HIx ->
frm0 fc ->
Z.of_nat (length LM) < 8 ->
(forall n, 0 <= n <= 20 -> tpB n <= TGT_BB_A_jo /\ 1 + tpD n <= TGT_BD_A_jo) ->
(forall (Fr p n : Z) (s : option jshape) m' md' (A' : ASA A4L HIx) B' F' fc' ptr' rem' data' BS' LK' (y1 gp' y5 y6 y7 b0 b1 b2 b3 b4 b5 b6 b7 y28 y29 y30 y31 : word),
Fr mod 256 = 0 -> 6574080 <= Fr -> Fr + 256 <= alloc_ceiling -> (Fr + 256 + 8 <= A_SB \/ A_HMB <= Fr) -> 0 <= n <= 20 ->
(forall sh, s = Some sh -> exists w, jtx sh BS' = Some (w, []) /\ w <= 26 * (n + 1) + 64) ->
GINVA HIx sp0 sp1 lo Fr LB LM m md F B data size p m' md' A' B' F' fc' ptr' rem' data' s BS' LK' (tpB n) (1 + tpD n) ->
AJ5 A4L HIx A' T md' (hstateA sp0 sp1 Fr p s11 (Z_to_bv 64 (-8)) y1 gp' y5 y6 y7 b0 b1 b2 b3 b4 b5 b6 b7 y28 y29 y30 y31 F' 0x91c78 fc' m')) ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 sp1) gp (Z_to_bv 64 A_TP) t0 t1 t2 sp0 (Z_to_bv 64 sp1) (Z_to_bv 64 data) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x91adc) fc None m (seg_rom asegs)).
Proof.
intros until j32. intros HP BB BD PAY PLEN SZ D0 DCE INB LOC LCK GA ST FDA LO LOS HBOT SPA1 SP10 HT FRM LML TPC K.
pose proof (bv_unsigned_in_range 64 sp0) as SP0R. change (bv_modulus 64) with (2^64) in SP0R.
pose proof alloc_ceiling_range as ACR. pose proof (hiA_top_le A4L HIx) as HT47.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. change (hl_segs A4L) with asegs in MI.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP) as (SB1 & SB2 & SB3 & SB4).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2. apply ro_C8_of_bytes_at in SB3.
assert (UARC : ro_cells asegs m (hl_uar_cell A4L) [C4 (Z_to_bv 64 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SB4]).
clear SB4. a4l.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(lo, sp1 + 32)] m) as MU.
unfold A_TP in *.
reenterA asegs A4L HIx asegs_wx HP.
step. step. step. step. step. step. step. step.
norm_sx32. step. if_false. step. step.
evt_done5.
eapply (stack_malloc_full HIx) with (k := 2) (bytes := 256) (lo := lo) (LB := LB) (LM := LM) (FR := @nil frame) (B := B);
[ exact HP | lia | .. ].
all: rewrite ?unsigned_lit by lia.
1: rewrite Q1Ey.fr_size_2; lia.
1: reflexivity.
1: cbn [length]; lia.
1: exact ST.
1: exact LO.
1: cbn [hl_stack_A A4L]; lia.
1: clear - SPA1; Z.div_mod_to_equations; lia.
1: lia.
1: reflexivity.
1: reflexivity.
intros ms1 m1 md1 A1 Fr RS1 VM1 ST1 HPR1 FRNZ (jff & FF1) SHB1 HP1. open_ret RS1.
rewrite ?unsigned_lit in ST1, HPR1 by lia.

assert (INF : In (Fr, 2) [(Fr, 2)]) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as (_ & HFal & HF0 & HFc & HFimg & _ & HFshw & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFapp.
pose proof (frame_above_img HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFhi.
rewrite Q1Ey.fr_size_2 in HFal, HFc, HFimg, HFapp. rewrite Q1Ey.fr_shadow_len_2 in HFshw. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp, HFhi.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in FDA; [| left; cbn; lia].
assert (LOCcs : forall a, 6434400 - 48 <= a < 6434400 - 48 + 8 -> hl_client_static A4H a).
{ intros a Ha. cbn [hl_client_static A4H]. unfold a4_client_static. lia. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in LOC; [| right; left; cbn; intros z Hz; apply LOCcs; unfold T_LOCCELL_A, A_TP in Hz; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in LCK; [| right; left; cbn; intros z Hz; cbn [hl_client_static A4H]; unfold a4_client_static; unfold T_LOCALE_LOCK_A in Hz; lia].
assert (GA1 : GA_jo m1) by (eapply GA_jo_pres; [exact HPR1 | exact GA]).
assert (PAY1 : bytes_at asegs m1 data payload).
{ eapply (window_bytesG LB data size); [exact INB | exact PAY | exact PLEN | lia | lia |].
intros a Ha (b & Hb & Hr). apply (HPR1 a Ha). right; right. exists b. split; [apply in_or_app; left; exact Hb | exact Hr]. }
assert (PX1 : heap_presx A4H (xtgt_A (bv_unsigned sp0)) (LB ++ LM) (sp1 + 32) m m1).
{ apply heap_pres_presx. eapply heap_pres_weaken; [exact HPR1 | lia |]. intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; exact Hb | right; apply in_or_app; left; exact Hb]. }
clear SB1 SB2 SB3 UARC PAY GA. stash PAY1.
unfold T_LOCCELL_A, T_LOCALE_LOCK_A, A_TP in LOC, LCK.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP1) as (SB1 & SB2 & _ & _).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2. a4l.
assert (FSH1 : rw_cells asegs m1 (shad A4L Fr) [CB 32 (repeat (Z_to_bv 8 0) 32)]).
{ split; [split; [cbn; split; [reflexivity | exact I] | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SHB1] | exact HFshw]. }
rewrite Q1Ey.fr_size_2 in FF1. change (Z.to_nat (256 - 8)) with 248%nat in FF1.
unfold shad in FSH1. a4l.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 32 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1. change (hl_segs A4L) with asegs in MI1. clear MI.
clear MU WM. pose proof (wmono_refl asegs m1) as WM. pose proof (munch_refl [(lo, sp1 + 32); (Fr, Fr + 248); (sh, sh + 32)] m1) as MU.
unfold A_SB in HFapp.
reenterA asegs A4L HIx asegs_wx HP1.
step. step. step. step. if_truex.
stepz. step. step. step. step. step.
rewrite (unsigned_lit Fr) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
step. step. step. step. step.
stepz. stepz. stepz. step. step.
fold sh.
do 4 stepz. step. do 28 stepz.
stepz. stepz.
do 3 stepz.
step. step. step. step.

assert (FRAL : Fr mod 256 = 0) by exact HFal.
assert (FRLO : 6574080 <= Fr) by exact HFhi.
assert (FRHI : Fr + 256 <= alloc_ceiling) by exact HFc.
assert (FRAPP : Fr + 256 + 8 <= A_SB \/ A_HMB <= Fr) by (unfold A_SB, A_HMB; clear - HFapp; change ((2 ^ 47 - 1) / 8 + 2147450880 + 1) with 17594333495296 in HFapp; lia).
pose proof (fdp_evidenceA HIx sp0 sp1 lo Fr LB LM m md F B data size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP) as EVD.
pose proof (fslot_evidenceA HIx sp0 sp1 lo Fr LB LM m md F B data size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP) as FSL.
pose proof (own_writesA HIx sp0 sp1 lo Fr LB LM m md F B data size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP) as OWN.
pose proof (GA_jo_own HIx sp0 sp1 lo Fr LB LM m md F B data size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP) as GAO.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m2 end.
lazymatch goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
assert (WOK : Forall (own_iv sp1 lo Fr) [(lo, sp1 + 32); (Fr, Fr + 248); (sh, sh + 32)]).
{ unfold own_iv, sh. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
destruct (OWN A1 LB B m1 m2 md1 _ HP1 (incl_refl _) MU WM MI2 WOK) as (HP2 & HPX2 & AG2).
destruct (EVD A1 LB B m2 md1 data size HP2 (incl_refl _) ltac:(lia) ltac:(lia)) as (RT2 & UNP2 & UND2).
unstash PAY1.
assert (PAY2 : bytes_at asegs m2 data payload).
{ eapply (window_bytesG LB data size); [exact INB | exact PAY1 | exact PLEN | lia | lia |].
intros a Ha (b & Hb & Hr). apply (AG2 a Ha). exists b. split; [apply in_or_app; left; exact Hb | exact Hr]. }
clear PAY1.
assert (UNS2 : unpoisoned asegs m2 A_SB (Fr + 32) 24).
{ lazymatch type of FSH1 with rw_cells _ _ _ ?cs => let l := c1_bytes cs in
exact (FSL m2 l 4%nat 7%nat FSH1 eq_refl ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)) end. }

change [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 101026); C8 (Z_to_bv 64 596632); CB 224 (skipn 8 (skipn 8 (skipn 8 jff)))]
with ([C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 101026); C8 (Z_to_bv 64 596632)] ++ [CB 224 (skipn 8 (skipn 8 (skipn 8 jff)))]) in FF1.
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FF1 as [HDR BODY]. cbn [cells_size csize Nat.add] in BODY. change (Z.of_nat 24) with 24 in BODY.
destruct (rw_cells_CB_cut asegs _ _ _ _ 8 BODY ltac:(lia)) as [G0 B1]. clear BODY. change (Z.of_nat 8) with 8 in B1. change (224 - 8)%nat with 216%nat in B1.
replace (Fr + 24 + 8) with (Fr + 32) in B1 by lia.
destruct (rw_cells_CB_cut asegs _ _ _ _ 24 B1 ltac:(lia)) as [S1 B2]. clear B1. change (Z.of_nat 24) with 24 in B2. change (216 - 24)%nat with 192%nat in B2.
replace (Fr + 32 + 24) with (Fr + 56) in B2 by lia.
lazymatch type of FDA with rw_cells _ _ _ [?c0; ?c1; ?c2; ?c3] => change [c0; c1; c2; c3] with ([c0; c1] ++ [c2; c3]) in FDA end.
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FDA as [SL FDP]. cbn [cells_size csize Nat.add] in FDP. change (Z.of_nat 16) with 16 in FDP.
eapply evt_cut; [eapply QgoM.Mq0.crls_A with (S := Fr + 32) (P := sp1 + 16) (ptr := data) (rem := size) (lo := lo) (maxlen := 20) (data := payload) |].
all: rewrite ?unsigned_lit by lia.
1: reflexivity.
1: reflexivity.
1: reflexivity.
1: lia.
1: exact RT2.
1: exact S1.
1: exact UNS2.
1: clear - FRAL; Z.div_mod_to_equations; lia.
1: lia.
1: unfold app_range, A_SB, A_HMB in *; lia.
1: exact FDP.
1: exact UNP2.
1: clear - SPA1; Z.div_mod_to_equations; lia.
1: exact PAY2.
1: exact PLEN.
1: exact D0.
1: exact UND2.
1: lazymatch goal with H : stk asegs m2 lo sp1 |- _ => exact H end.
1: exact LO.
1: unfold CRLS_STK_A; lia.
1: clear - SPA1; Z.div_mod_to_equations; lia.
1: lia.
1: lia.
1: { destruct INB as [Z0 | INB']; [left; exact Z0 | right].
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP2 INF (in_or_app _ _ _ (or_introl INB'))) as DF. rewrite Q1Ey.fr_size_2 in DF. lia. }
1: lia.
1: lia.
1: exact MI2.
intros ms3 (yt0 & yt1 & yt2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & yt3 & yt4 & yt5 & yt6 & m3 & n1 & k1 & str1 & rest1 & -> & MU3 & WM3 & MI3 & Hn1 & Hstr1 & NONUL1 & STR3 & Hk1 & FD3 & PAY3 & ST3).
unfold crls_WA in MU3. rewrite unsigned_lit in MU3, ST3 by lia.
clear S1 FDP PAY2 RT2 UNP2 UND2 UNS2 HPX2 AG2.
transport_after_call asegs m2 m3 MU3 WM3. clear MU3 WM3 MI2.
replace (ret_pc (Z_to_bv 64 0x91c20)) with (Z_to_bv 64 0x91c20) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

step. step. rewrite short_flag0A by lia. step. if_false. step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m4 end.
lazymatch goal with H : mem_inv asegs m4 |- _ => rename H into MI4 end.
lazymatch goal with H : munch _ m1 m4 |- _ => rename H into MU4 end.
lazymatch goal with H : wmono asegs m1 m4 |- _ => rename H into WM4 end.
destruct (OWN A1 LB B m1 m4 md1 _ HP1 (incl_refl _) MU4 WM4 MI4 WOK) as (HP4 & HPX4 & AG4).
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP4) as (errv4 & ERR4). cbn [hl_tp hl_segs A4L A4H hla_base] in ERR4.
assert (LREST : Z.of_nat (length rest1) = 22 - Z.of_nat (length str1)).
{ destruct STR3 as [[WF _] _]. cbn in WF. rewrite length_app in WF. cbn [length] in WF. lia. }
pose proof STR3 as STRB. apply rw_cells_app with (cs1 := [_]) in STRB as [_ STRB]. cbn [cells_size csize Nat.add] in STRB.
pose proof (rw_cells_bytes_at asegs m4 _ _ STRB) as SB. cbn [cells_bytes cbytes app] in SB. rewrite app_nil_r in SB.
change (Fr + 32 + Z.of_nat 1) with (Fr + 32 + 1) in SB.
assert (UNS4 : unpoisoned asegs m4 A_SB (Fr + 32) 24).
{ lazymatch type of FSH1 with rw_cells _ _ _ ?cs => let l := c1_bytes cs in
exact (FSL m4 l 4%nat 7%nat FSH1 eq_refl ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)) end. }
pose proof (TPC (Z.of_nat (length str1)) ltac:(lia)) as CTP.
assert (PX4 : heap_presx A4H (xtgt_A (bv_unsigned sp0)) (LB ++ LM) (sp1 + 32) m m4) by (eapply heap_presx_trans; [exact PX1 | exact HPX4]).
pose proof (ca_TOKPARSE _ _ _ _ _ _ _ CA) as TPA. unfold jo_tokparse_A_stmt, JO_TOKPARSE_A, JO_TOKPARSE_STK_A, JO_TOKPARSE_URA_A in TPA.
replace (str1 ++ Z_to_bv 8 0 :: rest1) with (str1 ++ Z_to_bv 8 0 :: rest1) in SB by reflexivity.
assert (GA4 : GA_jo m4) by (exact (GAO m1 m4 _ GA1 MU4 WM4 WOK)).
evt_done5.
eapply TPA with (A := A1) (LBc := LB) (FRS := [(Fr, 2)]) (B := B) (sb := Fr + 32 + 1) (lo := lo) (str0 := str1) (slack := rest1) (errv := errv4) (u := UWpaid).
- split; [exact HP4|]. rewrite unsigned_lit by lia.
split; [lazymatch goal with H : stk asegs m4 lo sp1 |- _ => exact H end|]. split; [exact LO|]. split; [lia|]. split; [clear - SPA1; Z.div_mod_to_equations; lia|]. split; [lia|].
split; [exact ERR4|]. split; [reflexivity | vm_compute; reflexivity].
- rewrite unsigned_lit by lia. exact SPA1.
- exact LML.
- split; [exact SB|]. split; [apply Forall_forall; intros b Hb E0; apply NONUL1; replace (Z_to_bv 8 0) with b by (apply bv_eq; rewrite E0; reflexivity); exact Hb|].
split; [rewrite LREST; clear - FRAL Hstr1 Hn1; Z.div_mod_to_equations; lia|].
split; [exists Fr, 2; split; [exact INF|]; rewrite Q1Ey.fr_size_2; lia|].
eapply (QsKa.Mq1.unpoisoned_sub_any asegs _ A_SB (Fr + 32) 24); [exact UNS4 | lia | lia | lia].
- lia.
- split; [exact LOC|]. split; [exact LCK|]. split; [exact (proj1 GA4) | exact (proj2 (proj2 GA4))].
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
assert (INFR : In (Fr, 248) (LB ++ LM ++ fr_ivs A4L [(Fr, 2)])) by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
assert (INSH : In (sh, 32) (LB ++ LM ++ fr_ivs A4L [(Fr, 2)])) by (apply in_or_app; right; apply in_or_app; right; right; left; reflexivity).
apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPX5) in HDR; [| right; right; exists (Fr, 248); split; [exact INFR | cbn; lia]].
apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPX5) in G0; [| right; right; exists (Fr, 248); split; [exact INFR | cbn; lia]].
apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPX5) in STR3; [| right; right; exists (Fr, 248); split; [exact INFR | cbn; lia]].
apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPX5) in B2; [| right; right; exists (Fr, 248); split; [exact INFR | cbn; lia]].
apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPX5) in FSH1; [| right; right; exists (sh, 32); split; [exact INSH | cbn; lia]].
apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPX5) in SL; [| left; lia].
apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPX5) in FD3; [| left; lia].
assert (PAY5 : bytes_at asegs m5 data payload).
{ eapply (window_bytesG LB data size); [exact INB | exact PAY3 | exact PLEN | lia | lia |].
intros a Ha (b & Hb & Hr). apply (HPX5 a Ha). right; right. exists b. split; [apply in_or_app; left; exact Hb | exact Hr]. }
assert (GA5 : GA_jo m5).
{ eapply GA_jo_pointwise; [exact GA4 | exact LHG5 |]. intros a Ha. apply (HPX5 a); [lia|]. right; left.
split; [cbn [hl_client_static A4H]; unfold a4_client_static; lia|]. unfold xlocA, a4_volatile, QlKV.Mq4.LOCCELL_A, A_TP. lia. }
clear PAY3 GA4 GA1 LOC LCK ERR4 STRB SB UNS4 HPX4 AG4 HP4 MU4 WM4 MI4.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI5. change (hl_segs A4L) with asegs in MI5.
pose proof (wmono_refl asegs m5) as WM. pose proof (munch_refl [(lo, sp1 + 32); (Fr, Fr + 248); (sh, sh + 32)] m5) as MU.
unfold QlKV.Mq4.LOCCELL_A, QlKV.Mq4.LOCALE_LOCK_A, QlKV.Mq4.GLOBLOC_A, A_TP in LOC5, LCK5.
stash PAY5.
change (hl_segs A4H) with asegs in *.
reenterA asegs A4L HIx asegs_wx HP5. change (hl_segs A4H) with asegs.
step.
step. step. rewrite short_flag0A by lia. step. if_true.
step. step. step. step.
do 3 stepz.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m6 end.
lazymatch goal with H : mem_inv asegs m6 |- _ => rename H into MI6 end.
lazymatch goal with H : munch _ m5 m6 |- _ => rename H into MU6 end.
lazymatch goal with H : wmono asegs m5 m6 |- _ => rename H into WM6 end.
assert (INCL5 : incl LB (RBS ++ LK ++ LB)) by (intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb).
destruct (OWN A5 (RBS ++ LK ++ LB) B5 m5 m6 md5 _ HP5 INCL5 MU6 WM6 MI6 WOK) as (HP6 & HPX6 & AG6).
assert (PX6 : heap_presx A4H (xtgt_A (bv_unsigned sp0)) (LB ++ LM) (sp1 + 32) m m6).
{ eapply heap_presx_trans; [| exact HPX6]. eapply heap_presx_trans; [exact PX4|].
eapply heap_presx_weaken; [exact HPX5 | lia | |].
- intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; exact Hb | right; apply in_or_app; left; exact Hb].
- intros a [Xa | Xa]; [left; exact Xa | right; left; unfold T_LOCCELL_A; exact Xa]. }
unstash PAY5.
assert (PAY6 : bytes_at asegs m6 data payload).
{ eapply (window_bytesG (RBS ++ LK ++ LB) data size); [destruct INB as [Z0|I1]; [left; exact Z0 | right; apply INCL5; exact I1] | exact PAY5 | exact PLEN | lia | lia |].
intros a Ha (b & Hb & Hr). apply (AG6 a Ha). exists b. split; [apply in_or_app; left; exact Hb | exact Hr]. }
pose proof (bytes_at_skipn asegs m6 data payload k1 PAY6 ltac:(lia)) as WIN6.
assert (GA6 : GA_jo m6) by (exact (GAO m5 m6 _ GA5 MU6 WM6 WOK)).

assert (FJ : exists fj, rw_cells asegs m6 Fr [CB 248 fj]).
{ lazymatch type of STR3 with rw_cells _ _ _ ?c3 => lazymatch type of B2 with rw_cells _ _ _ ?c4 =>
assert (X1 : rw_cells asegs m6 (Fr + 32) (c3 ++ c4)) by (apply (proj2 (rw_cells_app asegs m6 (Fr + 32) c3 c4)); split; [exact STR3 | cbn [cells_size csize Nat.add]; replace (Fr + 32 + Z.of_nat 24) with (Fr + 56) by lia; exact B2]) end end.
lazymatch type of G0 with rw_cells _ _ _ ?c2 => lazymatch type of X1 with rw_cells _ _ _ ?c34 =>
assert (X2 : rw_cells asegs m6 (Fr + 24) (c2 ++ c34)) by (apply (proj2 (rw_cells_app asegs m6 (Fr + 24) c2 c34)); split; [exact G0 | cbn [cells_size csize Nat.add]; replace (Fr + 24 + Z.of_nat 8) with (Fr + 32) by lia; exact X1]) end end.
lazymatch type of HDR with rw_cells _ _ _ ?c1 => lazymatch type of X2 with rw_cells _ _ _ ?c234 =>
assert (X3 : rw_cells asegs m6 Fr (c1 ++ c234)) by (apply (proj2 (rw_cells_app asegs m6 Fr c1 c234)); split; [exact HDR | cbn [cells_size csize Nat.add]; change (Z.of_nat 24) with 24; exact X2]) end end.
lazymatch type of X3 with rw_cells _ _ _ ?cs => change (rw_cells asegs m6 Fr ([] ++ cs ++ [])) in X3 end.
apply rw_cells_merge in X3. cbn [app] in X3.
lazymatch type of X3 with rw_cells _ _ _ [CB ?n ?b] => exists b; let v := eval vm_compute in n in change n with v in X3 end. exact X3. }
destruct FJ as [fj FJ].
assert (VM6 : model_vm_only (cfg_model md) (cfg_model md5)) by (eapply model_vm_only_trans; [exact VM1 | exact VM5]).
lazymatch goal with H : stk asegs m6 lo sp1 |- _ => rename H into ST6 end.
assert (HI6 : HINVA sp0 sp1 lo Fr LB LM m md F data size SHB0 m6 md5 F5 fc5 (data + k1) (size - k1) (skipn (Z.to_nat k1) payload)).
{ unfold HINVA. split; [exact PX6|]. split; [exact VM6|]. split; [exact FS5|]. split; [exact (FRM5 FRM)|].
split; [exact LOC5|]. split; [exact LCK5|]. split; [exact GA6|]. split; [exact ST6|].
split; [eexists; exact SL|]. split; [exact FD3|]. split; [exists fj; exact FJ|]. split; [exact FSH1|]. split; [reflexivity|].
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
End Mq1.
From Stdlib Require Permutation.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qtgi QRUw QkMG QG8z Qdyh Qiiq Q4v2 Q1Y6 QrQv QEUF QW22 QdGy QYZ0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z Qdyh.Mq3 Qdyh.Mq4.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq4 Qiiq.Mq0 QsKa.Mq6 Q4v2.Mq0 Q1Ey Ql4f.Mq1 Q1Y6.Mq2 QsKa.Mq8 QlKV.Mq5 QrQv.Mq2 QEUF QW22.Mq3 QdGy.Mq2 QYZ0.Mq3 QdGy.Mq6 Q63E.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSFinishA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis PUT : put_stmt_A HIx.

Ltac pe_openA STC INV :=
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR); pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk);
destruct INV as [CORE REST];
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR);
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).

Ltac shq_facts HP INq INtk q mxd tk dz j SH SEPc SEPq SEPt :=
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd dz j HP INq ltac:(lia) ltac:(lia)) as SH;
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q (32 * mxd) (4 * dz + j) q (32 * mxd) HP INq ltac:(lia) (in_or_app _ _ _ (or_introl INq))) as (SEPc & SEPq & _);
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q (32 * mxd) (4 * dz + j) tk 72 HP INq ltac:(lia) (in_or_app _ _ _ (or_introl INtk))) as (_ & SEPt & _);
cbn [hl_sb A4L] in SEPc, SEPq, SEPt.

Lemma seg_finish_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(gp t0 t1 t2 a3 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> BOK pf pa ts B (S (Z.to_nat 512 + nB)) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_finish ->

((t_depth ts = 0)%nat ->
forall x1' a0' a1' a2' a4' s5' s7' s11' t4' t6',
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_OUT x1' gp t0 t1 t2 a0' a1' a2' a3 a4' a5 a6 a7 s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F fc m)) ->

(forall m' md' A' B' pj' dp lp gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
t_depth ts = S dp -> nth_error (t_levels ts) dp = Some lp -> (tl_st lp = ST_array_add \/ tl_st lp = ST_ovadd) ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(TST dp (lupd (t_levels ts) (S dp) (TL ST_eatws ST_start 0 None [] 0 [])) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (tl_cur l) (tl_cs l) (tl_cbs l)) cb nb pj' sv errv ->
pj_obj pj' = Z_to_bv 64 (tl_cur l) ->
PBOK m' (TST dp (lupd (t_levels ts) (S dp) (TL ST_eatws ST_start 0 None [] 0 [])) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (tl_cur l) (tl_cs l) (tl_cbs l)) kP ->
BOK pf pa (TST dp (lupd (t_levels ts) (S dp) (TL ST_eatws ST_start 0 None [] 0 [])) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (tl_cur l) (tl_cs l) (tl_cbs l)) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_REDO (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5'
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_finish) (t_co ts) gp t0 t1 t2
(Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l))
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3 (Z_to_bv 64 APE_JTAB) a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC BSL INV PBK BK Hl Hst Kout Kredo. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA, pe_msO in *.
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
unfold APE_BREAK, APE_REDO, APE_OUT, APE_ERRMEM, APE_ERRST, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
destruct (lvl_mode_finish _ _ _ SS26 ltac:(rewrite <- Hst; exact Hmode)) as (Ec0 & Ehn0 & Ess). subst c0 hn0.
cbn [name_ok] in NM0. destruct NM0 as [Hn0 Hnbs0].
assert (Eobjbs : objbs = []).
{ unfold cur_st in OBJ. cbn [t_levels t_depth t_objbs ts0] in OBJ. rewrite Hl, Hst in OBJ. exact OBJ. }
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 2 SHQ2 SEPQ2c SEPQ2q SEPQ2t.
replace (q / 8 + 4 * (Z.of_nat depth) + 2 + A_SB) with (bse / 8 + 2147450882) in SHQ2 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 2) = bse / 8 + 2147450882) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ2c, SEPQ2q, SEPQ2t. clear EQx.
stash Himg_t. stash Himg_q. clear PB REST TSK OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SEPQ2c SEPQ2q SEPQ2t Hdtq.
reenterA asegs A4L HIx asegs_wx HP. rewrite Hst. unfold ST_finish. cbn [pe_jtA].
replace (q + 32 * Z.of_nat depth) with bse by lia.
step.
step.
destruct depth as [|dp].
{
if_false. step.
evt_done5. subst bse. eapply (Kout eq_refl). }
if_truex.
step.
asan_chkA.
step.
step.

pose proof (PE_WIN_open HIx GA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv l INV0 Hl Hn0 Hnbs0 Eobjbs) as WIN0.
set (lw0 := TL (tl_st l) (tl_ss l) (tl_cur l) None [] 0 []) in *. set (tw0 := ts_lvl ts0 lw0) in *.
eapply (pe_get_w HIx GA GA_pres (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B tw0 (tl_cur l) (tl_cs l) (tl_cbs l) cb nb pj sv errv);
[exact STC | exact WIN0 |].
intros mg1 a1' a2' a3' WIN1 PBT1.
cbn [pf_spf] in *. unfold A_TP in *.
clear TOK SLOTS SHT SHQ SHQ4 SHQ2 Ld MU WM MI HP INtk INq WIN0 Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk.

pose proof WIN1 as (CORE1 & BASE1 & _). destruct CORE1 as (_ & _ & _ & _ & TOK & _ & _ & TSK1 & FR1). pose proof (proj1 BASE1) as HP. clear BASE1.
unfold tw0, ts_lvl, ts0 in TOK. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR1 as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw0 (tl_cbs l)))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw0 (tl_cbs l)))) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t1.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q1.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs mg1) as WM.
assert (Hlw0 : nth_error (t_levels tw0) (S dp) = Some lw0) by (unfold tw0, ts_lvl, ts0; cbn [t_levels t_depth]; apply nth_error_lupd_eq; apply nth_error_Some; rewrite Hl; discriminate).
pose proof (TSK1 (S dp) lw0 Hlw0) as Ld. rewrite <- Hbse in Ld. unfold srec_cells, lw0 in Ld. cbn [tl_st tl_ss tl_cur tl_name] in Ld.
shq_facts HP INq INtk q mxd tk (Z.of_nat (S dp)) 0 SHQ0 SEPQ0c SEPQ0q SEPQ0t.
replace (q / 8 + 4 * (Z.of_nat (S dp)) + 0 + A_SB) with (bse / 8 + 2147450880) in SHQ0 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat (S dp)) + 0) = bse / 8 + 2147450880) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ0c, SEPQ0q, SEPQ0t. clear EQx.
shq_facts HP INq INtk q mxd tk (Z.of_nat (S dp)) 2 SHQ2 SEPQ2c SEPQ2q SEPQ2t.
replace (q / 8 + 4 * (Z.of_nat (S dp)) + 2 + A_SB) with (bse / 8 + 2147450882) in SHQ2 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat (S dp)) + 2) = bse / 8 + 2147450882) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ2c, SEPQ2q, SEPQ2t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 2 HP INtk ltac:(lia)) as SHT2.
replace (tk / 8 + 2 + A_SB) with (tk / 8 + 2147450882) in SHT2 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT2c & SEPT2q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT2t & _).
cbn [hl_sb A4L] in SEPT2c, SEPT2q, SEPT2t. assert (EQx : tk / 8 + A_SB + 2 = tk / 8 + 2147450882) by (unfold A_SB; lia). rewrite EQx in SEPT2c, SEPT2q, SEPT2t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 7 HP INtk ltac:(lia)) as SHT7.
replace (tk / 8 + 7 + A_SB) with (tk / 8 + 2147450887) in SHT7 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 7 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT7c & SEPT7q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 7 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT7t & _).
cbn [hl_sb A4L] in SEPT7c, SEPT7q, SEPT7t. assert (EQx : tk / 8 + A_SB + 7 = tk / 8 + 2147450887) by (unfold A_SB; lia). rewrite EQx in SEPT7c, SEPT7q, SEPT7t. clear EQx.
pose proof (munch_refl [(bse, bse + 32); (spf, spf + 312)] mg1) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_Q0_L : csep (bse / 8 + 2147450880) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPQ0q HbseR; lia).
assert (cs_Q2_L : csep (bse / 8 + 2147450882) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPQ2q HbseR; lia).
clear Hdtq SEPQ0q SEPQ0t SEPQ2q SEPQ2t SEPT2q SEPT2t SEPT7q SEPT7t.
stash Himg_t1. stash Himg_q1. stash WIN1. stash TSK1. stash FR1.
lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
asan_rechkM 1.
step.
asan_rechkA.
clear SHT7 SHT2.
step.
norm_sx32.
step.
step.
rewrite (unsigned_lit (Z.of_nat (S dp))) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step.
replace (q + Z.of_nat (S dp) * 32) with bse by lia.
asan_chkA.
stepz.
step.
asan_chkA.
step. step.
stepz.
asan_chkA.
step.
step.

set (lw1 := TL ST_eatws ST_start (tl_cur l) None [] 0 []).
set (pj1 := PEJA (pj_0 pj) (pj_8 pj) (pj_16 pj) (Z_to_bv 64 (tl_cur l)) (pj_288 pj) (pj_304 pj) (pj_gap pj) (pj_fhd pj) (pj_f1 pj) (pj_f2 pj)).
unstash WIN1. unstash TSK1. unstash FR1.
assert (Hlen0 : length (t_levels tw0) = Z.to_nat mxd) by (unfold tw0, ts_lvl, ts0; cbn [t_levels t_depth]; rewrite lupd_length; exact LEN32).
assert (PBK0 : PBOKat m tw0 (co + kP)) by (exact (PBOKat_same m ts0 tw0 _ eq_refl eq_refl PBK)).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ mg1 mc, WMc : wmono asegs mg1 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _, SLc : rw_cells asegs mc spf _ |- _ =>
evt_done5;
assert (TSKc : tstack asegs mc q (lupd (t_levels tw0) (t_depth tw0) lw1))
by (rewrite Hbse in MUc, Lc; eapply (tstack_put asegs mg1 mc q (t_levels tw0) (S dp) lw1 [(spf, spf + 312)]);
[exact TSK1 | rewrite Hlen0; lia | exact MUc | exact WMc
| intros j Hj Hne; rewrite Hlen0 in Hj; cbn [disjoint_from fst snd]; split; [left; unfold alloc_ceiling in *; lia | exact I] | exact Lc]);
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj1 sv)
by (eapply (pe_frameA_slotw HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) _ LM FRS B A mg1 mc md lo [(bse, bse + 32)] cb nb pj pj1 sv);
[ exact STC | exact HP
| apply Forall_cons; [exists q, (32 * mxd); cbn [fst snd]; split; [apply in_or_app; left; exact INq | lia] | apply Forall_nil]
| exact FR1 | eapply munch_weaken; [| exact MUc]; intros x Hx; cbn [outside] in *; tauto | exact WMc | exact SLc
| reflexivity | reflexivity | reflexivity | reflexivity ]);
destruct (PE_WIN_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mg1 mc md A B tw0 (tl_cur l) (tl_cs l) (tl_cbs l) 2
cb nb pj sv errv [(bse, bse + 32); (spf, spf + 312)] lw1 cb nb pj1 STC WIN1 MUc WMc MIc
ltac:(apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_cons; [left; right; left; cbn [fst snd pf_spf pa_sp0]; lia | apply Forall_nil]])
TOKc TSKc FRc ltac:(unfold lvl_bare, lw1, ST_eatws, ST_start; cbn [tl_st tl_ss tl_cs tl_cbs tl_name tl_nbs]; repeat split; try reflexivity; lia)) as [WIN1' PBT1']
end end.
set (tw1 := ts_lvl tw0 lw1) in *.
eapply (pe_put_w HIx GA GA_pres PUT (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md A B tw1 (tl_cur l) (tl_cs l) (tl_cbs l) cb nb pj1 sv errv T (co + kP) ts0 _);
[exact STC | exact WIN1' | exact (PBT1' _ (PBT1 _ PBK0)) | exact BK | rewrite unsigned_lit by lia; reflexivity |].
intros mp2 md2 A2 B2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 WIN2 PBK2 BK2 FS2 FRM2.
cbn [pf_spf] in *. unfold A_TP in *.
clear TOK SLOTS Ld SHQ0 SHQ2 MU WM MI HP INtk INq Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk WIN1 WIN1' PBT1 PBT1' TSK1 FR1 PBK0 BK SEPQ0c SEPQ2c SEPT2c SEPT7c cs_tk_L cs_L_tk cs_Q0_L cs_Q2_L TSKc FRc.

pose proof WIN2 as (COREx & BASEx & _). destruct COREx as (_ & _ & _ & _ & TOK & _ & _ & TSK2 & FR2). pose proof (proj1 BASEx) as HP. clear BASEx.
unfold tw1, tw0, ts_lvl, ts0 in TOK. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR2 as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc pj_0 pj_8 pj_16 pj_obj pj_288 pj_304 pj1] in SLOTS.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw1 (tl_cbs l)))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw1 (tl_cbs l)))) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q2.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs mp2) as WM.
assert (Hlw1 : nth_error (t_levels tw1) (S dp) = Some lw1) by (unfold tw1, tw0, ts_lvl, ts0; cbn [t_levels t_depth]; apply nth_error_lupd_eq; rewrite ?lupd_length; apply nth_error_Some; rewrite Hl; discriminate).
pose proof (TSK2 (S dp) lw1 Hlw1) as Ld. rewrite <- Hbse in Ld. unfold srec_cells, lw1 in Ld. cbn [tl_st tl_ss tl_cur tl_name] in Ld.
shq_facts HP INq INtk q mxd tk (Z.of_nat (S dp)) 2 SHQ2 SEPQ2c SEPQ2q SEPQ2t.
replace (q / 8 + 4 * (Z.of_nat (S dp)) + 2 + A_SB) with (bse / 8 + 2147450882) in SHQ2 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat (S dp)) + 2) = bse / 8 + 2147450882) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ2c, SEPQ2q, SEPQ2t. clear EQx.
shq_facts HP INq INtk q mxd tk (Z.of_nat (S dp)) 3 SHQ3 SEPQ3c SEPQ3q SEPQ3t.
replace (q / 8 + 4 * (Z.of_nat (S dp)) + 3 + A_SB) with (bse / 8 + 2147450883) in SHQ3 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat (S dp)) + 3) = bse / 8 + 2147450883) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ3c, SEPQ3q, SEPQ3t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 7 HP INtk ltac:(lia)) as SHT7.
replace (tk / 8 + 7 + A_SB) with (tk / 8 + 2147450887) in SHT7 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 7 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT7c & SEPT7q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 7 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT7t & _).
cbn [hl_sb A4L] in SEPT7c, SEPT7q, SEPT7t. assert (EQx : tk / 8 + A_SB + 7 = tk / 8 + 2147450887) by (unfold A_SB; lia). rewrite EQx in SEPT7c, SEPT7q, SEPT7t. clear EQx.
pose proof (munch_refl [(bse, bse + 32)] mp2) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_Q3_L : csep (bse / 8 + 2147450883) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPQ3q HbseR; lia).
clear Hdtq SEPQ2q SEPQ2t SEPQ3q SEPQ3t SEPT7q SEPT7t.
stash Himg_t2. stash Himg_q2. stash WIN2. stash TSK2. stash FR2.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_rechkA.
clear SHT7.
step. step.
replace (q + Z.of_nat (S dp) * 32) with bse by lia.
step.
asan_chkA.
stepz.
step.
asan_chkA.
step.
step.

set (lw2 := TL ST_eatws ST_start 0 None [] 0 []).
unstash WIN2. unstash TSK2. unstash FR2.
assert (Hlen1 : length (t_levels tw1) = Z.to_nat mxd) by (unfold tw1, tw0, ts_lvl, ts0; cbn [t_levels t_depth]; rewrite !lupd_length; exact LEN32).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ mp2 mc, WMc : wmono asegs mp2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5;
assert (INqL : Forall (fun iv => exists a n, In (a, n) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw1 (tl_cbs l)) ++ LM) /\ a <= fst iv /\ snd iv <= a + n) [(bse, bse + 32)])
by (apply Forall_cons; [exists q, (32 * mxd); cbn [fst snd]; split; [apply in_or_app; left; exact INq | lia] | apply Forall_nil]);
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj1 sv)
by (eapply (pe_frameA_blkwriteG HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) _ LM FRS B2 A2 mp2 mc md2 lo [(bse, bse + 32)] cb nb pj1 sv); [exact STC | exact HP | exact INqL | exact FR2 | exact MUc | exact WMc]);
assert (TSKc : tstack asegs mc q (lupd (t_levels tw1) (t_depth tw1) lw2))
by (rewrite Hbse in MUc, Lc; eapply (tstack_put asegs mp2 mc q (t_levels tw1) (S dp) lw2 []);
[exact TSK2 | rewrite Hlen1; lia | exact MUc | exact WMc | intros; exact I | exact Lc]);
destruct (PE_WIN_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mp2 mc md2 A2 B2 tw1 (tl_cur l) (tl_cs l) (tl_cbs l) 1
cb nb pj1 sv errv [(bse, bse + 32)] lw2 cb nb pj1 STC WIN2 MUc WMc MIc
ltac:(apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil])
TOKc TSKc FRc ltac:(unfold lvl_bare, lw2, ST_eatws, ST_start; cbn [tl_st tl_ss tl_cs tl_cbs tl_name tl_nbs]; repeat split; try reflexivity; lia)) as [WIN2' PBT2']
end end.
set (tw2 := ts_lvl tw1 lw2) in *.
eapply (pe_free_null_w HIx GA GA_pres (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md2 A2 B2 tw2 (tl_cur l) (tl_cs l) (tl_cbs l) 1 cb nb pj1 sv errv T (co + kP) ts0 nB);
[exact STC | exact BSL | exact WIN2' | exact (PBT2' _ PBK2) | exact BK2 | rewrite unsigned_lit by lia; reflexivity |].
intros mf3 md3 A3 B3 r' v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 WIN3 PBK3 BK3.
cbn [pf_spf] in *. unfold A_TP in *.
clear TOK SLOTS Ld SHQ2 SHQ3 MU WM MI HP INtk INq Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk WIN2 WIN2' PBT2' TSK2 FR2 PBK2 BK2 SEPQ2c SEPQ3c SEPT7c cs_tk_L cs_L_tk cs_Q3_L TSKc FRc INqL.

pose proof WIN3 as (COREx & BASEx & _). destruct COREx as (_ & _ & _ & _ & TOK & _ & _ & TSK3 & FR3). pose proof (proj1 BASEx) as HP. clear BASEx.
unfold tw2, tw1, tw0, ts_lvl, ts0 in TOK. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR3 as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc pj_0 pj_8 pj_16 pj_obj pj_288 pj_304 pj1] in SLOTS.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw2 (tl_cbs l)))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw2 (tl_cbs l)))) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t3.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q3.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs mf3) as WM.
assert (Hlw2 : nth_error (t_levels tw2) (S dp) = Some lw2) by (unfold tw2, tw1, tw0, ts_lvl, ts0; cbn [t_levels t_depth]; apply nth_error_lupd_eq; rewrite ?lupd_length; apply nth_error_Some; rewrite Hl; discriminate).
pose proof (TSK3 (S dp) lw2 Hlw2) as Ld. rewrite <- Hbse in Ld. unfold srec_cells, lw2 in Ld. cbn [tl_st tl_ss tl_cur tl_name] in Ld.
shq_facts HP INq INtk q mxd tk (Z.of_nat (S dp)) 3 SHQ3 SEPQ3c SEPQ3q SEPQ3t.
replace (q / 8 + 4 * (Z.of_nat (S dp)) + 3 + A_SB) with (bse / 8 + 2147450883) in SHQ3 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat (S dp)) + 3) = bse / 8 + 2147450883) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ3c, SEPQ3q, SEPQ3t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 7 HP INtk ltac:(lia)) as SHT7.
replace (tk / 8 + 7 + A_SB) with (tk / 8 + 2147450887) in SHT7 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 7 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT7c & SEPT7q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 7 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT7t & _).
cbn [hl_sb A4L] in SEPT7c, SEPT7q, SEPT7t. assert (EQx : tk / 8 + A_SB + 7 = tk / 8 + 2147450887) by (unfold A_SB; lia). rewrite EQx in SEPT7c, SEPT7q, SEPT7t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 2 HP INtk ltac:(lia)) as SHT2.
replace (tk / 8 + 2 + A_SB) with (tk / 8 + 2147450882) in SHT2 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT2c & SEPT2q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT2t & _).
cbn [hl_sb A4L] in SEPT2c, SEPT2q, SEPT2t. assert (EQx : tk / 8 + A_SB + 2 = tk / 8 + 2147450882) by (unfold A_SB; lia). rewrite EQx in SEPT2c, SEPT2q, SEPT2t. clear EQx.
pose proof (munch_refl [(bse, bse + 32)] mf3) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_T2_L : csep (tk / 8 + 2147450882) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPT2q HbseR; lia).
clear Hdtq SEPQ3q SEPQ3t SEPT7q SEPT7t SEPT2q SEPT2t.
stash Himg_t3. stash Himg_q3. stash WIN3. stash TSK3. stash FR3.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_rechkA.
clear SHT7.
step. step.
replace (q + Z.of_nat (S dp) * 32) with bse by lia.
step. step. step.
sh_normO.
asan_rechkM 5.
clear SHQ3.
stepz.
step.
asan_rechkA.

unstash WIN3. unstash TSK3. unstash FR3.
assert (Hlen2 : length (t_levels tw2) = Z.to_nat mxd) by (unfold tw2, tw1, tw0, ts_lvl, ts0; cbn [t_levels t_depth]; rewrite !lupd_length; exact LEN32).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ mf3 mc, WMc : wmono asegs mf3 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
assert (INqL : Forall (fun iv => exists a n, In (a, n) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw2 (tl_cbs l)) ++ LM) /\ a <= fst iv /\ snd iv <= a + n) [(bse, bse + 32)])
by (apply Forall_cons; [exists q, (32 * mxd); cbn [fst snd]; split; [apply in_or_app; left; exact INq | lia] | apply Forall_nil]);
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj1 sv)
by (eapply (pe_frameA_blkwriteG HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) _ LM FRS B3 A3 mf3 mc md3 lo [(bse, bse + 32)] cb nb pj1 sv); [exact STC | exact HP | exact INqL | exact FR3 | exact MUc | exact WMc]);
assert (TSKc : tstack asegs mc q (lupd (t_levels tw2) (t_depth tw2) lw2))
by (pose proof MUc as MUc'; pose proof Lc as Lc'; rewrite Hbse in MUc', Lc'; eapply (tstack_put asegs mf3 mc q (t_levels tw2) (S dp) lw2 []);
[exact TSK3 | rewrite Hlen2; lia | exact MUc' | exact WMc | intros; exact I | exact Lc']);
destruct (PE_WIN_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mf3 mc md3 A3 B3 tw2 (tl_cur l) (tl_cs l) (tl_cbs l) 1
cb nb pj1 sv errv [(bse, bse + 32)] lw2 cb nb pj1 STC WIN3 MUc WMc MIc
ltac:(apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil])
TOKc TSKc FRc ltac:(unfold lvl_bare, lw2, ST_eatws, ST_start; cbn [tl_st tl_ss tl_cs tl_cbs tl_name tl_nbs]; repeat split; try reflexivity; lia)) as [WIN3' PBT3'];
clear MUc WMc; pose proof (munch_refl [(tk, tk + 72)] mc) as MUt; pose proof (wmono_refl asegs mc) as WMt
end end.
set (tw3 := ts_lvl tw2 lw2) in *.
stash WIN3'. clear WIN3 TSK3 FR3 TSKc FRc.
step.
norm_sx32.
step.
replace (Z.of_nat (S dp) + -1) with (Z.of_nat dp) by lia.
stepz.
step.

unstash WIN3'.
assert (Hdp : (dp < length levels)%nat) by lia.
destruct (nth_error levels dp) as [lp|] eqn:Hlp; [| apply nth_error_None in Hlp; lia].
assert (STp : tl_st lp = ST_array_add \/ tl_st lp = ST_ovadd).
{ pose proof (LV dp lp Hlp) as (_ & _ & _ & Mp). replace (dp <? S dp)%nat with true in Mp by (symmetry; apply Nat.ltb_lt; lia).
destruct Mp as [(E & _) | (E & _)]; [left | right]; exact E. }
pose proof (BOK_weak _ _ _ _ _ (BOK_pop (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts0 B3 nB l dp BK3 eq_refl Hl Hnbs0 Eobjbs)) as BUDf.
pose proof (BOK_pop (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts0 B3 nB l dp BK3 eq_refl Hl Hnbs0 Eobjbs) as BKf.
unfold ts0 in BUDf, BKf. cbn [t_levels t_depth t_co t_pb t_pbs t_x] in BUDf, BKf.
assert (Hrl : nth_error (t_levels tw3) (S dp) = Some (TL ST_eatws ST_start 0 None [] 0 []))
by (unfold tw3, tw2, tw1, tw0, ts_lvl, ts0; cbn [t_levels t_depth]; apply nth_error_lupd_eq; rewrite !lupd_length; apply nth_error_Some; rewrite Hl; discriminate).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mcF _) =>
lazymatch goal with MUc : munch _ ?mb mcF, WMc : wmono asegs ?mb mcF, MIc : mem_inv asegs mcF, TOKc : rw_cells asegs mcF tk _ |- _ =>
evt_done5;
destruct (PE_WIN_close_pop HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mb mcF md3 A3 B3 tw3 (tl_cur l) (tl_cs l) (tl_cbs l) cb nb pj1 sv errv dp
STC WIN3' eq_refl Hrl MUc WMc MIc TOKc
ltac:(unfold tw3, tw2, tw1, tw0, ts_lvl, ts0; cbn [t_levels t_depth t_co t_pb t_pbs t_x]; rewrite !lupd_lupdS; exact BUDf)) as [INVf PBTf];
pose proof (PBTf _ (PBT3' _ PBK3)) as PBKf;
unfold tw3, tw2, tw1, tw0, ts_lvl, ts0 in INVf, PBKf; cbn [t_levels t_depth t_co t_pb t_pbs t_x] in INVf, PBKf; rewrite !lupd_lupdS in INVf, PBKf;
eapply (Kredo mcF md3 A3 B3 pj1 dp lp); [reflexivity | exact Hlp | exact STp | exact INVf | reflexivity | exact PBKf | exact BKf | exact FS2 | exact FRM2]
end end.
Qed.
End PeSFinishA.
End RC__1.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QRUw.Mq2 QmZZ. Import QPZI.Mq4. Import QkMG. Import QG8z Qdyh.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq4 Qiiq.Mq0 QsKa.Mq6 Q4v2.Mq0 QlKV.Mq5 QlKV.Mq7 Q1Ey Ql4f.Mq1 QsKa.Mq8 QrQv.Mq2 QEUF QdGy.Mq6 Q63E.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSNameCallA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.

Lemma pe_free_name_n :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP v2 ra2 p n : Z)
(ra gp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_NWIN HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts [(p, n)] cb nb pj sv errv ->
PBOKat m ts kP -> 512 <= bB B ->
pe_s0 sv = Z_to_bv 64 v2 -> pe_ra sv = Z_to_bv 64 ra2 ->
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64 ->
uw_ok A4L (hl_free A4H) ra (UWfp ra2 v2) ->
bv_unsigned ra mod 2 = 0 ->
(forall m2 md2 A2 (r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word),
PE_NWIN HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 (charge B 512 0) ts [] cb nb pj sv errv ->
PBOKat m2 ts kP ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 (Z_to_bv 64 (pa_sp0 pa)) s1 r w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F (ret_pc ra) fc None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x632c4) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC WIN PBK COST S0V RAV HV UWK RA K.
pose proof WIN as (CORE & BASE & LVo & CUR & Eobj). pose proof BASE as (HP1 & ST1 & ERR1 & _).
pose proof CORE as (_ & _ & _ & _ & _ & _ & _ & _ & FR1).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
assert (SPF : lo <= pf_spf pf - 4096 /\ pf_spf pf mod 16 = 0 /\ pf_spf pf < hiA_top A4L HIx + 64 /\ 0 <= pf_spf pf < 2^62 /\ 0 <= pa_sp0 pa < 2^63).
{ clear - LOS HT Gle Gspf SP0. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; lia. }
destruct SPF as (SPF1 & SPF2 & SPF3 & SPF4 & SPF5).
set (RB := pe_blocksA pf q LB0 ts) in *.
assert (HPa : HEAPA A4L HIx A ((p, n) :: RB) LM ((pa_F pa, 2) :: FRS) B m md).
{ eapply (heapA_perm A4L HIx); [exact HP1 | | apply Permutation_refl | apply Permutation_refl]. exact (perm_blocks_tsF pf q LB0 ts [(p, n)] Eobj). }
pose proof (pe_uw_at HIx pf pa lo m cb nb pj sv v2 ra2 STC FR1 S0V RAV (proj1 HV) (proj2 HV)) as UWA.
eapply (hiA_free A4L HIx) with (p := p) (u := UWfp ra2 v2) (lo := lo) (errv := errv);
[ exact HPa | right; exists n; left; reflexivity | rewrite unsigned_lit by lia; exact ST1 | exact LO | rewrite unsigned_lit by lia; cbn [hl_stack_A A4L]; exact SPF1
| rewrite unsigned_lit by lia; exact SPF2 | rewrite unsigned_lit by lia; exact SPF3 | exact ERR1 | reflexivity | reflexivity
| split; [rewrite !unsigned_lit by lia; apply (uw_at_pre0 _ _ _ _ _ _ UWA); lia | exact UWK] | exact COST
| cbn [uw_cost]; destruct (p =? 0); exact (proj2 (heapA_budget A4L HIx _ _ _ _ _ _ _ HP1)) | ].
intros ms2 m2 md2 A2 r RS2 VM2 ST2 HPR2 ERR2 HP2.
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & ->).
cbn [hl_segs hl_tp hla_base A4L A4H] in *. rewrite ?(unsigned_lit (pf_spf pf)) in ST2 by lia. rewrite ?(unsigned_lit (pf_spf pf)) in HPR2 by lia.
rewrite lb_remove_head in HPR2, HP2.
assert (Ecost : (if p =? 0 then 0 else uw_cost (UWfp ra2 v2)) = 0) by (destruct (p =? 0); reflexivity). rewrite Ecost in HP2.
assert (WIN2 : PE_NWIN HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 (charge B 512 0) ts [] cb nb pj sv errv).
{ eapply (PE_NWIN_callG HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B (charge B 512 0) ts [(p, n)] [] cb nb pj sv errv errv);
[exact STC | exact WIN | exact VM2 | exact HPR2 | | exact ST2 | exact ERR2].
eapply (heapA_perm A4L HIx); [exact HP2 | | apply Permutation_refl | apply Permutation_refl].
apply Permutation_sym. exact (perm_blocks_tsF pf q LB0 ts [] Eobj). }
eapply (K m2 md2 A2 r); [exact WIN2|].
assert (AG : agree_on asegs RB m m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPR2 | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
eapply PBOKat_agree; [exact PBK | exact AG |]. unfold RB, pe_blocksA, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb.
Qed.
End PeSNameCallA.
End RC__1.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI QSHS Qc5u QAzu Q6vt QZUC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z Qdyh.Mq3 Qdyh.Mq4.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QSHS Ql4f.Mq4 Q1Y6.Mq4 QsKa.Mqh QlKV.Mqf QrQv.Mq4 QEUF.Mq2 QW22.Mq8 QdGy.Mq9 QYZ0.Mq8 QdGy.Mqe Q63E.Mqe.
Import QPZI.Mq4. Import Qc5u QAzu.Mq0 Q6vt QZUC.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSFinishB.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis PUT : put_stmt_A HIx.

Ltac pe_openA STC INV :=
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR); pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk);
destruct INV as [CORE REST];
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR);
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).

Ltac shq_facts HP INq INtk q mxd tk dz j SH SEPc SEPq SEPt :=
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd dz j HP INq ltac:(lia) ltac:(lia)) as SH;
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q (32 * mxd) (4 * dz + j) q (32 * mxd) HP INq ltac:(lia) (in_or_app _ _ _ (or_introl INq))) as (SEPc & SEPq & _);
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q (32 * mxd) (4 * dz + j) tk 72 HP INq ltac:(lia) (in_or_app _ _ _ (or_introl INtk))) as (_ & SEPt & _);
cbn [hl_sb A4L] in SEPc, SEPq, SEPt.

Lemma tstack_recells : forall m q levels i l l', tstack asegs m q levels -> nth_error levels i = Some l -> srec_cells l' = srec_cells l -> tstack asegs m q (lupd levels i l').
Proof.
intros m q levels i l l' TS Hl E j lj Hj. destruct (PeanoNat.Nat.eq_dec j i) as [-> | N].
- rewrite nth_error_lupd_eq in Hj by (apply nth_error_Some; rewrite Hl; discriminate). injection Hj as <-. rewrite E. exact (TS i l Hl).
- rewrite nth_error_lupd_neq in Hj by congruence. exact (TS j lj Hj).
Qed.

Lemma PE_WIN_resetB : forall pf pa q LB0 LM FRS payload me lo m m' md md' A A' B B' ts p s BS cb nb pj sv errv dp,
PE_STATIC_A HIx pf pa lo ->
PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts p s BS 2 cb nb pj sv errv ->
t_depth ts = S dp ->
model_vm_only (cfg_model md) (cfg_model md') ->
HEAPA A4L HIx A' (pe_blocksA pf q LB0 (tsF ts BS)) LM ((pa_F pa, 2) :: FRS) B' m' md' ->
put_pre A4H A4F s m' BS p 1 ->
tstack asegs m' q (lupd (t_levels ts) (S dp) lvl_reset) ->
rw_cells asegs m' (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat (S dp)) q (t_x ts)) ->
stk asegs m' lo (pf_spf pf) ->
heap_pres A4H (LB0 ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m m' ->
rw_cells asegs m' A_ERRNO [C4 errv] ->
agree_on asegs (tstate_blocks ts) m m' ->
PE_WIN HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_lvl ts lvl_reset) p s BS 1 cb nb pj sv errv
/\ (forall b, PBOKat m ts b -> PBOKat m' (ts_lvl ts lvl_reset) b).
Proof.
intros pf pa q LB0 LM FRS payload me lo m m' md md' A A' B B' ts p s BS cb nb pj sv errv dp STC (CORE & BASE & LVo & CUR & Eobj & PP) Ed VM HP2 PP2 TSK2 TOK2 ST2 HPR ERR2 AG.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR).
destruct CUR as (lc & Hlc & BARE). rewrite Ed in Hlc.
assert (EBLK : pe_blocksA pf q LB0 (tsF (ts_lvl ts lvl_reset) BS) = pe_blocksA pf q LB0 (tsF ts BS)).
{ apply (pe_blocksA_tsF_lvl pf q LB0 ts BS lc lvl_reset); [rewrite Ed; exact Hlc|].
destruct BARE as (_ & _ & _ & C4 & _ & C6). unfold lvl_blocks, lvl_reset. cbn [tl_cbs tl_nbs]. rewrite C4, C6. reflexivity. }
assert (FR2 : pe_frameA asegs m' pf pa cb nb pj sv).
{ eapply pe_frameA_pres; [exact HPR | lia | exact GEO | | | exact FR].
- apply in_or_app; right. apply in_or_app; right. change 248 with (fr_size 2 - 8). apply fr_ivs_frame. left; reflexivity.
- apply in_or_app; right. apply in_or_app; right. rewrite <- fr_shadow_len_2. change (shA (pa_F pa)) with (shad A4L (pa_F pa)). apply fr_ivs_shadow. left; reflexivity. }
split.
- split; [| split; [| split; [| split; [| split; [unfold ts_lvl; cbn [t_objbs]; exact Eobj | exact PP2]]]]].
+ unfold PE_CORE_A, ts_lvl; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. rewrite Ed.
split; [rewrite lupd_length; exact LEN32|]. split; [rewrite <- Ed; exact D32|]. split; [exact CO|]. split; [exact CHOFF|]. split; [exact TOK2|].
split; [| split; [exact Hpb | split; [exact TSK2 | exact FR2]]].
eapply pbuf_agree; [exact PB | exact AG |]. unfold tstate_blocks. intros b Hb. apply in_or_app; left. exact Hb.
+ rewrite EBLK. eapply (PE_BASE_A_callG HIx GA GA_pres pf pa LB0 LM FRS payload me lo m m' md md' A A' B B' _ _ errv errv LB0);
[exact STC | exact BASE | exact VM | exact HPR | apply incl_refl | exact HP2 | exact ST2 | exact ERR2].
+ unfold ts_lvl; cbn [t_levels t_depth]. intros i li Hli Hne. rewrite nth_error_lupd_neq in Hli by congruence.
eapply (lvl_cur_agree asegs A4F); [exact (LVo i li Hli Hne) | exact AG |].
intros b Hb. unfold tstate_blocks. apply in_or_app; right. apply in_or_app; right. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map. eapply nth_error_In; exact Hli.
+ exists lvl_reset. unfold ts_lvl; cbn [t_levels t_depth]. rewrite Ed. split; [apply nth_error_lupd_eq; apply nth_error_Some; rewrite Hlc; discriminate|].
unfold lvl_bare, lvl_reset. cbn [tl_st tl_ss tl_cs tl_cbs tl_name tl_nbs]. repeat split; try reflexivity; lia.
- intros b PBK. eapply PBOKat_same with (ts := ts); [reflexivity | reflexivity |].
eapply PBOKat_agree; [exact PBK | exact AG | unfold tstate_blocks; intros x Hx; apply in_or_app; left; exact Hx].
Qed.

Lemma seg_finish_B :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> BOK pf pa ts B (S (Z.to_nat 512 + nB)) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_finish ->

((t_depth ts = 0)%nat ->
forall gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6',
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_OUT gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F fc m)) ->

(forall m' md' A' B' pj' dp lp gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
t_depth ts = S dp -> nth_error (t_levels ts) dp = Some lp -> (tl_st lp = ST_array_add \/ tl_st lp = ST_ovadd) ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(TST dp (lupd (t_levels ts) (S dp) (TL ST_eatws ST_start 0 None [] 0 [])) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (tl_cur l) (tl_cs l) (tl_cbs l)) cb nb pj' sv errv ->
pj_obj pj' = Z_to_bv 64 (tl_cur l) ->
PBOK m' (TST dp (lupd (t_levels ts) (S dp) (TL ST_eatws ST_start 0 None [] 0 [])) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (tl_cur l) (tl_cs l) (tl_cbs l)) kP ->
BOK pf pa (TST dp (lupd (t_levels ts) (S dp) (TL ST_eatws ST_start 0 None [] 0 [])) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (tl_cur l) (tl_cs l) (tl_cbs l)) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_REDO (t_co ts) gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_finish) (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 0) (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5 (Z_to_bv 64 APE_JTAB) a7 s3 (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK BK Hl Hst Kout Kredo. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA, pe_msO in *.
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
unfold APE_BREAK, APE_REDO, APE_OUT, APE_ERRMEM, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
destruct (lvl_mode_finish _ _ _ SS26 ltac:(rewrite <- Hst; exact Hmode)) as (Ec0 & Ehn0 & Ess). subst c0 hn0.
cbn [name_ok] in NM0. destruct NM0 as [Hn0 Hnbs0].
assert (Eobjbs : objbs = []).
{ unfold cur_st in OBJ. cbn [t_levels t_depth t_objbs ts0] in OBJ. rewrite Hl, Hst in OBJ. exact OBJ. }
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 2 SHQ2 SEPQ2c SEPQ2q SEPQ2t.
replace (q / 8 + 4 * (Z.of_nat depth) + 2 + A_SB) with (bse / 8 + 2147450882) in SHQ2 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 2) = bse / 8 + 2147450882) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ2c, SEPQ2q, SEPQ2t. clear EQx.
stash Himg_t. stash Himg_q. clear PB REST TSK OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SEPQ2c SEPQ2q SEPQ2t Hdtq.
reenterA asegs A4L HIx asegs_wx HP. rewrite Hst. unfold ST_finish. cbn [pe_jtA].
replace (q + 32 * Z.of_nat depth) with bse by lia.
step.
destruct depth as [|dp].
{
if_false. step.
evt_done5. subst bse. eapply (Kout eq_refl). }
if_truex.
step.
asan_chkB.
step.
step.

pose proof (PE_WIN_open HIx GA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv l INV0 Hl Hn0 Hnbs0 Eobjbs) as WIN0.
set (lw0 := TL (tl_st l) (tl_ss l) (tl_cur l) None [] 0 []) in *. set (tw0 := ts_lvl ts0 lw0) in *.
eapply (pe_get_w HIx GA GA_pres (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B tw0 (tl_cur l) (tl_cs l) (tl_cbs l) cb nb pj sv errv);
[exact STC | exact WIN0 |].
intros mg1 a1' a2' a3' WIN1 PBT1.
cbn [pf_spf] in *. unfold A_TP in *.
clear TOK SLOTS SHT SHQ SHQ4 SHQ2 Ld MU WM MI HP INtk INq WIN0 Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk.

pose proof WIN1 as (CORE1 & BASE1 & _). destruct CORE1 as (_ & _ & _ & _ & TOK & _ & _ & TSK1 & FR1). pose proof (proj1 BASE1) as HP. clear BASE1.
unfold tw0, ts_lvl, ts0 in TOK. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR1 as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw0 (tl_cbs l)))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw0 (tl_cbs l)))) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t1.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q1.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs mg1) as WM.
assert (Hlw0 : nth_error (t_levels tw0) (S dp) = Some lw0) by (unfold tw0, ts_lvl, ts0; cbn [t_levels t_depth]; apply nth_error_lupd_eq; apply nth_error_Some; rewrite Hl; discriminate).
pose proof (TSK1 (S dp) lw0 Hlw0) as Ld. rewrite <- Hbse in Ld. unfold srec_cells, lw0 in Ld. cbn [tl_st tl_ss tl_cur tl_name] in Ld.
shq_facts HP INq INtk q mxd tk (Z.of_nat (S dp)) 0 SHQ0 SEPQ0c SEPQ0q SEPQ0t.
replace (q / 8 + 4 * (Z.of_nat (S dp)) + 0 + A_SB) with (bse / 8 + 2147450880) in SHQ0 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat (S dp)) + 0) = bse / 8 + 2147450880) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ0c, SEPQ0q, SEPQ0t. clear EQx.
shq_facts HP INq INtk q mxd tk (Z.of_nat (S dp)) 2 SHQ2 SEPQ2c SEPQ2q SEPQ2t.
replace (q / 8 + 4 * (Z.of_nat (S dp)) + 2 + A_SB) with (bse / 8 + 2147450882) in SHQ2 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat (S dp)) + 2) = bse / 8 + 2147450882) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ2c, SEPQ2q, SEPQ2t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 2 HP INtk ltac:(lia)) as SHT2.
replace (tk / 8 + 2 + A_SB) with (tk / 8 + 2147450882) in SHT2 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT2c & SEPT2q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT2t & _).
cbn [hl_sb A4L] in SEPT2c, SEPT2q, SEPT2t. assert (EQx : tk / 8 + A_SB + 2 = tk / 8 + 2147450882) by (unfold A_SB; lia). rewrite EQx in SEPT2c, SEPT2q, SEPT2t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 7 HP INtk ltac:(lia)) as SHT7.
replace (tk / 8 + 7 + A_SB) with (tk / 8 + 2147450887) in SHT7 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 7 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT7c & SEPT7q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 7 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT7t & _).
cbn [hl_sb A4L] in SEPT7c, SEPT7q, SEPT7t. assert (EQx : tk / 8 + A_SB + 7 = tk / 8 + 2147450887) by (unfold A_SB; lia). rewrite EQx in SEPT7c, SEPT7q, SEPT7t. clear EQx.
pose proof (munch_refl [(spf, spf + 312)] mg1) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_Q0_L : csep (bse / 8 + 2147450880) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPQ0q HbseR; lia).
assert (cs_Q2_L : csep (bse / 8 + 2147450882) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPQ2q HbseR; lia).
clear Hdtq SEPQ0q SEPQ0t SEPQ2q SEPQ2t SEPT2q SEPT2t SEPT7q SEPT7t.
stash Himg_t1. stash Himg_q1. stash WIN1. stash TSK1. stash FR1.
lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

step.
step. rewrite ?sxb_zero, ?zxb_zero. stepz. step. step. if_true.
clear SHT7 SHT2.
step.
norm_sx32.
step.

set (pj1 := PEJA (pj_0 pj) (pj_8 pj) (pj_16 pj) (Z_to_bv 64 (tl_cur l)) (pj_288 pj) (pj_304 pj) (pj_gap pj) (pj_fhd pj) (pj_f1 pj) (pj_f2 pj)).
set (lput := TL (tl_st l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) 0 []).
unstash WIN1. unstash TSK1. unstash FR1.
assert (Hlen0 : length (t_levels tw0) = Z.to_nat mxd) by (unfold tw0, ts_lvl, ts0; cbn [t_levels t_depth]; rewrite lupd_length; exact LEN32).
assert (PBK0 : PBOKat m tw0 (co + kP)) by (exact (PBOKat_same m ts0 tw0 _ eq_refl eq_refl PBK)).
assert (EW : ts_lvl tw0 lw0 = tw0) by (unfold tw0, ts_lvl, ts0; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs]; rewrite lupd_lupdS; reflexivity).
assert (Eobj0 : t_objbs tw0 = []) by (unfold tw0, ts_lvl, ts0; cbn [t_objbs]; exact Eobjbs).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ mg1 mc, WMc : wmono asegs mg1 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, SLc : rw_cells asegs mc spf _ |- _ =>
evt_done5;
assert (HWf : Forall (pe_wtfA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl)) [(spf, spf + 312)]) by (apply Forall_cons; [right; left; cbn [fst snd pf_spf pa_sp0]; lia | apply Forall_nil]);
assert (TSKc : tstack asegs mc q (lupd (t_levels tw0) (t_depth tw0) lw0))
by (unfold tw0, ts_lvl, ts0; cbn [t_levels t_depth]; rewrite lupd_lupdS;
eapply (tstack_wtfA HIx) with (ts := tsF tw0 (tl_cbs l)); [exact STC | exact HP | exact TSK1 | exact Hlen0 | exact MUc | exact WMc | exact HWf]);
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj1 sv)
by (eapply (pe_frameA_slotw HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) _ LM FRS B A mg1 mc md lo [] cb nb pj pj1 sv);
[ exact STC | exact HP | apply Forall_nil | exact FR1 | exact MUc | exact WMc | exact SLc | reflexivity | reflexivity | reflexivity | reflexivity ]);
destruct (PE_WIN_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mg1 mc md A B tw0 (tl_cur l) (tl_cs l) (tl_cbs l) 2
cb nb pj sv errv [(spf, spf + 312)] lw0 cb nb pj1 STC WIN1 MUc WMc MIc
ltac:(apply Forall_cons; [left; right; left; cbn [fst snd pf_spf pa_sp0]; lia | apply Forall_nil])
TOKc TSKc FRc ltac:(unfold lvl_bare, lw0; cbn [tl_st tl_ss tl_cs tl_cbs tl_name tl_nbs]; repeat split; try reflexivity; lia)) as [WIN1' PBT1'];
rewrite EW in WIN1', PBT1'
end end.
pose proof WIN1' as (CORE1' & BASE1' & _ & _ & _ & PP1'). destruct CORE1' as (_ & _ & _ & _ & TOK1' & _ & _ & TSK1' & _). pose proof BASE1' as (HP1' & ST1' & ERR1' & _).
eapply (tok_reset_level_B_cps HIx PUT) with (i := S dp) (l := lput) (levels := lupd (t_levels tw0) (S dp) lput) (P := tstate_blocks tw0) (LB0 := LB0) (LM := LM)
(FRS := (Ff, 2) :: FRS) (B := B) (lo := lo) (errv := errv) (q := q) (r := tk) (pb := pb) (depth := Z.of_nat (S dp)) (mxd := mxd) (fl := fl)
(x := TS isd stpos (Z_to_bv 64 co) err ucs high quote) (rc := 2) (REST := pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 tw0).
{ apply nth_error_lupd_eq. rewrite Hlen0. lia. }
{ lia. }
{ exact (proj1 (proj2 RR)). }
{ rewrite lupd_length. exact Hlen0. }
{ unfold lvl_blocks, lput. cbn [tl_cbs tl_nbs]. rewrite app_nil_r.
eapply (heapA_perm A4L HIx); [exact HP1' | apply perm_blocks_tsF; exact Eobj0 | apply Permutation_refl | apply Permutation_refl]. }
{ reflexivity. }
{ unfold lput. cbn [tl_cs tl_cbs tl_cur]. exact PP1'. }
{ left. split; reflexivity. }
{ eapply (tstack_recells _ q (t_levels tw0) (S dp) lw0 lput); [exact TSK1' | exact Hlw0 | reflexivity]. }
{ exact TOK1'. }
{ rewrite unsigned_lit by lia. exact ST1'. }
{ exact LO. }
{ rewrite unsigned_lit by lia. unfold put_stk_A. clear - LOS. lia. }
{ rewrite unsigned_lit by lia. clear - Gspf. Z.div_mod_to_equations. lia. }
{ rewrite unsigned_lit by lia. clear - HT Gle. lia. }
{ apply heap_pres_refl. }
{ exact ERR1'. }
{
unfold lput. cbn [tl_cs tl_cbs]. replace (put_costA (tl_cs l) 2 (tl_cbs l)) with 0 by (unfold put_costA; destruct (tl_cs l); reflexivity).
pose proof (BOK_ledger_nonneg _ _ _ _ _ BK) as L0. pose proof BK as (H1 & _ & H3 & _). unfold bneed in H1.
pose proof (K_ev_pos (PEF tk oldl newl len lenr sb spf pmd mxd fl)). pose proof (Zle_0_nat (length (tstate_blocks ts0))).
replace (K_ev (PEF tk oldl newl len lenr sb spf pmd mxd fl) * Z.of_nat (S (Z.to_nat 512 + nB))) with (K_ev (PEF tk oldl newl len lenr sb spf pmd mxd fl) * Z.of_nat nB + 513) in H1 by (unfold K_ev; lia).
pose proof (Z.mul_nonneg_nonneg (K_ev (PEF tk oldl newl len lenr sb spf pmd mxd fl)) (Z.of_nat nB) ltac:(lia) ltac:(lia)). unfold K_free, K_exit in *.
cbn [pa_bslack] in H1. clear - H1 H H0 H2 H3 L0 BSL. lia. }
{ rewrite unsigned_lit by lia. reflexivity. }

intros ms2 md2 A2 (m2 & B2 & rv & RS2 & VM2 & OUT2 & TS2 & TOK2 & ST2 & HPR2 & ERR2 & AG2 & BB2 & BD2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
a4l. rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR2 by lia.
cbn [pf_spf] in *. unfold A_TP in *.
rewrite lupd_lupdS in TS2.
assert (HPP2 : HEAPA A4L HIx A2 (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw0 (tl_cbs l))) LM ((Ff, 2) :: FRS) B2 m2 md2 /\ put_pre A4H A4F (tl_cs l) m2 (tl_cbs l) (tl_cur l) 1).
{ unfold lput in OUT2. cbn [tl_cs tl_cbs tl_cur] in OUT2.
destruct OUT2 as [([Es | Erc] & H) | (s' & Es & _ & J' & H)]; [| exfalso; lia |].
- rewrite Es in PP1' |- *. destruct PP1' as [Ep EBS]. rewrite EBS. split; [| split; [exact Ep | reflexivity]].
eapply (heapA_perm A4L HIx); [exact H | | apply Permutation_refl | apply Permutation_refl].
apply Permutation_sym. eapply Permutation_trans; [apply perm_blocks_tsF; exact Eobj0 | cbn [app]; apply Permutation_refl].
- rewrite Es in PP1' |- *. destruct PP1' as (Hp & _ & _). split; [| split; [exact Hp | split; [lia | exact J']]].
eapply (heapA_perm A4L HIx); [exact H | apply Permutation_sym; apply perm_blocks_tsF; exact Eobj0 | apply Permutation_refl | apply Permutation_refl]. }
destruct HPP2 as [HP2 PP2].
destruct (PE_WIN_resetB (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ m2 md md2 A A2 B B2 tw0 (tl_cur l) (tl_cs l) (tl_cbs l) cb nb pj1 sv errv dp
STC WIN1' eq_refl VM2 HP2 PP2 TS2 TOK2 ST2 HPR2 ERR2 AG2) as [WIN2 PBT2].
pose proof (PBT2 _ (PBT1' _ (PBT1 _ PBK0))) as PBK2.
assert (BK2 : BOK (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts0 B2 nB).
{ eapply (BOK_pay _ _ _ _ B2 nB (put_costA (tl_cs lput) 2 (tl_cbs lput) + 512) BK); [unfold put_costA, lput; cbn [tl_cs tl_cbs]; destruct (tl_cs l); cbn; lia | exact BB2 | clear - BD2; lia]. }
clear TOK SLOTS Ld SHQ0 SHQ2 MU WM MI HP INtk INq Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk WIN1 WIN1' PBT1 PBT1' TSK1 FR1 PBK0 TSK1' TOK1' HP1' ST1' ERR1' PP1' HP2 PP2 TS2 TOK2 ST2 HPR2 ERR2 AG2 BB2 BD2 VM2
SEPQ0c SEPQ2c SEPT2c SEPT7c cs_tk_L cs_L_tk cs_Q0_L cs_Q2_L.
set (tw2 := ts_lvl tw0 lvl_reset) in *.

pose proof WIN2 as (COREx & BASEx & _). destruct COREx as (_ & _ & _ & _ & TOK & _ & _ & TSK3 & FR3). pose proof (proj1 BASEx) as HP. clear BASEx.
unfold tw2, tw0, ts_lvl, ts0 in TOK. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR3 as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc pj_0 pj_8 pj_16 pj_obj pj_288 pj_304 pj1] in SLOTS.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw2 (tl_cbs l)))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t3.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 2 HP INtk ltac:(lia)) as SHT2.
replace (tk / 8 + 2 + A_SB) with (tk / 8 + 2147450882) in SHT2 by (unfold A_SB; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m2) as WM.
pose proof (munch_refl [(tk, tk + 72)] m2) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t3. stash WIN2. stash TSK3. stash FR3.
reenterA asegs A4L HIx asegs_wx HP.
asan_rechkMB 1.
step. step.
norm_sx32.
do 3 step.
norm_w32. replace (Z.of_nat (S dp) + -1) with (Z.of_nat dp) by lia.
step. if_truex.
asan_rechkB.
clear SHT2.
step.
stepz.
step.

unstash WIN2.
assert (Hdp : (dp < length levels)%nat) by lia.
destruct (nth_error levels dp) as [lp|] eqn:Hlp; [| apply nth_error_None in Hlp; lia].
assert (STp : tl_st lp = ST_array_add \/ tl_st lp = ST_ovadd).
{ pose proof (LV dp lp Hlp) as (_ & _ & _ & Mp). replace (dp <? S dp)%nat with true in Mp by (symmetry; apply Nat.ltb_lt; lia).
destruct Mp as [(E & _) | (E & _)]; [left | right]; exact E. }
pose proof (BOK_weak _ _ _ _ _ (BOK_pop (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts0 B2 nB l dp BK2 eq_refl Hl Hnbs0 Eobjbs)) as BUDf.
pose proof (BOK_pop (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts0 B2 nB l dp BK2 eq_refl Hl Hnbs0 Eobjbs) as BKf.
unfold ts0 in BUDf, BKf. cbn [t_levels t_depth t_co t_pb t_pbs t_x] in BUDf, BKf.
assert (Hrl : nth_error (t_levels tw2) (S dp) = Some (TL ST_eatws ST_start 0 None [] 0 []))
by (unfold tw2, tw0, ts_lvl, ts0; cbn [t_levels t_depth]; apply nth_error_lupd_eq; rewrite !lupd_length; apply nth_error_Some; rewrite Hl; discriminate).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mcF _) =>
lazymatch goal with MUc : munch _ ?mb mcF, WMc : wmono asegs ?mb mcF, MIc : mem_inv asegs mcF, TOKc : rw_cells asegs mcF tk _ |- _ =>
evt_done5;
destruct (PE_WIN_close_pop HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mb mcF md2 A2 B2 tw2 (tl_cur l) (tl_cs l) (tl_cbs l) cb nb pj1 sv errv dp
STC WIN2 eq_refl Hrl MUc WMc MIc TOKc
ltac:(unfold tw2, tw0, ts_lvl, ts0; cbn [t_levels t_depth t_co t_pb t_pbs t_x]; rewrite !lupd_lupdS; exact BUDf)) as [INVf PBTf];
pose proof (PBTf _ PBK2) as PBKf;
unfold tw2, tw0, ts_lvl, ts0 in INVf, PBKf; cbn [t_levels t_depth t_co t_pb t_pbs t_x] in INVf, PBKf; rewrite !lupd_lupdS in INVf, PBKf;
eapply (Kredo mcF md2 A2 B2 pj1 dp lp); [reflexivity | exact Hlp | exact STp | exact INVf | reflexivity | exact PBKf | exact BKf | exact FS2 | exact FRM2]
end end.
Qed.
End PeSFinishB.
End RC__1.
End Mq4.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QRUw.Mq2 QmZZ. Import QPZI.Mq4. Import QkMG. Import QG8z Qdyh.Mq0.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QlKV.Mqf QlKV.Mqh QSHS Ql4f.Mq4 QsKa.Mqh QrQv.Mq4 QEUF.Mq2 QdGy.Mqe Q63E.Mqc.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSNameCallA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.

Lemma pe_free_name_n :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP v2 ra2 p n : Z)
(ra gp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_NWIN HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts [(p, n)] cb nb pj sv errv ->
PBOKat m ts kP -> 512 <= bB B ->
pe_s0 sv = Z_to_bv 64 v2 -> pe_ra sv = Z_to_bv 64 ra2 ->
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64 ->
uw_ok A4L (hl_free A4H) ra (UWfp ra2 v2) ->
bv_unsigned ra mod 2 = 0 ->
(forall m2 md2 A2 (r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word),
PE_NWIN HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 (charge B 512 0) ts [] cb nb pj sv errv ->
PBOKat m2 ts kP ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 (Z_to_bv 64 (pa_sp0 pa)) s1 r w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F (ret_pc ra) fc None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x6369c) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC WIN PBK COST S0V RAV HV UWK RA K.
pose proof WIN as (CORE & BASE & LVo & CUR & Eobj). pose proof BASE as (HP1 & ST1 & ERR1 & _).
pose proof CORE as (_ & _ & _ & _ & _ & _ & _ & _ & FR1).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
assert (SPF : lo <= pf_spf pf - 4096 /\ pf_spf pf mod 16 = 0 /\ pf_spf pf < hiA_top A4L HIx + 64 /\ 0 <= pf_spf pf < 2^62 /\ 0 <= pa_sp0 pa < 2^63).
{ clear - LOS HT Gle Gspf SP0. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; lia. }
destruct SPF as (SPF1 & SPF2 & SPF3 & SPF4 & SPF5).
set (RB := pe_blocksA pf q LB0 ts) in *.
assert (HPa : HEAPA A4L HIx A ((p, n) :: RB) LM ((pa_F pa, 2) :: FRS) B m md).
{ eapply (heapA_perm A4L HIx); [exact HP1 | | apply Permutation_refl | apply Permutation_refl]. exact (perm_blocks_tsF pf q LB0 ts [(p, n)] Eobj). }
pose proof (pe_uw_at HIx pf pa lo m cb nb pj sv v2 ra2 STC FR1 S0V RAV (proj1 HV) (proj2 HV)) as UWA.
eapply (hiA_free A4L HIx) with (p := p) (u := UWfp ra2 v2) (lo := lo) (errv := errv);
[ exact HPa | right; exists n; left; reflexivity | rewrite unsigned_lit by lia; exact ST1 | exact LO | rewrite unsigned_lit by lia; cbn [hl_stack_A A4L]; exact SPF1
| rewrite unsigned_lit by lia; exact SPF2 | rewrite unsigned_lit by lia; exact SPF3 | exact ERR1 | reflexivity | reflexivity
| split; [rewrite !unsigned_lit by lia; apply (uw_at_pre0 _ _ _ _ _ _ UWA); lia | exact UWK] | exact COST
| cbn [uw_cost]; destruct (p =? 0); exact (proj2 (heapA_budget A4L HIx _ _ _ _ _ _ _ HP1)) | ].
intros ms2 m2 md2 A2 r RS2 VM2 ST2 HPR2 ERR2 HP2.
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & ->).
cbn [hl_segs hl_tp hla_base A4L A4H] in *. rewrite ?(unsigned_lit (pf_spf pf)) in ST2 by lia. rewrite ?(unsigned_lit (pf_spf pf)) in HPR2 by lia.
rewrite lb_remove_head in HPR2, HP2.
assert (Ecost : (if p =? 0 then 0 else uw_cost (UWfp ra2 v2)) = 0) by (destruct (p =? 0); reflexivity). rewrite Ecost in HP2.
assert (WIN2 : PE_NWIN HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 (charge B 512 0) ts [] cb nb pj sv errv).
{ eapply (PE_NWIN_callG HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B (charge B 512 0) ts [(p, n)] [] cb nb pj sv errv errv);
[exact STC | exact WIN | exact VM2 | exact HPR2 | | exact ST2 | exact ERR2].
eapply (heapA_perm A4L HIx); [exact HP2 | | apply Permutation_refl | apply Permutation_refl].
apply Permutation_sym. exact (perm_blocks_tsF pf q LB0 ts [] Eobj). }
eapply (K m2 md2 A2 r); [exact WIN2|].
assert (AG : agree_on asegs RB m m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPR2 | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
eapply PBOKat_agree; [exact PBK | exact AG |]. unfold RB, pe_blocksA, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb.
Qed.
End PeSNameCallA.
End RC__1.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QRUw.Mq2 QmZZ. Import QPZI.Mq4. Import QkMG. Import QG8z Qdyh.Mq0.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QlKV.Mqf QlKV.Mqh QSHS Ql4f.Mq4 QsKa.Mqh QrQv.Mq4 QEUF.Mq2 QdGy.Mqe Q63E.Mqc.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma nonul_forallA : forall s : list byte, ~ In (Z_to_bv 8 0) s -> Forall (fun b => bv_unsigned b <> 0) s.
Proof.
induction s as [|b s IH]; intros H; [constructor|]. constructor.
- intros E. apply H. left. apply bv_eq. rewrite E. reflexivity.
- apply IH. intros Hin. apply H. right. exact Hin.
Qed.

Lemma BOK_name_attach : forall pf pa ts B B' n l st' ss' nm nn c {C},
BOK pf pa ts B (S (Z.to_nat C + n)) -> nth_error (t_levels ts) (t_depth ts) = Some l -> tl_nbs l = [] ->
lvl_closed l = false -> lvl_closed (TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) nm [(nm, nn)]) = false ->
nn <= Z.max 0 (pf_len pf) + 1 ->
c + K_free <= C ->
bB B - c <= bB B' -> bD B - 1 <= bD B' ->
BOK pf pa (ts_lvl ts (TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) nm [(nm, nn)])) B' n.
Proof.
intros pf pa ts B B' n l st' ss' nm nn c C (H1 & H2 & H3 & H4 & H5) Hl Hnbs Hop Hop' Hnn HC HB HD.
set (l' := TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) nm [(nm, nn)]) in *.
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
pose proof (H5 (t_depth ts) l (le_n _) Hl) as (P0 & AI & OI & NI).
assert (Hphi : phi_open l' = phi_open l) by (unfold phi_open; rewrite Hop, Hop'; reflexivity).
pose proof (tstate_blocks_lvl_length ts l l' Hl) as Hblk.
assert (Hlb : Z.of_nat (length (lvl_blocks l')) = Z.of_nat (length (lvl_blocks l)) + 1) by (unfold lvl_blocks, l'; cbn [tl_cbs tl_nbs]; rewrite Hnbs, !length_app; cbn [length]; lia).
unfold BOK, bneed in *.
replace (K_ev pf * Z.of_nat (S (Z.to_nat C + n))) with (K_ev pf * Z.of_nat n + (Z.max 0 C + 1)) in H1 by (unfold K_ev; lia).
split.
{ rewrite Hblk. unfold ts_lvl; cbn [t_levels t_depth t_pbs]. rewrite (ledger_open_lupd (t_levels ts) (S (t_depth ts)) (t_depth ts) l l' Hl (Nat.lt_succ_diag_r _)). unfold K_free in *. lia. }
split; [lia|]. split; [exact H3|]. split; [exact H4|].
unfold ts_lvl; cbn [t_levels t_depth]. intros i li Hi Hn.
destruct (PeanoNat.Nat.eq_dec i (t_depth ts)) as [-> | NE].
- rewrite nth_error_lupd_eq in Hn by exact Hd. injection Hn as <-. split; [lia|].
split; [intros _ kids Hcs; apply AI; [exact Hop | exact Hcs]|]. split; [intros _ kids Hcs; apply (OI Hop kids); exact Hcs|].
apply Forall_cons; [cbn [snd]; exact Hnn | apply Forall_nil].
- rewrite nth_error_lupd_neq in Hn by congruence. exact (H5 i li Hi Hn).
Qed.

Section PeSNameDupA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.

Lemma pe_strdup_name :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP v2 ra2 buf size : Z) (str : list byte)
(ra gp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_NWIN HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts [] cb nb pj sv errv ->
PBOKat m ts kP ->
In (buf, size) (t_pbs ts) -> Z.of_nat (length str) + 1 <= size -> Z.of_nat (length str) + 1 < 2^32 ->
bytes_at asegs m buf (str ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str ->
16 * (Z.of_nat (length str) + 1) + 512 <= bB B ->
pe_s0 sv = Z_to_bv 64 v2 -> pe_ra sv = Z_to_bv 64 ra2 ->
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64 ->
uw_ok A4L (hl_strdup A4L) ra (UWfp ra2 v2) ->
bv_unsigned ra mod 2 = 0 ->
(forall m2 md2 A2 (errv2 : word) (r : Z) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word),
( (r = 0 /\ PE_NWIN HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 (charge B (16 * (Z.of_nat (length str) + 1) + 512) 0) ts [] cb nb pj sv errv2)
\/ (0 < r < 2^62 /\ cstr asegs m2 r (Z.of_nat (length str) + 1) str
/\ PE_NWIN HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 (charge B (16 * (Z.of_nat (length str) + 1) + 512) 0) ts [(r, Z.of_nat (length str) + 1)] cb nb pj sv errv2) ) ->
PBOKat m2 ts kP ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 r) w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F (ret_pc ra) fc None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 buf) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x4fdd8) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC WIN PBK INB SZ L32 STR NN COST S0V RAV HV UWK RA K.
pose proof WIN as (CORE & BASE & LVo & CUR & Eobj). pose proof BASE as (HP1 & ST1 & ERR1 & _).
pose proof CORE as (_ & _ & _ & _ & _ & _ & _ & _ & FR1).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
assert (SPF : lo <= pf_spf pf - 4096 /\ pf_spf pf mod 16 = 0 /\ pf_spf pf < hiA_top A4L HIx + 64 /\ 0 <= pf_spf pf < 2^62 /\ 0 <= pa_sp0 pa < 2^63).
{ clear - LOS HT Gle Gspf SP0. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; lia. }
destruct SPF as (SPF1 & SPF2 & SPF3 & SPF4 & SPF5).
set (RB := pe_blocksA pf q LB0 ts) in *.
assert (HPa : HEAPA A4L HIx A RB LM ((pa_F pa, 2) :: FRS) B m md).
{ eapply (heapA_perm A4L HIx); [exact HP1 | | apply Permutation_refl | apply Permutation_refl]. exact (perm_blocks_tsF pf q LB0 ts [] Eobj). }
assert (INbuf : In (buf, size) RB) by (unfold RB, pe_blocksA, tstate_blocks; apply in_or_app; left; apply in_or_app; left; exact INB).
pose proof (pe_uw_at HIx pf pa lo m cb nb pj sv v2 ra2 STC FR1 S0V RAV (proj1 HV) (proj2 HV)) as UWA.
eapply (hiA_strdup A4L HIx) with (LB := RB) (ab := buf) (nb := size) (src := buf) (str := str) (u := UWfp ra2 v2) (lo := lo) (errv := errv);
[ exact HPa | exact INbuf | lia | lia | exact STR | exact NN | exact L32 | rewrite unsigned_lit by lia; exact ST1 | exact LO
| rewrite unsigned_lit by lia; cbn [hl_stack_A A4L]; exact SPF1 | rewrite unsigned_lit by lia; exact SPF2 | rewrite unsigned_lit by lia; exact SPF3 | exact ERR1 | reflexivity | reflexivity
| rewrite !unsigned_lit by lia; apply (uw_at_pre0 _ _ _ _ _ _ UWA); lia | exact UWK | exact COST
| cbn [uw_cost]; exact (proj2 (heapA_budget A4L HIx _ _ _ _ _ _ _ HP1)) | ].
intros ms2 m2 md2 A2 r errv2 RS2 VM2 ST2 HPR2 ERR2 OUT2.
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & ->).
cbn [hl_segs hl_tp hla_base A4L A4H] in *. rewrite ?(unsigned_lit (pf_spf pf)) in ST2 by lia. rewrite ?(unsigned_lit (pf_spf pf)) in HPR2 by lia.
cbn [uw_cost] in OUT2.
assert (AG : agree_on asegs RB m m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPR2 | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
eapply (K m2 md2 A2 errv2 r).
2:{ eapply PBOKat_agree; [exact PBK | exact AG |]. unfold RB, pe_blocksA, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb. }
destruct OUT2 as [(-> & _ & HP2) | (Hr & NEWK & HP2)].
- left. split; [reflexivity|].
eapply (PE_NWIN_callG HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B _ ts [] [] cb nb pj sv errv errv2);
[exact STC | exact WIN | exact VM2 | exact HPR2 | | exact ST2 | exact ERR2].
eapply (heapA_perm A4L HIx); [exact HP2 | | apply Permutation_refl | apply Permutation_refl].
apply Permutation_sym. exact (perm_blocks_tsF pf q LB0 ts [] Eobj).
- right.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r _ HP2 ltac:(apply in_or_app; left; left; reflexivity)) as (_ & _ & Hr0 & Hrhi & Hrwr).
cbn [hl_segs hla_base A4L A4H] in Hrwr. pose proof alloc_ceiling_range as ACR.
split; [lia|].
split.
+ split; [lia|]. split; [apply nonul_forallA; exact NN|]. exists []. rewrite app_nil_r.
pose proof (bytes_at_bound _ _ _ _ NEWK) as NB. rewrite length_app in NB. cbn [length] in NB.
split; [split; [cbn; split; [rewrite length_app; cbn [length]; lia | exact I] | cbn; rewrite app_nil_r; exact NEWK] |].
cbn [cells_size csize Nat.add]. replace (Z.of_nat (Z.to_nat (Z.of_nat (length str) + 1) + 0)) with (Z.of_nat (length str) + 1) by lia. exact Hrwr.
+ eapply (PE_NWIN_callG HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B _ ts [] [(r, Z.of_nat (length str) + 1)] cb nb pj sv errv errv2);
[exact STC | exact WIN | exact VM2 | exact HPR2 | | exact ST2 | exact ERR2].
eapply (heapA_perm A4L HIx); [exact HP2 | | apply Permutation_refl | apply Permutation_refl].
apply Permutation_sym. exact (perm_blocks_tsF pf q LB0 ts [(r, Z.of_nat (length str) + 1)] Eobj).
Qed.
End PeSNameDupA.
End RC__1.
End Mq6.

From Stdlib Require Import ZArith List Lia Bool Permutation.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmZZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPZI.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QG8z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QG8z. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyh.Mq0.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4v2.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1Ey.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1Ey. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql4f.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql4f.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrQv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrQv.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEUF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEUF. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdGy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdGy.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q63E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q63E.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma nonul_forallA : forall s : list byte, ~ In (Z_to_bv 8 0) s -> Forall (fun b => bv_unsigned b <> 0) s.
Proof.
induction s as [|b s IH]; intros H; [constructor|]. constructor.
- intros E. apply H. left. apply bv_eq. rewrite E. reflexivity.
- apply IH. intros Hin. apply H. right. exact Hin.
Qed.

Lemma BOK_name_attach : forall pf pa ts B B' n l st' ss' nm nn c {C},
BOK pf pa ts B (S (Z.to_nat C + n)) -> nth_error (t_levels ts) (t_depth ts) = Some l -> tl_nbs l = [] ->
lvl_closed l = false -> lvl_closed (TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) nm [(nm, nn)]) = false ->
nn <= Z.max 0 (pf_len pf) + 1 ->
c + K_free <= C ->
bB B - c <= bB B' -> bD B - 1 <= bD B' ->
BOK pf pa (ts_lvl ts (TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) nm [(nm, nn)])) B' n.
Proof.
intros pf pa ts B B' n l st' ss' nm nn c C (H1 & H2 & H3 & H4 & H5) Hl Hnbs Hop Hop' Hnn HC HB HD.
set (l' := TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) nm [(nm, nn)]) in *.
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
pose proof (H5 (t_depth ts) l (le_n _) Hl) as (P0 & AI & OI & NI).
assert (Hphi : phi_open l' = phi_open l) by (unfold phi_open; rewrite Hop, Hop'; reflexivity).
pose proof (tstate_blocks_lvl_length ts l l' Hl) as Hblk.
assert (Hlb : Z.of_nat (length (lvl_blocks l')) = Z.of_nat (length (lvl_blocks l)) + 1) by (unfold lvl_blocks, l'; cbn [tl_cbs tl_nbs]; rewrite Hnbs, !length_app; cbn [length]; lia).
unfold BOK, bneed in *.
replace (K_ev pf * Z.of_nat (S (Z.to_nat C + n))) with (K_ev pf * Z.of_nat n + (Z.max 0 C + 1)) in H1 by (unfold K_ev; lia).
split.
{ rewrite Hblk. unfold ts_lvl; cbn [t_levels t_depth t_pbs]. rewrite (ledger_open_lupd (t_levels ts) (S (t_depth ts)) (t_depth ts) l l' Hl (Nat.lt_succ_diag_r _)). unfold K_free in *. lia. }
split; [lia|]. split; [exact H3|]. split; [exact H4|].
unfold ts_lvl; cbn [t_levels t_depth]. intros i li Hi Hn.
destruct (PeanoNat.Nat.eq_dec i (t_depth ts)) as [-> | NE].
- rewrite nth_error_lupd_eq in Hn by exact Hd. injection Hn as <-. split; [lia|].
split; [intros _ kids Hcs; apply AI; [exact Hop | exact Hcs]|]. split; [intros _ kids Hcs; apply (OI Hop kids); exact Hcs|].
apply Forall_cons; [cbn [snd]; exact Hnn | apply Forall_nil].
- rewrite nth_error_lupd_neq in Hn by congruence. exact (H5 i li Hi Hn).
Qed.

Section PeSNameDupA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.

Lemma pe_strdup_name :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP v2 ra2 buf size : Z) (str : list byte)
(ra gp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_NWIN HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts [] cb nb pj sv errv ->
PBOKat m ts kP ->
In (buf, size) (t_pbs ts) -> Z.of_nat (length str) + 1 <= size -> Z.of_nat (length str) + 1 < 2^32 ->
bytes_at asegs m buf (str ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str ->
16 * (Z.of_nat (length str) + 1) + 512 <= bB B ->
pe_s0 sv = Z_to_bv 64 v2 -> pe_ra sv = Z_to_bv 64 ra2 ->
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64 ->
uw_ok A4L (hl_strdup A4L) ra (UWfp ra2 v2) ->
bv_unsigned ra mod 2 = 0 ->
(forall m2 md2 A2 (errv2 : word) (r : Z) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word),
( (r = 0 /\ PE_NWIN HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 (charge B (16 * (Z.of_nat (length str) + 1) + 512) 0) ts [] cb nb pj sv errv2)
\/ (0 < r < 2^62 /\ cstr asegs m2 r (Z.of_nat (length str) + 1) str
/\ PE_NWIN HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 (charge B (16 * (Z.of_nat (length str) + 1) + 512) 0) ts [(r, Z.of_nat (length str) + 1)] cb nb pj sv errv2) ) ->
PBOKat m2 ts kP ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 r) w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F (ret_pc ra) fc None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) s1 (Z_to_bv 64 buf) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x4fa00) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC WIN PBK INB SZ L32 STR NN COST S0V RAV HV UWK RA K.
pose proof WIN as (CORE & BASE & LVo & CUR & Eobj). pose proof BASE as (HP1 & ST1 & ERR1 & _).
pose proof CORE as (_ & _ & _ & _ & _ & _ & _ & _ & FR1).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
assert (SPF : lo <= pf_spf pf - 4096 /\ pf_spf pf mod 16 = 0 /\ pf_spf pf < hiA_top A4L HIx + 64 /\ 0 <= pf_spf pf < 2^62 /\ 0 <= pa_sp0 pa < 2^63).
{ clear - LOS HT Gle Gspf SP0. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; lia. }
destruct SPF as (SPF1 & SPF2 & SPF3 & SPF4 & SPF5).
set (RB := pe_blocksA pf q LB0 ts) in *.
assert (HPa : HEAPA A4L HIx A RB LM ((pa_F pa, 2) :: FRS) B m md).
{ eapply (heapA_perm A4L HIx); [exact HP1 | | apply Permutation_refl | apply Permutation_refl]. exact (perm_blocks_tsF pf q LB0 ts [] Eobj). }
assert (INbuf : In (buf, size) RB) by (unfold RB, pe_blocksA, tstate_blocks; apply in_or_app; left; apply in_or_app; left; exact INB).
pose proof (pe_uw_at HIx pf pa lo m cb nb pj sv v2 ra2 STC FR1 S0V RAV (proj1 HV) (proj2 HV)) as UWA.
eapply (hiA_strdup A4L HIx) with (LB := RB) (ab := buf) (nb := size) (src := buf) (str := str) (u := UWfp ra2 v2) (lo := lo) (errv := errv);
[ exact HPa | exact INbuf | lia | lia | exact STR | exact NN | exact L32 | rewrite unsigned_lit by lia; exact ST1 | exact LO
| rewrite unsigned_lit by lia; cbn [hl_stack_A A4L]; exact SPF1 | rewrite unsigned_lit by lia; exact SPF2 | rewrite unsigned_lit by lia; exact SPF3 | exact ERR1 | reflexivity | reflexivity
| rewrite !unsigned_lit by lia; apply (uw_at_pre0 _ _ _ _ _ _ UWA); lia | exact UWK | exact COST
| cbn [uw_cost]; exact (proj2 (heapA_budget A4L HIx _ _ _ _ _ _ _ HP1)) | ].
intros ms2 m2 md2 A2 r errv2 RS2 VM2 ST2 HPR2 ERR2 OUT2.
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & ->).
cbn [hl_segs hl_tp hla_base A4L A4H] in *. rewrite ?(unsigned_lit (pf_spf pf)) in ST2 by lia. rewrite ?(unsigned_lit (pf_spf pf)) in HPR2 by lia.
cbn [uw_cost] in OUT2.
assert (AG : agree_on asegs RB m m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPR2 | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
eapply (K m2 md2 A2 errv2 r).
2:{ eapply PBOKat_agree; [exact PBK | exact AG |]. unfold RB, pe_blocksA, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb. }
destruct OUT2 as [(-> & _ & HP2) | (Hr & NEWK & HP2)].
- left. split; [reflexivity|].
eapply (PE_NWIN_callG HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B _ ts [] [] cb nb pj sv errv errv2);
[exact STC | exact WIN | exact VM2 | exact HPR2 | | exact ST2 | exact ERR2].
eapply (heapA_perm A4L HIx); [exact HP2 | | apply Permutation_refl | apply Permutation_refl].
apply Permutation_sym. exact (perm_blocks_tsF pf q LB0 ts [] Eobj).
- right.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r _ HP2 ltac:(apply in_or_app; left; left; reflexivity)) as (_ & _ & Hr0 & Hrhi & Hrwr).
cbn [hl_segs hla_base A4L A4H] in Hrwr. pose proof alloc_ceiling_range as ACR.
split; [lia|].
split.
+ split; [lia|]. split; [apply nonul_forallA; exact NN|]. exists []. rewrite app_nil_r.
pose proof (bytes_at_bound _ _ _ _ NEWK) as NB. rewrite length_app in NB. cbn [length] in NB.
split; [split; [cbn; split; [rewrite length_app; cbn [length]; lia | exact I] | cbn; rewrite app_nil_r; exact NEWK] |].
cbn [cells_size csize Nat.add]. replace (Z.of_nat (Z.to_nat (Z.of_nat (length str) + 1) + 0)) with (Z.of_nat (length str) + 1) by lia. exact Hrwr.
+ eapply (PE_NWIN_callG HIx GA GA_pres pf pa q LB0 LM FRS payload me lo m m2 md md2 A A2 B _ ts [] [(r, Z.of_nat (length str) + 1)] cb nb pj sv errv errv2);
[exact STC | exact WIN | exact VM2 | exact HPR2 | | exact ST2 | exact ERR2].
eapply (heapA_perm A4L HIx); [exact HP2 | | apply Permutation_refl | apply Permutation_refl].
apply Permutation_sym. exact (perm_blocks_tsF pf q LB0 ts [(r, Z.of_nat (length str) + 1)] Eobj).
Qed.
End PeSNameDupA.
End RC__1.
