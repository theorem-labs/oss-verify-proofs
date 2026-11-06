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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q63E.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpFy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpFy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Quj7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Quj7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnX9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpNt.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrIB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

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
Collection CtxAll := RC__ HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP p s10 s11 T BB0 BD0 wtx.

Notation SINVAc := (SINVA HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size p wtx).
Notation KSBc := (KSB HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size p s10 s11 T wtx).
Notation KSFAc := (KSFA HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size p s10 s11 T wtx).
Notation sstateBc := (sstateB sp0 sp1 Fr p s10 s11).
Let HINVA_callc := HINVA_call HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP.
Let EVDc := fdp_evidenceA HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP.
Let FSLc := fslot_evidenceA HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP.
Let OWNc := own_writesA HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP.
Let GAOc := GA_jo_own HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP.
Let set_callc := set_callA HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP p s10 s11 T BB0 BD0 wtx.
Let SINVA_ownc := SINVA_own HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP p s10 s11 T BB0 BD0 wtx.
Let SINVA_retc := SINVA_ret HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP p s10 s11 T BB0 BD0 wtx.

Lemma bytes_at_firstn : forall segs m a (bs : list byte) (c : Z),
bytes_at segs m a bs -> 0 <= c <= Z.of_nat (length bs) -> bytes_at segs m a (firstn (Z.to_nat c) bs).
Proof.
intros segs m a bs c B Hc. pose proof (bytes_at_sub segs m a bs 0 (Z.to_nat c) B ltac:(lia)) as X.
change (Z.of_nat 0) with 0 in X. rewrite Z.add_0_r in X. exact X.
Qed.

Ltac seg_open SI m :=
pose proof SI as ((PX & VM & FS & FRM & LOC & LCK & G & ST & SL & FD & (fj0 & fj1 & FF0 & FF1) & FSH & LSH & BY & L & P0 & P1 & P2) & HP & RR & RD & BB & BD & RW);
pose proof (heapA_mem_inv _ HIx _ _ _ _ _ _ _ HP) as MI; change (hl_segs _) with asegs in MI;
pose proof alloc_ceiling_range as ACR; pose proof (hiA_top_le _ HIx) as HT47;
pose proof (bv_unsigned_in_range 64 sp0) as SP0R; change (bv_modulus 64) with (2^64) in SP0R;
unfold T_LOCCELL_A, T_LOCALE_LOCK_A, A_TP in LOC, LCK;
(lazymatch type of BY with bytes_at _ _ ?pp ?dd => assert (BYm : bytes_at asegs m pp dd /\ True) by (split; [exact BY | exact I]) end);
pose proof FRAPP as FRAPPu; unfold A_SB, A_HMB in FRAPPu;
unfold sstateB, A_TP;
set (sh := Fr / 8 + 2147450880) in *;
assert (SHR : 2147450880 <= sh /\ sh + 64 <= 17594333495296) by (unfold sh; clear - FRLO FRHI ACR; Z.div_mod_to_equations; lia).

#[using="CtxAll"] Lemma pds_of : forall A LBx B m md ptr rem, HEAPAx A LBx LM [(Fr, 3)] B m md -> incl LB0 LBx -> data0 <= ptr -> ptr + rem <= data0 + size -> 0 <= rem ->
rem = 0 \/ Fr + 32 + 16 <= ptr \/ ptr + rem <= Fr + 32.
Proof.
intros A LBx B m md ptr rem HP Hi P1 P2 R0. destruct INB as [Z0 | INB']; [lia|].
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP (or_introl eq_refl) (in_or_app _ _ _ (or_introl (Hi _ INB')))) as DF.
rewrite fr_size_3 in DF. right. lia.
Qed.

#[using="CtxAll HINVA_callc EVDc OWNc GAOc set_callc SINVA_ownc CA"] Lemma seg_setintA : forall m md (A : ASA A4L HIx) B F fc ptr rem data r BS LK sb sd
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
SINVAc SHB0 m md A B F fc ptr rem data r BS LK sb sd ->
KSBc (Fr + 32) (Fr + 128) 0x920e0 SHB0 r sb sd ->
AJ5 A4L HIx A T md (sstateBc (Fr + 32) (Fr + 128) x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x920c0 fc m).
Proof.
intros m md A B F fc ptr rem data r BS LK sb sd x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 SI K.
seg_open SI m.
assert (INCL : incl LB0 (BS ++ LK ++ LB0)) by (intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb).
destruct (EVDc A (BS ++ LK ++ LB0) B m md SHB0 ptr rem HP INCL FSH LSH ltac:(vm_compute; reflexivity) P1 P2) as (RT & UNP & UND).
pose proof (pds_of A (BS ++ LK ++ LB0) B m md ptr rem HP INCL P1 P2 ltac:(lia)) as PDS.
pose proof (munch_refl [(sp1 - 16, sp1); (Fr + 32 + 8, Fr + 32 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
(let L := constr:(A4L) in reenterA asegs L HIx asegs_wx HP).
step. step. step. step. step.
eapply evt_cut; [eapply Quj7.cii_i32_B with (P := Fr + 32) (ptr := ptr) (rem := rem) (lo := lo) (data := data) |].
all: rewrite ?unsigned_lit by lia.
1: reflexivity.
1: vm_compute; reflexivity.
1: vm_compute; reflexivity.
1: exact RT.
1: exact FD.
1: exact UNP.
1: clear - FRAL; Z.div_mod_to_equations; lia.
1: exact BY.
1: exact L.
1: exact P0.
1: exact UND.
1: exact ST.
1: exact LO.
1: lia.
1: lia.
1: lia.
1: unfold A_SB, A_HMB; clear - FRAPPu; lia.
1: lia.
1: exact PDS.
1: exact MI.
intros ms2 (yt0 & yt1 & yt2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & yt3 & yt4 & yt5 & yt6 & m2 & -> & MU2 & WM2 & MI2 & VAL & FD2 & BY2 & ST2).
unfold cii_WSA in MU2. rewrite ?unsigned_lit in MU2, ST2 by lia.
clear FD. stash FSH. transport_after_call asegs m m2 MU2 WM2. unstash FSH.
assert (SHFR : Fr + 504 <= sh \/ sh + 64 <= Fr) by (unfold sh; clear - FRAPPu FRLO; Z.div_mod_to_equations; lia).
apply (rw_cells_transport asegs [(sp1 - 16, sp1); (Fr + 32 + 8, Fr + 32 + 16)] m m2) in FSH; [| exact MU2 | exact WM2 | ].
2:{ cbn [disjoint_from cells_size csize Nat.add length map fst snd]. rewrite ?cells_size_C1, ?LSH. clear - SHR SHFR LO LOS ACR. lia. }
replace (ret_pc (Z_to_bv 64 0x920d4)) with (Z_to_bv 64 0x920d4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
step. step. step.
evt_done5.
eapply (set_callc 0x9e1d0 0x920e0 (Fr + 32) (Fr + 128)); [exact (ca_SETI _ _ _ _ _ _ _ CA) | lia | reflexivity | lia | lia | | exact K].
eapply (SINVA_ownc SHB0 SHB0 m m2) with (ptr' := ptr) (rem' := Z.max (rem - 4) 0) (data' := firstn (Z.to_nat (Z.max (rem - 4) 0)) data) (W := [(sp1 - 16, sp1); (Fr + 32 + 8, Fr + 32 + 16)]);
[ exact SI | exact MU2 | exact WM2 | exact MI2 | unfold own_iv; repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil | apply fsaved_refl | exact FRM
| exact LOC | exact LCK | exact ST2 | exact SL | exact FD2 | exists fj0, fj1; split; [exact FF0 | exact FF1] | exact FSH | exact LSH
| apply bytes_at_firstn; [exact (proj1 BYm) | lia] | rewrite firstn_length_le by lia; lia | exact P0 | exact P1 | lia ].
Qed.

#[using="CtxAll HINVA_callc EVDc OWNc GAOc set_callc SINVA_ownc CA"] Lemma seg_setint64A : forall m md (A : ASA A4L HIx) B F fc ptr rem data r BS LK sb sd
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
SINVAc SHB0 m md A B F fc ptr rem data r BS LK sb sd ->
KSBc (Fr + 32) (Fr + 128) 0x92100 SHB0 r sb sd ->
AJ5 A4L HIx A T md (sstateBc (Fr + 32) (Fr + 128) x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x920e0 fc m).
Proof.
intros m md A B F fc ptr rem data r BS LK sb sd x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 SI K.
seg_open SI m.
assert (INCL : incl LB0 (BS ++ LK ++ LB0)) by (intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb).
destruct (EVDc A (BS ++ LK ++ LB0) B m md SHB0 ptr rem HP INCL FSH LSH ltac:(vm_compute; reflexivity) P1 P2) as (RT & UNP & UND).
pose proof (pds_of A (BS ++ LK ++ LB0) B m md ptr rem HP INCL P1 P2 ltac:(lia)) as PDS.
pose proof (munch_refl [(sp1 - 16, sp1); (Fr + 32 + 8, Fr + 32 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
(let L := constr:(A4L) in reenterA asegs L HIx asegs_wx HP).
step. step. step. step. step.
eapply evt_cut; [eapply Quj7.cii_i64_B with (P := Fr + 32) (ptr := ptr) (rem := rem) (lo := lo) (data := data) |].
all: rewrite ?unsigned_lit by lia.
1: reflexivity.
1: vm_compute; reflexivity.
1: vm_compute; reflexivity.
1: exact RT.
1: exact FD.
1: exact UNP.
1: clear - FRAL; Z.div_mod_to_equations; lia.
1: exact BY.
1: exact L.
1: exact P0.
1: exact UND.
1: exact ST.
1: exact LO.
1: lia.
1: lia.
1: lia.
1: unfold A_SB, A_HMB; clear - FRAPPu; lia.
1: lia.
1: exact PDS.
1: exact MI.
intros ms2 (yt0 & yt1 & yt2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & yt3 & yt4 & yt5 & yt6 & m2 & -> & MU2 & WM2 & MI2 & VAL & FD2 & BY2 & ST2).
unfold cii_WSA in MU2. rewrite ?unsigned_lit in MU2, ST2 by lia.
clear FD. stash FSH. transport_after_call asegs m m2 MU2 WM2. unstash FSH.
assert (SHFR : Fr + 504 <= sh \/ sh + 64 <= Fr) by (unfold sh; clear - FRAPPu FRLO; Z.div_mod_to_equations; lia).
apply (rw_cells_transport asegs [(sp1 - 16, sp1); (Fr + 32 + 8, Fr + 32 + 16)] m m2) in FSH; [| exact MU2 | exact WM2 | ].
2:{ cbn [disjoint_from cells_size csize Nat.add length map fst snd]. rewrite ?cells_size_C1, ?LSH. clear - SHR SHFR LO LOS ACR. lia. }
replace (ret_pc (Z_to_bv 64 0x920f4)) with (Z_to_bv 64 0x920f4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
step. step. step.
evt_done5.
eapply (set_callc 0x9e27c 0x92100 (Fr + 32) (Fr + 128)); [exact (ca_SETI64 _ _ _ _ _ _ _ CA) | lia | reflexivity | lia | lia | | exact K].
eapply (SINVA_ownc SHB0 SHB0 m m2) with (ptr' := ptr) (rem' := Z.max (rem - 8) 0) (data' := firstn (Z.to_nat (Z.max (rem - 8) 0)) data) (W := [(sp1 - 16, sp1); (Fr + 32 + 8, Fr + 32 + 16)]);
[ exact SI | exact MU2 | exact WM2 | exact MI2 | unfold own_iv; repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil | apply fsaved_refl | exact FRM
| exact LOC | exact LCK | exact ST2 | exact SL | exact FD2 | exists fj0, fj1; split; [exact FF0 | exact FF1] | exact FSH | exact LSH
| apply bytes_at_firstn; [exact (proj1 BYm) | lia] | rewrite firstn_length_le by lia; lia | exact P0 | exact P1 | lia ].
Qed.

#[using="CtxAll HINVA_callc EVDc OWNc GAOc set_callc SINVA_ownc CA"] Lemma seg_setuint64A : forall m md (A : ASA A4L HIx) B F fc ptr rem data r BS LK sb sd
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
SINVAc SHB0 m md A B F fc ptr rem data r BS LK sb sd ->
KSBc (Fr + 32) (Fr + 128) 0x9211c SHB0 r sb sd ->
AJ5 A4L HIx A T md (sstateBc (Fr + 32) (Fr + 128) x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x92100 fc m).
Proof.
intros m md A B F fc ptr rem data r BS LK sb sd x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 SI K.
seg_open SI m.
assert (INCL : incl LB0 (BS ++ LK ++ LB0)) by (intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb).
destruct (EVDc A (BS ++ LK ++ LB0) B m md SHB0 ptr rem HP INCL FSH LSH ltac:(vm_compute; reflexivity) P1 P2) as (RT & UNP & UND).
pose proof (pds_of A (BS ++ LK ++ LB0) B m md ptr rem HP INCL P1 P2 ltac:(lia)) as PDS.
pose proof (munch_refl [(sp1 - 16, sp1); (Fr + 32 + 8, Fr + 32 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
(let L := constr:(A4L) in reenterA asegs L HIx asegs_wx HP).
step. step. step. step.
eapply evt_cut; [eapply Quj7.cii_u64_B with (P := Fr + 32) (ptr := ptr) (rem := rem) (lo := lo) (data := data) |].
all: rewrite ?unsigned_lit by lia.
1: reflexivity.
1: vm_compute; reflexivity.
1: vm_compute; reflexivity.
1: exact RT.
1: exact FD.
1: exact UNP.
1: clear - FRAL; Z.div_mod_to_equations; lia.
1: exact BY.
1: exact L.
1: exact P0.
1: exact UND.
1: exact ST.
1: exact LO.
1: lia.
1: lia.
1: lia.
1: unfold A_SB, A_HMB; clear - FRAPPu; lia.
1: lia.
1: exact PDS.
1: exact MI.
intros ms2 (yt0 & yt1 & yt2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & yt3 & yt4 & yt5 & yt6 & m2 & -> & MU2 & WM2 & MI2 & VAL & FD2 & BY2 & ST2).
unfold cii_WSA in MU2. rewrite ?unsigned_lit in MU2, ST2 by lia.
clear FD. stash FSH. transport_after_call asegs m m2 MU2 WM2. unstash FSH.
assert (SHFR : Fr + 504 <= sh \/ sh + 64 <= Fr) by (unfold sh; clear - FRAPPu FRLO; Z.div_mod_to_equations; lia).
apply (rw_cells_transport asegs [(sp1 - 16, sp1); (Fr + 32 + 8, Fr + 32 + 16)] m m2) in FSH; [| exact MU2 | exact WM2 | ].
2:{ cbn [disjoint_from cells_size csize Nat.add length map fst snd]. rewrite ?cells_size_C1, ?LSH. clear - SHR SHFR LO LOS ACR. lia. }
replace (ret_pc (Z_to_bv 64 0x92110)) with (Z_to_bv 64 0x92110) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
step. step. step.
evt_done5.
eapply (set_callc 0x9ed0c 0x9211c (Fr + 32) (Fr + 128)); [exact (ca_SETU64 _ _ _ _ _ _ _ CA) | lia | reflexivity | lia | lia | | exact K].
eapply (SINVA_ownc SHB0 SHB0 m m2) with (ptr' := ptr) (rem' := Z.max (rem - 8) 0) (data' := firstn (Z.to_nat (Z.max (rem - 8) 0)) data) (W := [(sp1 - 16, sp1); (Fr + 32 + 8, Fr + 32 + 16)]);
[ exact SI | exact MU2 | exact WM2 | exact MI2 | unfold own_iv; repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil | apply fsaved_refl | exact FRM
| exact LOC | exact LCK | exact ST2 | exact SL | exact FD2 | exists fj0, fj1; split; [exact FF0 | exact FF1] | exact FSH | exact LSH
| apply bytes_at_firstn; [exact (proj1 BYm) | lia] | rewrite firstn_length_le by lia; lia | exact P0 | exact P1 | lia ].
Qed.
#[using="Type"] Lemma rdepth_set_double_rootA : forall d r, rdepth (set_double_root d r) <= rdepth r.
Proof. clear. intros d r. destruct r as [|s| |]; cbn; try lia. pose proof (Q0Ek.sdepth_nonneg s). destruct s; cbn in *; lia. Qed.
#[using="Type"] Lemma rdepth_set_string_rootA : forall r, rdepth (set_string_root r) <= rdepth r.
Proof. clear. intros r. destruct r as [|s| |]; cbn; try lia. pose proof (Q0Ek.sdepth_nonneg s). destruct s; cbn in *; lia. Qed.
Definition hjA_fp1 := Eval vm_compute in match image_bytes asegs 0x10340 8 with Some bs => bs | None => [] end.
Definition hjA_fp2 := Eval vm_compute in match image_bytes asegs 0x10330 8 with Some bs => bs | None => [] end.
Lemma hjA_ro : forall m, mem_inv asegs m -> ro_cells asegs m 0x10340 [CB 8 hjA_fp1] /\ ro_cells asegs m 0x10330 [CB 8 hjA_fp2].
Proof.
intros m MI. split.
- change 8%nat with (length hjA_fp1). apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ]. change (Z.of_nat (length hjA_fp1)) with 8%Z. lia.
- change 8%nat with (length hjA_fp2). apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ]. change (Z.of_nat (length hjA_fp2)) with 8%Z. lia.
Qed.

#[using="CtxAll HINVA_callc EVDc OWNc GAOc set_callc SINVA_ownc SINVA_retc CA"] Lemma seg_setdoubleA : forall m md (A : ASA A4L HIx) B F fc ptr rem data r BS LK sb sd
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
SINVAc SHB0 m md A B F fc ptr rem data r BS LK sb sd ->
sb + JO_SETDBL_COSTB_A <= TGT_BB_A_jo -> sd + JO_SETDBL_COSTD_A <= TGT_BD_A_jo ->
KSBc (Fr + 32) (Fr + 128) 0x9213c SHB0 (set_double_root (fn_dbl_to_json_string A4F) r) (sb + JO_SETDBL_COSTB_A) (sd + JO_SETDBL_COSTD_A) ->
AJ5 A4L HIx A T md (sstateBc (Fr + 32) (Fr + 128) x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x9211c fc m).
Proof.
intros m md A B F fc ptr rem data r BS LK sb sd x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 SI CB CD K.
seg_open SI m.
assert (INCL : incl LB0 (BS ++ LK ++ LB0)) by (intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb).
destruct (EVDc A (BS ++ LK ++ LB0) B m md SHB0 ptr rem HP INCL FSH LSH ltac:(vm_compute; reflexivity) P1 P2) as (RTm & UNPm & UND).
pose proof (pds_of A (BS ++ LK ++ LB0) B m md ptr rem HP INCL P1 P2 ltac:(lia)) as PDS.
destruct (hjA_ro m MI) as [RO1 RO2].
pose proof (munch_refl [(sp1 - 64, sp1); (Fr + 32 + 8, Fr + 32 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
(let L := constr:(A4L) in reenterA asegs L HIx asegs_wx HP).
step. step. step. step. step. step.
clear RO1 RO2.
eapply evt_cut.
{ eapply QpNt.Mq5.cfp_A with (P := Fr + 32) (ptr := ptr) (rem := rem) (lo := lo) (data := data);
[ reflexivity | exact RTm | exact FD | exact UNPm | clear - FRAL; Z.div_mod_to_equations; lia | exact BY | exact L | exact P0 | exact UND
| rewrite unsigned_lit by lia; exact ST | exact LO | rewrite unsigned_lit by lia; lia | lia | lia | unfold A_SB, A_HMB; clear - FRAPPu; lia | lia | exact PDS | exact MI
| rewrite freg_get_same by reflexivity; vm_compute; reflexivity
| rewrite freg_get_other by (vm_compute; reflexivity); rewrite freg_get_same by reflexivity; vm_compute; reflexivity
| exact FRM ]. }
intros ms' (yt0 & yt1 & yt2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & yt3 & yt4 & yt5 & yt6 & F1 & fc1 & m1 & -> & FS1 & FRM1 & MU1 & WM1 & MI1 & FD1 & B1 & ST1).
unfold fdp_WSA in MU1. rewrite unsigned_lit in ST1, MU1 by lia.
replace (ret_pc (Z_to_bv 64 0x92134)) with (Z_to_bv 64 0x92134 : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
clear FD. stash FSH. transport_after_call asegs m m1 MU1 WM1. unstash FSH.
assert (SHFR : Fr + 504 <= sh \/ sh + 64 <= Fr) by (unfold sh; clear - FRAPPu FRLO; Z.div_mod_to_equations; lia).
apply (rw_cells_transport asegs [(sp1 - 64, sp1); (Fr + 32 + 8, Fr + 32 + 16)] m m1) in FSH; [| exact MU1 | exact WM1 | ].
2:{ cbn [disjoint_from cells_size csize Nat.add length map fst snd]. rewrite ?cells_size_C1, ?LSH. clear - SHR SHFR LO LOS ACR. lia. }
assert (SI1 : SINVAc SHB0 m1 md A B F1 fc1 ptr (Z.max (rem - 9) 0) (firstn (Z.to_nat (Z.max (rem - 9) 0)) data) r BS LK sb sd).
{ eapply (SINVA_ownc SHB0 SHB0 m m1) with (F := F) (W := [(sp1 - 64, sp1); (Fr + 32 + 8, Fr + 32 + 16)]);
[ exact SI | exact MU1 | exact WM1 | exact MI1 | unfold own_iv; repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil
| | exact FRM1 | exact LOC | exact LCK | exact ST1 | exact SL | exact FD1 | exists fj0, fj1; split; [exact FF0 | exact FF1] | exact FSH | exact LSH
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
split; [exact ST1|]; split; [exact LO|]; split; [lia|]; split; [clear - SPA1; Z.div_mod_to_equations; lia|]; split; [lia|];
split; [exact ERR1|]; split; [reflexivity | vm_compute; reflexivity]
| exact RR1 | lia | lia | reflexivity |].
intros ms' md' m' rv A' B' BS' (RS & VM' & ST' & HPR' & [errv' ERR']) [CHB CHD] ERRx RR' HP' BSEQ.
destruct RS as (xt0 & xt1 & xt2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & F' & fc' & -> & FS' & FRM').
rewrite unsigned_lit in ST', HPR' by lia.
replace (ret_pc (Z_to_bv 64 0x9213c)) with (Z_to_bv 64 0x9213c : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unfold KSB, sstateB in K. eapply K.
eapply SINVA_retc; [exact SI1 | exact HPR' | exact VM' | exact FS' | exact (FRM' FRM1) | exact ST' | exact HP' | exact RR' | | lia | lia | (destruct r as [|shq|tjq|]; [exact I | destruct shq; cbn [rootWm set_double_root] in BSEQ |- *; first [exact I | rewrite BSEQ; exact RW] | exact I | exact I])].
pose proof (rdepth_set_double_rootA (fn_dbl_to_json_string A4F) r). lia.
Qed.

#[using="CtxAll HINVA_callc EVDc FSLc OWNc GAOc"] Lemma crls_callB : forall (ret : Z) (g0 : nat) (s6v : Z) shb m md (A : ASA A4L HIx) B F fc ptr rem data r BS LK sb sd
(gp t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
0 <= ret < 2^64 -> ret mod 2 = 0 -> (g0 = 16%nat \/ g0 = 24%nat) -> 0 <= s6v < 2^64 ->
forallb (fun b => bv_unsigned b =? 0) (firstn 3 (skipn g0 shb)) = true ->
forallb (fun b => bv_unsigned b =? 0) (firstn 2 (skipn 4 shb)) = true ->
SINVAc shb m md A B F fc ptr rem data r BS LK sb sd ->
(forall m' md' (A' : ASA A4L HIx) ptr' rem' data' (n : Z) (str rest : list byte) (xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
SINVAc shb m' md' A' B F fc ptr' rem' data' r BS LK sb sd ->
rw_cells asegs m' (Fr + 8 * Z.of_nat g0) [C1 (Z_to_bv 8 (2 * n)); CB 23 (str ++ Z_to_bv 8 0 :: rest)] ->
0 <= n <= 10 -> Z.of_nat (length str) <= n -> ~ In (Z_to_bv 8 0) str -> mem_inv asegs m' ->
AJ5 A4L HIx A' T md' (sstateBc (Fr + 32) s6v (Z_to_bv 64 ret) gp xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 F ret fc m')) ->
AJ5 A4L HIx A T md (sstateBc (Fr + 32) s6v (Z_to_bv 64 ret) gp t0 t1 t2 (Z_to_bv 64 (Fr + 8 * Z.of_nat g0)) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 10) a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x92528 fc m).
Proof.
intros ret g0 s6v shb m md A B F fc ptr rem data r BS LK sb sd gp t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Hret Hret2 Hg0 Hs6 SHZ SH45 SI K.
seg_open SI m.
assert (INCL : incl LB0 (BS ++ LK ++ LB0)) by (intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb).
destruct (EVDc A (BS ++ LK ++ LB0) B m md shb ptr rem HP INCL FSH LSH SH45 P1 P2) as (RTm & UNPm & UND).
set (S := Fr + 8 * Z.of_nat g0) in *.
assert (HS : S = Fr + 128 \/ S = Fr + 192) by (subst S; destruct Hg0 as [-> | ->]; [left | right]; reflexivity).
assert (UNSm : unpoisoned asegs m A_SB S 24).
{ pose proof (FSLc m shb g0 (g0 + 3)%nat FSH LSH ltac:(lia) ltac:(lia) ltac:(replace (g0 + 3 - g0)%nat with 3%nat by lia; exact SHZ)) as U.
replace (8 * Z.of_nat (g0 + 3 - g0)) with 24 in U by lia. exact U. }
assert (INF : In (Fr, 3) [(Fr, 3)]) by (left; reflexivity).
pose proof (pds_of A (BS ++ LK ++ LB0) B m md ptr rem HP INCL P1 P2 ltac:(lia)) as PDS.

destruct (rw_cells_CB_cut asegs _ _ _ _ (Z.to_nat (S - (Fr + 48))) FF1 ltac:(lia)) as [FA FB']. rewrite Z2Nat.id in FB' by lia.
replace (Fr + 48 + (S - (Fr + 48))) with S in FB' by lia.
destruct (rw_cells_CB_cut asegs _ _ _ _ 24 FB' ltac:(lia)) as [S1 FB]. clear FB'. change (Z.of_nat 24) with 24 in FB.
clear FF1.
eapply (QnX9.crls_A HIx) with (S := S) (P := Fr + 32) (ptr := ptr) (rem := rem) (lo := lo) (maxlen := 10) (data := data) (LB := BS ++ LK ++ LB0) (LM := LM) (FRS := [(Fr, 3)]) (B := B);
rewrite ?unsigned_lit by lia;
first [ reflexivity | exact HP | exact S1 | exact UNSm | exact FD | exact UNPm | exact BY | exact L | exact P0 | exact LO | exact SPA1 | exact MI | exact ST
| idtac ].
all: lazymatch goal with |- forall _, _ => idtac | |- _ => try solve [ lia | cbn [length]; lia | subst S; clear - FRAL Hg0; destruct Hg0 as [-> | ->]; Z.div_mod_to_equations; lia
| clear - FRAL; Z.div_mod_to_equations; lia | unfold QnX9.CRLS_STK_B; lia
| exists Fr, 3; split; [left; reflexivity | rewrite fr_size_3; lia]
| destruct INB as [Z0 | INB']; [left; exact Z0 | right; exists data0, size; split; [apply INCL; exact INB' | lia]]
| destruct PDS as [Z0 | PD]; [left; exact Z0 | right; lia] ] end.
1: { destruct INB as [Z0 | INB']; [left; clear - Z0 P1 P2 L; lia | right]. exists data0, size. split; [apply in_or_app; right; apply in_or_app; right; exact INB' | lia]. }
1: { destruct (Z.eq_dec rem 0) as [R0 | RN]; [left; exact R0 | right]. destruct INB as [Z0 | INB']; [exfalso; clear - Z0 P1 P2 L RN; lia|].
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF (in_or_app _ _ _ (or_introl (INCL _ INB')))) as DF. rewrite fr_size_3 in DF. clear - DF P1 P2 HS SZ RN L. lia. }
intros ms3 m3 md3 A3 n1 k1 str1 rest1 yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 -> VM3 ST3 PRES3 HP3 MI3 Hn1 Hstr1 NONUL1 STR3 Hk1 FD3 PAY3.
replace (ret_pc (Z_to_bv 64 ret)) with (Z_to_bv 64 ret : word) by (symmetry; apply ret_pc_even; [lia | exact Hret2]).
clear S1 FD BY UNSm UNPm UND RTm.

unfold QnX9.crls_presB in PRES3.
assert (INFR : In (Fr, 504) ((BS ++ LK ++ LB0) ++ LM ++ fr_ivs A4L [(Fr, 3)])) by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
assert (INSH : In (sh, 64) ((BS ++ LK ++ LB0) ++ LM ++ fr_ivs A4L [(Fr, 3)])) by (apply in_or_app; right; apply in_or_app; right; right; left; reflexivity).
assert (SHFR : Fr + 504 <= sh \/ sh + 64 <= Fr) by (unfold sh; clear - FRAPPu FRLO; Z.div_mod_to_equations; lia).
assert (LOCcs : forall a, 6444320 - 48 <= a < 6444320 - 48 + 8 -> hl_client_static A4H a) by (intros a Ha; cbn [hl_client_static A4H]; unfold a4_client_static; lia).
apply (presB_rw_cells_gen _ _ _ _ _ _ _ _ PRES3) in FF0; [| right; right; exists (Fr, 504); split; [exact INFR | cbn; lia] | cbn; lia | cbn; lia].
apply (presB_rw_cells_gen _ _ _ _ _ _ _ _ PRES3) in FA; [| right; right; exists (Fr, 504); split; [exact INFR | cbn; lia] | cbn [cells_size csize Nat.add]; rewrite ?Z2Nat.id by lia; clear - HS; lia | cbn [cells_size csize Nat.add]; rewrite ?Z2Nat.id by lia; clear - HS; lia].
apply (presB_rw_cells_gen _ _ _ _ _ _ _ _ PRES3) in FB; [| right; right; exists (Fr, 504); split; [exact INFR | cbn; lia] | cbn; lia | cbn; lia].
apply (presB_rw_cells_gen _ _ _ _ _ _ _ _ PRES3) in FSH; [| right; right; exists (sh, 64); split; [exact INSH | rewrite cells_size_C1, LSH; cbn; lia] | rewrite cells_size_C1, LSH; clear - SHFR HS; lia | rewrite cells_size_C1, LSH; clear - SHFR HS; lia].
apply (presB_rw_cells_gen _ _ _ _ _ _ _ _ PRES3) in SL; [| left; cbn; lia | cbn; lia | cbn; lia].
apply (presB_rw_cells_gen _ _ _ _ _ _ _ _ PRES3) in LOC; [| right; left; cbn; intros z Hz; apply LOCcs; lia | cbn; lia | cbn; lia].
apply (presB_rw_cells_gen _ _ _ _ _ _ _ _ PRES3) in LCK; [| right; left; cbn; intros z Hz; cbn [hl_client_static A4H]; unfold a4_client_static; lia | cbn; lia | cbn; lia].
assert (GA3 : GA_jo m3).
{ destruct (proj1 G) as (GH & [seed GS]).
apply (presB_rw_cells_gen _ _ _ _ _ _ _ _ PRES3) in GH; [| right; left; cbn; intros z Hz; cbn [hl_client_static A4H]; unfold a4_client_static; unfold GHASHA in Hz; lia | cbn; unfold GHASHA; lia | cbn; unfold GHASHA; lia].
apply (presB_rw_cells_gen _ _ _ _ _ _ _ _ PRES3) in GS; [| right; left; cbn; intros z Hz; cbn [hl_client_static A4H]; unfold a4_client_static; unfold GSEEDA in Hz; lia | cbn; unfold GSEEDA; lia | cbn; unfold GSEEDA; lia].
eapply GA_jo_pointwise; [exact G | split; [exact GH | exists seed; exact GS] |].
intros a Ha. apply (PRES3 a); [lia | right; left; cbn [hl_client_static A4H]; unfold a4_client_static; lia | lia | lia]. }
assert (PX3 : heap_presx A4H (xtgt_A (bv_unsigned sp0)) (LB0 ++ LM) (sp1 + 8) m0 m3).
{ eapply heap_presx_trans; [exact PX |].
intros a Ha CAx.
assert (NSP : ~ (S <= a < S + 24) /\ ~ (Fr + 32 <= a < Fr + 32 + 16)).
{ destruct CAx as [H | [[H _] | ((ba & bn) & Hb & Hr)]].
- clear - H LO LOS FRHI HS. lia.
- cbn [hl_client_static A4H] in H. unfold a4_client_static in H. clear - H FRLO HS. lia.
- pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP3 INF ltac:(apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply INCL; exact Hb | right; exact Hb])) as DF.
rewrite fr_size_3 in DF. cbn [blk_addr blk_size fst snd] in Hr. clear - DF Hr HS. lia. }
destruct NSP as [NS NP].
exact (PRES3 a Ha ltac:(destruct CAx as [H | [[H _] | H]]; [left; clear - H; lia | right; left; exact H | right; right; unfold in_block in H |- *; destruct H as (b & Hb & Hr); exists b; split; [apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply INCL; exact Hb | right; apply in_or_app; left; exact Hb] | exact Hr]]) NS NP). }

assert (FJ1 : exists fj', rw_cells asegs m3 (Fr + 48) [CB 456 fj']).
{ lazymatch type of STR3 with rw_cells _ _ _ ?c3 => lazymatch type of FB with rw_cells _ _ _ ?c4 =>
assert (X1 : rw_cells asegs m3 S (c3 ++ c4)) by (apply (proj2 (rw_cells_app asegs m3 S c3 c4)); split; [exact STR3 | cbn [cells_size csize Nat.add]; change (Z.of_nat 24) with 24; exact FB]) end end.
lazymatch type of FA with rw_cells _ _ _ ?c1 => lazymatch type of X1 with rw_cells _ _ _ ?c34 =>
assert (X3 : rw_cells asegs m3 (Fr + 48) (c1 ++ c34)) by (apply (proj2 (rw_cells_app asegs m3 (Fr + 48) c1 c34)); split; [exact FA | cbn [cells_size csize Nat.add]; rewrite ?Nat.add_0_r, ?Z2Nat.id by lia; replace (Fr + 48 + (S - (Fr + 48))) with S by lia; exact X1]) end end.
lazymatch type of X3 with rw_cells _ _ _ ?cs => change (rw_cells asegs m3 (Fr + 48) ([] ++ cs ++ [])) in X3 end.
apply rw_cells_merge in X3. cbn [app] in X3.
lazymatch type of X3 with rw_cells _ _ _ [CB ?n ?b] => exists b; replace 456%nat with n; [exact X3 |] end.
cbn [cells_size csize Nat.add]. clear - HS. destruct HS as [-> | ->]; [replace (Fr + 128 - (Fr + 48)) with 80 by lia | replace (Fr + 192 - (Fr + 48)) with 144 by lia]; reflexivity. }
destruct FJ1 as [fj1' FJ1].
pose proof (bytes_at_skipn asegs m3 ptr data k1 PAY3 ltac:(lia)) as WIN3.
assert (AG3 : agree_on asegs (BS ++ LK ++ LB0) m m3).
{ intros a Ha (b & Hb & Hr). destruct b as [ba bn]. cbn [blk_addr blk_size fst snd] in Hr.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF (in_or_app _ _ _ (or_introl Hb))) as DF. rewrite fr_size_3 in DF.
apply (PRES3 a Ha); [right; right; exists (ba, bn); split; [apply in_or_app; left; exact Hb | exact Hr] | clear - DF Hr HS; lia | clear - DF Hr; lia]. }
eapply (K m3 md3 A3 (ptr + k1) (rem - k1) (skipn (Z.to_nat k1) data) n1 str1 rest1); [| exact STR3 | lia | exact Hstr1 | exact NONUL1 | exact MI3].
split; [| split; [exact HP3 | split; [| split; [exact RD | split; [exact BB | split; [exact BD | exact RW]]]]]].
- unfold HINVA. split; [exact PX3|]. split; [eapply model_vm_only_trans; [exact VM | exact VM3]|]. split; [exact FS|]. split; [exact FRM|].
split; [exact LOC|]. split; [exact LCK|]. split; [exact GA3|]. split; [exact ST3|]. split; [exact SL|]. split; [exact FD3|].
split; [exists fj0, fj1'; split; [exact FF0 | exact FJ1]|]. split; [exact FSH|]. split; [exact LSH|].
split; [exact WIN3|]. split; [rewrite length_skipn; lia|]. lia.
- eapply (QrIB.Mq0.jroot_rep_agree A4H A4F r m m3 BS (BS ++ LK ++ LB0)); [exact RR | exact AG3 | intros b Hb; apply in_or_app; left; exact Hb].
Qed.
#[using="CtxAll HINVA_callc EVDc FSLc OWNc GAOc set_callc SINVA_ownc SINVA_retc CA"] Lemma seg_setstringA : forall m md (A : ASA A4L HIx) B F fc ptr rem data r BS LK sb sd
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
SINVAc SHB0 m md A B F fc ptr rem data r BS LK sb sd ->
sb + 1200 <= TGT_BB_A_jo -> sd + JO_SETSTR_COSTD_A <= TGT_BD_A_jo ->
KSBc (Fr + 32) (Fr + 128) 0x921a4 SHB0 (set_string_root r) (sb + 1200) (sd + JO_SETSTR_COSTD_A) ->
AJ5 A4L HIx A T md (sstateBc (Fr + 32) (Fr + 128) x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x9213c fc m).
Proof.
intros m md A B F fc ptr rem data r BS LK sb sd x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 SI CB CD K.
seg_open SI m.
assert (WOK : Forall (own_iv sp1 lo Fr) [(lo, sp1 + 8); (Fr, Fr + 504); (sh, sh + 64)]) by (unfold own_iv, sh; repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil).
pose proof (munch_refl [(lo, sp1 + 8); (Fr, Fr + 504); (sh, sh + 64)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold SHB0 in FSH. cbn [map app repeat] in FSH.
(let L := constr:(A4L) in reenterA asegs L HIx asegs_wx HP).
do 3 stepz. step. step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m2 end.
lazymatch goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
assert (SI2 : SINVAc SHB2 m2 md A B F fc ptr rem data r BS LK sb sd).
{ let cs := eval cbv in (map C1 SHB2) in apply (rw_cells_recast asegs m2 sh _ cs) in FSH; [| cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity].
eapply (SINVA_ownc SHB0 SHB2 m m2);
[ exact SI | exact MU | exact WM | exact MI2 | exact WOK | apply fsaved_refl | exact FRM | exact LOC | exact LCK | eassumption | eassumption | eassumption
| exists fj0, fj1; split; eassumption | exact FSH | reflexivity | exact (proj1 BYm) | exact L | exact P0 | exact P1 | exact P2 ]. }
evt_done5.
replace (Fr + 128) with (Fr + 8 * Z.of_nat 16) at 2 by lia.
eapply (crls_callB 0x92158 16%nat (Fr + 128) SHB2 m2); [lia | reflexivity | left; reflexivity | lia | vm_compute; reflexivity | vm_compute; reflexivity | exact SI2 |].
clear - K CB CD LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP BB0 BD0 CA HINVA_callc EVDc FSLc OWNc GAOc set_callc SINVA_ownc SINVA_retc.
intros m3 md3 A3 ptr3 rem3 data3 n3 str3 rest3 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 SI3 STR3 Hn3 Hstr3 NONUL3 MI3.
change (Fr + 8 * Z.of_nat 16) with (Fr + 128) in STR3.
pose proof SI3 as ((PX3 & VM3 & FS3 & FRM3 & LOC3 & LCK3 & G3 & ST3 & _ & _ & _ & FSH3 & LSH3 & _ & _ & _ & _ & _) & HP3 & RR3 & RD3 & BB3 & BD3 & RW3).
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP3) as (errv3 & ERR3). cbn [hl_tp hl_segs A4L A4H hla_base] in ERR3. unfold A_TP in ERR3.
pose proof alloc_ceiling_range as ACR. pose proof (hiA_top_le A4L HIx) as HT47.
pose proof (bv_unsigned_in_range 64 sp0) as SP0R. change (bv_modulus 64) with (2^64) in SP0R.
assert (UNS3 : unpoisoned asegs m3 A_SB (Fr + 128) 24).
{ pose proof (FSLc m3 SHB2 16%nat 19%nat FSH3 LSH3 ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)) as U. change (Fr + 8 * Z.of_nat 16) with (Fr + 128) in U. exact U. }
assert (LREST : Z.of_nat (length rest3) = 22 - Z.of_nat (length str3)).
{ destruct STR3 as [[WF _] _]. cbn in WF. rewrite length_app in WF. cbn [length] in WF. lia. }
pose proof STR3 as STRB. apply rw_cells_app with (cs1 := [_]) in STRB as [_ STRB]. cbn [cells_size csize Nat.add] in STRB.
pose proof (rw_cells_bytes_at asegs m3 _ _ STRB) as SB. cbn [cells_bytes cbytes app] in SB. rewrite app_nil_r in SB.
change (Fr + 128 + Z.of_nat 1) with (Fr + 128 + 1) in SB. clear STRB FSH3.
pose proof (munch_refl (@nil (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
unfold sstateB, A_TP.
reenterA asegs A4L HIx asegs_wx HP3.
step. step. rewrite short_flag0A by lia. step. if_false. step. step. step. step.
evt_done5.
pose proof (ca_SETS _ _ _ _ _ _ _ CA) as SS. unfold jo_set_string_A_stmt, JO_SET_STRING_A, JO_SETSTR_STK_A, jo_setstr_costB in SS. unfold JO_SETSTR_COSTD_A in *.
eapply SS with (A := A3) (BS := BS) (LB := LK ++ LB0) (FRS := [(Fr, 3)]) (B := B) (lo := lo) (p := p) (S := Fr + 128 + 1) (sb := str3) (slack := rest3) (r := r) (errv := errv3).
- split; [exact HP3|]. rewrite unsigned_lit by lia.
split; [exact ST3|]. split; [exact LO|]. split; [lia|]. split; [clear - SPA1; Z.div_mod_to_equations; lia|]. split; [lia|].
split; [exact ERR3|]. split; [reflexivity | vm_compute; reflexivity].
- exact RR3.
- split; [exact SB|]. split; [apply Forall_forall; intros b Hb E0; apply NONUL3; replace (Z_to_bv 8 0) with b by (apply bv_eq; rewrite E0; reflexivity); exact Hb|].
split; [rewrite LREST; clear - FRAL Hstr3 Hn3; Z.div_mod_to_equations; lia|].
split; [exists Fr, 3; split; [left; reflexivity|]; rewrite fr_size_3; lia|].
eapply (QsKa.Mqa.unpoisoned_sub_any asegs _ A_SB (Fr + 128) 24); [exact UNS3 | lia | lia | lia].
- lia.
- lia.
- lia.
- reflexivity.
- f_equal. lia.
- unfold set_string_postA.
intros ms4 md4 m4 rv4 A4 B4 BS4 (RS4 & VM4 & ST4 & HPR4 & [errv4 ERR4]) [CHB4 CHD4] RR4 HP4 SLEN4 BSEQ4.
destruct RS4 as (zt0 & zt1 & zt2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 & F4 & fc4 & -> & FS4 & FRM4).
rewrite unsigned_lit in ST4, HPR4 by lia.
replace (ret_pc (Z_to_bv 64 0x92178)) with (Z_to_bv 64 0x92178 : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
assert (SI4 : SINVAc SHB2 m4 md4 A4 B4 F4 fc4 ptr3 rem3 data3 (set_string_root r) BS4 LK (sb + 1200) (sd + 2)).
{ eapply SINVA_retc; [exact SI3 | exact HPR4 | exact VM4 | exact FS4 | exact (FRM4 FRM3) | exact ST4 | exact HP4 | exact RR4 | | lia | lia | (destruct r as [|shq|tjq|]; [exact I | destruct shq; cbn [rootWm set_string_root is_string_root] in BSEQ4 |- *; first [exact I | rewrite (BSEQ4 eq_refl); exact RW3] | exact I | exact I])].
pose proof (rdepth_set_string_rootA r). lia. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in STR3;
[| eapply (client_range_block A4H _ _ _ _ Fr 504); [apply in_or_app; right; apply in_or_app; right; left; reflexivity | lia | cbn [cells_size csize Nat.add]; lia]].
change (hl_segs A4H) with asegs in *.
clear SI3 HP3 RR3 SB UNS3 ERR3 MU WM MI3 PX3 VM3 FS3 LOC3 LCK3 G3 ST3.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI4. change (hl_segs A4L) with asegs in MI4.
pose proof (munch_refl (@nil (Z * Z)) m4) as MU. pose proof (wmono_refl asegs m4) as WM.
reenterA asegs A4L HIx asegs_wx HP4. change (hl_segs A4H) with asegs.
step. step. rewrite short_flag0A by lia. step. if_true.
step.
clear STR3 MU WM.
pose proof SI4 as ((_ & _ & _ & _ & LOC4 & LCK4 & _ & _ & SL4 & FD4 & (fj04 & fj14 & FF04 & FF14) & FSH4 & _ & BY4 & L4 & P04 & P14 & P24) & _).
unfold T_LOCCELL_A, T_LOCALE_LOCK_A, A_TP in LOC4, LCK4. unfold SHB2, SHB0 in FSH4. cbn [map app firstn skipn repeat] in FSH4.
fold sh in FSH4.
assert (SHR4 : 2147450880 <= sh /\ sh + 64 <= 17594333495296) by (unfold sh; clear - FRLO FRHI ACR; Z.div_mod_to_equations; lia).
pose proof FRAPP as FRAPPu. unfold A_SB, A_HMB in FRAPPu.
assert (BYm4 : bytes_at asegs m4 ptr3 data3 /\ True) by (split; [exact BY4 | exact I]). clear BY4.
assert (WOK : Forall (own_iv sp1 lo Fr) [(lo, sp1 + 8); (Fr, Fr + 504); (sh, sh + 64)]) by (unfold own_iv, sh; repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil).
pose proof (munch_refl [(lo, sp1 + 8); (Fr, Fr + 504); (sh, sh + 64)] m4) as MU. pose proof (wmono_refl asegs m4) as WM.
fold sh.
do 3 stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m5 end.
lazymatch goal with H : mem_inv asegs m5 |- _ => rename H into MI5 end.
let cs := eval cbv in (map C1 SHB0) in apply (rw_cells_recast asegs m5 sh _ cs) in FSH4; [| cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity].
evt_done5.
unfold KSB, sstateB in K. fold sh in K. eapply K.
eapply (SINVA_ownc SHB2 SHB0 m4 m5);
[ exact SI4 | exact MU | exact WM | exact MI5 | exact WOK | apply fsaved_refl | exact (FRM4 FRM3) | exact LOC4 | exact LCK4 | eassumption | exact SL4 | exact FD4
| exists fj04, fj14; split; [exact FF04 | exact FF14] | exact FSH4 | reflexivity | exact (proj1 BYm4) | exact L4 | exact P04 | exact P14 | exact P24 ].
Qed.

#[using="CtxAll HINVA_callc EVDc OWNc GAOc set_callc SINVA_ownc CA"] Lemma seg_setboolA : forall m md (A : ASA A4L HIx) B F fc ptr rem data r BS LK sb sd
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
SINVAc SHB0 m md A B F fc ptr rem data r BS LK sb sd ->
KSBc (Fr + 32) (Fr + 192) 0x92200 SHB0 r sb sd ->
AJ5 A4L HIx A T md (sstateBc (Fr + 32) (Fr + 128) x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x921a4 fc m).
Proof.
intros m md A B F fc ptr rem data r BS LK sb sd x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 SI K.
seg_open SI m.
assert (INCL : incl LB0 (BS ++ LK ++ LB0)) by (intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb).
destruct (EVDc A (BS ++ LK ++ LB0) B m md SHB0 ptr rem HP INCL FSH LSH ltac:(vm_compute; reflexivity) P1 P2) as (_ & UNP & UND).
pose proof (pds_of A (BS ++ LK ++ LB0) B m md ptr rem HP INCL P1 P2 ltac:(lia)) as PDS.
pose proof (bytes_at_bound _ _ _ _ BY) as DB.
assert (WAPP : Forall (fun iv : Z * Z => snd iv <= A_SB \/ A_HMB <= fst iv) [(Fr + 32 + 8, Fr + 32 + 16)]).
{ unfold A_SB, A_HMB. apply Forall_cons; [cbn [fst snd]; clear - FRAPPu; lia | apply Forall_nil]. }
pose proof (munch_refl [(Fr + 32 + 8, Fr + 32 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
(let L := constr:(A4L) in reenterA asegs L HIx asegs_wx HP).
assert (EXITK : forall (mc : word -> option byte) (ya0 ya1 ya2 ya3 : word) (c : Z),
rw_cells asegs mc (Fr + 32) [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 c)] -> c = Z.max (rem - 1) 0 ->
munch [(Fr + 32 + 8, Fr + 32 + 16)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
evt asegs (AJ5e A4L HIx A T md)
(MS (mkR x1 (Z_to_bv 64 sp1) gp (Z_to_bv 64 6444320) t0 t1 t2 sp0 (Z_to_bv 64 sp1) ya0 ya1 ya2 ya3 a4 a5 a6 a7
(Z_to_bv 64 sh) (Z_to_bv 64 Fr) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 p) (Z_to_bv 64 (Fr + 128)) (Z_to_bv 64 (Fr + 64))
(Z_to_bv 64 Fr) (Z_to_bv 64 2147450880) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x921f4) fc None mc (seg_rom asegs))).
{ intros mc ya0 ya1 ya2 ya3 c FDc Hc MUc WMc MIc.
clear FD MU WM. stash FSH. transport_after_call asegs m mc MUc WMc. unstash FSH.
assert (SHFR : Fr + 504 <= sh \/ sh + 64 <= Fr) by (unfold sh; clear - FRAPPu FRLO; Z.div_mod_to_equations; lia).
apply (rw_cells_transport asegs [(Fr + 32 + 8, Fr + 32 + 16)] m mc) in FSH; [| exact MUc | exact WMc | ].
2:{ cbn [disjoint_from cells_size csize Nat.add length map fst snd]. rewrite ?cells_size_C1, ?LSH. clear - SHFR. lia. }
step. step. step.
evt_done5.
eapply (set_callc 0x9db50 0x92200 (Fr + 32) (Fr + 192)); [exact (ca_SETB _ _ _ _ _ _ _ CA) | lia | reflexivity | lia | lia | | exact K].
eapply (SINVA_ownc SHB0 SHB0 m mc) with (ptr' := ptr) (rem' := c) (data' := firstn (Z.to_nat c) data) (W := [(Fr + 32 + 8, Fr + 32 + 16)]);
[ exact SI | exact MUc | exact WMc | exact MIc | unfold own_iv; apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil] | apply fsaved_refl | exact FRM
| exact LOC | exact LCK | exact ST | exact SL | exact FDc | exists fj0, fj1; split; [exact FF0 | exact FF1] | exact FSH | exact LSH
| apply bytes_at_firstn; [exact (proj1 BYm) | lia] | rewrite firstn_length_le by lia; lia | exact P0 | exact P1 | lia ]. }
step.
destruct (Z.eq_dec rem 0) as [R0 | RN].
{ rewrite R0. step. if_true. step.
eapply EXITK with (c := rem); [exact FD | lia | exact MU | exact WM | exact MI]. }
step. if_falsex.
step. step. step.
stepz.
step. if_falsex.
step. step. step. step. ub_resolve.
step. if_falsex.
lazymatch goal with MUd : munch _ m ?md' |- evt _ _ (MS _ _ _ _ _ ?md' _) =>
assert (UNDd : unpoisoned asegs md' A_SB ptr rem) by (eapply unpoisoned_keep; [exact (UND ltac:(lia)) | exact MUd | lia | lia | exact WAPP]);
pose proof BY as BYd;
destruct (unpoisoned_byte_ro md' ptr rem (ptr + (rem + -1)) UNDd ltac:(lia)) as (v1 & SHK & Hv1) end.
destruct (nth_error data (Z.to_nat (rem - 1))) as [b1|] eqn:Hb1; [| exfalso; apply nth_error_None in Hb1; lia].
pose proof (bv_unsigned_in_range 8 b1) as BR1. unfold bv_modulus in BR1. cbn in BR1.
step. step. sh_norm. step. step.
lazymatch goal with |- evt _ ?Q (MS _ _ _ _ _ ?mm _) =>
assert (BE0 : forall (za1 za2 za3 : word),
evt asegs Q (MS (mkR x1 (Z_to_bv 64 sp1) gp (Z_to_bv 64 6444320) t0 t1 t2 sp0 (Z_to_bv 64 sp1) (Z_to_bv 64 (ptr + (rem + -1))) za1 za2 za3 a4 a5 a6 a7
(Z_to_bv 64 sh) (Z_to_bv 64 Fr) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 p) (Z_to_bv 64 (Fr + 128)) (Z_to_bv 64 (Fr + 64))
(Z_to_bv 64 Fr) (Z_to_bv 64 2147450880) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x921e4) fc None mm (seg_rom asegs))) end.
2:{ destruct Hv1 as [-> | [Hv8 Hvm]].
- rewrite sxb_zero. if_false. apply BE0.
- rewrite (QsKa.Mqa.sxb_small v1) by lia. if_truex. step. step.
rewrite (unsigned_lit (ptr + (rem + -1))) by lia. rewrite QsKa.Mqa.land7_mod8 by lia. if_truex. apply BE0. }
intros za1 za2 za3. clear SHK v1 Hv1 UNDd.
pose proof (u8ro_read asegs _ ptr data (rem - 1) b1 _ BYd Hb1 ltac:(lia) eq_refl) as RD1.
replace (ptr + (rem - 1)) with (ptr + (rem + -1)) in RD1 by lia.
step. clear RD1.
step. step.
lazymatch goal with H : rw_cells asegs ?mx (Fr + 32) _ |- _ => rename H into FD3 end.
eapply EXITK with (c := rem + -1); [exact FD3 | lia | eassumption | eassumption | eassumption].
Qed.
#[using="CtxAll HINVA_callc EVDc FSLc OWNc GAOc set_callc SINVA_ownc SINVA_retc CA"] Lemma seg_setstrlenA : forall m md (A : ASA A4L HIx) B F fc ptr rem data r BS LK sb sd
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
SINVAc SHB0 m md A B F fc ptr rem data r BS LK sb sd ->
sb + 1200 <= TGT_BB_A_jo -> sd + JO_SETSTR_COSTD_A <= TGT_BD_A_jo ->
KSFAc 0x92248 (set_string_root r) (sb + 1200) (sd + JO_SETSTR_COSTD_A) ->
AJ5 A4L HIx A T md (sstateBc (Fr + 32) (Fr + 192) x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x92200 fc m).
Proof.
intros m md A B F fc ptr rem data r BS LK sb sd x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 SI CB CD K.
seg_open SI m.
assert (WOK : Forall (own_iv sp1 lo Fr) [(lo, sp1 + 8); (Fr, Fr + 504); (sh, sh + 64)]) by (unfold own_iv, sh; repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil).
pose proof (munch_refl [(lo, sp1 + 8); (Fr, Fr + 504); (sh, sh + 64)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold SHB0 in FSH. cbn [map app repeat] in FSH.
(let L := constr:(A4L) in reenterA asegs L HIx asegs_wx HP).
do 3 stepz. step. step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m2 end.
lazymatch goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
assert (SI2 : SINVAc SHB3 m2 md A B F fc ptr rem data r BS LK sb sd).
{ let cs := eval cbv in (map C1 SHB3) in apply (rw_cells_recast asegs m2 sh _ cs) in FSH; [| cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity].
eapply (SINVA_ownc SHB0 SHB3 m m2);
[ exact SI | exact MU | exact WM | exact MI2 | exact WOK | apply fsaved_refl | exact FRM | exact LOC | exact LCK | eassumption | eassumption | eassumption
| exists fj0, fj1; split; eassumption | exact FSH | reflexivity | exact (proj1 BYm) | exact L | exact P0 | exact P1 | exact P2 ]. }
evt_done5.
replace (Fr + 192) with (Fr + 8 * Z.of_nat 24) at 2 by lia.
eapply (crls_callB 0x9221c 24%nat (Fr + 192) SHB3 m2); [lia | reflexivity | right; reflexivity | lia | vm_compute; reflexivity | vm_compute; reflexivity | exact SI2 |].
clear - K CB CD LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP BB0 BD0 CA HINVA_callc EVDc FSLc OWNc GAOc set_callc SINVA_ownc SINVA_retc.
intros m3 md3 A3 ptr3 rem3 data3 n3 str3 rest3 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 SI3 STR3 Hn3 Hstr3 NONUL3 MI3.
change (Fr + 8 * Z.of_nat 24) with (Fr + 192) in STR3.
pose proof SI3 as ((PX3 & VM3 & FS3 & FRM3 & LOC3 & LCK3 & G3 & ST3 & _ & _ & _ & FSH3 & LSH3 & _ & _ & _ & _ & _) & HP3 & RR3 & RD3 & BB3 & BD3 & RW3).
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP3) as (errv3 & ERR3). cbn [hl_tp hl_segs A4L A4H hla_base] in ERR3. unfold A_TP in ERR3.
pose proof alloc_ceiling_range as ACR. pose proof (hiA_top_le A4L HIx) as HT47.
pose proof (bv_unsigned_in_range 64 sp0) as SP0R. change (bv_modulus 64) with (2^64) in SP0R.
assert (UNS3 : unpoisoned asegs m3 A_SB (Fr + 192) 24).
{ pose proof (FSLc m3 SHB3 24%nat 27%nat FSH3 LSH3 ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)) as U. change (Fr + 8 * Z.of_nat 24) with (Fr + 192) in U. exact U. }
assert (L23 : length (str3 ++ Z_to_bv 8 0 :: rest3) = 23%nat) by (destruct STR3 as [[WF _] _]; cbn in WF; lia).
pose proof STR3 as STRB. apply rw_cells_app with (cs1 := [_]) in STRB as [_ STRB]. cbn [cells_size csize Nat.add] in STRB.
pose proof (rw_cells_bytes_at asegs m3 _ _ STRB) as SB. cbn [cells_bytes cbytes app] in SB. rewrite app_nil_r in SB.
change (Fr + 192 + Z.of_nat 1) with (Fr + 192 + 1) in SB. clear STRB FSH3.
pose proof (bytes_at_firstn asegs m3 _ _ n3 SB ltac:(lia)) as SBn.
pose proof (munch_refl (@nil (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
unfold sstateB, A_TP.
reenterA asegs A4L HIx asegs_wx HP3.
step. step. rewrite short_flag0A by lia. step. if_false. step. step. rewrite short_sizeA by lia. step. step. step. step.
rewrite (unsigned_lit n3) by lia. rewrite Z.add_0_r. rewrite (swrap32_id n3) by lia.
evt_done5.
pose proof (ca_SETSL _ _ _ _ _ _ _ CA) as SS. unfold jo_set_string_len_A_stmt, JO_SET_STRING_LEN_A, JO_SETSTR_STK_A, jo_setstr_costB in SS. unfold JO_SETSTR_COSTD_A in *.
assert (LSB : Z.of_nat (length (firstn (Z.to_nat n3) (str3 ++ Z_to_bv 8 0 :: rest3))) = n3) by (rewrite firstn_length_le by lia; lia).
eapply SS with (A := A3) (BS := BS) (LB := LK ++ LB0) (FRS := [(Fr, 3)]) (B := B) (lo := lo) (p := p) (S := Fr + 192 + 1) (sb := firstn (Z.to_nat n3) (str3 ++ Z_to_bv 8 0 :: rest3)) (r := r) (errv := errv3).
- split; [exact HP3|]. rewrite unsigned_lit by lia.
split; [exact ST3|]. split; [exact LO|]. split; [lia|]. split; [clear - SPA1; Z.div_mod_to_equations; lia|]. split; [lia|].
split; [exact ERR3|]. split; [reflexivity | vm_compute; reflexivity].
- exact RR3.
- split; [exact SBn|]. split; [exists Fr, 3; split; [left; reflexivity|]; rewrite fr_size_3; lia|].
intros NE. rewrite LSB. assert (0 < n3) by (destruct (Z.eq_dec n3 0) as [E|]; [| lia]; exfalso; apply NE; rewrite E; reflexivity).
eapply (QsKa.Mqa.unpoisoned_sub_any asegs _ A_SB (Fr + 192) 24); [exact UNS3 | lia | lia | lia].
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
replace (ret_pc (Z_to_bv 64 0x92248)) with (Z_to_bv 64 0x92248 : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
assert (SI4 : SINVAc SHB3 m4 md4 A4 B4 F4 fc4 ptr3 rem3 data3 (set_string_root r) BS4 LK (sb + 1200) (sd + 2)).
{ eapply SINVA_retc; [exact SI3 | exact HPR4 | exact VM4 | exact FS4 | exact (FRM4 FRM3) | exact ST4 | exact HP4 | exact RR4 | | lia | lia | (destruct r as [|shq|tjq|]; [exact I | destruct shq; cbn [rootWm set_string_root is_string_root] in BSEQ4 |- *; first [exact I | rewrite (BSEQ4 eq_refl); exact RW3] | exact I | exact I])].
pose proof (rdepth_set_string_rootA r). lia. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in STR3;
[| eapply (client_range_block A4H _ _ _ _ Fr 504); [apply in_or_app; right; apply in_or_app; right; left; reflexivity | lia | cbn [cells_size csize Nat.add]; lia]].
change (hl_segs A4H) with asegs in *.
unfold KSFA, sstateB in K.
assert (ISR : is_string_root (set_string_root r) = is_string_root r) by (destruct r as [|shq|tjq|]; [reflexivity | destruct shq; reflexivity | reflexivity | reflexivity]).
eapply K; [exact SI4| | intros HS; first [exists n3; split; [clear - Hn3; lia | apply SLEN4; rewrite <- ISR; exact HS] | exists (Z.of_nat (length str3)); split; [clear - Hn3 Hstr3; lia | apply SLEN4; rewrite <- ISR; exact HS]]].
exists n3, (str3 ++ Z_to_bv 8 0 :: rest3). split; [lia | exact STR3].
Qed.

#[using="CtxAll HINVA_callc EVDc FSLc OWNc GAOc set_callc SINVA_ownc SINVA_retc CA"] Lemma seg_settersA : forall m md (A : ASA A4L HIx) B F fc ptr rem data r BS LK sb sd
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
SINVAc SHB0 m md A B F fc ptr rem data r BS LK sb sd ->
sb + 2912 <= TGT_BB_A_jo -> sd + 5 <= TGT_BD_A_jo ->
KSFAc 0x92248 (setters_root r) (sb + 2912) (sd + 5) ->
AJ5 A4L HIx A T md (sstateBc (Fr + 32) (Fr + 128) x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x920c0 fc m).
Proof.
intros m md A B F fc ptr rem data r BS LK sb sd x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 SI CB CD K.
unfold JO_SETDBL_COSTB_A, JO_SETDBL_COSTD_A, JO_SETSTR_COSTD_A in *.
eapply seg_setintA; [exact SI|]. unfold KSB. intros.
eapply seg_setint64A; [eassumption|]. unfold KSB. intros.
eapply seg_setuint64A; [eassumption|]. unfold KSB. intros.
eapply seg_setdoubleA; [eassumption | unfold JO_SETDBL_COSTB_A; lia | unfold JO_SETDBL_COSTD_A; lia |]. unfold KSB, JO_SETDBL_COSTB_A, JO_SETDBL_COSTD_A. intros.
eapply seg_setstringA; [eassumption | lia | unfold JO_SETSTR_COSTD_A; lia |]. unfold KSB, JO_SETSTR_COSTD_A. intros.
eapply seg_setboolA; [eassumption|]. unfold KSB. intros.
eapply seg_setstrlenA; [eassumption | lia | unfold JO_SETSTR_COSTD_A; lia |]. unfold JO_SETSTR_COSTD_A.
unfold KSFA in *. intros. unfold setters_root in K.
eapply K; [| eassumption | eassumption].
replace (sb + 2912) with (sb + 512 + 1200 + 1200) by lia. replace (sd + 5) with (sd + 1 + 2 + 2) by lia. eassumption.
Qed.
End Ctx.
End AHarnJo2.
End RC__1.
