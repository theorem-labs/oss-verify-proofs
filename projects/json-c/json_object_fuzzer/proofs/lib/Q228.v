(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QRjH QHnV QCcH QfLs Q0Ek QjDH QTEu Qsw7 QJjn QRUw Q7UD Qhd4 Qwm6 QlKV Q4v2 QgHv Q1Y6 QsKa Q9O6 QL3k Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa Q4v2.Mq0 QgHv.Mq0 Q1Y6.Mq1 QsKa.Mq6 QlKV.Mq2 QsKa Q9O6.Mq2 QL3k.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Local Ltac flia := Qo9G.term_slim ltac:(Zify.zify; xlia zchecker).

Definition AESC_STACK : Z := 240 + 12256.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section AEsc.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Definition esc_specA : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud)
(pb buf bpos cap Sa n fl lo sa sk : Z) (src content : list byte) (errv : word),
HEAPAx A ((pb, PB_SZ) :: (buf, cap) :: LB) LM FRS B m md ->
pbuf_core asegs m pb buf bpos cap content ->
In (sa, sk) LB -> sa <= Sa -> Sa + n <= sa + sk ->
bytes_at asegs m Sa src -> Z.of_nat (length src) = n -> 0 <= n < 2^31 ->
32 <= cap < 2^30 -> bpos + 6 * n < 2^28 -> ser_need cap bpos (6 * n) <= bB B ->
aflags_ok fl ->
Z.of_nat (length FRS) + 1 < 4096 ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AESC_STACK ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> JHEX_A m ->
tp = wz A_TP -> bv_unsigned ra mod 2 = 0 -> frm0 fc ->
a0 = wz pb -> a1 = wz Sa -> a2 = wz n -> a3 = wz fl ->
(forall ms' md' A', ser_postA HIx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B pb cap bpos (6 * n) lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz AESCAPE) fc None m (seg_rom asegs)).

Variables (sp gp : word) (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS0 : list frame) (B0 : bud) (pb lo : Z).
Variables (bpos0 cap0 w : Z).
Let usp := bv_unsigned sp.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis HT : usp <= hiA_top A4L HIx.
Hypothesis CAP0 : 32 <= cap0 < 2^30.
Hypothesis TXT : bpos0 + w < 2^28.
Hypothesis NEED : ser_need cap0 bpos0 w <= bB B0.
Hypothesis JHEX0 : JHEX_A m0.
Hypothesis ESC : esc_specA.
Notation ser_memx := (ser_memA HIx sp m0 md0 LB LM FRS0 B0 pb lo bpos0 cap0 w).

Lemma ser_escapeA :
forall (ret : Z) (x3 t0 t1 t2 x8 x9 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
(F Fc : bvmap 5 word) (fcc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (FRSc : list frame) (FA : Z) (CH : list (Z * list cell)) (e Sa n fl sa sk : Z) (src : list byte),
ser_memx A FRSc FA CH e m md ->
In (sa, sk) LB -> sa <= Sa -> Sa + n <= sa + sk ->
bytes_at asegs m Sa src -> Z.of_nat (length src) = n -> 0 <= n < 2^31 ->
0 <= e -> e + 6 * n <= w ->
aflags_ok fl -> Z.of_nat (length FRSc) + 1 < 4096 ->
lo <= FA - AESC_STACK -> FA mod 16 = 0 -> FA <= usp -> 0 <= FA ->
x3 = gp -> 0 <= ret < 2^64 -> ret mod 2 = 0 ->
fsaved F Fc -> frm0 fcc ->
(forall (A' : ASA A4L HIx) m' md' (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F' fc',
ser_memx A' FRSc FA CH (e + 6 * n) m' md' -> fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A' T md' (MS (mkR (wz ret) (wz FA) gp (wz A_TP) t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7'
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6') F' (wz ret) fc' None m' (seg_rom asegs))) ->
AJ5 A4L HIx A T md (MS (mkR (wz ret) (wz FA) x3 (wz A_TP) t0 t1 t2 x8 x9 (wz pb) (wz Sa) (wz n) (wz fl) a4 a5 a6 a7
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) Fc (wz AESCAPE) fcc None m (seg_rom asegs)).
Proof.
intros until src. intros INV INs Hs1 Hs2 SRC SRCL Hn He Hew FL FRN LOS FAA FAU FA0 -> Hret Hret2 FS FRM K.
destruct INV as (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & Hbp & Hcap & HBB & HBD).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
assert (U2 : bv_unsigned (wz FA) = FA) by (apply unsigned_lit; unfold usp in *; lia).
assert (CAPB : ser_capb cap0 bpos0 w < 2^30) by (unfold ser_capb; flia).
assert (NEEDc : ser_need cap bpos (6 * n) <= bB B).
{ eapply (ser_need_step cap0 cap bpos0 bpos w (6 * n) (bB B0) (bB B)); [exact Hcap | lia | exact NEED | exact HBB]. }
assert (JH : JHEX_A m) by (eapply JHEX_A_pres; [exact HPR | exact JHEX0]).
eapply ESC with (A := A) (LB := LB) (LM := LM) (FRS := FRSc) (B := B) (buf := buf) (bpos := bpos) (cap := cap) (lo := lo) (content := content) (errv := errv)
(Sa := Sa) (n := n) (fl := fl) (sa := sa) (sk := sk) (src := src);
rewrite ?U2.
- exact HP.
- exact PB.
- exact INs.
- exact Hs1.
- exact Hs2.
- exact SRC.
- exact SRCL.
- exact Hn.
- lia.
- lia.
- exact NEEDc.
- exact FL.
- exact FRN.
- exact ST.
- exact LO.
- exact LOS.
- exact FAA.
- unfold usp in *. lia.
- exact ERR.
- exact JH.
- reflexivity.
- rewrite unsigned_lit by lia. exact Hret2.
- exact FRM.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- intros ms' md' A' POST.
destruct POST as (m' & r & errv' & buf' & cap' & bpos' & content' & B' & RS & VM' & ST' & HPR' & ERR' & HP' & PB' & Hbp' & Hcap' & HBB' & HBD').
destruct RS as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F' & fc' & -> & FS' & FR').
rewrite U2 in ST', HPR'.
replace (ret_pc (wz ret)) with (wz ret) by (symmetry; apply ret_pc_even; [lia | exact Hret2]).
apply K; [| eapply fsaved_trans; [exact FS | exact FS'] | exact (FR' FRM)].
pose proof (ser_capb_mono cap0 cap bpos0 bpos w (6 * n) Hcap ltac:(lia)) as MONO.
exists buf', cap', bpos', content', errv', B'.
split; [exact HP'|]. split; [exact PB'|].
split; [eapply chunks_pres; [exact HPR' | exact CHok | exact CHm]|]. split; [exact CHok|]. split; [exact FSUB|].
split; [exact ERR'|]. split; [exact ST'|].
split. { eapply heap_pres_trans; [exact HPR | eapply heap_pres_weaken; [exact HPR' | unfold usp in *; lia |]].
intros bb Hbb. apply in_app_or in Hbb. apply in_or_app. destruct Hbb as [Hbb|Hbb]; [left; exact Hbb | right].
apply in_app_or in Hbb. apply in_or_app. destruct Hbb as [Hbb|Hbb]; [left; exact Hbb | right; apply FSUB; exact Hbb]. }
split; [eapply model_vm_only_trans; [exact VM | exact VM']|].
split; [lia|]. split; [lia|]. split; [lia | lia].
Qed.
End AEsc.
End RC__1.
End Mq0.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache QWxq_c1 Qfw3_c1 Qc3B QZDE QmZZ Q6WR QrPc QYIF QgoP QXUB QJZd Qw5U Q1Ey Qvmy Qawr QYZ0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun QWxq_c1.Mq0 Qfw3_c1.Mq2 Qc3B QZDE OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn.
Import Q6WR Q6WR.Mq0 QrPc.
Import QYIF.
Import QgoP.
Import Q7UD QXUB.Mq0 Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq4 QlKV.Mqa QsKa.Mq0 QJZd.Mq0 QsKa.Mq8 Qw5U.Mq0.

Import QsKa.Mq6.

Import Qvmy.Mq0 Qawr.Mq0 QYZ0.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Ltac gi_fs_tail := let k := fresh "k" in let Hk := fresh "Hk" in intros k Hk; cbn [FSAVED In] in Hk; repeat (destruct Hk as [<- | Hk]); [..| destruct Hk]; rewrite ?freg_get_other by (vm_compute; reflexivity); reflexivity.

Ltac gi_exit EPI XHP XPD PD1 HP1 A1 md1 mb VM1 :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (EPI mc A1 md1);
[ eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
| apply XHP; assumption | exact VM1 | eapply (XPD mb mc PD1 A1 md1 HP1); assumption
| first [apply fsaved_refl | gi_fs_tail] | first [intros Hf; exact Hf | intros _; assumption] ] end.
Section AJoGetUint64.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis ERRNOL : QlKV.Mq4.errno_location_A_stmt.
Hypothesis PI64 : parse_i64_A_stmt HIx 0xa3c68.

Lemma RTC_GU64PC : forall A LB LM FR B m md, HEAPAx A LB LM FR B m md -> bytes_at asegs m 0xe6a48 (le8 (Z_to_bv 64 0x9cf10)).
Proof.
intros A LB LM FR B m md HP. apply (rtc_cell HIx _ _ _ _ _ _ _ _ _ HP). unfold a4_rt_consts.
repeat (first [left; reflexivity | right]).
Qed.

Definition GU64_STK_A : Z := 96 + PI64_STK_A.

Lemma get_uint64_A : jo_get_num_A_stmt HIx 0x9cf10 GU64_STK_A.
Proof.
unfold jo_get_num_A_stmt. intros until errv. intros (HP & ST & LO & LOS & SPA16 & HT & ERR & TP & RA) JO FRN SPA FRM A0 K.
unfold GU64_STK_A, PI64_STK_A in LOS. subst a0 tp.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof alloc_ceiling_range as ACR.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP) as (SB1 & SB2 & SB3 & SB4).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2. apply ro_C8_of_bytes_at in SB3.
assert (UARC : ro_cells asegs m (hl_uar_cell A4L) [C4 (Z_to_bv 64 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SB4]).
clear SB4. a4l.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU.
unfold A_ERRNO, A_TP in *.
stash ERR.
reenterA asegs A4L HIx asegs_wx HP.
carve_frame 96%nat ST.
step. stepz. do 8 step.
step. step.
rewrite (unsigned_lit (bv_unsigned sp + -96)) by lia. change 18446744073709551584 with (2^64 - 2^5). rewrite OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.land_align_down by lia. change (2^5) with 32.
replace (bv_unsigned sp + -96 - (bv_unsigned sp + -96) mod 32) with (bv_unsigned sp + -96) by (clear - SPA; Z.div_mod_to_equations; lia).
step. step. step. step. step. step. step. step.
norm_sx32. step. if_false. step. step.
evt_done5.
eapply (stack_malloc_full HIx) with (k := 0) (bytes := 64) (lo := lo) (LB := BS ++ LB) (LM := LM) (FR := FRS) (B := B);
[ heap_nowA A4L HIx HP MU WM MI | lia | .. ].
all: rewrite ?unsigned_lit by lia.
1: rewrite fr_size_0; lia.
1: reflexivity.
1: lia.
1: exact ST.
1: exact LO.
1: cbn [hl_stack_A A4L]; lia.
1: clear - SPA; Z.div_mod_to_equations; lia.
1: lia.
1: reflexivity.
1: reflexivity.
intros ms1 m1' md1 A1 Fr RS1 VM1 ST1 HPR1 FRNZ (jff & FF1) SHB1 HP1. open_ret RS1.
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP1) as (errv1 & ERR1). unfold A_ERRNO, A_TP in ERR1. cbn [hl_tp A4L A4H hla_base] in ERR1.
rewrite ?unsigned_lit in ST1, HPR1 by lia.
clear ERR.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as (_ & HFal & HF0 & HFc & HFimg & _ & HFshw & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFapp.
rewrite fr_size_0 in HFal, HFc, HFimg, HFapp. rewrite fr_shadow_len_0 in HFshw. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in FR; [| left; cbn; lia].
clear SB1 SB2 SB3 UARC.
pose proof (RTC_GU64PC _ _ _ _ _ _ _ HP1) as PCC. apply ro_C8_of_bytes_at in PCC.
assert (FSH1 : rw_cells asegs m1' (shad A4L Fr) [CB 8 (repeat (Z_to_bv 8 0) 8)]).
{ split; [split; [cbn; split; [reflexivity | exact I] | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SHB1] | exact HFshw]. }
rewrite fr_size_0 in FF1. change (Z.to_nat (64 - 8)) with 56%nat in FF1.
unfold shad in FSH1. a4l.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 8 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1. change (hl_segs A4L) with asegs in MI1. clear MI.
rename MU into MU0. rename WM into WM0. pose proof (wmono_refl asegs m1') as WM. pose proof (munch_refl [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6434236, 6434240)] m1') as MU.
change (6434400 - 164) with 6434236 in ERR1.
unfold A_SB in HFapp.
reenterA asegs A4L HIx asegs_wx HP1.
step. step. step. if_truex.
stepz.
step. step. step. step.
rewrite (unsigned_lit Fr) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
step. step. step. stepz. stepz. stepz. step. step.
fold sh.
stepz. stepz. stepz. stepz. step. stepz. stepz. stepz. stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (SHE : ro_cells asegs mc 2148255159 [C1 (Z_to_bv 8 0)]) end.
{ apply QsKa.Mq1.ro_C1_of_bytes_at.
pose proof (heapA_shadow_img A4L HIx _ _ _ _ _ _ _ (6434236 / 8) HP1) as X.
assert (E : img_shadow_val (hl_reg_globals A4L) (6434236 / 8) = 0) by (vm_compute; reflexivity). rewrite E in X.
cbn [hl_sb A4L hl_img_lo hl_img_hi hla_base A4H] in X. unfold A_SB in X.
specialize (X ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
change (6434236 / 8 + 2147450880) with 2148255159 in X.
eapply bytes_at_transport; [exact X | exact MU |]. cbn [disjoint_from length]. change (Z.of_nat 1) with 1. unfold sh. clear - HFimg HFapp HF0 HFc ACR LO LOS SPR. Z.div_mod_to_equations. lia. }
step.
eapply evt_cut; [eapply ERRNOL; reflexivity |]. intros ms9 ->.
replace (ret_pc (Z_to_bv 64 0x9d000)) with (Z_to_bv 64 0x9d000) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unfold A_ERRNO, A_TP. change (6434400 - 164) with 6434236.
step. step. step. rewrite ?sxb_zero. step. if_false.
stepz.

lazymatch type of FF1 with rw_cells _ _ _ [?c1; ?c2; ?c3; CB 32 ?jj] =>
apply (rw_cells_split_CB asegs _ Fr [c1; c2; c3] 32 jj [] [8; 8; 16]%nat) in FF1; [| reflexivity]; cbn [mk_CB_cells app] in FF1 end.
apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _] _)) in FF1. destruct FF1 as [FFa FFe]. cbn [cells_size csize Nat.add] in FFe.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FFe. destruct FFe as [FFe FFb]. cbn [cells_size csize Nat.add] in FFb.
change (Z.of_nat 32) with 32 in FFe, FFb. replace (Fr + 32 + Z.of_nat 8) with (Fr + 40) in FFb by lia.
apply rw_cells_C8_of_CB8 in FFe.
assert (XHP : forall mX, munch [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6434236, 6434240)] m1' mX -> wmono asegs m1' mX -> mem_inv asegs mX ->
HEAPAx A1 (BS ++ LB) LM ((Fr, 0) :: FRS) B mX md1).
{ intros mX MUX WMX MIX. exact (fk0_HEAPA HIx _ _ _ _ _ _ _ _ _ _ _ HP1 LO HT MUX WMX MIX). }
assert (PD1 : heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1').
{ eapply heap_presD_trans; [| eapply heap_presD_of_pres; [exact HPR1 | lia]].
eapply (presD_private HIx _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp) (Fr + 32) HP MU0 WM0); [| lia |].
- intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. exact Hb.
- apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. lia. }
assert (XPD : forall mb mX, heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mb ->
forall AX mdX, HEAPAx AX (BS ++ LB) LM ((Fr, 0) :: FRS) B mb mdX ->
munch [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6434236, 6434240)] mb mX -> wmono asegs mb mX ->
heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mX).
{ intros mb mX PDb AX mdX HPb MUX WMX. eapply heap_presD_trans; [exact PDb |].
eapply (fk0_presD HIx); [exact HPb | exact LO | lia | exact MUX | exact WMX]. }

lazymatch type of FR with rw_cells _ _ _ ?frc => lazymatch type of FSH1 with rw_cells _ _ _ ?shc => lazymatch type of FFa with rw_cells _ _ _ ?ffc =>
assert (EPI : forall (mX : word -> option byte) (AX : ASA A4L HIx) (mdX : config) (F1 : bvmap 5 word) (fc1 : bv 32)
(eX xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs6 xt3 xt4 xt5 xt6 : word),
mem_inv asegs mX ->
rw_cells asegs mX (bv_unsigned sp + -96) frc -> rw_cells asegs mX sh shc -> rw_cells asegs mX Fr ffc ->
rw_cells asegs mX 6434236 [C4 eX] -> stk asegs mX lo (bv_unsigned sp + -96) ->
HEAPAx AX (BS ++ LB) LM ((Fr, 0) :: FRS) B mX mdX -> model_vm_only (cfg_model md) (cfg_model mdX) ->
heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mX ->
fsaved F F1 -> (frm0 fc -> frm0 fc1) ->
evt asegs (AJ5e A4L HIx AX T mdX)
(MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 6434400) xt0 xt1 xt2 sp xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 Fr) xs3 (Z_to_bv 64 sh) (Z_to_bv 64 Fr) xs6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
F1 (Z_to_bv 64 0x9d160) fc1 None mX (seg_rom asegs)))
end end end.
{ intros mX AX mdX F1 fc1 eX xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs6 xt3 xt4 xt5 xt6 MIX FRX FSHX FFX ERRX STX HPX VMX PDX FSX FRMX.
clear MU WM MI1 FR FSH1 FFa FFe FFb ST1 ERR1 SHE PCC.
pose proof (wmono_refl asegs mX) as WM. pose proof (munch_refl [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6434236, 6434240)] mX) as MU.
step. stepz. step. step. stepz. step. if_falsex. step. do 8 stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ mX mc, WMc : wmono asegs mX mc, MIc : mem_inv asegs mc |- _ =>
pose proof (fk0_HEAPA HIx _ _ _ _ _ _ _ _ _ _ _ HPX LO HT MUc WMc MIc) as HPY;
pose proof (XPD mX mc PDX AX mdX HPX MUc WMc) as PDY end end.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HPY INF) as (_ & _ & _ & _ & _ & _ & _ & (fp & FPB & FPR & FPnc & FPimg & FPns & FPfr)).
rewrite fr_size_0 in FPB. replace (Fr + 64 - 8) with (Fr + 56) in FPB by lia.
pose proof (ro_C8_of_bytes_at asegs _ _ _ FPB) as FPC.
step.
evt_done5.
eapply (hiA_frame_release A4L HIx) with (Fr := Fr) (k := 0) (fp := fp) (rX := Z_to_bv 5 10);
[exact HPY | exact INF | rewrite fr_size_0; replace (Fr + 64 - 8) with (Fr + 56) by lia; exact FPB | lia | reflexivity | vm_compute; discriminate | | ].
1: vm_compute; split; reflexivity.
intros m5 md5 A5 VM5 HP5 Hoff Hwv.
cbn [fr_remove fr_base fst Z.eqb] in HP5. rewrite Z.eqb_refl in HP5.
lazymatch type of HPY with HEAPA _ _ _ _ _ _ _ ?mq _ => assert (MUr : munch [(fp, fp + 1)] mq m5) end.
{ intros x Hx. cbn [outside] in Hx. pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. cbn in XR.
rewrite <- (Z_to_bv_bv_unsigned x). change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)). apply Hoff; lia. }
lazymatch type of HPY with HEAPA _ _ _ _ _ _ _ ?mq _ => assert (WMr : wmono asegs mq m5) by exact Hwv end.
assert (FPlow : fp < alloc_ceiling) by (destruct (Z.lt_ge_cases fp alloc_ceiling) as [L|G]; [exact L | exfalso; apply FPnc; left; exact G]).
apply (rw_cells_transport asegs [(fp, fp + 1)] _ m5) in FRX; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] _ m5) in ERRX; [| exact MUr | exact WMr | cbn [disjoint_from cells_size csize Nat.add]; cbn [hl_scratch A4L A4H hla_base] in FPns; unfold A_TP in FPns; lia].
apply (stk_transport_disjoint asegs [(fp, fp + 1)] _ m5) in STX; [| exact MUr | exact WMr | cbn [disjoint_from]; lia].
change (643488 + 4) with 643492.
clear FFX FSHX FPC.
reenterA asegs A4L HIx asegs_wx HP5.
do 13 step.
evt_done5.
eapply (K _ md5 m5 (bv_unsigned xa1) A5).
- assert (PD5 : heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m5).
{ eapply heap_presD_trans; [exact PDY |].
eapply (presD_fp HIx _ _ _ _ _ _ _ _ (Fr + 32) _ (bv_unsigned sp) fp HPY); [| lia | exact FPnc | exact FPfr | exact Hoff | exact Hwv].
intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. destruct Hb as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H]. }
split; [| split; [| split; [| split]]].
+ rewrite Z_to_bv_bv_unsigned. apply ret_statew_intro; [exact FSX | exact FRMX].
+ eapply model_vm_only_trans; [exact VMX | exact VM5].
+ release_frame FRX STX (bv_unsigned sp). exact STX.
+ eapply (heap_pres_of_presD (Fr + 32)).
* eapply heap_presD_weaken; [exact PD5 | lia |]. intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; apply in_or_app; right; exact Hb | apply in_or_app; right; exact Hb].
* intros a Hd Hc.
destruct (own_frame_fresh HIx Fr 0 (BS ++ LB) LB LM FRS B A1 m1' md1 HP1 ltac:(intros b Hb; apply in_or_app; right; exact Hb)) as [OFF OFS].
assert (Ho : outside [(Fr + 32, Fr + 40)] a).
{ eapply (Q1Ey.client_outsideF HIx A1 (BS ++ LB) LM ((Fr, 0) :: FRS) B (LB ++ LM ++ fr_ivs A4L FRS) m1' md1 [(Fr + 32, Fr + 40)] (bv_unsigned sp) HP1); [| lia | | lia | exact Hc].
- intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. destruct Hb as [H|H]; [left; apply in_app_or in H; apply in_or_app; destruct H as [H|H]; [left; apply in_or_app; right; exact H | right; exact H] | right; cbn [fr_ivs flat_map app]; right; right; exact H].
- apply Forall_cons; [| apply Forall_nil]. right; right; right. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. cbn [fst snd]. rewrite fr_size_0. lia. }
cbn [outside] in Ho. lia.
+ eexists. exact ERRX.
- assert (PD5 : heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m5).
{ eapply heap_presD_trans; [exact PDY |].
eapply (presD_fp HIx _ _ _ _ _ _ _ _ (Fr + 32) _ (bv_unsigned sp) fp HPY); [| lia | exact FPnc | exact FPfr | exact Hoff | exact Hwv].
intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. destruct Hb as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H]. }
eapply (jopt_agree asegs A4F BS m m5 s BS p); [exact JO | | apply incl_refl].
eapply (agree_of_presD (Fr + 32)); [exact PD5 | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb |].
intros a n Hin.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 INF ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin)) as DF. rewrite fr_size_0 in DF. lia.
- exact HP5. }
step.
destruct s as [shp|].
2:{  destruct JO as [Hp _]. rewrite Hp in *. if_truex. step.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1. }
destruct JO as [Hp J].

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m1' mc, WMc : wmono asegs m1' mc, MIc : mem_inv asegs mc |- _ =>
pose proof (XHP mc MUc WMc MIc) as HPc;
assert (AGc : agree_on asegs BS m mc);
[ eapply (agree_of_presD (Fr + 32)); [exact (XPD m1' mc PD1 A1 md1 HP1 MUc WMc) | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb |];
let a := fresh "a" in let n := fresh "n" in let Hin := fresh "Hin" in intros a n Hin;
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 INF ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin)) as DF; rewrite fr_size_0 in DF; lia
| ] end end.
pose proof (jval_agree asegs A4F shp BS m _ BS p 1 J AGc (incl_refl _)) as Jc.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HPc) as ND0.
assert (ND : List.NoDup (map blk_addr BS)) by exact (nodup_app_l' _ _ (nodup_app_l' _ _ ND0)).
destruct (jval_hdr asegs A4F shp _ BS p 1 Jc ND) as (n & tojs & pb & udel & ud & rest & INp & SZ & N48 & HDR & CLOSE).
assert (INpA : In (p, n) (BS ++ LB)) by (apply in_or_app; left; exact INp).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HPc ltac:(apply in_or_app; left; exact INpA)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HPc ltac:(apply in_or_app; left; exact INpA)) as Hpimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg.
assert (Hp8 : p mod 8 = 0) by (clear - Hpal; Z.div_mod_to_equations; lia).
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p n 0 HPc INpA ltac:(lia) ltac:(lia)) as SH0. rewrite Z.add_0_r in SH0.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p n 5 HPc INpA ltac:(lia) ltac:(lia)) as SH5. replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SH5 by lia.
if_falsex.
unfold jhdr_cells in HDR, SZ. cbn [app hl_segs hla_base A4L A4H] in HDR, SZ.
pose proof (jtype_range shp) as JR.
asan_chk0.
step. rewrite sx32_small by lia. step. step. step.
destruct shp as [|u| |h|kids|kids]; cbn [jtype] in *; unfold JT_BOOLEAN, JT_DOUBLE, JT_INT, JT_STRING, JT_OBJECT, JT_ARRAY in *; if_lit.
-
step. step. if_lit.
destruct Jc as (pb_ & PBS & REST & EBS & OPB & (b & junk_ & ER & CELLS)). cbn [hl_segs hla_base A4L A4H] in CELLS. unfold jhdr_cells in CELLS. cbn [app] in CELLS.
step. asan_chkA.
step. step.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
-
step. step. if_lit. step. step. if_lit.
destruct Jc as (pb_ & PBS & REST & EBS & OPB & Jc). cbn [hl_segs hla_base A4L A4H] in Jc.
lazymatch type of HPc with HEAPA _ _ _ _ _ _ _ ?mc _ => assert (CELLS : exists tojs' udel' ud' bits, rw_cells asegs mc p (jhdr_cells 2 1 tojs' pb_ udel' ud' ++ [C8 bits])) end.
{ destruct u; [destruct Jc as (bits & ud_ & udn & uds & _ & _ & C & _) | destruct Jc as (bits & _ & _ & C)]; do 4 eexists; exact C. }
clear Jc. destruct CELLS as (tojs' & udel' & ud' & bits & CELLS). unfold jhdr_cells in CELLS. cbn [app] in CELLS.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MIc : mem_inv asegs mc |- _ =>
let b1 := eval vm_compute in (match image_bytes asegs 0x10350 8 with Some bs => bs | None => [] end) in
assert (RO1 : ro_cells asegs mc 0x10350 [CB 8 b1]) by (change 8%nat with (length b1); apply ro_cells_image; [exact MIc | vm_compute; reflexivity | lia | cbn; lia]) end end.
step. asan_chkA.
step. step. step. step. step.
if_cases Hc1.
+
step. rewrite ?sxb_zero. step. if_false. step. stepz. step. step.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
+ step. step. step.
if_cases Hc2.
*
step. step. step. step. step. step. step.
if_cases Hc3.
--  step. step. gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
--
step. rewrite ?sxb_zero. step. if_false. step. step. stepz. step.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
*
step. rewrite ?sxb_zero. step. if_true. step. step. stepz. step.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
-
step. step. if_lit. step. step. if_lit.
destruct Jc as (pb_ & PBS & REST & EBS & OPB & (cty & v & junk_ & ER & Hcty & CELLS)). cbn [hl_segs hla_base A4L A4H] in CELLS. unfold jhdr_cells in CELLS. cbn [app] in CELLS.
assert (INp56 : In (p, 56) (BS ++ LB)) by (apply in_or_app; left; rewrite EBS, ER; cbn; left; reflexivity).
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p 56 6 HPc INp56 ltac:(lia) ltac:(lia)) as SH6. replace (p / 8 + 2147450880 + 6) with (p / 8 + 2147450886) in SH6 by lia.
step. asan_chkA.
step. rewrite sx32_small by lia. step. step.
destruct Hcty as [-> | ->]; if_lit.
+
step. if_lit.
step. asan_chkA. step. step.
if_cases Hc7.
* gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
* step. rewrite ?sxb_zero. step. if_false. step. step. stepz. step.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
+
step. asan_chkA. step. step.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
-
step. step. if_lit.
destruct Jc as (pb_ & PBS & REST & EBS & OPB & Jc). cbn [hl_segs hla_base A4L A4H] in Jc, OPB.
lazymatch type of HPc with HEAPA _ _ _ _ _ _ _ ?mc _ =>
assert (TXT : exists (TX TB TBN len : Z) (str0 rest0 : list byte) (lencell : list cell),
In (TB, TBN) BS /\ TB <= TX /\ TX + Z.of_nat (length str0) + 1 <= TB + TBN /\ ~ In (Z_to_bv 8 0) str0 /\
bytes_at asegs mc TX (str0 ++ [Z_to_bv 8 0]) /\
rw_cells asegs mc (p + 40) (C8 (Z_to_bv 64 len) :: lencell) /\ -2^31 < len < 2^31 /\
((0 <= len /\ TX = p + 48) \/ (len < 0 /\ lencell = [C8 (Z_to_bv 64 TX)])) /\
(exists pn, In (p, pn) BS /\ 56 <= pn)) end.
{ destruct h.
- destruct Jc as (len & pd & pdn & str & junk2 & ER & Hlen & Hstr & Hpdn & C1 & C2).
destruct (first_nul_split2A str junk2) as (str0 & rest0 & E0 & NIN & L0).
exists pd, pd, pdn, len, str0, rest0, [C8 (Z_to_bv 64 pd)].
split; [rewrite EBS, ER; cbn; right; left; reflexivity|]. split; [lia|]. split; [lia|]. split; [exact NIN|].
split. { apply rw_cells_bytes_at in C2. cbn [cells_bytes cbytes app] in C2. rewrite app_nil_r in C2.
eapply bytes_at_cstr_prefix2A; [exact C2 | exact E0]. }
split. { unfold jhdr_cells in C1. cbn [app] in C1. apply rw_cells_app with (cs1 := [_;_;_;_;_;_]) in C1 as [_ C1]. cbn [cells_size csize Nat.add] in C1. change (p + Z.of_nat 40) with (p + 40) in C1. exact C1. }
split; [lia|]. split; [right; split; [lia | reflexivity]|]. exists 56. split; [rewrite EBS, ER; cbn; left; reflexivity | lia].
- destruct Jc as (len & str & junkS & ER & Hlen & Hstr & C1).
destruct (first_nul_split2A str junkS) as (str0 & rest0 & E0 & NIN & L0).
exists (p + 48), p, (str_objsize len), len, str0, rest0, [CB (Z.to_nat (str_objsize len - 48)) (str ++ [Z_to_bv 8 0] ++ junkS)].
split; [rewrite EBS, ER; cbn; left; reflexivity|]. split; [lia|]. split; [unfold str_objsize; lia|]. split; [exact NIN|].
unfold jhdr_cells in C1. cbn [app] in C1. apply rw_cells_app with (cs1 := [_;_;_;_;_;_]) in C1 as [_ C1]. cbn [cells_size csize Nat.add] in C1. change (p + Z.of_nat 40) with (p + 40) in C1.
split. { pose proof C1 as C2. apply rw_cells_app with (cs1 := [_]) in C2 as [_ C2]. cbn [cells_size csize Nat.add] in C2.
apply rw_cells_bytes_at in C2. cbn [cells_bytes cbytes app] in C2. rewrite app_nil_r in C2.
change (p + 40 + Z.of_nat 8) with (p + 40 + 8) in C2. replace (p + 40 + 8) with (p + 48) in C2 by lia. eapply bytes_at_cstr_prefix2A; [exact C2 | exact E0]. }
split; [exact C1|]. split; [lia|]. split; [left; split; [lia | reflexivity]|]. exists (str_objsize len). split; [rewrite EBS, ER; cbn; left; reflexivity | unfold str_objsize; lia]. }
clear Jc. destruct TXT as (TX & TB & TBN & len & str0 & rest0 & lencell & INT & TLO & THI & NIN & BY & LENC & Hlen & ALT & (pn & INpn & Hpn)).
assert (INTA : In (TB, TBN) ((BS ++ LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; left; exact INT).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ TB TBN HPc INTA) as (_ & _ & Htlo & Hthi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ TB TBN HPc INTA) as Htimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Htimg.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HPc INF INTA) as DFT. rewrite fr_size_0 in DFT.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ TB TBN HPc INTA) as APT. cbn [hl_sb A4L] in APT. unfold A_SB in APT.
assert (INpnA : In (p, pn) (BS ++ LB)) by (apply in_or_app; left; exact INpn).
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p pn 6 HPc INpnA ltac:(lia) ltac:(lia)) as SH6. replace (p / 8 + 2147450880 + 6) with (p / 8 + 2147450886) in SH6 by lia.
apply rw_cells_app with (cs1 := [_]) in LENC as [LEN1 LEN2]. cbn [cells_size csize Nat.add] in LEN2. change (p + 40 + Z.of_nat 8) with (p + 40 + 8) in LEN2. replace (p + 40 + 8) with (p + 48) in LEN2 by lia.

lazymatch goal with |- evt _ ?Q (MS ?r ?Fx ?pc ?fcx None ?mc ?rom) =>
let r' := open_constr:(mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in unify r r';
lazymatch r' with mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31 =>
assert (CONT : forall xa1 : word, evt asegs Q
(MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 TX) xa1 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) Fx (Z_to_bv 64 0x9d14c) fcx None mc rom))
end end.
{ intros xa1.
step. step. step.
pose proof (unpoisoned_of_blk HIx _ _ _ _ _ _ _ TB TBN TX (Z.of_nat (length str0) + 1) HPc ltac:(apply in_or_app; left; exact INT) ltac:(lia) ltac:(lia) ltac:(lia)) as UNS.
lazymatch type of FSH1 with rw_cells _ ?mc _ _ => assert (UNE : unpoisoned asegs mc A_SB (Fr + 32) 8) end.
{ pose proof (rw_cells_bytes_at asegs _ _ _ FSH1) as SHB. cbn [cells_bytes cbytes app] in SHB.
lazymatch type of SHB with bytes_at _ _ _ ?wb => eapply (unpoisoned_gran8 asegs _ A_SB (Fr + 32) wb ltac:(clear - HFal; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(unfold A_SB; lia) eq_refl) end.
- replace (((Fr + 32) / 8 + A_SB) / 8 * 8) with sh by (unfold sh, A_SB; clear - HFal; Z.div_mod_to_equations; lia). exact SHB.
- replace (((Fr + 32) / 8 + A_SB) mod 8) with 4 by (unfold A_SB; clear - HFal; Z.div_mod_to_equations; lia). reflexivity. }
evt_done5.
eapply PI64 with (LB := BS ++ LB) (LM := LM) (FRS := (Fr, 0) :: FRS) (B := B) (str := str0) (SA := TX) (R := Fr + 32) (lo := lo);
[ exact HPc | rewrite unsigned_lit by lia; eassumption | exact LO | unfold PI64_STK_A; rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; clear - SPA; Z.div_mod_to_equations; lia | rewrite unsigned_lit by lia; lia
| unfold A_ERRNO, A_TP; eassumption | reflexivity | rewrite unsigned_lit by lia; reflexivity
| reflexivity | reflexivity | exact BY | exact NIN
| exists TB, TBN; split; [apply in_or_app; left; exact INT | lia]
| exact UNS
| exists Fr, 0; split; [exact INF | rewrite fr_size_0; lia]
| exact FFe | exact UNE | clear - HFal; Z.div_mod_to_equations; lia
| cbn [length]; lia
| ].
rewrite ?unsigned_lit by lia.
intros ms3 md3 m3 A3 rv vR eR RS3 VM3 ST3 PD3 HRV RC3 ERR3 HP3. open_ret RS3.

pose proof (frame_above_img HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFhi. cbn [hl_img_hi A4H] in HFhi.
lazymatch type of PD3 with heap_presD _ _ _ ?mb _ =>
assert (HPR3 : heap_pres A4H [(Fr, 32); (sh, 8)] (bv_unsigned sp + -96) mb m3) end.
{ intros a Ha Hc. apply (PD3 a Ha).
- destruct Hc as [Hc | [Hc | (b & Hb & Hr)]]; [left; exact Hc | right; left; exact Hc |].
right; right. destruct Hb as [<- | [<- | []]]; cbn [blk_addr blk_size fst snd] in Hr.
+ exists (Fr, fr_size 0 - 8). split; [apply in_or_app; right; apply in_or_app; right; cbn [fr_ivs flat_map app fr_base fr_class fst snd]; left; reflexivity | cbn [blk_addr blk_size fst snd]; rewrite fr_size_0; lia].
+ exists (shad A4L Fr, fr_shadow_len 0). split; [apply in_or_app; right; apply in_or_app; right; cbn [fr_ivs flat_map app fr_base fr_class fst snd]; right; left; reflexivity | unfold shad; cbn [blk_addr blk_size fst snd hl_sb A4L]; rewrite fr_shadow_len_0; unfold A_SB; fold sh; lia].
- destruct Hc as [Hc | [Hc | (b & Hb & Hr)]].
+ lia.
+ cbn [hl_client_static A4H] in Hc. unfold a4_client_static in Hc. lia.
+ destruct Hb as [<- | [<- | []]]; cbn [blk_addr blk_size fst snd] in Hr; lia. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FFa; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FSH1; [| eapply client_range_block; [right; left; reflexivity | lia | cbn; lia]].
change (hl_segs A4H) with asegs in FR, FFa, FSH1.
lazymatch goal with MUc : munch _ m1' ?mc, WMc : wmono asegs m1' ?mc |- _ =>
assert (PDm3 : heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m3);
[ eapply heap_presD_trans; [exact (XPD m1' mc PD1 A1 md1 HP1 MUc WMc) |];
eapply heap_presD_weaken; [exact PD3 | lia |];
let b := fresh "b" in let Hb := fresh "Hb" in intros b Hb; rewrite app_assoc in Hb; apply in_app_or in Hb; rewrite app_assoc; apply in_or_app;
destruct Hb as [Hb|Hb]; [left; exact Hb | right; cbn [fr_ivs flat_map app]; right; right; exact Hb]
| clear MUc WMc ] end.
assert (VM13 : model_vm_only (cfg_model md) (cfg_model md3)) by (eapply model_vm_only_trans; [exact VM1 | exact VM3]).
assert (XHP3 : forall mX, munch [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6434236, 6434240)] m3 mX -> wmono asegs m3 mX -> mem_inv asegs mX ->
HEAPAx A3 (BS ++ LB) LM ((Fr, 0) :: FRS) B mX md3).
{ intros mX MUX WMX MIX. exact (fk0_HEAPA HIx _ _ _ _ _ _ _ _ _ _ _ HP3 LO HT MUX WMX MIX). }
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI3. change (hl_segs A4L) with asegs in MI3.
pose proof (wmono_refl asegs m3) as WM. pose proof (munch_refl [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6434236, 6434240)] m3) as MU.
unfold A_ERRNO, A_TP in ERR3. change (6434400 - 164) with 6434236 in ERR3.
replace (ret_pc (Z_to_bv 64 643416)) with (Z_to_bv 64 643416) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
reenterA asegs A4L HIx asegs_wx HP3.
step.

destruct HRV as [-> | ->]; if_lit.
+
step. step.
gi_exit EPI XHP3 XPD PDm3 HP3 A3 md3 m3 VM13.
+
step.
gi_exit EPI XHP3 XPD PDm3 HP3 A3 md3 m3 VM13. }
step. asan_chkA.
step. step. step.
destruct ALT as [[Hl ETX] | [Hl ->]].
+  if_truex. rewrite <- ETX. apply CONT.
+  if_falsex. asan_chkA. step. apply CONT.
-  step. step. if_lit. step. step. if_lit. gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
-  step. step. if_lit. step. step. if_lit. gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
Qed.
End AJoGetUint64.
End RC__1.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qtgi QkMG QG8z Qdyh Qiiq Ql4f QrQv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw QkMG. Import QG8z Qdyh.Mq3 Qdyh.Mq6.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq4 Qiiq.Mq0 Q1Ey Ql4f.Mq1 QsKa.Mq8 QrQv.Mq2 QYZ0.Mq3.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition pe_jt2A (c : Z) : Z :=
match c with
| 34 => 0x974dc
| 39 => 0x974c4
| 45 => 0x9426c
| 48 => 0x9426c | 49 => 0x9426c | 50 => 0x9426c | 51 => 0x9426c | 52 => 0x9426c
| 53 => 0x9426c | 54 => 0x9426c | 55 => 0x9426c | 56 => 0x9426c | 57 => 0x9426c
| 70 => 0x94b78
| 73 => 0x94fe0
| 78 => 0x94f88
| 84 => 0x94b78
| 91 => 0x97554
| 102 => 0x94b78
| 105 => 0x94fe0
| 110 => 0x94f88
| 116 => 0x94b78
| 123 => 0x97434
| _ => 0x987d4
end.

Definition pe_jtab2A : list byte := Eval vm_compute in match image_bytes asegs 0x22f20 360 with Some bs => bs | None => [] end.
Lemma pe_jtab2A_ro : forall m, mem_inv asegs m -> ro_cells asegs m 0x22f20 [CB 360 pe_jtab2A].
Proof.
intros m MI. change 360%nat with (length pe_jtab2A).
apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ].
change (Z.of_nat (length pe_jtab2A)) with 360%Z. lia.
Qed.

Lemma ro_cells_bytes_atA : forall segs m A cs, ro_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof. intros segs m A cs [_ H]. exact H. Qed.

Section PeSStartDA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.

Ltac pe_openA STC INV :=
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR); pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk);
destruct INV as [CORE REST];
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR);
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).

Lemma start_dispatch_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s10 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
(forall a1' a3',
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jt2A (bv_unsigned cb)) (t_co ts) gp t0 t1 t2 a0 a1' a2 a3' a4 a5 a6 a7 s5 s10 (Z_to_bv 64 (pa_F pa + 64)) F fc m)) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_start) (t_co ts) gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s10 (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC INV K. pe_openA STC INV.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold pe_frameA in FR. destruct FR as (_ & _ & _ & FF & _). unfold ff_cellsA in FF.
unfold pe_msA in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (pe_jtab2A_ro m MI) as JT.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear TOK PB TSK REST LV OBJ HPR BUD STR ERR SBin.
reenterA asegs A4L HIx asegs_wx HP. unfold ST_start. cbn [pe_jtA].
step.
change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)).
step. step.
destruct (Z_lt_dec (bv_unsigned cb) 34) as [LT | GE].
-
replace (Z_to_bv 64 (bv_unsigned cb + -34)) with (Z_to_bv 64 (bv_unsigned cb + -34 + 2^64)).
2:{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite <- (Z_mod_plus_full (bv_unsigned cb + -34) 1 (2^64)). f_equal. }
step. if_falsex. step. evt_done5.
replace (pe_jt2A (bv_unsigned cb)) with 0x987d4 in K.
2:{ assert (R : 0 <= bv_unsigned cb <= 33) by lia. clear - R. enum_from (bv_unsigned cb) 0%Z 34%nat; reflexivity. }
apply K.
- destruct (Z_lt_dec 123 (bv_unsigned cb)) as [GT | LE].
+ step. if_falsex. step. evt_done5.
replace (pe_jt2A (bv_unsigned cb)) with 0x987d4 in K. 2:{ assert (R : 124 <= bv_unsigned cb <= 255) by lia. clear - R. enum_from (bv_unsigned cb) 124%Z 132%nat; reflexivity. }
apply K.
+ step. if_truex. step.
rewrite (unsigned_lit (bv_unsigned cb + -34)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
step. step. step.
pose proof (bytes_at_read asegs m 0x22f20 pe_jtab2A ((bv_unsigned cb + -34) * 4) 4 (ro_cells_bytes_atA _ _ _ _ JT) ltac:(lia)
ltac:(change (length pe_jtab2A) with 360%nat; lia)) as RD.
unfold wa in RD. replace (0x22f20 + (bv_unsigned cb + -34) * 4) with ((bv_unsigned cb + -34) * 4 + 143136) in RD by lia.
step. step. step.
evt_done5.
assert (R : 34 <= bv_unsigned cb <= 123) by lia.
match goal with |- AJ5 _ _ _ _ _ (MS _ _ ?pc _ _ _ _) =>
replace pc with (Z_to_bv 64 (pe_jt2A (bv_unsigned cb))); [apply K |] end.
clear - R. enum_from (bv_unsigned cb) 34%Z 90%nat; apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma start_default_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s10 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_ERRST (t_co ts) gp t0 t1 t2 (Z_to_bv 64 4) a1 a2 a3 a4 a5 a6 a7 s5 s10 (Z_to_bv 64 (pa_F pa + 64)) F fc m) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x987d4 (t_co ts) gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s10 (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC INV K. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & _ & _).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
unfold pe_msA in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (TST depth levels co pb pbs x obj objs objbs))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
unfold APE_ERRST in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear TOK PB TSK REST LV OBJ HPR BUD STR ERR SBin.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_rechkA.
step. step.
evt_done5.
exact K.
Qed.
End PeSStartDA.
End RC__1.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4xz QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa Q4v2.Mq0 QgHv.Mq0 Q1Y6.Mq1 QsKa.Mq6 Q4xz QlKV.Mq2 QsKa Q9O6.Mq2 QL3k.Mq1.
Import QWxq_c1 QsjA.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).

Ltac fold_mkR :=
lazymatch goal with
| |- context [MS (TNode (TNode (TNode (TNode (TNode (TNode TEmpty (Some ?x31) TEmpty) (Some ?x15) TEmpty) (Some ?x7) (TNode TEmpty (Some ?x23) TEmpty)) (Some ?x3) (TNode (TNode TEmpty (Some ?x19) TEmpty) (Some ?x11) (TNode TEmpty (Some ?x27) TEmpty))) (Some ?x1) (TNode (TNode (TNode TEmpty (Some ?x17) TEmpty) (Some ?x9) (TNode TEmpty (Some ?x25) TEmpty)) (Some ?x5) (TNode (TNode TEmpty (Some ?x21) TEmpty) (Some ?x13) (TNode TEmpty (Some ?x29) TEmpty)))) None (TNode (TNode (TNode (TNode TEmpty (Some ?x16) TEmpty) (Some ?x8) (TNode TEmpty (Some ?x24) TEmpty)) (Some ?x4) (TNode (TNode TEmpty (Some ?x20) TEmpty) (Some ?x12) (TNode TEmpty (Some ?x28) TEmpty))) (Some ?x2) (TNode (TNode (TNode TEmpty (Some ?x18) TEmpty) (Some ?x10) (TNode TEmpty (Some ?x26) TEmpty)) (Some ?x6) (TNode (TNode TEmpty (Some ?x22) TEmpty) (Some ?x14) (TNode TEmpty (Some ?x30) TEmpty))))) ?F ?pc ?fc ?rv ?m ?ro] =>
change (TNode (TNode (TNode (TNode (TNode (TNode TEmpty (Some x31) TEmpty) (Some x15) TEmpty) (Some x7) (TNode TEmpty (Some x23) TEmpty)) (Some x3) (TNode (TNode TEmpty (Some x19) TEmpty) (Some x11) (TNode TEmpty (Some x27) TEmpty))) (Some x1) (TNode (TNode (TNode TEmpty (Some x17) TEmpty) (Some x9) (TNode TEmpty (Some x25) TEmpty)) (Some x5) (TNode (TNode TEmpty (Some x21) TEmpty) (Some x13) (TNode TEmpty (Some x29) TEmpty)))) None (TNode (TNode (TNode (TNode TEmpty (Some x16) TEmpty) (Some x8) (TNode TEmpty (Some x24) TEmpty)) (Some x4) (TNode (TNode TEmpty (Some x20) TEmpty) (Some x12) (TNode TEmpty (Some x28) TEmpty))) (Some x2) (TNode (TNode (TNode TEmpty (Some x18) TEmpty) (Some x10) (TNode TEmpty (Some x26) TEmpty)) (Some x6) (TNode (TNode TEmpty (Some x22) TEmpty) (Some x14) (TNode TEmpty (Some x30) TEmpty)))))
with (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
| |- _ => idtac
end.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition ser_trueA : list byte := Eval vm_compute in match image_bytes asegs 0x236c0 4 with Some bs => bs | None => [] end.
Definition ser_falseA : list byte := Eval vm_compute in match image_bytes asegs 0x236e0 5 with Some bs => bs | None => [] end.

Section Ser.
Variable HIx : heap_iface_A A4L.
Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.

Lemma ser_boolA : ser_specA HIx ASER_BOOL Sbool.
Proof.
unfold ser_specA. intros until errv. intros HP PB JN INCL JTX CAP TXT NEED FL Hlv Hlvd FRSN ST LO LOS SPA HT ERR JHX TP' RA FRM A0 A1 A2 A3 K.
destruct JN as (b & junk & EREST & NODE). unfold jhdr_cells in NODE. cbn [app] in NODE.
subst a0 a1 a2 a3 tp REST.
cbn [app jtx] in JTX. rewrite Z.eqb_refl in JTX. injection JTX as <- _.
unfold ASER_BOOL, ser_budgetA, ASER_LEVEL, ASER_LEAF in *. cbn [sdepth Z.mul Z.add] in LOS.
word_range sp SPR.
destruct FL as [Rfl FL58].
assert (FL32 : Z.land fl 32 = 0) by (replace 32 with (Z.land 58 32) by reflexivity; rewrite Z.land_assoc, FL58; reflexivity).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
assert (INp : In (p, 48) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; apply INCL; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p 48 HP ltac:(apply in_or_app; left; exact INp)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ pb PB_SZ HP ltac:(apply in_or_app; left; left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(apply in_or_app; left; right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
unfold_consts.
shadow_inA A4L HIx HP INp SHp.
pose proof PB as (Hbp & Hcap & Hlen & PBS & PBUF).
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
pose proof alloc_ceiling_range as ACR.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 48%nat ST.
do 6 step.
do 6 step. rewrite (unsigned_lit fl) by lia. rewrite FL32.
step. if_truex.
step. asan_chkA.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
assert (INV1 : ser_memA HIx sp m md LB LM FRS B pb lo bpos cap 8 A FRS (bv_unsigned sp + -48)
[(bv_unsigned sp + -48, [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 junk0))))); C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])] 0 m1 md).
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

assert (TAILK : forall (lit k : Z) (bs : list byte) (t0_ t1_ t2_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ : word),
ro_bytes_b asegs lit bs = true -> Z.of_nat (length bs) = k -> 0 < k <= 5 -> 0 <= lit -> lit + k < 2^32 -> src_ro_chk lit k = true ->
evt asegs (AJ5e A4L HIx A T md)
(MS (mkR (Z_to_bv 64 0x9aed0) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 6434400) t0_ t1_ t2_ (Z_to_bv 64 pb) (Z_to_bv 64 p)
(Z_to_bv 64 pb) (Z_to_bv 64 lit) (Z_to_bv 64 k) (Z_to_bv 64 fl) a4_ a5_ a6_ a7_ (Z_to_bv 64 0) (Z_to_bv 64 2147450880)
s4 s5 s6 s7 s8 s9 s10 s11 t3_ t4_ t5_ t6_)
F (Z_to_bv 64 0x9a0ac) fc None m1 (seg_rom asegs))).
{ intros lit k bs t0_ t1_ t2_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ RB BL Hk Hl Hlk CHK.
pose proof INV1 as (buf1 & cap1 & bpos1 & content1 & errv1 & B1 & HP1 & _).
evt_done5.
eapply (ser_appendA HIx sp gp m md LB LM FRS B pb lo bpos cap 8 LO HT CAP TXT NEED OBL_REALLOC_NF) with (F := F) (sb := bs) (e := 0);
[ exact INV1 | apply rodata_bytes_at; [exact MI1 | exact RB | lia | lia] | exact BL | lia | lia
| right; right; apply src_globA_of_chk; exact CHK
| intros _; eapply (unpoisoned_of_glob HIx); [exact HP1 | apply src_globA_of_chk; exact CHK | lia]
| lia | lia | lia
| replace (bv_unsigned sp + -48) with (bv_unsigned sp - 16 * 3) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | apply fsaved_refl | exact FRM | ].
intros A2 m2 md2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 INV2 FS2 FR2 _.
pose proof INV2 as (buf2 & cap2 & bpos2 & content2 & errv2 & B2 & HP2 & PB2 & CH2 & _ & _ & ERR2 & ST2 & HPR2 & VM2 & Hb2 & Hc2 & HB2 & HD2).
apply Forall_inv in CH2. cbn [fst snd] in CH2.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI2. cbn [hl_segs hla_base A4L A4H] in MI2.
a4l. reenterA asegs A4L HIx asegs_wx HP2.
step. if_truex.
do 5 step. step. step.
evt_done5. apply K. unfold ser_postA.
exists m2, a0', errv2, buf2, cap2, bpos2, content2, B2.
split; [apply ret_statew_intro; [exact FS2 | intros _; exact FR2]|].
split; [exact VM2|].
split; [release_frame CH2 ST2 (bv_unsigned sp); exact ST2|].
split; [exact HPR2|]. split; [exact ERR2|]. split; [exact HP2|]. split; [exact PB2|].
split; [lia|]. split; [exact Hc2|]. split; lia. }

step. if_cases Kb; fold_mkR.
-
do 5 step. fold_mkR.
eapply (TAILK 0x236e0 5 ser_falseA); [vm_compute; reflexivity | reflexivity | lia | lia | lia | vm_compute; reflexivity].
-
do 6 step. fold_mkR.
eapply (TAILK 0x236c0 4 ser_trueA); [vm_compute; reflexivity | reflexivity | lia | lia | lia | vm_compute; reflexivity].
Qed.
End Ser.
End RC__1.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun Qfw3_c1.Mq2.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa Q4v2.Mq0 QgHv.Mq0 Q1Y6.Mq1 QsKa.Mq6 QlKV.Mq2 QsKa Q9O6.Mq2 QL3k.Mq1.
Import QWxq_c1 QsjA.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).

Lemma disjoint_from_above : forall W c a n, Forall (fun iv : Z * Z => c <= fst iv) W -> a + n <= c -> disjoint_from W a n.
Proof.
induction W as [|[l h] W IH]; intros c a n HW Han; cbn [disjoint_from]; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. cbn [fst] in H1. split; [left; lia | eapply IH; eassumption].
Qed.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section K0.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Lemma heapA_blocks_below : forall A LBx LMx FR B m md W a n, HEAPAx A LBx LMx FR B m md -> In (a, n) (LBx ++ LMx) ->
Forall (fun iv : Z * Z => alloc_ceiling <= fst iv) W -> disjoint_from W a n.
Proof.
intros A LBx LMx FR B m md W a n HP Hin HW.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a n HP Hin) as (_ & _ & _ & Hhi & _).
eapply disjoint_from_above; eassumption.
Qed.

Lemma blk_granS : forall A LBx LMx FR B m md a n i, HEAPAx A LBx LMx FR B m md -> In (a, n) LBx -> 0 <= i -> 8 * i + 8 <= n ->
ro_cells asegs m (a / 8 + 2147450880 + i) [C1 (Z_to_bv 8 0)].
Proof.
intros A LBx LMx FR B m md a n i HP Hin Hi Hn.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ a n HP Hin) as SH. unfold shad in SH. cbn [hl_sb hl_segs hla_base A4L A4H] in SH. unfold A_SB in SH.
assert (E : 8 * i / 8 = i) by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
pose proof (shadow_at0 asegs m (a / 8 + 2147450880) n (8 * i) ltac:(lia) ltac:(rewrite E; lia) SH) as X. rewrite E in X. exact X.
Qed.

End K0.

Section K.
Variable HIx : heap_iface_A A4L.
Variables (sp : word) (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS0 : list frame) (B0 : bud) (pb lo : Z).
Variables (bpos0 cap0 w : Z).
Let usp := bv_unsigned sp.
Hypothesis HT : usp <= hiA_top A4L HIx.
Notation ser_memx := (ser_memA HIx sp m0 md0 LB LM FRS0 B0 pb lo bpos0 cap0 w).

Lemma ser_memA_stackW : forall A FRSc FA CH CH' e m mc md W,
ser_memx A FRSc FA CH e m md -> munch W m mc -> wmono asegs m mc -> mem_inv asegs mc ->
Forall (fun iv : Z * Z => alloc_ceiling <= fst iv /\ snd iv <= usp) W ->
Forall (fun ch => rw_cells asegs mc (fst ch) (snd ch)) CH' -> Forall (chunk_ok LB LM FRSc FA) CH' -> stk asegs mc lo FA -> alloc_ceiling <= usp ->
ser_memx A FRSc FA CH' e mc md.
Proof.
intros A FRSc FA CH CH' e m mc md W (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & Hbp & Hcap & HBB & HBD)
MU WM MIc HW CHc CHokc STc LOU.
assert (HW1 : Forall (fun iv : Z * Z => alloc_ceiling <= fst iv) W) by (eapply Forall_impl; [| exact HW]; intros iv [H _]; exact H).
pose proof alloc_ceiling_range as ACR.
exists buf, cap, bpos, content, errv, B.
split.
{ eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MIc].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU).
eapply Forall_impl; [| exact HW]. intros iv [H1 H2]. left. unfold usp in *. lia. }
destruct PB as (Hb0 & Hc0 & Hlen & PBS & PBUF).
split.
{ split; [exact Hb0|]. split; [exact Hc0|]. split; [exact Hlen|]. split.
- eapply (rw_cells_transport asegs W m mc); [exact PBS | exact MU | exact WM |].
eapply (heapA_blocks_below HIx _ _ _ _ _ _ _ W pb PB_SZ HP); [apply in_or_app; left; left; reflexivity | exact HW1].
- eapply (rw_cells_transport asegs W m mc); [exact PBUF | exact MU | exact WM |].
cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(apply in_or_app; left; right; left; reflexivity)) as (Hn & _ & _ & Hhi & _).
rewrite Z2Nat.id by lia. eapply disjoint_from_above; [exact HW1 | exact Hhi]. }
split; [exact CHc|]. split; [exact CHokc|]. split; [exact FSUB|].
split.
{ eapply (rw_cells_transport asegs W m mc); [exact ERR | exact MU | exact WM |].
eapply disjoint_from_above; [exact HW1|]. unfold A_ERRNO, A_TP. cbn [cells_size csize Nat.add]. unfold alloc_ceiling, sp_window_lo, stack_max_size in *. lia. }
split; [exact STc|].
split.
{ eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch A4H _ usp); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | | exact LOU |].
- intros bb Hbb. apply in_app_or in Hbb. apply in_or_app. destruct Hbb as [Hbb|Hbb]; [left; right; right; exact Hbb|].
right. apply in_app_or in Hbb. destruct Hbb as [Hbb|Hbb]; [apply in_or_app; left; exact Hbb | apply in_or_app; right; apply FSUB; exact Hbb].
- eapply Forall_impl; [| exact HW]. intros iv [H1 H2]. left. split; assumption. }
split; [exact VM|]. split; [exact Hbp|]. split; [exact Hcap|]. split; [exact HBB | exact HBD].
Qed.
End K.
End RC__1.
End Mq4.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa Q4v2.Mq0 QgHv.Mq0 Q1Y6.Mq1 QsKa.Mq6 QlKV.Mq2 QsKa Q9O6.Mq2 QL3k.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Notation b8 := (Z_to_bv 8) (only parsing).

Definition ADBL_STACK : Z := 144 + 8192.
Definition ADBL_MEMAPP_RET : Z := 0x9d59c.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section Dbl.
Variable HIx : heap_iface_A A4L.

Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud).
Variables (pb lo bpos0 cap0 : Z) (T : TSet).
Variables (q d Fr : Z).

Definition dblSaved : list cell := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Definition dblFF (j8 bufb jr : list byte) : list cell := [C8 (wz 1102416563); C8 (wz 0x19d61); C8 (wz 0x9d3bc); CB 8 j8; CB 128 bufb; CB 88 jr].
Definition dblSH (v : Z) (t8 : list byte) : list cell :=
[C1 (b8 241); C1 (b8 241); C1 (b8 241); C1 (b8 241);
C1 (b8 v); C1 (b8 v); C1 (b8 v); C1 (b8 v); C1 (b8 v); C1 (b8 v); C1 (b8 v); C1 (b8 v);
C1 (b8 v); C1 (b8 v); C1 (b8 v); C1 (b8 v); C1 (b8 v); C1 (b8 v); C1 (b8 v); C1 (b8 v);
C1 (b8 243); C1 (b8 243); C1 (b8 243); C1 (b8 243); CB 8 t8].

Definition dblCH (LOC : list cell) (j8 bufb jr t8 : list byte) (v : Z) : list (Z * list cell) :=
[(q, LOC); (bv_unsigned sp + -104, dblSaved); (Fr, dblFF j8 bufb jr); (Fr / 8 + 2147450880, dblSH v t8)].

Definition dbl_inv (v : Z) (A : ASA A4L HIx) (e : Z) (bufb : list byte) (m : word -> option byte) (md : config) : Prop :=
exists LOC j8 jr t8, cells_size LOC = Z.to_nat (24 + d) /\
ser_memA HIx sp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 9 A ((Fr, 2) :: FRS) q (dblCH LOC j8 bufb jr t8 v) e m md.
End Dbl.
End RC__1.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun Qfw3_c1.Mq2.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa Q4v2.Mq0 QgHv.Mq0 Q1Y6.Mq1 QsKa.Mq6 Q4xz QlKV.Mq2 QsKa Q9O6.Mq2 QL3k.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition lit_bytesA (a : Z) (k : nat) : list byte := match image_bytes asegs a k with Some bs => bs | None => [] end.
Definition LIT_LBRACK : list byte := Eval vm_compute in lit_bytesA 0x23800 1.
Definition LIT_RBRACK : list byte := Eval vm_compute in lit_bytesA 0x23840 1.
Definition LIT_SP_RBRACK : list byte := Eval vm_compute in lit_bytesA 0x23820 2.
Definition LIT_COMMA : list byte := Eval vm_compute in lit_bytesA 0x23440 1.
Definition LIT_SPACE : list byte := Eval vm_compute in lit_bytesA 0x23480 1.
Definition LIT_NULL : list byte := Eval vm_compute in lit_bytesA 0x23360 4.
Definition LIT_QUOTE : list byte := Eval vm_compute in lit_bytesA 0x234c0 1.

Section Lit.
Variable HIx : heap_iface_A A4L.
Variables (sp gp : word) (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS0 : list frame) (B0 : bud) (pb lo : Z).
Variables (bpos0 cap0 w : Z).
Let usp := bv_unsigned sp.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis HT : usp <= hiA_top A4L HIx.
Hypothesis CAP0 : 32 <= cap0 < 2^30.
Hypothesis TXT : bpos0 + w < 2^28.
Hypothesis NEED : ser_need cap0 bpos0 w <= bB B0.
Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.
Notation ser_memx := (ser_memA HIx sp m0 md0 LB LM FRS0 B0 pb lo bpos0 cap0 w).

Lemma ser_litA :
forall (lit k : Z) (bs : list byte),
ro_bytes_b asegs lit bs = true -> Z.of_nat (length bs) = k -> src_ro_chk lit k = true -> 0 < k < 2^31 -> 0 <= lit -> lit + k < 2^32 ->
forall (ret : Z) (x3 t0 t1 t2 x8 x9 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
(F Fc : bvmap 5 word) (fcc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (FRSc : list frame) (FA : Z) (CH : list (Z * list cell)) (e : Z),
ser_memx A FRSc FA CH e m md ->
0 <= e -> e + k <= w ->
lo <= FA - 112 - 4096 -> FA mod 16 = 0 -> FA <= usp -> 0 <= FA ->
x3 = gp -> 0 <= ret < 2^64 -> ret mod 2 = 0 ->
fsaved F Fc -> frm0 fcc ->
(forall (A' : ASA A4L HIx) m' md' (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F' fc',
ser_memx A' FRSc FA CH (e + k) m' md' -> fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A' T md' (MS (mkR (wz ret) (wz FA) gp (wz A_TP) t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7'
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6') F' (wz ret) fc' None m' (seg_rom asegs))) ->
AJ5 A4L HIx A T md (MS (mkR (wz ret) (wz FA) x3 (wz A_TP) t0 t1 t2 x8 x9 (wz pb) (wz lit) (wz k) a3 a4 a5 a6 a7
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) Fc (wz AMEMAPPEND) fcc None m (seg_rom asegs)).
Proof.
intros lit k bs RB BL CHK Hk Hl Hlk. intros until e. intros INV He Hek LOS FAA FAU FA0 X3 Hret Hret2 FS FRM K.
pose proof (ser_memA_mem_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
pose proof INV as (buf1 & cap1 & bpos1 & content1 & errv1 & B1 & HP1 & _).
eapply (ser_appendA HIx sp gp m0 md0 LB LM FRS0 B0 pb lo bpos0 cap0 w LO HT CAP0 TXT NEED OBL_REALLOC_NF) with (F := F) (sb := bs) (e := e);
[ exact INV | apply rodata_bytes_at; [exact MI | exact RB | lia | lia] | exact BL | lia | lia
| right; right; apply src_globA_of_chk; exact CHK
| intros _; eapply (unpoisoned_of_glob HIx); [exact HP1 | apply src_globA_of_chk; exact CHK | lia]
| exact He | exact Hek | exact LOS | exact FAA | exact FAU | exact FA0 | exact X3 | exact Hret | exact Hret2 | exact FS | exact FRM | ].
intros A2 m2 md2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 INV2 FS2 FR2 _.
eapply K; eassumption.
Qed.
End Lit.
End RC__1.
End Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpNt Q30W Qekr QkXq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa Q4v2.Mq0 QgHv.Mq0 Q1Y6.Mq1 QsKa.Mq6 QsKa.Mq7 QpNt.Mq4 QsKa.Mq5 Q30W.Mq1 Qekr.Mq1 QkXq.Mq1 QlKV.Mq2 QsKa Q9O6.Mq2 QL3k.Mq1.
Import QWxq_c1 QsjA.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).

Ltac fold_mkR :=
lazymatch goal with
| |- context [MS (TNode (TNode (TNode (TNode (TNode (TNode TEmpty (Some ?x31) TEmpty) (Some ?x15) TEmpty) (Some ?x7) (TNode TEmpty (Some ?x23) TEmpty)) (Some ?x3) (TNode (TNode TEmpty (Some ?x19) TEmpty) (Some ?x11) (TNode TEmpty (Some ?x27) TEmpty))) (Some ?x1) (TNode (TNode (TNode TEmpty (Some ?x17) TEmpty) (Some ?x9) (TNode TEmpty (Some ?x25) TEmpty)) (Some ?x5) (TNode (TNode TEmpty (Some ?x21) TEmpty) (Some ?x13) (TNode TEmpty (Some ?x29) TEmpty)))) None (TNode (TNode (TNode (TNode TEmpty (Some ?x16) TEmpty) (Some ?x8) (TNode TEmpty (Some ?x24) TEmpty)) (Some ?x4) (TNode (TNode TEmpty (Some ?x20) TEmpty) (Some ?x12) (TNode TEmpty (Some ?x28) TEmpty))) (Some ?x2) (TNode (TNode (TNode TEmpty (Some ?x18) TEmpty) (Some ?x10) (TNode TEmpty (Some ?x26) TEmpty)) (Some ?x6) (TNode (TNode TEmpty (Some ?x22) TEmpty) (Some ?x14) (TNode TEmpty (Some ?x30) TEmpty))))) ?F ?pc ?fc ?rv ?m ?ro] =>
change (TNode (TNode (TNode (TNode (TNode (TNode TEmpty (Some x31) TEmpty) (Some x15) TEmpty) (Some x7) (TNode TEmpty (Some x23) TEmpty)) (Some x3) (TNode (TNode TEmpty (Some x19) TEmpty) (Some x11) (TNode TEmpty (Some x27) TEmpty))) (Some x1) (TNode (TNode (TNode TEmpty (Some x17) TEmpty) (Some x9) (TNode TEmpty (Some x25) TEmpty)) (Some x5) (TNode (TNode TEmpty (Some x21) TEmpty) (Some x13) (TNode TEmpty (Some x29) TEmpty)))) None (TNode (TNode (TNode (TNode TEmpty (Some x16) TEmpty) (Some x8) (TNode TEmpty (Some x24) TEmpty)) (Some x4) (TNode (TNode TEmpty (Some x20) TEmpty) (Some x12) (TNode TEmpty (Some x28) TEmpty))) (Some x2) (TNode (TNode (TNode TEmpty (Some x18) TEmpty) (Some x10) (TNode TEmpty (Some x26) TEmpty)) (Some x6) (TNode (TNode TEmpty (Some x22) TEmpty) (Some x14) (TNode TEmpty (Some x30) TEmpty)))))
with (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
| |- _ => idtac
end.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section Ser.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.

Lemma ser_udA : ser_specA HIx ASER_UD (Sdouble true).
Proof.
unfold ser_specA. intros until errv. intros HP PB JN INCL JTX CAP TXT NEED FL Hlv Hlvd FRSN ST LO LOS SPA HT ERR JHX TP' RA FRM A0 A1 A2 A3 K.
destruct JN as (bits & ud & udn & uds & EREST & Hudn & NODE & CS). unfold jhdr_cells in NODE. cbn [app] in NODE.
subst a0 a1 a2 a3 tp REST.
cbn [app jtx] in JTX. rewrite Z.eqb_refl in JTX. injection JTX as <- _.
unfold ASER_UD, ser_budgetA, ASER_LEVEL, ASER_LEAF in *. cbn [sdepth Z.mul Z.add] in LOS.
word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
assert (INp : In (p, 48) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; apply INCL; left; reflexivity).
assert (INu : In (ud, udn) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; apply INCL; right; left; reflexivity).
assert (INuL : In (ud, udn) LB) by (apply INCL; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p 48 HP ltac:(apply in_or_app; left; exact INp)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ pb PB_SZ HP ltac:(apply in_or_app; left; left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(apply in_or_app; left; right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
destruct (key_stringA HIx _ _ _ _ _ _ _ ud udn uds HP INu CS) as (slack & STR & PAD & NN & UAL & UL & UPOS & UHI & USL).
clear CS.
unfold_consts.
shadow_inA A4L HIx HP INp SHp.
pose proof PB as (Hbp & Hcap & Hlen & PBS & PBUF).
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
pose proof alloc_ceiling_range as ACR.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 32%nat ST.
do 5 step. do 3 step. step.
asan_chkA.
do 4 step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
assert (HP1 : HEAPAx A ((pb, PB_SZ) :: (buf, cap) :: LB) LM FRS B m1 md) by (heap_nowA A4L HIx HP MU WM MI1).
assert (HPR1 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1).
{ eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros bb Hbb; apply in_app_or in Hbb; apply in_or_app; destruct Hbb as [Hbb|Hbb]; [left; right; right; exact Hbb | right; exact Hbb] | lia | solve_clientWA A4L HIx HP]. }
clear MU WM.

eapply (astrlen_any_A HIx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 md A _ LM FRS B ud udn ud lo uds slack);
a4l_goal; rewrite ?unsigned_lit by lia;
first [exact HP1 | exact INu | exact NN | exact STR | exact PAD | exact USL | exact ST | exact LO | exact MI1 | reflexivity | lia
| replace (bv_unsigned sp + -32) with (bv_unsigned sp - 16 * 2) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity | idtac].
intros x0 x1' x2 y1' y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 m3 MU3 WM3 MI3 STR3 ST3.
stash STR3.
transport_after_call asegs m1 m3 MU3 WM3; try match goal with H : mem_inv asegs m1 |- _ => clear H end.
unstash STR3.
assert (HP3 : HEAPAx A ((pb, PB_SZ) :: (buf, cap) :: LB) LM FRS B m3 md).
{ eapply (heapA_client_frame A4L HIx); [exact HP1 | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP1 MU3); solve_frameW_withA HP1 | exact WM3 | exact MI3]. }
assert (HPR13 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m1 m3).
{ eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU3 | exact WM3 |].
eapply (client_outsideA A4L HIx); [exact HP1 | intros bb Hbb; apply in_app_or in Hbb; apply in_or_app; destruct Hbb as [Hbb|Hbb]; [left; right; right; exact Hbb | right; exact Hbb] | lia | solve_clientWA A4L HIx HP1]. }
clear MU3 WM3.
pose proof (wmono_refl asegs m3) as WM. pose proof (munch_refl (@nil (Z * Z)) m3) as MU.
replace (ret_pc (Z_to_bv 64 646448)) with (Z_to_bv 64 646448) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
set (len := Z.of_nat (length uds)) in *.
assert (Hlen31 : 0 <= len < 2^31) by (unfold len; lia).
step. rewrite (unsigned_lit len) by lia. rewrite Z.add_0_r. rewrite swrap32_id by lia.
do 4 step. fold_mkR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
match goal with H : mem_inv asegs m4 |- _ => rename H into MI4 end.
assert (INV4 : ser_memA HIx sp m md LB LM FRS B pb lo bpos cap (16 + Z.max 0 (udn - 1)) A FRS (bv_unsigned sp + -32)
[(bv_unsigned sp + -32, [C8 s2; C8 s1; C8 s0; C8 ra])] 0 m4 md).
{ exists buf, cap, bpos, content, errv, B.
split; [heap_nowA A4L HIx HP3 MU WM MI4|].
split; [split; [lia|]; split; [lia|]; split; [exact Hlen|]; split; [exact PBS | exact PBUF]|].
split; [constructor; [exact FR | constructor]|].
split; [constructor; [left; cbn [fst]; lia | constructor]|].
split; [intros bb Hbb; exact Hbb|].
split; [exact ERR|]. split; [exact ST3|].
split. { eapply heap_pres_trans; [exact HPR1|]. eapply heap_pres_trans; [exact HPR13|].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |]. intros a Ha Hc. exact I. }
split; [apply model_vm_only_refl|].
split; [lia|]. split; [unfold ser_capb; lia|]. split; lia. }
pose proof INV4 as (buf4 & cap4 & bpos4 & content4 & errv4 & B4 & HP4 & _).
assert (SRC : bytes_at asegs m4 ud uds).
{ replace (uds ++ Z_to_bv 8 0 :: slack) with (uds ++ (Z_to_bv 8 0 :: slack)) in STR3 by reflexivity.
apply bytes_at_app in STR3. exact (proj1 STR3). }
evt_done5.
eapply (ser_appendA HIx sp gp m md LB LM FRS B pb lo bpos cap (16 + Z.max 0 (udn - 1)) LO HT CAP TXT NEED OBL_REALLOC_NF) with (F := F) (sb := uds) (e := 0);
[ exact INV4 | exact SRC | reflexivity | fold len; lia | lia
| left; exists ud, udn; split; [exact INuL | fold len; lia]
| intros Hk; eapply (unpoisoned_of_blk HIx); [exact HP4 | right; right; exact INuL | lia | fold len; lia | exact Hk]
| lia | fold len; lia | lia
| replace (bv_unsigned sp + -32) with (bv_unsigned sp - 16 * 2) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | apply fsaved_refl | exact FRM | ].
intros A2 m2 md2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 INV2 FS2 FR2 _.
pose proof INV2 as (buf2 & cap2 & bpos2 & content2 & errv2 & B2 & HP2 & PB2 & CH2 & _ & _ & ERR2 & ST2 & HPR2 & VM2 & Hb2 & Hc2 & HB2 & HD2).
apply Forall_inv in CH2. cbn [fst snd] in CH2.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI2. cbn [hl_segs hla_base A4L A4H] in MI2.
a4l. reenterA asegs A4L HIx asegs_wx HP2.
step. do 4 step. step. step.
evt_done5. apply K. unfold ser_postA.
exists m2, (Z_to_bv 64 len), errv2, buf2, cap2, bpos2, content2, B2.
split; [apply ret_statew_intro; [exact FS2 | intros _; exact FR2]|].
split; [exact VM2|].
split; [release_frame CH2 ST2 (bv_unsigned sp); exact ST2|].
split; [exact HPR2|]. split; [exact ERR2|]. split; [exact HP2|]. split; [exact PB2|].
split; [fold len in Hb2; lia|]. split; [exact Hc2|]. split; lia.
Qed.
End Ser.
End RC__1.
End Mq7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi Qx2n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun QWxq_c1.Mq0 Qfw3_c1.Mq2 Qc3B.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn.
Import QgoP.
Import QZAi.Mq1 Qx2n.
Import Q7UD QXUB.Mq0 Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq4 QlKV.Mqa QsKa.Mq0 QsKa.Mq8 Qw5U.Mq0.

Import Qvmy.Mq0 Qawr.Mq0.
Import Qw5U.Mq3 QL3k.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section MStrtodBridge.
Variable HIx : heap_iface_A A4L.
Hypothesis SCANH : scan_total_stmtA.
Hypothesis STRTOD : astrtod_total_stmt.

Definition STRTOD_STK_A : Z := 12288.
Definition strtod_A_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud)
(str : list byte) (SA R lo : Z) (rj errv : word),
HEAPA A4L HIx A LB LM FRS B m md ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - STRTOD_STK_A ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 SA -> a1 = Z_to_bv 64 R ->
bytes_at asegs m SA (str ++ [QgoP.b0]) -> ~ In QgoP.b0 str ->
Z.of_nat (length str) < 2^31 ->
(exists a n, In (a, n) LB /\ a <= SA /\ SA + Z.of_nat (length str) + 1 <= a + n) ->
(exists Fc kc, In (Fc, kc) FRS /\ Fc <= R /\ R + 8 <= Fc + fr_size kc - 8) ->
rw_cells asegs m R [C8 rj] -> R mod 8 = 0 ->
frm0 fc ->
(forall ms' m' (a0' v e' : word),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0' m' ms' ->
stk asegs m' lo (bv_unsigned sp) ->
heap_presD R (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
rw_cells asegs m' R [C8 v] -> rw_cells asegs m' A_ERRNO [C4 e'] ->
HEAPA A4L HIx A LB LM FRS B m' md ->
AJ5 A4L HIx A T md ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xda5f4) fc None m (seg_rom asegs)).

Theorem strtod_A_of_musl : strtod_A_stmt.
Proof.
unfold strtod_A_stmt, STRTOD_STK_A. intros until errv. intros HP ST LO LOS SPA HT ERR TP RA A0 A1 STR NUL LS (ab & nb & INB & HB1 & HB2) (Fc & kc & INF & HF1 & HF2) RC RAL FRM K.
subst a0 a1 tp.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. change (hl_segs A4L) with asegs in MI.
pose proof alloc_ceiling_range as ACR.
pose proof (hiA_top_le A4L HIx) as HT47.
destruct (heapA_canary A4L HIx _ _ _ _ _ _ _ HP) as (g & CAN1 & CAN2 & _). cbn [hl_got_guard hl_guard A4L A4H hla_base] in CAN1, CAN2.
assert (INBA : In (ab, nb) (LB ++ LM)) by (apply in_or_app; left; exact INB).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ ab nb HP INBA) as (_ & _ & Hb0 & Hbc & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ ab nb HP INBA) as Hbimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hbimg.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & _ & HF0 & HFc & _).
pose proof (frame_above_img HIx _ _ _ _ _ _ _ _ _ HP INF) as HFhi. cbn [hl_img_hi A4H] in HFhi.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INBA) as DF.
set (txtZ := map bv_unsigned str ++ [0]).
assert (FA : Forall (fun c => 0 <= c < 256) (map bv_unsigned str)).
{ apply Forall_map. apply Forall_forall. intros b _. pose proof (bv_unsigned_in_range 8 b) as R0. unfold bv_modulus in R0. cbn in R0. lia. }
destruct (SCANH (map bv_unsigned str) FA) as (bits & used & SCAN & U0).
assert (LTX : zlength txtZ = Z.of_nat (length str) + 1) by (unfold zlength, txtZ; rewrite length_app, length_map; cbn [length]; lia).
assert (LPRE : zlength (map bv_unsigned str) = Z.of_nat (length str)) by (unfold zlength; rewrite length_map; reflexivity).
unfold A_ERRNO, A_TP in *.
a4l.
reenterA asegs A4L HIx asegs_wx HP.
eapply evt_cut.
{ eapply STRTOD with (T := SA) (PE := R) (txt := txtZ) (pre := map bv_unsigned str) (post := []) (lo := lo) (bits := bits) (used := used) (canary := g).
- unfold txtZ. rewrite map_app. cbn [map]. rewrite map_unsigned_bytesA. exact STR.
- unfold txtZ. apply Forall_app. split; [exact FA | constructor; [lia | constructor]].
- reflexivity.
- rewrite LPRE. lia.
- rewrite LTX. lia.
- exact RC.
- exact SCAN.
- exact ST.
- unfold ASTRTOD_DEPTH. lia.
- lia.
- lia.
- lia.
- rewrite LTX. lia.
- left. rewrite LTX. split; lia.
- lia.
- lia.
- left. lia.
- rewrite LTX. lia.
- exact CAN1.
- exact CAN2.
- unfold A_TP. exact ERR.
- exact MI.
- exact FRM.
- reflexivity.
- reflexivity.
- reflexivity. }
cbv beta delta [astrtod_post]. unfold A_TP. change (6434400 - 164) with 6434236. change (6434400 - 160) with 6434240.
intros ms' (q0 & q1 & q2 & qa0 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & F' & fc' & m' & ev' & -> & MU & WM & MI' & FRM' & FKEEP & FA0 & ST' & PE' & TXT' & ERR' & USED).
evt_done5.
eapply (K _ m' qa0 _ ev').
- apply ret_statew_intro; [| intros _; exact FRM'].
intros k Hk. cbn [FSAVED In] in Hk.
repeat (destruct Hk as [<- | Hk]); [..| destruct Hk]; apply FKEEP; vm_compute; lia.
- exact ST'.
- eapply (presD_private HIx _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp) R HP MU WM); [| lia |].
+ intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. exact Hb.
+ apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]].
* left. cbn [fst snd]. lia.
* right; right; right; right. cbn [fst snd]. lia.
* right; right; left. intros x Hx. cbn [fst snd] in Hx. cbn [hl_scratch A4L A4H hla_base]. unfold A_TP. lia.
- exact PE'.
- exact ERR'.
- eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MI'].
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP MU).
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]].
+ left. cbn [fst snd]. lia.
+ right; right; right. exists Fc, kc. split; [exact INF|]. left. cbn [fst snd]. lia.
+ right; right; left. intros x Hx. cbn [fst snd] in Hx. cbn [hl_scratch A4L A4H hla_base]. unfold A_TP. lia.
Qed.
End MStrtodBridge.
End RC__1.
End Mq8.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq9.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj Q4v2 QgHv Q1Y6 QsKa.Mqf. Import QlKV.Mq2 QsKa. Import Q9O6.Mq5 QL3k.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Local Ltac flia := Qo9G.term_slim ltac:(Zify.zify; xlia zchecker).

Definition AESC_STACK : Z := 240 + 12256.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section AEsc.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Definition esc_specA : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud)
(pb buf bpos cap Sa n fl lo sa sk : Z) (src content : list byte) (errv : word),
HEAPAx A ((pb, PB_SZ) :: (buf, cap) :: LB) LM FRS B m md ->
pbuf_core asegs m pb buf bpos cap content ->
In (sa, sk) LB -> sa <= Sa -> Sa + n <= sa + sk ->
bytes_at asegs m Sa src -> Z.of_nat (length src) = n -> 0 <= n < 2^31 ->
32 <= cap < 2^30 -> bpos + 6 * n < 2^28 -> ser_need cap bpos (6 * n) <= bB B ->
aflags_ok fl ->
Z.of_nat (length FRS) + 1 < 4096 ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AESC_STACK ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> JHEX_A m ->
tp = wz A_TP -> bv_unsigned ra mod 2 = 0 -> frm0 fc ->
a0 = wz pb -> a1 = wz Sa -> a2 = wz n -> a3 = wz fl ->
(forall ms' md' A', ser_postA HIx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B pb cap bpos (6 * n) lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz AESCAPE) fc None m (seg_rom asegs)).

Variables (sp gp : word) (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS0 : list frame) (B0 : bud) (pb lo : Z).
Variables (bpos0 cap0 w : Z).
Let usp := bv_unsigned sp.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis HT : usp <= hiA_top A4L HIx.
Hypothesis CAP0 : 32 <= cap0 < 2^30.
Hypothesis TXT : bpos0 + w < 2^28.
Hypothesis NEED : ser_need cap0 bpos0 w <= bB B0.
Hypothesis JHEX0 : JHEX_A m0.
Hypothesis ESC : esc_specA.
Notation ser_memx := (ser_memA HIx sp m0 md0 LB LM FRS0 B0 pb lo bpos0 cap0 w).

Lemma ser_escapeA :
forall (ret : Z) (x3 t0 t1 t2 x8 x9 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
(F Fc : bvmap 5 word) (fcc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (FRSc : list frame) (FA : Z) (CH : list (Z * list cell)) (e Sa n fl sa sk : Z) (src : list byte),
ser_memx A FRSc FA CH e m md ->
In (sa, sk) LB -> sa <= Sa -> Sa + n <= sa + sk ->
bytes_at asegs m Sa src -> Z.of_nat (length src) = n -> 0 <= n < 2^31 ->
0 <= e -> e + 6 * n <= w ->
aflags_ok fl -> Z.of_nat (length FRSc) + 1 < 4096 ->
lo <= FA - AESC_STACK -> FA mod 16 = 0 -> FA <= usp -> 0 <= FA ->
x3 = gp -> 0 <= ret < 2^64 -> ret mod 2 = 0 ->
fsaved F Fc -> frm0 fcc ->
(forall (A' : ASA A4L HIx) m' md' (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F' fc',
ser_memx A' FRSc FA CH (e + 6 * n) m' md' -> fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A' T md' (MS (mkR (wz ret) (wz FA) gp (wz A_TP) t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7'
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6') F' (wz ret) fc' None m' (seg_rom asegs))) ->
AJ5 A4L HIx A T md (MS (mkR (wz ret) (wz FA) x3 (wz A_TP) t0 t1 t2 x8 x9 (wz pb) (wz Sa) (wz n) (wz fl) a4 a5 a6 a7
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) Fc (wz AESCAPE) fcc None m (seg_rom asegs)).
Proof.
intros until src. intros INV INs Hs1 Hs2 SRC SRCL Hn He Hew FL FRN LOS FAA FAU FA0 -> Hret Hret2 FS FRM K.
destruct INV as (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & Hbp & Hcap & HBB & HBD).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
assert (U2 : bv_unsigned (wz FA) = FA) by (apply unsigned_lit; unfold usp in *; lia).
assert (CAPB : ser_capb cap0 bpos0 w < 2^30) by (unfold ser_capb; flia).
assert (NEEDc : ser_need cap bpos (6 * n) <= bB B).
{ eapply (ser_need_step cap0 cap bpos0 bpos w (6 * n) (bB B0) (bB B)); [exact Hcap | lia | exact NEED | exact HBB]. }
assert (JH : JHEX_A m) by (eapply JHEX_A_pres; [exact HPR | exact JHEX0]).
eapply ESC with (A := A) (LB := LB) (LM := LM) (FRS := FRSc) (B := B) (buf := buf) (bpos := bpos) (cap := cap) (lo := lo) (content := content) (errv := errv)
(Sa := Sa) (n := n) (fl := fl) (sa := sa) (sk := sk) (src := src);
rewrite ?U2.
- exact HP.
- exact PB.
- exact INs.
- exact Hs1.
- exact Hs2.
- exact SRC.
- exact SRCL.
- exact Hn.
- lia.
- lia.
- exact NEEDc.
- exact FL.
- exact FRN.
- exact ST.
- exact LO.
- exact LOS.
- exact FAA.
- unfold usp in *. lia.
- exact ERR.
- exact JH.
- reflexivity.
- rewrite unsigned_lit by lia. exact Hret2.
- exact FRM.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- intros ms' md' A' POST.
destruct POST as (m' & r & errv' & buf' & cap' & bpos' & content' & B' & RS & VM' & ST' & HPR' & ERR' & HP' & PB' & Hbp' & Hcap' & HBB' & HBD').
destruct RS as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F' & fc' & -> & FS' & FR').
rewrite U2 in ST', HPR'.
replace (ret_pc (wz ret)) with (wz ret) by (symmetry; apply ret_pc_even; [lia | exact Hret2]).
apply K; [| eapply fsaved_trans; [exact FS | exact FS'] | exact (FR' FRM)].
pose proof (ser_capb_mono cap0 cap bpos0 bpos w (6 * n) Hcap ltac:(lia)) as MONO.
exists buf', cap', bpos', content', errv', B'.
split; [exact HP'|]. split; [exact PB'|].
split; [eapply chunks_pres; [exact HPR' | exact CHok | exact CHm]|]. split; [exact CHok|]. split; [exact FSUB|].
split; [exact ERR'|]. split; [exact ST'|].
split. { eapply heap_pres_trans; [exact HPR | eapply heap_pres_weaken; [exact HPR' | unfold usp in *; lia |]].
intros bb Hbb. apply in_app_or in Hbb. apply in_or_app. destruct Hbb as [Hbb|Hbb]; [left; exact Hbb | right].
apply in_app_or in Hbb. apply in_or_app. destruct Hbb as [Hbb|Hbb]; [left; exact Hbb | right; apply FSUB; exact Hbb]. }
split; [eapply model_vm_only_trans; [exact VM | exact VM']|].
split; [lia|]. split; [lia|]. split; [lia | lia].
Qed.
End AEsc.
End RC__1.
End Mq9.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSHS Qc5u QAzu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqa.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw QkMG. Import QG8z Qdyh.Mq3 Qdyh.Mq6.
Import Qhd4 Qwm6.
Import QbFI.
Import Qwm6.Mq4 QlKV.Mqi QsKa.Mqd Qiiq QSHS Ql4f.Mq4 QsKa.Mqh QrQv.Mq4 QYZ0.Mq8.
Import Qc5u QAzu.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition pe_jt2A (c : Z) : Z :=
match c with
| 34 => 0x98a00
| 39 => 0x989e0
| 45 => 0x94d04
| 48 => 0x94d04 | 49 => 0x94d04 | 50 => 0x94d04 | 51 => 0x94d04 | 52 => 0x94d04
| 53 => 0x94d04 | 54 => 0x94d04 | 55 => 0x94d04 | 56 => 0x94d04 | 57 => 0x94d04
| 70 => 0x95690
| 73 => 0x95b64
| 78 => 0x95b04
| 84 => 0x95690
| 91 => 0x98900
| 102 => 0x95690
| 105 => 0x95b64
| 110 => 0x95b04
| 116 => 0x95690
| 123 => 0x98820
| _ => 0x99c70
end.

Definition pe_jtab2A : list byte := Eval vm_compute in match image_bytes asegs 0x22f90 360 with Some bs => bs | None => [] end.
Lemma pe_jtab2A_ro : forall m, mem_inv asegs m -> ro_cells asegs m 0x22f90 [CB 360 pe_jtab2A].
Proof.
intros m MI. change 360%nat with (length pe_jtab2A).
apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ].
change (Z.of_nat (length pe_jtab2A)) with 360%Z. lia.
Qed.

Lemma ro_cells_bytes_atA : forall segs m A cs, ro_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof. intros segs m A cs [_ H]. exact H. Qed.

Section PeSStartDA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.

Ltac pe_openA STC INV :=
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR); pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk);
destruct INV as [CORE REST];
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR);
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).

Lemma start_dispatch_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
(forall a1' a5',
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jt2A (bv_unsigned cb)) (t_co ts) gp t0 a0 a1' a2 a3 a4 a5' a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m)) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_start) (t_co ts) gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC INV K. pe_openA STC INV.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & FF & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (pe_jtab2A_ro m MI) as JT.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear TOK PB TSK REST LV OBJ HPR BUD STR ERR SBin.
reenterA asegs A4L HIx asegs_wx HP. unfold ST_start. cbn [pe_jtA].
step. step.
change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)).
step. step.
destruct (Z_lt_dec (bv_unsigned cb) 34) as [LT | GE].
-
replace (Z_to_bv 64 (bv_unsigned cb + -34)) with (Z_to_bv 64 (bv_unsigned cb + -34 + 2^64)).
2:{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite <- (Z_mod_plus_full (bv_unsigned cb + -34) 1 (2^64)). f_equal. }
step. if_falsex. step. evt_done5.
replace (pe_jt2A (bv_unsigned cb)) with 0x99c70 in K.
2:{ assert (R : 0 <= bv_unsigned cb <= 33) by lia. clear - R. enum_from (bv_unsigned cb) 0%Z 34%nat; reflexivity. }
apply K.
- destruct (Z_lt_dec 123 (bv_unsigned cb)) as [GT | LE].
+ step. if_falsex. step. evt_done5.
replace (pe_jt2A (bv_unsigned cb)) with 0x99c70 in K. 2:{ assert (R : 124 <= bv_unsigned cb <= 255) by lia. clear - R. enum_from (bv_unsigned cb) 124%Z 132%nat; reflexivity. }
apply K.
+ step. if_truex. step.
rewrite (unsigned_lit (bv_unsigned cb + -34)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
step. step. step.
pose proof (bytes_at_read asegs m 0x22f90 pe_jtab2A ((bv_unsigned cb + -34) * 4) 4 (ro_cells_bytes_atA _ _ _ _ JT) ltac:(lia)
ltac:(change (length pe_jtab2A) with 360%nat; lia)) as RD.
unfold wa in RD. replace (0x22f90 + (bv_unsigned cb + -34) * 4) with ((bv_unsigned cb + -34) * 4 + 143248) in RD by lia.
step. step. step.
evt_done5.
assert (R : 34 <= bv_unsigned cb <= 123) by lia.
match goal with |- AJ5 _ _ _ _ _ (MS _ _ ?pc _ _ _ _) =>
replace pc with (Z_to_bv 64 (pe_jt2A (bv_unsigned cb))); [apply K |] end.
clear - R. enum_from (bv_unsigned cb) 34%Z 90%nat; apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma start_default_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_ERR2 gp t0 (Z_to_bv 64 (pf_lenr pf)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 4) a1 a2 a3 a4 a5 a6 a7 s3 (Z_to_bv 64 (pf_sb pf + t_co ts)) s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x99c70 (t_co ts) gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC INV K. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & _ & _).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
unfold pe_msA, pe_msO in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (TST depth levels co pb pbs x obj objs objbs))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
unfold APE_ERR2 in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear TOK PB TSK REST LV OBJ HPR BUD STR ERR SBin.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_rechkB.
step. step.
evt_done5.
exact K.
Qed.
End PeSStartDA.
End RC__1.
End Mqa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRBl QUrr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqb.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj Q4v2 QgHv Q1Y6 QsKa.Mqf QUrr. Import QlKV.Mq2 QsKa. Import Q9O6.Mq5 QL3k.Mq4.
Import QWxq_c1 QsjA.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).

Ltac fold_mkR :=
lazymatch goal with
| |- context [MS (TNode (TNode (TNode (TNode (TNode (TNode TEmpty (Some ?x31) TEmpty) (Some ?x15) TEmpty) (Some ?x7) (TNode TEmpty (Some ?x23) TEmpty)) (Some ?x3) (TNode (TNode TEmpty (Some ?x19) TEmpty) (Some ?x11) (TNode TEmpty (Some ?x27) TEmpty))) (Some ?x1) (TNode (TNode (TNode TEmpty (Some ?x17) TEmpty) (Some ?x9) (TNode TEmpty (Some ?x25) TEmpty)) (Some ?x5) (TNode (TNode TEmpty (Some ?x21) TEmpty) (Some ?x13) (TNode TEmpty (Some ?x29) TEmpty)))) None (TNode (TNode (TNode (TNode TEmpty (Some ?x16) TEmpty) (Some ?x8) (TNode TEmpty (Some ?x24) TEmpty)) (Some ?x4) (TNode (TNode TEmpty (Some ?x20) TEmpty) (Some ?x12) (TNode TEmpty (Some ?x28) TEmpty))) (Some ?x2) (TNode (TNode (TNode TEmpty (Some ?x18) TEmpty) (Some ?x10) (TNode TEmpty (Some ?x26) TEmpty)) (Some ?x6) (TNode (TNode TEmpty (Some ?x22) TEmpty) (Some ?x14) (TNode TEmpty (Some ?x30) TEmpty))))) ?F ?pc ?fc ?rv ?m ?ro] =>
change (TNode (TNode (TNode (TNode (TNode (TNode TEmpty (Some x31) TEmpty) (Some x15) TEmpty) (Some x7) (TNode TEmpty (Some x23) TEmpty)) (Some x3) (TNode (TNode TEmpty (Some x19) TEmpty) (Some x11) (TNode TEmpty (Some x27) TEmpty))) (Some x1) (TNode (TNode (TNode TEmpty (Some x17) TEmpty) (Some x9) (TNode TEmpty (Some x25) TEmpty)) (Some x5) (TNode (TNode TEmpty (Some x21) TEmpty) (Some x13) (TNode TEmpty (Some x29) TEmpty)))) None (TNode (TNode (TNode (TNode TEmpty (Some x16) TEmpty) (Some x8) (TNode TEmpty (Some x24) TEmpty)) (Some x4) (TNode (TNode TEmpty (Some x20) TEmpty) (Some x12) (TNode TEmpty (Some x28) TEmpty))) (Some x2) (TNode (TNode (TNode TEmpty (Some x18) TEmpty) (Some x10) (TNode TEmpty (Some x26) TEmpty)) (Some x6) (TNode (TNode TEmpty (Some x22) TEmpty) (Some x14) (TNode TEmpty (Some x30) TEmpty)))))
with (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
| |- _ => idtac
end.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition ser_trueA : list byte := Eval vm_compute in match image_bytes asegs 0x23720 4 with Some bs => bs | None => [] end.
Definition ser_falseA : list byte := Eval vm_compute in match image_bytes asegs 0x23740 5 with Some bs => bs | None => [] end.

Section Ser.
Variable HIx : heap_iface_A A4L.
Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.

Lemma ser_boolA : ser_specA HIx ASER_BOOL Sbool.
Proof.
unfold ser_specA. intros until errv. intros HP PB JN INCL JTX CAP TXT NEED FL Hlv Hlvd FRSN ST LO LOS SPA HT ERR JHX TP' RA FRM A0 A1 A2 A3 K.
destruct JN as (b & junk & EREST & NODE). unfold jhdr_cells in NODE. cbn [app] in NODE.
subst a0 a1 a2 a3 tp REST.
cbn [app jtx] in JTX. rewrite Z.eqb_refl in JTX. injection JTX as <- _.
unfold ASER_BOOL, ser_budgetA, ASER_LEVEL, ASER_LEAF in *. cbn [sdepth Z.mul Z.add] in LOS.
word_range sp SPR.
destruct FL as [Rfl FL58].
assert (FL32 : Z.land fl 32 = 0) by (replace 32 with (Z.land 58 32) by reflexivity; rewrite Z.land_assoc, FL58; reflexivity).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
assert (INp : In (p, 48) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; apply INCL; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p 48 HP ltac:(apply in_or_app; left; exact INp)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ pb PB_SZ HP ltac:(apply in_or_app; left; left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(apply in_or_app; left; right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
unfold_consts.
shadow_inA A4L HIx HP INp SHp.
pose proof PB as (Hbp & Hcap & Hlen & PBS & PBUF).
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
pose proof alloc_ceiling_range as ACR.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 48%nat ST.
do 6 bstep.
do 6 bstep. rewrite (unsigned_lit fl) by lia. rewrite FL32.
bstep. if_truex.
bstep. asan_chkA.
bstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
assert (INV1 : ser_memA HIx sp m md LB LM FRS B pb lo bpos cap 8 A FRS (bv_unsigned sp + -48)
[(bv_unsigned sp + -48, [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 junk0))))); C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])] 0 m1 md).
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

assert (TAILK : forall (lit k : Z) (bs : list byte) (t0_ t1_ t2_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ : word),
ro_bytes_b asegs lit bs = true -> Z.of_nat (length bs) = k -> 0 < k <= 5 -> 0 <= lit -> lit + k < 2^32 -> src_ro_chk lit k = true ->
evt asegs (AJ5e A4L HIx A T md)
(MS (mkR (Z_to_bv 64 0x9c59c) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 6444320) t0_ t1_ t2_ (Z_to_bv 64 pb) (Z_to_bv 64 p)
(Z_to_bv 64 pb) (Z_to_bv 64 lit) (Z_to_bv 64 k) (Z_to_bv 64 fl) a4_ a5_ a6_ a7_ (Z_to_bv 64 0) (Z_to_bv 64 2147450880)
s4 s5 s6 s7 s8 s9 s10 s11 t3_ t4_ t5_ t6_)
F (Z_to_bv 64 0x9b4fc) fc None m1 (seg_rom asegs))).
{ intros lit k bs t0_ t1_ t2_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ RB BL Hk Hl Hlk CHK.
pose proof INV1 as (buf1 & cap1 & bpos1 & content1 & errv1 & B1 & HP1 & _).
evt_done5.
eapply (ser_appendA HIx sp gp m md LB LM FRS B pb lo bpos cap 8 LO HT CAP TXT NEED OBL_REALLOC_NF) with (F := F) (sb := bs) (e := 0);
[ exact INV1 | apply rodata_bytes_at; [exact MI1 | exact RB | lia | lia] | exact BL | lia | lia
| right; right; apply src_globA_of_chk; exact CHK
| intros _; eapply (unpoisoned_of_glob HIx); [exact HP1 | apply src_globA_of_chk; exact CHK | lia]
| lia | lia | lia
| replace (bv_unsigned sp + -48) with (bv_unsigned sp - 16 * 3) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | apply fsaved_refl | exact FRM | ].
intros A2 m2 md2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 INV2 FS2 FR2 _.
pose proof INV2 as (buf2 & cap2 & bpos2 & content2 & errv2 & B2 & HP2 & PB2 & CH2 & _ & _ & ERR2 & ST2 & HPR2 & VM2 & Hb2 & Hc2 & HB2 & HD2).
apply Forall_inv in CH2. cbn [fst snd] in CH2.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI2. cbn [hl_segs hla_base A4L A4H] in MI2.
a4l. reenterA asegs A4L HIx asegs_wx HP2.
bstep. if_truex.
do 5 bstep. bstep. bstep.
evt_done5. apply K. unfold ser_postA.
exists m2, a0', errv2, buf2, cap2, bpos2, content2, B2.
split; [apply ret_statew_intro; [exact FS2 | intros _; exact FR2]|].
split; [exact VM2|].
split; [release_frame CH2 ST2 (bv_unsigned sp); exact ST2|].
split; [exact HPR2|]. split; [exact ERR2|]. split; [exact HP2|]. split; [exact PB2|].
split; [lia|]. split; [exact Hc2|]. split; lia. }

bstep. if_cases Kb; fold_mkR.
-
do 5 bstep. fold_mkR.
eapply (TAILK 0x23740 5 ser_falseA); [vm_compute; reflexivity | reflexivity | lia | lia | lia | vm_compute; reflexivity].
-
do 6 bstep. fold_mkR.
eapply (TAILK 0x23720 4 ser_trueA); [vm_compute; reflexivity | reflexivity | lia | lia | lia | vm_compute; reflexivity].
Qed.
End Ser.
End RC__1.
End Mqb.

Module Mqc.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun Qfw3_c1.Mq2.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj Q4v2 QgHv Q1Y6 QsKa.Mqf. Import QlKV.Mq2 QsKa. Import Q9O6.Mq5 QL3k.Mq4.
Import QWxq_c1 QsjA.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).

Lemma disjoint_from_above : forall W c a n, Forall (fun iv : Z * Z => c <= fst iv) W -> a + n <= c -> disjoint_from W a n.
Proof.
induction W as [|[l h] W IH]; intros c a n HW Han; cbn [disjoint_from]; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. cbn [fst] in H1. split; [left; lia | eapply IH; eassumption].
Qed.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section K0.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Lemma heapA_blocks_below : forall A LBx LMx FR B m md W a n, HEAPAx A LBx LMx FR B m md -> In (a, n) (LBx ++ LMx) ->
Forall (fun iv : Z * Z => alloc_ceiling <= fst iv) W -> disjoint_from W a n.
Proof.
intros A LBx LMx FR B m md W a n HP Hin HW.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a n HP Hin) as (_ & _ & _ & Hhi & _).
eapply disjoint_from_above; eassumption.
Qed.

Lemma blk_granS : forall A LBx LMx FR B m md a n i, HEAPAx A LBx LMx FR B m md -> In (a, n) LBx -> 0 <= i -> 8 * i + 8 <= n ->
ro_cells asegs m (a / 8 + 2147450880 + i) [C1 (Z_to_bv 8 0)].
Proof.
intros A LBx LMx FR B m md a n i HP Hin Hi Hn.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ a n HP Hin) as SH. unfold shad in SH. cbn [hl_sb hl_segs hla_base A4L A4H] in SH. unfold A_SB in SH.
assert (E : 8 * i / 8 = i) by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
pose proof (shadow_at0 asegs m (a / 8 + 2147450880) n (8 * i) ltac:(lia) ltac:(rewrite E; lia) SH) as X. rewrite E in X. exact X.
Qed.

End K0.

Section K.
Variable HIx : heap_iface_A A4L.
Variables (sp : word) (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS0 : list frame) (B0 : bud) (pb lo : Z).
Variables (bpos0 cap0 w : Z).
Let usp := bv_unsigned sp.
Hypothesis HT : usp <= hiA_top A4L HIx.
Notation ser_memx := (ser_memA HIx sp m0 md0 LB LM FRS0 B0 pb lo bpos0 cap0 w).

Lemma ser_memA_stackW : forall A FRSc FA CH CH' e m mc md W,
ser_memx A FRSc FA CH e m md -> munch W m mc -> wmono asegs m mc -> mem_inv asegs mc ->
Forall (fun iv : Z * Z => alloc_ceiling <= fst iv /\ snd iv <= usp) W ->
Forall (fun ch => rw_cells asegs mc (fst ch) (snd ch)) CH' -> Forall (chunk_ok LB LM FRSc FA) CH' -> stk asegs mc lo FA -> alloc_ceiling <= usp ->
ser_memx A FRSc FA CH' e mc md.
Proof.
intros A FRSc FA CH CH' e m mc md W (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & Hbp & Hcap & HBB & HBD)
MU WM MIc HW CHc CHokc STc LOU.
assert (HW1 : Forall (fun iv : Z * Z => alloc_ceiling <= fst iv) W) by (eapply Forall_impl; [| exact HW]; intros iv [H _]; exact H).
pose proof alloc_ceiling_range as ACR.
exists buf, cap, bpos, content, errv, B.
split.
{ eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MIc].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU).
eapply Forall_impl; [| exact HW]. intros iv [H1 H2]. left. unfold usp in *. lia. }
destruct PB as (Hb0 & Hc0 & Hlen & PBS & PBUF).
split.
{ split; [exact Hb0|]. split; [exact Hc0|]. split; [exact Hlen|]. split.
- eapply (rw_cells_transport asegs W m mc); [exact PBS | exact MU | exact WM |].
eapply (heapA_blocks_below HIx _ _ _ _ _ _ _ W pb PB_SZ HP); [apply in_or_app; left; left; reflexivity | exact HW1].
- eapply (rw_cells_transport asegs W m mc); [exact PBUF | exact MU | exact WM |].
cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(apply in_or_app; left; right; left; reflexivity)) as (Hn & _ & _ & Hhi & _).
rewrite Z2Nat.id by lia. eapply disjoint_from_above; [exact HW1 | exact Hhi]. }
split; [exact CHc|]. split; [exact CHokc|]. split; [exact FSUB|].
split.
{ eapply (rw_cells_transport asegs W m mc); [exact ERR | exact MU | exact WM |].
eapply disjoint_from_above; [exact HW1|]. unfold A_ERRNO, A_TP. cbn [cells_size csize Nat.add]. unfold alloc_ceiling, sp_window_lo, stack_max_size in *. lia. }
split; [exact STc|].
split.
{ eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch A4H _ usp); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | | exact LOU |].
- intros bb Hbb. apply in_app_or in Hbb. apply in_or_app. destruct Hbb as [Hbb|Hbb]; [left; right; right; exact Hbb|].
right. apply in_app_or in Hbb. destruct Hbb as [Hbb|Hbb]; [apply in_or_app; left; exact Hbb | apply in_or_app; right; apply FSUB; exact Hbb].
- eapply Forall_impl; [| exact HW]. intros iv [H1 H2]. left. split; assumption. }
split; [exact VM|]. split; [exact Hbp|]. split; [exact Hcap|]. split; [exact HBB | exact HBD].
Qed.
End K.
End RC__1.
End Mqc.

Module Mqd.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj Q4v2 QgHv Q1Y6 QsKa.Mqf. Import QlKV.Mq2 QsKa. Import Q9O6.Mq5 QL3k.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Notation b8 := (Z_to_bv 8) (only parsing).

Definition ADBL_STACK : Z := 144 + 8192.
Definition ADBL_MEMAPP_RET : Z := 0x9efd0.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section Dbl.
Variable HIx : heap_iface_A A4L.

Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud).
Variables (pb lo bpos0 cap0 : Z) (T : TSet).
Variables (q d Fr : Z).

Definition dblSaved : list cell := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Definition dblFF (j8 bufb jr : list byte) : list cell := [C8 (wz 1102416563); C8 (wz 0x19e77); C8 (wz 0x9ee14); CB 8 j8; CB 128 bufb; CB 88 jr].
Definition dblSH (v : Z) (t8 : list byte) : list cell :=
[C1 (b8 241); C1 (b8 241); C1 (b8 241); C1 (b8 241);
C1 (b8 v); C1 (b8 v); C1 (b8 v); C1 (b8 v); C1 (b8 v); C1 (b8 v); C1 (b8 v); C1 (b8 v);
C1 (b8 v); C1 (b8 v); C1 (b8 v); C1 (b8 v); C1 (b8 v); C1 (b8 v); C1 (b8 v); C1 (b8 v);
C1 (b8 243); C1 (b8 243); C1 (b8 243); C1 (b8 243); CB 8 t8].

Definition dblCH (LOC : list cell) (j8 bufb jr t8 : list byte) (v : Z) : list (Z * list cell) :=
[(q, LOC); (bv_unsigned sp + -104, dblSaved); (Fr, dblFF j8 bufb jr); (Fr / 8 + 2147450880, dblSH v t8)].

Definition dbl_inv (v : Z) (A : ASA A4L HIx) (e : Z) (bufb : list byte) (m : word -> option byte) (md : config) : Prop :=
exists LOC j8 jr t8, cells_size LOC = Z.to_nat (24 + d) /\
ser_memA HIx sp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 9 A ((Fr, 2) :: FRS) q (dblCH LOC j8 bufb jr t8 v) e m md.
End Dbl.
End RC__1.
End Mqd.

Module Mqe.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun Qfw3_c1.Mq2.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj Q4v2 QgHv Q1Y6 QsKa.Mqf QUrr. Import QlKV.Mq2 QsKa. Import Q9O6.Mq5 QL3k.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition lit_bytesA (a : Z) (k : nat) : list byte := match image_bytes asegs a k with Some bs => bs | None => [] end.
Definition LIT_LBRACK : list byte := Eval vm_compute in lit_bytesA 0x23860 1.
Definition LIT_RBRACK : list byte := Eval vm_compute in lit_bytesA 0x238a0 1.
Definition LIT_SP_RBRACK : list byte := Eval vm_compute in lit_bytesA 0x23880 2.
Definition LIT_COMMA : list byte := Eval vm_compute in lit_bytesA 0x234a0 1.
Definition LIT_SPACE : list byte := Eval vm_compute in lit_bytesA 0x234e0 1.
Definition LIT_NULL : list byte := Eval vm_compute in lit_bytesA 0x233c0 4.
Definition LIT_QUOTE : list byte := Eval vm_compute in lit_bytesA 0x23520 1.

Section Lit.
Variable HIx : heap_iface_A A4L.
Variables (sp gp : word) (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS0 : list frame) (B0 : bud) (pb lo : Z).
Variables (bpos0 cap0 w : Z).
Let usp := bv_unsigned sp.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis HT : usp <= hiA_top A4L HIx.
Hypothesis CAP0 : 32 <= cap0 < 2^30.
Hypothesis TXT : bpos0 + w < 2^28.
Hypothesis NEED : ser_need cap0 bpos0 w <= bB B0.
Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.
Notation ser_memx := (ser_memA HIx sp m0 md0 LB LM FRS0 B0 pb lo bpos0 cap0 w).

Lemma ser_litA :
forall (lit k : Z) (bs : list byte),
ro_bytes_b asegs lit bs = true -> Z.of_nat (length bs) = k -> src_ro_chk lit k = true -> 0 < k < 2^31 -> 0 <= lit -> lit + k < 2^32 ->
forall (ret : Z) (x3 t0 t1 t2 x8 x9 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
(F Fc : bvmap 5 word) (fcc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (FRSc : list frame) (FA : Z) (CH : list (Z * list cell)) (e : Z),
ser_memx A FRSc FA CH e m md ->
0 <= e -> e + k <= w ->
lo <= FA - 112 - 4096 -> FA mod 16 = 0 -> FA <= usp -> 0 <= FA ->
x3 = gp -> 0 <= ret < 2^64 -> ret mod 2 = 0 ->
fsaved F Fc -> frm0 fcc ->
(forall (A' : ASA A4L HIx) m' md' (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F' fc',
ser_memx A' FRSc FA CH (e + k) m' md' -> fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A' T md' (MS (mkR (wz ret) (wz FA) gp (wz A_TP) t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7'
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6') F' (wz ret) fc' None m' (seg_rom asegs))) ->
AJ5 A4L HIx A T md (MS (mkR (wz ret) (wz FA) x3 (wz A_TP) t0 t1 t2 x8 x9 (wz pb) (wz lit) (wz k) a3 a4 a5 a6 a7
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) Fc (wz AMEMAPPEND) fcc None m (seg_rom asegs)).
Proof.
intros lit k bs RB BL CHK Hk Hl Hlk. intros until e. intros INV He Hek LOS FAA FAU FA0 X3 Hret Hret2 FS FRM K.
pose proof (ser_memA_mem_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
pose proof INV as (buf1 & cap1 & bpos1 & content1 & errv1 & B1 & HP1 & _).
eapply (ser_appendA HIx sp gp m0 md0 LB LM FRS0 B0 pb lo bpos0 cap0 w LO HT CAP0 TXT NEED OBL_REALLOC_NF) with (F := F) (sb := bs) (e := e);
[ exact INV | apply rodata_bytes_at; [exact MI | exact RB | lia | lia] | exact BL | lia | lia
| right; right; apply src_globA_of_chk; exact CHK
| intros _; eapply (unpoisoned_of_glob HIx); [exact HP1 | apply src_globA_of_chk; exact CHK | lia]
| exact He | exact Hek | exact LOS | exact FAA | exact FAU | exact FA0 | exact X3 | exact Hret | exact Hret2 | exact FS | exact FRM | ].
intros A2 m2 md2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 INV2 FS2 FR2 _.
eapply K; eassumption.
Qed.
End Lit.
End RC__1.
End Mqe.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q60A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqf.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0.
Import QbFI.  Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj Q4v2 QgHv Q1Y6 QsKa.Mqf QsKa.Mqg QpNt.Mq8 QsKa.Mqe Q30W Q60A. Import QlKV.Mq2 QsKa. Import Q9O6.Mq5 QL3k.Mq4.
Import QWxq_c1 QsjA.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).

Ltac fold_mkR :=
lazymatch goal with
| |- context [MS (TNode (TNode (TNode (TNode (TNode (TNode TEmpty (Some ?x31) TEmpty) (Some ?x15) TEmpty) (Some ?x7) (TNode TEmpty (Some ?x23) TEmpty)) (Some ?x3) (TNode (TNode TEmpty (Some ?x19) TEmpty) (Some ?x11) (TNode TEmpty (Some ?x27) TEmpty))) (Some ?x1) (TNode (TNode (TNode TEmpty (Some ?x17) TEmpty) (Some ?x9) (TNode TEmpty (Some ?x25) TEmpty)) (Some ?x5) (TNode (TNode TEmpty (Some ?x21) TEmpty) (Some ?x13) (TNode TEmpty (Some ?x29) TEmpty)))) None (TNode (TNode (TNode (TNode TEmpty (Some ?x16) TEmpty) (Some ?x8) (TNode TEmpty (Some ?x24) TEmpty)) (Some ?x4) (TNode (TNode TEmpty (Some ?x20) TEmpty) (Some ?x12) (TNode TEmpty (Some ?x28) TEmpty))) (Some ?x2) (TNode (TNode (TNode TEmpty (Some ?x18) TEmpty) (Some ?x10) (TNode TEmpty (Some ?x26) TEmpty)) (Some ?x6) (TNode (TNode TEmpty (Some ?x22) TEmpty) (Some ?x14) (TNode TEmpty (Some ?x30) TEmpty))))) ?F ?pc ?fc ?rv ?m ?ro] =>
change (TNode (TNode (TNode (TNode (TNode (TNode TEmpty (Some x31) TEmpty) (Some x15) TEmpty) (Some x7) (TNode TEmpty (Some x23) TEmpty)) (Some x3) (TNode (TNode TEmpty (Some x19) TEmpty) (Some x11) (TNode TEmpty (Some x27) TEmpty))) (Some x1) (TNode (TNode (TNode TEmpty (Some x17) TEmpty) (Some x9) (TNode TEmpty (Some x25) TEmpty)) (Some x5) (TNode (TNode TEmpty (Some x21) TEmpty) (Some x13) (TNode TEmpty (Some x29) TEmpty)))) None (TNode (TNode (TNode (TNode TEmpty (Some x16) TEmpty) (Some x8) (TNode TEmpty (Some x24) TEmpty)) (Some x4) (TNode (TNode TEmpty (Some x20) TEmpty) (Some x12) (TNode TEmpty (Some x28) TEmpty))) (Some x2) (TNode (TNode (TNode TEmpty (Some x18) TEmpty) (Some x10) (TNode TEmpty (Some x26) TEmpty)) (Some x6) (TNode (TNode TEmpty (Some x22) TEmpty) (Some x14) (TNode TEmpty (Some x30) TEmpty)))))
with (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
| |- _ => idtac
end.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section Ser.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.

Lemma ser_udA : ser_specA HIx ASER_UD (Sdouble true).
Proof.
unfold ser_specA. intros until errv. intros HP PB JN INCL JTX CAP TXT NEED FL Hlv Hlvd FRSN ST LO LOS SPA HT ERR JHX TP' RA FRM A0 A1 A2 A3 K.
destruct JN as (bits & ud & udn & uds & EREST & Hudn & NODE & CS). unfold jhdr_cells in NODE. cbn [app] in NODE.
subst a0 a1 a2 a3 tp REST.
cbn [app jtx] in JTX. rewrite Z.eqb_refl in JTX. injection JTX as <- _.
unfold ASER_UD, ser_budgetA, ASER_LEVEL, ASER_LEAF in *. cbn [sdepth Z.mul Z.add] in LOS.
word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
assert (INp : In (p, 48) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; apply INCL; left; reflexivity).
assert (INu : In (ud, udn) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; apply INCL; right; left; reflexivity).
assert (INuL : In (ud, udn) LB) by (apply INCL; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p 48 HP ltac:(apply in_or_app; left; exact INp)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ pb PB_SZ HP ltac:(apply in_or_app; left; left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(apply in_or_app; left; right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
destruct (key_stringA HIx _ _ _ _ _ _ _ ud udn uds HP INu CS) as (slack & STR & PAD & NN & UAL & UL & UPOS & UHI & USL).
clear CS.
unfold_consts.
shadow_inA A4L HIx HP INp SHp.
pose proof PB as (Hbp & Hcap & Hlen & PBS & PBUF).
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
pose proof alloc_ceiling_range as ACR.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 32%nat ST.
do 5 step.
step. if_falsex.
step.
step. step. ubsan_align Hpal.
do 3 step. step.
asan_chkA.
do 3 step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
assert (HP1 : HEAPAx A ((pb, PB_SZ) :: (buf, cap) :: LB) LM FRS B m1 md) by (heap_nowA A4L HIx HP MU WM MI1).
assert (HPR1 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1).
{ eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros bb Hbb; apply in_app_or in Hbb; apply in_or_app; destruct Hbb as [Hbb|Hbb]; [left; right; right; exact Hbb | right; exact Hbb] | lia | solve_clientWA A4L HIx HP]. }
clear MU WM.

eapply (astrlen_any_A HIx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 md A _ LM FRS B ud udn ud lo uds slack);
a4l_goal; rewrite ?unsigned_lit by lia;
first [exact HP1 | exact INu | exact NN | exact STR | exact PAD | exact USL | exact ST | exact LO | exact MI1 | reflexivity | lia
| replace (bv_unsigned sp + -32) with (bv_unsigned sp - 16 * 2) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity | idtac].
intros x0 x1' x2 y1' y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 m3 MU3 WM3 MI3 STR3 ST3.
stash STR3.
transport_after_call asegs m1 m3 MU3 WM3; try match goal with H : mem_inv asegs m1 |- _ => clear H end.
unstash STR3.
assert (HP3 : HEAPAx A ((pb, PB_SZ) :: (buf, cap) :: LB) LM FRS B m3 md).
{ eapply (heapA_client_frame A4L HIx); [exact HP1 | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP1 MU3); solve_frameW_withA HP1 | exact WM3 | exact MI3]. }
assert (HPR13 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m1 m3).
{ eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU3 | exact WM3 |].
eapply (client_outsideA A4L HIx); [exact HP1 | intros bb Hbb; apply in_app_or in Hbb; apply in_or_app; destruct Hbb as [Hbb|Hbb]; [left; right; right; exact Hbb | right; exact Hbb] | lia | solve_clientWA A4L HIx HP1]. }
clear MU3 WM3.
pose proof (wmono_refl asegs m3) as WM. pose proof (munch_refl (@nil (Z * Z)) m3) as MU.
replace (ret_pc (Z_to_bv 64 653340)) with (Z_to_bv 64 653340) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
set (len := Z.of_nat (length uds)) in *.
assert (Hlen31 : 0 <= len < 2^31) by (unfold len; lia).
step. rewrite (unsigned_lit len) by lia. rewrite Z.add_0_r. rewrite swrap32_id by lia.
do 4 step. fold_mkR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
match goal with H : mem_inv asegs m4 |- _ => rename H into MI4 end.
assert (INV4 : ser_memA HIx sp m md LB LM FRS B pb lo bpos cap (16 + Z.max 0 (udn - 1)) A FRS (bv_unsigned sp + -32)
[(bv_unsigned sp + -32, [C8 s2; C8 s1; C8 s0; C8 ra])] 0 m4 md).
{ exists buf, cap, bpos, content, errv, B.
split; [heap_nowA A4L HIx HP3 MU WM MI4|].
split; [split; [lia|]; split; [lia|]; split; [exact Hlen|]; split; [exact PBS | exact PBUF]|].
split; [constructor; [exact FR | constructor]|].
split; [constructor; [left; cbn [fst]; lia | constructor]|].
split; [intros bb Hbb; exact Hbb|].
split; [exact ERR|]. split; [exact ST3|].
split. { eapply heap_pres_trans; [exact HPR1|]. eapply heap_pres_trans; [exact HPR13|].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |]. intros a Ha Hc. exact I. }
split; [apply model_vm_only_refl|].
split; [lia|]. split; [unfold ser_capb; lia|]. split; lia. }
pose proof INV4 as (buf4 & cap4 & bpos4 & content4 & errv4 & B4 & HP4 & _).
assert (SRC : bytes_at asegs m4 ud uds).
{ replace (uds ++ Z_to_bv 8 0 :: slack) with (uds ++ (Z_to_bv 8 0 :: slack)) in STR3 by reflexivity.
apply bytes_at_app in STR3. exact (proj1 STR3). }
evt_done5.
eapply (ser_appendA HIx sp gp m md LB LM FRS B pb lo bpos cap (16 + Z.max 0 (udn - 1)) LO HT CAP TXT NEED OBL_REALLOC_NF) with (F := F) (sb := uds) (e := 0);
[ exact INV4 | exact SRC | reflexivity | fold len; lia | lia
| left; exists ud, udn; split; [exact INuL | fold len; lia]
| intros Hk; eapply (unpoisoned_of_blk HIx); [exact HP4 | right; right; exact INuL | lia | fold len; lia | exact Hk]
| lia | fold len; lia | lia
| replace (bv_unsigned sp + -32) with (bv_unsigned sp - 16 * 2) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | apply fsaved_refl | exact FRM | ].
intros A2 m2 md2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 INV2 FS2 FR2 _.
pose proof INV2 as (buf2 & cap2 & bpos2 & content2 & errv2 & B2 & HP2 & PB2 & CH2 & _ & _ & ERR2 & ST2 & HPR2 & VM2 & Hb2 & Hc2 & HB2 & HD2).
apply Forall_inv in CH2. cbn [fst snd] in CH2.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI2. cbn [hl_segs hla_base A4L A4H] in MI2.
a4l. reenterA asegs A4L HIx asegs_wx HP2.
step. do 4 step. step. step.
evt_done5. apply K. unfold ser_postA.
exists m2, (Z_to_bv 64 len), errv2, buf2, cap2, bpos2, content2, B2.
split; [apply ret_statew_intro; [exact FS2 | intros _; exact FR2]|].
split; [exact VM2|].
split; [release_frame CH2 ST2 (bv_unsigned sp); exact ST2|].
split; [exact HPR2|]. split; [exact ERR2|]. split; [exact HP2|]. split; [exact PB2|].
split; [fold len in Hb2; lia|]. split; [exact Hc2|]. split; lia.
Qed.
End Ser.
End RC__1.
End Mqf.

Module Mqg.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun QWxq_c1.Mq0 Qfw3_c1.Mq2 Qc3B.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn.
Import QgoP.
Import QZAi.Mq1 Qx2n.
Import QbFI QXUB. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QsKa.Mqd QlKV.Mqj QsKa.Mq9 QsKa.Mqh Qw5U.Mq5.

Import Qvmy Qawr.
Import Qw5U.Mq8 QL3k.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section MStrtodBridge.
Variable HIx : heap_iface_A A4L.
Hypothesis SCANH : scan_total_stmtA.
Hypothesis STRTOD : astrtod_total_stmt.

Definition STRTOD_STK_A : Z := 12288.
Definition strtod_A_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud)
(str : list byte) (SA R lo : Z) (rj errv : word),
HEAPA A4L HIx A LB LM FRS B m md ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - STRTOD_STK_A ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 SA -> a1 = Z_to_bv 64 R ->
bytes_at asegs m SA (str ++ [QgoP.b0]) -> ~ In QgoP.b0 str ->
Z.of_nat (length str) < 2^31 ->
(exists a n, In (a, n) LB /\ a <= SA /\ SA + Z.of_nat (length str) + 1 <= a + n) ->
(exists Fc kc, In (Fc, kc) FRS /\ Fc <= R /\ R + 8 <= Fc + fr_size kc - 8) ->
rw_cells asegs m R [C8 rj] -> R mod 8 = 0 ->
frm0 fc ->
(forall ms' m' (a0' v e' : word),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0' m' ms' ->
stk asegs m' lo (bv_unsigned sp) ->
heap_presD R (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
rw_cells asegs m' R [C8 v] -> rw_cells asegs m' A_ERRNO [C4 e'] ->
HEAPA A4L HIx A LB LM FRS B m' md ->
AJ5 A4L HIx A T md ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdccb8) fc None m (seg_rom asegs)).

Theorem strtod_A_of_musl : strtod_A_stmt.
Proof.
unfold strtod_A_stmt, STRTOD_STK_A. intros until errv. intros HP ST LO LOS SPA HT ERR TP RA A0 A1 STR NUL LS (ab & nb & INB & HB1 & HB2) (Fc & kc & INF & HF1 & HF2) RC RAL FRM K.
subst a0 a1 tp.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. change (hl_segs A4L) with asegs in MI.
pose proof alloc_ceiling_range as ACR.
pose proof (hiA_top_le A4L HIx) as HT47.
destruct (heapA_canary A4L HIx _ _ _ _ _ _ _ HP) as (g & CAN1 & CAN2 & _). cbn [hl_got_guard hl_guard A4L A4H hla_base] in CAN1, CAN2.
assert (INBA : In (ab, nb) (LB ++ LM)) by (apply in_or_app; left; exact INB).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ ab nb HP INBA) as (_ & _ & Hb0 & Hbc & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ ab nb HP INBA) as Hbimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hbimg.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & _ & HF0 & HFc & _).
pose proof (frame_above_img HIx _ _ _ _ _ _ _ _ _ HP INF) as HFhi. cbn [hl_img_hi A4H] in HFhi.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INBA) as DF.
set (txtZ := map bv_unsigned str ++ [0]).
assert (FA : Forall (fun c => 0 <= c < 256) (map bv_unsigned str)).
{ apply Forall_map. apply Forall_forall. intros b _. pose proof (bv_unsigned_in_range 8 b) as R0. unfold bv_modulus in R0. cbn in R0. lia. }
destruct (SCANH (map bv_unsigned str) FA) as (bits & used & SCAN & U0).
assert (LTX : zlength txtZ = Z.of_nat (length str) + 1) by (unfold zlength, txtZ; rewrite length_app, length_map; cbn [length]; lia).
assert (LPRE : zlength (map bv_unsigned str) = Z.of_nat (length str)) by (unfold zlength; rewrite length_map; reflexivity).
unfold A_ERRNO, A_TP in *.
a4l.
reenterA asegs A4L HIx asegs_wx HP.
eapply evt_cut.
{ eapply STRTOD with (T := SA) (PE := R) (txt := txtZ) (pre := map bv_unsigned str) (post := []) (lo := lo) (bits := bits) (used := used) (canary := g).
- unfold txtZ. rewrite map_app. cbn [map]. rewrite map_unsigned_bytesA. exact STR.
- unfold txtZ. apply Forall_app. split; [exact FA | constructor; [lia | constructor]].
- reflexivity.
- rewrite LPRE. lia.
- rewrite LTX. lia.
- exact RC.
- exact SCAN.
- exact ST.
- unfold ASTRTOD_DEPTH. lia.
- lia.
- lia.
- lia.
- rewrite LTX. lia.
- left. rewrite LTX. split; lia.
- lia.
- lia.
- left. lia.
- rewrite LTX. lia.
- exact CAN1.
- exact CAN2.
- unfold A_TP. exact ERR.
- exact MI.
- exact FRM.
- reflexivity.
- reflexivity.
- reflexivity. }
cbv beta delta [astrtod_post]. unfold A_TP. change (6444320 - 164) with 6444156. change (6444320 - 160) with 6444160.
intros ms' (q0 & q1 & q2 & qa0 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & F' & fc' & m' & ev' & -> & MU & WM & MI' & FRM' & FKEEP & FA0 & ST' & PE' & TXT' & ERR' & USED).
evt_done5.
eapply (K _ m' qa0 _ ev').
- apply ret_statew_intro; [| intros _; exact FRM'].
intros k Hk. cbn [FSAVED In] in Hk.
repeat (destruct Hk as [<- | Hk]); [..| destruct Hk]; apply FKEEP; vm_compute; lia.
- exact ST'.
- eapply (presD_private HIx _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp) R HP MU WM); [| lia |].
+ intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. exact Hb.
+ apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]].
* left. cbn [fst snd]. lia.
* right; right; right; right. cbn [fst snd]. lia.
* right; right; left. intros x Hx. cbn [fst snd] in Hx. cbn [hl_scratch A4L A4H hla_base]. unfold A_TP. lia.
- exact PE'.
- exact ERR'.
- eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MI'].
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP MU).
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]].
+ left. cbn [fst snd]. lia.
+ right; right; right. exists Fc, kc. split; [exact INF|]. left. cbn [fst snd]. lia.
+ right; right; left. intros x Hx. cbn [fst snd] in Hx. cbn [hl_scratch A4L A4H hla_base]. unfold A_TP. lia.
Qed.
End MStrtodBridge.
End RC__1.
End Mqg.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.
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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6WR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6WR.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrPc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrPc.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvmy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvmy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qawr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qawr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYZ0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYZ0.Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QAzu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Ltac gi_fs_tail := let k := fresh "k" in let Hk := fresh "Hk" in intros k Hk; cbn [FSAVED In] in Hk; repeat (destruct Hk as [<- | Hk]); [..| destruct Hk]; rewrite ?freg_get_other by (vm_compute; reflexivity); reflexivity.

Ltac gi_exit EPI XHP XPD PD1 HP1 A1 md1 mb VM1 :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (EPI mc A1 md1);
[ eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
| apply XHP; assumption | exact VM1 | eapply (XPD mb mc PD1 A1 md1 HP1); assumption
| first [apply fsaved_refl | gi_fs_tail] | first [intros Hf; exact Hf | intros _; assumption] ] end.
Section AJoGetUint64.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis ERRNOL : QlKV.Mqe.errno_location_A_stmt.
Hypothesis PI64 : parse_i64_A_stmt HIx 0xa62ec.

Lemma RTC_GU64PC : forall A LB LM FR B m md, HEAPAx A LB LM FR B m md -> bytes_at asegs m 0xe8e48 (le8 (Z_to_bv 64 0x9e8d8)).
Proof.
intros A LB LM FR B m md HP. apply (rtc_cell HIx _ _ _ _ _ _ _ _ _ HP). unfold a4_rt_consts.
repeat (first [left; reflexivity | right]).
Qed.

Definition GU64_STK_A : Z := 96 + PI64_STK_A.

Lemma get_uint64_A : jo_get_num_A_stmt HIx 0x9e8d8 GU64_STK_A.
Proof.
unfold jo_get_num_A_stmt. intros until errv. intros (HP & ST & LO & LOS & SPA16 & HT & ERR & TP & RA) JO FRN SPA FRM A0 K.
unfold GU64_STK_A, PI64_STK_A in LOS. subst a0 tp.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof alloc_ceiling_range as ACR.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP) as (SB1 & SB2 & SB3 & SB4).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2. apply ro_C8_of_bytes_at in SB3.
assert (UARC : ro_cells asegs m (hl_uar_cell A4L) [C4 (Z_to_bv 64 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SB4]).
clear SB4. a4l.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU.
unfold A_ERRNO, A_TP in *.
stash ERR.
reenterA asegs A4L HIx asegs_wx HP.
carve_frame 96%nat ST.
bstep. bstepz. do 8 bstep.
bstep. bstep.
rewrite (unsigned_lit (bv_unsigned sp + -96)) by lia. change 18446744073709551584 with (2^64 - 2^5). rewrite OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.land_align_down by lia. change (2^5) with 32.
replace (bv_unsigned sp + -96 - (bv_unsigned sp + -96) mod 32) with (bv_unsigned sp + -96) by (clear - SPA; Z.div_mod_to_equations; lia).
bstep. bstep. bstep. bstep. bstep. bstep. bstep. bstep.
norm_sx32. bstep. if_false. bstep. bstep.
evt_done5.
eapply (stack_malloc_full HIx) with (k := 0) (bytes := 64) (lo := lo) (LB := BS ++ LB) (LM := LM) (FR := FRS) (B := B);
[ heap_nowA A4L HIx HP MU WM MI | lia | .. ].
all: rewrite ?unsigned_lit by lia.
1: rewrite fr_size_0; lia.
1: reflexivity.
1: lia.
1: exact ST.
1: exact LO.
1: cbn [hl_stack_A A4L]; lia.
1: clear - SPA; Z.div_mod_to_equations; lia.
1: lia.
1: reflexivity.
1: reflexivity.
intros ms1 m1' md1 A1 Fr RS1 VM1 ST1 HPR1 FRNZ (jff & FF1) SHB1 HP1. open_ret RS1.
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP1) as (errv1 & ERR1). unfold A_ERRNO, A_TP in ERR1. cbn [hl_tp A4L A4H hla_base] in ERR1.
rewrite ?unsigned_lit in ST1, HPR1 by lia.
clear ERR.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as (_ & HFal & HF0 & HFc & HFimg & _ & HFshw & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFapp.
rewrite fr_size_0 in HFal, HFc, HFimg, HFapp. rewrite fr_shadow_len_0 in HFshw. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in FR; [| left; cbn; lia].
clear SB1 SB2 SB3 UARC.
pose proof (RTC_GU64PC _ _ _ _ _ _ _ HP1) as PCC. apply ro_C8_of_bytes_at in PCC.
assert (FSH1 : rw_cells asegs m1' (shad A4L Fr) [CB 8 (repeat (Z_to_bv 8 0) 8)]).
{ split; [split; [cbn; split; [reflexivity | exact I] | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SHB1] | exact HFshw]. }
rewrite fr_size_0 in FF1. change (Z.to_nat (64 - 8)) with 56%nat in FF1.
unfold shad in FSH1. a4l.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 8 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1. change (hl_segs A4L) with asegs in MI1. clear MI.
rename MU into MU0. rename WM into WM0. pose proof (wmono_refl asegs m1') as WM. pose proof (munch_refl [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6444156, 6444160)] m1') as MU.
change (6444320 - 164) with 6444156 in ERR1.
unfold A_SB in HFapp.
reenterA asegs A4L HIx asegs_wx HP1.
bstep. bstep. bstep. if_truex.
bstepz.
bstep. bstep. bstep. bstep.
rewrite (unsigned_lit Fr) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
bstep. bstep. bstep. bstepz. bstepz. bstepz. bstep. bstep.
fold sh.
bstepz. bstepz. bstepz. bstepz. bstep. bstepz. bstepz. bstepz. bstepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (SHE : ro_cells asegs mc 2148256399 [C1 (Z_to_bv 8 0)]) end.
{ apply QsKa.Mqa.ro_C1_of_bytes_at.
pose proof (heapA_shadow_img A4L HIx _ _ _ _ _ _ _ (6444156 / 8) HP1) as X.
assert (E : img_shadow_val (hl_reg_globals A4L) (6444156 / 8) = 0) by (vm_compute; reflexivity). rewrite E in X.
cbn [hl_sb A4L hl_img_lo hl_img_hi hla_base A4H] in X. unfold A_SB in X.
specialize (X ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
change (6444156 / 8 + 2147450880) with 2148256399 in X.
eapply bytes_at_transport; [exact X | exact MU |]. cbn [disjoint_from length]. change (Z.of_nat 1) with 1. unfold sh. clear - HFimg HFapp HF0 HFc ACR LO LOS SPR. Z.div_mod_to_equations. lia. }
bstep.
eapply evt_cut; [eapply ERRNOL; reflexivity |]. intros ms9 ->.
replace (ret_pc (Z_to_bv 64 0x9e9c8)) with (Z_to_bv 64 0x9e9c8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unfold A_ERRNO, A_TP. change (6444320 - 164) with 6444156.
bstep. bstep. bstep. rewrite ?sxb_zero. bstep. if_false.
bstepz.

lazymatch type of FF1 with rw_cells _ _ _ [?c1; ?c2; ?c3; CB 32 ?jj] =>
apply (rw_cells_split_CB asegs _ Fr [c1; c2; c3] 32 jj [] [8; 8; 16]%nat) in FF1; [| reflexivity]; cbn [mk_CB_cells app] in FF1 end.
apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _] _)) in FF1. destruct FF1 as [FFa FFe]. cbn [cells_size csize Nat.add] in FFe.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FFe. destruct FFe as [FFe FFb]. cbn [cells_size csize Nat.add] in FFb.
change (Z.of_nat 32) with 32 in FFe, FFb. replace (Fr + 32 + Z.of_nat 8) with (Fr + 40) in FFb by lia.
apply rw_cells_C8_of_CB8 in FFe.
assert (XHP : forall mX, munch [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6444156, 6444160)] m1' mX -> wmono asegs m1' mX -> mem_inv asegs mX ->
HEAPAx A1 (BS ++ LB) LM ((Fr, 0) :: FRS) B mX md1).
{ intros mX MUX WMX MIX. exact (fk0_HEAPA HIx _ _ _ _ _ _ _ _ _ _ _ HP1 LO HT MUX WMX MIX). }
assert (PD1 : heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1').
{ eapply heap_presD_trans; [| eapply heap_presD_of_pres; [exact HPR1 | lia]].
eapply (presD_private HIx _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp) (Fr + 32) HP MU0 WM0); [| lia |].
- intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. exact Hb.
- apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. lia. }
assert (XPD : forall mb mX, heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mb ->
forall AX mdX, HEAPAx AX (BS ++ LB) LM ((Fr, 0) :: FRS) B mb mdX ->
munch [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6444156, 6444160)] mb mX -> wmono asegs mb mX ->
heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mX).
{ intros mb mX PDb AX mdX HPb MUX WMX. eapply heap_presD_trans; [exact PDb |].
eapply (fk0_presD HIx); [exact HPb | exact LO | lia | exact MUX | exact WMX]. }

lazymatch type of FR with rw_cells _ _ _ ?frc => lazymatch type of FSH1 with rw_cells _ _ _ ?shc => lazymatch type of FFa with rw_cells _ _ _ ?ffc =>
assert (EPI : forall (mX : word -> option byte) (AX : ASA A4L HIx) (mdX : config) (F1 : bvmap 5 word) (fc1 : bv 32)
(eX xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs6 xt3 xt4 xt5 xt6 : word),
mem_inv asegs mX ->
rw_cells asegs mX (bv_unsigned sp + -96) frc -> rw_cells asegs mX sh shc -> rw_cells asegs mX Fr ffc ->
rw_cells asegs mX 6444156 [C4 eX] -> stk asegs mX lo (bv_unsigned sp + -96) ->
HEAPAx AX (BS ++ LB) LM ((Fr, 0) :: FRS) B mX mdX -> model_vm_only (cfg_model md) (cfg_model mdX) ->
heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mX ->
fsaved F F1 -> (frm0 fc -> frm0 fc1) ->
evt asegs (AJ5e A4L HIx AX T mdX)
(MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 6444320) xt0 xt1 xt2 sp xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 Fr) xs3 (Z_to_bv 64 sh) (Z_to_bv 64 Fr) xs6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
F1 (Z_to_bv 64 0x9eb3c) fc1 None mX (seg_rom asegs)))
end end end.
{ intros mX AX mdX F1 fc1 eX xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs6 xt3 xt4 xt5 xt6 MIX FRX FSHX FFX ERRX STX HPX VMX PDX FSX FRMX.
clear MU WM MI1 FR FSH1 FFa FFe FFb ST1 ERR1 SHE PCC.
pose proof (wmono_refl asegs mX) as WM. pose proof (munch_refl [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6444156, 6444160)] mX) as MU.
bstep. bstepz. bstep. bstep. bstepz. bstep. if_falsex. bstep. do 8 bstepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ mX mc, WMc : wmono asegs mX mc, MIc : mem_inv asegs mc |- _ =>
pose proof (fk0_HEAPA HIx _ _ _ _ _ _ _ _ _ _ _ HPX LO HT MUc WMc MIc) as HPY;
pose proof (XPD mX mc PDX AX mdX HPX MUc WMc) as PDY end end.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HPY INF) as (_ & _ & _ & _ & _ & _ & _ & (fp & FPB & FPR & FPnc & FPimg & FPns & FPfr)).
rewrite fr_size_0 in FPB. replace (Fr + 64 - 8) with (Fr + 56) in FPB by lia.
pose proof (ro_C8_of_bytes_at asegs _ _ _ FPB) as FPC.
bstep.
evt_done5.
eapply (hiA_frame_release A4L HIx) with (Fr := Fr) (k := 0) (fp := fp) (rX := Z_to_bv 5 10);
[exact HPY | exact INF | rewrite fr_size_0; replace (Fr + 64 - 8) with (Fr + 56) by lia; exact FPB | lia | reflexivity | vm_compute; discriminate | | ].
1: vm_compute; split; reflexivity.
intros m5 md5 A5 VM5 HP5 Hoff Hwv.
cbn [fr_remove fr_base fst Z.eqb] in HP5. rewrite Z.eqb_refl in HP5.
lazymatch type of HPY with HEAPA _ _ _ _ _ _ _ ?mq _ => assert (MUr : munch [(fp, fp + 1)] mq m5) end.
{ intros x Hx. cbn [outside] in Hx. pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. cbn in XR.
rewrite <- (Z_to_bv_bv_unsigned x). change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)). apply Hoff; lia. }
lazymatch type of HPY with HEAPA _ _ _ _ _ _ _ ?mq _ => assert (WMr : wmono asegs mq m5) by exact Hwv end.
assert (FPlow : fp < alloc_ceiling) by (destruct (Z.lt_ge_cases fp alloc_ceiling) as [L|G]; [exact L | exfalso; apply FPnc; left; exact G]).
apply (rw_cells_transport asegs [(fp, fp + 1)] _ m5) in FRX; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] _ m5) in ERRX; [| exact MUr | exact WMr | cbn [disjoint_from cells_size csize Nat.add]; cbn [hl_scratch A4L A4H hla_base] in FPns; unfold A_TP in FPns; lia].
apply (stk_transport_disjoint asegs [(fp, fp + 1)] _ m5) in STX; [| exact MUr | exact WMr | cbn [disjoint_from]; lia].
change (650108 + 4) with 650112.
clear FFX FSHX FPC.
reenterA asegs A4L HIx asegs_wx HP5.
do 13 bstep.
evt_done5.
eapply (K _ md5 m5 (bv_unsigned xa1) A5).
- assert (PD5 : heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m5).
{ eapply heap_presD_trans; [exact PDY |].
eapply (presD_fp HIx _ _ _ _ _ _ _ _ (Fr + 32) _ (bv_unsigned sp) fp HPY); [| lia | exact FPnc | exact FPfr | exact Hoff | exact Hwv].
intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. destruct Hb as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H]. }
split; [| split; [| split; [| split]]].
+ rewrite Z_to_bv_bv_unsigned. apply ret_statew_intro; [exact FSX | exact FRMX].
+ eapply model_vm_only_trans; [exact VMX | exact VM5].
+ release_frame FRX STX (bv_unsigned sp). exact STX.
+ eapply (heap_pres_of_presD (Fr + 32)).
* eapply heap_presD_weaken; [exact PD5 | lia |]. intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; apply in_or_app; right; exact Hb | apply in_or_app; right; exact Hb].
* intros a Hd Hc.
destruct (own_frame_fresh HIx Fr 0 (BS ++ LB) LB LM FRS B A1 m1' md1 HP1 ltac:(intros b Hb; apply in_or_app; right; exact Hb)) as [OFF OFS].
assert (Ho : outside [(Fr + 32, Fr + 40)] a).
{ eapply (QSHS.client_outsideF HIx A1 (BS ++ LB) LM ((Fr, 0) :: FRS) B (LB ++ LM ++ fr_ivs A4L FRS) m1' md1 [(Fr + 32, Fr + 40)] (bv_unsigned sp) HP1); [| lia | | lia | exact Hc].
- intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. destruct Hb as [H|H]; [left; apply in_app_or in H; apply in_or_app; destruct H as [H|H]; [left; apply in_or_app; right; exact H | right; exact H] | right; cbn [fr_ivs flat_map app]; right; right; exact H].
- apply Forall_cons; [| apply Forall_nil]. right; right; right. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. cbn [fst snd]. rewrite fr_size_0. lia. }
cbn [outside] in Ho. lia.
+ eexists. exact ERRX.
- assert (PD5 : heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m5).
{ eapply heap_presD_trans; [exact PDY |].
eapply (presD_fp HIx _ _ _ _ _ _ _ _ (Fr + 32) _ (bv_unsigned sp) fp HPY); [| lia | exact FPnc | exact FPfr | exact Hoff | exact Hwv].
intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. destruct Hb as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H]. }
eapply (jopt_agree asegs A4F BS m m5 s BS p); [exact JO | | apply incl_refl].
eapply (agree_of_presD (Fr + 32)); [exact PD5 | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb |].
intros a n Hin.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 INF ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin)) as DF. rewrite fr_size_0 in DF. lia.
- exact HP5. }
bstep.
destruct s as [shp|].
2:{  destruct JO as [Hp _]. rewrite Hp in *. if_truex. bstep.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1. }
destruct JO as [Hp J].

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m1' mc, WMc : wmono asegs m1' mc, MIc : mem_inv asegs mc |- _ =>
pose proof (XHP mc MUc WMc MIc) as HPc;
assert (AGc : agree_on asegs BS m mc);
[ eapply (agree_of_presD (Fr + 32)); [exact (XPD m1' mc PD1 A1 md1 HP1 MUc WMc) | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb |];
let a := fresh "a" in let n := fresh "n" in let Hin := fresh "Hin" in intros a n Hin;
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 INF ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin)) as DF; rewrite fr_size_0 in DF; lia
| ] end end.
pose proof (jval_agree asegs A4F shp BS m _ BS p 1 J AGc (incl_refl _)) as Jc.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HPc) as ND0.
assert (ND : List.NoDup (map blk_addr BS)) by exact (nodup_app_l' _ _ (nodup_app_l' _ _ ND0)).
destruct (jval_hdr asegs A4F shp _ BS p 1 Jc ND) as (n & tojs & pb & udel & ud & rest & INp & SZ & N48 & HDR & CLOSE).
assert (INpA : In (p, n) (BS ++ LB)) by (apply in_or_app; left; exact INp).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HPc ltac:(apply in_or_app; left; exact INpA)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HPc ltac:(apply in_or_app; left; exact INpA)) as Hpimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg.
assert (Hp8 : p mod 8 = 0) by (clear - Hpal; Z.div_mod_to_equations; lia).
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p n 0 HPc INpA ltac:(lia) ltac:(lia)) as SH0. rewrite Z.add_0_r in SH0.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p n 5 HPc INpA ltac:(lia) ltac:(lia)) as SH5. replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SH5 by lia.
if_falsex.
ub_skip.
unfold jhdr_cells in HDR, SZ. cbn [app hl_segs hla_base A4L A4H] in HDR, SZ.
pose proof (jtype_range shp) as JR.
asan_chk0.
bstep. rewrite sx32_small by lia. bstep. bstep. bstep.
destruct shp as [|u| |h|kids|kids]; cbn [jtype] in *; unfold JT_BOOLEAN, JT_DOUBLE, JT_INT, JT_STRING, JT_OBJECT, JT_ARRAY in *; if_lit.
-
bstep. bstep. if_lit.
destruct Jc as (pb_ & PBS & REST & EBS & OPB & (b & junk_ & ER & CELLS)). cbn [hl_segs hla_base A4L A4H] in CELLS. unfold jhdr_cells in CELLS. cbn [app] in CELLS.
bstep. asan_chkA.
bstep. bstep.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
-
bstep. bstep. if_lit. bstep. bstep. if_lit.
destruct Jc as (pb_ & PBS & REST & EBS & OPB & Jc). cbn [hl_segs hla_base A4L A4H] in Jc.
lazymatch type of HPc with HEAPA _ _ _ _ _ _ _ ?mc _ => assert (CELLS : exists tojs' udel' ud' bits, rw_cells asegs mc p (jhdr_cells 2 1 tojs' pb_ udel' ud' ++ [C8 bits])) end.
{ destruct u; [destruct Jc as (bits & ud_ & udn & uds & _ & _ & C & _) | destruct Jc as (bits & _ & _ & C)]; do 4 eexists; exact C. }
clear Jc. destruct CELLS as (tojs' & udel' & ud' & bits & CELLS). unfold jhdr_cells in CELLS. cbn [app] in CELLS.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MIc : mem_inv asegs mc |- _ =>
let b1 := eval vm_compute in (match image_bytes asegs 0x10358 8 with Some bs => bs | None => [] end) in
assert (RO1 : ro_cells asegs mc 0x10358 [CB 8 b1]) by (change 8%nat with (length b1); apply ro_cells_image; [exact MIc | vm_compute; reflexivity | lia | cbn; lia]);

let b3 := eval vm_compute in (match image_bytes asegs 0x10300 8 with Some bs => bs | None => [] end) in
assert (RO3 : ro_cells asegs mc 0x10300 [CB 8 b3]) by (change 8%nat with (length b3); apply ro_cells_image; [exact MIc | vm_compute; reflexivity | lia | cbn; lia]) end end.
bstep. asan_chkA.
bstep. bstep. bstep. bstep. bstep.
if_cases Hc1.
+
bstep. rewrite ?sxb_zero. bstep. if_false. bstep. bstepz. bstep. bstep.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
+ bstep. bstep. bstep.
if_cases Hc2.
*
bstep. bstep. bstep. bstep. bstep. bstep. bstep.
if_cases Hc3.
--
pose proof (bv_unsigned_in_range 64 bits) as BITR. change (bv_modulus 64) with (2^64) in BITR.
assert (NANOK : forall b : word, bv_ltu (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned b) 1))) 1)) (Z_to_bv 64 9218868437227405313) = true ->
fp_is_nan fmt_double (bv_unsigned b) = false).
{ clear. intros b H. pose proof (bv_unsigned_in_range 64 b) as BR. change (bv_modulus 64) with (2^64) in BR.
apply QAzu.Mq1.nan_test_clear; [exact BR|].
rewrite OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.bv_ltu_Z in H. apply Z.ltb_lt in H. rewrite (unsigned_lit 9218868437227405313) in H by lia.
rewrite !unsigned_lit_wrap in H. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 in H by lia.
replace ((bv_unsigned b * 2 ^ 1) mod 2 ^ 64 / 2 ^ 1) with (bv_unsigned b mod 2 ^ 63) in H by (clear H; Z.div_mod_to_equations; lia).
rewrite Z.mod_small in H by (clear H; Z.div_mod_to_equations; lia). exact H. }
assert (UBLO : bv_eqb (bword (flt_d (Z_to_bv 64 13830554455654793216) bits)) (Z_to_bv 64 0) = false).
{ unfold flt_d. rewrite (unsigned_lit 13830554455654793216) by lia. change 13830554455654793216 with QAzu.Mq1.B_M1.
change (fst (fp_lt fmt_double ?a ?b)) with (QAzu.Mq1.flt a b).
rewrite (QAzu.Mq1.ub_u64_lo (bv_unsigned bits) BITR (NANOK bits Hc3)); [reflexivity|].
unfold flt_d in Hc2. rewrite (unsigned_lit 0) in Hc2 by lia.
change (fst (fp_lt fmt_double ?a ?b)) with (QAzu.Mq1.flt a b) in Hc2.
destruct (QAzu.Mq1.flt (bv_unsigned bits) 0); [discriminate | reflexivity]. }
assert (UBHI : bv_eqb (bword (flt_d bits (Z_to_bv 64 4895412794951729152))) (Z_to_bv 64 0) = false).
{ unfold flt_d. rewrite (unsigned_lit 4895412794951729152) by lia. change 4895412794951729152 with QAzu.Mq1.B_U64MAX.
change (fst (fp_lt fmt_double ?a ?b)) with (QAzu.Mq1.flt a b).
rewrite (QAzu.Mq1.ub_u64_hi (bv_unsigned bits) BITR (NANOK bits Hc3)); [reflexivity|].
unfold fle_d in Hc1. rewrite (unsigned_lit 4895412794951729152) in Hc1 by lia. change 4895412794951729152 with QAzu.Mq1.B_U64MAX in Hc1.
change (fst (fp_le fmt_double ?a ?b)) with (QAzu.Mq1.fle a b) in Hc1.
destruct (QAzu.Mq1.fle QAzu.Mq1.B_U64MAX (bv_unsigned bits)); [discriminate | reflexivity]. }
bstep. bstep. bstep. bstep. rewrite UBLO; cbv iota.
bstep. bstep. rewrite UBHI; cbv iota.
bstep. bstep. gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
--
bstep. rewrite ?sxb_zero. bstep. if_false. bstep. bstep. bstepz. bstep.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
*
bstep. rewrite ?sxb_zero. bstep. if_true. bstep. bstep. bstepz. bstep.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
-
bstep. bstep. if_lit. bstep. bstep. if_lit.
destruct Jc as (pb_ & PBS & REST & EBS & OPB & (cty & v & junk_ & ER & Hcty & CELLS)). cbn [hl_segs hla_base A4L A4H] in CELLS. unfold jhdr_cells in CELLS. cbn [app] in CELLS.
assert (INp56 : In (p, 56) (BS ++ LB)) by (apply in_or_app; left; rewrite EBS, ER; cbn; left; reflexivity).
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p 56 6 HPc INp56 ltac:(lia) ltac:(lia)) as SH6. replace (p / 8 + 2147450880 + 6) with (p / 8 + 2147450886) in SH6 by lia.
bstep. asan_chkA.
bstep. rewrite sx32_small by lia. bstep. bstep.
destruct Hcty as [-> | ->]; if_lit.
+
bstep. if_lit.
bstep. asan_chkA. bstep. bstep.
if_cases Hc7.
* gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
* bstep. rewrite ?sxb_zero. bstep. if_false. bstep. bstep. bstepz. bstep.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
+
bstep. asan_chkA. bstep. bstep.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
-
bstep. bstep. if_lit.
destruct Jc as (pb_ & PBS & REST & EBS & OPB & Jc). cbn [hl_segs hla_base A4L A4H] in Jc, OPB.
lazymatch type of HPc with HEAPA _ _ _ _ _ _ _ ?mc _ =>
assert (TXT : exists (TX TB TBN len : Z) (str0 rest0 : list byte) (lencell : list cell),
In (TB, TBN) BS /\ TB <= TX /\ TX + Z.of_nat (length str0) + 1 <= TB + TBN /\ ~ In (Z_to_bv 8 0) str0 /\
bytes_at asegs mc TX (str0 ++ [Z_to_bv 8 0]) /\
rw_cells asegs mc (p + 40) (C8 (Z_to_bv 64 len) :: lencell) /\ -2^31 < len < 2^31 /\
((0 <= len /\ TX = p + 48) \/ (len < 0 /\ lencell = [C8 (Z_to_bv 64 TX)])) /\
(exists pn, In (p, pn) BS /\ 56 <= pn)) end.
{ destruct h.
- destruct Jc as (len & pd & pdn & str & junk2 & ER & Hlen & Hstr & Hpdn & C1 & C2).
destruct (first_nul_split2A str junk2) as (str0 & rest0 & E0 & NIN & L0).
exists pd, pd, pdn, len, str0, rest0, [C8 (Z_to_bv 64 pd)].
split; [rewrite EBS, ER; cbn; right; left; reflexivity|]. split; [lia|]. split; [lia|]. split; [exact NIN|].
split. { apply rw_cells_bytes_at in C2. cbn [cells_bytes cbytes app] in C2. rewrite app_nil_r in C2.
eapply bytes_at_cstr_prefix2A; [exact C2 | exact E0]. }
split. { unfold jhdr_cells in C1. cbn [app] in C1. apply rw_cells_app with (cs1 := [_;_;_;_;_;_]) in C1 as [_ C1]. cbn [cells_size csize Nat.add] in C1. change (p + Z.of_nat 40) with (p + 40) in C1. exact C1. }
split; [lia|]. split; [right; split; [lia | reflexivity]|]. exists 56. split; [rewrite EBS, ER; cbn; left; reflexivity | lia].
- destruct Jc as (len & str & junkS & ER & Hlen & Hstr & C1).
destruct (first_nul_split2A str junkS) as (str0 & rest0 & E0 & NIN & L0).
exists (p + 48), p, (str_objsize len), len, str0, rest0, [CB (Z.to_nat (str_objsize len - 48)) (str ++ [Z_to_bv 8 0] ++ junkS)].
split; [rewrite EBS, ER; cbn; left; reflexivity|]. split; [lia|]. split; [unfold str_objsize; lia|]. split; [exact NIN|].
unfold jhdr_cells in C1. cbn [app] in C1. apply rw_cells_app with (cs1 := [_;_;_;_;_;_]) in C1 as [_ C1]. cbn [cells_size csize Nat.add] in C1. change (p + Z.of_nat 40) with (p + 40) in C1.
split. { pose proof C1 as C2. apply rw_cells_app with (cs1 := [_]) in C2 as [_ C2]. cbn [cells_size csize Nat.add] in C2.
apply rw_cells_bytes_at in C2. cbn [cells_bytes cbytes app] in C2. rewrite app_nil_r in C2.
change (p + 40 + Z.of_nat 8) with (p + 40 + 8) in C2. replace (p + 40 + 8) with (p + 48) in C2 by lia. eapply bytes_at_cstr_prefix2A; [exact C2 | exact E0]. }
split; [exact C1|]. split; [lia|]. split; [left; split; [lia | reflexivity]|]. exists (str_objsize len). split; [rewrite EBS, ER; cbn; left; reflexivity | unfold str_objsize; lia]. }
clear Jc. destruct TXT as (TX & TB & TBN & len & str0 & rest0 & lencell & INT & TLO & THI & NIN & BY & LENC & Hlen & ALT & (pn & INpn & Hpn)).
assert (INTA : In (TB, TBN) ((BS ++ LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; left; exact INT).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ TB TBN HPc INTA) as (_ & _ & Htlo & Hthi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ TB TBN HPc INTA) as Htimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Htimg.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HPc INF INTA) as DFT. rewrite fr_size_0 in DFT.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ TB TBN HPc INTA) as APT. cbn [hl_sb A4L] in APT. unfold A_SB in APT.
assert (INpnA : In (p, pn) (BS ++ LB)) by (apply in_or_app; left; exact INpn).
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p pn 6 HPc INpnA ltac:(lia) ltac:(lia)) as SH6. replace (p / 8 + 2147450880 + 6) with (p / 8 + 2147450886) in SH6 by lia.
apply rw_cells_app with (cs1 := [_]) in LENC as [LEN1 LEN2]. cbn [cells_size csize Nat.add] in LEN2. change (p + 40 + Z.of_nat 8) with (p + 40 + 8) in LEN2. replace (p + 40 + 8) with (p + 48) in LEN2 by lia.

lazymatch goal with |- evt _ ?Q (MS ?r ?Fx ?pc ?fcx None ?mc ?rom) =>
let r' := open_constr:(mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in unify r r';
lazymatch r' with mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31 =>
assert (CONT : forall xa1 : word, evt asegs Q
(MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 TX) xa1 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) Fx (Z_to_bv 64 0x9eb28) fcx None mc rom))
end end.
{ intros xa1.
bstep. bstep. bstep.
pose proof (unpoisoned_of_blk HIx _ _ _ _ _ _ _ TB TBN TX (Z.of_nat (length str0) + 1) HPc ltac:(apply in_or_app; left; exact INT) ltac:(lia) ltac:(lia) ltac:(lia)) as UNS.
lazymatch type of FSH1 with rw_cells _ ?mc _ _ => assert (UNE : unpoisoned asegs mc A_SB (Fr + 32) 8) end.
{ pose proof (rw_cells_bytes_at asegs _ _ _ FSH1) as SHB. cbn [cells_bytes cbytes app] in SHB.
lazymatch type of SHB with bytes_at _ _ _ ?wb => eapply (unpoisoned_gran8 asegs _ A_SB (Fr + 32) wb ltac:(clear - HFal; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(unfold A_SB; lia) eq_refl) end.
- replace (((Fr + 32) / 8 + A_SB) / 8 * 8) with sh by (unfold sh, A_SB; clear - HFal; Z.div_mod_to_equations; lia). exact SHB.
- replace (((Fr + 32) / 8 + A_SB) mod 8) with 4 by (unfold A_SB; clear - HFal; Z.div_mod_to_equations; lia). reflexivity. }
evt_done5.
eapply PI64 with (LB := BS ++ LB) (LM := LM) (FRS := (Fr, 0) :: FRS) (B := B) (str := str0) (SA := TX) (R := Fr + 32) (lo := lo);
[ exact HPc | rewrite unsigned_lit by lia; eassumption | exact LO | unfold PI64_STK_A; rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; clear - SPA; Z.div_mod_to_equations; lia | rewrite unsigned_lit by lia; lia
| unfold A_ERRNO, A_TP; eassumption | reflexivity | rewrite unsigned_lit by lia; reflexivity
| reflexivity | reflexivity | exact BY | exact NIN
| exists TB, TBN; split; [apply in_or_app; left; exact INT | lia]
| exact UNS
| exists Fr, 0; split; [exact INF | rewrite fr_size_0; lia]
| exact FFe | exact UNE | clear - HFal; Z.div_mod_to_equations; lia
| cbn [length]; lia
| ].
rewrite ?unsigned_lit by lia.
intros ms3 md3 m3 A3 rv vR eR RS3 VM3 ST3 PD3 HRV RC3 ERR3 HP3. open_ret RS3.

pose proof (frame_above_img HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFhi. cbn [hl_img_hi A4H] in HFhi.
lazymatch type of PD3 with heap_presD _ _ _ ?mb _ =>
assert (HPR3 : heap_pres A4H [(Fr, 32); (sh, 8)] (bv_unsigned sp + -96) mb m3) end.
{ intros a Ha Hc. apply (PD3 a Ha).
- destruct Hc as [Hc | [Hc | (b & Hb & Hr)]]; [left; exact Hc | right; left; exact Hc |].
right; right. destruct Hb as [<- | [<- | []]]; cbn [blk_addr blk_size fst snd] in Hr.
+ exists (Fr, fr_size 0 - 8). split; [apply in_or_app; right; apply in_or_app; right; cbn [fr_ivs flat_map app fr_base fr_class fst snd]; left; reflexivity | cbn [blk_addr blk_size fst snd]; rewrite fr_size_0; lia].
+ exists (shad A4L Fr, fr_shadow_len 0). split; [apply in_or_app; right; apply in_or_app; right; cbn [fr_ivs flat_map app fr_base fr_class fst snd]; right; left; reflexivity | unfold shad; cbn [blk_addr blk_size fst snd hl_sb A4L]; rewrite fr_shadow_len_0; unfold A_SB; fold sh; lia].
- destruct Hc as [Hc | [Hc | (b & Hb & Hr)]].
+ lia.
+ cbn [hl_client_static A4H] in Hc. unfold a4_client_static in Hc. lia.
+ destruct Hb as [<- | [<- | []]]; cbn [blk_addr blk_size fst snd] in Hr; lia. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FFa; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FSH1; [| eapply client_range_block; [right; left; reflexivity | lia | cbn; lia]].
change (hl_segs A4H) with asegs in FR, FFa, FSH1.
lazymatch goal with MUc : munch _ m1' ?mc, WMc : wmono asegs m1' ?mc |- _ =>
assert (PDm3 : heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m3);
[ eapply heap_presD_trans; [exact (XPD m1' mc PD1 A1 md1 HP1 MUc WMc) |];
eapply heap_presD_weaken; [exact PD3 | lia |];
let b := fresh "b" in let Hb := fresh "Hb" in intros b Hb; rewrite app_assoc in Hb; apply in_app_or in Hb; rewrite app_assoc; apply in_or_app;
destruct Hb as [Hb|Hb]; [left; exact Hb | right; cbn [fr_ivs flat_map app]; right; right; exact Hb]
| clear MUc WMc ] end.
assert (VM13 : model_vm_only (cfg_model md) (cfg_model md3)) by (eapply model_vm_only_trans; [exact VM1 | exact VM3]).
assert (XHP3 : forall mX, munch [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6444156, 6444160)] m3 mX -> wmono asegs m3 mX -> mem_inv asegs mX ->
HEAPAx A3 (BS ++ LB) LM ((Fr, 0) :: FRS) B mX md3).
{ intros mX MUX WMX MIX. exact (fk0_HEAPA HIx _ _ _ _ _ _ _ _ _ _ _ HP3 LO HT MUX WMX MIX). }
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI3. change (hl_segs A4L) with asegs in MI3.
pose proof (wmono_refl asegs m3) as WM. pose proof (munch_refl [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6444156, 6444160)] m3) as MU.
unfold A_ERRNO, A_TP in ERR3. change (6444320 - 164) with 6444156 in ERR3.
replace (ret_pc (Z_to_bv 64 650036)) with (Z_to_bv 64 650036) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
reenterA asegs A4L HIx asegs_wx HP3.
bstep.

destruct HRV as [-> | ->]; if_lit.
+
bstep. bstep.
gi_exit EPI XHP3 XPD PDm3 HP3 A3 md3 m3 VM13.
+
bstep.
gi_exit EPI XHP3 XPD PDm3 HP3 A3 md3 m3 VM13. }
bstep. asan_chkA.
bstep. bstep. bstep.
destruct ALT as [[Hl ETX] | [Hl ->]].
+  if_truex. rewrite <- ETX. apply CONT.
+  if_falsex. asan_chkA. bstep. apply CONT.
-  bstep. bstep. if_lit. bstep. bstep. if_lit. gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
-  bstep. bstep. if_lit. bstep. bstep. if_lit. gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
Qed.
End AJoGetUint64.
End RC__1.
