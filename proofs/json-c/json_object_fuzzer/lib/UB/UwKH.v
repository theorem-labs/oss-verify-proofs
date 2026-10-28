(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG Qnhz QO3A Q7m0 QSpR QuJV QCPB QH7x QXup UEQM Lib.GwApply QWxq Qfw3 QRjH QHnV QCcH QfLs Q0Ek QjDH UC8c Qsw7 QJjn UBpZ UT7i Uv6q U7zy UD4E UzWc QnCn UJ3T Qio9 QHXC Qfe5 QId5 QBGG Uuoa ULch Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QsRG.Mq0 Qnhz.Mq0 QsRG QO3A Q7m0 QSpR.Mq4 QuJV QCPB.Mq0 QH7x.
Import QXup.
Import UEQM.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq.Mq0 Qfw3.Mq2.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0.
Import UC8c.Mq0.
Import Qsw7 QJjn.
Import UBpZ UT7i Uv6q U7zy UD4E.
Import UzWc.
Import QnCn.Mq0.
Import UJ3T.
Import Qio9 QHXC Qfe5 QId5 QBGG.
Import Uuoa.Mq0 ULch.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma land1_cases : forall fl, 0 <= fl -> Z.land fl 1 = 0 \/ Z.land fl 1 = 1.
Proof.
intros fl H. change 1 with (Z.ones 1) at 1. change 1 with (Z.ones 1) at 2. rewrite !Z.land_ones by lia.
change (2^1) with 2. pose proof (Z.mod_pos_bound fl 2 ltac:(lia)). lia.
Qed.
#[using="Type"] Lemma land2_cases : forall fl, 0 <= fl -> Z.land fl 2 = 0 \/ Z.land fl 2 = 2.
Proof.
intros fl H.
assert (E : Z.land fl 2 = 2 * Z.b2z (Z.testbit fl 1)).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
destruct (Z.eq_dec i 1) as [->|NE].
- change (Z.testbit 2 1) with true. rewrite Bool.andb_true_r. destruct (Z.testbit fl 1); reflexivity.
- replace (Z.testbit 2 i) with false.
2:{ symmetry. destruct (Z.eq_dec i 0) as [->|NE0]; [reflexivity|]. apply Z.bits_above_log2; [lia | cbn; lia]. }
rewrite Bool.andb_false_r. symmetry. destruct (Z.testbit fl 1).
+ change (2 * Z.b2z true) with 2. destruct (Z.eq_dec i 0) as [->|NE0]; [reflexivity|]. apply Z.bits_above_log2; [lia | cbn; lia].
+ change (2 * Z.b2z false) with 0. apply Z.bits_0. }
rewrite E. destruct (Z.testbit fl 1); cbn; lia.
Qed.
#[using="Type"] Lemma land3_lor : forall fl, Z.land fl 3 = Z.lor (Z.land fl 1) (Z.land fl 2).
Proof. intros fl. change 3 with (Z.lor 1 2). rewrite Z.land_lor_distr_r. reflexivity. Qed.

Section WithFn.
Variable fn : fnaddrs.
#[using="Type"] Lemma kids_okp_nth : forall m kids ps KBS i k,
kids_okp rsegs fn m kids ps KBS -> nth_error kids i = Some k ->
exists v bs, nth_error ps i = Some v /\ nth_error KBS i = Some bs /\
match k with None => v = 0 /\ bs = [] | Some s' => v <> 0 /\ jval rsegs fn s' m bs v 1 end.
Proof.
intros m kids. induction kids as [|k0 kids IH]; intros ps KBS i k KOK Hn; [destruct i; discriminate Hn|].
destruct ps as [|v0 ps]; [destruct KOK|]. destruct KBS as [|bs0 KBS]; [destruct KOK|].
rewrite kids_okp_cons in KOK. destruct KOK as [H0 KOK].
destruct i as [|i]; cbn in Hn |- *.
- injection Hn as ->. exists v0, bs0. auto.
- eapply IH; eassumption.
Qed.
#[using="Type"] Lemma kids_okp_len : forall m kids ps KBS, kids_okp rsegs fn m kids ps KBS -> length ps = length kids /\ length KBS = length kids.
Proof.
intros m kids. induction kids as [|k0 kids IH]; intros ps KBS KOK.
- destruct ps; [|destruct KOK]. destruct KBS; [|destruct KOK]. split; reflexivity.
- destruct ps as [|v0 ps]; [destruct KOK|]. destruct KBS as [|bs0 KBS]; [destruct KOK|].
rewrite kids_okp_cons in KOK. destruct KOK as [_ KOK]. destruct (IH _ _ KOK) as [L1 L2]. cbn. lia.
Qed.
End WithFn.

Section Ser.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Hypothesis MEMMOVE : memmove_stmt.
Hypothesis HT63 : hi_top S4L HIx < 2^63.

Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB : list blk) (pb lo p rc pb0 lv fl a : Z).
Variables (ABS : list blk) (ps : list Z) (KBS : list (list blk)) (kids : list (option jshape)) (T : TSet).
Let usp := bv_unsigned sp.
Hypothesis KIDS : forall s', In (Some s') kids -> ser_spec HIx (fn_of s') s'.
Hypothesis LBS : lb_small LB.
Hypothesis FL : flags_ok fl.
Hypothesis Hlv : 0 <= lv.
Hypothesis Hlvd : lv + sdepth (Sarr kids) <= 1000.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= usp - ser_budget (Sarr kids).
Hypothesis SPA : usp mod 16 = 0.
Hypothesis HT : usp <= hi_top S4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis FRM : frm0 fc.
Hypothesis INCL : incl ((p, 48) :: ABS ++ concat KBS) LB.
Hypothesis NODE0 : rw_cells rsegs m0 p (jhdr_cells JT_ARRAY rc (fn_arr_to_json_string S4F) pb0 0 0 ++ [C8 (Z_to_bv 64 a)]).
Hypothesis AL0 : alist rsegs S4F m0 ABS a ps.
Hypothesis KOK : kids_okp rsegs S4F m0 kids ps KBS.
Hypothesis K : forall ms' md', ser_post HIx ra sp gp (Z_to_bv 64 TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB pb lo ms' md' ->
realizes rsegs (mkCfg ms' md') T.

Variables (f1 f2 : Z).
Hypothesis Hf1 : Z.land fl 1 = f1.
Hypothesis Hf2 : Z.land fl 2 = f2.

Notation ser_memx := (ser_mem HIx sp m0 md0 LB pb lo).
Let LEN := Z.of_nat (length ps).
Definition savedR : list cell := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

#[using="RC__ ra m0 a ABS LBS FL LOS INCL AL0 KOK"] Lemma facts :
0 <= usp < 2^64 /\ In (p, 48) LB /\
Z.land fl 32 = 0 /\ Z.land fl 16 = 0 /\ Z.land fl 8 = 0 /\ 0 <= fl < 2^31 /\
0 <= kdepth kids /\ lo <= usp - 160 - 208 * kdepth kids - 8560 /\
LEN = Z.of_nat (length kids) /\ length KBS = length kids /\ LEN < 2^61.
Proof.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
assert (INp : In (p, 48) LB) by (apply INCL; left; reflexivity).
destruct FL as [Rfl FL56]. destruct (land56_bits fl FL56) as (FL32 & FL16 & FL8).
pose proof (kdepth_nonneg kids) as KD. unfold ser_budget in LOS. rewrite sdepth_arr in LOS.
destruct (kids_okp_len _ _ _ _ _ KOK) as [L1 L2].
destruct AL0 as (arr & size & junk & _ & Hps & Hsz & _).
repeat split; try assumption; unfold LEN, usp in *; lia.
Qed.

#[using="ra fl usp LBS FL LOS INCL NODE0 AL0 KOK LEN"] Lemma factsM : forall FA FR m md, ser_memx FA FR m md ->
mem_inv rsegs m /\ model_ok md /\ 0 < p /\ p + 48 <= alloc_ceiling /\ p mod 16 = 0 /\
rw_cells rsegs m p (jhdr_cells JT_ARRAY rc (fn_arr_to_json_string S4F) pb0 0 0 ++ [C8 (Z_to_bv 64 a)]) /\
alist rsegs S4F m ABS a ps /\
(forall i s' v bs, nth_error kids i = Some (Some s') -> nth_error ps i = Some v -> nth_error KBS i = Some bs ->
jval rsegs S4F s' m bs v 1 /\ incl bs LB /\ 0 < v /\ v + 48 <= alloc_ceiling /\ v mod 16 = 0 /\ sdepth s' <= kdepth kids).
Proof.
intros FA FR m md (A & buf & cap & bpos & content & errv & HP & PB & FRc & ERR & ST & HPR & VM).
pose proof facts as (SPR & INp & _).
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
assert (INp' : In (p, 48) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; exact INp).
pose proof (heap_blk S4L HIx _ _ _ _ p 48 HP INp') as (_ & Hpal & Hplo & Hphi & _).
assert (AG : agree_on rsegs LB m0 m) by (eapply (agree_of_heap_pres rsegs S4L); [exact HPR | reflexivity | apply incl_refl]).
split; [exact MI|]. split; [exact (heap_model_ok _ _ _ _ _ _ HP)|]. split; [exact Hplo|]. split; [exact Hphi|]. split; [exact Hpal|].
split. { eapply (heap_pres_rw_cells S4L); [exact HPR | exact NODE0 |]. right; right. exists (p, 48). split; [exact INp | cbn; lia]. }
split. { eapply (alist_agree rsegs S4F); [exact AL0 | exact AG |]. intros b Hb. apply INCL. right. apply in_or_app. left. exact Hb. }
intros i s' v bs Hk Hp Hb.
destruct (kids_okp_nth _ _ _ _ _ i (Some s') KOK Hk) as (v' & bs' & Hp' & Hb' & Hv & J).
rewrite Hp in Hp'. injection Hp' as <-. rewrite Hb in Hb'. injection Hb' as <-.
assert (IB : incl bs LB).
{ intros b Hbb. apply INCL. right. apply in_or_app. right. apply in_concat. exists bs. split; [| exact Hbb]. eapply nth_error_In. exact Hb. }
assert (J' : jval rsegs S4F s' m bs v 1) by (eapply (jval_agree rsegs S4F); [exact J | exact AG | exact IB]).
split; [exact J'|]. split; [exact IB|].
destruct (proj1 (jval_split rsegs S4F s' m bs v 1) J') as (pbc & PBSc & RESTc & Ebs & _ & JN).
destruct (jnode_hdr rsegs S4F _ _ _ _ _ _ JN) as (n & ty & udel & ud & cs & rest & ER & Hn & _).
assert (INv : In (v, n) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; apply IB; rewrite Ebs, ER; apply in_or_app; left; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ v n HP INv) as (_ & Hval & Hvlo & Hvhi & _).
split; [exact Hvlo|]. split; [lia|]. split; [exact Hval|].
apply kdepth_in. eapply nth_error_In. exact Hk.
Qed.

#[using="INCL"] Lemma abs_ok : forall FA FR m md, ser_memx FA FR m md ->
forall b n, In (b, n) ABS -> 0 < b /\ b mod 16 = 0 /\ b + n <= alloc_ceiling.
Proof.
intros FA FR m md (A & buf & cap & bpos & content & errv & HP & _) b n Hb.
assert (IN : In (b, n) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; apply INCL; right; apply in_or_app; left; exact Hb).
pose proof (heap_blk S4L HIx _ _ _ _ b n HP IN) as (_ & H1 & H2 & H3 & _). repeat split; assumption.
Qed.

#[using="RC__ ra sp m0 LB lo p fl a ABS ps KBS kids usp LBS FL LOS INCL AL0 KOK Hf1 LEN"] Lemma FC1 : f1 = 0 \/ f1 = 1. Proof. rewrite <- Hf1. apply land1_cases. pose proof facts as (_ & _ & _ & _ & _ & R & _). lia. Qed.
#[using="RC__ ra sp m0 LB lo p fl a ABS ps KBS kids usp LBS FL LOS INCL AL0 KOK Hf2 LEN"] Lemma FC2 : f2 = 0 \/ f2 = 2. Proof. rewrite <- Hf2. apply land2_cases. pose proof facts as (_ & _ & _ & _ & _ & R & _). lia. Qed.

Definition arrFR : list cell :=
[C8 (Z_to_bv 64 lv); C8 (Z_to_bv 64 0x127bc); C8 (Z_to_bv 64 0x13204); C8 (Z_to_bv 64 0x105a2); C8 (Z_to_bv 64 (2 * lv + 2));
C8 (Z_to_bv 64 (lv + 1073741825)); C8 (Z_to_bv 64 0)] ++ savedR.

#[using="MEMMOVE fc p fl a ABS ps KBS kids LBS FL LO LOS SPA HT RA INCL AL0 KOK K LEN"] Lemma arr_tailcall :
forall (x2 x3 t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' m md FR (lit k : Z) (bs : list byte),
x2 = sp -> x3 = gp ->
ser_memx (usp + -160) FR m md -> cells_size FR = 160%nat ->
ro_bytes_b rsegs lit bs = true -> Z.of_nat (length bs) = k -> 0 < k < 2^31 -> 0 <= lit -> lit + k < 2^64 ->
fsaved F F' -> frm0 fc' ->
realizes rsegs (mkCfg (MS (mkR ra x2 x3 (Z_to_bv 64 TP) t0 t1 t2 s0 s1 (Z_to_bv 64 pb) (Z_to_bv 64 lit) (Z_to_bv 64 k) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F' (Z_to_bv 64 MEMAPPEND) fc' None m (seg_rom rsegs)) md) T.
Proof.
intros until bs. intros -> -> INV HFR RB BL Hk Hl Hlk FS' FR'.
pose proof facts as (SPR & INp & FL32 & FL16 & FL8 & Rfl & KD & LOS' & _).
destruct INV as (A & buf & cap & bpos & content & errv & HP & PB & FRc & ERR & ST & HPR & VM).
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (stk_release rsegs _ _ _ _ ST FRc ltac:(lia)) as ST'. rewrite HFR in ST'.
replace (usp + -160 + Z.of_nat 160) with usp in ST' by lia.
destruct (ro_src m lit bs LB k usp MI RB BL Hl ltac:(lia)) as [SB SBC].
eapply (memappend_cps HIx MEMMOVE) with (A := A) (LB := LB) (buf := buf) (bpos := bpos) (cap := cap) (b := lit) (n := k)
(lo := lo) (content := content) (src := bs) (errv := errv).
- exact HP.
- exact PB.
- lia.
- exact SB.
- exact BL.
- exact SBC.
- lia.
- lia.
- destruct (ser_src_sep_buf HIx _ _ _ _ _ _ _ _ _ _ _ HP SBC BL Hl ltac:(lia) ltac:(unfold usp; unfold_consts; lia)) as [?|SEP]; [lia | exact SEP].
- exact ST'.
- exact LO.
- unfold ser_budget in LOS. unfold usp in *. lia.
- exact SPA.
- exact HT.
- unfold ERRNO in ERR. exact ERR.
- unfold TP. reflexivity.
- exact RA.
- reflexivity.
- reflexivity.
- reflexivity.
- intros ms' md' POST.
destruct POST as (m' & A' & r & errv' & buf' & cap' & RS & VM' & ST2 & HPR' & ERR' & HP' & OUT).
destruct RS as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F'' & fc'' & -> & FS'' & FR'').
apply K. unfold ser_post.
assert (PB' : exists bpos' content', pbuf_core rsegs m' pb buf' bpos' cap' content').
{ destruct OUT as [[_ PBF] | (_ & -> & -> & PBC)].
- destruct PBF as (bufq & bposq & sizeq & pre & post & E & L & C). injection E as <- <-. eauto.
- eauto. }
destruct PB' as (bpos' & content' & PB').
exists m', A', (Z_to_bv 64 r), errv', buf', cap', bpos', content'.
split; [| split; [eapply model_vm_only_trans; [exact VM | exact VM'] | split; [exact ST2 | split; [| split; [unfold ERRNO; exact ERR' | split; [exact HP' | exact PB']]]]]].
+ unfold TP. apply ret_statew_intro; [eapply fsaved_trans; [exact FS' | exact FS''] | intros _; exact (FR'' FR')].
+ eapply heap_pres_trans; [exact HPR | exact HPR'].
Qed.

#[using="MEMMOVE fc p rc pb0 a ABS ps KBS kids LBS FL LO LOS SPA HT RA INCL NODE0 AL0 KOK K f1 f2 Hf1 Hf2 LEN"] Lemma arr_close :
forall (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) F' fc' m md (pre : list cell),
ser_memx (usp + -160) (pre ++ savedR) m md -> cells_size pre = 56%nat ->
fsaved F F' -> frm0 fc' ->
realizes rsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (usp + -160)) gp (Z_to_bv 64 TP) t0 t1 t2 (Z_to_bv 64 pb) x9 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 fl) x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F' (Z_to_bv 64 0x25208) fc' None m (seg_rom rsegs)) md) T.
Proof.
intros until pre. intros INV Hpre FS' FR'. pose proof FC1 as C1. pose proof FC2 as C2.
pose proof facts as (SPR & INp & FL32 & FL16 & FL8 & Rfl & KD & LOS' & _).
destruct (factsM _ _ _ _ INV) as (MI & MOK & _).
pose proof INV as INV'. destruct INV as (A & buf & cap & bpos & content & errv & HP & PB & FRc & ERR & ST & HPR & VM).
destruct PB as (Hbp & Hcap & Hln & PBS & PBUF). unfold ERRNO in ERR. unfold TP.
pose proof (heap_blk S4L HIx _ _ _ _ pb PB_SZ HP ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
apply (proj1 (rw_cells_app rsegs _ _ _ _)) in FRc as [FRp FRs]. rewrite Hpre in FRs. change (Z.of_nat 56) with 56 in FRs.
replace (usp + -160 + 56) with (usp + -104) in FRs by lia. unfold savedR in FRs. unfold usp in *. unfold_consts.
assert (Rfl64 : 0 <= fl < 2^64) by lia.
apply rz_evt; [exact MOK|].
destruct (Z.eq_dec (Z.lor f1 f2) 1) as [E1|NE1].
-
symb_run 30%nat [MEMAPPEND] [false].
2:{ sc_cbn. rewrite alu_and3 by lia. rewrite land3_lor, Hf1, Hf2.
destruct C1 as [E|E]; rewrite E in *; destruct C2 as [E'|E']; rewrite E' in *; compute in E1; try lia; vm_compute; reflexivity. }
apply evt_RZ_done. eapply (arr_tailcall _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' _ md (pre ++ savedR) 0x10659 2 [Z_to_bv 8 32; Z_to_bv 8 93]);
[ first [reflexivity | apply bv_eq; rewrite unsigned_lit by lia; lia] | reflexivity | exact INV' | rewrite cells_size_app, Hpre; reflexivity
| vm_compute; reflexivity | reflexivity | lia | lia | lia | exact FS' | exact FR' ].
- symb_run 30%nat [MEMAPPEND] [true].
2:{ sc_cbn. rewrite alu_and3 by lia. rewrite land3_lor, Hf1, Hf2.
destruct C1 as [E|E]; rewrite E in *; destruct C2 as [E'|E']; rewrite E' in *; compute in NE1; try congruence; vm_compute; reflexivity. }
apply evt_RZ_done. eapply (arr_tailcall _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' _ md (pre ++ savedR) 0x120da 1 [Z_to_bv 8 93]);
[ first [reflexivity | apply bv_eq; rewrite unsigned_lit by lia; lia] | reflexivity | exact INV' | rewrite cells_size_app, Hpre; reflexivity
| vm_compute; reflexivity | reflexivity | lia | lia | lia | exact FS' | exact FR' ].
Qed.

#[using="MEMMOVE fc p rc pb0 a ABS ps KBS kids LBS FL Hlv Hlvd LO LOS SPA HT RA INCL NODE0 AL0 KOK K f1 Hf1 Hf2 LEN"] Lemma arr_exit :
forall (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x24 x25 x27 t3 t4 t5 t6 : word) F' fc' m md (mid : list cell),
ser_memx (usp + -160) (C8 (Z_to_bv 64 lv) :: mid ++ C8 (Z_to_bv 64 0) :: savedR) m md -> cells_size mid = 40%nat ->
fsaved F F' -> frm0 fc' ->
realizes rsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (usp + -160)) gp (Z_to_bv 64 TP) t0 t1 t2 (Z_to_bv 64 pb) x9 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 fl) x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 f2) x27 t3 t4 t5 t6) F' (Z_to_bv 64 0x25200) fc' None m (seg_rom rsegs)) md) T.
Proof.
intros until mid. intros INV Hmid FS' FR'.
pose proof facts as (SPR & INp & FL32 & FL16 & FL8 & Rfl & KD & LOS' & _).
destruct (factsM _ _ _ _ INV) as (MI & MOK & _).
pose proof INV as INV'. destruct INV as (A & buf & cap & bpos & content & errv & HP & PB & FRc & ERR & ST & HPR & VM).
destruct PB as (Hbp & Hcap & Hln & PBS & PBUF). unfold ERRNO in ERR. unfold TP.
pose proof (heap_blk S4L HIx _ _ _ _ pb PB_SZ HP ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).

change (C8 (Z_to_bv 64 lv) :: mid ++ C8 (Z_to_bv 64 0) :: savedR) with ([C8 (Z_to_bv 64 lv)] ++ (mid ++ C8 (Z_to_bv 64 0) :: savedR)) in FRc.
apply (proj1 (rw_cells_app rsegs _ _ _ _)) in FRc as [FR0 FRms]. cbn [cells_size csize Nat.add] in FRms. change (Z.of_nat 8) with 8 in FRms.
apply (proj1 (rw_cells_app rsegs _ _ _ _)) in FRms as [FRm FRs]. rewrite Hmid in FRs. change (Z.of_nat 40) with 40 in FRs.
replace (usp + -160 + 8 + 40) with (usp + -112) in FRs by lia. unfold savedR in FRs. unfold usp in *. unfold_consts.
assert (Rlv : 0 <= lv < 1000) by (pose proof (sdepth_arr kids); pose proof (kdepth_nonneg kids); lia).
apply rz_evt; [exact MOK|].
destruct FC2 as [E2|E2]; rewrite E2.
-
symb_run 4%nat [0x25208]%Z (@nil bool).
apply evt_RZ_done. eapply arr_close with (pre := [C8 (Z_to_bv 64 lv)] ++ mid ++ [C8 (Z_to_bv 64 0)]);
[ rewrite <- !app_assoc; exact INV' | rewrite !cells_size_app, Hmid; reflexivity | exact FS' | exact FR' ].
-
symb_run 20%nat [MEMAPPEND] (@nil bool).
destruct (ro_src m 0x122e0 [Z_to_bv 8 10] LB 1 (bv_unsigned sp + -160) MI ltac:(vm_compute; reflexivity) eq_refl ltac:(lia) ltac:(lia)) as [SBq SBCq].
apply evt_RZ_done.
eapply (ser_append HIx MEMMOVE sp gp m0 md0 LB pb lo LO HT) with (F := F) (sb := [Z_to_bv 8 10]);
[ exact INV' | exact SBq | reflexivity | lia | lia | lia | exact SBCq | left; lia | lia
| replace (bv_unsigned sp + -160) with (bv_unsigned sp - 16 * 10) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS' | exact FR' | ].
clear dependent m. intros m2 md2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 INV2 FS2 FR2 _.
pose proof INV2 as INV2'. destruct (factsM _ _ _ _ INV2) as (MI2 & MOK2 & _).
destruct INV2 as (A2 & buf2 & cap2 & bpos2 & content2 & errv2 & HP2 & PB2 & FRc2 & ERR2 & ST2 & HPR2 & VM2). unfold ERRNO in ERR2.
change (C8 (Z_to_bv 64 lv) :: mid ++ C8 (Z_to_bv 64 0) :: savedR) with ([C8 (Z_to_bv 64 lv)] ++ (mid ++ C8 (Z_to_bv 64 0) :: savedR)) in FRc2.
apply (proj1 (rw_cells_app rsegs _ _ _ _)) in FRc2 as [FR0' FRms']. cbn [cells_size csize Nat.add] in FRms'. change (Z.of_nat 8) with 8 in FRms'.
apply (proj1 (rw_cells_app rsegs _ _ _ _)) in FRms' as [FRm' FRs']. rewrite Hmid in FRs'. change (Z.of_nat 40) with 40 in FRs'.
replace (bv_unsigned sp + -160 + 8 + 40) with (bv_unsigned sp + -112) in FRs' by lia. unfold savedR in FRs'.
apply rz_evt; [exact MOK2|].
symb_run 20%nat [PBMEMSET] (@nil bool). rewrite ?slliw1_small by lia.
apply evt_RZ_done.
eapply (ser_memset HIx sp gp m0 md0 LB pb lo LO HT) with (F := F);
[ exact INV2' | lia | lia
| replace (bv_unsigned sp + -160) with (bv_unsigned sp - 16 * 10) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS2 | exact FR2 | ].
clear dependent m2. intros m3 md3 t0_ t1_ t2_ a0_ a1_ a2_ a3_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ F3 fc3 INV3 FS3 FR3.
pose proof INV3 as INV3'. destruct (factsM _ _ _ _ INV3) as (MI3 & MOK3 & _).
destruct INV3 as (A3 & buf3 & cap3 & bpos3 & content3 & errv3 & HP3 & PB3 & FRc3 & ERR3 & ST3 & HPR3 & VM3). unfold ERRNO in ERR3.
change (C8 (Z_to_bv 64 lv) :: mid ++ C8 (Z_to_bv 64 0) :: savedR) with ([C8 (Z_to_bv 64 lv)] ++ (mid ++ C8 (Z_to_bv 64 0) :: savedR)) in FRc3.
apply (proj1 (rw_cells_app rsegs _ _ _ _)) in FRc3 as [FR0'' FRms'']. cbn [cells_size csize Nat.add] in FRms''. change (Z.of_nat 8) with 8 in FRms''.
apply (proj1 (rw_cells_app rsegs _ _ _ _)) in FRms'' as [FRm'' FRs'']. rewrite Hmid in FRs''. change (Z.of_nat 40) with 40 in FRs''.
replace (bv_unsigned sp + -160 + 8 + 40) with (bv_unsigned sp + -112) in FRs'' by lia. unfold savedR in FRs''.
apply rz_evt; [exact MOK3|].
symb_run 30%nat [MEMAPPEND] (@nil bool).
apply evt_RZ_done. eapply arr_tailcall with (FR := C8 (Z_to_bv 64 lv) :: mid ++ C8 (Z_to_bv 64 0) :: savedR) (bs := [Z_to_bv 8 93]);
[ first [reflexivity | apply bv_eq; rewrite unsigned_lit by lia; lia] | reflexivity | exact INV3' | cbn [cells_size csize app]; rewrite cells_size_app, Hmid; reflexivity
| vm_compute; reflexivity | reflexivity | lia | lia | lia | exact FS3 | exact FR3 ].
Qed.

#[using="fc p rc pb0 fl a ABS ps KBS kids LBS FL LO LOS INCL NODE0 AL0 KOK K LEN"] Lemma arr_fail :
forall (x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) F' fc' m md (pre : list cell),
ser_memx (usp + -160) (pre ++ savedR) m md -> cells_size pre = 56%nat ->
fsaved F F' -> frm0 fc' ->
realizes rsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (usp + -160)) gp (Z_to_bv 64 TP) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F' (Z_to_bv 64 0x25024) fc' None m (seg_rom rsegs)) md) T.
Proof.
intros until pre. intros INV Hpre FS' FR'.
pose proof facts as (SPR & INp & FL32 & FL16 & FL8 & Rfl & KD & LOS' & _).
destruct (factsM _ _ _ _ INV) as (MI & MOK & _).
destruct INV as (A & buf & cap & bpos & content & errv & HP & PB & FRc & ERR & ST & HPR & VM). unfold ERRNO in ERR. unfold TP.
pose proof FRc as FRj.
apply (proj1 (rw_cells_app rsegs _ _ _ _)) in FRc as [FRp FRs]. rewrite Hpre in FRs. change (Z.of_nat 56) with 56 in FRs.
replace (usp + -160 + 56) with (usp + -104) in FRs by lia. unfold savedR in FRs. unfold usp in *. unfold_consts.
apply rz_evt; [exact MOK|].
symb_run 24%nat (@nil Z) (@nil bool).
step.
apply evt_RZ_done. apply K. unfold ser_post.
exists m, A. eexists. exists errv, buf, cap, bpos, content.
split; [| split; [exact VM | split; [| split; [exact HPR | split; [exact ERR | split; [exact HP | exact PB]]]]]].
- replace (Z_to_bv 64 (bv_unsigned sp + -160 + 160)) with sp by (apply bv_eq; rewrite unsigned_lit by lia; lia).
unfold TP. apply ret_statew_intro; [exact FS' | intros _; exact FR'].
- pose proof (stk_release rsegs _ _ _ _ ST FRj ltac:(lia)) as ST'.
rewrite cells_size_app, Hpre in ST'. cbn [cells_size csize Nat.add savedR length] in ST'.
replace (bv_unsigned sp + -160 + Z.of_nat 160) with (bv_unsigned sp) in ST' by lia. exact ST'.
Qed.

Definition st_head (pc ii : Z) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m : word -> option byte) : machine_state :=
MS (mkR x1 (Z_to_bv 64 (usp + -160)) gp (Z_to_bv 64 TP) t0 t1 t2 (Z_to_bv 64 pb) (Z_to_bv 64 0) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 fl) (Z_to_bv 64 p) (Z_to_bv 64 (lv + 1)) (Z_to_bv 64 0) (Z_to_bv 64 ii) (Z_to_bv 64 0x1120c) (Z_to_bv 64 f1)
(Z_to_bv 64 0x10eb1) (Z_to_bv 64 f2) (Z_to_bv 64 0x122e0) t3 t4 t5 t6) F' (Z_to_bv 64 pc) fc' None m (seg_rom rsegs).
Definition loopK (bound : Z) : Prop :=
forall ii x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m md,
ser_memx (usp + -160) arrFR m md -> fsaved F F' -> frm0 fc' -> 1 <= ii < LEN -> LEN - ii <= bound ->
realizes rsegs (mkCfg (st_head 0x25120 ii x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m) md) T.

Ltac open_frame FRc FR0 FRs :=
unfold arrFR in FRc;
apply (proj1 (rw_cells_app rsegs _ _ _ _)) in FRc as [FR0 FRs]; cbn [cells_size csize Nat.add] in FRs; change (Z.of_nat 56) with 56 in FRs;
replace (bv_unsigned sp + -160 + 56) with (bv_unsigned sp + -104) in FRs by lia; unfold savedR in FRs.

#[using="MEMMOVE fc rc pb0 a ABS KBS kids LBS FL Hlv Hlvd LO LOS SPA HT RA INCL NODE0 AL0 KOK K Hf1 Hf2"] Lemma arr_a94 :
forall ii x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m md,
ser_memx (usp + -160) arrFR m md -> fsaved F F' -> frm0 fc' -> 0 <= ii < LEN -> loopK (LEN - ii - 1) ->
realizes rsegs (mkCfg (st_head 0x25110 ii x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m) md) T.
Proof.
intros until md. intros INV FS' FR' Hii IH.
pose proof facts as (SPR & INp & FL32 & FL16 & FL8 & Rfl & KD & LOS' & LENk & LKBS & LEN32).
destruct (factsM _ _ _ _ INV) as (MI & MOK & Hplo & Hphi & Hpal & NODE & AL & KF).
pose proof INV as INV'. destruct INV as (A & buf & cap & bpos & content & errv & HP & PB & FRc & ERR & ST & HPR & VM). unfold ERRNO in ERR.
open_frame FRc FR0 FRs.
unfold st_head, TP. unfold usp in *. unfold_consts. unfold jhdr_cells in NODE. cbn [app] in NODE.
assert (Rii : 0 <= ii < 2^62) by lia. assert (Rlen : 0 <= LEN < 2^62) by (unfold LEN; lia).
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
apply rz_evt; [exact MOK|].
symb_run 8%nat [array_list_length_entry] (@nil bool).
call (array_list_length_spec _ _ _ _ _ _ _ _ _ (Z_to_bv 64 a)); [exact MI | exact AL | eapply abs_ok; exact INV' | reflexivity |].
fold LEN.
destruct (Z.lt_ge_cases (ii + 1) LEN) as [LT|GE].
-
symb_run 4%nat [0x25120]%Z [false].
apply evt_RZ_done. apply IH; [| exact FS' | exact FR' | lia | lia].
eapply (ser_mem_pure HIx); [exact INV' | exact MU | exact WM | assumption].
- symb_run 4%nat [0x25200]%Z [true].
apply evt_RZ_done. eapply arr_exit with (mid := [C8 (Z_to_bv 64 0x127bc); C8 (Z_to_bv 64 0x13204); C8 (Z_to_bv 64 0x105a2); C8 (Z_to_bv 64 (2 * lv + 2)); C8 (Z_to_bv 64 (lv + 1073741825))]);
[ eapply (ser_mem_pure HIx); [exact INV' | exact MU | exact WM | assumption] | reflexivity | exact FS' | exact FR' ].
Qed.

#[using="MEMMOVE fc rc pb0 a ABS KBS kids KIDS LBS FL Hlv Hlvd LO LOS SPA HT RA INCL NODE0 AL0 KOK K Hf1 Hf2"] Lemma arr_b08 :
forall ii x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m md,
ser_memx (usp + -160) arrFR m md -> fsaved F F' -> frm0 fc' -> 0 <= ii < LEN -> loopK (LEN - ii - 1) ->
realizes rsegs (mkCfg (st_head 0x2519c ii x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m) md) T.
Proof.
intros until md. intros INV FS' FR' Hii IH.
pose proof facts as (SPR & INp & FL32 & FL16 & FL8 & Rfl & KD & LOS' & LENk & LKBS & LEN32).
destruct (factsM _ _ _ _ INV) as (MI & MOK & Hplo & Hphi & Hpal & NODE & AL & _).
pose proof INV as INV'. destruct INV as (A & buf & cap & bpos & content & errv & HP & PB & FRc & ERR & ST & HPR & VM). unfold ERRNO in ERR.
open_frame FRc FR0 FRs.
unfold st_head, TP. unfold usp in *. unfold_consts. unfold jhdr_cells in NODE. cbn [app] in NODE.
assert (Rii : 0 <= ii < 2^62) by lia. assert (Rlen : 0 <= LEN < 2^62) by (unfold LEN; lia).
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.

destruct (nth_error kids (Z.to_nat ii)) as [k|] eqn:Hk.
2:{ exfalso. apply nth_error_None in Hk. unfold LEN in *. lia. }
destruct (kids_okp_nth _ _ _ _ _ _ _ KOK Hk) as (v & bs & Hv & Hbs & KD').
pose proof (al_nth_in ps ii ltac:(unfold LEN in *; lia)) as Hv'. rewrite Hv in Hv'. injection Hv' as Ev.
apply rz_evt; [exact MOK|].
symb_run 8%nat [array_list_get_idx_entry] (@nil bool).
call (array_list_get_idx_spec _ _ _ _ _ _ _ _ _ (Z_to_bv 64 a) (Z_to_bv 64 ii)); [exact MI | exact AL | eapply abs_ok; exact INV' | reflexivity | reflexivity | lia |].
replace (ii <? Z.of_nat (length ps)) with true by (symmetry; apply Z.ltb_lt; unfold LEN in *; lia). rewrite <- Ev.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv rsegs m1 |- _ => rename H into MI1 end.
assert (INV1 : ser_memx (bv_unsigned sp + -160) arrFR m1 md) by (eapply (ser_mem_pure HIx); [exact INV' | exact MU | exact WM | exact MI1]).
destruct k as [s'|].
-
destruct KD' as [Hv0 _].
destruct (factsM _ _ _ _ INV1) as (_ & _ & _ & _ & _ & _ & _ & KF).
destruct (KF (Z.to_nat ii) s' v bs Hk Hv Hbs) as (J & IB & Hvlo & Hvhi & Hval & Hsd).
destruct (proj1 (jval_split rsegs S4F s' m1 bs v 1) J) as (pbc & PBSc & RESTc & Ebs & OPB & JN).
destruct (jnode_hdr rsegs S4F _ _ _ _ _ _ JN) as (n & ty & udel & ud & cs & rest & ER & Hn & HDR).
rewrite (fn_of_S4F s') in HDR. apply (proj1 (rw_cells_app rsegs _ _ _ _)) in HDR as [HDR _].
pose proof (fn_of_range s') as FR_. pose proof (fn_of_even s') as FE_.
unfold_consts. assert (Rv : 1 <= v < 140737488355328) by lia.
symb_run 12%nat (@nil Z) [false].
2:{ sc_cbn. apply brne_and_zero; [lia | lia | apply land7_of_mod16; exact Hval]. }
step. replace (ret_pc (Z_to_bv 64 (fn_of s'))) with (Z_to_bv 64 (fn_of s')) by (symmetry; apply ret_pc_even; [lia | exact FE_]).
fold_mkR. apply evt_RZ_done.
assert (Hin : In (Some s') kids) by (eapply nth_error_In; exact Hk).
pose proof (sdepth_arr kids) as SDA.
eapply (ser_child HIx sp gp m0 md0 LB pb lo LO HT _ _ (KIDS s' Hin)) with (F := F) (RESTc := RESTc) (rc' := 1) (pbc := pbc);
[ exact INV1 | exact JN | intros b Hb; apply IB; rewrite Ebs; apply in_or_app; left; exact Hb | exact LBS | exact FL | lia | lia
| unfold ser_budget; lia
| replace (bv_unsigned sp + -160) with (bv_unsigned sp - 16 * 10) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS' | exact FR' | ].
clear dependent m1.
intros m2 md2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 INV2 FS2 FR2.
destruct (factsM _ _ _ _ INV2) as (MI2 & MOK2 & _).
apply rz_evt; [exact MOK2|].
step. if_cases Kge; fold_mkR.
+
apply evt_RZ_done. apply arr_a94; assumption.
+
symb_run 4%nat [0x25024]%Z (@nil bool).
apply evt_RZ_done. eapply arr_fail with (pre := [C8 (Z_to_bv 64 lv); C8 (Z_to_bv 64 0x127bc); C8 (Z_to_bv 64 0x13204); C8 (Z_to_bv 64 0x105a2); C8 (Z_to_bv 64 (2 * lv + 2));
C8 (Z_to_bv 64 (lv + 1073741825)); C8 (Z_to_bv 64 0)]);
[ exact INV2 | reflexivity | exact FS2 | exact FR2 ].
-
destruct KD' as [Ev0 _]. rewrite Ev0.
symb_run 14%nat [MEMAPPEND] (@nil bool).
destruct (ro_src m1 0x10eb1 (map (Z_to_bv 8) [110; 117; 108; 108]) LB 4 (bv_unsigned sp + -160) MI1 ltac:(vm_compute; reflexivity) eq_refl ltac:(lia) ltac:(lia)) as [SBq SBCq].
apply evt_RZ_done.
eapply (ser_append HIx MEMMOVE sp gp m0 md0 LB pb lo LO HT) with (F := F) (sb := map (Z_to_bv 8) [110; 117; 108; 108]);
[ exact INV1 | exact SBq | reflexivity | lia | lia | lia | exact SBCq | left; lia | lia
| replace (bv_unsigned sp + -160) with (bv_unsigned sp - 16 * 10) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS' | exact FR' | ].
clear dependent m1.
intros m2 md2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 INV2 FS2 FR2 _.
apply arr_a94; assumption.
Qed.

Ltac open_inv INV MI MOK FR0 FRs :=
let INVc := fresh "INVc" in
pose proof INV as INVc;
let A_ := fresh "A_" in let buf_ := fresh "buf_" in let cap_ := fresh "cap_" in let bpos_ := fresh "bpos_" in
let content_ := fresh "content_" in let errv_ := fresh "errv_" in let HP_ := fresh "HP_" in let PB_ := fresh "PB_" in
let FRc := fresh "FRc" in let ERR_ := fresh "ERR_" in let ST_ := fresh "ST_" in let HPR_ := fresh "HPR_" in let VM_ := fresh "VM_" in
destruct INVc as (A_ & buf_ & cap_ & bpos_ & content_ & errv_ & HP_ & PB_ & FRc & ERR_ & ST_ & HPR_ & VM_);
pose proof (heap_mem_inv _ _ _ _ _ _ HP_) as MI; cbn [hl_segs S4L] in MI;
pose proof (heap_model_ok _ _ _ _ _ _ HP_) as MOK;
unfold ERRNO in ERR_; clear PB_ HPR_ VM_;
open_frame FRc FR0 FRs.

#[using="MEMMOVE fc rc pb0 a ABS KBS kids KIDS LBS FL Hlv Hlvd LO LOS SPA HT RA INCL NODE0 AL0 KOK K Hf1 Hf2"] Lemma arr_iter :
forall ii x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m md,
ser_memx (usp + -160) arrFR m md -> fsaved F F' -> frm0 fc' -> 1 <= ii < LEN -> loopK (LEN - ii - 1) ->
realizes rsegs (mkCfg (st_head 0x25120 ii x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m) md) T.
Proof.
intros until md. intros INV FS' FR' Hii IH.
pose proof facts as (SPR & INp & FL32 & FL16 & FL8 & Rfl & KD & LOS' & LENk & LKBS & LEN32).
pose proof FC1 as C1. pose proof FC2 as C2.
open_inv INV MI MOK FR0 FRs.
unfold st_head, TP. unfold usp in *. unfold_consts.
assert (Rii : 0 <= ii < 2^62) by lia. assert (Rlv : 0 <= lv < 1000) by (pose proof (sdepth_arr kids); lia).
apply rz_evt; [exact MOK|].

symb_run 10%nat [MEMAPPEND] (@nil bool).
destruct (ro_src m 0x1120c [Z_to_bv 8 44] LB 1 (bv_unsigned sp + -160) MI ltac:(vm_compute; reflexivity) eq_refl ltac:(lia) ltac:(lia)) as [SBq SBCq].
apply evt_RZ_done.
eapply (ser_append HIx MEMMOVE sp gp m0 md0 LB pb lo LO HT) with (F := F) (sb := [Z_to_bv 8 44]);
[ exact INV | exact SBq | reflexivity | lia | lia | lia | exact SBCq | left; lia | lia
| replace (bv_unsigned sp + -160) with (bv_unsigned sp - 16 * 10) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS' | exact FR' | ].
clear dependent m. intros m1 md1 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F1 fc1 INV1 FS1 FR1 _.
open_inv INV1 MI1 MOK1 FR0' FRs'.
apply rz_evt; [exact MOK1|].
destruct C2 as [E2|E2].
- destruct C1 as [E1|E1].
+
symb_run 40%nat [0x2519c]%Z [false; true].
apply evt_RZ_done. apply arr_b08; [exact INV1 | exact FS1 | exact FR1 | lia | exact IH].
+
symb_run 40%nat [MEMAPPEND; 0x2519c]%Z [false; false].
destruct (ro_src m1 0x105a2 [Z_to_bv 8 32] LB 1 (bv_unsigned sp + -160) MI1 ltac:(vm_compute; reflexivity) eq_refl ltac:(lia) ltac:(lia)) as [SBr SBCr].
apply evt_RZ_done.
eapply (ser_append HIx MEMMOVE sp gp m0 md0 LB pb lo LO HT) with (F := F) (sb := [Z_to_bv 8 32]);
[ exact INV1 | exact SBr | reflexivity | lia | lia | lia | exact SBCr | left; lia | lia
| replace (bv_unsigned sp + -160) with (bv_unsigned sp - 16 * 10) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS1 | exact FR1 | ].
clear dependent m1. intros m2 md2 t0_ t1_ t2_ a0_ a1_ a2_ a3_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ F2 fc2 INV2 FS2 FR2 _.
open_inv INV2 MI2 MOK2 FR0'' FRs''.
apply rz_evt; [exact MOK2|].
symb_run 40%nat [0x2519c]%Z (@nil bool).
apply evt_RZ_done. apply arr_b08; [exact INV2 | exact FS2 | exact FR2 | lia | exact IH].
-
symb_run 40%nat [MEMAPPEND] [true].
destruct (ro_src m1 0x122e0 [Z_to_bv 8 10] LB 1 (bv_unsigned sp + -160) MI1 ltac:(vm_compute; reflexivity) eq_refl ltac:(lia) ltac:(lia)) as [SBr SBCr].
apply evt_RZ_done.
eapply (ser_append HIx MEMMOVE sp gp m0 md0 LB pb lo LO HT) with (F := F) (sb := [Z_to_bv 8 10]);
[ exact INV1 | exact SBr | reflexivity | lia | lia | lia | exact SBCr | left; lia | lia
| replace (bv_unsigned sp + -160) with (bv_unsigned sp - 16 * 10) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS1 | exact FR1 | ].
clear dependent m1. intros m2 md2 t0_ t1_ t2_ a0_ a1_ a2_ a3_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ F2 fc2 INV2 FS2 FR2 _.
open_inv INV2 MI2 MOK2 FR0'' FRs''.
apply rz_evt; [exact MOK2|].
symb_run 40%nat [PBMEMSET] (@nil bool). rewrite ?slliw1_small by lia.
apply evt_RZ_done.
eapply (ser_memset HIx sp gp m0 md0 LB pb lo LO HT) with (F := F);
[ exact INV2 | lia | lia
| replace (bv_unsigned sp + -160) with (bv_unsigned sp - 16 * 10) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS2 | exact FR2 | ].
clear dependent m2. intros m3 md3 t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F3 fc3 INV3 FS3 FR3.
apply arr_b08; [exact INV3 | exact FS3 | exact FR3 | lia | exact IH].
Qed.

#[using="MEMMOVE fc rc pb0 a ABS KBS kids KIDS LBS FL Hlv Hlvd LO LOS SPA HT RA INCL NODE0 AL0 KOK K Hf1 Hf2"] Lemma arr_loop : forall n, loopK (Z.of_nat n).
Proof.
induction n as [|n IHn]; unfold loopK; intros until md; intros INV FS' FR' Hii Hb.
- exfalso. lia.
- eapply arr_iter; [exact INV | exact FS' | exact FR' | exact Hii |].
unfold loopK in *. intros. eapply IHn; try eassumption. lia.
Qed.
#[using="ra ps LBS LO HT LEN"] Lemma ser_mem_frame : forall FA FR FR' m md x,
ser_memx FA FR m md -> munch [(FA, FA + Z.of_nat (cells_size FR))] m x -> wmono rsegs m x -> mem_inv rsegs x ->
rw_cells rsegs x FA FR' -> lo <= FA -> FA + Z.of_nat (cells_size FR) <= usp ->
ser_memx FA FR' x md.
Proof.
intros FA FR FR' m md x (A & buf & cap & bpos & content & errv & HP & PB & FRc & ERR & ST & HPR & VM) MU WM MI FRn Hlo Hhi.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. unfold usp in Hhi, HPR.
pose proof (heap_blk S4L HIx _ _ _ _ pb PB_SZ HP ltac:(left; reflexivity)) as (_ & Hal & Hplo & Hphi & _).
pose proof (heap_blk S4L HIx _ _ _ _ buf cap HP ltac:(right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
pose proof LO as LO'. unfold alloc_ceiling, sp_window_lo, stack_max_size in LO', Hphi, Hbhi.
exists A, buf, cap, bpos, content, errv.
split; [heap_now S4L HIx HP MU WM MI|].
split. { destruct PB as (H1 & H2 & H3 & H4 & H5). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; (eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; rewrite ?Z2Nat.id by lia; lia]). }
split; [exact FRn|].
split; [eapply rw_cells_transport; [exact ERR | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; unfold ERRNO; lia]|].
split; [eapply stk_transport_disjoint; [exact ST | exact MU | exact WM | cbn [disjoint_from]; lia]|].
split; [| exact VM].
eapply heap_pres_trans; [exact HPR|]. eapply (heap_pres_of_munch S4L); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros bb Hbb; right; right; exact Hbb | unfold alloc_ceiling, sp_window_lo, stack_max_size; lia |]. solve_clientW S4L HIx HP.
Qed.
#[using="MEMMOVE fc rc pb0 a ABS KBS kids KIDS LBS FL Hlv Hlvd LO LOS SPA HT RA INCL NODE0 AL0 KOK K Hf1 Hf2"] Lemma arr_a34 :
forall x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 x25 x27 t3 t4 t5 t6 F' fc' m md junk,
ser_memx (usp + -160) ([C8 (Z_to_bv 64 lv); CB 24 junk; C8 (Z_to_bv 64 (2 * lv + 2)); C8 (Z_to_bv 64 (lv + 1073741825)); C8 (Z_to_bv 64 0)] ++ savedR) m md ->
fsaved F F' -> frm0 fc' -> 0 < LEN ->
realizes rsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (usp + -160)) gp (Z_to_bv 64 TP) t0 t1 t2 (Z_to_bv 64 pb) (Z_to_bv 64 0) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 fl) (Z_to_bv 64 p) (Z_to_bv 64 (lv + 1)) (Z_to_bv 64 0) (Z_to_bv 64 lv) x23 (Z_to_bv 64 f1) x25 (Z_to_bv 64 f2) x27 t3 t4 t5 t6)
F' (Z_to_bv 64 0x250b0) fc' None m (seg_rom rsegs)) md) T.
Proof.
intros until junk. intros INV FS' FR' LEN0.
pose proof facts as (SPR & INp & FL32 & FL16 & FL8 & Rfl & KD & LOS' & LENk & LKBS & LEN32).
destruct (factsM _ _ _ _ INV) as (MI & MOK & Hplo & Hphi & Hpal & NODE & AL & _).
pose proof INV as INV'. destruct INV as (A & buf & cap & bpos & content & errv & HP & PB & FRc & ERR & ST & HPR & VM). unfold ERRNO in ERR.
cbn [app] in FRc. unfold savedR in FRc.
unfold TP. unfold usp in *. unfold_consts. unfold jhdr_cells in NODE. cbn [app] in NODE.
assert (Rlv : 0 <= lv < 1000) by (pose proof (sdepth_arr kids); lia). assert (Rlen : 0 <= LEN < 2^62) by (unfold LEN; lia).
pose proof (munch_refl [(bv_unsigned sp + -160, bv_unsigned sp + -160 + 160)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
apply rz_evt; [exact MOK|].
symb_run 8%nat [array_list_length_entry] (@nil bool).
call (array_list_length_spec _ _ _ _ _ _ _ _ _ (Z_to_bv 64 a)); [exact MI | exact AL | eapply abs_ok; exact INV' | reflexivity |].
fold LEN.
destruct (Z.lt_ge_cases LEN 2) as [LT|GE].
-
symb_run 8%nat [0x25200]%Z [true].
apply evt_RZ_done. eapply arr_exit with (mid := [CB 24 junk; C8 (Z_to_bv 64 (2 * lv + 2)); C8 (Z_to_bv 64 (lv + 1073741825))]);
[ | reflexivity | exact FS' | exact FR' ].
eapply ser_mem_frame; [exact INV' | exact MU | exact WM | assumption | unfold usp; cbn [app]; unfold savedR; assumption | lia | unfold usp; cbn; lia].
- symb_run 30%nat [0x25120]%Z [false].
apply evt_RZ_done.
pose proof (arr_loop (length ps)) as LK. unfold loopK in LK. fold LEN in LK.
eapply (LK 1); [ | exact FS' | exact FR' | lia | lia].
eapply ser_mem_frame; [exact INV' | exact MU | exact WM | assumption | unfold usp, arrFR; cbn [app]; unfold savedR; exact FRc | lia | unfold usp; cbn; lia].
Qed.

#[using="MEMMOVE fc rc pb0 a ABS KBS kids KIDS LBS FL Hlv Hlvd LO LOS SPA HT RA INCL NODE0 AL0 KOK K Hf1 Hf2"] Lemma arr_978 :
forall x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 x23 x25 x27 t3 t4 t5 t6 F' fc' m md junk,
ser_memx (usp + -160) ([C8 (Z_to_bv 64 lv); CB 24 junk; C8 (Z_to_bv 64 (2 * lv + 2)); C8 (Z_to_bv 64 (lv + 1073741825)); C8 (Z_to_bv 64 0)] ++ savedR) m md ->
fsaved F F' -> frm0 fc' -> 0 < LEN ->
realizes rsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (usp + -160)) gp (Z_to_bv 64 TP) t0 t1 t2 (Z_to_bv 64 pb) (Z_to_bv 64 0) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 fl) (Z_to_bv 64 p) (Z_to_bv 64 (lv + 1)) x21 (Z_to_bv 64 lv) x23 (Z_to_bv 64 f1) x25 (Z_to_bv 64 f2) x27 t3 t4 t5 t6)
F' (Z_to_bv 64 0x24ff0) fc' None m (seg_rom rsegs)) md) T.
Proof.
intros until junk. intros INV FS' FR' LEN0.
pose proof facts as (SPR & INp & FL32 & FL16 & FL8 & Rfl & KD & LOS' & LENk & LKBS & LEN32).
destruct (factsM _ _ _ _ INV) as (MI & MOK & Hplo & Hphi & Hpal & NODE & AL & _).
pose proof INV as INV'. destruct INV as (A & buf & cap & bpos & content & errv & HP & PB & FRc & ERR & ST & HPR & VM). unfold ERRNO in ERR.
cbn [app] in FRc. unfold savedR in FRc.
unfold TP. unfold usp in *. unfold_consts. unfold jhdr_cells in NODE. cbn [app] in NODE.
assert (Rlv : 0 <= lv < 1000) by (pose proof (sdepth_arr kids); lia). assert (Rlen : 0 <= LEN < 2^62) by (unfold LEN; lia).
assert (Rfl64 : 0 <= fl < 2^64) by lia.
pose proof (munch_refl [(bv_unsigned sp + -160, bv_unsigned sp + -160 + 160)] m) as MU. pose proof (wmono_refl rsegs m) as WM.

destruct kids as [|k kids'] eqn:Ekids; [exfalso; rewrite LENk in LEN0; cbn in LEN0; lia|].
assert (Hk : nth_error kids 0 = Some k) by (rewrite Ekids; reflexivity). rewrite <- Ekids in *. clear Ekids kids'.
destruct (kids_okp_nth _ _ _ _ _ _ _ KOK Hk) as (v & bs & Hv & Hbs & KD').
pose proof (al_nth_in ps 0 ltac:(unfold LEN in *; lia)) as Hv'. change (Z.to_nat 0) with 0%nat in Hv'. rewrite Hv in Hv'. injection Hv' as Ev.
apply rz_evt; [exact MOK|].
symb_run 30%nat [array_list_get_idx_entry] (@nil bool).
rewrite ?FL32.
call (array_list_get_idx_spec _ _ _ _ _ _ _ _ _ (Z_to_bv 64 a) (Z_to_bv 64 0)); [exact MI | exact AL | eapply abs_ok; exact INV' | reflexivity | reflexivity | lia |].
replace (0 <? Z.of_nat (length ps)) with true by (symmetry; apply Z.ltb_lt; unfold LEN in *; lia). rewrite <- Ev.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv rsegs m1 |- _ => rename H into MI1 end.
destruct k as [s'|].
-
destruct KD' as [Hv0 _].
assert (INVp : ser_memx (bv_unsigned sp + -160) ([C8 (Z_to_bv 64 lv); CB 24 junk; C8 (Z_to_bv 64 (2 * lv + 2)); C8 (Z_to_bv 64 (lv + 1073741825)); C8 (Z_to_bv 64 0)] ++ savedR) m1 md)
by (eapply ser_mem_frame; [exact INV' | exact MU | exact WM | exact MI1 | cbn [app]; unfold savedR; exact FRc | lia | cbn; lia]).
destruct (factsM _ _ _ _ INVp) as (_ & _ & _ & _ & _ & _ & _ & KF).
destruct (KF 0%nat s' v bs Hk Hv Hbs) as (J & IB & Hvlo & Hvhi & Hval & Hsd).
destruct (proj1 (jval_split rsegs S4F s' m1 bs v 1) J) as (pbc & PBSc & RESTc & Ebs & OPB & JN).
destruct (jnode_hdr rsegs S4F _ _ _ _ _ _ JN) as (n & ty & udel & ud & cs & rest & ER & Hn & HDR).
rewrite (fn_of_S4F s') in HDR. apply (proj1 (rw_cells_app rsegs _ _ _ _)) in HDR as [HDR _].
pose proof (fn_of_range s') as FR_. pose proof (fn_of_even s') as FE_.
unfold_consts. assert (Rv : 1 <= v < 140737488355328) by lia.
pose proof (munch_refl [(bv_unsigned sp + -160, bv_unsigned sp + -160 + 160)] m1) as MU1. pose proof (wmono_refl rsegs m1) as WM1.
clear MU WM.
symb_run 12%nat (@nil Z) [false].
2:{ sc_cbn. apply brne_and_zero; [lia | lia | apply land7_of_mod16; exact Hval]. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
match goal with H : mem_inv rsegs m2 |- _ => rename H into MI2 end.
assert (INV2 : ser_memx (bv_unsigned sp + -160) ([C8 (Z_to_bv 64 lv); CB 24 junk; C8 (Z_to_bv 64 (2 * lv + 2)); C8 (Z_to_bv 64 (lv + 1073741825)); C8 (Z_to_bv 64 0)] ++ savedR) m2 md)
by (eapply ser_mem_frame; [exact INVp | exact MU1 | exact WM1 | exact MI2 | cbn [app]; unfold savedR; exact FRc | lia | cbn; lia]).
clear J PBSc RESTc Ebs OPB JN rest ER HDR IB.
destruct (factsM _ _ _ _ INV2) as (_ & _ & _ & _ & _ & _ & _ & KF2).
destruct (KF2 0%nat s' v bs Hk Hv Hbs) as (J & IB & _).
destruct (proj1 (jval_split rsegs S4F s' m2 bs v 1) J) as (pbc2 & PBSc & RESTc & Ebs & OPB & JN).
step. replace (ret_pc (Z_to_bv 64 (fn_of s'))) with (Z_to_bv 64 (fn_of s')) by (symmetry; apply ret_pc_even; [lia | exact FE_]).
fold_mkR. apply evt_RZ_done.
assert (Hin : In (Some s') kids) by (eapply nth_error_In; exact Hk).
pose proof (sdepth_arr kids) as SDA.
eapply (ser_child HIx sp gp m0 md0 LB pb lo LO HT _ _ (KIDS s' Hin)) with (F := F) (RESTc := RESTc) (rc' := 1) (pbc := pbc2);
[ exact INV2 | exact JN | intros b Hb; apply IB; rewrite Ebs; apply in_or_app; left; exact Hb | exact LBS | exact FL | lia | lia
| unfold ser_budget; lia
| replace (bv_unsigned sp + -160) with (bv_unsigned sp - 16 * 10) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS' | exact FR' | ].
try clear dependent m1. clear dependent m2.
intros m3 md3 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F3 fc3 INV3 FS3 FR3.
destruct (factsM _ _ _ _ INV3) as (MI3 & MOK3 & _).
apply rz_evt; [exact MOK3|].
step. if_cases Kge; fold_mkR.
+ apply evt_RZ_done. eapply arr_a34; [exact INV3 | exact FS3 | exact FR3 | lia].
+ apply evt_RZ_done. eapply arr_fail with (pre := [C8 (Z_to_bv 64 lv); CB 24 junk; C8 (Z_to_bv 64 (2 * lv + 2)); C8 (Z_to_bv 64 (lv + 1073741825)); C8 (Z_to_bv 64 0)]);
[ exact INV3 | reflexivity | exact FS3 | exact FR3 ].
-
destruct KD' as [Ev0 _]. rewrite Ev0.
symb_run 14%nat [MEMAPPEND] (@nil bool).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
match goal with H : mem_inv rsegs m2 |- _ => rename H into MI2 end.
assert (INV2 : ser_memx (bv_unsigned sp + -160) ([C8 (Z_to_bv 64 lv); CB 24 junk; C8 (Z_to_bv 64 (2 * lv + 2)); C8 (Z_to_bv 64 (lv + 1073741825)); C8 (Z_to_bv 64 0)] ++ savedR) m2 md)
by (eapply ser_mem_frame; [exact INV' | exact MU | exact WM | exact MI2 | cbn [app]; unfold savedR; exact FRc | lia | cbn; lia]).
destruct (ro_src m2 0x10eb1 (map (Z_to_bv 8) [110; 117; 108; 108]) LB 4 (bv_unsigned sp + -160) MI2 ltac:(vm_compute; reflexivity) eq_refl ltac:(lia) ltac:(lia)) as [SBq SBCq].
apply evt_RZ_done.
eapply (ser_append HIx MEMMOVE sp gp m0 md0 LB pb lo LO HT) with (F := F) (sb := map (Z_to_bv 8) [110; 117; 108; 108]);
[ exact INV2 | exact SBq | reflexivity | lia | lia | lia | exact SBCq | left; lia | lia
| replace (bv_unsigned sp + -160) with (bv_unsigned sp - 16 * 10) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS' | exact FR' | ].
clear dependent m2.
intros m3 md3 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F3 fc3 INV3 FS3 FR3 _.
eapply arr_a34; [exact INV3 | exact FS3 | exact FR3 | lia].
Qed.

#[using="MEMMOVE rc pb0 a ABS ps KBS kids KIDS LBS FL Hlv Hlvd LO LOS SPA HT RA FRM INCL NODE0 AL0 KOK K f1 f2 Hf1 Hf2 LEN"] Lemma arr_entry :
forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) m md A buf cap bpos content errv,
HEAPx A ((pb, PB_SZ) :: (buf, cap) :: LB) m md ->
pbuf_core rsegs m pb buf bpos cap content ->
stk rsegs m lo usp ->
rw_cells rsegs m ERRNO [C4 errv] ->
heap_pres S4L LB usp m0 m -> model_vm_only md0 md ->
realizes rsegs (mkCfg (MS (mkR ra sp gp (Z_to_bv 64 TP) t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 pb) (Z_to_bv 64 lv) (Z_to_bv 64 fl) a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 SER_ARR) fc None m (seg_rom rsegs)) md) T.
Proof.
intros until errv. intros HP PB ST ERR HPR0 VM0.
pose proof facts as (SPR & INp & FL32 & FL16 & FL8 & Rfl & KD & LOS' & LENk & LKBS & LEN32).
pose proof FC1 as C1. pose proof FC2 as C2.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
assert (INp' : In (p, 48) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; exact INp).
pose proof (heap_blk S4L HIx _ _ _ _ p 48 HP INp') as (_ & Hpal & Hplo & Hphi & _).
pose proof (heap_blk S4L HIx _ _ _ _ pb PB_SZ HP ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heap_blk S4L HIx _ _ _ _ buf cap HP ltac:(right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
assert (NODE : rw_cells rsegs m p (jhdr_cells JT_ARRAY rc (fn_arr_to_json_string S4F) pb0 0 0 ++ [C8 (Z_to_bv 64 a)])).
{ eapply (heap_pres_rw_cells S4L); [exact HPR0 | exact NODE0 |]. right; right. exists (p, 48). split; [exact INp | cbn; lia]. }
unfold jhdr_cells in NODE. cbn [app] in NODE.
unfold TP, ERRNO in *. unfold usp in *. unfold_consts.
assert (Rlv : 0 <= lv < 1000) by (pose proof (sdepth_arr kids); lia). assert (Rfl64 : 0 <= fl < 2^64) by lia.
assert (Rlen : 0 <= LEN < 2^62) by (unfold LEN; lia).
destruct PB as (Hbp & Hcap & Hln & PBS & PBUF).
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
apply rz_evt; [exact MOK|].
carve_frame 160%nat ST.
symb_run 30%nat [MEMAPPEND] (@nil bool).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv rsegs m1 |- _ => rename H into MI1 end.
assert (HP1 : HEAPx A ((pb, PB_SZ) :: (buf, cap) :: LB) m1 md) by (heap_now S4L HIx HP MU WM MI1).
assert (HPR1 : heap_pres S4L LB (bv_unsigned sp) m0 m1).
{ eapply heap_pres_trans; [exact HPR0|].
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros bb Hbb; right; right; exact Hbb | unfold_consts; lia |].
solve_clientW S4L HIx HP. }
lazymatch type of FR with rw_cells _ _ _ ?cs => assert (INV1 : ser_memx (bv_unsigned sp + -160) cs m1 md) end.
{ exists A, buf, cap, bpos, content, errv.
split; [exact HP1|]. split; [split; [lia|]; split; [lia|]; split; [exact Hln|]; split; [exact PBS|exact PBUF]|].
split; [exact FR|]. split; [exact ERR|]. split; [exact ST|]. split; [exact HPR1 | exact VM0]. }
clear HP1 HPR1 MU WM.
destruct (ro_src m1 0x1120e [Z_to_bv 8 91] LB 1 (bv_unsigned sp + -160) MI1 ltac:(vm_compute; reflexivity) eq_refl ltac:(lia) ltac:(lia)) as [SBq SBCq].
apply evt_RZ_done.
eapply (ser_append HIx MEMMOVE sp gp m0 md0 LB pb lo LO HT) with (F := F) (sb := [Z_to_bv 8 91]);
[ exact INV1 | exact SBq | reflexivity | lia | lia | lia | exact SBCq | left; lia | lia
| replace (bv_unsigned sp + -160) with (bv_unsigned sp - 16 * 10) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | apply fsaved_refl | exact FRM | ].
clear dependent m1.
intros m2 md2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 INV2 FS2 FR2 _.
destruct (factsM _ _ _ _ INV2) as (MI2 & MOK2 & _ & _ & _ & NODE2 & AL2 & _).
pose proof INV2 as INV2'. destruct INV2' as (A2 & buf2 & cap2 & bpos2 & content2 & errv2 & HP2 & PB2 & FRc & ERR2 & ST2 & HPR2 & VM2).
unfold jhdr_cells in NODE2. cbn [app] in NODE2.
pose proof (munch_refl [(bv_unsigned sp + -160, bv_unsigned sp + -160 + 160)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
apply rz_evt; [exact MOK2|].
symb_run 20%nat [array_list_length_entry] [false; false].
2:{ sc_cbn. apply brne_and_zero; [lia | lia | apply land7_of_mod16; exact Hpal]. }
call (array_list_length_spec _ _ _ _ _ _ _ _ _ (Z_to_bv 64 a)); [exact MI2 | exact AL2 | eapply abs_ok; exact INV2 | reflexivity |].
fold LEN.
destruct (Z.eq_dec LEN 0) as [L0|L0].
-
rewrite L0. symb_run 8%nat [0x25208]%Z (@nil bool).
apply evt_RZ_done.
eapply arr_close with (pre := [CB 56 _]); [ | reflexivity | exact FS2 | exact FR2 ].
eapply ser_mem_frame; [exact INV2 | exact MU | exact WM | exact MI | exact FRc | lia | cbn; lia].
- symb_run 20%nat (@nil Z) [false].
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
match goal with H : rw_cells rsegs m3 (bv_unsigned sp + -160) _ |- _ => rename H into FRc3 end.
rewrite ?(u64_of_Z (lv + 1)) in FRc3 by lia. rewrite ?(u64_of_Z fl) in FRc3 by lia. rewrite ?(u64_of_Z fl) by lia.
change (1 mod 32) with 1 in FRc3. rewrite (Z.shiftl_mul_pow2 (lv + 1) 1) in FRc3 by lia.
change (2 ^ 1) with 2 in FRc3. rewrite (swrap32_id ((lv + 1) * 2)) in FRc3 by lia.
replace ((lv + 1) * 2) with (2 * lv + 2) in FRc3 by lia.
rewrite ?FL8 in FRc3. rewrite ?FL8, ?Hf1, ?Hf2.
replace (v_slt (Z_to_bv 64 (lv + 1)) (Z_to_bv 64 lv)) with (Z_to_bv 64 0)
by (symmetry; unfold v_slt, c_lts, bv_lts; rewrite !s64_of_Z by lia; destruct (Z.ltb_spec (lv + 1) lv); [lia | reflexivity]).
lazymatch type of FRc3 with rw_cells _ _ _ ?cs => assert (INV3 : ser_memx (bv_unsigned sp + -160) cs m3 md2) end.
{ eapply ser_mem_frame; [exact INV2 | exact MU | exact WM | exact MI | exact FRc3 | lia | cbn; lia]. }
clear MU WM.
destruct C2 as [E2|E2].
+ destruct C1 as [E1|E1].
*
symb_run 20%nat [0x24ff0]%Z [false; true].
apply evt_RZ_done. eapply arr_978; [exact INV3 | exact FS2 | exact FR2 | lia].
*
symb_run 20%nat [MEMAPPEND; 0x24ff0]%Z [false; false].
destruct (ro_src m3 0x105a2 [Z_to_bv 8 32] LB 1 (bv_unsigned sp + -160) MI ltac:(vm_compute; reflexivity) eq_refl ltac:(lia) ltac:(lia)) as [SBr SBCr].
apply evt_RZ_done.
eapply (ser_append HIx MEMMOVE sp gp m0 md0 LB pb lo LO HT) with (F := F) (sb := [Z_to_bv 8 32]);
[ exact INV3 | exact SBr | reflexivity | lia | lia | lia | exact SBCr | left; lia | lia
| replace (bv_unsigned sp + -160) with (bv_unsigned sp - 16 * 10) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS2 | exact FR2 | ].
clear dependent m3. intros m4 md4 t0_ t1_ t2_ a0_ a1_ a2_ a3_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ F4 fc4 INV4 FS4 FR4 _.
destruct (factsM _ _ _ _ INV4) as (MI4 & MOK4 & _).
apply rz_evt; [exact MOK4|].
symb_run 30%nat [0x24ff0]%Z (@nil bool).
apply evt_RZ_done. eapply arr_978; [exact INV4 | exact FS4 | exact FR4 | lia].
+
symb_run 20%nat [MEMAPPEND] [true].
destruct (ro_src m3 0x122e0 [Z_to_bv 8 10] LB 1 (bv_unsigned sp + -160) MI ltac:(vm_compute; reflexivity) eq_refl ltac:(lia) ltac:(lia)) as [SBr SBCr].
apply evt_RZ_done.
eapply (ser_append HIx MEMMOVE sp gp m0 md0 LB pb lo LO HT) with (F := F) (sb := [Z_to_bv 8 10]);
[ exact INV3 | exact SBr | reflexivity | lia | lia | lia | exact SBCr | left; lia | lia
| replace (bv_unsigned sp + -160) with (bv_unsigned sp - 16 * 10) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS2 | exact FR2 | ].
clear dependent m3. intros m4 md4 t0_ t1_ t2_ a0_ a1_ a2_ a3_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ F4 fc4 INV4 FS4 FR4 _.
destruct (factsM _ _ _ _ INV4) as (MI4 & MOK4 & _).
pose proof INV4 as INV4'. destruct INV4' as (A4 & buf4 & cap4 & bpos4 & content4 & errv4 & HP4 & PB4 & FRc4 & _).
apply rz_evt; [exact MOK4|].
symb_run 30%nat [PBMEMSET] (@nil bool). rewrite ?slliw1_small by lia.
apply evt_RZ_done.
eapply (ser_memset HIx sp gp m0 md0 LB pb lo LO HT) with (F := F);
[ exact INV4 | lia | lia
| replace (bv_unsigned sp + -160) with (bv_unsigned sp - 16 * 10) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS4 | exact FR4 | ].
clear dependent m4. intros m5 md5 t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F5 fc5 INV5 FS5 FR5.
eapply arr_978; [exact INV5 | exact FS5 | exact FR5 | lia].
Qed.
End Ser.

Section SerArrMain.
Variable HIx : heap_iface S4L.
Hypothesis MEMMOVE : memmove_stmt.
Hypothesis HT63 : hi_top S4L HIx < 2^63.

#[using="MEMMOVE"] Lemma ser_arr : forall kids,
(forall s', In (Some s') kids -> ser_spec HIx (fn_of s') s') ->
ser_spec HIx SER_ARR (Sarr kids).
Proof.
intros kids KIDS. unfold ser_spec. intros until errv. intros HP PB JN INCL LBS FL Hlv Hlvd ST LO LOS SPA HT ERR TP' RA FRM A0 A1 A2 A3 K.
destruct JN as (a & ABS & ps & KBS & EREST & NODE & AL & Lps & LK & KOK).
subst a0 a1 a2 a3 tp. rewrite EREST in INCL.
eapply (arr_entry HIx MEMMOVE) with (f1 := Z.land fl 1) (f2 := Z.land fl 2);
first [ exact KIDS | exact HP | exact PB | exact NODE | exact AL | exact KOK | exact INCL | exact K | eassumption | reflexivity
| apply heap_pres_refl | apply model_vm_only_refl ].
Qed.
End SerArrMain.

End RC__1.
End Mq0.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QsRG.Mq0 Qnhz.Mq0 QsRG QO3A Q7m0 QSpR.Mq4 QuJV QCPB.Mq0 QH7x.
Import QXup.
Import UEQM.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0.
Import UC8c.Mq0.
Import Qsw7 QJjn.
Import UBpZ UT7i Uv6q U7zy UD4E.
Import UzWc.
Import Qio9 QHXC Qfe5 QId5 QBGG.
Import Uuoa.Mq0 ULch.Mq0.
Import Q6q3.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section Ser.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Hypothesis MEMMOVE : memmove_stmt.

#[using="MEMMOVE"] Lemma ser_bool : ser_spec HIx SER_BOOL Sbool.
Proof.
unfold ser_spec. intros until errv. intros HP PB JN INCL LBS FL Hlv Hlvd ST LO LOS SPA HT ERR TP' RA FRM A0 A1 A2 A3 K.
destruct JN as (b & junk & EREST & NODE). unfold jhdr_cells in NODE. cbn [app] in NODE.
subst a0 a1 a2 a3 tp. unfold TP, SER_BOOL, ERRNO in *. unfold ser_budget in LOS. cbn [sdepth Z.mul Z.add] in LOS.
word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
assert (INp : In (p, 48) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; apply INCL; rewrite EREST; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ p 48 HP INp) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heap_blk S4L HIx _ _ _ _ pb PB_SZ HP ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heap_blk S4L HIx _ _ _ _ buf cap HP ltac:(right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
unfold_consts.
destruct FL as [Rfl FL56]. destruct (land56_bits fl FL56) as (FL32 & FL16 & FL8).
assert (Rfl64 : 0 <= fl < 2^64) by lia.
destruct PB as (Hbp & Hcap & Hlen & PBS & PBUF).
pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
apply rz_evt; [exact MOK|].
carve_frame 32%nat ST.
symb_run 17%nat [0x249cc]%Z [true; false; false].
2:{ sc_cbn. apply brne_and_zero; [lia | lia | apply land7_of_mod16; exact Hpal]. }
2:{ sc_cbn. apply br_and_zero; [exact Rfl64 | lia | exact FL32]. }
rewrite FL32.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv rsegs m1 |- _ => rename H into MI1 end.
assert (HP1 : HEAPx A ((pb, PB_SZ) :: (buf, cap) :: LB) m1 md) by (heap_now S4L HIx HP MU WM MI1).
assert (HPR1 : heap_pres S4L LB (bv_unsigned sp) m m1).
{ eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros bb Hbb; right; right; exact Hbb | unfold_consts; lia |].
solve_clientW S4L HIx HP. }
assert (INV1 : ser_mem HIx sp m md LB pb lo (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] m1 md).
{ exists A, buf, cap, bpos, content, errv.
split; [exact HP1|]. split; [split; [lia|]; split; [lia|]; split; [exact Hlen|]; split; [exact PBS|exact PBUF]|].
split; [exact FR|]. split; [exact ERR|]. split; [exact ST|]. split; [exact HPR1 | apply model_vm_only_refl]. }
clear HP1 HPR1 MU WM.

assert (TAILK : forall (lit k : Z) (bs : list byte) (t0_ t1_ t2_ a3_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ : word) mq,
ser_mem HIx sp m md LB pb lo (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] mq md ->
ro_bytes_b rsegs lit bs = true -> Z.of_nat (length bs) = k -> 0 < k < 2^31 -> 0 <= lit -> lit + k < 2^64 ->
evt rsegs (RZ rsegs md T)
(MS (mkR (Z_to_bv 64 0x249f4) (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 490496) t0_ t1_ t2_ (Z_to_bv 64 pb) (Z_to_bv 64 p)
(Z_to_bv 64 pb) (Z_to_bv 64 lit) (Z_to_bv 64 k) a3_ a4_ a5_ a6_ a7_ (Z_to_bv 64 0) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3_ t4_ t5_ t6_)
F (Z_to_bv 64 147876) fc None mq (seg_rom rsegs))).
{ intros lit k bs t0_ t1_ t2_ a3_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ mq INVq RB BL Hk Hl Hlk.
pose proof (ser_mem_mem_inv _ _ _ _ _ _ _ _ _ _ _ INVq) as MIq.
destruct (ro_src mq lit bs LB k (bv_unsigned sp + -32) MIq RB BL Hl ltac:(lia)) as [SB SBC].
apply evt_RZ_done.
eapply (ser_append HIx MEMMOVE sp gp m md LB pb lo LO HT) with (F := F) (sb := bs);
[ exact INVq | exact SB | exact BL | lia | lia | lia | exact SBC | left; lia | lia
| replace (bv_unsigned sp + -32) with (bv_unsigned sp - 16 * 2) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | apply fsaved_refl | exact FRM | ].
intros m2 md2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 INV2 FS2 FR2 _.
pose proof INV2 as INV2'. destruct INV2 as (A2 & buf2 & cap2 & bpos2 & content2 & errv2 & HP2 & PB2 & FR2c & ERR2 & ST2 & HPR2 & VM2).
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI2. cbn [hl_segs S4L] in MI2.
apply rz_evt; [exact MOK2|].
symb_run 12%nat (@nil Z) (@nil bool).
step.
apply evt_RZ_done. apply K. unfold ser_post.
exists m2, A2, a0', errv2, buf2, cap2, bpos2, content2.
split; [| split; [exact VM2 | split; [| split; [exact HPR2 | split; [exact ERR2 | split; [exact HP2 | exact PB2]]]]]].
- replace (Z_to_bv 64 (bv_unsigned sp + -32 + 32)) with sp by (apply bv_eq; rewrite unsigned_lit by lia; lia).
apply ret_statew_intro; [exact FS2 | intros _; exact FR2].
- release_frame FR2c ST2 (bv_unsigned sp). exact ST2. }

step. if_cases Kb; fold_mkR.
-
symb_run 10%nat [MEMAPPEND] (@nil bool).
eapply (TAILK 0x102d0 5 (map (Z_to_bv 8) [102; 97; 108; 115; 101])); [exact INV1 | vm_compute; reflexivity | reflexivity | lia | lia | lia].
-
symb_run 10%nat [MEMAPPEND] (@nil bool).
eapply (TAILK 0x1188f 4 (map (Z_to_bv 8) [116; 114; 117; 101])); [exact INV1 | vm_compute; reflexivity | reflexivity | lia | lia | lia].
Qed.
End Ser.

End RC__1.
End Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QsRG.Mq0 Qnhz.Mq0 QsRG QO3A Q7m0 QSpR.Mq4 QuJV QCPB.Mq0 QH7x.
Import QXup.
Import UEQM.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq.Mq0 Qfw3.Mq2 Qc3B.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0.
Import UC8c.Mq0.
Import Qsw7 QJjn.
Import UBpZ UT7i Uv6q U7zy UD4E.
Import UzWc.
Import Qio9 QHXC Qfe5 QId5 QBGG.
Import Uuoa.Mq0 ULch.Mq0.
Import Q6q3.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section Ser.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Hypothesis MEMMOVE : memmove_stmt.
Hypothesis HT63 : hi_top S4L HIx < 2^63.

#[using="MEMMOVE HT63"] Lemma ser_dbl : ser_spec HIx SER_DBL (Sdouble false).
Proof.
unfold ser_spec. intros until errv. intros HP PB JN INCL LBS FL Hlv Hlvd ST LO LOS SPA HT ERR TP' RA FRM A0 A1 A2 A3 K.
destruct JN as (bits & EREST & SPEC & NODE). unfold jhdr_cells in NODE. cbn [app] in NODE.
subst a0 a1 a2 a3 tp. unfold TP, SER_DBL, ERRNO in *. unfold ser_budget in LOS. cbn [sdepth Z.mul Z.add] in LOS.
word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
assert (INp : In (p, 48) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; apply INCL; rewrite EREST; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ p 48 HP INp) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heap_blk S4L HIx _ _ _ _ pb PB_SZ HP ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heap_blk S4L HIx _ _ _ _ buf cap HP ltac:(right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
unfold_consts.
destruct FL as [Rfl FL56].
destruct PB as (Hbp & Hcap & Hlen & PBS & PBUF).
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
apply rz_evt; [exact MOK|].

symb_run 3%nat [SER_DBLF] (@nil bool).
carve_frame 176%nat ST.
symb_run 12%nat [0x25d8c]%Z [false; false].
2:{ sc_cbn. apply brne_and_zero; [lia | lia | apply land7_of_mod16; exact Hpal]. }
step. fold_mkR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv rsegs m1 |- _ => rename H into MI1 end.

assert (TAILK : forall (k : Z) (pre : list cell) (sb : list byte) (t0_ t1_ t2_ a3_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ : word) F' fc' mq,
ser_mem HIx sp m md LB pb lo (bv_unsigned sp + -176) (pre ++ [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) mq md ->
cells_size pre = 128%nat -> bytes_at rsegs mq (bv_unsigned sp + -176) sb -> Z.of_nat (length sb) = k -> 0 < k < 2^31 ->
fsaved F F' -> frm0 fc' ->
evt rsegs (RZ rsegs md T)
(MS (mkR (Z_to_bv 64 0x25dd8) (Z_to_bv 64 (bv_unsigned sp + -176)) gp (Z_to_bv 64 490496) t0_ t1_ t2_ (Z_to_bv 64 pb) (Z_to_bv 64 k)
(Z_to_bv 64 pb) (Z_to_bv 64 (bv_unsigned sp + -176)) (Z_to_bv 64 k) a3_ a4_ a5_ a6_ a7_ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3_ t4_ t5_ t6_)
F' (Z_to_bv 64 147876) fc' None mq (seg_rom rsegs))).
{ intros k pre sb t0_ t1_ t2_ a3_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ F' fc' mq INVq Hpre SB BL Hk FS' FR'.
clear MU WM PBS PBUF ERR NODE MI1.
apply evt_RZ_done.
eapply (ser_append HIx MEMMOVE sp gp m md LB pb lo LO HT) with (F := F) (sb := sb);
[ exact INVq | exact SB | exact BL | lia | lia | lia | left; left; lia | left; lia | lia
| replace (bv_unsigned sp + -176) with (bv_unsigned sp - 16 * 11) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS' | exact FR' | ].
intros m2 md2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 INV2 FS2 FR2 _.
destruct INV2 as (A2 & buf2 & cap2 & bpos2 & content2 & errv2 & HP2 & PB2 & FR2c & ERR2 & ST2 & HPR2 & VM2).
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI2. cbn [hl_segs S4L] in MI2.

apply (proj1 (rw_cells_app rsegs _ _ _ _)) in FR2c as [FRp FRs]. rewrite Hpre in FRs. change (Z.of_nat 128) with 128 in FRs.
replace (bv_unsigned sp + -176 + 128) with (bv_unsigned sp + -48) in FRs by lia. unfold ERRNO, TP in *.
apply rz_evt; [exact MOK2|].
symb_run 12%nat (@nil Z) (@nil bool).
step.
apply evt_RZ_done. apply K. unfold ser_post.
exists m2, A2. eexists. exists errv2, buf2, cap2, bpos2, content2.
split; [| split; [exact VM2 | split; [| split; [exact HPR2 | split; [exact ERR2 | split; [exact HP2 | exact PB2]]]]]].
- replace (Z_to_bv 64 (bv_unsigned sp + -176 + 176)) with sp by (apply bv_eq; rewrite unsigned_lit by lia; lia).
apply ret_statew_intro; [exact FS2 | intros _; exact FR2].
- assert (FRj : rw_cells rsegs m2 (bv_unsigned sp + -176) (pre ++ [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
{ apply (proj2 (rw_cells_app rsegs _ _ _ _)). split; [exact FRp|]. rewrite Hpre. change (Z.of_nat 128) with 128.
replace (bv_unsigned sp + -176 + 128) with (bv_unsigned sp + -48) by lia. exact FRs. }
pose proof (stk_release rsegs _ _ _ _ ST2 FRj ltac:(lia)) as ST2'.
rewrite cells_size_app, Hpre in ST2'. cbn [cells_size csize Nat.add] in ST2'.
replace (bv_unsigned sp + -176 + Z.of_nat 176) with (bv_unsigned sp) in ST2' by lia. exact ST2'. }

assert (MKINV : forall mq FRq, munch [(lo, bv_unsigned sp)] m mq -> wmono rsegs m mq -> mem_inv rsegs mq ->
rw_cells rsegs mq (bv_unsigned sp + -176) FRq ->
rw_cells rsegs mq pb [C8 (Z_to_bv 64 buf); C4 (Z_to_bv 64 bpos); C4 (Z_to_bv 64 cap)] ->
rw_cells rsegs mq buf [CB (Z.to_nat cap) content] ->
rw_cells rsegs mq 490332 [C4 errv] -> stk rsegs mq lo (bv_unsigned sp + -176) ->
ser_mem HIx sp m md LB pb lo (bv_unsigned sp + -176) FRq mq md).
{ intros mq FRq MUq WMq MIq FRc PBSq PBUFq ERRq STq.
assert (HPq : HEAPx A ((pb, PB_SZ) :: (buf, cap) :: LB) mq md) by (heap_now S4L HIx HP MUq WMq MIq).
assert (HPRq : heap_pres S4L LB (bv_unsigned sp) m mq).
{ eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MUq | exact WMq |].
eapply (client_outside S4L HIx); [exact HP | intros bb Hbb; right; right; exact Hbb | unfold_consts; lia |].
solve_clientW S4L HIx HP. }
exists A, buf, cap, bpos, content, errv.
split; [exact HPq|]. split; [split; [lia|]; split; [lia|]; split; [exact Hlen|]; split; [exact PBSq|exact PBUFq]|].
split; [exact FRc|]. split; [exact ERRq|]. split; [exact STq|]. split; [exact HPRq | apply model_vm_only_refl]. }
destruct (Z.eq_dec (bv_unsigned bits mod 2^63) 0x7FF0000000000000) as [INF|NAN].
-
destruct (inf_bits bits INF) as [E|E]; subst bits.
+
symb_run 3%nat [0x25d98]%Z (@nil bool). step. fold_mkR.
symb_run 10%nat [0x25e00]%Z (@nil bool). step. step.
replace (flt_d (Z_to_bv 64 0) (Z_to_bv 64 9218868437227405312)) with true by (vm_compute; reflexivity).
change (bword true) with (Z_to_bv 64 1). fold_mkR.
symb_run 20%nat [MEMAPPEND] (@nil bool).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
match goal with H : mem_inv rsegs m3 |- _ => rename H into MI3 end.
lazymatch type of FR with rw_cells _ _ _ ?cs =>
lazymatch cs with ?c1 :: ?c2 :: ?c3 :: ?rest =>
eapply (TAILK 8 [c1; c2; c3] (firstn 8 (cells_bytes cs)));
[ eapply MKINV; try eassumption | reflexivity | | reflexivity | lia | | ] end end.
* pose proof (rw_cells_bytes_at rsegs m3 _ _ FR) as BY. rewrite <- (firstn_skipn 8 (cells_bytes _)) in BY.
exact (proj1 (proj1 (bytes_at_app rsegs m3 _ _ _) BY)).
* fsaved_tmp.
* assumption.
+
symb_run 3%nat [0x25d98]%Z (@nil bool). step. fold_mkR.
symb_run 10%nat [0x25e00]%Z (@nil bool). step. step.
replace (flt_d (Z_to_bv 64 0) (Z_to_bv 64 18442240474082181120)) with false by (vm_compute; reflexivity).
change (bword false) with (Z_to_bv 64 0). fold_mkR.
symb_run 20%nat [MEMAPPEND] (@nil bool).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
match goal with H : mem_inv rsegs m3 |- _ => rename H into MI3 end.
lazymatch type of FR with rw_cells _ _ _ ?cs =>
lazymatch cs with ?c1 :: ?c2 :: ?c3 :: ?rest =>
eapply (TAILK 9 [c1; c2; c3] (firstn 9 (cells_bytes cs)));
[ eapply MKINV; try eassumption | reflexivity | | reflexivity | lia | | ] end end.
* pose proof (rw_cells_bytes_at rsegs m3 _ _ FR) as BY. rewrite <- (firstn_skipn 9 (cells_bytes _)) in BY.
exact (proj1 (proj1 (bytes_at_app rsegs m3 _ _ _) BY)).
* fsaved_tmp.
* assumption.
-
assert (NANgt : 0x7FF0000000000001 <= bv_unsigned bits mod 2^63) by (unfold dbl_special in SPEC; lia).
symb_run 3%nat [0x25d98]%Z (@nil bool). step. fold_mkR.
symb_run 16%nat [MEMAPPEND] [false].
2:{ sc_cbn. rewrite abs63m_ltu by lia. apply Z.ltb_ge. lia. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
match goal with H : mem_inv rsegs m3 |- _ => rename H into MI3 end.
lazymatch type of FR with rw_cells _ _ _ ?cs =>
lazymatch cs with ?c1 :: ?c2 :: ?rest =>
eapply (TAILK 3 [c1; c2] (firstn 3 (cells_bytes cs)));
[ eapply MKINV; try eassumption | reflexivity | | reflexivity | lia | | ] end end.
+ pose proof (rw_cells_bytes_at rsegs m3 _ _ FR) as BY. rewrite <- (firstn_skipn 3 (cells_bytes _)) in BY.
exact (proj1 (proj1 (bytes_at_app rsegs m3 _ _ _) BY)).
+ fsaved_tmp.
+ assumption.
Qed.
End Ser.

End RC__1.
End Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UgLo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QsRG.Mq0 Qnhz.Mq0 QsRG QO3A Q7m0 QSpR.Mq4 QuJV QCPB.Mq0 QH7x.
Import QXup.
Import UEQM.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0.
Import UC8c.Mq0.
Import Qsw7 QJjn.
Import UBpZ UT7i Uv6q U7zy UD4E.
Import UzWc.
Import UgLo.
Import Qio9 QHXC Qfe5 QId5 QBGG.
Import Uuoa.Mq0 ULch.Mq0.
Import Q6q3.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section Ser.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Hypothesis MEMMOVE : memmove_stmt.

#[using="MEMMOVE"] Lemma ser_ud : ser_spec HIx SER_UD (Sdouble true).
Proof.
unfold ser_spec. intros until errv. intros HP PB JN INCL LBS FL Hlv Hlvd ST LO LOS SPA HT ERR TP' RA FRM A0 A1 A2 A3 K.
destruct JN as (bits & ud & udn & uds & EREST & Hudn & NODE & CSTR). unfold jhdr_cells in NODE. cbn [app] in NODE.
subst a0 a1 a2 a3 tp. unfold TP, SER_UD, ERRNO in *. unfold ser_budget in LOS. cbn [sdepth Z.mul Z.add] in LOS.
word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
assert (INp : In (p, 48) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; apply INCL; rewrite EREST; left; reflexivity).
assert (INudL : In (ud, udn) LB) by (apply INCL; rewrite EREST; right; left; reflexivity).
assert (INud : In (ud, udn) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; exact INudL).
pose proof (heap_blk S4L HIx _ _ _ _ p 48 HP INp) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heap_blk S4L HIx _ _ _ _ ud udn HP INud) as (_ & Hual & Hulo & Huhi & _).
pose proof (heap_blk S4L HIx _ _ _ _ pb PB_SZ HP ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heap_blk S4L HIx _ _ _ _ buf cap HP ltac:(right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
destruct (cstr_slack HIx _ _ _ _ _ _ _ HP INud CSTR) as (slack & SBY & SLK & NONUL).
destruct CSTR as (Hlen1 & _ & _).
remember (uds ++ Z_to_bv 8 0 :: slack) as sfull eqn:Esf.
assert (LENsf : Z.of_nat (length sfull) = Z.of_nat (length uds) + 1 + Z.of_nat (length slack)) by (subst sfull; rewrite length_app; cbn [length]; lia).
assert (LENsb : Z.of_nat (length slack) <= udn - Z.of_nat (length uds) - 1 + 15) by lia.
unfold_consts.
destruct FL as [Rfl FL56].
destruct PB as (Hbp & Hcap & Hlen & PBS & PBUF).
pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
apply rz_evt; [exact MOK|].
carve_frame 32%nat ST.
symb_run 18%nat [STRLEN] [false; false].
2:{ sc_cbn. apply brne_and_zero; [lia | lia | apply land7_of_mod16; exact Hpal]. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv rsegs m1 |- _ => rename H into MI1 end.

subst sfull.
call (strlen_spec _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ud)); [ rewrite unsigned_lit by lia; exact SBY | exact NONUL | rewrite unsigned_lit by lia; clear -SLK; lia | exact MI1 | ].
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
match goal with H : mem_inv rsegs m2 |- _ => rename H into MI2 end.
match goal with H : bytes_at rsegs m2 _ (uds ++ _) |- _ => rename H into SBY2; rewrite unsigned_lit in SBY2 by lia end.
assert (Hlen31 : 0 <= Z.of_nat (length uds) < 2^31) by lia.
symb_run 8%nat [MEMAPPEND] (@nil bool). rewrite ?Z.add_0_r.
assert (HP2 : HEAPx A ((pb, PB_SZ) :: (buf, cap) :: LB) m2 md) by (heap_now S4L HIx HP MU WM MI2).
assert (HPR2 : heap_pres S4L LB (bv_unsigned sp) m m2).
{ eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros bb Hbb; right; right; exact Hbb | unfold_consts; lia |].
solve_clientW S4L HIx HP. }
assert (INV2 : ser_mem HIx sp m md LB pb lo (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] m2 md).
{ exists A, buf, cap, bpos, content, errv.
split; [exact HP2|]. split; [split; [lia|]; split; [lia|]; split; [exact Hlen|]; split; [exact PBS|exact PBUF]|].
split; [exact FR|]. split; [exact ERR|]. split; [exact ST|]. split; [exact HPR2 | apply model_vm_only_refl]. }
clear HP2 HPR2 MU WM.
assert (SB2 : bytes_at rsegs m2 ud uds) by (exact (proj1 (proj1 (bytes_at_app rsegs m2 ud _ _) SBY2))).
apply evt_RZ_done.
eapply (ser_append HIx MEMMOVE sp gp m md LB pb lo LO HT) with (F := F) (sb := uds);
[ exact INV2 | exact SB2 | lia | lia | lia | lia
| left; right; right; exists (ud, udn); split; [exact INudL | cbn; lia]
| right; exists udn; split; [exact INudL | lia]
| lia
| replace (bv_unsigned sp + -32) with (bv_unsigned sp - 16 * 2) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | apply fsaved_refl | exact FRM | ].
intros m3 md3 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F3 fc3 INV3 FS3 FR3 _.
destruct INV3 as (A3 & buf3 & cap3 & bpos3 & content3 & errv3 & HP3 & PB3 & FR3c & ERR3 & ST3 & HPR3 & VM3).
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI3. cbn [hl_segs S4L] in MI3.
apply rz_evt; [exact MOK3|].
symb_run 12%nat (@nil Z) (@nil bool).
step.
apply evt_RZ_done. apply K. unfold ser_post.
exists m3, A3. eexists. exists errv3, buf3, cap3, bpos3, content3.
split; [| split; [exact VM3 | split; [| split; [exact HPR3 | split; [exact ERR3 | split; [exact HP3 | exact PB3]]]]]].
- replace (Z_to_bv 64 (bv_unsigned sp + -32 + 32)) with sp by (apply bv_eq; rewrite unsigned_lit by lia; lia).
apply ret_statew_intro; [exact FS3 | intros _; exact FR3].
- release_frame FR3c ST3 (bv_unsigned sp). exact ST3.
Qed.
End Ser.

End RC__1.
End Mq3.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QO3A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QO3A. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7m0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7m0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QuJV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QuJV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCPB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCPB.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QH7x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QH7x.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UBpZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UBpZ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UT7i.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UT7i. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv6q.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv6q. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UD4E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UD4E.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UzWc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UzWc.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qio9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qio9. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHXC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHXC. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfe5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfe5. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QId5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QId5.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uuoa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uuoa. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require ULch.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import ULch.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section Esc.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Hypothesis MEMMOVE : memmove_stmt.
Hypothesis HEXP : forall A LB m md, HEAPx A LB m md -> bytes_at rsegs m JHEX_SLOT (le8 (wz JHEX)).
Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB : list blk) (pb Sa n lo : Z) (src : list byte).
Let usp := bv_unsigned sp.
Hypothesis SRCL : Z.of_nat (length src) = n.
Hypothesis SCL : src_cls LB n usp Sa src.
Hypothesis Hn : 0 < n < 2^31.
Hypothesis HSa : 0 <= Sa /\ Sa + n < 2^64.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= usp - 192 - 8320.
Hypothesis SPA : usp mod 16 = 0.
Hypothesis HT : usp <= hi_top S4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis FRM : frm0 fc.

Notation esc_memx := (esc_mem HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB pb Sa lo src).
Notation esc_postx := (esc_post HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB pb Sa lo src).

Definition st_loop (pc : Z) (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x27 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
(m : word -> option byte) (pos posb start : Z) : machine_state :=
MS (mkR x1 (Z_to_bv 64 (usp + -144)) gp (wz 0x77c00) t0 t1 t2 (wz pb) (wz n) (wz start) a1 a2 a3 a4 a5 a6 a7
(wz Sa) (wz 0x1299a) (wz (18446744073709551615 - Sa)) (wz posb) (wz pos) (wz 0) (wz 1) (wz 47) (wz 140754668238592) x27 t3 t4 t5 t6)
F' (wz pc) fc' None m (seg_rom rsegs).

Definition loopK (T : TSet) (bound : Z) : Prop :=
forall x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x27 t3 t4 t5 t6 F' fc' m md pos start,
esc_memx m md -> fsaved F F' -> frm0 fc' -> 0 <= start <= pos -> pos < n -> n - pos <= bound ->
realizes rsegs (mkCfg (st_loop 0x27084 x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x27 t3 t4 t5 t6 F' fc' m pos pos start) md) T.

#[using="MEMMOVE SRCL SCL Hn HSa LO LOS SPA HT"] Lemma esc_join98 :
forall x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x27 t3 t4 t5 t6 F' fc' m md pos start' T,
esc_memx m md -> fsaved F F' -> frm0 fc' -> 0 <= pos < n -> 0 <= start' <= pos + 1 ->
loopK T (n - pos - 1) ->
(forall ms' md', esc_postx ms' md' -> realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (st_loop 0x27078 x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x27 t3 t4 t5 t6 F' fc' m pos pos start') md) T.
Proof.
intros until T. intros INV FS FR Hpos Hst IH K.
pose proof INV as INV0.
destruct INV as (A & buf & cap & bpos & content & errv & j1 & j2 & sbf & HP & PB & FRc & SRC & ERR & ST & HPR & VM).
unfold st_loop. pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. unfold usp in *. unfold_consts.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
unfold escF in FRc.
apply rz_evt; [exact MOK|].
destruct (Z.eq_dec (pos + 1) n) as [EQ|NE].
- symb_run 6%nat [0x27298; 0x27084]%Z [true].
apply evt_RZ_done. eapply (esc_exit HIx MEMMOVE); try eassumption. lia.
- symb_run 6%nat [0x27298; 0x27084]%Z [false].
apply evt_RZ_done. eapply IH; try eassumption; lia.
Qed.

#[using="RC__ ra sp Sa n src usp HSa"] Lemma mask_clear : forall c : byte,
32 <= bv_unsigned c <= 47 -> bv_unsigned c <> 34 -> bv_unsigned c <> 47 ->
branch_taken BC_EQ (alu64 ALU_AND (alu64 ALU_SRL (Z_to_bv 64 140754668238592) (Z_to_bv 64 (bv_unsigned c))) (Z_to_bv 64 1))
(Z_to_bv 64 0) = true.
Proof.
intros c Hc H34 H47.
assert (E : bv_unsigned c = 32 \/ bv_unsigned c = 33 \/ bv_unsigned c = 35 \/ bv_unsigned c = 36 \/ bv_unsigned c = 37 \/
bv_unsigned c = 38 \/ bv_unsigned c = 39 \/ bv_unsigned c = 40 \/ bv_unsigned c = 41 \/ bv_unsigned c = 42 \/
bv_unsigned c = 43 \/ bv_unsigned c = 44 \/ bv_unsigned c = 45 \/ bv_unsigned c = 46) by lia.
destruct E as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]]; rewrite E; vm_compute; reflexivity.
Qed.

#[using="Type"] Lemma chk_nz_add : forall a b : Z, 0 <= a -> 0 <= b -> 0 < a + b < 2^64 ->
branch_taken BC_EQ (alu64 ALU_XOR (Z_to_bv 64 1) (alu64 ALU_SLTU (alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b)) (Z_to_bv 64 1)))
(Z_to_bv 64 0) = false.
Proof.
intros a b Ha Hb Hab. clear - Ha Hb Hab.
rewrite QsjA.alu_xor, QsjA.alu_sltu, QsjA.alu_add. unfold QsjA.v_xor, QsjA.v_sltu, QsjA.v_add, QsjA.c_ltu, bv_ltu.
rewrite (unsigned_lit a), (unsigned_lit b) by lia. rewrite (unsigned_lit (a + b)) by lia.
replace (a + b <? bv_unsigned (Z_to_bv 64 1)) with false by (symmetry; apply Z.ltb_ge; rewrite unsigned_lit by lia; lia).
vm_compute. reflexivity.
Qed.

#[using="MEMMOVE SRCL SCL Hn HSa LO LOS SPA HT"] Lemma esc_iter_regular :
forall x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x27 t3 t4 t5 t6 F' fc' m md pos start (c : byte) T,
esc_memx m md -> fsaved F F' -> frm0 fc' -> 0 <= start <= pos -> pos < n ->
nth_error src (Z.to_nat pos) = Some c ->
32 <= bv_unsigned c -> bv_unsigned c <> 34 -> bv_unsigned c <> 92 -> bv_unsigned c <> 47 ->
loopK T (n - pos - 1) ->
(forall ms' md', esc_postx ms' md' -> realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (st_loop 0x27084 x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x27 t3 t4 t5 t6 F' fc' m pos pos start) md) T.
Proof.
intros until T. intros INV FS FR Hst Hpos Hc C32 C34 C92 C47 IH K.
pose proof INV as INV0.
destruct INV as (A & buf & cap & bpos & content & errv & j1 & j2 & sbf & HP & PB & FRc & SRC & ERR & ST & HPR & VM).
pose proof (bv_unsigned_in_range 8 c) as CR. unfold bv_modulus in CR. cbn in CR.
unfold st_loop. pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. unfold usp in *. unfold_consts.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
unfold escF in FRc.
assert (SA0 : 0 < Sa) by (eapply (esc_sa_pos HIx); eassumption).
apply rz_evt; [exact MOK|].
symb_run 8%nat [0x2709c]%Z [false; false; false].
2: { sc_cbn. apply chk_nz_add; lia. }
destruct (Z.lt_ge_cases 47 (bv_unsigned c)) as [HI|LOW].
-
assert (RG : 48 <= bv_unsigned c < 256) by lia.
symb_run 10%nat [0x27078]%Z [false] extra [Z_to_bv 64 (bv_unsigned c)].
apply evt_RZ_done. eapply esc_join98; try eassumption; lia.
-
assert (RG : 32 <= bv_unsigned c < 48) by lia.
symb_run 10%nat [0x27078]%Z [true] extra [Z_to_bv 64 (bv_unsigned c)].
apply evt_RZ_done. eapply esc_join98; try eassumption; try lia.

sc_cbn. apply mask_clear; lia.
Qed.
End Esc.

End RC__1.
