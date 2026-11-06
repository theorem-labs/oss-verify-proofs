(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseReadSound.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseRdKit FseRdKit2.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg ABase RtCells AF_fse_rd_base AF_fse_rd_cnt1 AF_fse_rd_count AF_fse_rd_zero.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKitF.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common.FseWalkKit.simpl_arr_sizes_fwk_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.
Local Ltac acc_hint ::= rdA_acc_hint.
Section CANSEC1. Context {rc : runConstT}.
Definition rd_epiA (C : rdctxA) (m1 : amem) (x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x29 : word) : machine_state :=
MS (mkR x1 (Z_to_bv 64 (a_SPA C)) (a_gp C) (a_tp C)
(Z_to_bv 64 1) x6 x7
(Z_to_bv 64 (a_SP C)) (Z_to_bv 64 (a_SPA C)) x10 x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 (a_BUF C + zlen (a_buf C))) x20 (Z_to_bv 64 (a_NC C)) x22 (Z_to_bv 64 (a_msv0 C + 1))
(Z_to_bv 64 2147450880) (Z_to_bv 64 (a_FF C)) (Z_to_bv 64 (Z.shiftr (a_FF C) 3 + 2147450880)) (Z_to_bv 64 (a_BUF C))
(Z_to_bv 64 18446744071562067968) x29 (Z_to_bv 64 23) (Z_to_bv 64 125613361))
(a_F C) (Z_to_bv 64 0x82548) (a_fc C) None m1 (seg_rom bsegs).
Definition rd_mainA_post (C : rdctxA) (rt : list Z) (msv tl n : Z) : machine_state -> Prop :=
fun ms' => exists m' (x1 x6 x7 x10 x11 x13 x14 x15 x16 x17 x18 x20 x22 x29 : word),
ms' = rd_epiA C m' x1 x6 x7 x10 x11 (Z_to_bv 64 n) x13 x14 x15 x16 x17 x18 x20 x22 x29
/\ rd_invA C m' rt (Z_to_bv 64 msv) (Z_to_bv 64 tl).
Section Loop.
Variable C : rdctxA.
Variable RNG : footprint.
Hypothesis OK : rd_okA C.
Hypothesis SH : rd_shA C.
Hypothesis RNGS : rd_rngA C RNG.
Variable tl : Z.
Hypothesis Htl : 5 <= tl <= 15.
Notation buf := (a_buf C).
Notation msv1 := (a_msv0 C + 1).
Notation BUF := (a_BUF C).
Notation NC := (a_NC C).
Notation MSVP := (a_MSVP C).
Ltac cbnR := cbn [r_nc r_ip r_bitStream r_bitCount r_charnum r_remaining r_threshold r_nbBits r_previous0] in *.
Ltac zify_lts K :=
unfold bv_lts in K; rewrite ?land7_mod in K;
rewrite !signed_lit_small64 in K by (Z.div_mod_to_equations; lia);
zify_bool K.
#[using="rc OK SH RNGS"] Lemma exit_runA : forall s m1 msvw (x1 x6 x7 x12 x18 x20 x22 x29 : word),
rd_invA C m1 (r_nc s) msvw (Z_to_bv 64 tl) -> rd_brk_okA C s ->
r_remaining s = 1 -> 1 <= r_charnum s <= msv1 -> r_bitCount s <= 32 ->
evtF bsegs RNG (rd_mainA_post C (r_nc s) (r_charnum s - 1) tl (r_ip s + (r_bitCount s + 7) / 8))
(rd_exitA C s m1 x1 x6 x7 x12 x18 x20 x22 x29).
Proof.
intros s m1 msvw x1 x6 x7 x12 x18 x20 x22 x29 INV (B1 & B2 & B3 & B4 & B5) Erem Hcn Hbc.
pose proof RNGS as RNGS'. destruct RNGS' as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
pose proof (okA_lin C OK) as (HH & HM0 & HM1 & HRT & SP16 & SPK & LO & LOA & SPA12 & SPA3 & NC0 & NC1 & N8 & MS0 & MS1 & M4
& TL0 & TL1 & T4 & BF0 & BF1 & B8 & FF0 & FF1 & F64).
pose proof atop_range as ATR. unfold RDA_CALLEE, KHIGH, AIMG_HI, KEND in *.
unfold rd_exitA, rd_lstA.
destruct s as [nc ip bs bc cn rem thr nb p0]. cbnR. subst rem.
assert (UM : unpoisoned m1 MSVP (MSVP + 4))
by (destruct INV as (_ & _ & _ & _ & _ & _ & _ & MU & _); apply (inv_shadowA C m1 OK SH MU)).
Local Ltac2 Set LiaHints.tbl := fun () => "00X0?10609739141.80 11556575866.80 12532332107.80 13541292123.92 13541292123.94 14171358514.79 18296467856.79 19628484000.79 22736838437.12724666713561.92 29786284892.79 32982392605.80 33818344436.92 35982969068.80 3712023524.88  3712023529.90  37501951439.91 39159981841.82 40829096255.14642058076465.80 44071106355.79 47375192777.91 50553141824.90 50553141838.90 53538128661.14659308628433.79 59308628566.80 59308693840.80 59310676694.14662179820399.71 63370135212.79 63375992104.88 65857236465.79 65979773735.71 8469969012.80  8929349025.80  8937270825.91  8937270826.90  8943522981.71  9084385950.80  00000400700800B00L00P00T00Y00f01001101201i01l02002402502h02l02o03703j04T05D05M05U05]06L06U06V06W06X06]06^06_07T08I09>09?09BS2B2S1QSS2LO5SPA12S2LO5SPA12S2B2S2B3S3HM0S2M41H2H03H19S2LO5SPA12SSS4SP162LO3LOA5SPA124SPA33NC03MS03MS12M43TL03BF03FF03ATRS1QS2B2S2B2SS4SP162LO3LOA5SPA124SPA33NC03MS03TL03BF03FF03ATR2CKS2SRS1QS2B23HbcS2B22B42B52LO3LOA5SPA123NC03MS03TL03BF03BF13FF03ATRS2LO3LOA5SPA123NC03MS03MS13TL03BF03FF03ATRS2B22HH2LO3LOA5SPA123NC03MS03TL03BF03BF13FF03ATRS2CK1G2H0S3Hcn2K2S3Hbc2K3S2B22B42LO3LOA5SPA123NC03MS03TL03BF03FF03ATR2G1S2CK1G2G'SSSS3HbcSSS2B22B42B52LO3LOA5SPA123NC03MS03TL03BF03BF13FF03ATR1QS2B22B42B52LO3LOA5SPA123NC03MS03TL03BF03BF13FF03ATR1QS2B22B42B52LO3LOA5SPA123NC03MS03TL03BF03BF13FF03ATR1QSS1Q".
destruct (chk1A m1 MSVP (MSVP + 4) MSVP 4 UM ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia))
as (b & RDB & CK & SR). clear UM.
pose proof INV as INV'. destruct INV' as (_ & _ & _ & HMSV & _ & (j0 & j64 & FR) & _). unfold FRA_main, ASHB in FR.
change (2^31) with 2147483648 in *.
zstep. zstep. zstep. zstep. if_false.
zstep. if_cases K2; zify_cond K2; [| exfalso; lia].
zstep. zstep. if_cases K3; zify_cond K3; rewrite ?signed_lit in K3 by lia; [exfalso; lia|].
zstep. rewrite sxb_sval.
pose proof (rw_cells_store_ok bsegs m1 MSVP [C4 msvw] 0 (C4 msvw) 4 HMSV eq_refl eq_refl) as SOK.
cbn [Z.of_nat] in SOK. rewrite Z.add_0_r in SOK. clear HMSV.
assert (JOIN : forall (y11 y12 : word),
evtF bsegs RNG (rd_mainA_post C nc (cn - 1) tl (ip + (bc + 7) / 8))
(MS (mkR x1 (Z_to_bv 64 (a_SPA C)) (a_gp C) (a_tp C) (Z_to_bv 64 1) x6 x7
(Z_to_bv 64 (a_SP C)) (Z_to_bv 64 (a_SPA C)) (Z_to_bv 64 (BUF + ip)) y11 y12 (Z_to_bv 64 cn)
(Z_to_bv 64 1) (Z_to_bv 64 (Z.shiftr MSVP 3 + 2147450880)) (Z_to_bv 64 bc) (Z_to_bv 64 4)
x18 (Z_to_bv 64 (BUF + zlen buf)) x20 (Z_to_bv 64 NC) x22 (Z_to_bv 64 (a_msv0 C + 1))
(Z_to_bv 64 2147450880) (Z_to_bv 64 (a_FF C)) (Z_to_bv 64 (Z.shiftr (a_FF C) 3 + 2147450880)) (Z_to_bv 64 BUF)
(Z_to_bv 64 18446744071562067968) x29 (Z_to_bv 64 23) (Z_to_bv 64 125613361))
(a_F C) (Z_to_bv 64 0x82514) (a_fc C) None m1 (seg_rom bsegs))).
{ intros y11 y12. clear RDB CK SR.
zstep. zstep.
zstep. rewrite ?(FseWalkKit.swrap32_small (bc + 7)) by lia. rewrite (Z.shiftr_div_pow2 (bc + 7) 3) by lia. change (2^3) with 8.
assert (Q : 0 <= (bc + 7) / 8 < 5) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
rewrite ?(FseWalkKit.swrap32_small ((bc + 7) / 8)) by lia.
zstep.
zstep. clear FR.
zstep.
pose proof (rd_invA_storeM C m1 nc msvw (Z_to_bv 64 tl) (cn + -1) OK INV) as INV2.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
change mm with (write_to_mem m1 (wa MSVP) (le4 (Z_to_bv 64 (cn + -1)))) end.
remember (write_to_mem m1 (wa MSVP) (le4 (Z_to_bv 64 (cn + -1)))) as m' eqn:Hm. clear Hm INV SOK.
zstep. if_cases G1; zify_cond G1; [exfalso; lia|].
zstep. replace (BUF + ip + (bc + 7) / 8 <? BUF + ip) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
zstep.
replace (Z.lxor ((bc + 7) / 8) 9223372036854775808 <? 0 + 9223372036854775808) with false
by (symmetry; apply Z.ltb_ge; change 9223372036854775808 with (2^63); rewrite zb_lxor_pow2_small by lia; lia).
cbn [Z.b2z].
zstep. zstep. zstep. if_false.
zstep.
rewrite ?(Z.mod_small (BUF + ip) 18446744073709551616), ?(Z.mod_small BUF 18446744073709551616) by lia.
replace (BUF + ip + (bc + 7) / 8 - BUF) with (ip + (bc + 7) / 8) by lia.
apply evtF_done. unfold rd_mainA_post.
eexists. do 14 eexists. split; [unfold rd_epiA; reflexivity|].
replace (cn - 1) with (cn + -1) by lia. exact INV2. }
zstep. if_cases G; zify_cond G.
- zstep. zstep. zstep. zstep.
if_cases G'; zify_lts G'; [| exfalso; Z.div_mod_to_equations; lia]. apply JOIN.
- apply JOIN.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc OK"] Lemma buf_h8A : 8 <= FseNCount.Zlength buf.
Proof. unfold FseNCount.Zlength. destruct OK as (HH & _). Local Ltac2 Set LiaHints.tbl := fun () => "0010=52018712845.9000004S2HH".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc OK"] Lemma msv1_okA : 1 <= msv1 <= FseNCount.Zlength (a_rt0 C).
Proof. unfold FseNCount.Zlength. destruct OK as (_ & _ & HM0 & HM1 & _). Local Ltac2 Set LiaHints.tbl := fun () => "0010>48770900490.10000009S3HM03HM1".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc OK SH RNGS Htl"] Lemma loop_runA : forall f s sF m1 msvw (x7 x12 x20 x22 x29 : word),
rloop buf msv1 f s = Ok sF ->
rd_invA C m1 (r_nc s) msvw (Z_to_bv 64 tl) -> CTL msv1 (a_rt0 C) tl s -> POS buf s -> r_bitCount s < 32 ->
r_remaining sF = 1 -> r_charnum sF <= msv1 -> r_bitCount sF <= 32 ->
evtF bsegs RNG (rd_mainA_post C (r_nc sF) (r_charnum sF - 1) tl (r_ip sF + (r_bitCount sF + 7) / 8)) (rd_headA C s m1 x7 x12 x20 x22 x29).
Proof.
induction f as [|f IH]; intros s sF m1 msvw x7 x12 x20 x22 x29 RL INV HC HP HB32 F1 F2 F3.
{ cbn in RL. discriminate RL. }
cbn [rloop] in RL.
set (POSTF := rd_mainA_post C (r_nc sF) (r_charnum sF - 1) tl (r_ip sF + (r_bitCount sF + 7) / 8)).
assert (CNT : forall s1 m2 (y7 y10 y22 : word),
rd_invA C m2 (r_nc s1) msvw (Z_to_bv 64 tl) -> CTL msv1 (a_rt0 C) tl s1 -> POS buf s1 -> r_bitCount s1 < 32 ->
(let! fl := rcount_block buf msv1 s1 in match fl with Brk s' => Ok s' | Cont s' => rloop buf msv1 f s' end) = Ok sF ->
evtF bsegs RNG POSTF (rd_cntA C s1 m2 y7 y10 y22)).
{ intros s1 m2 y7 y10 y22 INV1 HC1 HP1 HB1 RL1.
destruct (rcount_total buf (buf_all_bytesA C OK) buf_h8A msv1 (a_rt0 C) msv1_okA tl Htl s1 HC1 HP1 HB1) as (fl & EF & HF).
rewrite EF in RL1. cbn [bind] in RL1.
eapply (count_runA C RNG OK SH RNGS tl Htl POSTF s1 m2 msvw (Z_to_bv 64 tl) fl); try eassumption.
- intros s' m3 z1 z6 z7 z12 z18 z20 z22 z29 -> INV3 BK. injection RL1 as ->.
destruct HF as ((_ & CN1 & _) & _).
eapply (exit_runA sF m3 msvw); try assumption. Local Ltac2 Set LiaHints.tbl := fun () => "0030>45237659827.4166338264904.4166350914419.5000000100900AFS2F23CN1S2F23CN1".
lia.
- intros s' m3 z7 z12 z20 z22 z29 -> INV3. destruct HF as (HC3 & HP3 & HB3 & _).
eapply IH; eassumption. }
unfold rbody in RL.
destruct (r_previous0 s) eqn:EP.
-
destruct (rzero_total buf (buf_all_bytesA C OK) buf_h8A msv1 (a_rt0 C) msv1_okA tl Htl s HC HP HB32) as (flz & EZ & HZ).
rewrite EZ in RL. cbn [bind] in RL.
unfold rd_headA. rewrite EP.
eapply (zero_runA C RNG OK SH RNGS POSTF tl s m1 msvw (Z_to_bv 64 tl) flz); try eassumption.
+ intros s' z1 z6 z7 z12 z18 z20 z22 z29 -> EN BK. cbn [bind] in RL. injection RL as ->.
destruct HZ as ((_ & CN1 & _) & _).
eapply (exit_runA sF m1 msvw); try assumption; try lia. rewrite EN. exact INV.
+ intros s' z7 z10 z22 -> EN. destruct HZ as (HC1 & HP1 & HB1 & _).
apply CNT; try assumption. rewrite EN. exact INV.
-
cbn [bind] in RL.
unfold rd_headA. rewrite EP.
eapply (cnt_entryA C RNG tl Htl POSTF s m1); try eassumption.
intros y7 y10 y22. apply CNT; assumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Loop.
End CANSEC1.
