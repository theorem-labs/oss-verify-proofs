(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTEu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTEu. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXUB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXUB.  From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4v2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4v2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgHv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgHv. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1Y6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1Y6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpNt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpNt.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qw5U.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9O6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9O6.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QL3k.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QL3k.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql4f.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql4f. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSHS.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsjA.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section Ser.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.
Variable PFRT : (word -> option byte) -> Prop.
Variable PFLO : Z.
Hypothesis OBL_PFRT : forall A LB LM FRS B m md, HEAPAx A LB LM FRS B m md -> PFRT m.
Hypothesis OBL_PFLO : PFLO <= alloc_ceiling.
Hypothesis SNP_LD : isnprintf_ld_stmt PFRT PFLO.
Hypothesis SNP_LU : isnprintf_lu_stmt PFRT PFLO.

Lemma ser_intA_16 : ser_specA_al HIx 16 ASER_INT Sint.
Proof.
unfold ser_specA_al, ser_specA. intros until errv. intros D32 HP PB JN INCL JTX CAP TXT NEED FL Hlv Hlvd FRSN ST LO LOS SPA HT ERR JHX TP' RA FRM A0 A1 A2 A3 K.
destruct JN as (cty & v & junk & EREST & Hcty & NODE). unfold jhdr_cells in NODE. cbn [app] in NODE.
subst a0 a1 a2 a3 tp REST.
cbn [app jtx] in JTX. rewrite Z.eqb_refl in JTX. injection JTX as <- _.
unfold ASER_INT, ser_budgetA, ASER_LEVEL, ASER_LEAF in *. cbn [sdepth Z.mul Z.add] in LOS.
word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof alloc_ceiling_range as ACR.
pose proof (hiA_top_le A4L HIx) as HTLE.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP) as (SB1 & SB2 & SB3 & SB4).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2. apply ro_C8_of_bytes_at in SB3.
assert (UARC : ro_cells asegs m (hl_uar_cell A4L) [C4 (Z_to_bv 64 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SB4]).
clear SB4.
assert (INp : In (p, 56) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; apply INCL; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p 56 HP ltac:(apply in_or_app; left; exact INp)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ pb PB_SZ HP ltac:(apply in_or_app; left; left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(apply in_or_app; left; right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
unfold_consts.
shadow_inA A4L HIx HP INp SHp.
pose proof PB as (Hbp & Hcap & Hlen & PBS & PBUF).
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 112%nat ST.
step. stepz. do 9 step.
step. step.
rewrite (unsigned_lit (bv_unsigned sp + -96)) by lia. change 18446744073709551584 with (2^64 - 2^5). rewrite OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.land_align_down by lia. change (2^5) with 32.
replace (bv_unsigned sp + -96 - (bv_unsigned sp + -96) mod 32) with (bv_unsigned sp + -112) by (clear - D32; Z.div_mod_to_equations; lia).
do 9 step.
norm_sx32. step. if_false. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
evt_done5.
eapply (stack_malloc_full HIx) with (k := 1) (bytes := 96) (lo := lo) (LB := (pb, PB_SZ) :: (buf, cap) :: LB) (LM := LM) (FR := FRS) (B := B);
[ heap_nowA A4L HIx HP MU WM MI1 | lia | .. ].
all: rewrite ?unsigned_lit by lia.
1: rewrite fr_size_1; lia.
1: reflexivity.
1: lia.
1: exact ST.
1: exact LO.
1: cbn [hl_stack_A A4L]; lia.
1: clear - D32; Z.div_mod_to_equations; lia.
1: lia.
1: reflexivity.
1: reflexivity.
intros ms1 m1' md1 A1 Fr RS1 VM1 ST1 HPR1 FRNZ (jff & FF1) SHB1 HP1. open_ret RS1.
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP1) as (errv1 & ERR1). unfold A_ERRNO, A_TP in ERR1. cbn [hl_tp A4L A4H hla_base] in ERR1.
rewrite ?unsigned_lit in ST1, HPR1 by lia.
clear ERR.
assert (INF : In (Fr, 1) ((Fr, 1) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as (_ & HFal & HF0 & HFc & HFimg & _ & HFshw & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFapp.
pose proof (frame_above_img HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFhi. cbn [hl_img_hi A4H] in HFhi.
rewrite fr_size_1 in HFal, HFc, HFimg, HFapp. rewrite fr_shadow_len_1 in HFshw. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp. unfold A_SB in HFapp.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in NODE; [| eapply client_range_block; [apply in_or_app; left; exact INp | lia | cbn; lia]].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in PBS; [| eapply client_range_block; [apply in_or_app; left; left; reflexivity | cbn; lia | cbn; lia]].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in PBUF; [| eapply client_range_block; [apply in_or_app; left; right; left; reflexivity | cbn; lia | cbn; lia]].
clear SB1 SB2 SB3 UARC SHp.
shadow_inA A4L HIx HP1 INp SHp.
assert (INpX : In (p, 56) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; exact INp).
assert (INpbX : In (pb, PB_SZ) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; left; reflexivity).
assert (INbufX : In (buf, cap) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; right; left; reflexivity).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 INF INpX) as DFp. rewrite fr_size_1 in DFp.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 INF INpbX) as DFpb. rewrite fr_size_1 in DFpb.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 INF INbufX) as DFbuf. rewrite fr_size_1 in DFbuf.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INpX) as APp. cbn [hl_sb A4L] in APp. unfold A_SB in APp.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INpbX) as APpb. cbn [hl_sb A4L] in APpb. unfold A_SB in APpb.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INbufX) as APbuf. cbn [hl_sb A4L] in APbuf. unfold A_SB in APbuf.
assert (FSH1 : rw_cells asegs m1' (shad A4L Fr) [CB 16 (repeat (Z_to_bv 8 0) 16)]).
{ split; [split; [cbn; split; [reflexivity | exact I] | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SHB1] | exact HFshw]. }
clear SHB1.
rewrite fr_size_1 in FF1. change (Z.to_nat (128 - 8)) with 120%nat in FF1.
unfold shad in FSH1. a4l.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 16 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1'. change (hl_segs A4L) with asegs in MI1'. clear MI1.

assert (SUB0 : forall b, In b (LB ++ LM ++ fr_ivs A4L FRS) -> In b (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM) \/ In b (fr_ivs A4L FRS)).
{ intros b Hb. apply in_app_or in Hb as [Hb|Hb]; [left; apply in_or_app; left; right; right; exact Hb|]. apply in_app_or in Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb]. }
assert (SUB1 : forall b, In b (LB ++ LM ++ fr_ivs A4L FRS) -> In b (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM) \/ In b (fr_ivs A4L ((Fr, 1) :: FRS))).
{ intros b Hb. destruct (SUB0 b Hb) as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H]. }
destruct (own_frame_fresh HIx Fr 1 ((pb, PB_SZ) :: (buf, cap) :: LB) LB LM FRS B A1 m1' md1 HP1 ltac:(intros b Hb; right; right; exact Hb)) as [OFF OFS].
assert (HPR01 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1').
{ eapply heap_pres_trans.
- eapply (pres_private HIx _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp) HP MU WM SUB0 ltac:(lia)). apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. lia.
- eapply heap_pres_weaken; [exact HPR1 | lia |]. intros b Hb. apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; right; right; exact Hb | apply in_or_app; right; exact Hb]. }
clear MU WM. pose proof (wmono_refl asegs m1') as WM. pose proof (munch_refl [(lo, bv_unsigned sp); (Fr, Fr + 120); (sh, sh + 16)] m1') as MU.
reenterA asegs A4L HIx asegs_wx HP1.
step. step. step. if_truex.
stepz.
step. step. step. step.
rewrite (unsigned_lit Fr) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
step. step. step. step. step.
stepz. stepz. stepz. step. step.
fold sh.
do 12 stepz.
step. if_falsex.
step. step. ubsan_align Hpal.
step.

step; step; sh_norm;
repeat match goal with
| |- context [ (?p + ?j) / 8 ] => is_Zlit j; rewrite (div8_add p j) by lia; let k := eval vm_compute in (Z.div j 8) in change (j / 8) with k
end.
step. step. first [ if_false | if_true ]. rewrite ?sxb_zero, ?zxb_zero.
step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
match goal with H : stk asegs m2 lo _ |- _ => rename H into ST2 end.

assert (TAILK : forall (afmt : Z), isnprintf_l_stmt PFRT PFLO afmt ->
evt asegs (AJ5e A4L HIx A1 T md1)
(MS (mkR (Z_to_bv 64 640888) (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 6444320) u0 u1 u2 sp
(Z_to_bv 64 (bv_unsigned sp + -112)) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 21) (Z_to_bv 64 afmt) v (Z_to_bv 64 (-15)) v5 v6 v7
(Z_to_bv 64 Fr) (Z_to_bv 64 pb) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 sh) (Z_to_bv 64 Fr) (Z_to_bv 64 2147450880) s8 s9 s10 s11 u3 u4 u5 u6)
F (Z_to_bv 64 327028) fc None m2 (seg_rom asegs))).
{ intros afmt SNP.
assert (HPc : HEAPAx A1 ((pb, PB_SZ) :: (buf, cap) :: LB) LM ((Fr, 1) :: FRS) B m2 md1).
{ eapply (heapA_client_frame A4L HIx); [exact HP1 | | exact WM | exact MI2].
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP1 MU).
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]].
- left. cbn [fst snd]. lia.
- right; right; right. exists Fr, 1. split; [exact INF|]. left. cbn [fst snd]. rewrite fr_size_1. lia.
- right; right; right. exists Fr, 1. split; [exact INF|]. right. unfold shad. cbn [fst snd hl_sb A4L]. change (fr_shadow_len 1) with 16. unfold A_SB. fold sh. lia. }
pose proof (OBL_PFRT _ _ _ _ _ _ _ HPc) as RT2.
eapply (rw_cells_split_CB asegs _ _ [_; _; _] 96 _ [] [8%nat; 24%nat; 64%nat]) in FF1; [| reflexivity].
cbn [app mk_CB_cells] in FF1.
apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _] _)) in FF1. destruct FF1 as [FFa FFe]. cbn [cells_size csize Nat.add] in FFe.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FFe. destruct FFe as [FFe FFb]. cbn [cells_size csize Nat.add] in FFb.
change (Z.of_nat 32) with 32 in FFe, FFb. replace (Fr + 32 + Z.of_nat 24) with (Fr + 56) in FFb by lia.
apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _; _; _; _; _] _)) in FSH1. destruct FSH1 as [FSHa FSHb]. cbn [cells_size csize Nat.add] in FSHb.
change (sh + Z.of_nat 8) with (sh + 8) in FSHb.
destruct (sbuf_shadow_word m2 sh FSHa) as [FSHw2 _].
eapply evt_cut.
{ eapply (SNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 (Fr + 32) 21 24%nat _ lo); [| reflexivity].
unfold isnp_pre, SNP_STACK_A. rewrite ?unsigned_lit by lia.
split; [reflexivity|]. split; [reflexivity|]. split; [exact FFe|]. split; [exact RT2|].
split; [lia|]. split; [lia|]. split; [exact ST2|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [exact MI2|]. split; [exact FRM|]. split; [left; lia|].
split; [unfold dappJ; destruct HFapp; [left | right]; lia|].
intros k Hk. eapply (rng_okJ_sbuf m2 Fr SBUF_SHWORD k HFal); [lia | lia | unfold A_SB; fold sh; exact FSHw2 | exact le8_SBUF_SHWORD | lia]. }
intros ms3 (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & F3 & fc3 & m3 & r & o & -> & MU3 & WM3 & MI3 & FRM3 & FREG3 & ST3 & Hr & (Hr20 & ONZ) & FFe3).
rewrite ?unsigned_lit in MU3, ST3 by lia.
assert (HP3 : HEAPAx A1 ((pb, PB_SZ) :: (buf, cap) :: LB) LM ((Fr, 1) :: FRS) B m3 md1).
{ eapply (heapA_client_frame A4L HIx); [exact HPc | | exact WM3 | exact MI3].
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HPc MU3).
apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
- left. cbn [fst snd]. lia.
- right; right; right. exists Fr, 1. split; [exact INF|]. left. cbn [fst snd]. rewrite fr_size_1. lia. }
stash FFe3.
transport_after_call asegs m2 m3 MU3 WM3; try match goal with H : mem_inv asegs m2 |- _ => clear H end.
unstash FFe3.
replace (ret_pc (Z_to_bv 64 640888)) with (Z_to_bv 64 640888) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

step. step.
pose proof (rw_cells_bytes_at asegs _ _ _ FFe3) as STR3. cbn [cells_bytes cbytes app] in STR3. rewrite app_nil_r in STR3.
assert (SLEN : length (o ++ Z_to_bv 8 0 :: skipn (S (length o)) (firstn 24 (skipn 8 (skipn 8 (skipn 8 (skipn 8 jff)))))) = 24%nat) by (destruct FFe3 as [[[Hwf _] _] _]; exact Hwf).
set (slack := skipn (S (length o)) (firstn 24 (skipn 8 (skipn 8 (skipn 8 (skipn 8 jff)))))) in *.
rewrite length_app in SLEN. cbn [length] in SLEN.
destruct (sbuf_shadow_word m3 sh FSHa) as [_ FSHb3].
eapply (astrlen_U _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc3 m3 (Fr + 32) lo o slack);
rewrite ?unsigned_lit by lia;
[ apply unpoisoned_sbuf; [exact HFal | lia | unfold A_SB; fold sh; exact FSHb3 | lia]
| exact (asan_rt_ok_of_HEAPA HIx _ _ _ _ _ _ _ HP3)
| lia | lia | left; lia | reflexivity | exact ONZ | lia | left; lia | exact STR3
| clear - SLEN Hr Hr20 HFal; Z.div_mod_to_equations; lia
| exact ST3 | exact LO | lia | clear - D32; Z.div_mod_to_equations; lia | exact MI3 | reflexivity | ].
intros z0 z1 z2 w1 w2 w3 w4 w5 w6 w7 z3 z4 z5 z6 m4 MU4 WM4 MI4 STR4 ST4.
assert (HP4 : HEAPAx A1 ((pb, PB_SZ) :: (buf, cap) :: LB) LM ((Fr, 1) :: FRS) B m4 md1).
{ eapply (heapA_client_frame A4L HIx); [exact HP3 | | exact WM4 | exact MI4].
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP3 MU4).
apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. lia. }
stash STR4.
transport_after_call asegs m3 m4 MU4 WM4; try match goal with H : mem_inv asegs m3 |- _ => clear H end.
unstash STR4.
replace (ret_pc (Z_to_bv 64 640896)) with (Z_to_bv 64 640896) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
set (len := Z.of_nat (length o)) in *.
step. rewrite (unsigned_lit len) by lia. rewrite Z.add_0_r. rewrite swrap32_id by lia.
do 3 step. fold_mkR.

assert (FS3 : fsaved F F3).
{ intros k Hk. apply FREG3. cbn in Hk. repeat (destruct Hk as [<- | Hk]; [vm_compute; discriminate|]). destruct Hk. }
assert (HPR04 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m4).
{ eapply heap_pres_trans; [exact HPR01|].
eapply (pres_private HIx _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp) HP1 MU WM SUB1 ltac:(lia)).
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]].
+ left. cbn [fst snd]. lia.
+ right; right; right. exists Fr, 1. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. cbn [fst snd]. rewrite fr_size_1. lia.
+ right; right; right. exists Fr, 1. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. right. unfold shad. cbn [fst snd hl_sb A4L]. change (fr_shadow_len 1) with 16. unfold A_SB. fold sh. lia. }
lazymatch type of FR with rw_cells _ _ _ ?frc => lazymatch type of FFa with rw_cells _ _ _ ?ffc => lazymatch type of FSHa with rw_cells _ _ _ ?sac => lazymatch type of FSHb with rw_cells _ _ _ ?sbc =>
assert (INV4 : ser_memA HIx sp m md LB LM FRS B pb lo bpos cap 20 A1 ((Fr, 1) :: FRS) (bv_unsigned sp + -112)
[(bv_unsigned sp + -112, frc); (Fr, ffc); (sh, sac); (sh + 8, sbc)] 0 m4 md1) end end end end.
{ exists buf, cap, bpos, content, errv1, B.
split; [exact HP4|].
split; [split; [lia|]; split; [lia|]; split; [exact Hlen|]; split; [exact PBS | exact PBUF]|].
split; [repeat (constructor; [eassumption|]); constructor|].
split.
{ constructor; [left; cbn [fst]; lia|].
constructor; [right; right; exists (Fr, fr_size 1 - 8); split; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact INF | cbn [blk_addr blk_size fst snd cells_size csize Nat.add]; rewrite fr_size_1; lia]|].
constructor; [right; right; exists (shad A4L Fr, fr_shadow_len 1); split; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_shadow; exact INF | unfold shad; cbn [blk_addr blk_size fst snd cells_size csize Nat.add hl_sb A4L]; change (fr_shadow_len 1) with 16; unfold A_SB; fold sh; lia]|].
constructor; [right; right; exists (shad A4L Fr, fr_shadow_len 1); split; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_shadow; exact INF | unfold shad; cbn [blk_addr blk_size fst snd cells_size csize Nat.add hl_sb A4L]; change (fr_shadow_len 1) with 16; unfold A_SB; fold sh; lia]|].
constructor. }
split; [intros b Hb; cbn [fr_ivs flat_map app]; right; right; exact Hb|].
split; [exact ERR1|]. split; [exact ST4|].
split; [exact HPR04|].
split; [exact VM1|].
split; [lia|]. split; [unfold ser_capb; lia|]. split; lia. }
assert (SRC4 : bytes_at asegs m4 (Fr + 32) o).
{ replace (o ++ Z_to_bv 8 0 :: slack) with (o ++ (Z_to_bv 8 0 :: slack)) in STR4 by reflexivity. apply bytes_at_app in STR4. exact (proj1 STR4). }
destruct (sbuf_shadow_word m4 sh FSHa) as [_ FSHb4].
evt_done5.
eapply (ser_appendA HIx sp gp m md LB LM FRS B pb lo bpos cap 20 LO HT CAP TXT NEED OBL_REALLOC_NF) with (F := F) (sb := o) (e := 0);
[ exact INV4 | exact SRC4 | reflexivity | fold len; lia | lia
| right; left; exists Fr, 1; split; [left; reflexivity | rewrite fr_size_1; fold len; lia]
| intros Hk; apply unpoisoned_sbuf; [exact HFal | lia | unfold A_SB; fold sh; exact FSHb4 | fold len; lia]
| lia | fold len; lia | lia
| clear - D32; Z.div_mod_to_equations; lia
| lia | lia | reflexivity | lia | reflexivity | exact FS3 | exact FRM3 | ].

intros A6 m6 md6 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F6 fc6 INV6 FS6 FR6 _.
pose proof INV6 as (buf6 & cap6 & bpos6 & content6 & errv6 & B6 & HP6 & PB6 & CH6 & _ & _ & ERR6 & ST6 & HPR6 & VM6 & Hb6 & Hc6 & HB6 & HD6).
apply Forall_cons_iff in CH6 as [FR6c CH6]. apply Forall_cons_iff in CH6 as [FFa6 CH6]. apply Forall_cons_iff in CH6 as [FSHa6 CH6]. apply Forall_cons_iff in CH6 as [FSHb6 _].
cbn [fst snd] in FR6c, FFa6, FSHa6, FSHb6.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP6) as MI6. cbn [hl_segs hla_base A4L A4H] in MI6.
pose proof PB6 as (Hbp6 & Hcap6 & Hlen6 & PBS6 & PBUF6).
assert (INpb6 : In (pb, PB_SZ) (((pb, PB_SZ) :: (buf6, cap6) :: LB) ++ LM)) by (apply in_or_app; left; left; reflexivity).
assert (INbuf6 : In (buf6, cap6) (((pb, PB_SZ) :: (buf6, cap6) :: LB) ++ LM)) by (apply in_or_app; left; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP6 INbuf6) as (_ & Hbal6 & Hblo6 & Hbhi6 & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbhi6.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP6 INF INpb6) as DFpb6. rewrite fr_size_1 in DFpb6.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP6 INF INbuf6) as DFbuf6. rewrite fr_size_1 in DFbuf6.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP6 INbuf6) as APbuf6. cbn [hl_sb A4L] in APbuf6. unfold A_SB in APbuf6.
clear MU WM. try clear FR. try clear FFa. try clear FFb. try clear FFe3. try clear FSHa. try clear FSHb. try clear STR4. try clear SRC4. try clear ST4. try clear HP4. try clear HP3. try clear HPc. try clear INV4. try clear FSHb3. try clear FSHb4. try clear PBS. try clear PBUF. try clear NODE. try clear ERR1. try clear SHp. try clear STR3. try clear INV6. try clear MI4.
pose proof (wmono_refl asegs m6) as WM. pose proof (munch_refl [(lo, bv_unsigned sp); (Fr, Fr + 120); (sh, sh + 16)] m6) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP6.
step. stepz. stepz. stepz. step. step. stepz.
step. if_falsex.
step. do 16 stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mX end.
match goal with H : mem_inv asegs mX |- _ => rename H into MIX end.
assert (HPX : HEAPAx A6 ((pb, PB_SZ) :: (buf6, cap6) :: LB) LM ((Fr, 1) :: FRS) B6 mX md6).
{ eapply (heapA_client_frame A4L HIx); [exact HP6 | | exact WM | exact MIX].
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP6 MU).
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]].
- left. cbn [fst snd]. lia.
- right; right; right. exists Fr, 1. split; [exact INF|]. left. cbn [fst snd]. rewrite fr_size_1. lia.
- right; right; right. exists Fr, 1. split; [exact INF|]. right. unfold shad. cbn [fst snd hl_sb A4L]. change (fr_shadow_len 1) with 16. unfold A_SB. fold sh. lia. }
assert (HPR6X : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m6 mX).
{ assert (SUB6 : forall b, In b (LB ++ LM ++ fr_ivs A4L FRS) -> In b (((pb, PB_SZ) :: (buf6, cap6) :: LB) ++ LM) \/ In b (fr_ivs A4L ((Fr, 1) :: FRS))).
{ intros b Hb. apply in_app_or in Hb as [Hb|Hb]; [left; apply in_or_app; left; right; right; exact Hb|]. apply in_app_or in Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; cbn [fr_ivs flat_map app]; right; right; exact Hb]. }
eapply (pres_private HIx _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp) HP6 MU WM SUB6 ltac:(lia)).
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]].
+ left. cbn [fst snd]. lia.
+ right; right; right. exists Fr, 1. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. cbn [fst snd]. rewrite fr_size_1. lia.
+ right; right; right. exists Fr, 1. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. right. unfold shad. cbn [fst snd hl_sb A4L]. change (fr_shadow_len 1) with 16. unfold A_SB. fold sh. lia. }
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HPX INF) as (_ & _ & _ & _ & _ & _ & _ & (fp & FPB & FPR & FPnc & FPimg & FPns & FPfr)).
rewrite fr_size_1 in FPB. replace (Fr + 128 - 8) with (Fr + 120) in FPB by lia.
pose proof (ro_C8_of_bytes_at asegs _ _ _ FPB) as FPC.
step.
evt_done5.
eapply (hiA_frame_release A4L HIx) with (Fr := Fr) (k := 1) (fp := fp) (rX := Z_to_bv 5 11);
[exact HPX | exact INF | rewrite fr_size_1; replace (Fr + 128 - 8) with (Fr + 120) by lia; exact FPB | lia | reflexivity | vm_compute; discriminate | | ].
1: vm_compute; split; reflexivity.
intros m7 md7 A7 VM7 HP7 Hoff Hwv.
cbn [fr_remove fr_base fst Z.eqb] in HP7. rewrite Z.eqb_refl in HP7.
assert (MUr : munch [(fp, fp + 1)] mX m7).
{ intros x Hx. cbn [outside] in Hx. pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. cbn in XR.
rewrite <- (Z_to_bv_bv_unsigned x). change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)). apply Hoff; lia. }
assert (WMr : wmono asegs mX m7) by exact Hwv.
assert (MI7 : mem_inv asegs m7).
{ intros y b Hb. destruct (Z.eq_dec (bv_unsigned y) fp) as [Ey | Ny].
- destruct (ro_addr asegs y) eqn:RO; [| reflexivity]. exfalso. apply ro_addr_asegs in RO. cbn [hl_img_lo hl_img_hi A4H hla_base A4L] in FPimg. lia.
- apply (MIX y b). rewrite <- Hb. symmetry. rewrite <- (Z_to_bv_bv_unsigned y). change (Z_to_bv 64 (bv_unsigned y)) with (wa (bv_unsigned y)). apply Hoff; [| exact Ny].
pose proof (bv_unsigned_in_range 64 y) as YR. unfold bv_modulus in YR. cbn in YR. lia. }
assert (FPlow : fp < alloc_ceiling) by (destruct (Z.lt_ge_cases fp alloc_ceiling) as [L|G]; [exact L | exfalso; apply FPnc; left; exact G]).
assert (FPpb : ~ (pb <= fp < pb + PB_SZ)) by (intros Hin; apply FPnc; right; right; exists (pb, PB_SZ); split; [exact INpb6 | exact Hin]).
assert (FPbuf : ~ (buf6 <= fp < buf6 + cap6)) by (intros Hin; apply FPnc; right; right; exists (buf6, cap6); split; [exact INbuf6 | exact Hin]).
apply (rw_cells_transport asegs [(fp, fp + 1)] mX m7) in FR6c; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] mX m7) in ERR6; [| exact MUr | exact WMr | cbn [disjoint_from cells_size csize Nat.add]; cbn [hl_scratch A4L A4H hla_base] in FPns; unfold A_TP in FPns; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] mX m7) in PBS6; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] mX m7) in PBUF6; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; lia].
apply (stk_transport_disjoint asegs [(fp, fp + 1)] mX m7) in ST6; [| exact MUr | exact WMr | cbn [disjoint_from]; lia].
change (641016 + 4) with 641020.
reenterA asegs A4L HIx asegs_wx HP7.
step. step. do 9 step. step.
release_frame FR6c ST6 (bv_unsigned sp).
step.
evt_done5. apply K. unfold ser_postA.
exists m7, a0', errv6, buf6, cap6, bpos6, content6, B6.
split; [apply ret_statew_intro; [exact FS6 | intros _; exact FR6]|].
split; [eapply model_vm_only_trans; [exact VM6 | exact VM7]|].
split; [exact ST6|].
split.
{ eapply heap_pres_trans; [exact HPR6|]. eapply heap_pres_trans; [exact HPR6X|].
assert (SUB7 : forall b, In b (LB ++ LM ++ fr_ivs A4L FRS) -> In b (((pb, PB_SZ) :: (buf6, cap6) :: LB) ++ LM) \/ In b (fr_ivs A4L ((Fr, 1) :: FRS))).
{ intros b Hb. apply in_app_or in Hb as [Hb|Hb]; [left; apply in_or_app; left; right; right; exact Hb|]. apply in_app_or in Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; cbn [fr_ivs flat_map app]; right; right; exact Hb]. }
exact (pres_fp HIx _ _ _ _ _ _ _ _ _ (bv_unsigned sp) fp HPX SUB7 ltac:(lia) FPnc FPfr Hoff Hwv). }
split; [exact ERR6|]. split; [exact HP7|].
split; [split; [exact Hbp6|]; split; [exact Hcap6|]; split; [exact Hlen6|]; split; [exact PBS6 | exact PBUF6]|].
split; [fold len in Hb6; lia|]. split; [exact Hc6|]. split; lia. }
step.
destruct Hcty as [-> | ->].
- first [if_truex | if_lit]. do 2 step. asan_chkA. do 5 step. fold_mkR. exact (TAILK A_FMT_LD SNP_LD).
- first [if_falsex | if_lit]. do 3 step. asan_chkA. do 5 step. fold_mkR. exact (TAILK A_FMT_LU SNP_LU).
Qed.
End Ser.
End RC__1.
