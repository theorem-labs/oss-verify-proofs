(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the run / keep / branch / leaf tactics, kept_run and same_io_wvb are the text of
   projects/reac-pw/fuzz_qdisc/proofs/lib/A/QPgSlots.v:123-188 (made there from proofs/libreac/fuzz_knock/lib/A/APgStep.v,
   origin/ossv/recipes 6ebe35ba632), the stack-slot write tactics that of QPgCheck.v:52-69, the entry regions those of
   QPgRt.v:61-65 / 193-243, the shadow entry that of proofs/libreac/fuzz_identity/lib/A/Prog/sb_dec.v:354-370
   (origin/ossv/recipes 4b6f0df50aa7), cw_U_sx32_eqb that of proofs/libreac/fuzz_knock/lib/A/APgStep.v:54-68
   (U_sx32_eqb, origin/ossv/recipes 4b6f0df50aa7), cw_join_win that of proofs/reac-pw/fuzz_qdisc/lib/A/QPgLoop0.v:169-196
   (ra_join_win, a working branch b0f706c04a19), cw_bcmp_at that of lib/Reusable/YCbq.v:2262-2310 (aj_bcmp_at) with
   the wrapper's same_but_materialized kept in its post, cw_st_ok_at that of lib/Reusable/YI04.v:342-356 (entry_st_ok_full)
   with the env apart from the registers, renamed with the prefix cw_ and moved to libdiginet/fuzz_codec's ASan
   build (image A); the leaf ends in lib/A/Prog/CPgBase.v's cdc_post, whose memory clause is CodecCJ's tcj_kept. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgWalk.v, with its module names changed; 414 of its 469 lines of code are new or changed and 578 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_owel.v, with its module names and numbers changed; 557 of its 629 lines of code are new or changed and 397 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_oweh_lib.v; 450 of its 526 lines of code are new or changed and 553 lines of the source are left out. *)
(* Segment OWEH of the image-A walk of LLVMFuzzerTestOneInput (lib/A/Prog/codec_amain_inv.v seg_oweh):
   owe()'s common part, 0x8220c-0x82264, 0x822d4-0x822ec and 0x827d4-0x827dc, from JOIN to OWEk or to CHK.
   The three straight pieces run on the states of lib/A/Prog/codec_amain_oweh_lib.v:
     JOIN 0x8220c to the call of the runtime's checked memset (one run per kind, the kind a literal of k's
     first field, so that the mask test (0x812 >> kind) & 1 and the bound test decide);
     the call itself (oh_memset);
     0x82248 to OWEk (the kind pinned as a literal, owe()'s table read as bytes of the image), and
     0x822e8 to 0x82248 when k.desk <> 0, else to CHK with want_rc = -1 (by pd_okA a NULL desk is od = None,
     and owe() answers E_ARG for a kind that needs a desk). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_agree.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08 YI16.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC CodecRo CodecGlobs.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CPgWalk CPgWalkImg CPgWalkIntr CPgWalkKept.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_inv codec_amain_st codec_amain_lem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_encl codec_amain_owel codec_amain_oweh_lib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.
Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis AMEMSET : aintrin_realizes tfibsegs B OSet CA_MEMSET.

(* ================================ the end of the first piece ================================ *)
Lemma oh_end1 : forall g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c k od kd E ss mem3 regs3 md3,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)]
  ly2 S2 W2 mem2 md2 kj ->
frames S2 = [(3, pos)] -> 0 <= kj <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
ops_at ops regs2 -> cur_at g sp1 c W2 mem2 -> k_at g pos k W2 mem2 -> rec_okZ k od ->
kz_kind k = kd -> 0 <= kd <= 11 ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)]
  ly2 S2 W2 mem3 md3 kj ->
env_agree 38 (am_env g pos c regs2 [kz_desk k]) E ->
st_ok tfibsegs E ss (restrict (w_H W2) (mkst regs3 (Z_to_bv 64 CA_MEMSET) mem3 (seg_rom tfibsegs))) ->
am_keep_ok (ss_regs ss) = true -> sr_get (ss_regs ss) 26%bv = SOff 26 0 ->
nth_error (ss_mem ss) 4 = Some am_cur_region ->
sr_get (ss_regs ss) 1%bv = SLit (oh_ret (oh_dk kd)) ->
sr_get (ss_regs ss) 10%bv = SOff 33 344 -> sr_get (ss_regs ss) 11%bv = SLit 0 ->
sr_get (ss_regs ss) 12%bv = SLit 16 -> sr_get (ss_regs ss) 23%bv = SOff 37 0 ->
sr_get (ss_regs ss) 24%bv = SLit kd ->
val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 248) 4 (fst (enc_kZ k od)) ->
val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 316) 4 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ oh_z1 g pos sp1 a ->
 aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
SRr tfibsegs W2 (mkCfg (mkst regs3 (Z_to_bv 64 CA_MEMSET) mem3 (seg_rom tfibsegs)) md3)
  (fun W3 c3 => exists dk, oh_call B MT K XM_LIB g pos sp1 ops dk W3 c3).
Proof using TL LAWS AMEMSET ROB.
intros g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c k od kd E ss mem3 regs3 md3
  HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hkind Hkd HJ3 HAE HS Hkeep H26 Hcur4
  S1 S10 S11 S12 S23 S24 V248 V316 KE.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hng & Hpg & Hpng & _).
change (fs_frame_bytes 3) with 512 in Hfceil. unfold AM_HI in *.
assert (FFS : LLVMF_STK = 32768) by reflexivity.
destruct (oh_fin B MT K XM_LIB TL LAWS g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c [kz_desk k] E ss
  mem3 regs3 md3 CA_MEMSET (oh_z1 g pos sp1) HJ Hfr HC Hops Hcur HJ3 HAE HS Hkeep H26 Hcur4
  ltac:(intros a Ha; unfold oh_z1 in Ha; lia) KE) as (HC3 & Hops3 & Hcur3).
pose proof Hkat as [HKK HKW].
destruct HKK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Vwl & Vwk & Vwd).
pose proof HKW as (_ & _ & Wdesk & _ & _ & _ & _ & _ & _ & _ & Wwl & Wwk & Wwd & _).
assert (KV : forall a n v, FA g pos + 320 <= a -> a + Z.of_nat n <= FA g pos + 360 ->
  val_mem tfibsegs (mrestrict (w_H W2) mem2) a n v -> val_mem tfibsegs (mrestrict (w_H W2) mem3) a n v).
{ intros a n v H1 H2 Hv. apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 mem3); [|exact Hv].
  intros x Hx. apply KE; [lia | unfold oh_z1; lia]. }
assert (V344 : val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 344) 8 (kz_want_len k)).
{ apply (KV _ 8%nat); [lia | cbn; lia |].
  replace (FA g pos + 344) with (FA g pos + 176 + 168) by lia. exact Vwl. }
assert (V352 : val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 352) 4 (kz_want_key k)).
{ apply (KV _ 4%nat); [lia | cbn; lia |].
  replace (FA g pos + 352) with (FA g pos + 176 + 176) by lia. exact Vwk. }
assert (V356 : val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 356) 4 (kz_want_display k)).
{ apply (KV _ 4%nat); [lia | cbn; lia |].
  replace (FA g pos + 356) with (FA g pos + 176 + 180) by lia. exact Vwd. }
assert (HK3 : k_at g pos (oh_set k (fst (enc_kZ k od)) 0 (kz_want k)
  (kz_want_len k) (kz_want_key k) (kz_want_display k)) W2 mem3).
{ apply (oh_k_at_set g pos k W2 mem2 W2 mem3 (fst (enc_kZ k od)) 0 (kz_want_len k) (kz_want_key k)
    (kz_want_display k) Hkat).
  - intros a Ha. apply KE; [lia | unfold oh_z1; lia].
  - exact V248.
  - exact V316.
  - exact V344.
  - exact V352.
  - exact V356.
  - exact (rec_kZ_rc_int k od Hrec).
  - lia.
  - exact Wwl.
  - exact Wwk.
  - exact Wwd. }
apply SRr_ret. exists (oh_dk kd). unfold oh_call.
apply (am_mcut B MT K XM_LIB g pos sp1 0 CA_MEMSET _ ly2 S2 W2 regs3 mem3 md3 kj HJ3 Hfr Hk Hmo HC3).
cbv beta. split; [exact Hops3|].
exists c, (oh_set k (fst (enc_kZ k od)) 0 (kz_want k) (kz_want_len k) (kz_want_key k)
  (kz_want_display k)), od.
split; [exact Hcur3|]. split; [exact HK3|]. split; [exact Hrec|].
split; [intros Hd _; cbn [kz_kind oh_set]; rewrite Hkind;
        exact (oh_dk_true B TL LAWS kd Hd)|].
split; [intros Hd; cbn [kz_kind oh_set]; rewrite Hkind;
        exact (oh_dk_false B TL LAWS kd Hd)|].
split; [reflexivity|]. split; [reflexivity|].
split.
{ exact (oh_reg_off B TL LAWS g pos c regs2 [kz_desk k] E ss W2 _ 23%bv 37 (kz_desk k)
    HAE HS S23 ltac:(lia) (am_ew_y g pos c regs2 [kz_desk k] 0) ltac:(lia)). }
split.
{ cbn [kz_kind oh_set]. rewrite Hkind.
  exact (oh_reg_lit B TL LAWS E ss W2 _ 24%bv kd HS S24). }
split.
{ exact (oh_reg_offo B TL LAWS g pos c regs2 [kz_desk k] E ss W2 _ 10%bv 33 344 (FA g pos)
    HAE HS S10 ltac:(lia) (am_ew_F g pos c regs2 [kz_desk k]) ltac:(lia) ltac:(lia)). }
split; [exact (oh_reg_lit B TL LAWS E ss W2 _ 11%bv 0 HS S11)|].
split; [exact (oh_reg_lit B TL LAWS E ss W2 _ 12%bv 16 HS S12)|].
exact (oh_reg_lit B TL LAWS E ss W2 _ 1%bv (oh_ret (oh_dk kd)) HS S1).
Qed.

(* ================================ the end at OWEk ================================ *)
Lemma oh_end3 : forall g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c k od kd ys E ss mem3 regs3 md3,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)]
  ly2 S2 W2 mem2 md2 kj ->
frames S2 = [(3, pos)] -> 0 <= kj <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
ops_at ops regs2 -> cur_at g sp1 c W2 mem2 -> k_at g pos k W2 mem2 -> rec_okZ k od ->
kz_kind k = kd -> 0 <= kd <= 11 -> (od = None -> kz_kind k = 1 \/ kz_kind k = 4 \/ kz_kind k = 11) ->
kz_rc k = fst (enc_kZ k od) -> kz_want_rc k = 0 -> kz_want_len k = 0 -> kz_want_key k = 0 ->
kz_want_display k = 0 -> getr regs2 23 = w64 (kz_desk k) ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)]
  ly2 S2 W2 mem3 md3 kj ->
env_agree 38 (am_env g pos c regs2 ys) E ->
st_ok tfibsegs E ss (restrict (w_H W2) (mkst regs3 (Z_to_bv 64 (owe_pc kd)) mem3 (seg_rom tfibsegs))) ->
am_keep_ok (ss_regs ss) = true -> sr_get (ss_regs ss) 26%bv = SOff 26 0 ->
nth_error (ss_mem ss) 4 = Some am_cur_region -> sr_get (ss_regs ss) 23%bv = SOff 23 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ oh_z2 g pos sp1 a ->
 aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
SRr tfibsegs W2 (mkCfg (mkst regs3 (Z_to_bv 64 (owe_pc kd)) mem3 (seg_rom tfibsegs)) md3)
  (fun W3 c3 => exists kind, inv_owe B MT K XM_LIB g pos sp1 ops kind W3 c3).
Proof using TL LAWS AMEMSET ROB.
intros g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c k od kd ys E ss mem3 regs3 md3
  HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hkind Hkd Hod Hrcq Hwrc Hwl Hwk Hwd R23 HJ3 HAE HS
  Hkeep H26 Hcur4 S23 KE.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hng & Hpg & Hpng & _).
change (fs_frame_bytes 3) with 512 in Hfceil. unfold AM_HI in *.
assert (FFS : LLVMF_STK = 32768) by reflexivity.
destruct (oh_fin B MT K XM_LIB TL LAWS g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys E ss
  mem3 regs3 md3 (owe_pc kd) (oh_z2 g pos sp1) HJ Hfr HC Hops Hcur HJ3 HAE HS Hkeep H26 Hcur4
  ltac:(intros a Ha; unfold oh_z2 in Ha; lia) KE) as (HC3 & Hops3 & Hcur3).
pose proof Hkat as [_ HKW].
pose proof HKW as (_ & _ & Wdesk & _).
assert (HK3 : k_at g pos k W2 mem3).
{ apply (oh_k_at_kept g pos k W2 mem2 W2 mem3 Hkat).
  intros a Ha. apply KE; [lia | unfold oh_z2; lia]. }
assert (E23 : ew (am_env g pos c regs2 ys) 23 = Z_to_bv 64 (kz_desk k)).
{ rewrite (am_ew_reg g pos c regs2 ys 23 23%bv eq_refl). exact R23. }
apply SRr_ret. exists kd. unfold inv_owe.
apply (am_mcut B MT K XM_LIB g pos sp1 0 (owe_pc kd) _ ly2 S2 W2 regs3 mem3 md3 kj HJ3 Hfr Hk Hmo HC3).
cbv beta. split; [exact Hops3|]. split; [lia|].
exists c, k, od.
split; [exact Hcur3|]. split; [exact HK3|]. split; [exact Hrec|]. split; [exact Hkind|].
split; [intros Hn; rewrite <- Hkind; exact (Hod Hn)|].
split; [exact Hrcq|]. split; [exact Hwrc|]. split; [exact Hwl|]. split; [exact Hwk|].
split; [exact Hwd|].
exact (oh_reg_off B TL LAWS g pos c regs2 ys E ss W2 _ 23%bv 23 (kz_desk k)
  HAE HS S23 ltac:(lia) E23 ltac:(lia)).
Qed.

(* ================================ the end at 0x82248 from the desk test ================================ *)
Lemma oh_end4 : forall g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c k od ys E ss mem3 regs3 md3,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)]
  ly2 S2 W2 mem2 md2 kj ->
frames S2 = [(3, pos)] -> 0 <= kj <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
ops_at ops regs2 -> cur_at g sp1 c W2 mem2 -> k_at g pos k W2 mem2 -> rec_okZ k od ->
(od = None -> kz_kind k = 1 \/ kz_kind k = 4 \/ kz_kind k = 11) ->
kz_rc k = fst (enc_kZ k od) -> kz_want_rc k = 0 -> kz_want_len k = 0 -> kz_want_key k = 0 ->
kz_want_display k = 0 -> getr regs2 23 = w64 (kz_desk k) -> getr regs2 24 = w64 (kz_kind k) ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)]
  ly2 S2 W2 mem3 md3 kj ->
env_agree 38 (am_env g pos c regs2 ys) E ->
st_ok tfibsegs E ss (restrict (w_H W2) (mkst regs3 (Z_to_bv 64 OH_R1) mem3 (seg_rom tfibsegs))) ->
am_keep_ok (ss_regs ss) = true -> sr_get (ss_regs ss) 26%bv = SOff 26 0 ->
nth_error (ss_mem ss) 4 = Some am_cur_region ->
sr_get (ss_regs ss) 23%bv = SOff 23 0 -> sr_get (ss_regs ss) 24%bv = SOff 24 0 ->
val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 316) 4 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ oh_z3 g pos sp1 a ->
 aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
SRr tfibsegs W2 (mkCfg (mkst regs3 (Z_to_bv 64 OH_R1) mem3 (seg_rom tfibsegs)) md3)
  (oh_mid B MT K XM_LIB g pos sp1 ops true).
Proof using TL LAWS AMEMSET ROB.
intros g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c k od ys E ss mem3 regs3 md3
  HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hod Hrcq Hwrc Hwl Hwk Hwd R23 R24 HJ3 HAE HS
  Hkeep H26 Hcur4 S23 S24 V316 KE.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hng & Hpg & Hpng & _).
change (fs_frame_bytes 3) with 512 in Hfceil. unfold AM_HI in *.
assert (FFS : LLVMF_STK = 32768) by reflexivity.
destruct (oh_fin B MT K XM_LIB TL LAWS g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys E ss
  mem3 regs3 md3 OH_R1 (oh_z3 g pos sp1) HJ Hfr HC Hops Hcur HJ3 HAE HS Hkeep H26 Hcur4
  ltac:(intros a Ha; unfold oh_z3 in Ha; lia) KE) as (HC3 & Hops3 & Hcur3).
pose proof Hkat as [HKK HKW].
destruct HKK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Vrc & _ & _ & _ & _ & Vwl & Vwk & Vwd).
pose proof HKW as (Wkind & _ & Wdesk & _ & _ & _ & _ & _ & Wrc & _ & Wwl & Wwk & Wwd & _).
assert (KV : forall a n v, a + Z.of_nat n <= FA g pos + 316 \/ FA g pos + 320 <= a ->
  FA g pos + 176 <= a -> a + Z.of_nat n <= FA g pos + 360 ->
  val_mem tfibsegs (mrestrict (w_H W2) mem2) a n v -> val_mem tfibsegs (mrestrict (w_H W2) mem3) a n v).
{ intros a n v H0 H1 H2 Hv. apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 mem3); [|exact Hv].
  intros x Hx. apply KE; [lia | unfold oh_z3; lia]. }
assert (V248 : val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 248) 4 (kz_rc k)).
{ apply (KV _ 4%nat); [left; cbn; lia | lia | cbn; lia |].
  replace (FA g pos + 248) with (FA g pos + 176 + 72) by lia. exact Vrc. }
assert (V344 : val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 344) 8 0).
{ apply (KV _ 8%nat); [right; lia | lia | cbn; lia |].
  replace (FA g pos + 344) with (FA g pos + 176 + 168) by lia. rewrite <- Hwl. exact Vwl. }
assert (V352 : val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 352) 4 0).
{ apply (KV _ 4%nat); [right; lia | lia | cbn; lia |].
  replace (FA g pos + 352) with (FA g pos + 176 + 176) by lia. rewrite <- Hwk. exact Vwk. }
assert (V356 : val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 356) 4 0).
{ apply (KV _ 4%nat); [right; lia | lia | cbn; lia |].
  replace (FA g pos + 356) with (FA g pos + 176 + 180) by lia. rewrite <- Hwd. exact Vwd. }
assert (HK3 : k_at g pos (oh_set k (kz_rc k) 0 (kz_want k) 0 0 0) W2 mem3).
{ apply (oh_k_at_set g pos k W2 mem2 W2 mem3 (kz_rc k) 0 0 0 0 Hkat).
  - intros a Ha. apply KE; [lia | unfold oh_z3; lia].
  - exact V248.
  - exact V316.
  - exact V344.
  - exact V352.
  - exact V356.
  - exact Wrc.
  - lia.
  - lia.
  - lia.
  - lia. }
assert (E23 : ew (am_env g pos c regs2 ys) 23 = Z_to_bv 64 (kz_desk k)).
{ rewrite (am_ew_reg g pos c regs2 ys 23 23%bv eq_refl). exact R23. }
assert (E24 : ew (am_env g pos c regs2 ys) 24 = Z_to_bv 64 (kz_kind k)).
{ rewrite (am_ew_reg g pos c regs2 ys 24 24%bv eq_refl). exact R24. }
pose proof Hrec as (Hkr & _).
apply SRr_ret. unfold oh_mid.
change (oh_ret true) with OH_R1.
apply (am_mcut B MT K XM_LIB g pos sp1 0 OH_R1 _ ly2 S2 W2 regs3 mem3 md3 kj HJ3 Hfr Hk Hmo HC3).
cbv beta. split; [exact Hops3|].
exists c, (oh_set k (kz_rc k) 0 (kz_want k) 0 0 0), od.
split; [exact Hcur3|]. split; [exact HK3|]. split; [exact Hrec|].
split; [intros _ Hn; exact (Hod Hn)|]. split; [discriminate|].
split; [exact Hrcq|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [reflexivity|].
split.
{ exact (oh_reg_off B TL LAWS g pos c regs2 ys E ss W2 _ 23%bv 23 (kz_desk k)
    HAE HS S23 ltac:(lia) E23 ltac:(lia)). }
exact (oh_reg_off B TL LAWS g pos c regs2 ys E ss W2 _ 24%bv 24 (kz_kind k)
  HAE HS S24 ltac:(lia) E24 ltac:(lia)).
Qed.

(* ================================ the end at CHK ================================ *)
Lemma oh_end_chk : forall g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c k ys E ss mem3 regs3 md3,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)]
  ly2 S2 W2 mem2 md2 kj ->
frames S2 = [(3, pos)] -> 0 <= kj <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
ops_at ops regs2 -> cur_at g sp1 c W2 mem2 -> k_at g pos k W2 mem2 -> rec_okZ k None ->
kz_rc k = fst (enc_kZ k None) -> kz_want_len k = 0 -> kz_want_key k = 0 -> kz_want_display k = 0 ->
oh_nd (kz_kind k) = true ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)]
  ly2 S2 W2 mem3 md3 kj ->
env_agree 38 (am_env g pos c regs2 ys) E ->
st_ok tfibsegs E ss (restrict (w_H W2) (mkst regs3 (Z_to_bv 64 PC_CHK) mem3 (seg_rom tfibsegs))) ->
am_keep_ok (ss_regs ss) = true -> sr_get (ss_regs ss) 26%bv = SOff 26 0 ->
nth_error (ss_mem ss) 4 = Some am_cur_region ->
val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 316) 4 (-1) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ oh_z3 g pos sp1 a ->
 aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
SRr tfibsegs W2 (mkCfg (mkst regs3 (Z_to_bv 64 PC_CHK) mem3 (seg_rom tfibsegs)) md3)
  (inv_chk B MT K XM_LIB g pos sp1 ops).
Proof using TL LAWS AMEMSET ROB.
intros g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c k ys E ss mem3 regs3 md3
  HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrcq Hwl Hwk Hwd Hnd HJ3 HAE HS Hkeep H26 Hcur4 V316 KE.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hng & Hpg & Hpng & _).
change (fs_frame_bytes 3) with 512 in Hfceil. unfold AM_HI in *.
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof Hkat as [HKK _].
destruct HKK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Vwl & Vwk & Vwd).
assert (KV : forall a n v, FA g pos + 320 <= a -> a + Z.of_nat n <= FA g pos + 360 ->
  val_mem tfibsegs (mrestrict (w_H W2) mem2) a n v -> val_mem tfibsegs (mrestrict (w_H W2) mem3) a n v).
{ intros a n v H1 H2 Hv. apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 mem3); [|exact Hv].
  intros x Hx. apply KE; [lia | unfold oh_z3; lia]. }
assert (V344 : val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 344) 8 0).
{ apply (KV _ 8%nat); [lia | cbn; lia |].
  replace (FA g pos + 344) with (FA g pos + 176 + 168) by lia. rewrite <- Hwl. exact Vwl. }
assert (V352 : val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 352) 4 0).
{ apply (KV _ 4%nat); [lia | cbn; lia |].
  replace (FA g pos + 352) with (FA g pos + 176 + 176) by lia. rewrite <- Hwk. exact Vwk. }
assert (V356 : val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 356) 4 0).
{ apply (KV _ 4%nat); [lia | cbn; lia |].
  replace (FA g pos + 356) with (FA g pos + 176 + 180) by lia. rewrite <- Hwd. exact Vwd. }
assert (Hfst : fst (owe_kZ k None) = -1).
{ unfold owe_kZ.
  rewrite (oh_spec_arg (kz_kind k) (kz_a k) (kz_b k) (kz_c k) (kz_delta k) (kz_bytes k) (kz_n k) Hnd).
  reflexivity. }
apply (owe_chk_end B MT K XM_LIB LAWS g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys k None 0
  mem3 regs3 md3 E ss (-1) [] 0 0 0 HJ Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrcq HJ3
  ltac:(destruct HAE as (HA & HD); split; [intros nn Hnn; apply HA; lia | exact HD]) HS
  Hkeep H26 Hcur4 eq_refl ltac:(cbn; lia)).
- intros a Ha Hz. apply KE; [exact Ha | intros H3; apply Hz; unfold owe_zone, oh_z3 in *; lia].
- exact V316.
- intros j Hj. cbn in Hj. lia.
- exact V344.
- exact V352.
- exact V356.
- lia.
- lia.
- lia.
- lia.
- apply (owe_want_ok_fail k None ([] ++ skipn (length (@nil Z)) (kz_want k)) (-1) Hfst).
  discriminate.
Qed.

(* ================================ the three pieces ================================ *)
(* one kind of the first piece: the run from JOIN to the memset call *)

Lemma oh_p1 : forall g pos sp1 ops W2 c2, inv_join B MT K XM_LIB g pos sp1 ops W2 c2 ->
SRr tfibsegs W2 c2 (fun W3 c3 => exists dk, oh_call B MT K XM_LIB g pos sp1 ops dk W3 c3).
Proof using TL LAWS AMEMSET ROB.
intros g pos sp1 ops W2 c2 (ly2 & S2 & regs2 & mem2 & md2 & kj & -> & HJ & Hfr & Hk & Hmo & HC &
  (Hops & c & k & od & Hcur & Hkat & Hrec & R10)).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hng & Hpg & Hpng & _).
change (fs_frame_bytes 3) with 512 in Hfceil. unfold AM_HI in *.
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof HC as (Hpre & _ & R2 & _).
pose proof Hrec as (Hkr & _).
remember (am_env g pos c regs2 [kz_desk k]) as E eqn:HEE.
assert (HAE : env_agree 38 (am_env g pos c regs2 [kz_desk k]) E) by (rewrite HEE; apply env_agree_refl).
assert (U2 : bv_unsigned (ew E 2) = sp1).
{ rewrite HEE, (am_ew_reg g pos c regs2 [kz_desk k] 2 2%bv eq_refl), R2. unfold w64.
  apply unsigned_lit_small. lia. }
assert (UF : bv_unsigned (ew E 33) = FA g pos).
{ rewrite HEE, (am_ew_F g pos c regs2 [kz_desk k]). apply unsigned_lit_small. lia. }
assert (D10 : sv_denot E (SOff 10 0) = Z_to_bv 64 (fst (enc_kZ k od))).
{ cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, HEE,
    (am_ew_reg g pos c regs2 [kz_desk k] 10 10%bv eq_refl). exact R10. }
pose proof (oh_start1 B MT K XM_LIB TL LAWS g pos sp1 ly2 S2 W2 regs2 mem2 md2 kj c k (kz_kind k)
  HJ Hfr HC Hcur Hkat eq_refl Hkr) as HS.
rewrite <- HEE in HS.
assert (SHOK : sh_ok tfibsegs CW_Bx [owe_SHk] E (mrestrict (w_H W2) mem2)).
{ apply Forall_cons; [|apply Forall_nil]. rewrite HEE.
  exact (owe_k_shent B MT K XM_LIB LAWS g pos sp1 ly2 S2 W2 regs2 mem2 md2 kj c [kz_desk k] HJ Hfr HC). }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ oh_z1 g pos sp1 a ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
cw_keep_j0 HJ HJ0.
unfold cfg_at. change (w64 PC_JOIN) with (Z_to_bv 64 PC_JOIN).
assert (Ek : kz_kind k = 0 \/ kz_kind k = 1 \/ kz_kind k = 2 \/ kz_kind k = 3 \/ kz_kind k = 4 \/
  kz_kind k = 5 \/ kz_kind k = 6 \/ kz_kind k = 7 \/ kz_kind k = 8 \/ kz_kind k = 9 \/
  kz_kind k = 10 \/ kz_kind k = 11) by lia.
destruct Ek as [Ek|[Ek|[Ek|[Ek|[Ek|[Ek|[Ek|[Ek|[Ek|[Ek|[Ek|Ek]]]]]]]]]]].
all: rewrite Ek in HS.
all: cw_run_to ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2 UF EFA) 0x51e34.
all: cw_keep ltac:(oh_kwr oh_z1 U2 UF).
all: oh_shape HS.
all: oh_fld HS 6%nat 248 4%N UF V248.
all: oh_fld HS 7%nat 316 4%N UF V316.
all: rewrite D10 in V248; apply oh_vm32 in V248.
all: cbn [sv_denot] in V316; apply oh_vm32 in V316.
all: lazymatch type of Ek with _ = ?kdv =>
      lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r3 _ ?m3 _) ?md3) _ =>
      lazymatch type of HS with st_ok _ ?Ev ?ssv _ =>
        apply (oh_end1 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c k od kdv Ev ssv m3 r3 md3
          HJ0 Hfr Hk Hmo HC Hops Hcur Hkat Hrec Ek ltac:(lia) ltac:(eassumption)
          ltac:(env_agree_chain HAE) HS
          ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
          ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
          ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
          V248 V316 KE)
      end end end.
Qed.

(* the table jump: one run per kind, to OWEk *)

Lemma oh_p3a : forall g pos sp1 ops W2 c2, oh_mid B MT K XM_LIB g pos sp1 ops true W2 c2 ->
SRr tfibsegs W2 c2 (fun W3 c3 => exists kind, inv_owe B MT K XM_LIB g pos sp1 ops kind W3 c3).
Proof using TL LAWS AMEMSET ROB.
intros g pos sp1 ops W2 c2 (ly2 & S2 & regs2 & mem2 & md2 & kj & -> & HJ & Hfr & Hk & Hmo & HC &
  (Hops & c & k & od & Hcur & Hkat & Hrec & Hdk1 & Hdk0 & Hrcq & Hwrc & Hwl & Hwk & Hwd & R23 & R24)).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hng & Hpg & Hpng & _).
change (fs_frame_bytes 3) with 512 in Hfceil. unfold AM_HI in *.
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof HC as (Hpre & _ & R2 & _).
pose proof Hrec as (Hkr & _).
assert (Hod : od = None -> kz_kind k = 1 \/ kz_kind k = 4 \/ kz_kind k = 11) by exact (Hdk1 eq_refl).
remember (am_env g pos c regs2 [kz_desk k]) as E eqn:HEE.
assert (HAE : env_agree 38 (am_env g pos c regs2 [kz_desk k]) E) by (rewrite HEE; apply env_agree_refl).
assert (U2 : bv_unsigned (ew E 2) = sp1).
{ rewrite HEE, (am_ew_reg g pos c regs2 [kz_desk k] 2 2%bv eq_refl), R2. unfold w64.
  apply unsigned_lit_small. lia. }
assert (UF : bv_unsigned (ew E 33) = FA g pos).
{ rewrite HEE, (am_ew_F g pos c regs2 [kz_desk k]). apply unsigned_lit_small. lia. }
pose proof (oh_start3 B MT K XM_LIB TL LAWS g pos sp1 ly2 S2 W2 regs2 mem2 md2 kj c [kz_desk k]
  (kz_kind k) HJ Hfr HC Hcur R24) as HS.
rewrite <- HEE in HS.
assert (SHOK : sh_ok tfibsegs CW_Bx [owe_SHk] E (mrestrict (w_H W2) mem2)).
{ apply Forall_cons; [|apply Forall_nil]. rewrite HEE.
  exact (owe_k_shent B MT K XM_LIB LAWS g pos sp1 ly2 S2 W2 regs2 mem2 md2 kj c [kz_desk k] HJ Hfr HC). }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ oh_z2 g pos sp1 a ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
cw_keep_j0 HJ HJ0.
change (oh_ret true) with OH_R1.
unfold cfg_at. change (w64 OH_R1) with (Z_to_bv 64 OH_R1).
assert (Ek : kz_kind k = 0 \/ kz_kind k = 1 \/ kz_kind k = 2 \/ kz_kind k = 3 \/ kz_kind k = 4 \/
  kz_kind k = 5 \/ kz_kind k = 6 \/ kz_kind k = 7 \/ kz_kind k = 8 \/ kz_kind k = 9 \/
  kz_kind k = 10 \/ kz_kind k = 11) by lia.
destruct Ek as [Ek|[Ek|[Ek|[Ek|[Ek|[Ek|[Ek|[Ek|[Ek|[Ek|[Ek|Ek]]]]]]]]]]].
all: rewrite Ek in HS.
all: lazymatch type of Ek with _ = ?kdv =>
      let p := eval vm_compute in (owe_pc kdv) in
      cw_run_to ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2 UF EFA) p end.
all: cw_keep ltac:(oh_kwr oh_z2 U2 UF).
all: oh_shape HS.
all: lazymatch type of Ek with _ = ?kdv =>
      lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r3 _ ?m3 _) ?md3) _ =>
      lazymatch type of HS with st_ok _ ?Ev ?ssv _ =>
        apply (oh_end3 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c k od kdv [kz_desk k] Ev ssv
          m3 r3 md3 HJ0 Hfr Hk Hmo HC Hops Hcur Hkat Hrec Ek ltac:(lia) Hod Hrcq Hwrc Hwl Hwk Hwd R23
          ltac:(eassumption) ltac:(env_agree_chain HAE) HS
          ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
          ltac:(vm_compute; reflexivity) KE)
      end end end.
Qed.

(* the desk test *)
Lemma oh_p3b : forall g pos sp1 ops W2 c2, oh_mid B MT K XM_LIB g pos sp1 ops false W2 c2 ->
SRr tfibsegs W2 c2 (fun W3 c3 => inv_chk B MT K XM_LIB g pos sp1 ops W3 c3 \/
  exists kind, inv_owe B MT K XM_LIB g pos sp1 ops kind W3 c3).
Proof using TL LAWS AMEMSET ROB.
intros g pos sp1 ops W2 c2 (ly2 & S2 & regs2 & mem2 & md2 & kj & -> & HJ & Hfr & Hk & Hmo & HC &
  (Hops & c & k & od & Hcur & Hkat & Hrec & Hdk1 & Hdk0 & Hrcq & Hwrc & Hwl & Hwk & Hwd & R23 & R24)).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hng & Hpg & Hpng & _).
change (fs_frame_bytes 3) with 512 in Hfceil. unfold AM_HI in *.
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof HC as (Hpre & _ & R2 & _).
pose proof Hrec as (Hkr & Hpd & _).
pose proof Hkat as [_ HKW].
pose proof HKW as (Wkind & _ & Wdesk & _).
assert (Hnd : oh_nd (kz_kind k) = true) by exact (Hdk0 eq_refl).
remember (am_env g pos c regs2 [kz_desk k]) as E eqn:HEE.
assert (HAE : env_agree 38 (am_env g pos c regs2 [kz_desk k]) E) by (rewrite HEE; apply env_agree_refl).
assert (U2 : bv_unsigned (ew E 2) = sp1).
{ rewrite HEE, (am_ew_reg g pos c regs2 [kz_desk k] 2 2%bv eq_refl), R2. unfold w64.
  apply unsigned_lit_small. lia. }
assert (UF : bv_unsigned (ew E 33) = FA g pos).
{ rewrite HEE, (am_ew_F g pos c regs2 [kz_desk k]). apply unsigned_lit_small. lia. }
assert (E23 : ew E 23 = Z_to_bv 64 (kz_desk k)).
{ rewrite HEE, (am_ew_reg g pos c regs2 [kz_desk k] 23 23%bv eq_refl). exact R23. }
pose proof (oh_start4 B MT K XM_LIB TL LAWS g pos sp1 ly2 S2 W2 regs2 mem2 md2 kj c [kz_desk k] k
  HJ Hfr HC Hcur Hkat Hwrc) as HS.
rewrite <- HEE in HS.
assert (SHOK : sh_ok tfibsegs CW_Bx [owe_SHk] E (mrestrict (w_H W2) mem2)).
{ apply Forall_cons; [|apply Forall_nil]. rewrite HEE.
  exact (owe_k_shent B MT K XM_LIB LAWS g pos sp1 ly2 S2 W2 regs2 mem2 md2 kj c [kz_desk k] HJ Hfr HC). }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ oh_z3 g pos sp1 a ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
cw_keep_j0 HJ HJ0.
change (oh_ret false) with OH_R0.
unfold cfg_at. change (w64 OH_R0) with (Z_to_bv 64 OH_R0).
cw_run ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2 UF EFA).
cw_keep ltac:(oh_kwr oh_z3 U2 UF).
cw_branch Hb.
all: rewrite branch_ne_U, U_lit, (cw_U_atom0 E 23 (kz_desk k) E23 ltac:(lia)) in Hb by lia.
- (* k.desk <> 0: owe()'s table *)
  apply negb_true_iff, Z.eqb_neq in Hb.
  cw_run_to ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2 UF EFA) 0x82248.
  cw_keep ltac:(oh_kwr oh_z3 U2 UF).
  oh_shape HS.
  oh_fld HS 5%nat 316 4%N UF V316.
  cbn [sv_denot] in V316. apply oh_vm32 in V316.
  eapply SRr_bind.
  { lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r3 _ ?m3 _) ?md3) _ =>
    lazymatch type of HS with st_ok _ ?Ev ?ssv _ =>
      apply (oh_end4 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c k od [kz_desk k] Ev ssv m3 r3 md3
        HJ0 Hfr Hk Hmo HC Hops Hcur Hkat Hrec
        ltac:(intros Hn; destruct Hpd as [(_ & Hd & _) | [(_ & _ & Hs) | (_ & _ & Hs)]];
              [exfalso; apply Hb; exact Hd | rewrite Hn in Hs; discriminate
              | rewrite Hn in Hs; discriminate])
        Hrcq Hwrc Hwl Hwk Hwd R23 R24 ltac:(eassumption) ltac:(env_agree_chain HAE) HS
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) V316 KE)
    end end. }
  cbv beta. intros W4 c4 _ Hmid.
  eapply SRr_mono; [exact (oh_p3a g pos sp1 ops W4 c4 Hmid)|].
  intros W5 c5 _ H5. right. exact H5.
- (* k.desk = 0: a NULL desk, so owe() refuses with E_ARG *)
  apply negb_false_iff, Z.eqb_eq in Hb.
  assert (Hnone : od = None).
  { destruct Hpd as [(_ & _ & Hn) | [(_ & Hd & _) | (_ & Hd & _)]];
    [exact Hn | unfold CM_SPEC_C24 in Hd; lia | unfold CM_SPEC_PC in Hd; lia]. }
  subst od.
  cw_run_to ltac:(owe_awr sp1 (e_sp0 g) pos (FA g pos) U2 UF EFA) 0x8273c.
  cw_keep ltac:(oh_kwr oh_z3 U2 UF).
  oh_shape HS.
  oh_fld HS 5%nat 316 4%N UF V316.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r3 _ ?m3 _) ?md3) _ =>
  lazymatch type of HS with st_ok _ ?Ev ?ssv _ =>
    eapply SRr_mono;
    [ apply (oh_end_chk g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c k [kz_desk k] Ev ssv m3 r3 md3
        HJ0 Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrcq Hwl Hwk Hwd Hnd
        ltac:(eassumption) ltac:(env_agree_chain HAE) HS
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        ltac:(apply (owe_vm _ _ 4 _ _ V316); vm_compute; reflexivity) KE)
    | intros W5 c5 _ H5; left; exact H5 ]
  end end.
Qed.

(* ================================ the segment ================================ *)
Theorem seg_oweh_holds : seg_oweh B MT K XM_LIB.
Proof using TL LAWS AMEMSET ROB.
unfold seg_oweh. intros g pos sp1 ops W2 c2 Hst.
eapply SRr_bind; [exact (oh_p1 g pos sp1 ops W2 c2 Hst)|].
cbv beta. intros W3 c3 _ (dk & Hcall).
eapply SRr_bind; [exact (oh_memset B MT K XM_LIB TL LAWS AMEMSET g pos sp1 ops dk W3 c3 Hcall)|].
cbv beta. intros W4 c4 _ Hmid. destruct dk.
- eapply SRr_mono; [exact (oh_p3a g pos sp1 ops W4 c4 Hmid)|].
  intros W5 c5 _ H5. right. exact H5.
- exact (oh_p3b g pos sp1 ops W4 c4 Hmid).
Qed.
End b.
End a.
