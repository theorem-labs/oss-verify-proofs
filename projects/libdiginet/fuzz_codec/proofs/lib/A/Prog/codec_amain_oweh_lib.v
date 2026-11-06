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
(* The pieces of segment OWEH of the image-A walk of LLVMFuzzerTestOneInput (lib/A/Prog/codec_amain_inv.v
   seg_oweh): owe()'s common part, from JOIN 0x8220c to OWEk (owe()'s table at 0x20f10) or to CHK.
     0x8220c lw s8,0(s6)        the kind (s6 = k = F + 176)
     0x82210 ld s7,16(s6)       k.desk
     0x82214 sw a0,72(s6)       k.rc = the encoder's code
     0x8221c bltu 11,s8         never taken (0 <= kind <= 11)
     0x82220-0x82230            (0x812 >> kind) & 1: the kinds that take a NULL desk (1, 4, 11)
     0x82234 / 0x822d4          want_rc = 0, then __asan_memset(k + 168, 0, 16) at 0x82244 / 0x822e4
     0x82248 (bit set) or 0x822e8 (bit clear, then `bnez s7` to 0x82248 when k.desk <> 0)
     0x82248 bltu 10,s8 -> 0x827c8, else owe()'s table at 0x20f10 -> owe_pc kind
     0x827d4-0x827dc            want_rc = -1, to CHK (a kind that needs a desk with a NULL desk)
   The walk is cut at the call of the runtime's checked memset (its state oh_call) and at its return
   (oh_mid): the executor runs the three straight pieces, and the call itself is taken semantically
   (aj_intrin_atS and the caller-journal facts of lib/A/Prog/codec_amain_encl.v).
   This file holds what the three pieces share: the record k after a field is written (oh_k_at_set), the
   bridge from a stopped executor state back to a cut (oh_fin), the memset step (oh_memset) and the start
   and end of each piece. The runs themselves are in lib/A/Prog/codec_amain_oweh.v. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_encl codec_amain_owel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ================================ the addresses and the kind test ================================ *)
(* owe()'s table of cases (11 words, read from the pinned image) *)
Definition OH_TBL : Z := 0x20f10.
(* the two return addresses of the memset call: 0x82244 (the kinds that take a NULL desk) and 0x822e4 *)
Definition OH_R1 : Z := 0x82248.
Definition OH_R0 : Z := 0x822e8.
(* the mask 0x812 at 0x82224: bit kind set means the kind takes a NULL desk (BUTTON, JOG, SYSEX) *)
Definition oh_nd (kind : Z) : bool := negb ((kind =? 1) || (kind =? 4) || (kind =? 11)).
Definition oh_dk (kind : Z) : bool := negb (oh_nd kind).
Definition oh_ret (dk : bool) : Z := if dk then OH_R1 else OH_R0.

(* k with rc, want_rc, want, want_len, want_key and want_display replaced *)
Definition oh_set (k : kcallZ) (r0 r : Z) (w : list Z) (l key dp : Z) : kcallZ :=
mkKcallZ (kz_kind k) (kz_p k) (kz_desk k) (kz_a k) (kz_b k) (kz_c k) (kz_delta k)
         (kz_bytes k) (kz_n k) r0 (kz_before k) (kz_out k) r w l key dp.

Lemma oh_set_id : forall k,
oh_set k (kz_rc k) (kz_want_rc k) (kz_want k) (kz_want_len k) (kz_want_key k) (kz_want_display k) = k.
Proof. intros []. reflexivity. Qed.

(* owe()'s answer for a kind that needs a desk, with a NULL desk (fuzz_codec.c:113-131) *)
Lemma oh_spec_arg : forall kind a b c delta bytes n, oh_nd kind = true ->
owe_spec kind None a b c delta bytes n = (-1, noc).
Proof.
intros kind a b c delta bytes n H. unfold oh_nd in H. unfold owe_spec. cbv zeta beta.
rewrite H. reflexivity.
Qed.

(* ================================ the regions of the three pieces ================================ *)
(* k's kind (F + 176) and k.desk (F + 192) read, the window of k.rc (F + 248) and of want_rc (F + 316) *)
Definition oh_rk (kd : Z) : YP09.region :=
am_frame_region 176 200 176 176
[YP09.mkChunk 176 (CVal 4 (SLit kd)); YP09.mkChunk 192 (CVal 8 (SOff 37 0))].
Definition oh_rrc : YP09.region := am_frame_region 248 252 248 252 [].
Definition oh_rw : YP09.region := am_frame_region 316 320 316 320 [].
Definition oh_rwz : YP09.region := am_frame_region 316 320 316 320 [YP09.mkChunk 316 (CVal 4 (SLit 0))].
(* owe()'s table, as bytes of the image *)
Definition oh_rt : YP09.region := cpg_img_region OH_TBL 44.
Definition oh_ss3 (kd : Z) : sstate :=
mkSS OH_R1 (sr_set am_sregs 24%bv (SLit kd)) (am_regs ++ [oh_rt]) None (mkFacts (am_atoms ++ []) [] []).

(* the bytes each piece may write: the cursor's window, k.rc, want_rc *)
Definition oh_z1 (g : ectx) (pos sp1 a : Z) : Prop :=
(sp1 + 152 <= a < sp1 + 168) \/ (FA g pos + 248 <= a < FA g pos + 252) \/
(FA g pos + 316 <= a < FA g pos + 320).
Definition oh_z2 (g : ectx) (pos sp1 a : Z) : Prop := sp1 + 152 <= a < sp1 + 168.
Definition oh_z3 (g : ectx) (pos sp1 a : Z) : Prop :=
(sp1 + 152 <= a < sp1 + 168) \/ (FA g pos + 316 <= a < FA g pos + 320).

(* the write windows of a state lie in the zone (U2 / UF: atoms 2 and 33 are sp1 and F) *)
Ltac oh_kwr zone U2 UF :=
  idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a (r & Hr & Hb); cbv beta; unfold zone;
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  repeat (destruct Hr as [<- | Hr];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?U2, ?UF in Hb; lia | ]);
  destruct Hr.
(* a field of the region i of a stopped state *)
Ltac oh_fld HS i off w UF V :=
  let Hr := fresh "Hr" in
  owe_region HS i Hr; rewrite restrict_mkst_fx in Hr; cbn [ms_mem] in Hr;
  pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ off w _ Hr UF ltac:(owe_in) ltac:(lia)) as V;
  clear Hr.
(* the stopped state as a mkst *)
Ltac oh_shape HS :=
  let Ems := fresh "Ems" in
  pose proof (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl) as Ems;
  rewrite Ems in HS; rewrite Ems; clear Ems.

(* ================================ the record after a field is written ================================ *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.

(* a byte of a 4-byte field read back modulo 2 ^ 32 (the executor's value of a register) *)
Lemma oh_vm32 : forall m a (v : Z),
val_mem tfibsegs m a 4 (bv_unsigned (Z_to_bv 64 v) mod 2 ^ (8 * Z.of_N 4)) -> val_mem tfibsegs m a 4 v.
Proof.
intros m a v H. apply (owe_vm _ _ 4 _ _ H).
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32).
rewrite Z.mod_mod by lia.
pose proof (Z.div_mod v (2 ^ 64) ltac:(lia)) as D.
replace (v mod 2 ^ 32) with ((2 ^ 64 * (v / 2 ^ 64) + v mod 2 ^ 64) mod 2 ^ 32) by (rewrite <- D; reflexivity).
replace (2 ^ 64 * (v / 2 ^ 64)) with ((2 ^ 32 * (v / 2 ^ 64)) * 2 ^ 32) by lia.
rewrite Z.add_comm, Z.mod_add by lia. reflexivity.
Qed.

(* bytes the runtime's memset set to zero *)
Lemma oh_le_byte_0 : forall w k, YO0f.le_byte 0 w k = 0.
Proof.
intros w k. unfold YO0f.le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia).
rewrite Z.shiftr_0_l. reflexivity.
Qed.
Lemma oh_val_zero : forall (W : world tfibsegs) mem q (n : nat),
(forall i, 0 <= i < Z.of_nat n -> aview tfibsegs (w_H W) mem (q + i) = Some 0) ->
val_mem tfibsegs (mrestrict (w_H W) mem) q n 0.
Proof.
intros W mem q n H j Hj.
destruct (am_mb W mem (q + Z.of_nat j) 0 (H (Z.of_nat j) ltac:(lia))) as (Hm & _).
rewrite Hm, oh_le_byte_0. reflexivity.
Qed.

(* k_at of the record with rc (q + 72), want_rc (q + 140), want_len, want_key and want_display replaced,
   from the bytes of k outside those fields kept and the fields read in the later memory *)
Lemma oh_k_at_set : forall g pos k (W2 : world tfibsegs) mem2 (W3 : world tfibsegs) mem3 r0 r l key dp,
k_at g pos k W2 mem2 ->
(forall a, FA g pos + 176 <= a < FA g pos + 248 \/ FA g pos + 252 <= a < FA g pos + 316 \/
           FA g pos + 320 <= a < FA g pos + 344 ->
 aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
val_mem tfibsegs (mrestrict (w_H W3) mem3) (FA g pos + 248) 4 r0 ->
val_mem tfibsegs (mrestrict (w_H W3) mem3) (FA g pos + 316) 4 r ->
val_mem tfibsegs (mrestrict (w_H W3) mem3) (FA g pos + 344) 8 l ->
val_mem tfibsegs (mrestrict (w_H W3) mem3) (FA g pos + 352) 4 key ->
val_mem tfibsegs (mrestrict (w_H W3) mem3) (FA g pos + 356) 4 dp ->
- 2 ^ 31 <= r0 < 2 ^ 31 -> - 2 ^ 31 <= r < 2 ^ 31 -> 0 <= l < 2 ^ 64 -> 0 <= key < 2 ^ 32 ->
- 2 ^ 31 <= dp < 2 ^ 31 ->
k_at g pos (oh_set k r0 r (kz_want k) l key dp) W3 mem3.
Proof.
intros g pos k W2 mem2 W3 mem3 r0 r l key dp [HK HW] KE Vr0 Vr Vl Vkey Vdp Hr0 Hr Hl Hkey Hdp.
destruct HK as (Vkind & Vp & Vdesk & Va & Vb & Vc & Vdelta & Gbytes & Vn & Vrc & Gbefore & Gout &
  Vwrc & Gwant & Vwl & Vwk & Vwd).
pose proof HW as (Wkind & Wp & Wdesk & Wa & Wb & Wc & Wdelta & Wn & Wrc & Wwrc & Wwl & Wwk & Wwd &
  Lbytes & Lbefore & Lout & Lwant).
assert (VK : forall o n v, 0 <= o ->
  (o + Z.of_nat n <= 72 \/ (76 <= o /\ o + Z.of_nat n <= 140) \/ (144 <= o /\ o + Z.of_nat n <= 168)) ->
  val_mem tfibsegs (mrestrict (w_H W2) mem2) (FA g pos + 176 + o) n v ->
  val_mem tfibsegs (mrestrict (w_H W3) mem3) (FA g pos + 176 + o) n v).
{ intros o n v Ho Hn Hv. apply (cw_val_mem_kept (w_H W2) (w_H W3) mem2 mem3); [|exact Hv].
  intros x Hx. apply KE. lia. }
assert (GK : forall o l', 0 <= o ->
  (o + Z.of_nat (length l') <= 72 \/ (76 <= o /\ o + Z.of_nat (length l') <= 140) \/
   (144 <= o /\ o + Z.of_nat (length l') <= 168)) ->
  garr8 tfibsegs (mrestrict (w_H W2) mem2) (FA g pos + 176 + o) l' ->
  garr8 tfibsegs (mrestrict (w_H W3) mem3) (FA g pos + 176 + o) l').
{ intros o l' Ho Hn Hg. apply (owe_garr8_kept (w_H W2) (w_H W3) mem2 mem3); [|exact Hg].
  intros x Hx. apply KE. lia. }
split.
- unfold kcall_atA.
  cbn [kz_kind kz_p kz_desk kz_a kz_b kz_c kz_delta kz_bytes kz_n kz_rc kz_before kz_out
    kz_want_rc kz_want kz_want_len kz_want_key kz_want_display oh_set].
  split; [rewrite <- (Z.add_0_r (FA g pos + 176)); apply VK; [lia | cbn; lia | rewrite Z.add_0_r; exact Vkind]|].
  split; [apply VK; [lia | cbn; lia | exact Vp]|].
  split; [apply VK; [lia | cbn; lia | exact Vdesk]|].
  split; [apply VK; [lia | cbn; lia | exact Va]|].
  split; [apply VK; [lia | cbn; lia | exact Vb]|].
  split; [apply VK; [lia | cbn; lia | exact Vc]|].
  split; [apply VK; [lia | cbn; lia | exact Vdelta]|].
  split; [apply GK; [lia | rewrite Lbytes; cbn; lia | exact Gbytes]|].
  split; [apply VK; [lia | cbn; lia | exact Vn]|].
  split; [replace (FA g pos + 176 + 72) with (FA g pos + 248) by lia; exact Vr0|].
  split; [apply GK; [lia | rewrite Lbefore; cbn; lia | exact Gbefore]|].
  split; [apply GK; [lia | rewrite Lout; cbn; lia | exact Gout]|].
  split; [replace (FA g pos + 176 + 140) with (FA g pos + 316) by lia; exact Vr|].
  split; [apply GK; [lia | rewrite Lwant; cbn; lia | exact Gwant]|].
  split; [replace (FA g pos + 176 + 168) with (FA g pos + 344) by lia; exact Vl|].
  split; [replace (FA g pos + 176 + 176) with (FA g pos + 352) by lia; exact Vkey|].
  replace (FA g pos + 176 + 180) with (FA g pos + 356) by lia. exact Vdp.
- unfold kcall_wfZ.
  cbn [kz_kind kz_p kz_desk kz_a kz_b kz_c kz_delta kz_bytes kz_n kz_rc kz_before kz_out
    kz_want_rc kz_want kz_want_len kz_want_key kz_want_display oh_set].
  repeat split; first [assumption | lia].
Qed.

(* the same record in a later memory that kept all of its 184 bytes *)
Lemma oh_k_at_kept : forall g pos k (W2 : world tfibsegs) mem2 (W3 : world tfibsegs) mem3,
k_at g pos k W2 mem2 ->
(forall a, FA g pos + 176 <= a < FA g pos + 360 ->
 aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
k_at g pos k W3 mem3.
Proof.
intros g pos k W2 mem2 W3 mem3 Hkat KE.
pose proof Hkat as [HK HW].
destruct HK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Vrc & _ & _ & Vwrc & _ & Vwl & Vwk & Vwd).
pose proof HW as (_ & _ & _ & _ & _ & _ & _ & _ & Wrc & Wwrc & Wwl & Wwk & Wwd & _).
assert (VK : forall o n v, 0 <= o -> o + Z.of_nat n <= 184 ->
  val_mem tfibsegs (mrestrict (w_H W2) mem2) (FA g pos + 176 + o) n v ->
  val_mem tfibsegs (mrestrict (w_H W3) mem3) (FA g pos + 176 + o) n v).
{ intros o n v Ho Hn Hv. apply (cw_val_mem_kept (w_H W2) (w_H W3) mem2 mem3); [|exact Hv].
  intros x Hx. apply KE. lia. }
assert (V248 : val_mem tfibsegs (mrestrict (w_H W3) mem3) (FA g pos + 248) 4 (kz_rc k)).
{ replace (FA g pos + 248) with (FA g pos + 176 + 72) by lia. apply VK; [lia | cbn; lia | exact Vrc]. }
assert (V316 : val_mem tfibsegs (mrestrict (w_H W3) mem3) (FA g pos + 316) 4 (kz_want_rc k)).
{ replace (FA g pos + 316) with (FA g pos + 176 + 140) by lia. apply VK; [lia | cbn; lia | exact Vwrc]. }
assert (V344 : val_mem tfibsegs (mrestrict (w_H W3) mem3) (FA g pos + 344) 8 (kz_want_len k)).
{ replace (FA g pos + 344) with (FA g pos + 176 + 168) by lia. apply VK; [lia | cbn; lia | exact Vwl]. }
assert (V352 : val_mem tfibsegs (mrestrict (w_H W3) mem3) (FA g pos + 352) 4 (kz_want_key k)).
{ replace (FA g pos + 352) with (FA g pos + 176 + 176) by lia. apply VK; [lia | cbn; lia | exact Vwk]. }
assert (V356 : val_mem tfibsegs (mrestrict (w_H W3) mem3) (FA g pos + 356) 4 (kz_want_display k)).
{ replace (FA g pos + 356) with (FA g pos + 176 + 180) by lia. apply VK; [lia | cbn; lia | exact Vwd]. }
pose proof (oh_k_at_set g pos k W2 mem2 W3 mem3 (kz_rc k) (kz_want_rc k) (kz_want_len k) (kz_want_key k)
  (kz_want_display k) Hkat ltac:(intros a Ha; apply KE; lia) V248 V316 V344 V352 V356 Wrc Wwrc Wwl Wwk Wwd) as H.
rewrite (oh_set_id k) in H. exact H.
Qed.

Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.

(* ================================ the two cuts inside the segment ================================ *)
(* at the call of the runtime's checked memset (0x51e34): k.rc written, want_rc = 0, the arguments set *)
Definition oh_call (g : ectx) (pos sp1 ops : Z) (dk : bool) : world tfibsegs -> config -> Prop :=
mcut B MT K XM_LIB g pos sp1 0 CA_MEMSET (fun ly2 S2 W2 regs2 mem2 md2 =>
ops_at ops regs2 /\
exists c k od, cur_at g sp1 c W2 mem2 /\ k_at g pos k W2 mem2 /\ rec_okZ k od /\
(dk = true -> od = None -> kz_kind k = 1 \/ kz_kind k = 4 \/ kz_kind k = 11) /\
(dk = false -> oh_nd (kz_kind k) = true) /\
kz_rc k = fst (enc_kZ k od) /\ kz_want_rc k = 0 /\
getr regs2 23 = w64 (kz_desk k) /\ getr regs2 24 = w64 (kz_kind k) /\
getr regs2 10 = w64 (FA g pos + 344) /\
getr regs2 11 = w64 0 /\ getr regs2 12 = w64 16 /\ getr regs2 1 = w64 (oh_ret dk)).

(* at the return of that call: the want fields are 0 as well *)
Definition oh_mid (g : ectx) (pos sp1 ops : Z) (dk : bool) : world tfibsegs -> config -> Prop :=
mcut B MT K XM_LIB g pos sp1 0 (oh_ret dk) (fun ly2 S2 W2 regs2 mem2 md2 =>
ops_at ops regs2 /\
exists c k od, cur_at g sp1 c W2 mem2 /\ k_at g pos k W2 mem2 /\ rec_okZ k od /\
(dk = true -> od = None -> kz_kind k = 1 \/ kz_kind k = 4 \/ kz_kind k = 11) /\
(dk = false -> oh_nd (kz_kind k) = true) /\
kz_rc k = fst (enc_kZ k od) /\ kz_want_rc k = 0 /\ kz_want_len k = 0 /\ kz_want_key k = 0 /\
kz_want_display k = 0 /\ getr regs2 23 = w64 (kz_desk k) /\ getr regs2 24 = w64 (kz_kind k)).

(* ================================ the frame's shadow and its bytes ================================ *)
(* the shadow bytes of a range of the frame are readable (the cut's 56 shadow bytes cover their hull) *)
Lemma oh_hull : forall g pos sp1 kv ly2 S2 (W2 : world tfibsegs) regs2 mem2 md2 off n,
mcommon B MT K XM_LIB g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 ->
0 <= off -> 0 < n -> off + n <= 448 ->
shadow_hull_vis (aview tfibsegs (w_H W2) mem2) (FA g pos + off) n.
Proof using TL LAWS ROB.
intros g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 off n HC Hoff Hn Hon.
pose proof HC as HF64. do 14 (destruct HF64 as (_ & HF64)). destruct HF64 as (HF64 & _).
pose proof HC as HSH. do 43 (destruct HSH as (_ & HSH)). destruct HSH as (HSH' & _).
set (F := FA g pos) in *.
assert (D64 : F = 64 * (F / 64)) by (pose proof (Z.div_mod F 64 ltac:(lia)) as D; lia).
assert (E8 : F / 8 = 8 * (F / 64)).
{ rewrite D64 at 1. replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia. apply Z.div_mul. lia. }
assert (DF : forall m, (F + m) / 8 = F / 8 + m / 8).
{ intros m. replace (F + m) with ((F / 8) * 8 + m) by lia. apply Z.div_add_l. lia. }
assert (Hq : exists q, SHADOW_OFF + F / 8 = 8 * q).
{ exists (268431360 + F / 64). unfold SHADOW_OFF. lia. }
destruct Hq as (q & Hq).
intros s Hs. unfold shadow_addr in Hs.
replace (F + off + n - 1) with (F + (off + n - 1)) in Hs by lia.
rewrite !DF in Hs.
replace (SHADOW_OFF + (F / 8 + off / 8)) with (8 * q + off / 8) in Hs by lia.
replace (SHADOW_OFF + (F / 8 + (off + n - 1) / 8)) with (8 * q + (off + n - 1) / 8) in Hs by lia.
assert (Hu1 : 0 <= off / 8) by (apply Z.div_pos; lia).
assert (Hu2 : (off + n - 1) / 8 <= 55).
{ assert (T1 : (off + n - 1) / 8 <= 447 / 8) by (apply Z.div_le_mono; lia).
  assert (T2 : 447 / 8 = 55) by reflexivity. lia. }
assert (Hw1 : 0 <= (off + n - 1) / 8) by (apply Z.div_pos; lia).
assert (R1 : (8 * q + off / 8) / 8 * 8 = 8 * q + off / 8 / 8 * 8)
  by (rewrite (Z.mul_comm 8 q), Z.div_add_l by lia; lia).
assert (R2 : (8 * q + (off + n - 1) / 8) / 8 * 8 = 8 * q + (off + n - 1) / 8 / 8 * 8)
  by (rewrite (Z.mul_comm 8 q), Z.div_add_l by lia; lia).
rewrite R1, R2 in Hs.
assert (H1 : 0 <= off / 8 / 8 * 8) by (pose proof (Z.div_pos (off / 8) 8 ltac:(lia) ltac:(lia)); lia).
assert (H2 : (off + n - 1) / 8 / 8 <= 6).
{ assert (T3 : (off + n - 1) / 8 / 8 <= 55 / 8) by (apply Z.div_le_mono; lia).
  assert (T4 : 55 / 8 = 6) by reflexivity. lia. }
assert (Hi : 0 <= s - (8 * q) < 56) by lia.
replace s with (shadow_addr F + (s - 8 * q)) by (unfold shadow_addr; lia).
rewrite (HSH' (s - 8 * q) Hi).
discriminate.
Qed.

(* a byte of the entry's own frame is none of the image's *)
Lemma oh_frame_not_img : forall pos F ly2 S2 (W2 : world tfibsegs) mem2 md2 a,
AR tfibsegs B ly2 S2 W2 mem2 md2 -> In (3, pos) (frames S2) -> frame_addr ly2 3 pos = F ->
F <= a < F + 512 -> in_img tfibsegs a -> False.
Proof using TL LAWS ROB.
intros pos F ly2 S2 W2 mem2 md2 a HAR Hin EFA Ha Him.
pose proof (al_client_img _ _ LAWS ly2 S2 W2 mem2 md2 a HAR) as Hc.
apply Hc; [|exact Him]. right. left. exists 3, pos. split; [exact Hin|].
unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 3) with 512. lia.
Qed.

(* ================================ the bridge back to a cut ================================ *)
(* From a stopped executor state whose run wrote only bytes of Zn (inside the cursor's window or k), the
   facts every cut of the segment carries: mcommon, the pass counter and the cursor. *)
Lemma oh_fin : forall g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys E ss mem3 regs3 md3 pcv (Zn : Z -> Prop),
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)]
  ly2 S2 W2 mem2 md2 kj ->
frames S2 = [(3, pos)] ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
ops_at ops regs2 -> cur_at g sp1 c W2 mem2 ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)]
  ly2 S2 W2 mem3 md3 kj ->
env_agree 38 (am_env g pos c regs2 ys) E ->
st_ok tfibsegs E ss (restrict (w_H W2) (mkst regs3 (Z_to_bv 64 pcv) mem3 (seg_rom tfibsegs))) ->
am_keep_ok (ss_regs ss) = true -> sr_get (ss_regs ss) 26%bv = SOff 26 0 ->
nth_error (ss_mem ss) 4 = Some am_cur_region ->
(forall a, Zn a -> (sp1 + 152 <= a < sp1 + 168) \/ (FA g pos + 176 <= a < FA g pos + 360)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Zn a ->
 aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs3 mem3 md3 /\ ops_at ops regs3 /\ cur_at g sp1 c W2 mem3.
Proof using TL LAWS ROB.
intros g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys E ss mem3 regs3 md3 pcv Zn
  HJ Hfr HC Hops Hcur HJ3 HAE HS Hkeep H26 Hcur4 HZ KE.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & _).
pose proof (owe_frame_app B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as Happ.
change (fs_frame_bytes 3) with 512 in Hfceil.
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold AM_HI in *.
pose proof HAE as (HA & HD).
assert (HAE35 : env_agree 35 (am_env g pos c regs2 ys) E)
  by (split; [intros nn Hnn; apply HA; lia | exact HD]).
pose proof HC as (_ & _ & R2 & _).
pose proof HC as HSH. do 43 (destruct HSH as (_ & HSH)). destruct HSH as (HSH & _).
pose proof HC as HPm. do 45 (destruct HPm as (_ & HPm)).
assert (D8 : 0 <= FA g pos / 8 /\ 8 * (FA g pos / 8) <= FA g pos)
  by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
assert (Hzsh : forall i, 0 <= i < 56 -> ~ Zn (shadow_addr (FA g pos) + i)).
{ intros i Hi Hz. destruct (HZ _ Hz) as [H | H]; unfold shadow_addr, SHADOW_OFF in H; appn; lia. }
assert (HMC : mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs3 mem3 md3).
{ apply (am_exit B MT K XM_LIB LAWS g pos sp1 0 0 c ys ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 regs3 mem3 md3 kj
    (Z_to_bv 64 pcv) ss E HC HJ3 HAE35 HS Hkeep).
  - intros a Ha. apply KE; [unfold am_keepzone in Ha; lia|].
    intros Hz. destruct (HZ _ Hz) as [H | H]; unfold am_keepzone in Ha; lia.
  - intros i Hi. rewrite (KE (shadow_addr (FA g pos) + i)); [exact (HSH i Hi)
    | unfold shadow_addr, SHADOW_OFF; lia | exact (Hzsh i Hi)].
  - exact HPm. }
split; [exact HMC|].
split.
- destruct Hops as [Hops1 Hops2]. split; [exact Hops1|].
  pose proof (st_ok_restrict_reg tfibsegs (w_H W2) E ss
    (mkst regs3 (Z_to_bv 64 pcv) mem3 (seg_rom tfibsegs)) 26%bv HS) as R26.
  change (getr (ms_regs (mkst regs3 (Z_to_bv 64 pcv) mem3 (seg_rom tfibsegs))) 26%bv) with (getr regs3 26%bv)
    in R26.
  rewrite R26, H26. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite (HA 26%nat ltac:(lia)), (am_ew_reg g pos c regs2 ys 26 26%bv eq_refl). exact Hops2.
- pose proof (st_ok_region_nth E ss _ 4 am_cur_region HS Hcur4) as Hrc4.
  rewrite restrict_mkst_fx in Hrc4. cbn [ms_mem] in Hrc4. unfold am_cur_region in Hrc4.
  assert (U2 : bv_unsigned (ew E 2) = sp1).
  { rewrite (HA 2%nat ltac:(lia)), (am_ew_reg g pos c regs2 ys 2 2%bv eq_refl), R2. unfold w64.
    apply unsigned_lit_small. lia. }
  destruct Hcur as (Hc & _ & _).
  split; [exact Hc|]. split.
  + apply (field_of_region E _ 2%nat sp1 _ 152 168 152 168 152 8 (SOff 35 0) (e_p g + c) Hrc4 U2);
    [left; reflexivity | | lia | lia].
    cbn [sv_denot]. rewrite (HA 35%nat ltac:(lia)), (am_ew_CP g pos c regs2 ys), Z.add_0_r, Z_to_bv_bv_unsigned.
    reflexivity.
  + apply (field_of_region E _ 2%nat sp1 _ 152 168 152 168 160 8 (SOff 36 0) (e_n g - c) Hrc4 U2);
    [right; left; reflexivity | | lia | lia].
    cbn [sv_denot]. rewrite (HA 36%nat ltac:(lia)), (am_ew_CN g pos c regs2 ys), Z.add_0_r, Z_to_bv_bv_unsigned.
    reflexivity.
Qed.

(* a register of a stopped state, read off its symbolic value *)
Lemma oh_reg_off : forall g pos c regs2 ys E ss (W : world tfibsegs) ms (r : bv 5) n v,
env_agree 38 (am_env g pos c regs2 ys) E -> st_ok tfibsegs E ss (restrict (w_H W) ms) ->
sr_get (ss_regs ss) r = SOff n 0 -> (n < 38)%nat ->
ew (am_env g pos c regs2 ys) n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
getr (ms_regs ms) r = w64 v.
Proof using TL LAWS ROB.
intros g pos c regs2 ys E ss W ms r n v HAE HS Hsr Hn Hew Hv.
rewrite (st_ok_restrict_reg tfibsegs (w_H W) E ss ms r HS), Hsr.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite (proj1 HAE n Hn), Hew. reflexivity.
Qed.
Lemma oh_reg_lit : forall E ss (W : world tfibsegs) ms (r : bv 5) v,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> sr_get (ss_regs ss) r = SLit v ->
getr (ms_regs ms) r = w64 v.
Proof using TL LAWS ROB.
intros E ss W ms r v HS Hsr.
rewrite (st_ok_restrict_reg tfibsegs (w_H W) E ss ms r HS), Hsr. reflexivity.
Qed.
(* the same for an offset of an atom *)
Lemma oh_reg_offo : forall g pos c regs2 ys E ss (W : world tfibsegs) ms (r : bv 5) n o v,
env_agree 38 (am_env g pos c regs2 ys) E -> st_ok tfibsegs E ss (restrict (w_H W) ms) ->
sr_get (ss_regs ss) r = SOff n o -> (n < 38)%nat ->
ew (am_env g pos c regs2 ys) n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + o < 2 ^ 64 ->
getr (ms_regs ms) r = w64 (v + o).
Proof using TL LAWS ROB.
intros g pos c regs2 ys E ss W ms r n o v HAE HS Hsr Hn Hew Hv Hvo.
rewrite (st_ok_restrict_reg tfibsegs (w_H W) E ss ms r HS), Hsr.
apply (am_den_off E n v o); [rewrite (proj1 HAE n Hn); exact Hew | lia | lia].
Qed.

(* the two sides of the mask test *)
Lemma oh_dk_true : forall kd, oh_dk kd = true -> kd = 1 \/ kd = 4 \/ kd = 11.
Proof using TL LAWS ROB.
intros kd H. unfold oh_dk, oh_nd in H. rewrite negb_involutive in H.
apply orb_prop in H. destruct H as [H | H].
- apply orb_prop in H. destruct H as [H | H].
  + left. apply Z.eqb_eq. exact H.
  + right. left. apply Z.eqb_eq. exact H.
- right. right. apply Z.eqb_eq. exact H.
Qed.
Lemma oh_dk_false : forall kd, oh_dk kd = false -> oh_nd kd = true.
Proof using TL LAWS ROB.
intros kd H. unfold oh_dk in H. apply negb_false_iff in H. exact H.
Qed.

(* ================================ the call of the runtime's checked memset ================================ *)
Section c.
Hypothesis AMEMSET : aintrin_realizes tfibsegs B OSet CA_MEMSET.

Lemma oh_memset : forall g pos sp1 ops dk W2 c2,
oh_call g pos sp1 ops dk W2 c2 -> SRr tfibsegs W2 c2 (oh_mid g pos sp1 ops dk).
Proof using TL LAWS ROB AMEMSET.
intros g pos sp1 ops dk W2 c2 (ly2 & S2 & regs2 & mem2 & md2 & kj & -> & HJ & Hfr & Hk & Hmo & HC &
  (Hops & c & k & od & Hcur & Hkat & Hrec & Hdk1 & Hdk0 & Hrcq & Hwrc & R23 & R24 & R10 & R11 & R12 & R1)).
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hng & Hpg & Hpng & _).
pose proof (owe_frame_app B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as Happ.
change (fs_frame_bytes 3) with 512 in Hfceil.
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold AM_HI in *.
pose proof HJ as (HAR & _).
assert (Hin : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
pose proof HC as (Hpre & _ & R2 & R9 & R8 & R3 & R4 & _).
assert (Usp : spZ regs2 = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hretok : YK0s.ret_ok (w64 (oh_ret dk)))
  by (destruct dk; apply ret_ok_even; vm_compute; reflexivity).
assert (Hal16 : sp1 mod 16 = 0).
{ pose proof (Z.div_mod sp1 32 ltac:(lia)) as D. rewrite Hsp32, Z.add_0_r in D.
  replace sp1 with ((2 * (sp1 / 32)) * 16) by lia. apply Z_mod_mult. }
assert (HBS : block_shadow (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (FA g pos + 176) 184)
  by exact (am_bs_k B MT K XM_LIB g pos sp1 ly2 S2 W2 regs2 mem2 md2 HC).
unfold cfg_at. change (w64 CA_MEMSET) with (Z_to_bv 64 CA_MEMSET).
eapply SRr_bind.
{ eapply (aj_intrin_atS tfibsegs B LAWS tfib_segs_low OSet CA_MEMSET AMEMSET W2 regs2 mem2 LLVMF_STK (e_sp0 g) []
    (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 md2 kj (FA g pos + 344) 0 16
    (sp1 - e_sp0 g) (w64 (oh_ret dk))).
  - exact HJ.
  - exact R10.
  - exact R11.
  - exact R12.
  - lia.
  - lia.
  - lia.
  - rewrite Usp. lia.
  - rewrite Zminus_mod, Hal16, Hsp016. reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - exact Hretok.
  - intros a Ha. split.
    + right. right. right. exists 3, pos. split; [left; reflexivity|]. left.
      unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 3) with 512. lia.
    + replace (e_sp0 g + (sp1 - e_sp0 g)) with sp1 by lia. unfold ESTACK. lia.
  - unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
    unfold kLowMemEnd, kHighMemBeg, kHighMemEnd.
    destruct Happ as (_ & [Hlo | (Hh1 & Hh2)]); [left; lia | right; lia].
  - exact (block_shadow_range (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (FA g pos + 176) 184
             (FA g pos + 344) 16 HBS ltac:(lia) ltac:(lia)).
  - intros _. exact (oh_hull g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 344 16 HC ltac:(lia) ltac:(lia) ltac:(lia)).
  - exact I. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HPR & Ha0 & Hset & Hkeep & Hpres2 & Hsame).
replace (e_sp0 g + (sp1 - e_sp0 g)) with sp1 in Hkeep by lia.
assert (KT0 : tcj_kept tfibsegs B 4096 ly2 S2 W2 mem2 W2 mem2 sp1 (fun a => FA g pos + 344 <= a < FA g pos + 360))
  by exact (cw_kept0 B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)]
              ly2 S2 W2 mem2 md2 kj sp1 4096 _ HJ ltac:(lia) ltac:(lia)).
assert (KT : tcj_kept tfibsegs B 4096 ly2 S2 W2 mem2 W2 mem3 sp1 (fun a => FA g pos + 344 <= a < FA g pos + 360)).
{ apply (cw_kept_step B LAWS 4096 ly2 S2 W2 mem2 md2 W2 mem2 mem3 sp1 _
    (fun a => (FA g pos + 344 <= a < FA g pos + 360) \/ (sp1 - ESTACK <= a < sp1))
    ltac:(unfold ESTACK; lia) HAR KT0).
  - intros a Ha Hz. apply Hkeep;
    [exact Ha | intros X; apply Hz; left; lia | intros X; apply Hz; right; lia].
  - intros a [Ha | Ha]; [right; left; split; [exact Ha|] | left; unfold ESTACK in Ha; lia].
    intros Him. exact (oh_frame_not_img pos (FA g pos) ly2 S2 W2 mem2 md2 a HAR Hin EFA ltac:(lia) Him).
  - exact Hpres2. }
rewrite <- Usp in KT.
destruct (am_call_kept B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c 4096
  (fun a => FA g pos + 344 <= a < FA g pos + 360) ly2 S2 W2 regs3 mem3 md3 kj
  HJ Hfr HC Hcur ltac:(intros a Ha; cbv beta in Ha; lia) HJ3 HPR (Permutation_refl _) KT)
  as (HC3 & Hcur3 & KF).
assert (HZ0 : forall i, 0 <= i < 16 -> aview tfibsegs (w_H W2) mem3 (FA g pos + 344 + i) = Some 0).
{ intros i Hi. rewrite (Hset i Hi). reflexivity. }
assert (V344 : val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 344) 8 0).
{ apply (oh_val_zero W2 mem3 (FA g pos + 344) 8). intros i Hi. apply HZ0. cbn in Hi. lia. }
assert (V352 : val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 352) 4 0).
{ apply (oh_val_zero W2 mem3 (FA g pos + 352) 4). intros i Hi. cbn in Hi.
  replace (FA g pos + 352 + i) with (FA g pos + 344 + (8 + i)) by lia. apply HZ0. lia. }
assert (V356 : val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 356) 4 0).
{ apply (oh_val_zero W2 mem3 (FA g pos + 356) 4). intros i Hi. cbn in Hi.
  replace (FA g pos + 356 + i) with (FA g pos + 344 + (12 + i)) by lia. apply HZ0. lia. }
pose proof Hkat as [HKK HKW].
destruct HKK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Vrc & _ & _ & Vwrc & _).
pose proof HKW as (_ & _ & _ & _ & _ & _ & _ & _ & Wrc & _).
assert (V248 : val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 248) 4 (kz_rc k)).
{ apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 mem3);
  [intros x Hx; cbn in Hx; apply KF; cbv beta; lia |].
  replace (FA g pos + 248) with (FA g pos + 176 + 72) by lia. exact Vrc. }
assert (V316 : val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 316) 4 0).
{ apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 mem3);
  [intros x Hx; cbn in Hx; apply KF; cbv beta; lia |].
  replace (FA g pos + 316) with (FA g pos + 176 + 140) by lia. rewrite <- Hwrc. exact Vwrc. }
assert (HK3 : k_at g pos (oh_set k (kz_rc k) 0 (kz_want k) 0 0 0) W2 mem3)
  by exact (oh_k_at_set g pos k W2 mem2 W2 mem3 (kz_rc k) 0 0 0 0 Hkat
              ltac:(intros a Ha; apply KF; cbv beta; lia) V248 V316 V344 V352 V356 Wrc
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
apply SRr_ret. unfold oh_mid.
apply (am_mcut B MT K XM_LIB g pos sp1 0 (oh_ret dk) _ ly2 S2 W2 regs3 mem3 md3 kj HJ3 Hfr Hk Hmo HC3).
cbv beta. split.
- destruct Hops as (Hops1 & R26). split; [exact Hops1|].
  assert (P26 : getr regs3 26 = getr regs2 26) by exact (HPR 26 ltac:(unfold acallee_saved; lia)).
  rewrite P26. exact R26.
- exists c, (oh_set k (kz_rc k) 0 (kz_want k) 0 0 0), od.
  split; [exact Hcur3|]. split; [exact HK3|]. split; [exact Hrec|].
  split; [exact Hdk1|]. split; [exact Hdk0|]. split; [exact Hrcq|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  assert (P23 : getr regs3 23 = getr regs2 23) by exact (HPR 23 ltac:(unfold acallee_saved; lia)).
  assert (P24 : getr regs3 24 = getr regs2 24) by exact (HPR 24 ltac:(unfold acallee_saved; lia)).
  split; [rewrite P23; exact R23|]. rewrite P24. exact R24.
Qed.
End c.

(* ================================ the start of each piece ================================ *)
(* JOIN 0x8220c: the kind and k.desk read, the windows of k.rc and want_rc *)
Lemma oh_start1 : forall g pos sp1 ly2 S2 W2 regs2 mem2 md2 kj c k kd,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)]
  ly2 S2 W2 mem2 md2 kj ->
frames S2 = [(3, pos)] ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
cur_at g sp1 c W2 mem2 -> k_at g pos k W2 mem2 -> kz_kind k = kd -> 0 <= kd <= 11 ->
st_ok tfibsegs (am_env g pos c regs2 [kz_desk k]) (am_ss PC_JOIN [oh_rk kd; oh_rrc; oh_rw] [])
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 PC_JOIN) mem2 (seg_rom tfibsegs))).
Proof using TL LAWS ROB.
intros g pos sp1 ly2 S2 W2 regs2 mem2 md2 kj c k kd HJ Hfr HC Hcur Hkat Hkind Hkd.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hng & Hpg & Hpng & _).
change (fs_frame_bytes 3) with 512 in Hfceil.
unfold AM_HI in *.
pose proof Hkat as [HKK HKW].
destruct HKK as (Vkind & _ & Vdesk & _).
pose proof HKW as (_ & _ & Wdesk & _).
remember (am_env g pos c regs2 [kz_desk k]) as E eqn:HEE.
assert (E37 : ew E 37 = Z_to_bv 64 (kz_desk k))
  by (subst E; exact (am_ew_y g pos c regs2 [kz_desk k] 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (FA g pos)) by (subst E; exact (am_ew_F g pos c regs2 [kz_desk k])).
assert (U33 : bv_unsigned (ew E 33) = FA g pos) by (rewrite E33; apply unsigned_lit_small; lia).
assert (Hrs : Forall (region_ok tfibsegs E (mrestrict (w_H W2) mem2)) [oh_rk kd; oh_rrc; oh_rw]).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  - unfold oh_rk. rewrite HEE.
    apply (am_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c [kz_desk k]
      176 200 176 176 _ HJ Hfr HC ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    rewrite <- HEE. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (chunk_ok_val tfibsegs E _ (FA g pos) 176 4 (SLit kd) kd);
      [reflexivity | cbn; lia | cbn; lia |].
      rewrite <- Hkind. exact Vkind.
    + apply (chunk_ok_val tfibsegs E _ (FA g pos) 192 8 (SOff 37 0) (kz_desk k));
      [rewrite (am_den_off E 37 (kz_desk k) 0 E37) by lia; f_equal; lia | cbn; lia | cbn; lia |].
      replace (FA g pos + 192) with (FA g pos + 176 + 16) by lia. exact Vdesk.
  - unfold oh_rrc. rewrite HEE.
    apply (am_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c [kz_desk k]
      248 252 248 252 _ HJ Hfr HC ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    apply Forall_nil.
  - unfold oh_rw. rewrite HEE.
    apply (am_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c [kz_desk k]
      316 320 316 320 _ HJ Hfr HC ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    apply Forall_nil. }
assert (Hpd : pairwise_disjoint E [oh_rk kd; oh_rrc; oh_rw]).
{ unfold oh_rk, oh_rrc, oh_rw, am_frame_region. cbn [pairwise_disjoint all_disjoint].
  unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U33.
  repeat split; lia. }
assert (Hap : Forall (fun r => all_disjoint E r am_regs) [oh_rk kd; oh_rrc; oh_rw]).
{ rewrite HEE. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  - exact (owe_frame_apart_base B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c [kz_desk k]
      176 200 176 176 _ HJ Hfr HC ltac:(lia) ltac:(lia)).
  - exact (owe_frame_apart_base B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c [kz_desk k]
      248 252 248 252 _ HJ Hfr HC ltac:(lia) ltac:(lia)).
  - exact (owe_frame_apart_base B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c [kz_desk k]
      316 320 316 320 _ HJ Hfr HC ltac:(lia) ltac:(lia)). }
pose proof (am_entry B MT K XM_LIB TL LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c PC_JOIN [kz_desk k]
  [oh_rk kd; oh_rrc; oh_rw] [] HJ Hfr HC Hcur ltac:(vm_compute; reflexivity)) as HS.
rewrite <- HEE in HS. exact (HS Hrs Hpd Hap I).
Qed.

(* OWEH's table jump at 0x82248, with the kind pinned as a literal *)
Lemma oh_start3 : forall g pos sp1 ly2 S2 W2 regs2 mem2 md2 kj c ys kd,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)]
  ly2 S2 W2 mem2 md2 kj ->
frames S2 = [(3, pos)] ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
cur_at g sp1 c W2 mem2 -> getr regs2 24 = w64 kd ->
st_ok tfibsegs (am_env g pos c regs2 ys) (oh_ss3 kd)
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 OH_R1) mem2 (seg_rom tfibsegs))).
Proof using TL LAWS ROB.
intros g pos sp1 ly2 S2 W2 regs2 mem2 md2 kj c ys kd HJ Hfr HC Hcur R24.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hng & Hpg & Hpng & _).
change (fs_frame_bytes 3) with 512 in Hfceil.
unfold AM_HI in *.
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof HC as (Hpre & _ & R2 & _).
remember (am_env g pos c regs2 ys) as E eqn:HEE.
assert (U2 : bv_unsigned (ew E 2) = sp1).
{ subst E. rewrite (am_ew_reg g pos c regs2 ys 2 2%bv eq_refl), R2. unfold w64.
  apply unsigned_lit_small. lia. }
pose proof (arodata_ok_at B MT K XM_LIB g [(3, pos)] ly2 S2 W2 mem2 md2 kj Hpre HJ) as HRO.
assert (Hrt : region_ok tfibsegs E (mrestrict (w_H W2) mem2) oh_rt).
{ apply (cpg_img_region_ok B CA_RLO CA_RHI E W2 mem2 OH_TBL 44).
  - exact HRO.
  - exact (am_in_ro OH_TBL 44 ltac:(vm_compute; reflexivity)).
  - intros a Ha. apply (proj1 (tl_lib_consts B TL a ltac:(unfold lib_const_addr, OH_TBL in *; lia))).
  - intros a Ha. apply (proj2 (tl_lib_consts B TL a ltac:(unfold lib_const_addr, OH_TBL in *; lia))).
  - vm_compute. reflexivity.
  - unfold OH_TBL. lia.
  - lia.
  - unfold OH_TBL. lia. }
assert (Hap : Forall (fun r => all_disjoint E r am_regs) [oh_rt]).
{ apply Forall_cons; [|apply Forall_nil].
  unfold oh_rt, cpg_img_region, am_regs, am_regs0, cw_regs, am_spill_region, am_cur_region,
    stack_region, got_region, bcell_region.
  cbn [app all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2.
  unfold A_GOT_shadow, A_shadow_glob, OH_TBL. repeat split; lia. }
pose proof (am_entry B MT K XM_LIB TL LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c OH_R1 ys
  [oh_rt] [] HJ Hfr HC Hcur ltac:(vm_compute; reflexivity)) as HS.
rewrite <- HEE in HS.
specialize (HS ltac:(apply Forall_cons; [exact Hrt | apply Forall_nil])
  ltac:(cbn [pairwise_disjoint all_disjoint]; tauto) Hap I).
apply (ast_ok_set_reg_fp tfibsegs E _ _ 24%bv (SLit kd) HS ltac:(vm_compute; reflexivity)).
symmetry. exact R24.
Qed.

(* the desk test at 0x822e8, with the window of want_rc holding 0 *)
Lemma oh_start4 : forall g pos sp1 ly2 S2 W2 regs2 mem2 md2 kj c ys k,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)]
  ly2 S2 W2 mem2 md2 kj ->
frames S2 = [(3, pos)] ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
cur_at g sp1 c W2 mem2 -> k_at g pos k W2 mem2 -> kz_want_rc k = 0 ->
st_ok tfibsegs (am_env g pos c regs2 ys) (am_ss OH_R0 [oh_rwz] [])
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 OH_R0) mem2 (seg_rom tfibsegs))).
Proof using TL LAWS ROB.
intros g pos sp1 ly2 S2 W2 regs2 mem2 md2 kj c ys k HJ Hfr HC Hcur Hkat Hwrc.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hng & Hpg & Hpng & _).
change (fs_frame_bytes 3) with 512 in Hfceil.
unfold AM_HI in *.
pose proof Hkat as [HKK _].
destruct HKK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Vwrc & _).
remember (am_env g pos c regs2 ys) as E eqn:HEE.
assert (Hrs : Forall (region_ok tfibsegs E (mrestrict (w_H W2) mem2)) [oh_rwz]).
{ apply Forall_cons; [|apply Forall_nil].
  unfold oh_rwz. rewrite HEE.
  apply (am_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ys
    316 320 316 320 _ HJ Hfr HC ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  rewrite <- HEE. apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val tfibsegs E _ (FA g pos) 316 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
  replace (FA g pos + 316) with (FA g pos + 176 + 140) by lia. rewrite <- Hwrc. exact Vwrc. }
assert (Hap : Forall (fun r => all_disjoint E r am_regs) [oh_rwz]).
{ rewrite HEE. apply Forall_cons; [|apply Forall_nil].
  exact (owe_frame_apart_base B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ys
    316 320 316 320 _ HJ Hfr HC ltac:(lia) ltac:(lia)). }
pose proof (am_entry B MT K XM_LIB TL LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c OH_R0 ys
  [oh_rwz] [] HJ Hfr HC Hcur ltac:(vm_compute; reflexivity)) as HS.
rewrite <- HEE in HS.
exact (HS Hrs ltac:(cbn [pairwise_disjoint all_disjoint]; tauto) Hap I).
Qed.

End b.
End a.
