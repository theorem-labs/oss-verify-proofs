(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 571 of its 593 lines of code are new or changed and 122 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/U/Prog/codec_main_owe0.v; 247 of its 266 lines of code are new or changed and 574 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_owe1.v; 141 of its 172 lines of code are new or changed and 235 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_rd5.v, with its addresses and numbers changed; 664 of its 733 lines of code are new or changed and 103 lines of the source are left out. *)
(* Segment RD11 SYSEX of the image-A walk of LLVMFuzzerTestOneInput (fuzz_codec.asan): the reader of kind 11,
   0x80c9c (rd_pc 11) to RUN 0x820d0, against lib/A/Prog/codec_amain_inv.v's seg_rd_run 11.
   - 0x80c9c-0x81388: k.a = fuzz_u8 (sw 24(s6)), k.b = fuzz_u8 (sw 28(s6)), n0 = fuzz_u8 % 25 (0x81364-0x81380:
     mul 41, srli 10, mul 25, subw, zext.b). Each input byte is read behind its instrumented check
     (lb; beqz FAST; j SLOW, lib/A/Prog/CPgTokJ.v). A missing byte reads 0 (0x81274 stores 0 into a and b with one
     8-byte store, 0x8132c / 0x81388 store or keep 0). The four paths meet at 0x8138c (the cut rd11_mid).
   - 0x8138c-0x813b4 (rd11_tail): n = min(n0, in.n) (bltu at 0x81390), the cursor moves by n, k.n = n (sd 64(s6)),
     a0 = k.bytes = F + 216 (the spill 88(s1)), a1 = the old in.p, a2 = n, jal __asan_memcpy (0x51998, through
     CPgWalkIntr.cw_intrin_call: destination k.bytes in the frame, source the input block), then j 0x820d0
     (codec_amain_encl.am_jump).
   The record at RUN: kind 11, the personality pair of the start, a, b, the n input bytes followed by the old
   zero bytes of k.bytes, n; before and out 0xa5^32 as HEAD left them. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08 YI16.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC CodecRo CodecGlobs CPgWalk.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CPgWalkIntr CPgWalkImg CPgTokJ CPgSat.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_inv codec_amain_st codec_amain_encl.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_rdlib codec_amain_rdin.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.


(* the write windows of a run: the save-area / cursor regions of atom 2 and the frame regions of atom 33 *)
Ltac rd11_awr B2 B33 HFR :=
idtac; lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own);
lazymatch type of B2 with bv_unsigned (ew _ 2) = ?spv =>
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [azlit_tac|]
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - sp0));
  [reflexivity | rewrite B2; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |]
| eapply (YCbq.awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat);
  [reflexivity | exact B33 | cbn [YP09.r_wlo YP09.r_whi]; intros ? ?; apply HFR; lia |] ]
end end.
(* the zone a run's frame writes: its windows, at the bases B2 / B33 give *)
Ltac rd11_kwr B2 B33 :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?B2, ?B33 in Hb; lia | ]);
destruct Hr.
(* a run of the head to its next stop (an undecided branch or the meeting point 0x8138c), with the input byte's
   obligation closed *)
Ltac rd11_run_t LAWS HJ0 HFR HC c E35 E32 B2 B33 EFA :=
cwj_run_to ltac:(rdj_awr B2 B33 EFA) 529292; try (rd_obl LAWS HJ0 HFR HC c E35 E32).
(* a branch on in.n - j (the atom 36 at offset -j), as a fact over Z *)
Ltac rd11_brn Hb E36 :=
rewrite ?branch_eq_U, ?branch_ne_U in Hb;
lazymatch type of Hb with context [U ?Ev (SOff 36 ?o)] =>
  rewrite (cw_U_offx Ev 36 _ o ltac:(rewrite ?ew_ewset_other by lia; exact E36) ltac:(lia)) in Hb end;
rewrite U_lit in Hb by lia; rewrite Z.mod_small in Hb by lia;
first [apply Z.eqb_eq in Hb | apply Z.eqb_neq in Hb].

(* ================================ the record ================================ *)
(* k at the meeting point 0x8138c: HEAD's record with kind 11, a and b stored *)
Definition rd11_kab (pv dv a b : Z) : kcallZ :=
mkKcallZ 11 pv dv a b 0 0 (repeat 0 24) 0 0 fa5 fa5 0 (repeat 0 24) 0 0 0.
(* k at RUN: bytes and n as the tail leaves them *)
Definition rd11_kfin (pv dv a b : Z) (bs : list Z) (t : Z) : kcallZ :=
mkKcallZ 11 pv dv a b 0 0 bs t 0 fa5 fa5 0 (repeat 0 24) 0 0 0.
(* the input bytes, and the t of them from the cursor c on *)
Definition rd11_inp (g : ectx) : list Z := map (fun x : byte => bv_unsigned x) (e_pl g).
Definition rd11_src (g : ectx) (c t : Z) : list Z :=
map (fun j => nth (Z.to_nat c + j) (rd11_inp g) 0) (seq 0 (Z.to_nat t)).
Definition PC_RD11M : Z := 0x8138c.
Definition rd11_kn : YP09.region := am_frame_region 240 248 240 248 [].
Definition rd11_SH : list shent := [mkSHE 33 176 360].

Lemma rd11_src_len : forall g c t, length (rd11_src g c t) = Z.to_nat t.
Proof. intros g c t. unfold rd11_src. rewrite length_map, length_seq. reflexivity. Qed.
Lemma rd11_src_nth : forall g c t j, (j < Z.to_nat t)%nat ->
nth j (rd11_src g c t) 0 = nth (Z.to_nat c + j) (rd11_inp g) 0.
Proof.
intros g c t j Hj. unfold rd11_src.
pose proof (map_nth (fun j0 => nth (Z.to_nat c + j0) (rd11_inp g) 0) (seq 0 (Z.to_nat t)) 0%nat j) as HM.
cbv beta in HM.
rewrite (nth_indep _ 0 (nth (Z.to_nat c + 0) (rd11_inp g) 0)) by (rewrite length_map, length_seq; lia).
rewrite HM, seq_nth by lia. reflexivity.
Qed.

Lemma rd11_enc_ok : forall pv dv a b t src od, pd_okA pv dv od -> 0 <= a < 256 -> 0 <= b < 256 -> 0 <= t <= 24 ->
length src = Z.to_nat t -> Forall (fun x => 0 <= x < 256) src ->
enc_okZ (rd11_kfin pv dv a b (src ++ repeat 0 (24 - Z.to_nat t)) t) od.
Proof.
intros pv dv a b t src od Hpd Ha Hb Ht Hl Hf.
unfold enc_okZ, rdr_kZ, reader_ok, rd11_kfin.
cbn [kz_kind kz_p kz_desk kz_a kz_b kz_c kz_delta kz_bytes kz_n kz_before kz_out].
split; [lia|]. split; [exact Hpd|]. split; [|split; reflexivity].
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [rewrite length_app, repeat_length; lia|].
split; [apply Forall_app; split; [exact Hf | apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia]|].
split; [lia|]. split; [intros; lia|]. split; [intros; lia|]. intros _; lia.
Qed.

Lemma rd11_kfin_wf : forall pv dv a b t src, 0 <= pv < 2 ^ 64 -> 0 <= dv < 2 ^ 64 -> 0 <= a < 256 -> 0 <= b < 256 ->
0 <= t <= 24 -> length src = Z.to_nat t ->
kcall_wfZ (rd11_kfin pv dv a b (src ++ repeat 0 (24 - Z.to_nat t)) t).
Proof.
intros pv dv a b t src Hp Hd Ha Hb Ht Hl. unfold kcall_wfZ, rd11_kfin.
cbn [kz_kind kz_p kz_desk kz_a kz_b kz_c kz_delta kz_bytes kz_n kz_rc kz_before kz_out kz_want_rc kz_want
  kz_want_len kz_want_key kz_want_display].
repeat split; try lia; try reflexivity. rewrite length_app, repeat_length. lia.
Qed.

(* ================================ arithmetic ================================ *)
Lemma rd11_U_add : forall E m k x y, ew E m = Z_to_bv 64 x -> ew E k = Z_to_bv 64 y -> 0 <= x -> 0 <= y ->
x + y < 2 ^ 64 -> U E (SAlu ALU_ADD (SOff m 0) (SOff k 0)) = x + y.
Proof.
intros E m k x y Hm Hk Hx Hy Hxy. rewrite U_SAlu, (U_atom E m x Hm), (U_atom E k y Hk) by lia.
cbn [zalu_raw]. apply zcanon_id. unfold M64. lia.
Qed.
Lemma rd11_U_sub : forall E m k x y, ew E m = Z_to_bv 64 x -> ew E k = Z_to_bv 64 y -> 0 <= x <= y -> y < 2 ^ 64 ->
U E (SAlu ALU_ADD (SMd M_MUL (SOff m 0) (SLit (-1))) (SOff k 0)) = y - x.
Proof.
intros E m k x y Hm Hk Hxy Hy.
rewrite U_SAlu, U_SMd, U_SLit, (U_atom E m x Hm), (U_atom E k y Hk) by lia.
cbn [zalu_raw zmd_raw]. unfold zcanon, M64.
rewrite Z.add_mod_idemp_l by lia.
replace (x * ((-1) mod 2 ^ 64) + y) with ((y - x) + x * 2 ^ 64)
  by (change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1); ring).
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
(* a bounded check over the 256 values of a byte *)
Lemma rd11_all256 : forall f : Z -> bool, forallb f (map Z.of_nat (seq 0 256)) = true ->
forall x, 0 <= x < 256 -> f x = true.
Proof.
intros f H x Hx. rewrite forallb_forall in H. apply H. apply in_map_iff.
exists (Z.to_nat x). split; [lia|]. apply in_seq. lia.
Qed.
(* 0x81368-0x81380: x * 41 >> 10 is x / 25, so the subtraction and the zero extension leave x mod 25 *)
Lemma rd11_U_n0 : forall E m x, ew E m = Z_to_bv 64 x -> 0 <= x < 256 ->
U E (SAlu ALU_AND (SAlu ALU_SUB (SOff m 0)
       (SMd M_MUL (SAlu ALU_SRL (SMd M_MUL (SOff m 0) (SLit 41)) (SLit 10)) (SLit 25))) (SLit 255)) = x mod 25.
Proof.
intros E m x Hm Hx.
rewrite !U_SAlu. rewrite !U_SMd. rewrite !U_SAlu. rewrite !U_SMd.
rewrite !U_lit by lia. rewrite (U_atom E m x Hm) by lia.
apply Z.eqb_eq.
exact (rd11_all256
  (fun y => zcanon (zalu_raw 63 64 ALU_AND
     (zcanon (zalu_raw 63 64 ALU_SUB y
        (zcanon (zmd_raw 64 M_MUL
           (zcanon (zalu_raw 63 64 ALU_SRL (zcanon (zmd_raw 64 M_MUL y 41)) 10)) 25)))) 255) =? y mod 25)
  ltac:(vm_compute; reflexivity) x Hx).
Qed.
(* the 8-byte store of 0 at k.a (0x81278) writes both a and b *)
Lemma rd11_le0 : forall w k, YO0f.le_byte 0 w k = 0.
Proof.
intros w k. unfold YO0f.le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia).
rewrite Z.shiftr_0_l. reflexivity.
Qed.
Lemma rd11_vm8_0 : forall (m : word -> option byte) a, val_mem tfibsegs m a 8 0 ->
val_mem tfibsegs m a 4 0 /\ val_mem tfibsegs m (a + 4) 4 0.
Proof.
intros m a H. split; intros k Hk; rewrite rd11_le0.
- rewrite <- (rd11_le0 8%nat k). apply H. lia.
- replace (a + 4 + Z.of_nat k) with (a + Z.of_nat (4 + k)) by lia.
  rewrite <- (rd11_le0 8%nat (4 + k)). apply H. lia.
Qed.
(* the frame's 64 shadow bytes lie off the frame, in the shadow band *)
Lemma rd11_shadow_apart : forall F i, 4096 <= F ->
(F + 512 <= 2147446784 \/ 17594333495296 <= F) -> F + 512 <= 0x7fffff800000 -> 0 <= i < 64 ->
(shadow_addr F + i < F \/ F + 512 <= shadow_addr F + i) /\ 2147450880 <= shadow_addr F + i < 17594333495296.
Proof.
intros F i H4 Happ Hhi Hi. unfold shadow_addr, SHADOW_OFF.
pose proof (Z.div_mod F 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma rd11_aview_vm1 : forall H m a v, val_mem tfibsegs (mrestrict H m) a 1 v -> 0 <= v < 256 ->
aview tfibsegs H m a = Some v.
Proof.
intros H m a v Hv Hr. pose proof (Hv 0%nat ltac:(lia)) as H0. cbn [Z.of_nat] in H0. rewrite Z.add_0_r in H0.
unfold aview. cbv beta. rewrite H0. cbn [option_map]. f_equal.
unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r, (Z.mod_small v 256) by lia.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite !(Z.mod_small v 256) by lia. reflexivity.
Qed.

(* The record at RUN from the record at the meeting point, the bytes kept, the copied bytes and k.n. *)
Lemma rd11_k_final : forall (W : world tfibsegs) m m' q pv dv a b t (src : list Z),
kcall_atA tfibsegs W m q (rd11_kab pv dv a b) ->
0 <= t <= 24 -> length src = Z.to_nat t ->
(forall o, 0 <= o < 184 -> ~ (40 <= o < 40 + t) -> ~ (64 <= o < 72) ->
   aview tfibsegs (w_H W) m' (q + o) = aview tfibsegs (w_H W) m (q + o)) ->
(forall j, (j < Z.to_nat t)%nat ->
   val_mem tfibsegs (mrestrict (w_H W) m') (q + 40 + Z.of_nat j) 1 (nth j src 0) /\ 0 <= nth j src 0 < 256) ->
val_mem tfibsegs (mrestrict (w_H W) m') (q + 64) 8 t ->
kcall_atA tfibsegs W m' q (rd11_kfin pv dv a b (src ++ repeat 0 (24 - Z.to_nat t)) t).
Proof.
intros W m m' q pv dv a b t src
  (V0 & V8 & V16 & V24 & V28 & V32 & V36 & G40 & V64 & V72 & G76 & G108 & V140 & G144 & V168 & V176 & V180)
  Ht Hl HK HB HN.
assert (KV : forall x n v, q <= x -> x + Z.of_nat n <= q + 184 ->
  (x + Z.of_nat n <= q + 40 \/ (q + 40 + t <= x /\ x + Z.of_nat n <= q + 64) \/ q + 72 <= x) ->
  val_mem tfibsegs (mrestrict (w_H W) m) x n v -> val_mem tfibsegs (mrestrict (w_H W) m') x n v).
{ intros x n v H1 H2 H3 Hv. apply (cw_val_mem_kept (w_H W) (w_H W) m m'); [|exact Hv].
  intros y Hy. replace y with (q + (y - q)) by lia. apply HK; lia. }
assert (KG : forall x l, q + 72 <= x -> x + Z.of_nat (length l) <= q + 184 ->
  garr8 tfibsegs (mrestrict (w_H W) m) x l -> garr8 tfibsegs (mrestrict (w_H W) m') x l).
{ intros x l H1 H2 Hg. apply (am_garr8_kept (w_H W) (w_H W) m m'); [|exact Hg].
  intros y Hy. replace y with (q + (y - q)) by lia. apply HK; lia. }
unfold rd11_kab, rd11_kfin, kcall_atA in *.
cbn [kz_kind kz_p kz_desk kz_a kz_b kz_c kz_delta kz_bytes kz_n kz_rc kz_before kz_out kz_want_rc kz_want
  kz_want_len kz_want_key kz_want_display] in *.
assert (L32 : length fa5 = 32%nat) by reflexivity.
assert (L24 : length (repeat 0 24) = 24%nat) by reflexivity.
split; [apply KV; [lia | cbn; lia | cbn; lia | exact V0]|].
split; [apply KV; [lia | cbn; lia | cbn; lia | exact V8]|].
split; [apply KV; [lia | cbn; lia | cbn; lia | exact V16]|].
split; [apply KV; [lia | cbn; lia | cbn; lia | exact V24]|].
split; [apply KV; [lia | cbn; lia | cbn; lia | exact V28]|].
split; [apply KV; [lia | cbn; lia | cbn; lia | exact V32]|].
split; [apply KV; [lia | cbn; lia | cbn; lia | exact V36]|].
split.
{ intros j Hj. rewrite length_app, repeat_length, Hl in Hj.
  destruct (Nat.lt_ge_cases j (Z.to_nat t)) as [Hjt | Hjt].
  - rewrite app_nth1 by lia. exact (HB j Hjt).
  - rewrite app_nth2 by lia. rewrite Hl. rewrite nth_repeat.
    destruct (G40 j ltac:(rewrite L24; lia)) as (Gv & _). rewrite nth_repeat in Gv.
    split; [|lia]. apply KV; [lia | cbn; lia | cbn; lia | exact Gv]. }
split; [exact HN|].
split; [apply KV; [lia | cbn; lia | cbn; lia | exact V72]|].
split; [apply KG; [lia | rewrite L32; lia | exact G76]|].
split; [apply KG; [lia | rewrite L32; lia | exact G108]|].
split; [apply KV; [lia | cbn; lia | cbn; lia | exact V140]|].
split; [apply KG; [lia | rewrite L24; lia | exact G144]|].
split; [apply KV; [lia | cbn; lia | cbn; lia | exact V168]|].
split; [apply KV; [lia | cbn; lia | cbn; lia | exact V176]|].
apply KV; [lia | cbn; lia | cbn; lia | exact V180].
Qed.

Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis AMEMCPY : aintrin_realizes tfibsegs B OCpy 0x51998.

(* the meeting point 0x8138c: a, b stored, a2 = n0 (the length byte % 25, or 0) *)
Definition rd11_mid (g : ectx) (pos sp1 ops : Z) : world tfibsegs -> config -> Prop :=
mcut B MT K XM_LIB g pos sp1 0 PC_RD11M (fun ly2 S2 W2 regs2 mem2 md2 =>
ops_at ops regs2 /\ exists c pv dv od a b n0, cur_at g sp1 c W2 mem2 /\ 1 <= c /\ pd_okA pv dv od /\
k_at g pos (rd11_kab pv dv a b) W2 mem2 /\ 0 <= a < 256 /\ 0 <= b < 256 /\
getr regs2 12 = w64 n0 /\ 0 <= n0 <= 24).

(* The state at the entry of __asan_memcpy (0x51998, ra = 0x813b8), from the meeting point's facts: the copy of
   the t input bytes at the cursor into k.bytes, the reseat at 0x813b8, the exit to the cut there and the
   `j 0x820d0` to RUN. *)
Lemma rd11_call : forall g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c pv dv od a b t Es ss ms md,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 kj ->
frames S2 = [(3, pos)] -> 0 <= kj <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
ops_at ops regs2 -> 1 <= c -> c + t <= e_n g -> pd_okA pv dv od ->
k_at g pos (rd11_kab pv dv a b) W2 mem2 -> 0 <= a < 256 -> 0 <= b < 256 -> 0 <= t <= 24 ->
st_ok tfibsegs Es ss (restrict (w_H W2) ms) -> ss_pc ss = 0x51998 -> ss_resv ss = None ->
ss_atoms_lt 40 ss = true -> sr_get (ss_regs ss) 1%bv = SLit 0x813b8 ->
am_keep_ok (ss_regs (ss_after_call ss [] 40 0x813b8)) = true ->
sr_get (ss_regs (ss_after_call ss [] 40 0x813b8)) 26%bv = SOff 26 0 ->
env_agree 35 (am_env g pos c regs2 []) Es ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 (ms_mem ms) md kj ->
getr (ms_regs ms) 10 = w64 (FA g pos + 216) -> getr (ms_regs ms) 11 = w64 (e_p g + c) -> getr (ms_regs ms) 12 = w64 t ->
getr (ms_regs ms) 2 = w64 sp1 -> getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
(forall x, 0 <= x < 2 ^ 64 -> ~ ((sp1 + 152 <= x < sp1 + 168) \/ (FA g pos + 240 <= x < FA g pos + 248)) ->
   aview tfibsegs (w_H W2) (ms_mem ms) x = aview tfibsegs (w_H W2) mem2 x) ->
val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms)) (sp1 + 152) 8 (e_p g + c + t) ->
val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms)) (sp1 + 160) 8 (e_n g - c - t) ->
val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms)) (FA g pos + 240) 8 t ->
SRr tfibsegs W2 (mkCfg ms md) (inv_run B MT K XM_LIB g pos sp1 ops).
Proof.
intros g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c pv dv od a b t Es ss ms md
  HJs Hfr Hkj HMO HC Hops Hc1 Hct Hpd Hkat Ha Hb Ht HS Hpc Hrv Hat Hra Hkeep R26 HAE HJ
  G10 G11 G12 G2 G3 G4 KE V152 V160 VN.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJs Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & Hblk).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
assert (FS3' : fs_frame_bytes 3 = 512) by (vm_compute; reflexivity).
assert (HES : ESTACK = 4096) by reflexivity.
rewrite FS3' in Hfceil. unfold AM_HI in Hchi, Hpn.
set (F := FA g pos) in *.
pose proof HJ as (HARc & _).
assert (Hin3 : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
destruct (frames_bounds tfibsegs B LAWS ly2 S2 W2 (ms_mem ms) md 3 pos HARc Hin3) as (_ & _ & Happ).
rewrite EFA, FS3' in Happ. unfold in_app, kLowShadowBeg, ASAN_CEIL in Happ. rewrite C3 in Happ.
assert (HSA : forall i, 0 <= i < 64 -> (shadow_addr F + i < F \/ F + 512 <= shadow_addr F + i) /\
  2147450880 <= shadow_addr F + i < 17594333495296) by (intros i Hi; apply rd11_shadow_apart; lia).
assert (SPZ : spZ (ms_regs ms) = sp1) by (unfold spZ; rewrite G2; unfold w64; apply unsigned_lit_small; lia).
assert (HFR : forall x, F <= x < F + 512 ->
  awr_byte LLVMF_STK (e_sp0 g) [] (ablocks B (e_ly g) (e_S g)) (ablocks B ly2 S2) ly2 [(3, pos)] x).
{ intros x Hx. right. right. right. exists 3, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
  rewrite EFA, FS3'. lia. }
pose proof HC as HSH. do 43 (destruct HSH as (_ & HSH)). destruct HSH as (HSH0 & Hga & HPerm).
pose proof HC as (Hpre & _).
pose proof Hpre as HPRE. unfold e_pre, codec_lib_pre_x in HPRE.
destruct HPRE as (_ & _ & _ & _ & _ & Hnpl & _).
(* the frame's shadow, and k's 23 usable shadow bytes, at the call *)
assert (HSHc : forall i, 0 <= i < 56 ->
  aview tfibsegs (w_H W2) (ms_mem ms) (shadow_addr F + i) = Some (nth (Z.to_nat i) (shm 0) 0)).
{ intros i Hi. pose proof (HSA i ltac:(lia)) as Hs. rewrite KE by lia. exact (HSH0 i Hi). }
assert (HBSc : block_shadow (aview tfibsegs (w_H W2) (ms_mem ms)) SHADOW_OFF (F + 176) 184).
{ apply am_block_shadow; [exact Hf64 | lia | reflexivity | lia |].
  intros i Hi. change ((184 + 7) / 8) with 23 in Hi. change (184 / 8) with 23. change (176 / 8) with 22.
  rewrite (proj2 (Z.ltb_lt i 23) ltac:(lia)).
  rewrite (HSHc (22 + i) ltac:(lia)). f_equal.
  pose proof amain_pure_sat as (_ & _ & _ & _ & _ & _ & _ & Hk23 & _).
  apply (Hk23 0 (Z.to_nat (22 + i))). lia. }
assert (Hdra : range_addressable (aview tfibsegs (w_H W2) (ms_mem ms)) SHADOW_OFF (F + 216) t)
  by (apply (block_shadow_range _ SHADOW_OFF (F + 176) 184 (F + 216) t HBSc); lia).
assert (Hdam : amem_range (F + 216) t) by (unfold amem_range; rewrite C3, C4, C5; lia).
(* the source: the t input bytes at the cursor, in the input block *)
assert (Hn1 : 0 < e_n g) by lia.
destruct (Hblk Hn1) as (Hinb & _).
destruct (rd_in_sep B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJs Hfr HC Hn1) as (Hinc & Hinf).
pose proof (req_size_pos (e_n g) ltac:(lia)) as (_ & Hrq).
pose proof (sat_block_rd tfibsegs B LAWS ly2 S2 W2 (ms_mem ms) md sp1 4096 (e_p g) (e_n g) (e_p g + c) t LLVMF_STK (e_sp0 g)
  HARc Hinb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (Hx0 & Hxn & Hxv & Hxra & Hxhull & Hxam & Hxwin).
pose proof (sep_block_frame tfibsegs B LAWS ly2 S2 W2 (ms_mem ms) md (e_p g) (e_n g) 3 pos HARc Hinb Hin3) as Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite EFA, FS3' in Hsep.
unfold coff_win in Hxwin.
(* 0x813b4 jal __asan_memcpy *)
refine (cw_intrin_call B LAWS OCpy 0x51998 AMEMCPY W2 Es ss ms md LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g)
  (e_mem g) (e_md g) [(3, pos)] ly2 S2 kj (F + 216) (e_p g + c) t 0x813b8 40%nat [] _ HS Hpc Hrv HJ G10 G11 G12
  _ _ _ _ _ _ _ G3 G4 Hra _ _ _ _ _ _ _ Hat eq_refl eq_refl eq_refl (submem_nil _) (Forall_nil _) _).
- lia.
- lia.
- lia.
- rewrite SPZ, HES. lia.
- rewrite SPZ. lia.
- rewrite SPZ. pose proof (Z.div_mod sp1 32 ltac:(lia)) as D. rewrite Hsp32, Z.add_0_r in D. rewrite D.
  replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by ring. apply Z_mod_mult.
- exact Hsp016.
- lia.
- apply ret_ok_even. vm_compute. reflexivity.
- intros x Hx. split; [apply HFR; lia | rewrite SPZ, HES; lia].
- exact Hdam.
- exact Hdra.
- intros Hn0. exact (sat_frame_hull tfibsegs B LAWS ly2 S2 W2 (ms_mem ms) md 3 pos F 216 t HARc Hin3 EFA Hf64
    ltac:(rewrite FS3'; reflexivity) ltac:(lia) Hn0 ltac:(rewrite FS3'; lia)).
- split; [lia|]. split; [lia|]. split.
  { intros y Hy. split; [apply Hxv; lia | rewrite SPZ, HES; lia]. }
  split; [lia|]. split; [exact Hxam|]. split; [exact Hxra | exact Hxhull].
- intros regs3 mem3 md3 HJ3 HP3 Ha03 Hcpy Hkept Hpres3 Hsm HS3.
  cbv beta iota in Hcpy. rewrite SPZ, HES in Hkept.
  assert (KF : forall x, 0 <= x < 2 ^ 64 -> ~ ((sp1 + 152 <= x < sp1 + 168) \/ (F + 240 <= x < F + 248)) ->
    ~ (F + 216 <= x < F + 216 + t) -> ~ (sp1 - 4096 <= x < sp1) ->
    aview tfibsegs (w_H W2) mem3 x = aview tfibsegs (w_H W2) mem2 x).
  { intros x Hx Hz Hd Hs. rewrite (Hkept x Hx Hd Hs). exact (KE x Hx Hz). }
  (* 0x813b8 j 0x820d0 *)
  unfold inv_run.
  refine (am_jump B MT K XM_LIB LAWS g pos sp1 0 0x813b8 PC_RUN _ W2 _ _ _ _ _);
    [vm_compute; reflexivity | unfold PC_RUN; lia | intros ? ? ? ? ? ? ? HP0; exact HP0 |].
  change (mkCfg (mkst regs3 (Z_to_bv 64 0x813b8) mem3 (seg_rom tfibsegs)) md3)
    with (cfg_at tfibsegs 0x813b8 regs3 mem3 md3).
  apply (am_mcut B MT K XM_LIB g pos sp1 0 0x813b8 _ ly2 S2 W2 regs3 mem3 md3 kj HJ3 Hfr Hkj HMO).
  + apply (am_exit B MT K XM_LIB LAWS g pos sp1 0 0 c [] ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 regs3 mem3 md3 kj
      (Z_to_bv 64 0x813b8) (ss_after_call ss [] 40 0x813b8) (havoc Es 40 (map (getr regs3) CLOB)) HC HJ3).
    * apply env_agree_havoc_ge; [lia | exact HAE].
    * exact HS3.
    * exact Hkeep.
    * intros x Hx. unfold am_keepzone in Hx. apply KF; lia.
    * intros i Hi. change (FA g pos) with F. pose proof (HSA i ltac:(lia)) as Hs. rewrite KF by lia. exact (HSH0 i Hi).
    * exact HPerm.
  + split.
    { destruct Hops as (Hops0 & R26o). split; [exact Hops0|].
      pose proof (st_ok_restrict_reg tfibsegs (w_H W2) _ _ _ 26%bv HS3) as G26. cbn [ms_regs mkst] in G26.
      rewrite R26 in G26. cbn [sv_denot] in G26. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, ew_havoc_old in G26 by lia.
      first [rewrite (proj1 HAE 26%nat ltac:(lia)) in G26 | rewrite <- (proj1 HAE 26%nat ltac:(lia)) in G26].
      rewrite (am_ew_reg g pos c regs2 [] 26 26%bv eq_refl) in G26. rewrite G26. exact R26o. }
    exists (c + t), (rd11_kfin pv dv a b (rd11_src g c t ++ repeat 0 (24 - Z.to_nat t)) t), od.
    split.
    { split; [lia|]. split.
      - replace (e_p g + (c + t)) with (e_p g + c + t) by lia.
        apply (cw_val_mem_kept (w_H W2) (w_H W2) (ms_mem ms) mem3); [|exact V152].
        intros y Hy. apply Hkept; cbn in Hy; lia.
      - replace (e_n g - (c + t)) with (e_n g - c - t) by lia.
        apply (cw_val_mem_kept (w_H W2) (w_H W2) (ms_mem ms) mem3); [|exact V160].
        intros y Hy. apply Hkept; cbn in Hy; lia. }
    pose proof (rd11_src_len g c t) as Hsl.
    assert (Hsrc : forall j, (j < Z.to_nat t)%nat ->
      aview tfibsegs (w_H W2) mem3 (F + 216 + Z.of_nat j) = Some (nth j (rd11_src g c t) 0) /\
      0 <= nth j (rd11_src g c t) 0 < 256).
    { intros j Hj. rewrite (rd11_src_nth g c t j Hj).
      assert (Hjl : (Z.to_nat c + j < length (rd11_inp g))%nat).
      { unfold rd11_inp. rewrite length_map. lia. }
      destruct (Hga (Z.to_nat c + j)%nat Hjl) as (Gv & Gr). split; [|exact Gr].
      rewrite (Hcpy (Z.of_nat j) ltac:(lia)).
      rewrite KE by lia.
      replace (e_p g + c + Z.of_nat j) with (e_p g + Z.of_nat (Z.to_nat c + j)) by lia.
      exact (rd11_aview_vm1 _ _ _ _ Gv Gr). }
    split; [split|].
    * apply (rd11_k_final W2 mem2 mem3 (F + 176) pv dv a b t (rd11_src g c t) (proj1 Hkat) Ht Hsl).
      ** intros o Ho H1 H2. apply KF; lia.
      ** intros j Hj. destruct (Hsrc j Hj) as (Hv & Hr). split; [|exact Hr].
         destruct (am_mb W2 mem3 _ _ Hv) as (Hm & _).
         replace (F + 176 + 40 + Z.of_nat j) with (F + 216 + Z.of_nat j) by lia.
         exact (cpg_val_mem1 _ _ _ Hr Hm).
      ** replace (F + 176 + 64) with (F + 240) by lia.
         apply (cw_val_mem_kept (w_H W2) (w_H W2) (ms_mem ms) mem3); [|exact VN].
         intros y Hy. apply Hkept; cbn in Hy; lia.
    * pose proof (proj2 Hkat) as (_ & Hpv & Hdv & _).
      apply rd11_kfin_wf; [exact Hpv | exact Hdv | exact Ha | exact Hb | exact Ht | exact Hsl].
    * apply rd11_enc_ok; [exact Hpd | exact Ha | exact Hb | exact Ht | exact Hsl|].
      apply Forall_forall. intros x Hx. apply (In_nth _ _ 0) in Hx as (j & Hj & <-).
      rewrite Hsl in Hj. exact (proj2 (Hsrc j Hj)).
Qed.

Lemma rd11_tail : forall g pos sp1 ops W2 c2, rd11_mid g pos sp1 ops W2 c2 ->
SRr tfibsegs W2 c2 (inv_run B MT K XM_LIB g pos sp1 ops).
Proof.
intros g pos sp1 ops W2 c2 H.
destruct H as (ly2 & S2 & regs2 & mem2 & md2 & kj & -> & HJ & Hfr & Hkj & HMO & HC & HP).
destruct HP as (Hops & c & pv & dv & od & a & b & n0 & Hcur & Hc1 & Hpd & Hkat & Ha & Hb & R12 & Hn0).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & Hblk).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof (am_entry B MT K XM_LIB TL LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c PC_RD11M [] [] []
  HJ Hfr HC Hcur eq_refl (Forall_nil _) I (Forall_nil _) I) as HS.
pose proof HJ as (HAR & _).
assert (Hin3 : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
assert (Hrkn : region_ok tfibsegs (am_env g pos c regs2 []) (mrestrict (w_H W2) mem2) rd11_kn).
{ apply (am_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c [] 240 248 240 248 []);
  [exact HJ | exact Hfr | exact HC | lia | lia | lia | lia | lia | apply Forall_nil]. }
pose proof (am_bs_k B MT K XM_LIB g pos sp1 ly2 S2 W2 regs2 mem2 md2 HC) as HBSK.
pose proof (sat_main_k_rd tfibsegs B LAWS ly2 S2 W2 mem2 md2 sp1 0 pos (FA g pos) LLVMF_STK (e_sp0 g)
  HAR Hin3 EFA Hf64 HBSK ltac:(lia) ltac:(lia)) as Hkrd.
assert (SHOK : sh_ok tfibsegs CW_Bx rd11_SH (am_env g pos c regs2 []) (mrestrict (w_H W2) mem2)).
{ apply Forall_cons; [|apply Forall_nil].
  exact (cw_shent_crd_off W2 mem2 sp1 0 (am_env g pos c regs2 []) 33 (FA g pos) 176 184 Hkrd
    (am_ew_F g pos c regs2 []) ltac:(lia) ltac:(lia) (am_ew_SB g pos c regs2 []) ltac:(lia)). }
remember (am_env g pos c regs2 []) as E eqn:HEE.
pose proof HC as (_ & _ & R2 & R9 & R8 & R3 & R4 & _).
assert (E2 : ew E 2 = w64 sp1) by (subst E; rewrite (am_ew_reg g pos c regs2 [] 2 2%bv eq_refl); exact R2).
assert (B2 : bv_unsigned (ew E 2) = sp1) by (rewrite E2; unfold w64; apply unsigned_lit_small; lia).
assert (E33 : ew E 33 = Z_to_bv 64 (FA g pos)) by (subst E; apply am_ew_F).
assert (B33 : bv_unsigned (ew E 33) = FA g pos) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply am_ew_SB).
assert (E35 : ew E 35 = Z_to_bv 64 (e_p g + c)) by (subst E; apply am_ew_CP).
assert (E36 : ew E 36 = Z_to_bv 64 (e_n g - c)) by (subst E; apply am_ew_CN).
assert (E12 : ew E 12 = Z_to_bv 64 n0) by (subst E; rewrite (am_ew_reg g pos c regs2 [] 12 12%bv eq_refl), R12; reflexivity).
assert (E3 : ew E 3 = w64 (as_gp B)) by (subst E; rewrite (am_ew_reg g pos c regs2 [] 3 3%bv eq_refl); exact R3).
assert (E4 : ew E 4 = w64 (as_tp B)) by (subst E; rewrite (am_ew_reg g pos c regs2 [] 4 4%bv eq_refl); exact R4).
assert (HAE : env_agree 35 (am_env g pos c regs2 []) E) by (subst E; apply env_agree_refl).
clear HEE.
set (F := FA g pos) in *.
assert (FS3' : fs_frame_bytes 3 = 512) by (vm_compute; reflexivity).
(* keep the save area, the spills and the cursor; the image's two cells are not read here *)
lazymatch goal with HS : st_ok _ ?Ev ?ssv ?msv |- _ =>
  let l := eval vm_compute in (ss_mem ssv) in
  let kr := eval vm_compute in [stack_region 0; am_spill_region; am_cur_region] in
  assert (HS1 : st_ok tfibsegs Ev (mkSS (ss_pc ssv) (ss_regs ssv) kr (ss_resv ssv) (ss_facts ssv)) msv)
  by (apply (st_ok_submem tfibsegs Ev ssv msv _ HS); [change (submem kr l); submem_to | reflexivity]);
  clear HS; rename HS1 into HS end.
rewrite FS3' in Hfceil.
lazymatch goal with HS : st_ok _ ?Ev ?ssv ?msv |- _ =>
  assert (Hdj : all_disjoint Ev rd11_kn (ss_mem ssv)) by
    (cbn [ss_mem all_disjoint]; unfold extent_disjoint, rd11_kn, am_frame_region;
     cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite B2, B33; repeat split; lia);
  pose proof (ast_ok_add_region tfibsegs Ev ssv msv rd11_kn HS eq_refl Hrkn Hdj) as HS2;
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2; clear HS Hdj; rename HS2 into HS end.
assert (HFR : forall x, F <= x < F + 512 ->
  awr_byte LLVMF_STK (e_sp0 g) [] (ablocks B (e_ly g) (e_S g)) (ablocks B ly2 S2) ly2 [(3, pos)] x).
{ intros x Hx. right. right. right. exists 3, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
  rewrite EFA, FS3'. lia. }
assert (KE : forall x, 0 <= x < 2 ^ 64 -> ~ ((sp1 + 152 <= x < sp1 + 168) \/ (F + 240 <= x < F + 248)) ->
  aview tfibsegs (w_H W2) mem2 x = aview tfibsegs (w_H W2) mem2 x) by (intros; reflexivity).
cw_keep_j0 HJ HJ0.
unfold cfg_at. change (w64 PC_RD11M) with (Z_to_bv 64 PC_RD11M).
pose proof Hcur as (Hc & C152 & C160).
(* 0x8138c ld a0,160(s1) *)
cw_run ltac:(rd11_awr B2 B33 HFR).
cw_keep ltac:(rd11_kwr B2 B33).
(* 0x81390 bltu a2,a0: n0 < in.n keeps n = n0, else n = in.n *)
cw_branch Hb1.
all: rewrite branch_ltu_U, (U_atom E 12 n0 E12 ltac:(lia)), (U_atom E 36 (e_n g - c) E36 ltac:(lia)) in Hb1.
- apply Z.ltb_lt in Hb1.
  (* 0x81398-0x813b4: the cursor moves by n0, k.n = n0, a0 = k.bytes, jal *)
  cw_run ltac:(rd11_awr B2 B33 HFR).
  cw_keep ltac:(rd11_kwr B2 B33).
  rreg HS (10%bv : bv 5) Ga0. rreg HS (11%bv : bv 5) Ga1. rreg HS (12%bv : bv 5) Ga2.
  rreg HS (2%bv : bv 5) Ga2s. rreg HS (3%bv : bv 5) Ga3. rreg HS (4%bv : bv 5) Ga4.
  rewrite B33 in Ga0. rewrite E35 in Ga1. rewrite E12 in Ga2. rewrite E2 in Ga2s. rewrite E3 in Ga3. rewrite E4 in Ga4.
  pose proof (st_ok_region_nth E _ _ 0%nat _ HS eq_refl) as Rk.
  pose proof (st_ok_region_nth E _ _ 3%nat _ HS eq_refl) as Rc.
  cbn [ms_mem restrict] in Rk, Rc.
  pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ 240 8 (SOff 12 0) Rk B33 ltac:(cbn; tauto) ltac:(lia)) as VN.
  pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ 152 8 (SAlu ALU_ADD (SOff 12 0) (SOff 35 0)) Rc B2
    ltac:(cbn; tauto) ltac:(lia)) as V152.
  pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ 160 8 (SAlu ALU_ADD (SMd M_MUL (SOff 12 0) (SLit (-1))) (SOff 36 0))
    Rc B2 ltac:(cbn; tauto) ltac:(lia)) as V160.
  assert (U12 : bv_unsigned (sv_denot E (SOff 12 0)) = n0) by exact (U_atom E 12 n0 E12 ltac:(lia)).
  assert (U152 : bv_unsigned (sv_denot E (SAlu ALU_ADD (SOff 12 0) (SOff 35 0))) = e_p g + c + n0)
    by (replace (e_p g + c + n0) with (n0 + (e_p g + c)) by lia;
        exact (rd11_U_add E 12 35 n0 (e_p g + c) E12 E35 ltac:(lia) ltac:(lia) ltac:(unfold AM_HI in *; lia))).
  assert (U160 : bv_unsigned (sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff 12 0) (SLit (-1))) (SOff 36 0))) = e_n g - c - n0)
    by exact (rd11_U_sub E 12 36 n0 (e_n g - c) E12 E36 ltac:(lia) ltac:(lia)).
  rewrite U12 in VN. rewrite U152 in V152. rewrite U160 in V160.
  change (N.to_nat 8) with 8%nat in VN, V152, V160. change (8 * Z.of_N 8) with 64 in VN, V152, V160.
  rewrite Z.mod_small in VN, V152, V160 by (unfold AM_HI in *; lia).
  eapply (rd11_call g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c pv dv od a b n0 E _ _ _ HJ0 Hfr Hkj HMO HC Hops
    Hc1 ltac:(lia) Hpd Hkat Ha Hb ltac:(lia) HS eq_refl eq_refl ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HAE HJ
    Ga0 Ga1 Ga2 Ga2s Ga3 Ga4 KE V152 V160 VN).
- apply Z.ltb_ge in Hb1.
  (* 0x81394 mv a2,a0; 0x81398-0x813b4 as above, with n = in.n *)
  cw_run ltac:(rd11_awr B2 B33 HFR).
  cw_keep ltac:(rd11_kwr B2 B33).
  rreg HS (10%bv : bv 5) Ga0. rreg HS (11%bv : bv 5) Ga1. rreg HS (12%bv : bv 5) Ga2.
  rreg HS (2%bv : bv 5) Ga2s. rreg HS (3%bv : bv 5) Ga3. rreg HS (4%bv : bv 5) Ga4.
  rewrite B33 in Ga0. rewrite E35 in Ga1. rewrite E36 in Ga2. rewrite E2 in Ga2s. rewrite E3 in Ga3. rewrite E4 in Ga4.
  pose proof (st_ok_region_nth E _ _ 0%nat _ HS eq_refl) as Rk.
  pose proof (st_ok_region_nth E _ _ 3%nat _ HS eq_refl) as Rc.
  cbn [ms_mem restrict] in Rk, Rc.
  pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ 240 8 (SOff 36 0) Rk B33 ltac:(cbn; tauto) ltac:(lia)) as VN.
  pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ 152 8 (SAlu ALU_ADD (SOff 35 0) (SOff 36 0)) Rc B2
    ltac:(cbn; tauto) ltac:(lia)) as V152.
  pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ 160 8 (SLit 0) Rc B2 ltac:(cbn; tauto) ltac:(lia)) as V160.
  assert (U36 : bv_unsigned (sv_denot E (SOff 36 0)) = e_n g - c) by exact (U_atom E 36 (e_n g - c) E36 ltac:(lia)).
  assert (U152 : bv_unsigned (sv_denot E (SAlu ALU_ADD (SOff 35 0) (SOff 36 0))) = e_p g + c + (e_n g - c))
    by exact (rd11_U_add E 35 36 (e_p g + c) (e_n g - c) E35 E36 ltac:(lia) ltac:(lia) ltac:(unfold AM_HI in *; lia)).
  assert (U0 : bv_unsigned (sv_denot E (SLit 0)) = e_n g - c - (e_n g - c))
    by (replace (e_n g - c - (e_n g - c)) with 0 by lia; exact (U_lit E 0 ltac:(lia))).
  rewrite U36 in VN. rewrite U152 in V152. rewrite U0 in V160.
  change (N.to_nat 8) with 8%nat in VN, V152, V160. change (8 * Z.of_N 8) with 64 in VN, V152, V160.
  rewrite Z.mod_small in VN, V152, V160 by (unfold AM_HI in *; lia).
  eapply (rd11_call g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c pv dv od a b (e_n g - c) E _ _ _ HJ0 Hfr Hkj HMO HC Hops
    Hc1 ltac:(lia) Hpd Hkat Ha Hb ltac:(lia) HS eq_refl eq_refl ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HAE HJ
    Ga0 Ga1 Ga2 Ga2s Ga3 Ga4 KE V152 V160 VN).
Qed.

(* The meeting point 0x8138c from the head's last executor state: its journal, the zone it wrote (k.a and k.b),
   the cursor's two chunks (j bytes taken), a, b and a2 = n0; then the tail. *)
Lemma rd11_mid_end : forall g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od Ef ss ms md3 j a b n0,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 k ->
frames S2 = [(3, pos)] -> 0 <= k <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 -> ops_at ops regs2 ->
k_at g pos (k_rdZ 11 pv dv) W2 mem2 -> pd_okA pv dv od -> 1 <= c ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2
  (ms_mem ms) md3 k ->
env_agree 40 (am_env g pos c regs2 ys) Ef ->
st_ok tfibsegs Ef ss (restrict (w_H W2) ms) -> ss_pc ss = PC_RD11M -> ss_resv ss = None ->
am_keep_ok (ss_regs ss) = true -> sr_get (ss_regs ss) 26%bv = SOff 26 0 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ rd_zone g pos sp1 24 32 x ->
   aview tfibsegs (w_H W2) (ms_mem ms) x = aview tfibsegs (w_H W2) mem2 x) ->
YP09.chunk_ok tfibsegs Ef (mrestrict (w_H W2) (ms_mem ms)) sp1 (YP09.mkChunk 152 (CVal 8 (SOff 35 j))) ->
YP09.chunk_ok tfibsegs Ef (mrestrict (w_H W2) (ms_mem ms)) sp1 (YP09.mkChunk 160 (CVal 8 (SOff 36 (- j)))) ->
0 <= j -> c + j <= e_n g ->
getr (ms_regs ms) 12 = w64 n0 -> 0 <= n0 <= 24 -> 0 <= a < 256 -> 0 <= b < 256 ->
val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms)) (FA g pos + 200) 4 a ->
val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms)) (FA g pos + 204) 4 b ->
SRr tfibsegs W2 {| cfg_ms := ms; cfg_model := md3 |} (inv_run B MT K XM_LIB g pos sp1 ops).
Proof.
intros g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od Ef ss ms md3 j a b n0
  HJ Hfr Hk Hmo HC Hops Hkat Hpd Hc1 HJ3 HAG HS Hpc Hresv Hkeep H26 KE Ca Cb Hj Hcj G12 Hn0 Ha Hb Va Vb.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hng & Hp & Hpn & _).
unfold AM_HI in Hpn.
destruct (rd_zone_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (Happ & Hf4096 & Hfc & Hsp0 & Hsp & Hsp47 & Hclo).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W2) Ef ss ms HS Hresv) as Ems.
rewrite Hpc in Ems.
pose proof HS as HS'. rewrite Ems in HS'.
pose proof Hkat as Hkat0.
destruct HAG as (HA & HD).
assert (E35 : ew Ef 35 = Z_to_bv 64 (e_p g + c)) by (rewrite (HA 35%nat ltac:(lia)); exact (am_ew_CP g pos c regs2 ys)).
assert (E36 : ew Ef 36 = Z_to_bv 64 (e_n g - c)) by (rewrite (HA 36%nat ltac:(lia)); exact (am_ew_CN g pos c regs2 ys)).
assert (HC3 : mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 (ms_regs ms) (ms_mem ms) md3).
{ apply (am_exit B MT K XM_LIB LAWS g pos sp1 0 0 c ys ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) md3
    k (Z_to_bv 64 PC_RD11M) ss Ef HC HJ3 ltac:(split; [intros i Hi; apply HA; lia | exact HD]) HS' Hkeep).
  - intros x Hx. apply KE.
    + unfold am_keepzone in Hx. lia.
    + exact (rd_keep_apart g pos sp1 24 32 x Hf4096 Hfc Hsp0 Hsp ltac:(lia) ltac:(lia) Hx).
  - intros i Hi. pose proof HC as HSH. do 43 (destruct HSH as (_ & HSH)). destruct HSH as (HSH' & _).
    rewrite <- (HSH' i Hi). apply KE.
    + unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_mod (FA g pos) 8 ltac:(lia)) as D.
      pose proof (Z.mod_pos_bound (FA g pos) 8 ltac:(lia)) as M. lia.
    + exact (rd_shadow_apart g pos sp1 24 32 i Happ Hf4096 Hfc Hsp0 Hsp Hclo ltac:(lia) ltac:(lia) Hi).
  - pose proof HC as HPerm. do 45 (destruct HPerm as (_ & HPerm)). exact HPerm. }
rewrite Ems.
change {| cfg_ms := mkst (ms_regs ms) (Z_to_bv 64 PC_RD11M) (ms_mem ms) (seg_rom tfibsegs); cfg_model := md3 |}
  with (cfg_at tfibsegs PC_RD11M (ms_regs ms) (ms_mem ms) md3).
apply rd11_tail.
apply (am_mcut B MT K XM_LIB g pos sp1 0 PC_RD11M _ ly2 S2 W2 (ms_regs ms) (ms_mem ms) md3 k HJ3 Hfr Hk Hmo HC3).
cbv beta. split.
- destruct Hops as (Hops' & R26). split; [exact Hops'|].
  rewrite (st_ok_restrict_reg tfibsegs (w_H W2) Ef ss ms 26%bv HS), H26. cbn [sv_denot].
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (HA 26%nat ltac:(lia)).
  rewrite (am_ew_reg g pos c regs2 ys 26 26%bv eq_refl). exact R26.
- exists (c + j), pv, dv, od, a, b, n0.
  split; [exact (rd_cur g sp1 c j W2 (ms_mem ms) Ef Ca Cb E35 E36 ltac:(lia) Hj Hcj ltac:(lia) ltac:(lia))|].
  split; [lia|]. split; [exact Hpd|].
  split.
  { change (rd11_kab pv dv a b) with (rdk 11 pv dv a b 0 0 (repeat 0 24)).
    apply (rd_kat g pos W2 mem2 (ms_mem ms) 11 pv dv a b 0 0 (repeat 0 24) Hkat0).
    - intros x Hx Hw. apply KE; [lia|]. unfold rd_zone. lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - apply repeat_length.
    - replace (FA g pos + 176 + 24) with (FA g pos + 200) by lia. exact Va.
    - replace (FA g pos + 176 + 28) with (FA g pos + 204) by lia. exact Vb.
    - apply (rd_kept4 g pos sp1 W2 mem2 (ms_mem ms) 11 pv dv 24 32 32 Hkat0 KE ltac:(lia) ltac:(lia) ltac:(lia)
        ltac:(lia) ltac:(lia)).
    - apply (rd_kept4 g pos sp1 W2 mem2 (ms_mem ms) 11 pv dv 24 32 36 Hkat0 KE ltac:(lia) ltac:(lia) ltac:(lia)
        ltac:(lia) ltac:(lia)).
    - destruct Hkat0 as ((_ & _ & _ & _ & _ & _ & _ & Vy & _) & _). cbn [kz_bytes k_rdZ] in Vy.
      apply (rd_garr8_kept (w_H W2) (w_H W2) mem2 (ms_mem ms)); [|exact Vy].
      intros x Hx. rewrite repeat_length in Hx. cbn [Z.of_nat] in Hx. apply KE; [lia|]. unfold rd_zone. lia. }
  split; [exact Ha|]. split; [exact Hb|]. split; [exact G12 | exact Hn0].
Qed.

(* the cursor's two chunks of the state (atom 2 = sp1) *)
Ltac rd11_cur_t B2 :=
lazymatch goal with HS : YP0l.st_ok _ _ _ _ |- _ =>
  let Ca := fresh "Ca" in let Cb := fresh "Cb" in
  rd_chunk HS 2%nat 152 Ca; rd_chunk HS 2%nat 160 Cb;
  rewrite ?ew_ewset_other in Ca, Cb by lia; rewrite B2 in Ca, Cb end.
(* k.a and k.b from the 8-byte store of 0 at k.a *)
Ltac rd11_kab8_t B33 :=
lazymatch goal with HS : YP0l.st_ok _ ?Ef _ _ |- _ =>
  let C := fresh "C" in let V8 := fresh "V8" in
  rd_chunk HS 33%nat 200 C;
  rewrite ?ew_ewset_other in C by lia; rewrite B33 in C;
  lazymatch type of C with YP09.chunk_ok _ _ _ ?base _ =>
    pose proof (rd_val_of_chunk Ef _ base 200 8 (SLit 0) C) as V8 end;
  cbn [sv_denot] in V8; rewrite unsigned_lit_small in V8 by lia; change (N.to_nat 8) with 8%nat in V8;
  lazymatch type of V8 with val_mem _ _ ?ad _ _ => destruct (rd11_vm8_0 _ ad V8) as (Va & Vb) end;
  lazymatch goal with Vb : val_mem _ _ (?bb + 200 + 4) _ _ |- _ =>
    replace (bb + 200 + 4) with (bb + 204) in Vb by lia end;
  clear C V8 end.
(* k.a (offset 200) from the chunk that holds the atom an, whose value is xv *)
Ltac rd11_va_t B33 E HAE an xv EYc :=
lazymatch goal with HS : YP0l.st_ok _ ?Ef _ _ |- _ =>
  let C := fresh "C" in let UA := fresh "UA" in let AG := fresh "AG" in let Va := fresh "Va" in
  rd_chunk HS 33%nat 200 C;
  rewrite ?ew_ewset_other in C by lia; rewrite B33 in C;
  lazymatch type of C with YP09.chunk_ok _ _ _ ?base _ =>
    pose proof (rd_chunk_u32 Ef _ base 200 (SOff an 0) C) as Va end;
  assert (AG : env_agree 40 E Ef) by env_agree_chain HAE;
  assert (UA : bv_unsigned (sv_denot Ef (SOff an 0)) = xv) by
    (change (bv_unsigned (sv_denot Ef (SOff an 0))) with (U Ef (SOff an 0));
     apply (U_atom Ef an xv); [rewrite (rd_ag 40 E Ef an AG ltac:(lia)); exact EYc | lia]);
  rewrite UA in Va; rewrite Z.mod_small in Va by lia; clear C UA AG end.
(* k.b (offset 204), the same *)
Ltac rd11_vb_t B33 E HAE an xv EYc :=
lazymatch goal with HS : YP0l.st_ok _ ?Ef _ _ |- _ =>
  let C := fresh "C" in let UA := fresh "UA" in let AG := fresh "AG" in let Vb := fresh "Vb" in
  rd_chunk HS 33%nat 204 C;
  rewrite ?ew_ewset_other in C by lia; rewrite B33 in C;
  lazymatch type of C with YP09.chunk_ok _ _ _ ?base _ =>
    pose proof (rd_chunk_u32 Ef _ base 204 (SOff an 0) C) as Vb end;
  assert (AG : env_agree 40 E Ef) by env_agree_chain HAE;
  assert (UA : bv_unsigned (sv_denot Ef (SOff an 0)) = xv) by
    (change (bv_unsigned (sv_denot Ef (SOff an 0))) with (U Ef (SOff an 0));
     apply (U_atom Ef an xv); [rewrite (rd_ag 40 E Ef an AG ltac:(lia)); exact EYc | lia]);
  rewrite UA in Vb; rewrite Z.mod_small in Vb by lia; clear C UA AG end.
(* k.b when the chunk is the literal 0 *)
Ltac rd11_vbz_t B33 :=
lazymatch goal with HS : YP0l.st_ok _ ?Ef _ _ |- _ =>
  let C := fresh "C" in let Vb := fresh "Vb" in
  rd_chunk HS 33%nat 204 C;
  rewrite ?ew_ewset_other in C by lia; rewrite B33 in C;
  lazymatch type of C with YP09.chunk_ok _ _ _ ?base _ =>
    pose proof (rd_chunk_u32 Ef _ base 204 (SLit 0) C) as Vb end;
  cbn [sv_denot] in Vb; rewrite unsigned_lit_small in Vb by lia;
  rewrite Z.mod_small in Vb by lia; clear C end.
(* the meeting point from the state of the head's last run *)
Ltac rd11_fin_t g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc1 HAE HEE j a b n0 :=
lazymatch goal with
| HS : YP0l.st_ok _ ?Ef ?ssf (restrict (w_H ?W) ?msf), HJm : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  KEh : forall x, _ -> ~ rd_zone _ _ _ _ _ x -> _,
  Cah : YP09.chunk_ok _ _ _ _ (YP09.mkChunk 152 _), Cbh : YP09.chunk_ok _ _ _ _ (YP09.mkChunk 160 _),
  Vah : val_mem _ _ (_ + 200) _ _, Vbh : val_mem _ _ (_ + 204) _ _,
  G12h : getr _ 12%bv = _ |- _ =>
  rewrite ?wvb_collapse in HJm;
  exact (rd11_mid_end g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od Ef ssf msf _ j a b n0
    HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc1 HJm ltac:(rewrite <- HEE; env_agree_chain HAE) HS
    ltac:(reflexivity) ltac:(reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    KEh Cah Cbh ltac:(lia) ltac:(lia) G12h ltac:(lia) ltac:(lia) ltac:(lia) Vah Vbh)
end.

Definition rd11_AF : list (nat * afact) :=
[(37%nat, mkAF 0 255 0); (38%nat, mkAF 0 255 0); (39%nat, mkAF 0 255 0)].

Theorem seg_rd11_holds : seg_rd_run B MT K XM_LIB 11.
Proof.
intros g pos sp1 ops W2 c2 Hrd.
destruct Hrd as (ly2 & S2 & regs2 & mem2 & md2 & k & -> & HJ & Hfr & Hk & Hmo & HC & HP).
destruct HP as (Hops & Hkind & c & pv & dv & od & Hcur & Hc1 & Hpd & R23 & Hkat).
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & Hblk).
unfold AM_HI in Hchi, Hpn.
pose proof Hcur as (Hc & C152 & C160).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
set (ys := [rd_ib g c; rd_ib g (c + 1); rd_ib g (c + 2)]).
assert (HAF : atoms_ok (am_env g pos c regs2 ys) rd11_AF).
{ unfold rd11_AF. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  pose proof (am_ew_y g pos c regs2 ys 0) as Y0. pose proof (am_ew_y g pos c regs2 ys 1) as Y1.
  pose proof (am_ew_y g pos c regs2 ys 2) as Y2.
  unfold AM_X0 in Y0, Y1, Y2. cbn [Nat.add] in Y0, Y1, Y2. rewrite Y0, Y1, Y2.
  cbn [nth ys]. pose proof (rd_ib_range g c). pose proof (rd_ib_range g (c + 1)). pose proof (rd_ib_range g (c + 2)).
  rewrite !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; lia. }
destruct (rd_start B MT K XM_LIB TL LAWS g pos sp1 ly2 S2 W2 regs2 mem2 md2 k c ys rd11_AF (rd_pc 11) 24 32 []
  HJ Hfr HC Hcur ltac:(lia) ltac:(lia) ltac:(lia) (Forall_nil _) eq_refl HAF) as [HS SHOK].
assert (HAE : env_agree 40 (am_env g pos c regs2 ys) (am_env g pos c regs2 ys)) by apply env_agree_refl.
remember (am_env g pos c regs2 ys) as E eqn:HEE.
assert (B2 : bv_unsigned (ew E 2) = sp1).
{ subst E. pose proof HC as (_ & _ & R2 & _). rewrite (am_ew_reg g pos c regs2 ys 2 2%bv eq_refl), R2. unfold w64.
  apply unsigned_lit_small. lia. }
assert (B33 : bv_unsigned (ew E 33) = FA g pos) by (subst E; rewrite (am_ew_F g pos c regs2 ys); apply unsigned_lit_small; lia).
assert (E35 : ew E 35 = Z_to_bv 64 (e_p g + c)) by (subst E; exact (am_ew_CP g pos c regs2 ys)).
assert (E36 : ew E 36 = Z_to_bv 64 (e_n g - c)) by (subst E; exact (am_ew_CN g pos c regs2 ys)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; exact (am_ew_SB g pos c regs2 ys)).
assert (EY0 : ew E 37 = Z_to_bv 64 (rd_ib g (c + Z.of_nat 0))) by (subst E; rewrite Z.add_0_r; exact (am_ew_y g pos c regs2 ys 0)).
assert (EY1 : ew E 38 = Z_to_bv 64 (rd_ib g (c + Z.of_nat 1))) by (subst E; exact (am_ew_y g pos c regs2 ys 1)).
assert (EY2 : ew E 39 = Z_to_bv 64 (rd_ib g (c + Z.of_nat 2))) by (subst E; exact (am_ew_y g pos c regs2 ys 2)).
assert (EY0c : ew E 37 = Z_to_bv 64 (rd_ib g c)) by (rewrite EY0; do 2 f_equal; lia).
assert (EY1c : ew E 38 = Z_to_bv 64 (rd_ib g (c + 1))) by (rewrite EY1; do 2 f_equal; lia).
assert (EY2c : ew E 39 = Z_to_bv 64 (rd_ib g (c + 2))) by (rewrite EY2; do 2 f_equal; lia).
pose proof (rd_ib_range g c) as RB0. pose proof (rd_ib_range g (c + 1)) as RB1.
pose proof (rd_ib_range g (c + 2)) as RB2.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ rd_zone g pos sp1 24 32 a ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
pose proof (rd_in_sep B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as HSEP.
cw_keep_j0 HJ HJ0.
unfold cfg_at. change (w64 (rd_pc 11)) with (Z_to_bv 64 0x80c9c). change (rd_pc 11) with 0x80c9c in HS.
(* 0x80c9c ld a1,160(s1); to the in.n test at 0x80ca0 *)
rd11_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
cw_branch Hb1; rd11_brn Hb1 E36.
- (* in.n = 0: 0x81274 stores 0 into a and b with one 8-byte store, n = 0 *)
  rd11_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
  rd11_cur_t B2. rd11_kab8_t B33.
  rreg HS (12%bv : bv 5) G12.
  rd11_fin_t g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc1 HAE HEE 0 0 0 0.
- rd_in_add LAWS HJ0 Hfr HC c 0%nat E35 EY0 HSEP.
  (* byte 0 = k.a (0x80ccc-0x80cd0); to the test of in.n - 1 at 0x80cd4 *)
  rd11_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
  cw_branch Hb2; rd11_brn Hb2 E36.
  + (* in.n = 1: 0x8132c stores b = 0, 0x81388 leaves n = 0 *)
    rd11_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
    rd11_cur_t B2. rd11_va_t B33 E HAE 37%nat (rd_ib g c) EY0c. rd11_vbz_t B33.
    rreg HS (12%bv : bv 5) G12.
    rd11_fin_t g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc1 HAE HEE
      1 (rd_ib g c) 0 0.
  + rd_in_add LAWS HJ0 Hfr HC c 1%nat E35 EY1 HSEP.
    (* byte 1 = k.b (0x80d00, 0x81334); to the test of in.n - 2 at 0x81338 *)
    rd11_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
    cw_branch Hb3; rd11_brn Hb3 E36.
    * (* in.n = 2: 0x81388 leaves n = 0 *)
      rd11_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
      rd11_cur_t B2. rd11_va_t B33 E HAE 37%nat (rd_ib g c) EY0c.
      rd11_vb_t B33 E HAE 38%nat (rd_ib g (c + 1)) EY1c.
      rreg HS (12%bv : bv 5) G12.
      rd11_fin_t g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc1 HAE HEE
        2 (rd_ib g c) (rd_ib g (c + 1)) 0.
    * rd_in_add LAWS HJ0 Hfr HC c 2%nat E35 EY2 HSEP.
      (* byte 2 = the length byte; n = byte % 25 (0x81364-0x81380) *)
      rd11_run_t LAWS HJ0 Hfr HC c E35 E32 B2 B33 EFA. cw_keep ltac:(rdj_kwr B2 B33).
      rd11_cur_t B2. rd11_va_t B33 E HAE 37%nat (rd_ib g c) EY0c.
      rd11_vb_t B33 E HAE 38%nat (rd_ib g (c + 1)) EY1c.
      lazymatch goal with HS : YP0l.st_ok _ ?Ef ?ssf (restrict (w_H ?Wf) ?msf) |- _ =>
        let e := eval vm_compute in (sr_get (ss_regs ssf) (12%bv : bv 5)) in
        assert (AGn : env_agree 40 E Ef) by env_agree_chain HAE;
        assert (G12 : getr (ms_regs msf) (12%bv : bv 5) = Z_to_bv 64 (rd_ib g (c + 2) mod 25)) by
          (refine (eq_trans (st_ok_restrict_reg tfibsegs (w_H Wf) Ef ssf msf (12%bv : bv 5) HS) _);
           change (sr_get (ss_regs ssf) (12%bv : bv 5)) with e;
           rewrite denot_lit_U;
           rewrite (rd11_U_n0 Ef 39 (rd_ib g (c + 2))
             ltac:(rewrite (rd_ag 40 E Ef 39%nat AGn ltac:(lia)); exact EY2c) ltac:(lia));
           reflexivity) end.
      pose proof (Z.mod_pos_bound (rd_ib g (c + 2)) 25 ltac:(lia)) as RM.
      rd11_fin_t g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc1 HAE HEE
        3 (rd_ib g c) (rd_ib g (c + 1)) (rd_ib g (c + 2) mod 25).
Qed.
End b.
End a.
