(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACai.v:155-159
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbl.v:141-145 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:140-148, 156-160 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-370
   [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan build (lib/B). The [Apache-2.0 OR MIT] text is used
   under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_A.v, with its module paths and module names changed; 212 of its 260 lines of code are new or changed and 760 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_entry_a.v, with its module paths and module names changed; 20 of its 45 lines of code are new or changed and 235 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/AU/Prog/codec_bmain_rdb.v, with its module paths and module names changed; 627 of its 656 lines of code are new or changed and 16 lines of the source are left out. *)
(* Segment RD11 (SYSEX) of the image-B walk of LLVMFuzzerTestOneInput: seg_rd_run 11 of
   lib/AU/Prog/codec_bmain_inv.v, from the reader cut at 0x80e48 to RUN 0x826f4. The image-A walk of the same
   segment (lib/A/Prog/codec_amain_rd11.v) at image B.
   - 0x80e48 .. 0x81580: k.a = fuzz_u8 (sw 24(s7) at 0x80e88), k.b = fuzz_u8 (sw 28(s7) at 0x80ec8),
     n0 = fuzz_u8 % 25 (0x80f08-0x80f20: mul 41, srli 10, mul 25, subw, zext.b). Each input byte is read behind
     its tests (in.n, the cursor's UBSan check, the instrumented check). A missing byte reads 0 (0x81574 /
     0x8157c store 0 into a and b, 0x81578 / 0x83020 set n0 = 0). The four paths meet at 0x81580 (the cut
     rd11_mid), each explored as in codec_bmain_rdb_lib.v (rd11_explore, rd11_mfin).
   - 0x81580 .. 0x815c4 (rd11_tail): n = min(n0, in.n) (bltu at 0x81584), the UBSan checks of `in->p += n`
     (fuzz.h:67: 0x81594 bgeu p + n, p (no wrap) and 0x815a8 (p = 0) = (p + n <> 0)), refuted by 4096 <= p and
     p + n below the allocator ceiling: the engine decides a check from the atoms' ranges (n0 in [0, 24] is an
     atom fact of the tail's state), and a check it leaves open is split with the side that reaches the trap
     refuted by its condition over Z (rd11_to_call); the cursor moves by n, k.n = n (sd 64(s7)), a0 = k.bytes =
     F + 232 (the spill 120(sp1)), a1 = the old in.p, a2 = n, jal __asan_memcpy (0x51ae8, through
     CPgWalkIntrU.cw_intrin_call: destination k.bytes in the frame, source the input block), then j 0x826f4
     (codec_bmain_encl.v bm_jump).
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC CPgSat.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CodecRo CodecGlobs CPgWalkU CPgWalkIntrU CPgWalkImgU CPgSatU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_inv codec_bmain_st codec_bmain_encl.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgTokJU codec_bmain_rdlib codec_bmain_rdin codec_bmain_rdb_lib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ================================ the record ================================ *)
(* k at the meeting point 0x81580: HEAD's record with kind 11, a and b stored *)
Definition rd11_kab (pv dv a b : Z) : kcallZ :=
mkKcallZ 11 pv dv a b 0 0 (repeat 0 24) 0 0 fa5 fa5 0 (repeat 0 24) 0 0 0.
(* k at RUN: bytes and n as the tail leaves them *)
Definition rd11_kfin (pv dv a b : Z) (bs : list Z) (t : Z) : kcallZ :=
mkKcallZ 11 pv dv a b 0 0 bs t 0 fa5 fa5 0 (repeat 0 24) 0 0 0.
(* the input bytes, and the t of them from the cursor c on *)
Definition rd11_inp (g : ectx) : list Z := map (fun x : byte => bv_unsigned x) (e_pl g).
Definition rd11_src (g : ectx) (c t : Z) : list Z :=
map (fun j => nth (Z.to_nat c + j) (rd11_inp g) 0) (seq 0 (Z.to_nat t)).
Definition PC_RD11M : Z := 0x81580.

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

Lemma rd11_enc_ok : forall pv dv a b t src od, pd_okB pv dv od -> 0 <= a < 256 -> 0 <= b < 256 -> 0 <= t <= 24 ->
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
(* 0x80f08-0x80f20: x * 41 >> 10 is x / 25, so the subtraction and the zero extension leave x mod 25 *)
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
{ intros x l H1 H2 Hg. apply (rd_garr8_kept (w_H W) (w_H W) m m'); [|exact Hg].
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
Hypothesis AMEMCPY : aintrin_realizes tfibsegs B OCpy BM_asan_memcpy.

(* the meeting point 0x81580: a, b stored, a2 = n0 (the length byte % 25, or 0) *)
Definition rd11_mid (g : ectx) (pos sp1 ops : Z) : world tfibsegs -> config -> Prop :=
mcut B MT K XM_LIB g pos sp1 0 PC_RD11M (fun ly2 S2 W2 regs2 mem2 md2 =>
ops_at ops regs2 /\ exists c pv dv od a b n0, cur_at g sp1 c W2 mem2 /\ 1 <= c /\ pd_okB pv dv od /\
k_at g pos (rd11_kab pv dv a b) W2 mem2 /\ 0 <= a < 256 /\ 0 <= b < 256 /\
getr regs2 12 = w64 n0 /\ 0 <= n0 <= 24).

(* The state at the entry of __asan_memcpy (0x51ae8, ra = 0x815c8), from the meeting point's facts: the copy of
   the t input bytes at the cursor into k.bytes, the reseat at 0x815c8, the exit to the cut there and the
   `j 0x826f4` to RUN. *)
Lemma rd11_call : forall g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c pv dv od a b t Es ss ms md,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 kj ->
frames S2 = [(3, pos)] -> 0 <= kj <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
ops_at ops regs2 -> 1 <= c -> c + t <= e_n g -> pd_okB pv dv od ->
k_at g pos (rd11_kab pv dv a b) W2 mem2 -> 0 <= a < 256 -> 0 <= b < 256 -> 0 <= t <= 24 ->
st_ok tfibsegs Es ss (restrict (w_H W2) ms) -> ss_pc ss = BM_asan_memcpy -> ss_resv ss = None ->
ss_atoms_lt 40 ss = true -> sr_get (ss_regs ss) 1%bv = SLit 0x815c8 ->
bm_keep_ok (ss_regs (ss_after_call ss [] 40 0x815c8)) = true ->
sr_get (ss_regs (ss_after_call ss [] 40 0x815c8)) 20%bv = SOff 20 0 ->
env_agree 35 (bm_env g pos c regs2 []) Es ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 (ms_mem ms) md kj ->
getr (ms_regs ms) 10 = w64 (FA g pos + 232) -> getr (ms_regs ms) 11 = w64 (e_p g + c) -> getr (ms_regs ms) 12 = w64 t ->
getr (ms_regs ms) 2 = w64 sp1 -> getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
(forall x, 0 <= x < 2 ^ 64 -> ~ rd_zone g pos sp1 64 72 x ->
   aview tfibsegs (w_H W2) (ms_mem ms) x = aview tfibsegs (w_H W2) mem2 x) ->
val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms)) (sp1 + 184) 8 (e_p g + c + t) ->
val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms)) (sp1 + 192) 8 (e_n g - c - t) ->
val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms)) (FA g pos + 256) 8 t ->
SRr tfibsegs W2 (mkCfg ms md) (inv_run B MT K XM_LIB g pos sp1 ops).
Proof.
intros g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c pv dv od a b t Es ss ms md
  HJs Hfr Hkj HMO HC Hops Hc1 Hct Hpd Hkat Ha Hb Ht HS Hpc Hrv Hat Hra Hkeep R20 HAE HJ
  G10 G11 G12 G2 G3 G4 KE V184 V192 VN.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJs Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & Hblk).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
assert (FS3' : fs_frame_bytes 3 = 512) by (vm_compute; reflexivity).
assert (HES : ESTACK = 4096) by reflexivity.
rewrite FS3' in Hfceil. unfold BM_HI in Hchi, Hpn.
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
pose proof HC as HSH. do 47 (destruct HSH as (_ & HSH)). destruct HSH as (HSH0 & Hga & HPerm).
pose proof HC as (Hpre & _).
pose proof Hpre as HPRE. unfold e_pre, codec_lib_pre_x in HPRE.
destruct HPRE as (_ & _ & _ & _ & _ & Hnpl & _).
(* the frame's shadow, and k's 23 usable shadow bytes, at the call *)
assert (HSHc : forall i, 0 <= i < 60 ->
  aview tfibsegs (w_H W2) (ms_mem ms) (shadow_addr F + i) = Some (nth (Z.to_nat i) (shm 0) 0)).
{ intros i Hi. pose proof (HSA i ltac:(lia)) as Hs. rewrite KE by (unfold rd_zone; lia). exact (HSH0 i Hi). }
assert (HBSc : block_shadow (aview tfibsegs (w_H W2) (ms_mem ms)) SHADOW_OFF (F + 192) 184).
{ apply bm_block_shadow; [exact Hf64 | lia | reflexivity | lia |].
  intros i Hi. change ((184 + 7) / 8) with 23 in Hi. change (184 / 8) with 23. change (192 / 8) with 24.
  rewrite (proj2 (Z.ltb_lt i 23) ltac:(lia)).
  rewrite (HSHc (24 + i) ltac:(lia)). f_equal.
  pose proof bmain_pure_sat as (_ & _ & _ & _ & _ & _ & _ & Hk23 & _).
  apply (Hk23 0 (Z.to_nat (24 + i))). lia. }
assert (Hdra : range_addressable (aview tfibsegs (w_H W2) (ms_mem ms)) SHADOW_OFF (F + 232) t)
  by (apply (block_shadow_range _ SHADOW_OFF (F + 192) 184 (F + 232) t HBSc); lia).
assert (Hdam : amem_range (F + 232) t) by (unfold amem_range; rewrite C3, C4, C5; lia).
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
(* 0x815c4 jal __asan_memcpy *)
refine (cw_intrin_call B LAWS OCpy BM_asan_memcpy AMEMCPY W2 Es ss ms md LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g)
  (e_mem g) (e_md g) [(3, pos)] ly2 S2 kj (F + 232) (e_p g + c) t 0x815c8 40%nat [] _ HS Hpc Hrv HJ G10 G11 G12
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
- intros Hn0. exact (sat_frame_hull tfibsegs B LAWS ly2 S2 W2 (ms_mem ms) md 3 pos F 232 t HARc Hin3 EFA Hf64
    ltac:(rewrite FS3'; reflexivity) ltac:(lia) Hn0 ltac:(rewrite FS3'; lia)).
- split; [lia|]. split; [lia|]. split.
  { intros y Hy. split; [apply Hxv; lia | rewrite SPZ, HES; lia]. }
  split; [lia|]. split; [exact Hxam|]. split; [exact Hxra | exact Hxhull].
- intros regs3 mem3 md3 HJ3 HP3 Ha03 Hcpy Hkept Hpres3 Hsm HS3.
  cbv beta iota in Hcpy. rewrite SPZ, HES in Hkept.
  assert (KF : forall x, 0 <= x < 2 ^ 64 -> ~ rd_zone g pos sp1 64 72 x ->
    ~ (F + 232 <= x < F + 232 + t) -> ~ (sp1 - 4096 <= x < sp1) ->
    aview tfibsegs (w_H W2) mem3 x = aview tfibsegs (w_H W2) mem2 x).
  { intros x Hx Hz Hd Hs. rewrite (Hkept x Hx Hd Hs). exact (KE x Hx Hz). }
  (* 0x815c8 j 0x826f4 *)
  unfold inv_run.
  refine (bm_jump B MT K XM_LIB LAWS g pos sp1 0 0x815c8 PC_RUN _ W2 _ _ _ _ _);
    [vm_compute; reflexivity | unfold PC_RUN; lia | intros ? ? ? ? ? ? ? HP0; exact HP0 |].
  change (mkCfg (mkst regs3 (Z_to_bv 64 0x815c8) mem3 (seg_rom tfibsegs)) md3)
    with (cfg_at tfibsegs 0x815c8 regs3 mem3 md3).
  apply (bm_mcut B MT K XM_LIB g pos sp1 0 0x815c8 _ ly2 S2 W2 regs3 mem3 md3 kj HJ3 Hfr Hkj HMO).
  + apply (bm_exit B MT K XM_LIB LAWS g pos sp1 0 0 c [] ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 regs3 mem3 md3 kj
      (Z_to_bv 64 0x815c8) (ss_after_call ss [] 40 0x815c8) (havoc Es 40 (map (getr regs3) CLOB)) HC HJ3).
    * apply env_agree_havoc_ge; [lia | exact HAE].
    * exact HS3.
    * exact Hkeep.
    * intros x Hx. unfold bm_keepzone in Hx. apply KF; unfold rd_zone; lia.
    * intros i Hi. change (FA g pos) with F. pose proof (HSA i ltac:(lia)) as Hs.
      rewrite KF by (unfold rd_zone; lia). exact (HSH0 i Hi).
    * exact HPerm.
  + split.
    { destruct Hops as (Hops0 & R20o). split; [exact Hops0|].
      pose proof (st_ok_restrict_reg tfibsegs (w_H W2) _ _ _ 20%bv HS3) as G20. cbn [ms_regs mkst] in G20.
      rewrite R20 in G20. cbn [sv_denot] in G20. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, ew_havoc_old in G20 by lia.
      first [rewrite (proj1 HAE 20%nat ltac:(lia)) in G20 | rewrite <- (proj1 HAE 20%nat ltac:(lia)) in G20].
      rewrite (bm_ew_reg g pos c regs2 [] 20 20%bv eq_refl) in G20. rewrite G20. exact R20o. }
    exists (c + t), (rd11_kfin pv dv a b (rd11_src g c t ++ repeat 0 (24 - Z.to_nat t)) t), od.
    split.
    { split; [lia|]. split.
      - replace (e_p g + (c + t)) with (e_p g + c + t) by lia.
        apply (cw_val_mem_kept (w_H W2) (w_H W2) (ms_mem ms) mem3); [|exact V184].
        intros y Hy. apply Hkept; cbn in Hy; lia.
      - replace (e_n g - (c + t)) with (e_n g - c - t) by lia.
        apply (cw_val_mem_kept (w_H W2) (w_H W2) (ms_mem ms) mem3); [|exact V192].
        intros y Hy. apply Hkept; cbn in Hy; lia. }
    pose proof (rd11_src_len g c t) as Hsl.
    assert (Hsrc : forall j, (j < Z.to_nat t)%nat ->
      aview tfibsegs (w_H W2) mem3 (F + 232 + Z.of_nat j) = Some (nth j (rd11_src g c t) 0) /\
      0 <= nth j (rd11_src g c t) 0 < 256).
    { intros j Hj. rewrite (rd11_src_nth g c t j Hj).
      assert (Hjl : (Z.to_nat c + j < length (rd11_inp g))%nat).
      { unfold rd11_inp. rewrite length_map. lia. }
      destruct (Hga (Z.to_nat c + j)%nat Hjl) as (Gv & Gr). split; [|exact Gr].
      rewrite (Hcpy (Z.of_nat j) ltac:(lia)).
      rewrite KE by (unfold rd_zone; lia).
      replace (e_p g + c + Z.of_nat j) with (e_p g + Z.of_nat (Z.to_nat c + j)) by lia.
      exact (rd11_aview_vm1 _ _ _ _ Gv Gr). }
    split; [split|].
    * apply (rd11_k_final W2 mem2 mem3 (F + 192) pv dv a b t (rd11_src g c t) (proj1 Hkat) Ht Hsl).
      ** intros o Ho H1 H2. apply KF; unfold rd_zone; lia.
      ** intros j Hj. destruct (Hsrc j Hj) as (Hv & Hr). split; [|exact Hr].
         destruct (bm_mb W2 mem3 _ _ Hv) as (Hm & _).
         replace (F + 192 + 40 + Z.of_nat j) with (F + 232 + Z.of_nat j) by lia.
         exact (cpg_val_mem1 _ _ _ Hr Hm).
      ** replace (F + 192 + 64) with (F + 256) by lia.
         apply (cw_val_mem_kept (w_H W2) (w_H W2) (ms_mem ms) mem3); [|exact VN].
         intros y Hy. apply Hkept; cbn in Hy; lia.
    * pose proof (proj2 Hkat) as (_ & Hpv & Hdv & _).
      apply rd11_kfin_wf; [exact Hpv | exact Hdv | exact Ha | exact Hb | exact Ht | exact Hsl].
    * apply rd11_enc_ok; [exact Hpd | exact Ha | exact Hb | exact Ht | exact Hsl|].
      apply Forall_forall. intros x Hx. apply (In_nth _ _ 0) in Hx as (j & Hj & <-).
      rewrite Hsl in Hj. exact (proj2 (Hsrc j Hj)).
Qed.

(* the evaluation of a branch condition of the tail over Z, from the atoms n0 (12), in.p (35) and in.n (36) *)
Ltac rd11_ueval Hu E E12 E35 E36 n0 xp xn :=
rewrite ?branch_geu_U, ?branch_ltu_U, ?branch_ne_U, ?branch_eq_U in Hu;
rewrite ?negb_true_iff, ?negb_false_iff in Hu;
rewrite ?Z.ltb_lt, ?Z.ltb_ge, ?Z.eqb_eq, ?Z.eqb_neq in Hu;
rewrite ?U_SAlu, ?U_SMd in Hu;
rewrite ?(U_atom E 12 n0 E12 ltac:(lia)), ?(U_atom E 35 xp E35 ltac:(lia)), ?(U_atom E 36 xn E36 ltac:(lia)) in Hu;
rewrite ?U_lit in Hu by lia;
cbn [zalu_raw zmd_raw] in Hu; unfold zcanon, M64 in Hu;
rewrite ?Z.mod_small in Hu by lia.
(* the run of the tail to the memcpy entry 0x51ae8; at an undecided UBSan check, the side that reaches the
   trap is refuted from its condition *)
Ltac rd11_to_call B2 B33 EFA E E12 E35 E36 n0 xp xn :=
cw_run ltac:(rdj_awr B2 B33 EFA); cw_keep ltac:(rdj_kwr B2 B33);
lazymatch goal with HS : st_ok _ _ ?ss _ |- _ =>
  let pc := eval vm_compute in (ss_pc ss) in
  lazymatch pc with
  | 334568 => idtac
  | _ => let Hu := fresh "Hu" in cw_branch Hu;
         first [ exfalso; rd11_ueval Hu E E12 E35 E36 n0 xp xn; lia
               | rd11_to_call B2 B33 EFA E E12 E35 E36 n0 xp xn ]
  end
end.

Lemma rd11_tail : forall g pos sp1 ops W2 c2, rd11_mid g pos sp1 ops W2 c2 ->
SRr tfibsegs W2 c2 (inv_run B MT K XM_LIB g pos sp1 ops).
Proof.
intros g pos sp1 ops W2 c2 H.
destruct H as (ly2 & S2 & regs2 & mem2 & md2 & kj & -> & HJ & Hfr & Hkj & HMO & HC & HP).
destruct HP as (Hops & c & pv & dv & od & a & b & n0 & Hcur & Hc1 & Hpd & Hkat & Ha & Hb & R12 & Hn0).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & Hblk).
unfold BM_HI in Hchi, Hpn.
assert (FFS : LLVMF_STK = 32768) by reflexivity.
assert (Hfb : FA g pos + 512 <= 2 ^ 47) by (change (fs_frame_bytes 3) with 512 in Hfceil; lia).
assert (Hfs : FA g pos + 376 <= sp1) by (change (fs_frame_bytes 3) with 512 in Hfceil; lia).
pose proof HC as (_ & _ & R2 & R9 & R8 & R3 & R4 & _).
(* the state at 0x81580: k writable at k.n only (codec_bmain_rdlib.v rd_ss with the window [64, 72)), and n0 in
   [0, 24] as an atom fact, from which the engine decides the check at 0x815a8 *)
assert (HAF : atoms_ok (bm_env g pos c regs2 []) [(12%nat, mkAF 0 24 0)]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite (bm_ew_reg g pos c regs2 [] 12 12%bv eq_refl), R12. unfold w64. rewrite unsigned_lit_small by lia.
  rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia. }
destruct (rd_start B MT K XM_LIB TL LAWS g pos sp1 ly2 S2 W2 regs2 mem2 md2 kj c [] [(12%nat, mkAF 0 24 0)] PC_RD11M
  64 72 [] HJ Hfr HC Hcur ltac:(lia) ltac:(lia) ltac:(lia) (Forall_nil _) eq_refl HAF) as [HS SHOK].
remember (bm_env g pos c regs2 []) as E eqn:HEE.
assert (E2 : ew E 2 = w64 sp1) by (subst E; rewrite (bm_ew_reg g pos c regs2 [] 2 2%bv eq_refl); exact R2).
assert (B2 : bv_unsigned (ew E 2) = sp1) by (rewrite E2; unfold w64; apply unsigned_lit_small; lia).
assert (E33 : ew E 33 = Z_to_bv 64 (FA g pos)) by (subst E; apply bm_ew_F).
assert (B33 : bv_unsigned (ew E 33) = FA g pos) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply bm_ew_SB).
assert (E35 : ew E 35 = Z_to_bv 64 (e_p g + c)) by (subst E; apply bm_ew_CP).
assert (E36 : ew E 36 = Z_to_bv 64 (e_n g - c)) by (subst E; apply bm_ew_CN).
assert (E12 : ew E 12 = Z_to_bv 64 n0) by (subst E; rewrite (bm_ew_reg g pos c regs2 [] 12 12%bv eq_refl), R12; reflexivity).
assert (E3 : ew E 3 = w64 (as_gp B)) by (subst E; rewrite (bm_ew_reg g pos c regs2 [] 3 3%bv eq_refl); exact R3).
assert (E4 : ew E 4 = w64 (as_tp B)) by (subst E; rewrite (bm_ew_reg g pos c regs2 [] 4 4%bv eq_refl); exact R4).
assert (HAE : env_agree 35 (bm_env g pos c regs2 []) E) by (subst E; apply env_agree_refl).
clear HEE.
assert (KE : forall x, 0 <= x < 2 ^ 64 -> ~ rd_zone g pos sp1 64 72 x ->
  aview tfibsegs (w_H W2) mem2 x = aview tfibsegs (w_H W2) mem2 x) by (intros; reflexivity).
cw_keep_j0 HJ HJ0.
unfold cfg_at. change (w64 PC_RD11M) with (Z_to_bv 64 PC_RD11M).
pose proof Hcur as (Hc & C184 & C192).
(* 0x81580 ld a0,192(s1); 0x81584 bltu a2,a0: n0 < in.n keeps n = n0, else n = in.n *)
cw_run ltac:(rdj_awr B2 B33 EFA). cw_keep ltac:(rdj_kwr B2 B33).
cw_branch Hb1.
all: rewrite branch_ltu_U, (U_atom E 12 n0 E12 ltac:(lia)), (U_atom E 36 (e_n g - c) E36 ltac:(lia)) in Hb1.
- apply Z.ltb_lt in Hb1.
  (* 0x8158c-0x815c4: the UBSan checks, the cursor moves by n0, k.n = n0, a0 = k.bytes, jal *)
  rd11_to_call B2 B33 EFA E E12 E35 E36 n0 (e_p g + c) (e_n g - c).
  rreg HS (10%bv : bv 5) Ga0. rreg HS (11%bv : bv 5) Ga1. rreg HS (12%bv : bv 5) Ga2.
  rreg HS (2%bv : bv 5) Ga2s. rreg HS (3%bv : bv 5) Ga3. rreg HS (4%bv : bv 5) Ga4.
  rewrite B33 in Ga0. rewrite E35 in Ga1. rewrite E12 in Ga2. rewrite E2 in Ga2s. rewrite E3 in Ga3. rewrite E4 in Ga4.
  pose proof (st_ok_region_nth E _ _ 0%nat _ HS eq_refl) as Rk.
  pose proof (st_ok_region_nth E _ _ 3%nat _ HS eq_refl) as Rc.
  cbn [ms_mem restrict] in Rk, Rc.
  pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ 256 8 (SOff 12 0) Rk B33 ltac:(cbn; tauto) ltac:(lia)) as VN.
  pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ 184 8 (SAlu ALU_ADD (SOff 12 0) (SOff 35 0)) Rc B2
    ltac:(cbn; tauto) ltac:(lia)) as V184.
  pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ 192 8 (SAlu ALU_ADD (SMd M_MUL (SOff 12 0) (SLit (-1))) (SOff 36 0))
    Rc B2 ltac:(cbn; tauto) ltac:(lia)) as V192.
  assert (U12 : bv_unsigned (sv_denot E (SOff 12 0)) = n0) by exact (U_atom E 12 n0 E12 ltac:(lia)).
  assert (U184 : bv_unsigned (sv_denot E (SAlu ALU_ADD (SOff 12 0) (SOff 35 0))) = e_p g + c + n0)
    by (replace (e_p g + c + n0) with (n0 + (e_p g + c)) by lia;
        exact (rd11_U_add E 12 35 n0 (e_p g + c) E12 E35 ltac:(lia) ltac:(lia) ltac:(lia))).
  assert (U192 : bv_unsigned (sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff 12 0) (SLit (-1))) (SOff 36 0))) = e_n g - c - n0)
    by exact (rd11_U_sub E 12 36 n0 (e_n g - c) E12 E36 ltac:(lia) ltac:(lia)).
  rewrite U12 in VN. rewrite U184 in V184. rewrite U192 in V192.
  change (N.to_nat 8) with 8%nat in VN, V184, V192. change (8 * Z.of_N 8) with 64 in VN, V184, V192.
  rewrite Z.mod_small in VN, V184, V192 by lia.
  eapply (rd11_call g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c pv dv od a b n0 E _ _ _ HJ0 Hfr Hkj HMO HC Hops
    Hc1 ltac:(lia) Hpd Hkat Ha Hb ltac:(lia) HS eq_refl eq_refl ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HAE HJ
    Ga0 Ga1 Ga2 Ga2s Ga3 Ga4 KE V184 V192 VN).
- apply Z.ltb_ge in Hb1.
  (* 0x81588 mv a2,a0; 0x8158c-0x815c4 as above, with n = in.n *)
  rd11_to_call B2 B33 EFA E E12 E35 E36 n0 (e_p g + c) (e_n g - c).
  rreg HS (10%bv : bv 5) Ga0. rreg HS (11%bv : bv 5) Ga1. rreg HS (12%bv : bv 5) Ga2.
  rreg HS (2%bv : bv 5) Ga2s. rreg HS (3%bv : bv 5) Ga3. rreg HS (4%bv : bv 5) Ga4.
  rewrite B33 in Ga0. rewrite E35 in Ga1. rewrite E36 in Ga2. rewrite E2 in Ga2s. rewrite E3 in Ga3. rewrite E4 in Ga4.
  pose proof (st_ok_region_nth E _ _ 0%nat _ HS eq_refl) as Rk.
  pose proof (st_ok_region_nth E _ _ 3%nat _ HS eq_refl) as Rc.
  cbn [ms_mem restrict] in Rk, Rc.
  pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ 256 8 (SOff 36 0) Rk B33 ltac:(cbn; tauto) ltac:(lia)) as VN.
  pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ 184 8 (SAlu ALU_ADD (SOff 35 0) (SOff 36 0)) Rc B2
    ltac:(cbn; tauto) ltac:(lia)) as V184.
  pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ 192 8 (SLit 0) Rc B2 ltac:(cbn; tauto) ltac:(lia)) as V192.
  assert (U36 : bv_unsigned (sv_denot E (SOff 36 0)) = e_n g - c) by exact (U_atom E 36 (e_n g - c) E36 ltac:(lia)).
  assert (U184 : bv_unsigned (sv_denot E (SAlu ALU_ADD (SOff 35 0) (SOff 36 0))) = e_p g + c + (e_n g - c))
    by exact (rd11_U_add E 35 36 (e_p g + c) (e_n g - c) E35 E36 ltac:(lia) ltac:(lia) ltac:(lia)).
  assert (U0 : bv_unsigned (sv_denot E (SLit 0)) = e_n g - c - (e_n g - c))
    by (replace (e_n g - c - (e_n g - c)) with 0 by lia; exact (U_lit E 0 ltac:(lia))).
  rewrite U36 in VN. rewrite U184 in V184. rewrite U0 in V192.
  change (N.to_nat 8) with 8%nat in VN, V184, V192. change (8 * Z.of_N 8) with 64 in VN, V184, V192.
  rewrite Z.mod_small in VN, V184, V192 by lia.
  eapply (rd11_call g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c pv dv od a b (e_n g - c) E _ _ _ HJ0 Hfr Hkj HMO HC Hops
    Hc1 ltac:(lia) Hpd Hkat Ha Hb ltac:(lia) HS eq_refl eq_refl ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HAE HJ
    Ga0 Ga1 Ga2 Ga2s Ga3 Ga4 KE V184 V192 VN).
Qed.

(* The meeting point 0x81580 from the head's last executor state: its journal, the zone it wrote (k.a and k.b),
   the cursor's two chunks (j bytes taken), a, b and a2 = n0; then the tail. *)
Lemma rd11_mid_end : forall g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od Ef ss ms md3 j a b n0,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 k ->
frames S2 = [(3, pos)] -> 0 <= k <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 -> ops_at ops regs2 ->
k_at g pos (k_rdZ 11 pv dv) W2 mem2 -> pd_okB pv dv od -> 1 <= c ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2
  (ms_mem ms) md3 k ->
env_agree 40 (bm_env g pos c regs2 ys) Ef ->
st_ok tfibsegs Ef ss (restrict (w_H W2) ms) -> ss_pc ss = PC_RD11M -> ss_resv ss = None ->
bm_keep_ok (ss_regs ss) = true -> sr_get (ss_regs ss) 20%bv = SOff 20 0 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ rd_zone g pos sp1 24 32 x ->
   aview tfibsegs (w_H W2) (ms_mem ms) x = aview tfibsegs (w_H W2) mem2 x) ->
YP09.chunk_ok tfibsegs Ef (mrestrict (w_H W2) (ms_mem ms)) sp1 (YP09.mkChunk 184 (CVal 8 (SOff 35 j))) ->
YP09.chunk_ok tfibsegs Ef (mrestrict (w_H W2) (ms_mem ms)) sp1 (YP09.mkChunk 192 (CVal 8 (SOff 36 (- j)))) ->
0 <= j -> c + j <= e_n g ->
getr (ms_regs ms) 12 = w64 n0 -> 0 <= n0 <= 24 -> 0 <= a < 256 -> 0 <= b < 256 ->
val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms)) (FA g pos + 216) 4 a ->
val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms)) (FA g pos + 220) 4 b ->
SRr tfibsegs W2 {| cfg_ms := ms; cfg_model := md3 |} (inv_run B MT K XM_LIB g pos sp1 ops).
Proof.
intros g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od Ef ss ms md3 j a b n0
  HJ Hfr Hk Hmo HC Hops Hkat Hpd Hc1 HJ3 HAG HS Hpc Hresv Hkeep H20 KE Ca Cb Hj Hcj G12 Hn0 Ha Hb Va Vb.
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hng & Hp & Hpn & _).
unfold BM_HI in Hpn.
destruct (rd_zone_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (Happ & Hf4096 & Hfc & Hsp0 & Hsp & Hsp47 & Hclo).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W2) Ef ss ms HS Hresv) as Ems.
rewrite Hpc in Ems.
pose proof HS as HS'. rewrite Ems in HS'.
pose proof Hkat as Hkat0.
destruct HAG as (HA & HD).
assert (E35 : ew Ef 35 = Z_to_bv 64 (e_p g + c)) by (rewrite (HA 35%nat ltac:(lia)); exact (bm_ew_CP g pos c regs2 ys)).
assert (E36 : ew Ef 36 = Z_to_bv 64 (e_n g - c)) by (rewrite (HA 36%nat ltac:(lia)); exact (bm_ew_CN g pos c regs2 ys)).
assert (HC3 : mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 (ms_regs ms) (ms_mem ms) md3).
{ apply (bm_exit B MT K XM_LIB LAWS g pos sp1 0 0 c ys ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) md3
    k (Z_to_bv 64 PC_RD11M) ss Ef HC HJ3 ltac:(split; [intros i Hi; apply HA; lia | exact HD]) HS' Hkeep).
  - intros x Hx. apply KE.
    + unfold bm_keepzone in Hx. lia.
    + exact (rd_keep_apart g pos sp1 24 32 x Hf4096 Hfc Hsp0 Hsp ltac:(lia) ltac:(lia) Hx).
  - intros i Hi. pose proof HC as HSH. do 47 (destruct HSH as (_ & HSH)). destruct HSH as (HSH' & _).
    rewrite <- (HSH' i Hi). apply KE.
    + unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_mod (FA g pos) 8 ltac:(lia)) as D.
      pose proof (Z.mod_pos_bound (FA g pos) 8 ltac:(lia)) as M. lia.
    + exact (rd_shadow_apart g pos sp1 24 32 i Happ Hf4096 Hfc Hsp0 Hsp Hclo ltac:(lia) ltac:(lia) Hi).
  - pose proof HC as HPerm. do 49 (destruct HPerm as (_ & HPerm)). exact HPerm. }
rewrite Ems.
change {| cfg_ms := mkst (ms_regs ms) (Z_to_bv 64 PC_RD11M) (ms_mem ms) (seg_rom tfibsegs); cfg_model := md3 |}
  with (cfg_at tfibsegs PC_RD11M (ms_regs ms) (ms_mem ms) md3).
apply rd11_tail.
apply (bm_mcut B MT K XM_LIB g pos sp1 0 PC_RD11M _ ly2 S2 W2 (ms_regs ms) (ms_mem ms) md3 k HJ3 Hfr Hk Hmo HC3).
cbv beta. split.
- destruct Hops as (Hops' & R20). split; [exact Hops'|].
  rewrite (st_ok_restrict_reg tfibsegs (w_H W2) Ef ss ms 20%bv HS), H20. cbn [sv_denot].
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (HA 20%nat ltac:(lia)).
  rewrite (bm_ew_reg g pos c regs2 ys 20 20%bv eq_refl). exact R20.
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
    - replace (FA g pos + 192 + 24) with (FA g pos + 216) by lia. exact Va.
    - replace (FA g pos + 192 + 28) with (FA g pos + 220) by lia. exact Vb.
    - apply (rd_kept4 g pos sp1 W2 mem2 (ms_mem ms) 11 pv dv 24 32 32 Hkat0 KE ltac:(lia) ltac:(lia) ltac:(lia)
        ltac:(lia) ltac:(lia)).
    - apply (rd_kept4 g pos sp1 W2 mem2 (ms_mem ms) 11 pv dv 24 32 36 Hkat0 KE ltac:(lia) ltac:(lia) ltac:(lia)
        ltac:(lia) ltac:(lia)).
    - destruct Hkat0 as ((_ & _ & _ & _ & _ & _ & _ & Vy & _) & _). cbn [kz_bytes k_rdZ] in Vy.
      apply (rd_garr8_kept (w_H W2) (w_H W2) mem2 (ms_mem ms)); [|exact Vy].
      intros x Hx. rewrite repeat_length in Hx. cbn [Z.of_nat] in Hx. apply KE; [lia|]. unfold rd_zone. lia. }
  split; [exact Ha|]. split; [exact Hb|]. split; [exact G12 | exact Hn0].
Qed.
End b.
End a.

(* a stored byte's range, by the engine's range of the stored value *)
Ltac rd11_rng :=
lazymatch goal with
| HS : YP0l.st_ok _ ?Ef ?ssf _ |- 0 <= bv_unsigned (sv_denot _ ?v) mod 2 ^ 32 < 256 =>
  let r := eval vm_compute in (sv_urange (ss_facts ssf) v) in
  lazymatch r with Some (?lo, ?hi) =>
    let H := fresh "Hr" in
    pose proof (sv_urange_sound Ef (ss_facts ssf) v lo hi (st_ok_facts_ok tfibsegs Ef ssf _ HS)
      ltac:(vm_compute; reflexivity)) as H;
    unfold U in H; rewrite Z.mod_small by lia; lia end
end.
(* the meeting point from the state of the head's last run: a = k.a, b = k.b and n0 = a2 as the state holds them
   (n0 is 0, or the third byte mod 25: rd11_U_n0 on its atom BM_X0 + 2) *)
Ltac rd11_mfin TL LAWS AMEMCPY HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc1 HAE B2 B33 EY2 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od :=
lazymatch goal with
| HS : YP0l.st_ok _ ?Ef ?ssf (restrict (w_H ?Wf) ?msf), HJm : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  KE : forall a, _ -> ~ rd_zone _ _ _ _ _ a -> _ |- _ =>
  let Ca := fresh "Ca" in let Cb := fresh "Cb" in let Cx := fresh "Cx" in let Cy := fresh "Cy" in
  rd_chunk HS 2%nat 184 Ca; rd_chunk HS 2%nat 192 Cb;
  rewrite ?ew_ewset_other in Ca, Cb by lia; rewrite B2 in Ca, Cb;
  rd_chunk HS 33%nat 216 Cx; rd_chunk HS 33%nat 220 Cy;
  rewrite ?ew_ewset_other in Cx, Cy by lia; rewrite B33 in Cx, Cy;
  lazymatch type of Ca with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 184 (CVal 8 (SOff 35 ?j))) =>
  lazymatch type of Cx with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 216 (CVal 4 ?va)) =>
  lazymatch type of Cy with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 220 (CVal 4 ?vb)) =>
  let e12 := eval vm_compute in (sr_get (ss_regs ssf) (12%bv : bv 5)) in
  let Va := fresh "Va" in let Vb := fresh "Vb" in let Ha := fresh "Ha" in let Hb := fresh "Hb" in
  let G12 := fresh "G12" in let Hn0 := fresh "Hn0" in let AG := fresh "AG" in
  pose proof (rd_chunk_u32 _ _ _ _ _ Cx) as Va; pose proof (rd_chunk_u32 _ _ _ _ _ Cy) as Vb;
  assert (Ha : 0 <= bv_unsigned (sv_denot Ef va) mod 2 ^ 32 < 256) by rd11_rng;
  assert (Hb : 0 <= bv_unsigned (sv_denot Ef vb) mod 2 ^ 32 < 256) by rd11_rng;
  assert (G12 : getr (ms_regs msf) (12%bv : bv 5) = Z_to_bv 64 (U Ef e12)) by
    (refine (eq_trans (st_ok_restrict_reg tfibsegs (w_H Wf) Ef ssf msf (12%bv : bv 5) HS) _);
     change (sr_get (ss_regs ssf) 12%bv) with e12; apply denot_lit_U);
  assert (AG : env_agree 40 (bm_env g pos c regs2 ys) Ef) by env_agree_chain HAE;
  assert (Hn0 : 0 <= U Ef e12 <= 24) by
    (first
     [ let r := eval vm_compute in (sv_urange (ss_facts ssf) e12) in
       lazymatch r with Some (?lo, ?hi) =>
         let H := fresh "Hr" in
         pose proof (sv_urange_sound Ef (ss_facts ssf) e12 lo hi (st_ok_facts_ok tfibsegs Ef ssf _ HS)
           ltac:(vm_compute; reflexivity)) as H; lia end
     | pose proof (rd_ib_range g (c + 2)) as Hr2;
       rewrite (rd11_U_n0 Ef 39 (rd_ib g (c + 2)) ltac:(rewrite (rd_ag 40 _ Ef 39%nat AG ltac:(lia)); exact EY2) Hr2);
       pose proof (Z.mod_pos_bound (rd_ib g (c + 2)) 25 ltac:(lia)); lia ]);
  rewrite ?wvb_collapse in HJm;
  exact (rd11_mid_end _ _ _ _ TL LAWS AMEMCPY g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od Ef ssf msf _ j
    (bv_unsigned (sv_denot Ef va) mod 2 ^ 32) (bv_unsigned (sv_denot Ef vb) mod 2 ^ 32) (U Ef e12)
    HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc1 HJm AG HS
    ltac:(reflexivity) ltac:(reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    KE Ca Cb ltac:(lia) ltac:(lia) G12 Hn0 Ha Hb Va Vb)
  end end end
end.
(* every path of the head from the cut to the meeting point 0x81580 (codec_bmain_rdb_lib.v rdb_explore with
   that stop) *)
Ltac rd11_explore LAWS HJ0 HFR HC c E35 E32 E36 B2 B33 EFA EYall HSEP fin :=
cwj_run_to ltac:(rdj_awr B2 B33 EFA) 529792; try (rd_obl LAWS HJ0 HFR HC c E35 E32);
cw_keep ltac:(rdj_kwr B2 B33);
lazymatch goal with
| HS : st_ok _ _ ?ss _ |- _ =>
  let pc := eval vm_compute in (ss_pc ss) in
  lazymatch pc with
  | 529792 => fin
  | _ =>
    let Hb := fresh "Hb" in
    cw_branch Hb; rdb_brn Hb E36;
    lazymatch type of Hb with
    | _ = 0 => rd11_explore LAWS HJ0 HFR HC c E35 E32 E36 B2 B33 EFA EYall HSEP fin
    | 0 < _ =>
      lazymatch goal with HS' : st_ok _ _ ?ss' _ |- _ =>
        let jz := eval vm_compute in (rd_cur_off (ss_mem ss')) in
        lazymatch jz with Some ?jj =>
          let j := eval vm_compute in (Z.to_nat jj) in
          rd_in_add LAWS HJ0 HFR HC c j E35 EYall HSEP;
          rd11_explore LAWS HJ0 HFR HC c E35 E32 E36 B2 B33 EFA EYall HSEP fin
        end
      end
    end
  end
end.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis AMEMCPY : aintrin_realizes tfibsegs B OCpy BM_asan_memcpy.

Theorem seg_rd11_holds : seg_rd_run B MT K XM_LIB 11.
Proof.
intros g pos sp1 ops W2 c2 Hrd.
destruct Hrd as (ly2 & S2 & regs2 & mem2 & md2 & k & -> & HJ & Hfr & Hk & Hmo & HC & HP).
destruct HP as (Hops & Hkind & c & pv & dv & od & Hcur & Hc1 & Hpd & R22 & Hkat).
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & Hblk).
unfold BM_HI in Hchi, Hpn.
pose proof Hcur as (Hc & C184 & C192).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
assert (Hfb : FA g pos + 512 <= 2 ^ 47) by (change (fs_frame_bytes 3) with 512 in Hfceil; lia).
assert (Hfs : FA g pos + 376 <= sp1) by (change (fs_frame_bytes 3) with 512 in Hfceil; lia).
set (ys := rd_ys g c 3).
destruct (rd_start B MT K XM_LIB TL LAWS g pos sp1 ly2 S2 W2 regs2 mem2 md2 k c ys (rd_AF 3) (rd_pc 11) 24 32
  [] HJ Hfr HC Hcur ltac:(lia) ltac:(lia) ltac:(lia) (Forall_nil _) eq_refl (rd_AF_ok g pos c regs2 3)) as [HS SHOK].
set (E := bm_env g pos c regs2 ys) in HS, SHOK.
assert (HAE : env_agree 40 E E) by apply env_agree_refl.
pose proof HC as (_ & _ & R2 & _).
assert (B2 : bv_unsigned (ew E 2) = sp1).
{ unfold E. rewrite (bm_ew_reg g pos c regs2 ys 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
assert (B33 : bv_unsigned (ew E 33) = FA g pos) by (unfold E; rewrite (bm_ew_F g pos c regs2 ys); apply unsigned_lit_small; lia).
assert (E35 : ew E 35 = Z_to_bv 64 (e_p g + c)) by (unfold E; exact (bm_ew_CP g pos c regs2 ys)).
assert (E36 : ew E 36 = Z_to_bv 64 (e_n g - c)) by (unfold E; exact (bm_ew_CN g pos c regs2 ys)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (unfold E; exact (bm_ew_SB g pos c regs2 ys)).
assert (EYall : forall j, (j < 3)%nat -> ew E (BM_X0 + j) = Z_to_bv 64 (rd_ib g (c + Z.of_nat j)))
  by (intros j Hj; exact (rd_EY g pos c regs2 3 j Hj)).
assert (EY2 : ew (bm_env g pos c regs2 ys) 39 = Z_to_bv 64 (rd_ib g (c + 2)))
  by exact (rd_EY g pos c regs2 3 2 ltac:(lia)).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ rd_zone g pos sp1 24 32 a ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
pose proof (rd_in_sep B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as HSEP.
cw_keep_j0 HJ HJ0.
unfold cfg_at. change (w64 (rd_pc 11)) with (Z_to_bv 64 0x80e48). change (rd_pc 11) with 0x80e48 in HS.
rd11_explore LAWS HJ0 Hfr HC c E35 E32 E36 B2 B33 EFA EYall HSEP
  ltac:(idtac; rd11_mfin TL LAWS AMEMCPY HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc1 HAE B2 B33 EY2 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys pv dv od).
Qed.
End c.
