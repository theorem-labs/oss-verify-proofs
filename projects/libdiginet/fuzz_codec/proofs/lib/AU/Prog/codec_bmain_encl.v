(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 571 of its 593 lines of code are new or changed and 122 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/U/Prog/codec_main_owe0.v; 247 of its 266 lines of code are new or changed and 574 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_owe1.v, with its module paths and module names changed; 398 of its 436 lines of code are new or changed and 228 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/AU/Prog/codec_bmain_rdlib.v, with its module names and numbers changed; 383 of its 456 lines of code are new or changed and 363 lines of the source are left out. *)
(* The pieces the encoder segments ENC0 .. ENC11 of the image-B walk of LLVMFuzzerTestOneInput share
   (lib/AU/Prog/codec_bmain_inv.v, 0x8271c-0x82834), and any segment of that walk that calls one of codec's own
   functions through its image-B contract. It is the image-A layer (lib/A/Prog/codec_amain_encl.v) at image B:
   the record k at F + 192 (s7), k.out at F + 300 (the spill 144(sp1)), k.bytes at F + 232 (the spill 120(sp1)),
   the cursor at 184(sp1), the loop counter in s4, image B's frame, entries and contracts. The step across a
   call is codec_bmain_headl.v's bm_call_kept_x (the image-A walk's am_call_kept at image B).
   - kz_set_out / kcall_at_out / k_at_kept: the call record with out replaced by the 32 bytes the encoder wrote;
   - bm_jb / bm_jump: a `j tgt` (jal x0) at pc moves a cut from pc to tgt (lib/Reusable/YK11.v step_jal_x0);
   - bmenc_finish: from the encoder call's entry state and the encoder's post (written over k.out = F + 300, the
     result cenc_res of enc_kZ) to JOIN 0x82834 (inv_join), through the `j 0x82834` after the call for ENC0 ..
     ENC10 (ENC11 returns to 0x82834 itself);
   - enc_start / enc_callst / enc_entry / enc_out / enc_pers: the executor state at an ENC cut, the cut facts at
     the encoder's entry, and the contract premises every encoder call shares.
   UBSan: none of the function's trap edges (codec_bmain_inv.v section traps) lies in 0x8271c-0x82834
   (bmenc_no_trap), so the encoder segments have no trap edge to refute. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC CPgEncC.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgEncU CodecRo CodecGlobs.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkU CPgWalkCallU CPgSatU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_inv codec_bmain_st codec_bmain_lem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_headl codec_bmain_rdlib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ================================ no trap edge in the encoder block ================================ *)
Lemma bmenc_no_trap :
  forallb (fun a => negb ((0x8271c <=? a) && (a <? 0x82834))) (bm_trap_taken ++ bm_trap_fall) = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================ the record after an encoder ================================ *)
Definition kz_set_out (k : kcallZ) (o : list Z) : kcallZ :=
mkKcallZ (kz_kind k) (kz_p k) (kz_desk k) (kz_a k) (kz_b k) (kz_c k) (kz_delta k) (kz_bytes k) (kz_n k) (kz_rc k)
(kz_before k) o (kz_want_rc k) (kz_want k) (kz_want_len k) (kz_want_key k) (kz_want_display k).

Section z. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma kcall_at_out : forall (W W' : world tfibsegs) mem mem' q k o,
kcall_atA tfibsegs W mem q k -> kcall_wfZ k ->
(forall x, q <= x < q + 184 -> ~ (q + 108 <= x < q + 140) ->
 aview tfibsegs (w_H W') mem' x = aview tfibsegs (w_H W) mem x) ->
garr8 tfibsegs (mrestrict (w_H W') mem') (q + 108) o ->
kcall_atA tfibsegs W' mem' q (kz_set_out k o).
Proof.
intros W W' mem mem' q k o
  (V0 & V8 & V16 & V24 & V28 & V32 & V36 & G40 & V64 & V72 & G76 & G108 & V140 & G144 & V168 & V176 & V180)
  (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Lb & Lbe & _ & Lw) Hk Ho.
unfold kz_set_out, kcall_atA. cbn [kz_kind kz_p kz_desk kz_a kz_b kz_c kz_delta kz_bytes kz_n kz_rc kz_before kz_out
  kz_want_rc kz_want kz_want_len kz_want_key kz_want_display].
assert (KV : forall o' n v, 0 <= o' -> o' + Z.of_nat n <= 184 -> (o' + Z.of_nat n <= 108 \/ 140 <= o') ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (q + o') n v -> val_mem tfibsegs (mrestrict (w_H W') mem') (q + o') n v).
{ intros o' n v H1 H2 H3 Hv. apply (cw_val_mem_kept (w_H W) (w_H W') mem mem'); [|exact Hv].
  intros x Hx. apply Hk; lia. }
assert (KG : forall o' l, 0 <= o' -> o' + Z.of_nat (length l) <= 184 -> (o' + Z.of_nat (length l) <= 108 \/ 140 <= o') ->
  garr8 tfibsegs (mrestrict (w_H W) mem) (q + o') l -> garr8 tfibsegs (mrestrict (w_H W') mem') (q + o') l).
{ intros o' l H1 H2 H3 Hg. apply (bm_garr8_kept_x (w_H W) (w_H W') mem mem'); [|exact Hg].
  intros x Hx. apply Hk; lia. }
split; [rewrite <- (Z.add_0_r q); apply KV; [lia | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact V0]|].
split; [apply KV; [lia | cbn; lia | cbn; lia | exact V8]|].
split; [apply KV; [lia | cbn; lia | cbn; lia | exact V16]|].
split; [apply KV; [lia | cbn; lia | cbn; lia | exact V24]|].
split; [apply KV; [lia | cbn; lia | cbn; lia | exact V28]|].
split; [apply KV; [lia | cbn; lia | cbn; lia | exact V32]|].
split; [apply KV; [lia | cbn; lia | cbn; lia | exact V36]|].
split; [apply KG; [lia | rewrite Lb; cbn; lia | rewrite Lb; cbn; lia | exact G40]|].
split; [apply KV; [lia | cbn; lia | cbn; lia | exact V64]|].
split; [apply KV; [lia | cbn; lia | cbn; lia | exact V72]|].
split; [apply KG; [lia | rewrite Lbe; cbn; lia | rewrite Lbe; cbn; lia | exact G76]|].
split; [exact Ho|].
split; [apply KV; [lia | cbn; lia | cbn; lia | exact V140]|].
split; [apply KG; [lia | rewrite Lw; cbn; lia | rewrite Lw; cbn; lia | exact G144]|].
split; [apply KV; [lia | cbn; lia | cbn; lia | exact V168]|].
split; [apply KV; [lia | cbn; lia | cbn; lia | exact V176]|].
apply KV; [lia | cbn; lia | cbn; lia | exact V180].
Qed.
End z.
(* the record kept whole *)
Lemma kz_set_out_id : forall k, kz_set_out k (kz_out k) = k.
Proof. intros []. reflexivity. Qed.

(* ================================ a `j tgt` at pc ================================ *)
Definition bm_jb (pc tgt : Z) : bool :=
match clookup tfibtbl_lib pc with
| Some w =>
    negb (is_ecall (Z_to_bv 32 w)) &&
    match decode_any (Z_to_bv 32 w) with
    | Some (Jal rd imm, sz) =>
        bv_eqb rd 0%bv && (sz =? 4) && (bv_unsigned (btgt (Z_to_bv 64 pc) (bv_signed imm)) =? tgt)
    | _ => false
    end
| None => false
end.

Lemma bm_jb_sound : forall pc tgt, bm_jb pc tgt = true -> 0 <= tgt < 2 ^ 64 ->
exists w imm, fetch_word tfibsegs (Z_to_bv 64 pc) = Some w /\ is_ecall w = false /\
decode_any w = Some (Jal 0 imm, 4) /\ btgt (Z_to_bv 64 pc) (bv_signed imm) = Z_to_bv 64 tgt.
Proof.
intros pc tgt H Ht. unfold bm_jb in H.
destruct (clookup tfibtbl_lib pc) as [w|] eqn:Hl; [|discriminate].
apply andb_true_iff in H as [He H]. apply negb_true_iff in He.
destruct (decode_any (Z_to_bv 32 w)) as [[i sz]|] eqn:Hd; [|discriminate].
destruct i; try discriminate.
apply andb_true_iff in H as [H Htg]. apply andb_true_iff in H as [Hr Hsz].
apply bv_eqb_eq in Hr. apply Z.eqb_eq in Hsz. apply Z.eqb_eq in Htg. subst rd sz.
exists (Z_to_bv 32 w), imm. split; [exact (tfibtbl_lib_ok _ _ Hl)|]. split; [exact He|].
split; [rewrite Hd; reflexivity|].
apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_small by lia. exact Htg.
Qed.

(* ================================ the encoder segments' executor state ================================
   ENCk's state: the reader layer's base without the .got slot and the cell (codec_bmain_rdlib.v rd_base), and
   k's scalar fields as atoms of the segment (enc_ys): p = atom 37 (8 bytes at k + 8), a / b / c = atoms 38 / 39 / 40
   (4 bytes at k + 24 / 28 / 32), delta mod 2^32 = atom 41 (k + 36), n = atom 42 (8 bytes at k + 64), in a region
   of the frame (atom 33) the segment only reads. *)
Definition enc_ys (k : kcallZ) : list Z := [kz_p k; kz_a k; kz_b k; kz_c k; kz_delta k mod 2 ^ 32; kz_n k].
Definition enc_rk : YP09.region := bm_frame_region 192 264 192 192
[YP09.mkChunk 200 (CVal 8 (SOff 37 0)); YP09.mkChunk 216 (CVal 4 (SOff 38 0)); YP09.mkChunk 220 (CVal 4 (SOff 39 0));
 YP09.mkChunk 224 (CVal 4 (SOff 40 0)); YP09.mkChunk 228 (CVal 4 (SOff 41 0)); YP09.mkChunk 256 (CVal 8 (SOff 42 0))].
Definition enc_ss (pc : Z) : sstate := mkSS pc bm_sregs (enc_rk :: rd_base) None (mkFacts bm_atoms [] []).

(* the registers the encoders' arguments arrive in, as the run leaves them: `lw` of a 4-byte field (sign-extended),
   `lbu` / `lhu` of its low byte(s) (zero-extended) *)
Lemma bm_sx32 : forall v, 0 <= v < 2 ^ 32 ->
sext 64 (bv_extract 0 32 (Z_to_bv 64 v)) = Z_to_bv 64 (DgnLib.s32 v).
Proof.
intros v Hv. rewrite sext64_lit. f_equal. unfold bv_signed.
rewrite bv_extract_unsigned, Z_to_bv_unsigned, Z.shiftr_0_r.
unfold bv_swrap, bv_wrap, DgnLib.s32.
change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 32) with (2 ^ 32). change (bv_half_modulus 32) with (2 ^ 31).
rewrite (Z.mod_small v (2 ^ 64)) by lia. rewrite (Z.mod_small v (2 ^ 32)) by lia.
destruct (Z.ltb_spec v (2 ^ 31)).
- rewrite Z.mod_small by lia. lia.
- replace (v + 2 ^ 31) with ((v - 2 ^ 31) + 1 * 2 ^ 32) by lia. rewrite Z.mod_add by lia.
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma bm_zx : forall v (w : N), 0 <= v < 2 ^ 64 ->
zext 64 (bv_extract 0 w (Z_to_bv 64 v)) = Z_to_bv 64 (v mod 2 ^ Z.of_N w).
Proof.
intros v w Hv. rewrite zext64_lit. f_equal.
rewrite bv_extract_unsigned, Z_to_bv_unsigned, Z.shiftr_0_r.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small v (2 ^ 64)) by lia. reflexivity.
Qed.
Lemma bm_s32_mod : forall d, - 2 ^ 31 <= d < 2 ^ 31 -> DgnLib.s32 (d mod 2 ^ 32) = d.
Proof.
intros d Hd. unfold DgnLib.s32.
destruct (Z.ltb_spec (d mod 2 ^ 32) (2 ^ 31)) as [Hl | Hl].
- destruct (Z_lt_le_dec d 0) as [Hn | Hn].
  + exfalso. replace d with ((d + 2 ^ 32) + (-1) * 2 ^ 32) in Hl by lia. rewrite Z.mod_add in Hl by lia.
    rewrite Z.mod_small in Hl by lia. lia.
  + apply Z.mod_small. lia.
- destruct (Z_lt_le_dec d 0) as [Hn | Hn].
  + replace d with ((d + 2 ^ 32) + (-1) * 2 ^ 32) at 1 by lia. rewrite Z.mod_add by lia.
    rewrite Z.mod_small by lia. lia.
  + rewrite Z.mod_small in Hl by lia. lia.
Qed.
Lemma bm_s32_range : forall c, 0 <= c < 2 ^ 32 -> - 2 ^ 31 <= DgnLib.s32 c < 2 ^ 31.
Proof. intros c Hc. unfold DgnLib.s32. destruct (Z.ltb_spec c (2 ^ 31)); lia. Qed.
(* the image-B premises on the pointers: k.out = F + 300 is 4-aligned, k.p is NULL or an 8-aligned personality *)
Lemma enc_out_al : forall F, F mod 64 = 0 -> (F + 300) mod 4 = 0.
Proof.
intros F H. pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite H, Z.add_0_r in D. rewrite D.
replace (64 * (F / 64) + 300) with ((16 * (F / 64) + 75) * 4) by lia. apply Z_mod_mult.
Qed.
Lemma enc_p_al : forall pv dv od, pd_okB pv dv od -> pv mod 8 = 0.
Proof. intros pv dv od [(-> & _) | [(-> & _) | (-> & _)]]; reflexivity. Qed.
(* bytes of the loaded image, by computation over the segments *)
Definition bm_img_b (q n : Z) : bool :=
existsb (fun s => (Z.of_N (seg_base s) <=? q) && (q + n <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool tfibsegs.
Lemma bm_img_of_b : forall q n, bm_img_b q n = true -> forall a, q <= a < q + n -> in_img tfibsegs a.
Proof.
intros q n Hb a Ha. unfold bm_img_b in Hb. apply existsb_exists in Hb as (s & Hin & Hc).
apply andb_prop in Hc as (Hlo & Hhi). apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
exists s. split; [exact Hin | lia].
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* the record kept whole, when its 184 bytes are *)
Lemma k_at_kept : forall g pos k (W W' : world tfibsegs) mem mem',
k_at g pos k W mem ->
(forall x, FA g pos + 192 <= x < FA g pos + 376 -> aview tfibsegs (w_H W') mem' x = aview tfibsegs (w_H W) mem x) ->
k_at g pos k W' mem'.
Proof.
intros g pos k W W' mem mem' (Hk & Hwf) KE. split; [|exact Hwf].
rewrite <- (kz_set_out_id k). apply (kcall_at_out W W' mem mem' (FA g pos + 192) k (kz_out k) Hk Hwf).
- intros x Hx _. apply KE. lia.
- pose proof Hk as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G108 & _).
  pose proof Hwf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Lo & _).
  apply (bm_garr8_kept_x (w_H W) (w_H W') mem mem'); [|exact G108].
  intros x Hx. rewrite Lo in Hx. cbn in Hx. apply KE. lia.
Qed.

(* the cursor at the end of a run whose state still holds the cursor region bm_cur_region *)
Lemma bm_cur_end : forall g pos c regs ys E ss (W : world tfibsegs) ms sp1,
env_agree 37 (bm_env g pos c regs ys) E ->
st_ok tfibsegs E ss (restrict (w_H W) ms) -> In bm_cur_region (ss_mem ss) ->
getr regs 2 = w64 sp1 -> 0 <= sp1 -> sp1 + 200 <= 2 ^ 64 ->
0 <= c <= e_n g -> 0 <= e_p g -> e_p g + e_n g < 2 ^ 64 ->
cur_at g sp1 c W (ms_mem ms).
Proof.
intros g pos c regs ys E ss W ms sp1 (HA & _) HS Hin R2 Hs0 Hs1 Hc Hp Hpn.
pose proof (st_ok_mem_ok tfibsegs E ss _ HS) as (_ & Hok & _).
rewrite Forall_forall in Hok. pose proof (Hok _ Hin) as Hr.
unfold region_ok, bm_cur_region in Hr.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in Hr.
destruct Hr as (_ & _ & _ & Hch).
assert (U2 : bv_unsigned (ew E 2) = sp1).
{ rewrite (HA 2%nat ltac:(lia)), (bm_ew_reg g pos c regs ys 2 2%bv eq_refl), R2. unfold w64.
  apply unsigned_lit_small. lia. }
rewrite U2 in Hch.
apply Forall_cons_iff in Hch as (H184 & Hch1). apply Forall_cons_iff in Hch1 as (H192 & _).
pose proof (rd_val_of_chunk E _ sp1 184 8 (SOff 35 0) H184) as V1.
pose proof (rd_val_of_chunk E _ sp1 192 8 (SOff 36 0) H192) as V2.
rewrite (bm_den_off E 35 (e_p g + c) 0) in V1;
  [| rewrite (HA 35%nat ltac:(lia)); exact (bm_ew_CP g pos c regs ys) | lia | lia].
rewrite (bm_den_off E 36 (e_n g - c) 0) in V2;
  [| rewrite (HA 36%nat ltac:(lia)); exact (bm_ew_CN g pos c regs ys) | lia | lia].
rewrite Z.add_0_r, unsigned_lit_small in V1, V2 by lia.
split; [exact Hc|]. split; [exact V1 | exact V2].
Qed.
Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws tfibsegs B.

(* A cut at a `j tgt` is the same cut at tgt; the cut's own P does not read the model. *)
Lemma bm_jump : forall g pos sp1 kv pc tgt (P : alayout -> astate -> world tfibsegs -> bvmap 5 word ->
  (word -> option byte) -> Model -> Prop) W c,
bm_jb pc tgt = true -> 0 <= tgt < 2 ^ 64 ->
(forall ly S W regs mem md md', P ly S W regs mem md -> P ly S W regs mem md') ->
mcut B MT K XM_LIB g pos sp1 kv pc P W c -> SRr tfibsegs W c (mcut B MT K XM_LIB g pos sp1 kv tgt P).
Proof.
intros g pos sp1 kv pc tgt P W c Hjb Ht HPmd (ly2 & S2 & regs2 & mem2 & md2 & k & -> & HJ & Hfr & Hk & Hmo & HC & HP).
destruct (bm_jb_sound pc tgt Hjb Ht) as (w & imm & Hf & He & Hd & Htg).
unfold cfg_at. change (w64 pc) with (Z_to_bv 64 pc).
apply (SRr_step tfibsegs Hwx_tfa W (mkst regs2 (Z_to_bv 64 pc) mem2 (seg_rom tfibsegs))
  (mkst regs2 (Z_to_bv 64 tgt) (mrestrict (w_H W) mem2) (seg_rom tfibsegs)) md2).
- reflexivity.
- rewrite restrict_mkst_fx. rewrite (step_jal_x0 tfibsegs regs2 _ _ _ w imm Hf He Hd). rewrite Htg. reflexivity.
- intros md' Hsame. apply SRr_ret. rewrite unrestrict_mkst_mrestrict.
  exists ly2, S2, regs2, mem2, md', k. split; [reflexivity|].
  split; [rewrite (same_but_materialized_wvb md2 md' Hsame); pose proof tfib_segs_low as Hsegs;
    eapply ajournal_materialize; eassumption|].
  split; [exact Hfr|]. split; [exact Hk|]. split; [exact Hmo|]. split; [exact HC|].
  exact (HPmd _ _ _ _ _ _ _ HP).
Qed.

(* ================================ the encoder call to JOIN ================================ *)
Lemma bmenc_finish : forall g pos sp1 ops c k od ly2 S2 W2 regsc mem2 md2 kev T ra W3 c3,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 kev ->
frames S2 = [(3, pos)] -> 0 <= kev <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regsc mem2 md2 ->
ops_at ops regsc -> cur_at g sp1 c W2 mem2 -> k_at g pos k W2 mem2 -> enc_okZ k od ->
getr regsc 1 = w64 ra -> (ra = PC_JOIN \/ bm_jb ra PC_JOIN = true) ->
cdc_post tfibsegs B MT LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] kev regsc T
  (cenc_wr (FA g pos + 300)) ly2 S2 W2 mem2 md2 (cenc_res tfibsegs (FA g pos + 300) fa5 (enc_kZ k od)) W3 c3 ->
SRr tfibsegs W3 c3 (inv_join B MT K XM_LIB g pos sp1 ops).
Proof.
intros g pos sp1 ops c k od ly2 S2 W2 regsc mem2 md2 kev T ra W3 c3 HJ Hfr Hk Hmo HC Hops Hcur Hkat Henc Hra Hjb Hpost.
destruct Hpost as (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HPR & Hfr3 & HPerm & _ & Hmo3 & HK & Ha0 & Hout).
unfold EV_CDC in HJ3. rewrite Z.add_0_r in HJ3.
destruct (bm_call_kept_x B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regsc mem2 md2 kev c T (cenc_wr (FA g pos + 300))
  ly3 S3 W3 regs3 mem3 md3 kev HJ Hfr HC Hcur ltac:(unfold cenc_wr; intros a Ha; lia) HJ3 HPR HPerm HK)
  as (HC3 & Hcur3 & KF).
pose proof Henc as (Hkind & Hpd & Hrdr & Hbe & Hko).
pose proof Hkat as (Hkat2 & Hwf).
set (o := cmd_outZ fa5 (snd (enc_kZ k od))).
assert (Lo : length o = 32%nat) by exact (enc_kZ_out_len k od Henc).
assert (Hkat3 : k_at g pos (kz_set_out k o) W3 mem3).
{ split.
  - apply (kcall_at_out W2 W3 mem2 mem3 (FA g pos + 192) k o Hkat2 Hwf).
    + intros x Hx Hx2. apply KF; [lia|]. unfold cenc_wr. lia.
    + replace (FA g pos + 192 + 108) with (FA g pos + 300) by lia. exact Hout.
  - destruct Hwf as (W1 & W2' & W3' & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13 & W14 & W15 & _ & W17).
    unfold kz_set_out, kcall_wfZ. cbn [kz_kind kz_p kz_desk kz_a kz_b kz_c kz_delta kz_bytes kz_n kz_rc kz_before kz_out
      kz_want_rc kz_want kz_want_len kz_want_key kz_want_display].
    exact (conj W1 (conj W2' (conj W3' (conj W4 (conj W5 (conj W6 (conj W7 (conj W8 (conj W9 (conj W10 (conj W11
      (conj W12 (conj W13 (conj W14 (conj W15 (conj Lo W17)))))))))))))))). }
assert (Hrec : rec_okZ (kz_set_out k o) od).
{ unfold rec_okZ, kz_set_out. cbn [kz_kind kz_p kz_desk kz_before kz_out].
  split; [exact Hkind|]. split; [exact Hpd|]. split; [exact Hrdr|]. split; [exact Hbe|]. reflexivity. }
assert (HPR20 : getr regs3 20 = getr regsc 20) by exact (HPR 20 ltac:(unfold acallee_saved; lia)).
pose proof HJ as (HAR & _).
assert (Hmo' : mo_le MT (e_S g) S3 0) by exact (mo_le_trans MT MTL _ _ _ 0 0 Hmo Hmo3).
assert (HM : mcut B MT K XM_LIB g pos sp1 0 ra (fun ly2 S2 W2 regs2 mem2 md2 => ops_at ops regs2 /\
  exists c k od, cur_at g sp1 c W2 mem2 /\ k_at g pos k W2 mem2 /\ rec_okZ k od /\
  getr regs2 10 = w64 (fst (enc_kZ k od))) W3 (cfg_at tfibsegs ra regs3 mem3 md3)).
{ exists ly3, S3, regs3, mem3, md3, kev. split; [reflexivity|].
  split; [exact HJ3|]. split; [rewrite Hfr3; exact Hfr|]. split; [exact Hk|]. split; [exact Hmo'|].
  split; [exact HC3|].
  split; [destruct Hops as [Ho1 Ho2]; split; [exact Ho1 | rewrite HPR20; exact Ho2]|].
  exists c, (kz_set_out k o), od. split; [exact Hcur3|]. split; [exact Hkat3|]. split; [exact Hrec|].
  exact Ha0. }
rewrite Hra. change (mkCfg (mkst regs3 (w64 ra) mem3 (seg_rom tfibsegs)) md3) with (cfg_at tfibsegs ra regs3 mem3 md3).
destruct Hjb as [-> | Hjb].
- apply SRr_ret. exact HM.
- apply (bm_jump g pos sp1 0 ra PC_JOIN _ W3 _ Hjb ltac:(unfold PC_JOIN; lia)); [|exact HM].
  intros ly S W regs mem md md' HP. exact HP.
Qed.

(* ================================ the encoder segments' start and call states ================================ *)
Hypothesis TL : TfibLib B.

(* ENCk's executor state: k's scalar fields as atoms 37 .. 42 *)
Lemma enc_start : forall g pos sp1 ly2 S2 W2 regs2 mem2 md2 kev c k pc,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 kev ->
frames S2 = [(3, pos)] ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
cur_at g sp1 c W2 mem2 -> k_at g pos k W2 mem2 ->
st_ok tfibsegs (bm_env g pos c regs2 (enc_ys k)) (enc_ss pc)
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 pc) mem2 (seg_rom tfibsegs))).
Proof.
intros g pos sp1 ly2 S2 W2 regs2 mem2 md2 kev c k pc HJ Hfr HC Hcur ((V0 & V8 & V16 & V24 & V28 & V32 & V36 & _ & V64 & _) & Hwf).
pose proof Hwf as (_ & Wp & _ & Wa & Wb & Wc & Wd & Wn & _).
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kev HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & _).
unfold BM_HI in Hchi.
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof HC as (Hpre & _ & R2 & _).
set (E := bm_env g pos c regs2 (enc_ys k)).
pose proof (bm_entry B MT K XM_LIB TL LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kev c pc (enc_ys k) [] []
  HJ Hfr HC Hcur eq_refl (Forall_nil _) I (Forall_nil _) I) as HS0.
fold E in HS0.
pose proof (st_ok_submem tfibsegs E (bm_ss pc [] []) _ rd_base HS0
  ltac:(cbn [bm_ss bm_ssb ss_mem]; unfold bm_regs, bm_regs0, cw_regs, rd_base; cbn [app]; submem_to)
  ltac:(vm_compute; reflexivity)) as HS1.
cbn [bm_ss bm_ssb ss_pc ss_regs ss_resv ss_facts] in HS1. rewrite app_nil_r in HS1.
assert (U2 : bv_unsigned (ew E 2) = sp1).
{ subst E. rewrite (bm_ew_reg g pos c regs2 _ 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
assert (U33 : bv_unsigned (ew E 33) = FA g pos).
{ subst E. rewrite (bm_ew_F g pos c regs2 _). apply unsigned_lit_small. lia. }
assert (EY : forall j, ew E (BM_X0 + j) = Z_to_bv 64 (nth j (enc_ys k) 0)) by (intros j; subst E; apply bm_ew_y).
pose proof (Z.mod_pos_bound (kz_delta k) (2 ^ 32) ltac:(lia)) as Md.
assert (DY : forall j v, nth j (enc_ys k) 0 = v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff (BM_X0 + j) 0) = Z_to_bv 64 v).
{ intros j v Hj Hv. rewrite (bm_den_off E (BM_X0 + j) v 0); [f_equal; lia | rewrite EY, Hj; reflexivity | lia | lia]. }
assert (Hrk : region_ok tfibsegs E (mrestrict (w_H W2) mem2) enc_rk).
{ apply (bm_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kev c (enc_ys k) 192 264 192 192
    _ HJ Hfr HC ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 200 8 (SOff 37 0) (kz_p k)); [exact (DY 0%nat (kz_p k) eq_refl ltac:(lia)) | cbn; lia | cbn; lia |].
    replace (FA g pos + 200) with (FA g pos + 192 + 8) by lia. exact V8.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 216 4 (SOff 38 0) (kz_a k)); [exact (DY 1%nat (kz_a k) eq_refl ltac:(lia)) | cbn; lia | cbn; lia |].
    replace (FA g pos + 216) with (FA g pos + 192 + 24) by lia. exact V24.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 220 4 (SOff 39 0) (kz_b k)); [exact (DY 2%nat (kz_b k) eq_refl ltac:(lia)) | cbn; lia | cbn; lia |].
    replace (FA g pos + 220) with (FA g pos + 192 + 28) by lia. exact V28.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 224 4 (SOff 40 0) (kz_c k)); [exact (DY 3%nat (kz_c k) eq_refl ltac:(lia)) | cbn; lia | cbn; lia |].
    replace (FA g pos + 224) with (FA g pos + 192 + 32) by lia. exact V32.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 228 4 (SOff 41 0) (kz_delta k mod 2 ^ 32));
      [exact (DY 4%nat (kz_delta k mod 2 ^ 32) eq_refl ltac:(lia)) | cbn; lia | cbn; lia |].
    replace (FA g pos + 228) with (FA g pos + 192 + 36) by lia. exact (cw_val_mem_mod _ _ 4 _ V36).
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 256 8 (SOff 42 0) (kz_n k)); [exact (DY 5%nat (kz_n k) eq_refl ltac:(lia)) | cbn; lia | cbn; lia |].
    replace (FA g pos + 256) with (FA g pos + 192 + 64) by lia. exact V64. }
pose proof (ast_ok_add_region tfibsegs E _ _ enc_rk HS1 eq_refl Hrk) as HS2.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.
apply HS2.
unfold rd_base, enc_rk, bm_frame_region, stack_region, bm_spill_region, bm_cur_region.
cbn [all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U33.
repeat split; lia.
Qed.

(* the cut facts at a callee's entry, after a run that wrote nothing outside the cursor window *)
Lemma enc_callst : forall g pos sp1 ops c k ly2 S2 W2 regs2 mem2 md2 kev ys E ss ms md3,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 kev ->
frames S2 = [(3, pos)] ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 -> ops_at ops regs2 -> cur_at g sp1 c W2 mem2 ->
k_at g pos k W2 mem2 ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2
  (ms_mem ms) md3 kev ->
env_agree 37 (bm_env g pos c regs2 ys) E ->
st_ok tfibsegs E ss (restrict (w_H W2) ms) -> ss_resv ss = None ->
bm_keep_ok (ss_regs ss) = true -> sr_get (ss_regs ss) 20%bv = SOff 20 0 ->
In bm_cur_region (ss_mem ss) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 184 <= a < sp1 + 200) ->
 aview tfibsegs (w_H W2) (ms_mem ms) a = aview tfibsegs (w_H W2) mem2 a) ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 (ms_regs ms) (ms_mem ms) md3 /\ ops_at ops (ms_regs ms) /\
cur_at g sp1 c W2 (ms_mem ms) /\ k_at g pos k W2 (ms_mem ms).
Proof.
intros g pos sp1 ops c k ly2 S2 W2 regs2 mem2 md2 kev ys E ss ms md3
  HJ Hfr HC Hops Hcur Hkat HJ3 HAG HS Hresv Hkeep H20 Hcr KE.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W2) E ss ms HS Hresv) as Ems.
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kev HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & Hblk).
pose proof HC as (Hpre & _ & R2 & _).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof Hcur as (Hc & _ & _).
pose proof HS as HS'. rewrite Ems in HS'.
assert (HAG35 : env_agree 35 (bm_env g pos c regs2 ys) E).
{ destruct HAG as (HA & HD). split; [intros n Hn'; apply HA; lia | exact HD]. }
split; [|split; [|split]].
- apply (bm_exit B MT K XM_LIB LAWS g pos sp1 0 0 c ys ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) md3
    kev (Z_to_bv 64 (ss_pc ss)) ss E HC HJ3 HAG35 HS' Hkeep).
  + intros a Ha. unfold bm_keepzone in Ha. apply KE; unfold BM_HI in *; [lia | lia].
  + intros i Hi. pose proof HC as HSH. do 47 (destruct HSH as (_ & HSH)). destruct HSH as (HSH' & _).
    rewrite <- (HSH' i Hi). apply KE.
    * unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_mod (FA g pos) 8 ltac:(lia)) as D.
      pose proof (Z.mod_pos_bound (FA g pos) 8 ltac:(lia)) as M. unfold BM_HI in *. lia.
    * unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_mod (FA g pos) 8 ltac:(lia)) as D.
      pose proof (Z.mod_pos_bound (FA g pos) 8 ltac:(lia)) as M. unfold BM_HI in *. lia.
  + pose proof HC as HPerm. do 49 (destruct HPerm as (_ & HPerm)). exact HPerm.
- destruct Hops as (Hops & R20). split; [exact Hops|].
  rewrite (st_ok_restrict_reg tfibsegs (w_H W2) E ss ms 20%bv HS), H20.
  destruct HAG as (HA & _). cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (HA 20%nat ltac:(lia)).
  rewrite (bm_ew_reg g pos c regs2 ys 20 20%bv eq_refl). exact R20.
- apply (bm_cur_end g pos c regs2 ys E ss W2 ms sp1 HAG HS Hcr R2); unfold BM_HI in *; lia.
- apply (k_at_kept g pos k W2 W2 mem2 (ms_mem ms) Hkat). intros x Hx. apply KE; unfold BM_HI in *; lia.
Qed.

(* the encoder's out argument at the call state *)
Lemma enc_out : forall g pos sp1 k ly2 S2 W2 regs mem md kev T,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem md kev ->
frames S2 = [(3, pos)] -> mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs mem md ->
k_at g pos k W2 mem -> kz_out k = fa5 -> 0 <= T -> 352 + T <= TB_main_need ->
cenc_out tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) ly2 S2 [(3, pos)] W2 mem sp1 T (FA g pos + 300) fa5.
Proof.
intros g pos sp1 k ly2 S2 W2 regs mem md kev T HJ Hfr HC ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G108 & _) & _) Ho HT HTn.
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs mem md kev HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & _).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity. pose proof satU_T_main_fits as Hfit.
split; [|split; [|reflexivity]].
- apply (satU_main_out_dst tfibsegs B LAWS LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
    [(3, pos)] ly2 S2 W2 mem md kev sp1 T pos (FA g pos) HJ ltac:(left; reflexivity) ltac:(rewrite Hfr; left; reflexivity)
    EFA Hf64 (bm_bs_k B MT K XM_LIB g pos sp1 ly2 S2 W2 regs mem md HC)); lia.
- rewrite Ho in G108. replace (FA g pos + 300) with (FA g pos + 192 + 108) by lia. exact G108.
Qed.

(* a callee's cdc_entry at a call state of the walk: the return address a literal, the rest from mcommon and the
   entry's budgets *)
Lemma enc_entry : forall g pos sp1 ly2 S2 W2 regs mem md kev T ra,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem md kev ->
frames S2 = [(3, pos)] -> 0 <= kev <= EV_LIB ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs mem md ->
getr regs 1 = Z_to_bv 64 ra -> 4096 <= ra < 2 ^ 63 -> ra mod 2 = 0 ->
0 <= T -> 352 + T <= TB_main_need ->
cdc_entry tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem md
  kev regs T.
Proof.
intros g pos sp1 ly2 S2 W2 regs mem md kev T ra HJ Hfr Hk HC R1 Hra Hra2 HT HTn.
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs mem md kev HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & _).
pose proof HC as (Hpre & _ & R2 & _ & _ & R3 & R4 & _).
pose proof Hpre as Hpre'. unfold e_pre, codec_lib_pre_x in Hpre'.
destruct Hpre' as (_ & _ & _ & _ & _ & _ & _ & _ & Hev & Hlive & _).
assert (FFS : LLVMF_STK = 32768) by reflexivity. pose proof satU_T_main_fits as Hfit.
assert (Usp : spZ regs = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; unfold BM_HI in *; lia).
apply (cpw_entry B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] (e_ly g) (e_S g)
  ly2 S2 W2 mem md kev regs T HJ).
- rewrite R1. apply ret_ok_even. rewrite unsigned_lit_small by lia. exact Hra2.
- unfold raZ. rewrite R1, unsigned_lit_small by lia. lia.
- exact R3.
- exact R4.
- rewrite Usp. pose proof (Z.div_mod sp1 32 ltac:(lia)) as D. rewrite Hsp32, Z.add_0_r in D.
  rewrite D. replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by lia. apply Z.mod_mul. lia.
- rewrite Usp. lia.
- rewrite Usp. lia.
- unfold EV_CDC, EV_LIB in *. lia.
- pose proof HC as HPerm. do 49 (destruct HPerm as (_ & HPerm)). exact HPerm.
- unfold LIVE_CDC, LIVE_LIB in *. lia.
Qed.

(* the personality argument and its disjointness from k.out, at a call state of the walk *)
Context {ROB : YCeh.ro_tfa_below_ofl}.
Lemma enc_pers : forall g pos sp1 ly2 S2 W2 regs mem md kev k od T,
globs_marked tfibsegs B CODEC_GLOBS -> img_shadow_vis tfibsegs B ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem md kev ->
frames S2 = [(3, pos)] -> mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs mem md ->
pd_okB (kz_p k) (kz_desk k) od -> 0 <= T -> 352 + T <= TB_main_need ->
pers_argA tfibsegs B W2 mem sp1 T (kz_p k) od /\ cpers_disj od (kz_p k) (FA g pos + 300) 32.
Proof.
intros g pos sp1 ly2 S2 W2 regs mem md kev k od T GM IV HJ Hfr HC Hpd HT HTn.
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs mem md kev HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & _).
pose proof HC as (Hpre & _).
assert (FFS : LLVMF_STK = 32768) by reflexivity. pose proof satU_T_main_fits as Hfit.
pose proof HJ as (HAR & _).
assert (Hin : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
split.
- apply (pers_argA_of_pdB B TL W2 mem sp1 T (kz_p k) (kz_desk k) od GM IV
    (arodata_ok_at B MT K XM_LIB g [(3, pos)] ly2 S2 W2 mem md kev Hpre HJ) Hpd).
  unfold CB_RHI. lia.
- destruct od as [d|]; [|exact I]. unfold cpers_disj.
  destruct (pd_range_B _ _ d Hpd) as (Hp & _).
  destruct (Z_le_gt_dec (kz_p k + 20) (FA g pos + 300)) as [Hle | Hgt]; [left; exact Hle|].
  destruct (Z_le_gt_dec (FA g pos + 300 + 32) (kz_p k + 16)) as [Hle2 | Hgt2]; [right; exact Hle2|].
  exfalso.
  apply (frm_img tfibsegs B LAWS ly2 S2 W2 mem md 3 pos (Z.max (FA g pos + 300) (kz_p k + 16)) HAR Hin);
    [rewrite EFA; change (fs_frame_bytes 3) with 512; lia|].
  apply (bm_img_of_b CB_PERS 48 ltac:(vm_compute; reflexivity)). unfold CB_PERS in *. lia.
Qed.
End b.
End a.
