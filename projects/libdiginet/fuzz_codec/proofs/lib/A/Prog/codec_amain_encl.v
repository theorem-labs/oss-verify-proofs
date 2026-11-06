(* The pieces the encoder segments ENC0 .. ENC11 of the image-A walk of LLVMFuzzerTestOneInput share
   (lib/A/Prog/codec_amain_inv.v, 0x820f4-0x8220c), and any segment of that walk that calls one of codec's own
   functions through its A-level contract:
   - am_call_kept: from the cut facts at a callee's entry (the journal at [(3, pos)], mcommon, the cursor) and the
     pieces of the callee's post (cdc_post: the journal at the return, the callee-saved registers, the blocks, and
     tcj_kept with sp = sp1 and a write set E inside the call record k = F + 176), the same facts at the return
     state, and every byte of the frame off E kept;
   - am_jb / am_jump: a `j tgt` (jal x0) at pc moves a cut from pc to tgt (lib/Reusable/YK11.v step_jal_x0);
   - kz_set_out / kcall_at_out: the call record with out replaced by the 32 bytes the encoder wrote;
   - amenc_finish: from the encoder call's entry state and the encoder's post (written over k.out = F + 284, the
     result cenc_res of enc_kZ) to JOIN 0x8220c (inv_join), through the `j 0x8220c` after the call for ENC0 ..
     ENC10 (ENC11 returns to 0x8220c itself). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC CPgEncC CodecRo CodecGlobs CPgWalk CPgWalkCall CPgSat.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_inv codec_amain_st codec_amain_lem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ================================ the record after an encoder ================================ *)
Definition kz_set_out (k : kcallZ) (o : list Z) : kcallZ :=
mkKcallZ (kz_kind k) (kz_p k) (kz_desk k) (kz_a k) (kz_b k) (kz_c k) (kz_delta k) (kz_bytes k) (kz_n k) (kz_rc k)
(kz_before k) o (kz_want_rc k) (kz_want k) (kz_want_len k) (kz_want_key k) (kz_want_display k).

(* bytes whose view is kept keep their values *)
Lemma am_garr8_kept : forall H H' (m m' : word -> option byte) a l,
(forall x, a <= x < a + Z.of_nat (length l) -> aview tfibsegs H' m' x = aview tfibsegs H m x) ->
garr8 tfibsegs (mrestrict H m) a l -> garr8 tfibsegs (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (cw_val_mem_kept H H' m m'); [|exact Hv]. intros x Hx. apply Hk. cbn in Hx. lia.
Qed.

(* the bytes of a value chunk, as val_mem *)
Lemma am_shiftr_mod : forall x (n k : nat), (k < n)%nat ->
Z.shiftr (x mod 2 ^ (8 * Z.of_nat n)) (8 * Z.of_nat k) mod 2 ^ 8 = Z.shiftr x (8 * Z.of_nat k) mod 2 ^ 8.
Proof.
intros x n k Hk. apply Z.bits_inj'. intros i Hi.
destruct (Z.lt_ge_cases i 8) as [H8|H8].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma am_val_of_chunk : forall E (m : word -> option byte) base off (w : N) v,
YP09.chunk_ok tfibsegs E m base (YP09.mkChunk off (CVal w v)) ->
val_mem tfibsegs m (base + off) (N.to_nat w) (bv_unsigned (sv_denot E v)).
Proof.
intros E m base off w v H k Hk.
destruct (H (Z.of_nat k) ltac:(cbn [YP09.c_len YP09.c_val YP09.cv_len]; lia)) as (b & Hb & Hm).
cbn [YP09.c_off YP09.c_val YP09.cbyte] in Hb, Hm. injection Hb as <-. rewrite Hm. f_equal.
unfold YP09.byte_of_word, YO0f.le_byte. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with (2 ^ 8). rewrite Z.mod_mod by lia.
symmetry. apply am_shiftr_mod. lia.
Qed.

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
{ intros o' l H1 H2 H3 Hg. apply (am_garr8_kept (w_H W) (w_H W') mem mem'); [|exact Hg].
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
(* the record kept whole *)
Lemma kz_set_out_id : forall k, kz_set_out k (kz_out k) = k.
Proof. intros []. reflexivity. Qed.
Lemma k_at_kept : forall g pos k (W W' : world tfibsegs) mem mem',
k_at g pos k W mem ->
(forall x, FA g pos + 176 <= x < FA g pos + 360 -> aview tfibsegs (w_H W') mem' x = aview tfibsegs (w_H W) mem x) ->
k_at g pos k W' mem'.
Proof.
intros g pos k W W' mem mem' (Hk & Hwf) KE. split; [|exact Hwf].
rewrite <- (kz_set_out_id k). apply (kcall_at_out W W' mem mem' (FA g pos + 176) k (kz_out k) Hk Hwf).
- intros x Hx _. apply KE. lia.
- pose proof Hk as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G108 & _).
  pose proof Hwf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Lo & _).
  apply (am_garr8_kept (w_H W) (w_H W') mem mem'); [|exact G108].
  intros x Hx. rewrite Lo in Hx. cbn in Hx. apply KE. lia.
Qed.

(* ================================ a `j tgt` at pc ================================ *)
Definition am_jb (pc tgt : Z) : bool :=
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

Lemma am_jb_sound : forall pc tgt, am_jb pc tgt = true -> 0 <= tgt < 2 ^ 64 ->
exists w imm, fetch_word tfibsegs (Z_to_bv 64 pc) = Some w /\ is_ecall w = false /\
decode_any w = Some (Jal 0 imm, 4) /\ btgt (Z_to_bv 64 pc) (bv_signed imm) = Z_to_bv 64 tgt.
Proof.
intros pc tgt H Ht. unfold am_jb in H.
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
   ENCk's state: the base without the .got slot and the cell (am_base3), and k's scalar fields as atoms of the
   segment (enc_ys): p = atom 37 (8 bytes at k + 8), a / b / c = atoms 38 / 39 / 40 (4 bytes at k + 24 / 28 / 32),
   delta mod 2^32 = atom 41 (k + 36), n = atom 42 (8 bytes at k + 64). *)
Definition am_base3 : smem := [stack_region 0; am_spill_region; am_cur_region].
Definition enc_ys (k : kcallZ) : list Z := [kz_p k; kz_a k; kz_b k; kz_c k; kz_delta k mod 2 ^ 32; kz_n k].
Definition enc_rk : YP09.region := am_frame_region 176 248 176 176
[YP09.mkChunk 184 (CVal 8 (SOff 37 0)); YP09.mkChunk 200 (CVal 4 (SOff 38 0)); YP09.mkChunk 204 (CVal 4 (SOff 39 0));
 YP09.mkChunk 208 (CVal 4 (SOff 40 0)); YP09.mkChunk 212 (CVal 4 (SOff 41 0)); YP09.mkChunk 240 (CVal 8 (SOff 42 0))].
Definition enc_ss (pc : Z) : sstate := mkSS pc am_sregs (enc_rk :: am_base3) None (mkFacts am_atoms [] []).

(* the registers the encoders' arguments arrive in, as the run leaves them: `lw` of a 4-byte field (sign-extended),
   `lbu` / `lhu` of its low byte(s) (zero-extended) *)
Lemma am_sx32 : forall v, 0 <= v < 2 ^ 32 ->
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
Lemma am_zx : forall v (w : N), 0 <= v < 2 ^ 64 ->
zext 64 (bv_extract 0 w (Z_to_bv 64 v)) = Z_to_bv 64 (v mod 2 ^ Z.of_N w).
Proof.
intros v w Hv. rewrite zext64_lit. f_equal.
rewrite bv_extract_unsigned, Z_to_bv_unsigned, Z.shiftr_0_r.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small v (2 ^ 64)) by lia. reflexivity.
Qed.
Lemma am_s32_mod : forall d, - 2 ^ 31 <= d < 2 ^ 31 -> DgnLib.s32 (d mod 2 ^ 32) = d.
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
Lemma am_s32_range : forall c, 0 <= c < 2 ^ 32 -> - 2 ^ 31 <= DgnLib.s32 c < 2 ^ 31.
Proof. intros c Hc. unfold DgnLib.s32. destruct (Z.ltb_spec c (2 ^ 31)); lia. Qed.
(* bytes of the loaded image, by computation over the segments *)
Definition am_img_b (q n : Z) : bool :=
existsb (fun s => (Z.of_N (seg_base s) <=? q) && (q + n <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool tfibsegs.
Lemma am_img_of_b : forall q n, am_img_b q n = true -> forall a, q <= a < q + n -> in_img tfibsegs a.
Proof.
intros q n Hb a Ha. unfold am_img_b in Hb. apply existsb_exists in Hb as (s & Hin & Hc).
apply andb_prop in Hc as (Hlo & Hhi). apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
exists s. split; [exact Hin | lia].
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* the cursor at the end of a run whose state still holds the cursor region am_cur_region *)
Lemma am_cur_end : forall g pos c regs ys E ss (W : world tfibsegs) ms sp1,
env_agree 37 (am_env g pos c regs ys) E ->
st_ok tfibsegs E ss (restrict (w_H W) ms) -> In am_cur_region (ss_mem ss) ->
getr regs 2 = w64 sp1 -> 0 <= sp1 -> sp1 + 168 <= 2 ^ 64 ->
0 <= c <= e_n g -> 0 <= e_p g -> e_p g + e_n g < 2 ^ 64 ->
cur_at g sp1 c W (ms_mem ms).
Proof.
intros g pos c regs ys E ss W ms sp1 (HA & _) HS Hin R2 Hs0 Hs1 Hc Hp Hpn.
pose proof (st_ok_mem_ok tfibsegs E ss _ HS) as (_ & Hok & _).
rewrite Forall_forall in Hok. pose proof (Hok _ Hin) as Hr.
unfold region_ok, am_cur_region in Hr.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in Hr.
destruct Hr as (_ & _ & _ & Hch).
assert (U2 : bv_unsigned (ew E 2) = sp1).
{ rewrite (HA 2%nat ltac:(lia)), (am_ew_reg g pos c regs ys 2 2%bv eq_refl), R2. unfold w64.
  apply unsigned_lit_small. lia. }
rewrite U2 in Hch.
apply Forall_cons_iff in Hch as (H152 & Hch1). apply Forall_cons_iff in Hch1 as (H160 & _).
pose proof (am_val_of_chunk E _ sp1 152 8 (SOff 35 0) H152) as V1.
pose proof (am_val_of_chunk E _ sp1 160 8 (SOff 36 0) H160) as V2.
rewrite (am_den_off E 35 (e_p g + c) 0) in V1;
  [| rewrite (HA 35%nat ltac:(lia)); exact (am_ew_CP g pos c regs ys) | lia | lia].
rewrite (am_den_off E 36 (e_n g - c) 0) in V2;
  [| rewrite (HA 36%nat ltac:(lia)); exact (am_ew_CN g pos c regs ys) | lia | lia].
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
Lemma am_jump : forall g pos sp1 kv pc tgt (P : alayout -> astate -> world tfibsegs -> bvmap 5 word ->
  (word -> option byte) -> Model -> Prop) W c,
am_jb pc tgt = true -> 0 <= tgt < 2 ^ 64 ->
(forall ly S W regs mem md md', P ly S W regs mem md -> P ly S W regs mem md') ->
mcut B MT K XM_LIB g pos sp1 kv pc P W c -> SRr tfibsegs W c (mcut B MT K XM_LIB g pos sp1 kv tgt P).
Proof.
intros g pos sp1 kv pc tgt P W c Hjb Ht HPmd (ly2 & S2 & regs2 & mem2 & md2 & k & -> & HJ & Hfr & Hk & Hmo & HC & HP).
destruct (am_jb_sound pc tgt Hjb Ht) as (w & imm & Hf & He & Hd & Htg).
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

(* ================================ a cut across a call ================================ *)
Lemma am_call_kept : forall g pos sp1 kv ly2 S2 W2 regsc mem2 md2 kev c T (Ef : Z -> Prop)
ly3 S3 W3 regs3 mem3 md3 k3,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 kev ->
frames S2 = [(3, pos)] ->
mcommon B MT K XM_LIB g pos sp1 kv ly2 S2 W2 regsc mem2 md2 ->
cur_at g sp1 c W2 mem2 ->
(forall a, Ef a -> FA g pos + 176 <= a < FA g pos + 360) ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly3 S3 W3 mem3 md3 k3 ->
aregs_preserved regsc regs3 ->
Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) ->
tcj_kept tfibsegs B T ly2 S2 W2 mem2 W3 mem3 (spZ regsc) Ef ->
mcommon B MT K XM_LIB g pos sp1 kv ly3 S3 W3 regs3 mem3 md3 /\ cur_at g sp1 c W3 mem3 /\
(forall a, FA g pos <= a < FA g pos + 512 -> ~ Ef a ->
 aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W2) mem2 a).
Proof.
intros g pos sp1 kv ly2 S2 W2 regsc mem2 md2 kev c T Ef ly3 S3 W3 regs3 mem3 md3 k3 HJ Hfr HC Hcur HEf HJ3 HPR HPerm HK.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 kv ly2 S2 W2 regsc mem2 md2 kev HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & Hblk).
pose proof HJ as (HAR & _).
assert (Hin : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
destruct (frames_bounds tfibsegs B LAWS ly2 S2 W2 mem2 md2 3 pos HAR Hin) as (_ & _ & Happ).
assert (E512 : fs_frame_bytes 3 = 512) by reflexivity.
rewrite EFA, E512 in Happ.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
destruct HC as (Hpre & Hsp1 & R2 & R9 & R8 & R3 & R4 & R20 & R18 & R21 & R22 & R25 & R19 & R27 & H64 &
  V16 & V24 & V32 & V40 & V48 & V56 & V64 & V72 & V80 & V88 & V96 & V104 & V112 & V120 &
  S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96 & S104 & VFL & SHM & GIN & PERM).
assert (Usp : spZ regsc = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
rewrite Usp in HK. destruct HK as (K1 & _ & _ & K4 & _ & _).
set (F := FA g pos) in *.
(* the machine stack at or above sp1: kept by clause 1 *)
assert (KS : forall a, sp1 <= a < e_sp0 g -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W2) mem2 a).
{ intros a Ha. apply K1; [lia | lia | intros He; pose proof (HEf a He); lia]. }
(* the frame and its shadow: kept by clause 4 off E *)
assert (KF : forall a, F <= a < F + 512 -> ~ Ef a -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W2) mem2 a).
{ intros a Ha He. apply (K4 3 pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA, E512; lia | exact He]. }
assert (KSH : forall i, 0 <= i < 56 ->
  aview tfibsegs (w_H W3) mem3 (shadow_addr F + i) = aview tfibsegs (w_H W2) mem2 (shadow_addr F + i)).
{ intros i Hi. apply (K4 3 pos _ Hin).
  - right. unfold in_zr. cbn [fst snd]. rewrite EFA, E512. change (512 / 8) with 64. lia.
  - intros He. pose proof (HEf _ He) as Hr. unfold shadow_addr, SHADOW_OFF in Hr.
    pose proof (Z.div_mod F 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M8.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. lia. }
assert (VK : forall a n v, sp1 <= a -> a + Z.of_nat n <= e_sp0 g ->
  val_mem tfibsegs (mrestrict (w_H W2) mem2) a n v -> val_mem tfibsegs (mrestrict (w_H W3) mem3) a n v).
{ intros a n v H1 H2 Hv. apply (cw_val_mem_kept (w_H W2) (w_H W3) mem2 mem3); [|exact Hv].
  intros x Hx. apply KS. lia. }
assert (P2 : getr regs3 2 = getr regsc 2) by exact (HPR 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs3 3 = getr regsc 3) by exact (HPR 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs3 4 = getr regsc 4) by exact (HPR 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs3 8 = getr regsc 8) by exact (HPR 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs3 9 = getr regsc 9) by exact (HPR 9 ltac:(unfold acallee_saved; lia)).
assert (P18 : getr regs3 18 = getr regsc 18) by exact (HPR 18 ltac:(unfold acallee_saved; lia)).
assert (P19 : getr regs3 19 = getr regsc 19) by exact (HPR 19 ltac:(unfold acallee_saved; lia)).
assert (P20 : getr regs3 20 = getr regsc 20) by exact (HPR 20 ltac:(unfold acallee_saved; lia)).
assert (P21 : getr regs3 21 = getr regsc 21) by exact (HPR 21 ltac:(unfold acallee_saved; lia)).
assert (P22 : getr regs3 22 = getr regsc 22) by exact (HPR 22 ltac:(unfold acallee_saved; lia)).
assert (P25 : getr regs3 25 = getr regsc 25) by exact (HPR 25 ltac:(unfold acallee_saved; lia)).
assert (P27 : getr regs3 27 = getr regsc 27) by exact (HPR 27 ltac:(unfold acallee_saved; lia)).
pose proof Hpre as Hpre'. unfold e_pre, codec_lib_pre_x in Hpre'.
destruct Hpre' as (_ & _ & _ & _ & _ & Hnpl & _).
pose proof Hcur as (Hc & C152 & C160).
split; [|split].
- refine (conj Hpre (conj Hsp1 _)).
  rewrite P2, P9, P8, P3, P4, P20, P18, P21, P22, P25, P19, P27.
  refine (conj R2 (conj R9 (conj R8 (conj R3 (conj R4 (conj R20 (conj R18 (conj R21 (conj R22 (conj R25
    (conj R19 (conj R27 (conj H64 _))))))))))))).
  split; [apply VK; [lia | cbn; lia | exact V16]|].
  split; [apply VK; [lia | cbn; lia | exact V24]|].
  split; [apply VK; [lia | cbn; lia | exact V32]|].
  split; [apply VK; [lia | cbn; lia | exact V40]|].
  split; [apply VK; [lia | cbn; lia | exact V48]|].
  split; [apply VK; [lia | cbn; lia | exact V56]|].
  split; [apply VK; [lia | cbn; lia | exact V64]|].
  split; [apply VK; [lia | cbn; lia | exact V72]|].
  split; [apply VK; [lia | cbn; lia | exact V80]|].
  split; [apply VK; [lia | cbn; lia | exact V88]|].
  split; [apply VK; [lia | cbn; lia | exact V96]|].
  split; [apply VK; [lia | cbn; lia | exact V104]|].
  split; [apply VK; [lia | cbn; lia | exact V112]|].
  split; [apply VK; [lia | cbn; lia | exact V120]|].
  split; [apply VK; [lia | cbn; lia | exact S8]|].
  split; [apply VK; [lia | cbn; lia | exact S16]|].
  split; [apply VK; [lia | cbn; lia | exact S24]|].
  split; [apply VK; [lia | cbn; lia | exact S32]|].
  split; [apply VK; [lia | cbn; lia | exact S40]|].
  split; [apply VK; [lia | cbn; lia | exact S48]|].
  split; [apply VK; [lia | cbn; lia | exact S56]|].
  split; [apply VK; [lia | cbn; lia | exact S64]|].
  split; [apply VK; [lia | cbn; lia | exact S72]|].
  split; [apply VK; [lia | cbn; lia | exact S80]|].
  split; [apply VK; [lia | cbn; lia | exact S88]|].
  split; [apply VK; [lia | cbn; lia | exact S96]|].
  split; [apply VK; [lia | cbn; lia | exact S104]|].
  split.
  { apply (cw_val_mem_kept (w_H W2) (w_H W3) mem2 mem3); [|exact VFL].
    intros x Hx. cbn in Hx. apply KF; [lia|]. intros He. pose proof (HEf x He). lia. }
  split; [intros i Hi; etransitivity; [exact (KSH i Hi) | exact (SHM i Hi)]|].
  split; [|exact (Permutation_trans HPerm PERM)].
  destruct (Z.eq_dec (e_n g) 0) as [Hn0 | Hn0].
  + intros j Hj. exfalso. rewrite length_map in Hj. lia.
  + destruct (Hblk ltac:(lia)) as (Hb2 & Hb0).
    assert (Hb3 : In (e_p g, e_n g) (ablocks B ly3 S3))
      by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Hb2]).
    pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & J2 & _).
    pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & J3 & _).
    pose proof (req_size_pos (e_n g) ltac:(lia)) as (_ & Hrq).
    apply (am_garr8_kept (w_H W2) (w_H W3) mem2 mem3); [|exact GIN].
    intros x Hx. rewrite length_map in Hx.
    replace x with (e_p g + (x - e_p g)) by lia.
    rewrite (J3 (e_p g) (e_n g) (x - e_p g) Hb0 Hb3 ltac:(lia) (inFP_nil _)).
    rewrite (J2 (e_p g) (e_n g) (x - e_p g) Hb0 Hb2 ltac:(lia) (inFP_nil _)). reflexivity.
- split; [exact Hc|]. split; [apply VK; [lia | cbn; lia | exact C152] | apply VK; [lia | cbn; lia | exact C160]].
- exact KF.
Qed.

(* ================================ the encoder call to JOIN ================================ *)
Lemma amenc_finish : forall g pos sp1 ops c k od ly2 S2 W2 regsc mem2 md2 kev T ra W3 c3,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 kev ->
frames S2 = [(3, pos)] -> 0 <= kev <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regsc mem2 md2 ->
ops_at ops regsc -> cur_at g sp1 c W2 mem2 -> k_at g pos k W2 mem2 -> enc_okZ k od ->
getr regsc 1 = w64 ra -> (ra = PC_JOIN \/ am_jb ra PC_JOIN = true) ->
cdc_post tfibsegs B MT LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] kev regsc T
  (cenc_wr (FA g pos + 284)) ly2 S2 W2 mem2 md2 (cenc_res tfibsegs (FA g pos + 284) fa5 (enc_kZ k od)) W3 c3 ->
SRr tfibsegs W3 c3 (inv_join B MT K XM_LIB g pos sp1 ops).
Proof.
intros g pos sp1 ops c k od ly2 S2 W2 regsc mem2 md2 kev T ra W3 c3 HJ Hfr Hk Hmo HC Hops Hcur Hkat Henc Hra Hjb Hpost.
destruct Hpost as (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HPR & Hfr3 & HPerm & _ & Hmo3 & HK & Ha0 & Hout).
unfold EV_CDC in HJ3. rewrite Z.add_0_r in HJ3.
destruct (am_call_kept g pos sp1 0 ly2 S2 W2 regsc mem2 md2 kev c T (cenc_wr (FA g pos + 284))
  ly3 S3 W3 regs3 mem3 md3 kev HJ Hfr HC Hcur ltac:(unfold cenc_wr; intros a Ha; lia) HJ3 HPR HPerm HK)
  as (HC3 & Hcur3 & KF).
pose proof Henc as (Hkind & Hpd & Hrdr & Hbe & Hko).
pose proof Hkat as (Hkat2 & Hwf).
set (o := cmd_outZ fa5 (snd (enc_kZ k od))).
assert (Lo : length o = 32%nat) by exact (enc_kZ_out_len k od Henc).
assert (Hkat3 : k_at g pos (kz_set_out k o) W3 mem3).
{ split.
  - apply (kcall_at_out W2 W3 mem2 mem3 (FA g pos + 176) k o Hkat2 Hwf).
    + intros x Hx Hx2. apply KF; [lia|]. unfold cenc_wr. lia.
    + replace (FA g pos + 176 + 108) with (FA g pos + 284) by lia. exact Hout.
  - destruct Hwf as (W1 & W2' & W3' & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13 & W14 & W15 & _ & W17).
    unfold kz_set_out, kcall_wfZ. cbn [kz_kind kz_p kz_desk kz_a kz_b kz_c kz_delta kz_bytes kz_n kz_rc kz_before kz_out
      kz_want_rc kz_want kz_want_len kz_want_key kz_want_display].
    exact (conj W1 (conj W2' (conj W3' (conj W4 (conj W5 (conj W6 (conj W7 (conj W8 (conj W9 (conj W10 (conj W11
      (conj W12 (conj W13 (conj W14 (conj W15 (conj Lo W17)))))))))))))))). }
assert (Hrec : rec_okZ (kz_set_out k o) od).
{ unfold rec_okZ, kz_set_out. cbn [kz_kind kz_p kz_desk kz_before kz_out].
  split; [exact Hkind|]. split; [exact Hpd|]. split; [exact Hrdr|]. split; [exact Hbe|]. reflexivity. }
assert (HPR26 : getr regs3 26 = getr regsc 26) by exact (HPR 26 ltac:(unfold acallee_saved; lia)).
pose proof HJ as (HAR & _).
assert (Hmo' : mo_le MT (e_S g) S3 0) by exact (mo_le_trans MT MTL _ _ _ 0 0 Hmo Hmo3).
assert (HM : mcut B MT K XM_LIB g pos sp1 0 ra (fun ly2 S2 W2 regs2 mem2 md2 => ops_at ops regs2 /\
  exists c k od, cur_at g sp1 c W2 mem2 /\ k_at g pos k W2 mem2 /\ rec_okZ k od /\
  getr regs2 10 = w64 (fst (enc_kZ k od))) W3 (cfg_at tfibsegs ra regs3 mem3 md3)).
{ exists ly3, S3, regs3, mem3, md3, kev. split; [reflexivity|].
  split; [exact HJ3|]. split; [rewrite Hfr3; exact Hfr|]. split; [exact Hk|]. split; [exact Hmo'|].
  split; [exact HC3|].
  split; [destruct Hops as [Ho1 Ho2]; split; [exact Ho1 | rewrite HPR26; exact Ho2]|].
  exists c, (kz_set_out k o), od. split; [exact Hcur3|]. split; [exact Hkat3|]. split; [exact Hrec|].
  exact Ha0. }
rewrite Hra. change (mkCfg (mkst regs3 (w64 ra) mem3 (seg_rom tfibsegs)) md3) with (cfg_at tfibsegs ra regs3 mem3 md3).
destruct Hjb as [-> | Hjb].
- apply SRr_ret. exact HM.
- apply (am_jump g pos sp1 0 ra PC_JOIN _ W3 _ Hjb ltac:(unfold PC_JOIN; lia)); [|exact HM].
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
st_ok tfibsegs (am_env g pos c regs2 (enc_ys k)) (enc_ss pc)
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 pc) mem2 (seg_rom tfibsegs))).
Proof.
intros g pos sp1 ly2 S2 W2 regs2 mem2 md2 kev c k pc HJ Hfr HC Hcur ((V0 & V8 & V16 & V24 & V28 & V32 & V36 & _ & V64 & _) & Hwf).
pose proof Hwf as (_ & Wp & _ & Wa & Wb & Wc & Wd & Wn & _).
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kev HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & _).
unfold AM_HI in Hchi.
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof HC as (Hpre & _ & R2 & _).
set (E := am_env g pos c regs2 (enc_ys k)).
pose proof (am_entry B MT K XM_LIB TL LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kev c pc (enc_ys k) [] []
  HJ Hfr HC Hcur eq_refl (Forall_nil _) I (Forall_nil _) I) as HS0.
fold E in HS0.
pose proof (st_ok_submem tfibsegs E (am_ss pc [] []) _ am_base3 HS0
  ltac:(cbn [am_ss am_ssb ss_mem]; unfold am_regs, am_regs0, cw_regs, am_base3; cbn [app]; submem_to)
  ltac:(vm_compute; reflexivity)) as HS1.
cbn [am_ss am_ssb ss_pc ss_regs ss_resv ss_facts] in HS1. rewrite app_nil_r in HS1.
assert (U2 : bv_unsigned (ew E 2) = sp1).
{ subst E. rewrite (am_ew_reg g pos c regs2 _ 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
assert (U33 : bv_unsigned (ew E 33) = FA g pos).
{ subst E. rewrite (am_ew_F g pos c regs2 _). apply unsigned_lit_small. lia. }
assert (EY : forall j, ew E (AM_X0 + j) = Z_to_bv 64 (nth j (enc_ys k) 0)) by (intros j; subst E; apply am_ew_y).
pose proof (Z.mod_pos_bound (kz_delta k) (2 ^ 32) ltac:(lia)) as Md.
assert (DY : forall j v, nth j (enc_ys k) 0 = v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff (AM_X0 + j) 0) = Z_to_bv 64 v).
{ intros j v Hj Hv. rewrite (am_den_off E (AM_X0 + j) v 0); [f_equal; lia | rewrite EY, Hj; reflexivity | lia | lia]. }
assert (Hrk : region_ok tfibsegs E (mrestrict (w_H W2) mem2) enc_rk).
{ apply (am_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kev c (enc_ys k) 176 248 176 176
    _ HJ Hfr HC ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 184 8 (SOff 37 0) (kz_p k)); [exact (DY 0%nat (kz_p k) eq_refl ltac:(lia)) | cbn; lia | cbn; lia |].
    replace (FA g pos + 184) with (FA g pos + 176 + 8) by lia. exact V8.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 200 4 (SOff 38 0) (kz_a k)); [exact (DY 1%nat (kz_a k) eq_refl ltac:(lia)) | cbn; lia | cbn; lia |].
    replace (FA g pos + 200) with (FA g pos + 176 + 24) by lia. exact V24.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 204 4 (SOff 39 0) (kz_b k)); [exact (DY 2%nat (kz_b k) eq_refl ltac:(lia)) | cbn; lia | cbn; lia |].
    replace (FA g pos + 204) with (FA g pos + 176 + 28) by lia. exact V28.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 208 4 (SOff 40 0) (kz_c k)); [exact (DY 3%nat (kz_c k) eq_refl ltac:(lia)) | cbn; lia | cbn; lia |].
    replace (FA g pos + 208) with (FA g pos + 176 + 32) by lia. exact V32.
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 212 4 (SOff 41 0) (kz_delta k mod 2 ^ 32));
      [exact (DY 4%nat (kz_delta k mod 2 ^ 32) eq_refl ltac:(lia)) | cbn; lia | cbn; lia |].
    replace (FA g pos + 212) with (FA g pos + 176 + 36) by lia. exact (cw_val_mem_mod _ _ 4 _ V36).
  - apply (chunk_ok_val tfibsegs E _ (FA g pos) 240 8 (SOff 42 0) (kz_n k)); [exact (DY 5%nat (kz_n k) eq_refl ltac:(lia)) | cbn; lia | cbn; lia |].
    replace (FA g pos + 240) with (FA g pos + 176 + 64) by lia. exact V64. }
pose proof (ast_ok_add_region tfibsegs E _ _ enc_rk HS1 eq_refl Hrk) as HS2.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.
apply HS2.
unfold am_base3, enc_rk, am_frame_region, stack_region, am_spill_region, am_cur_region.
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
env_agree 37 (am_env g pos c regs2 ys) E ->
st_ok tfibsegs E ss (restrict (w_H W2) ms) -> ss_resv ss = None ->
am_keep_ok (ss_regs ss) = true -> sr_get (ss_regs ss) 26%bv = SOff 26 0 ->
In am_cur_region (ss_mem ss) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 152 <= a < sp1 + 168) ->
 aview tfibsegs (w_H W2) (ms_mem ms) a = aview tfibsegs (w_H W2) mem2 a) ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 (ms_regs ms) (ms_mem ms) md3 /\ ops_at ops (ms_regs ms) /\
cur_at g sp1 c W2 (ms_mem ms) /\ k_at g pos k W2 (ms_mem ms).
Proof.
intros g pos sp1 ops c k ly2 S2 W2 regs2 mem2 md2 kev ys E ss ms md3
  HJ Hfr HC Hops Hcur Hkat HJ3 HAG HS Hresv Hkeep H26 Hcr KE.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W2) E ss ms HS Hresv) as Ems.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kev HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & Hblk).
pose proof HC as (Hpre & _ & R2 & _).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof Hcur as (Hc & _ & _).
pose proof HS as HS'. rewrite Ems in HS'.
assert (HAG35 : env_agree 35 (am_env g pos c regs2 ys) E).
{ destruct HAG as (HA & HD). split; [intros n Hn'; apply HA; lia | exact HD]. }
split; [|split; [|split]].
- apply (am_exit B MT K XM_LIB LAWS g pos sp1 0 0 c ys ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) md3
    kev (Z_to_bv 64 (ss_pc ss)) ss E HC HJ3 HAG35 HS' Hkeep).
  + intros a Ha. unfold am_keepzone in Ha. apply KE; [lia | lia].
  + intros i Hi. pose proof HC as HSH. do 43 (destruct HSH as (_ & HSH)). destruct HSH as (HSH' & _).
    rewrite <- (HSH' i Hi). apply KE.
    * unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_mod (FA g pos) 8 ltac:(lia)) as D.
      pose proof (Z.mod_pos_bound (FA g pos) 8 ltac:(lia)) as M. unfold AM_HI in *. lia.
    * unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_mod (FA g pos) 8 ltac:(lia)) as D.
      pose proof (Z.mod_pos_bound (FA g pos) 8 ltac:(lia)) as M. unfold AM_HI in *. lia.
  + pose proof HC as HPerm. do 45 (destruct HPerm as (_ & HPerm)). exact HPerm.
- destruct Hops as (Hops & R26). split; [exact Hops|].
  rewrite (st_ok_restrict_reg tfibsegs (w_H W2) E ss ms 26%bv HS), H26.
  destruct HAG as (HA & _). cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (HA 26%nat ltac:(lia)).
  rewrite (am_ew_reg g pos c regs2 ys 26 26%bv eq_refl). exact R26.
- apply (am_cur_end g pos c regs2 ys E ss W2 ms sp1 HAG HS Hcr R2); unfold AM_HI in *; lia.
- apply (k_at_kept g pos k W2 W2 mem2 (ms_mem ms) Hkat). intros x Hx. apply KE; unfold AM_HI in *; lia.
Qed.

(* the encoder's out argument at the call state *)
Lemma enc_out : forall g pos sp1 k ly2 S2 W2 regs mem md kev T,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem md kev ->
frames S2 = [(3, pos)] -> mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs mem md ->
k_at g pos k W2 mem -> kz_out k = fa5 -> 0 <= T -> 320 + T <= T_main_need ->
cenc_out tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) ly2 S2 [(3, pos)] W2 mem sp1 T (FA g pos + 284) fa5.
Proof.
intros g pos sp1 k ly2 S2 W2 regs mem md kev T HJ Hfr HC ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G108 & _) & _) Ho HT HTn.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs mem md kev HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & _).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity. unfold T_main_need in HTn.
split; [|split; [|reflexivity]].
- apply (sat_main_out_dst tfibsegs B LAWS LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
    [(3, pos)] ly2 S2 W2 mem md kev sp1 T pos (FA g pos) HJ ltac:(left; reflexivity) ltac:(rewrite Hfr; left; reflexivity)
    EFA Hf64 (am_bs_k B MT K XM_LIB g pos sp1 ly2 S2 W2 regs mem md HC)); lia.
- rewrite Ho in G108. replace (FA g pos + 284) with (FA g pos + 176 + 108) by lia. exact G108.
Qed.

(* a callee's cdc_entry at a call state of the walk: the return address a literal, the rest from mcommon and the
   entry's budgets *)
Lemma enc_entry : forall g pos sp1 ly2 S2 W2 regs mem md kev T ra,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem md kev ->
frames S2 = [(3, pos)] -> 0 <= kev <= EV_LIB ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs mem md ->
getr regs 1 = Z_to_bv 64 ra -> 4096 <= ra < 2 ^ 63 -> ra mod 2 = 0 ->
0 <= T -> 320 + T <= T_main_need ->
cdc_entry tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem md
  kev regs T.
Proof.
intros g pos sp1 ly2 S2 W2 regs mem md kev T ra HJ Hfr Hk HC R1 Hra Hra2 HT HTn.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs mem md kev HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & _).
pose proof HC as (Hpre & _ & R2 & _ & _ & R3 & R4 & _).
pose proof Hpre as Hpre'. unfold e_pre, codec_lib_pre_x in Hpre'.
destruct Hpre' as (_ & _ & _ & _ & _ & _ & _ & _ & Hev & Hlive & _).
assert (FFS : LLVMF_STK = 32768) by reflexivity. unfold T_main_need in HTn.
assert (Usp : spZ regs = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; unfold AM_HI in *; lia).
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
- pose proof HC as HPerm. do 45 (destruct HPerm as (_ & HPerm)). exact HPerm.
- unfold LIVE_CDC, LIVE_LIB in *. lia.
Qed.

(* the personality argument and its disjointness from k.out, at a call state of the walk *)
Context {ROB : ACeh.ro_tfa_below_ofl}.
Lemma enc_pers : forall g pos sp1 ly2 S2 W2 regs mem md kev k od T,
globs_marked tfibsegs B CODEC_GLOBS -> img_shadow_vis tfibsegs B ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem md kev ->
frames S2 = [(3, pos)] -> mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs mem md ->
pd_okA (kz_p k) (kz_desk k) od -> 0 <= T -> 320 + T <= T_main_need ->
pers_argA tfibsegs B W2 mem sp1 T (kz_p k) od /\ cpers_disj od (kz_p k) (FA g pos + 284) 32.
Proof.
intros g pos sp1 ly2 S2 W2 regs mem md kev k od T GM IV HJ Hfr HC Hpd HT HTn.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs mem md kev HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & _).
pose proof HC as (Hpre & _).
assert (FFS : LLVMF_STK = 32768) by reflexivity. unfold T_main_need in HTn.
pose proof HJ as (HAR & _).
assert (Hin : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
split.
- apply (pers_argA_of_pdA B TL W2 mem sp1 T (kz_p k) (kz_desk k) od GM IV
    (arodata_ok_at B MT K XM_LIB g [(3, pos)] ly2 S2 W2 mem md kev Hpre HJ) Hpd).
  unfold CA_RHI. lia.
- destruct od as [d|]; [|exact I]. unfold cpers_disj.
  destruct (pd_range_A _ _ d Hpd) as (Hp & _).
  destruct (Z_le_gt_dec (kz_p k + 20) (FA g pos + 284)) as [Hle | Hgt]; [left; exact Hle|].
  destruct (Z_le_gt_dec (FA g pos + 284 + 32) (kz_p k + 16)) as [Hle2 | Hgt2]; [right; exact Hle2|].
  exfalso.
  apply (frm_img tfibsegs B LAWS ly2 S2 W2 mem md 3 pos (Z.max (FA g pos + 284) (kz_p k + 16)) HAR Hin);
    [rewrite EFA; change (fs_frame_bytes 3) with 512; lia|].
  apply (am_img_of_b CA_PERS 48 ltac:(vm_compute; reflexivity)). unfold CA_PERS in *. lia.
Qed.
End b.
End a.
