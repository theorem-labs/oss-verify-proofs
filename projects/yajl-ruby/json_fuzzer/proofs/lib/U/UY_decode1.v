(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel SFW1_lemmas InitMem Arr Mem NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UMallocRep UMallocTree UMalloc_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UYajlAlign UYajl_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UY_rz UY_kit2 UF_strlen.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc Prelim YajlBase YajlBuf YajlLex YajlDecode YajlLeaf YajlFactsBuf YajlFactsLex YajlFactsDecode YajlFactsBits.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition LKnil (l : list block) : Prop := l = [].
Lemma lk_hide : forall l : list block, l = [] -> LKnil l. Proof. intros l H; exact H. Qed.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma zbytes_firstn : forall k l, zbytes (firstn k l) = firstn k (zbytes l).
Proof. intros k l. unfold zbytes. rewrite firstn_map. reflexivity. Qed.
Lemma zbytes_skipn : forall k l, zbytes (skipn k l) = skipn k (zbytes l).
Proof. intros k l. unfold zbytes. rewrite skipn_map. reflexivity. Qed.

Lemma bytes_at_sub : forall m A bs i k,
  bytes_at usegs m A bs -> (i <= length bs)%nat -> bytes_at usegs m (A + Z.of_nat i) (firstn k (skipn i bs)).
Proof.
  intros m A bs i k HB Hi.
  rewrite <- (firstn_skipn i bs) in HB. apply bytes_at_app in HB. destruct HB as [_ HB].
  rewrite length_firstn, Nat.min_l in HB by lia.
  rewrite <- (firstn_skipn k (skipn i bs)) in HB. apply bytes_at_app in HB. destruct HB as [HB _]. exact HB.
Qed.

Lemma bytes_at_zslice : forall m A str i k,
  bytes_at usegs m A (zbytes str) -> 0 <= i <= zlength str -> bytes_at usegs m (A + i) (zbytes (zslice str i k)).
Proof.
  intros m A str i k HB Hi. unfold zslice. rewrite zbytes_firstn, zbytes_skipn.
  replace i with (Z.of_nat (Z.to_nat i)) at 1 by lia. apply bytes_at_sub; [exact HB|]. rewrite zbytes_length. unfold zlength in Hi. lia.
Qed.

Lemma Forall_firstn : forall {A} (P : A -> Prop) k l, Forall P l -> Forall P (firstn k l).
Proof. intros A P k l H. rewrite <- (firstn_skipn k l) in H. apply Forall_app in H. tauto. Qed.
Lemma Forall_skipn : forall {A} (P : A -> Prop) k l, Forall P l -> Forall P (skipn k l).
Proof. intros A P k l H. rewrite <- (firstn_skipn k l) in H. apply Forall_app in H. tauto. Qed.
Lemma Forall_zslice : forall (P : Z -> Prop) str i k, Forall P str -> Forall P (zslice str i k).
Proof. intros P str i k HF. unfold zslice. apply Forall_firstn, Forall_skipn. exact HF. Qed.

(* [comment removed for export] *)
Lemma yzext32_idiom : forall x, 0 <= x < 2^32 ->
  (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) ≪ 32)) ≫ 32) = x.
Proof.
  intros x Hx. rewrite (unsigned_lit x) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite unsigned_lit by (change (2^64) with (2^32 * 2^32); nia).
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.
Lemma yswrap32_small : forall x, -2^31 <= x < 2^31 -> bv_swrap 32 x = x.
Proof. intros x Hx. rewrite ybv_swrap32_eq. rewrite Z.mod_small by lia. lia. Qed.

(* [comment removed for export] *)
End RC__1.
Open Scope yprog_scope.
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma dlf_exit : forall f b str len beg e, ~ e < len -> yleaf (ydecode_loop (S f) b str len beg e) (b, beg, e).
Proof. intros. cbn [ydecode_loop]. destruct (Z.ltb_spec e len); [lia| apply yl_ret]. Qed.

Lemma dlf_plain : forall f b str len beg e r, e < len -> znth str e <> c_bslash ->
  yleaf (ydecode_loop f b str len beg (e + 1)) r -> yleaf (ydecode_loop (S f) b str len beg e) r.
Proof.
  intros. cbn [ydecode_loop]. destruct (Z.ltb_spec e len); [| lia].
  destruct (Z.eqb_spec (znth str e) c_bslash); [congruence| assumption].
Qed.

Lemma dlf_esc : forall f b str len beg e u b1 r, e < len -> znth str e = c_bslash -> simple_escape (znth str (e + 1)) = Some u ->
  yleaf (ybuf_append b (zslice str beg (e - beg))) b1 ->
  yleaf (b2 <- ybuf_append b1 [u] ;; ydecode_loop f b2 str len (e + 1 + 1) (e + 1 + 1)) r ->
  yleaf (ydecode_loop (S f) b str len beg e) r.
Proof.
  intros f b str len beg e u b1 r Hlt Hb Hs H1 H2. cbn [ydecode_loop]. destruct (Z.ltb_spec e len); [| lia].
  rewrite Hb. cbn [Z.eqb c_bslash Pos.eqb]. eapply yleaf_bind; [exact H1|]. cbv beta. rewrite Hs. exact H2.
Qed.

(* [comment removed for export] *)
Lemma dlf_u : forall f b str len beg e cp b1 r, e < len -> znth str e = c_bslash -> znth str (e + 1) = c_u ->
  yhexToDigit 0 str (e + 1 + 1) = Some cp -> Z.land cp 64512 <> 55296 ->
  yleaf (ybuf_append b (zslice str beg (e - beg))) b1 ->
  yleaf (b2 <- ybuf_append b1 (if cp =? 0 then [0] else cstr (yUtf32toUtf8 cp)) ;; ydecode_loop f b2 str len (e + 1 + 1 + 3 + 1) (e + 1 + 1 + 3 + 1)) r ->
  yleaf (ydecode_loop (S f) b str len beg e) r.
Proof.
  intros f b str len beg e cp b1 r Hlt Hb Hu Hx Hns H1 H2. cbn [ydecode_loop]. destruct (Z.ltb_spec e len); [| lia].
  rewrite Hb. cbn [Z.eqb c_bslash Pos.eqb]. eapply yleaf_bind; [exact H1|]. cbv beta. rewrite Hu. cbn [simple_escape c_u c_r c_n c_bslash c_slash c_quote c_f c_b c_t Z.eqb Pos.eqb].
  rewrite Hx. destruct (Z.eqb_spec (Z.land cp 64512) 55296); [lia|]. exact H2.
Qed.

(* [comment removed for export] *)
Lemma dlf_us : forall f b str len beg e cp sur b1 r, e < len -> znth str e = c_bslash -> znth str (e + 1) = c_u ->
  yhexToDigit 0 str (e + 1 + 1) = Some cp -> Z.land cp 64512 = 55296 ->
  e + 1 + 1 + 3 + 2 < len -> znth str (e + 1 + 1 + 3 + 1) = c_bslash -> znth str (e + 1 + 1 + 3 + 2) = c_u ->
  yhexToDigit 0 str (e + 1 + 1 + 3 + 1 + 2) = Some sur ->
  yleaf (ybuf_append b (zslice str beg (e - beg))) b1 ->
  yleaf (b2 <- ybuf_append b1 (if combine_surrogate cp sur =? 0 then [0] else cstr (yUtf32toUtf8 (combine_surrogate cp sur))) ;;
         ydecode_loop f b2 str len (e + 1 + 1 + 3 + 1 + 5 + 1) (e + 1 + 1 + 3 + 1 + 5 + 1)) r ->
  yleaf (ydecode_loop (S f) b str len beg e) r.
Proof.
  intros f b str len beg e cp sur b1 r Hlt Hb Hu Hx Hsur Hl2 Hb2 Hu2 Hx2 H1 H2. cbn [ydecode_loop]. destruct (Z.ltb_spec e len); [| lia].
  rewrite Hb. cbn [Z.eqb c_bslash Pos.eqb]. eapply yleaf_bind; [exact H1|]. cbv beta. rewrite Hu. cbn [simple_escape c_u c_r c_n c_bslash c_slash c_quote c_f c_b c_t Z.eqb Pos.eqb].
  rewrite Hx. rewrite Hsur. cbn [Z.eqb Pos.eqb].
  replace (e + 1 + 1 + 3 + 2 <? len) with true by (symmetry; apply Z.ltb_lt; lia). rewrite Hb2, Hu2. cbn [andb Z.eqb c_bslash c_u Pos.eqb]. rewrite Hx2. exact H2.
Qed.

(* [comment removed for export] *)
Lemma dlf_uq : forall f b str len beg e cp b1 r, e < len -> znth str e = c_bslash -> znth str (e + 1) = c_u ->
  yhexToDigit 0 str (e + 1 + 1) = Some cp -> Z.land cp 64512 = 55296 ->
  (e + 1 + 1 + 3 + 2 <? len) && (znth str (e + 1 + 1 + 3 + 1) =? c_bslash) && (znth str (e + 1 + 1 + 3 + 2) =? c_u) = false ->
  yleaf (ybuf_append b (zslice str beg (e - beg))) b1 ->
  yleaf (b2 <- ybuf_append b1 [63] ;; ydecode_loop f b2 str len (e + 1 + 1 + 3 + 1) (e + 1 + 1 + 3 + 1)) r ->
  yleaf (ydecode_loop (S f) b str len beg e) r.
Proof.
  intros f b str len beg e cp b1 r Hlt Hb Hu Hx Hsur Hlook H1 H2. cbn [ydecode_loop]. destruct (Z.ltb_spec e len); [| lia].
  rewrite Hb. cbn [Z.eqb c_bslash Pos.eqb]. eapply yleaf_bind; [exact H1|]. cbv beta. rewrite Hu. cbn [simple_escape c_u c_r c_n c_bslash c_slash c_quote c_f c_b c_t Z.eqb Pos.eqb].
  rewrite Hx. rewrite Hsur. cbn [Z.eqb Pos.eqb]. rewrite Hlook. exact H2.
Qed.

Lemma zbytes_no_nul : forall us, Forall (fun c => 0 <= c < 256) us -> ~ In 0 us -> ~ In (Z_to_bv 8 0) (zbytes us).
Proof.
  intros us HF HN HI. unfold zbytes in HI. apply in_map_iff in HI. destruct HI as (x & HX & HIx).
  apply HN. rewrite Forall_forall in HF. specialize (HF x HIx).
  apply (f_equal bv_unsigned) in HX. rewrite !Z_to_bv_unsigned in HX. unfold bv_wrap, bv_modulus in HX.
  change (2 ^ Z.of_N 8) with 256 in HX. rewrite !Z.mod_small in HX by lia. subst x. exact HIx.
Qed.

Lemma zbytes_nth : forall l i, 0 <= i < zlength l -> nth_error (zbytes l) (Z.to_nat i) = Some (Z_to_bv 8 (znth l i)).
Proof.
  intros l i Hi. unfold zbytes, znth, zlength in *. rewrite nth_error_map.
  destruct (Z.ltb_spec i 0); [lia|].
  destruct (nth_error l (Z.to_nat i)) eqn:E; [| apply nth_error_None in E; lia].
  cbn. f_equal. f_equal. symmetry. apply nth_error_nth. exact E.
Qed.

Lemma lit_bytes : forall m A (l : list Z),
  mem_inv usegs m -> ro_bytes_b usegs A (zbytes l) = true -> 65536 <= A -> A + zlength l <= 2^64 -> bytes_at usegs m A (zbytes l).
Proof.
  intros m A l MI RO LOW HI. apply ro_bytes_at; [exact MI| lia| rewrite zbytes_length; unfold zlength in HI; lia| apply (ro_bytes_b_sound usegs); exact RO].
Qed.

End RC__2.
Ltac forall_bytes := repeat (apply Forall_cons; [split; [apply Z.leb_le| apply Z.ltb_lt]; vm_compute; reflexivity|]); apply Forall_nil.
Ltac not_in_lit := let HI := fresh in intros HI; repeat (destruct HI as [HI|HI]; [clear -HI; lia|]); exact HI.

Section RC__3.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma zb8_unb : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.
Lemma zbytes_unbytes : forall bs : list byte, zbytes (map bv_unsigned bs) = bs.
Proof. intros bs. unfold zbytes. rewrite map_map. induction bs as [|b bs IH]; [reflexivity|]. cbn [map]. rewrite IH. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.
Lemma Forall_unbytes : forall bs : list byte, Forall (fun c => 0 <= c < 256) (map bv_unsigned bs).
Proof.
  intros bs. apply Forall_forall. intros x Hx. apply in_map_iff in Hx. destruct Hx as (b & <- & _).
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.

(* [comment removed for export] *)
Lemma land_shiftl_high : forall a b k, 0 <= a < 2^k -> 0 <= b -> 0 <= k -> Z.land a (Z.shiftl b k) = 0.
Proof.
  intros a b k Ha Hb Hk. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.ltb_spec n k).
  - rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
  - rewrite <- (Z.mod_small a (2^k)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma lor_disjoint_add : forall a b, 0 <= a -> 0 <= b -> Z.land a b = 0 -> Z.lor a b = a + b.
Proof. intros a b Ha Hb H. rewrite <- Z.lxor_lor by exact H. symmetry. apply Z.add_nocarry_lxor. exact H. Qed.
Lemma land63_128 : forall a, 0 <= a -> Z.land (Z.land a 63) 128 = 0.
Proof. intros a Ha. change 128 with (Z.shiftl 1 7). apply land_shiftl_high; [| lia| lia]. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. split; [apply Z.mod_pos_bound; lia|]. pose proof (Z.mod_pos_bound a (2^6) ltac:(lia)). lia. Qed.
Lemma lor63_128 : forall a, 0 <= a -> Z.lor (Z.land a 63) 128 = Z.land a 63 + 128.
Proof. intros a Ha. apply lor_disjoint_add; [apply Z.land_nonneg; lia| lia| apply land63_128; lia]. Qed.
Lemma land63_range : forall a, 0 <= a -> 0 <= Z.land a 63 < 64.
Proof. intros a Ha. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound a (2^6) ltac:(lia)). lia. Qed.

Lemma land_lt_pow2 : forall a b n, 0 <= a -> 0 <= b < 2 ^ n -> 0 < n -> 0 <= Z.land a b < 2 ^ n.
Proof.
  intros a b n Ha Hb Hn. pose proof (proj2 (Z.land_nonneg a b) (or_introl Ha)) as H0. split; [exact H0|].
  destruct (Z.eq_dec (Z.land a b) 0) as [E|NZ]; [rewrite E; apply Z.pow_pos_nonneg; lia|].
  apply (proj2 (Z.log2_lt_pow2 (Z.land a b) n ltac:(lia))).
  pose proof (Z.log2_land a b Ha ltac:(lia)) as HL.
  destruct (Z.eq_dec b 0) as [->|NB]; [rewrite Z.land_0_r in NZ; lia|].
  pose proof (proj1 (Z.log2_lt_pow2 b n ltac:(lia)) ltac:(lia)). lia.
Qed.
Lemma land_lt16 : forall a, 0 <= a -> 0 <= Z.land a 64512 < 65536.
Proof. intros a Ha. apply (land_lt_pow2 a 64512 16); lia. Qed.

Lemma cstr_id : forall l, Forall (fun c => c <> 0) l -> cstr l = l.
Proof. induction l as [|c l IH]; intros H; [reflexivity|]. inversion H; subst. cbn. destruct (Z.eqb_spec c 0); [lia|]. rewrite IH; auto. Qed.

Definition u8enc (cp : Z) : list Z := if cp =? 0 then [0] else cstr (yUtf32toUtf8 cp).

Lemma u8enc_1 : forall cp, 0 < cp < 128 -> u8enc cp = [cp].
Proof. intros cp H. unfold u8enc, yUtf32toUtf8. destruct (Z.eqb_spec cp 0); [lia|]. destruct (Z.ltb_spec cp 128); [| lia]. cbn. destruct (Z.eqb_spec cp 0); [lia| reflexivity]. Qed.

Lemma u8enc_2 : forall cp, 128 <= cp < 2048 ->
  u8enc cp = [Z.shiftr cp 6 + 192; Z.land cp 63 + 128] /\ 192 <= Z.shiftr cp 6 + 192 < 224 /\ 128 <= Z.land cp 63 + 128 < 192.
Proof.
  intros cp H. pose proof (land63_range cp ltac:(lia)) as R1.
  assert (R2 : 0 <= Z.shiftr cp 6 < 32) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  assert (E1 : Z.lor (Z.shiftr cp 6) 192 = Z.shiftr cp 6 + 192).
  { apply lor_disjoint_add; [lia| lia|]. change 192 with (Z.shiftl 3 6). apply land_shiftl_high; lia. }
  unfold u8enc, yUtf32toUtf8. destruct (Z.eqb_spec cp 0); [lia|]. destruct (Z.ltb_spec cp 128); [lia|]. destruct (Z.ltb_spec cp 2048); [| lia].
  rewrite E1, lor63_128 by lia. split; [| lia]. apply cstr_id. repeat constructor; lia.
Qed.

Lemma shiftr_range : forall a k b, 0 <= a < 2^b -> 0 <= k <= b -> 0 <= Z.shiftr a k < 2^(b - k).
Proof.
  intros a k b Ha Hk. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. replace (k + (b - k)) with b by lia. lia.
Qed.

Lemma u8enc_3 : forall cp, 2048 <= cp < 65536 ->
  u8enc cp = [Z.shiftr cp 12 + 224; Z.land (Z.shiftr cp 6) 63 + 128; Z.land cp 63 + 128]
  /\ 224 <= Z.shiftr cp 12 + 224 < 240 /\ 128 <= Z.land (Z.shiftr cp 6) 63 + 128 < 192 /\ 128 <= Z.land cp 63 + 128 < 192.
Proof.
  intros cp H. pose proof (land63_range cp ltac:(lia)) as R1. pose proof (land63_range (Z.shiftr cp 6) ltac:(apply Z.shiftr_nonneg; lia)) as R2.
  pose proof (shiftr_range cp 12 16 ltac:(lia) ltac:(lia)) as R3. change (2 ^ (16 - 12)) with 16 in R3.
  assert (E1 : Z.lor (Z.shiftr cp 12) 224 = Z.shiftr cp 12 + 224).
  { apply lor_disjoint_add; [lia| lia|]. change 224 with (Z.shiftl 7 5). apply land_shiftl_high; lia. }
  unfold u8enc, yUtf32toUtf8. destruct (Z.eqb_spec cp 0); [lia|]. destruct (Z.ltb_spec cp 128); [lia|]. destruct (Z.ltb_spec cp 2048); [lia|].
  destruct (Z.ltb_spec cp 65536); [| lia].
  rewrite E1, !lor63_128 by (try apply Z.shiftr_nonneg; lia). split; [| lia]. apply cstr_id. repeat constructor; lia.
Qed.

Lemma u8enc_4 : forall cp, 65536 <= cp < 2097152 ->
  u8enc cp = [Z.shiftr cp 18 + 240; Z.land (Z.shiftr cp 12) 63 + 128; Z.land (Z.shiftr cp 6) 63 + 128; Z.land cp 63 + 128]
  /\ 240 <= Z.shiftr cp 18 + 240 < 248 /\ 128 <= Z.land (Z.shiftr cp 12) 63 + 128 < 192
  /\ 128 <= Z.land (Z.shiftr cp 6) 63 + 128 < 192 /\ 128 <= Z.land cp 63 + 128 < 192.
Proof.
  intros cp H. pose proof (land63_range cp ltac:(lia)) as R1. pose proof (land63_range (Z.shiftr cp 6) ltac:(apply Z.shiftr_nonneg; lia)) as R2.
  pose proof (land63_range (Z.shiftr cp 12) ltac:(apply Z.shiftr_nonneg; lia)) as R2'.
  pose proof (shiftr_range cp 18 21 ltac:(lia) ltac:(lia)) as R3. change (2 ^ (21 - 18)) with 8 in R3.
  assert (E1 : Z.lor (Z.shiftr cp 18) 240 = Z.shiftr cp 18 + 240).
  { apply lor_disjoint_add; [lia| lia|]. change 240 with (Z.shiftl 15 4). apply land_shiftl_high; lia. }
  unfold u8enc, yUtf32toUtf8. destruct (Z.eqb_spec cp 0); [lia|]. destruct (Z.ltb_spec cp 128); [lia|]. destruct (Z.ltb_spec cp 2048); [lia|].
  destruct (Z.ltb_spec cp 65536); [lia|]. destruct (Z.ltb_spec cp 2097152); [| lia].
  rewrite E1, !lor63_128 by (try apply Z.shiftr_nonneg; lia). split; [| lia]. apply cstr_id. repeat constructor; lia.
Qed.

(* [comment removed for export] *)
Lemma bits6_52 : forall x, 0 <= x -> (x * 2^52) mod 2^64 / 2^58 = Z.land (Z.shiftr x 6) 63.
Proof.
  intros x Hx. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, Z.shiftr_spec by lia.
  rewrite <- (Z.shiftr_div_pow2 _ 58) by lia. rewrite Z.shiftr_spec by lia.
  rewrite <- Z.land_ones by lia. rewrite Z.land_spec.
  rewrite <- (Z.shiftl_mul_pow2 _ 52) by lia.
  destruct (Z.ltb_spec n 6).
  - rewrite Z.shiftl_spec_high by lia. rewrite Z.ones_spec_low by lia.
    change 63 with (Z.ones 6). rewrite Z.ones_spec_low by lia. rewrite !andb_true_r. f_equal. lia.
  - rewrite (Z.ones_spec_high 64) by lia. change 63 with (Z.ones 6). rewrite (Z.ones_spec_high 6) by lia.
    rewrite !andb_false_r. reflexivity.
Qed.
Lemma bits12_46 : forall x, 0 <= x -> (x * 2^46) mod 2^64 / 2^58 = Z.land (Z.shiftr x 12) 63.
Proof.
  intros x Hx. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, Z.shiftr_spec by lia.
  rewrite <- (Z.shiftr_div_pow2 _ 58) by lia. rewrite Z.shiftr_spec by lia.
  rewrite <- Z.land_ones by lia. rewrite Z.land_spec.
  rewrite <- (Z.shiftl_mul_pow2 _ 46) by lia.
  destruct (Z.ltb_spec n 6).
  - rewrite Z.shiftl_spec_high by lia. rewrite Z.ones_spec_low by lia.
    change 63 with (Z.ones 6). rewrite Z.ones_spec_low by lia. rewrite !andb_true_r. f_equal. lia.
  - rewrite (Z.ones_spec_high 64) by lia. change 63 with (Z.ones 6). rewrite (Z.ones_spec_high 6) by lia.
    rewrite !andb_false_r. reflexivity.
Qed.

Lemma yfield6 : forall cp, 0 <= cp < 2^64 -> bv_unsigned (Z_to_bv 64 (cp ≪ 52)) ≫ 58 = Z.land (cp ≫ 6) 63.
Proof.
  intros cp H. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. apply bits6_52. lia.
Qed.
Lemma yfield12 : forall cp, 0 <= cp < 2^64 -> bv_unsigned (Z_to_bv 64 (cp ≪ 46)) ≫ 58 = Z.land (cp ≫ 12) 63.
Proof.
  intros cp H. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. apply bits12_46. lia.
Qed.
Lemma lead2 : forall cp, 128 <= cp < 2048 -> Z.lor (Z.shiftr cp 6) 192 = Z.shiftr cp 6 + 192.
Proof.
  intros cp H. pose proof (shiftr_range cp 6 11 ltac:(lia) ltac:(lia)) as R. change (2 ^ (11 - 6)) with 32 in R.
  apply lor_disjoint_add; [lia| lia|]. change 192 with (Z.shiftl 3 6). apply land_shiftl_high; lia.
Qed.
Lemma lead3 : forall cp, 2048 <= cp < 65536 -> Z.lor (Z.shiftr cp 12) 224 = Z.shiftr cp 12 + 224.
Proof.
  intros cp H. pose proof (shiftr_range cp 12 16 ltac:(lia) ltac:(lia)) as R. change (2 ^ (16 - 12)) with 16 in R.
  apply lor_disjoint_add; [lia| lia|]. change 224 with (Z.shiftl 7 5). apply land_shiftl_high; lia.
Qed.
Lemma lead4 : forall cp, 65536 <= cp < 2097152 -> Z.lor (Z.shiftr cp 18) 240 = Z.shiftr cp 18 + 240.
Proof.
  intros cp H. pose proof (shiftr_range cp 18 21 ltac:(lia) ltac:(lia)) as R. change (2 ^ (21 - 18)) with 8 in R.
  apply lor_disjoint_add; [lia| lia|]. change 240 with (Z.shiftl 15 4). apply land_shiftl_high; lia.
Qed.

Lemma skipn_S_tl : forall {A} n (l : list A), skipn (Datatypes.S n) l = skipn 1 (skipn n l).
Proof. intros A n l. revert n. induction l as [|a l IH]; intros n; [destruct n; reflexivity|]. destruct n as [|n]; [reflexivity|]. rewrite skipn_cons, IH. reflexivity. Qed.
Lemma zslice_cons : forall l i k, 0 <= i -> i < zlength l -> 0 < k -> zslice l i k = znth l i :: zslice l (i + 1) (k - 1).
Proof.
  intros l i k Hi Hl Hk. unfold zslice, znth, zlength in *.
  destruct (Z.ltb_spec i 0); [lia|].
  replace (Z.to_nat (i + 1)) with (Datatypes.S (Z.to_nat i)) by lia.
  replace (Z.to_nat k) with (Datatypes.S (Z.to_nat (k - 1))) by lia.
  rewrite skipn_S_tl.
  destruct (skipn (Z.to_nat i) l) as [|x t] eqn:E.
  - exfalso. apply (f_equal (@length Z)) in E. rewrite length_skipn in E. cbn in E. lia.
  - cbn [firstn skipn]. f_equal. assert (N : nth 0 (skipn (Z.to_nat i) l) 0 = nth (Z.to_nat i + 0)%nat l 0) by apply nth_skipn. rewrite E, Nat.add_0_r in N. cbn in N. exact N.
Qed.
Lemma zslice4 : forall l i, 0 <= i -> i + 4 <= zlength l ->
  zslice l i 4 = [znth l i; znth l (i + 1); znth l (i + 2); znth l (i + 3)].
Proof.
  intros l i Hi Hl. rewrite (zslice_cons l i 4) by lia. rewrite (zslice_cons l (i + 1) (4 - 1)) by lia.
  rewrite (zslice_cons l (i + 1 + 1) (4 - 1 - 1)) by lia. rewrite (zslice_cons l (i + 1 + 1 + 1) (4 - 1 - 1 - 1)) by lia.
  rewrite zslice_nil_len by lia.
  replace (i + 1 + 1) with (i + 2) by lia. replace (i + 2 + 1) with (i + 3) by lia. reflexivity.
Qed.

Section S.
Variable HK : RawAlloc.PState -> list block -> (word -> option byte) -> Model -> Prop.
Hypothesis HKS : HK_silent_stmt HK.
Hypothesis HKP : HK_perm_stmt HK.
Hypothesis HKF : HK_frame_stmt HK.
Hypothesis HKB : HK_blocks_stmt HK.
Hypothesis YAP : ybuf_append_stmt HK.
Hypothesis YHX : yhexToDigit_stmt.

Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia; rewrite ?signed_of_Z by lia;
  try (change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia); lia.
Ltac lkr := repeat match goal with H : LKnil ?l |- _ => unfold LKnil in H end; rewrite ?app_nil_r; repeat match goal with H : ?l = [] |- context [?l] => rewrite H end; cbn [app].
Ltac lk0 := lkr; reflexivity.
(* [comment removed for export] *)
Ltac sb_store := unfold wz; rewrite le1_wz by lia; mem_after_store.
Ltac zle := apply Z.leb_le; vm_compute; reflexivity.
Ltac lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       end).

Section Fn.
Variables (REST : list block) (mbd : mbuf) (db : ybuf) (AF S : Z) (str : list Z) (n lo B : Z) (errv : word) (K : TSet).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
Hypothesis CONT : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : PState)
    (db' : ybuf) (mbd' : mbuf) (LK : list block),
  ystring_decode_rpost HK sp tp m REST mbd db AF S str n lo B errv a0' m' mo' s' db' mbd' LK ->
  realizes_cfg acfg usegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                           F (ret_pc ra) fc None m' (seg_rom usegs)) mo') K.
Hypothesis K0 : K [].
Hypothesis TP : tp = wz RATP.
Hypothesis CEIL : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RY_DECODE_STACK.
Hypothesis SPB : bv_unsigned sp <= B.
Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
Hypothesis AFIN : yaf_in REST AF.
Hypothesis YR : yroom REST 3.
Hypothesis SF : Forall (fun c => 0 <= c < 256) str.
Hypothesis NL : n = zlength str.
Hypothesis N26 : n < 2^26.
Hypothesis SNZ : S <> 0.
Hypothesis S62 : S + n < 2^62.
Hypothesis TR : (exists bt, In bt REST /\ blk_addr bt <= S /\ S + n <= blk_addr bt + blk_size bt) \/ n = 0.
Hypothesis STXT : 0 < n -> S + n <= alloc_ceiling.
Hypothesis AFC : AF + 32 <= alloc_ceiling.
Hypothesis UAA : 0 < mb_addr mbd /\ mb_addr mbd mod 8 = 0 /\ 0 < AF /\ AF mod 8 = 0 /\ bv_unsigned sp mod 16 = 0.

(* [comment removed for export] *)
Definition dlits : list cell :=
  [C8 (wz 1047552); C8 (wz 55296); C8 (wz 66968); C8 (wz 67197); C8 (wz 67844); C8 (wz 67191);
   C8 (wz 66539); C8 (wz 66422); C8 (wz 67239); C8 (wz 66269)].
(* [comment removed for export] *)
Definition dframe (j0 j88 : list byte) : list cell :=
  CB 8 j0 :: dlits ++ [CB 16 j88; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Lemma str_pres : forall LB SPx ma mb,
  ry_pres LB SPx [] ma mb -> (forall b, In b REST -> In b LB) ->
  bytes_at usegs ma S (zbytes str) -> bytes_at usegs mb S (zbytes str).
Proof.
  intros LB SPx ma mb HP HI TB. destruct TR as [(bt & HBT & T1 & T2)|N0].
  - eapply bytes_at_agree; [apply ry_pres_agree; exact HP| exact TB|]. rewrite zbytes_length. intros a Ha.
    split; [| intros []]. right; right. exists bt. split; [apply HI; exact HBT| unfold zlength in NL; lia].
  - assert (str = []) as -> by (destruct str; [reflexivity| unfold zlength in *; cbn in *; lia]).
    destruct TB as (B0 & B1 & _). split; [exact B0|]. split; [exact B1|]. intros i Hi. cbn in Hi. lia.
Qed.

Lemma str_pres_munch : forall W ma mb,
  munch W ma mb -> Forall (fun iv : Z * Z => alloc_ceiling <= fst iv) W ->
  bytes_at usegs ma S (zbytes str) -> bytes_at usegs mb S (zbytes str).
Proof.
  intros W ma mb MU HW TB. destruct str as [|c str'] eqn:ES.
  - destruct TB as (B0 & B1 & _). split; [exact B0|]. split; [exact B1|]. intros i Hi. cbn in Hi. lia.
  - eapply (bytes_at_transport usegs); [exact TB| exact MU|]. rewrite zbytes_length.
    assert (NP : 0 < n) by (rewrite NL; unfold zlength; cbn; lia). specialize (STXT NP). rewrite NL in STXT. unfold zlength in STXT.
    apply disjoint_from_above. eapply Forall_impl; [| exact HW]. cbv beta. intros iv Hiv. unfold alloc_ceiling in *. lia.
Qed.

(* [comment removed for export] *)
Definition dsaved : list cell := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
(* [comment removed for export] *)
Definition dblob (j0 j88 : list byte) : list byte := cells_bytes (CB 8 j0 :: dlits ++ [CB 16 j88]).
Lemma dframe_blob : forall mx j0 j88,
  rw_cells usegs mx (bv_unsigned sp + -208) (dframe j0 j88) -> rw_cells usegs mx (bv_unsigned sp + -208) (CB 104 (dblob j0 j88) :: dsaved).
Proof.
  intros mx j0 j88 FR. unfold dframe in FR.
  change (CB 8 j0 :: dlits ++ CB 16 j88 :: ?sv) with ([] ++ (CB 8 j0 :: dlits ++ [CB 16 j88]) ++ dsaved) in FR.
  pose proof (rw_cells_merge usegs mx _ [] (CB 8 j0 :: dlits ++ [CB 16 j88]) dsaved FR) as J.
  cbn [cells_size csize Nat.add app dlits] in J. exact J.
Qed.

(* [comment removed for export] *)
Lemma str_read : forall mx i, bytes_at usegs mx S (zbytes str) -> 0 <= i < n ->
  ov_read_bytes usegs mx (wa (S + i)) 1 = Some [Z_to_bv 8 (znth str i)].
Proof. intros mx i TB Hi. eapply (u8ro_read usegs); [exact TB| apply zbytes_nth; lia| lia| reflexivity]. Qed.

Lemma str_byte : forall i, 0 <= i < n -> 0 <= znth str i < 256.
Proof.
  intros i Hi. unfold znth. destruct (Z.ltb_spec i 0); [lia|]. rewrite Forall_forall in SF.
  destruct (nth_error str (Z.to_nat i)) eqn:E; [| apply nth_error_None in E; unfold zlength in NL; lia].
  rewrite (nth_error_nth _ _ _ E). apply SF. eapply nth_error_In. exact E.
Qed.


(* [comment removed for export] *)
Lemma ua_append : forall mb b Sx src lox Bx ev spx, mb_same mbd mb -> 0 < Sx ->
  UA_ybuf_append REST mb b AF Sx src lox Bx ev spx.
Proof.
  intros mb b Sx src lox Bx ev spx [M1 M2] HS. destruct UAA as (U1 & U2 & U3 & U4 & _).
  unfold UA_ybuf_append. rewrite M2. repeat split; assumption.
Qed.
Lemma ua_append' : forall LKx mb b Sx src lox Bx ev spx, mb_same mbd mb -> 0 < Sx ->
  UA_ybuf_append (LKx ++ REST) mb b AF Sx src lox Bx ev spx.
Proof.
  intros LKx mb b Sx src lox Bx ev spx [M1 M2] HS. destruct UAA as (U1 & U2 & U3 & U4 & _).
  unfold UA_ybuf_append. rewrite M2. repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma decode_exit : forall (s2v s3v s4v s5v s6v s7v s8v s11v rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m1 : mem) (mo1 : Model) (s1' : PState) (errv1 : word) (b : ybuf) (mb : mbuf) (LK : list block) (beg' e' : Z) (junk : list byte),
  LK = [] -> HK s1' (buf_blocks mb b ++ LK ++ REST) m1 mo1 -> ystatics m1 ->
  rw_cells usegs m1 (bv_unsigned sp + -208) (CB 104 junk :: dsaved) -> stk usegs m1 lo (bv_unsigned sp + -208) -> mem_inv usegs m1 -> rauxv_ok m1 B ->
  rw_cells usegs m1 RERRNO [C4 errv1] ->
  ry_pres REST (bv_unsigned sp) [] m m1 ->
  rw_cells usegs m1 AF (alloc_cells ryc) ->
  bytes_at usegs m1 S (zbytes str) ->
  buf_rep usegs m1 mb b AF -> buf_inv b -> mb_same mbd mb -> yb_used b <= beg' ->
  0 <= beg' <= e' -> e' <= n ->
  (forall bf, yleaf (ybuf_append b (zslice str beg' (e' - beg'))) bf -> yleaf (ystring_decode db str n) bf) ->
  realizes_cfg acfg usegs (mkCfg (MS (mkR rav (wz (bv_unsigned sp + -208)) gp tp t0 t1 t2 (wz (mb_addr mb)) (wz S) a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v (wz beg') (wz e') s11v t3 t4 t5 t6)
                           F (wz 0x17554) fc None m1 (seg_rom usegs)) mo1) K.
Proof.
  intros until junk. intros ELK HK1 YS1 FR STK MI AX ERR PRES YAF TB BR BI MBS UB HBE HEN HL. apply lk_hide in ELK.
  unfold dsaved, wz in *. pose proof LO as LO'. unfold RY_DECODE_STACK, RY_BUF_APPEND_STACK, RY_WRAP_STACK, alloc_ceiling in LO'.
  pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
  unfold RERRNO in ERR. pose proof (zlength_nonneg str) as NL0. pose proof (proj1 TB) as S0.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -208)) = bv_unsigned sp + -208) by (apply unsigned_lit; lia).
  pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl usegs m1) as WM.
  rz_seg HKS HK1.
  step. step. step. rewrite (yzext32_idiom beg') by lia.
  step. if_cases G1; zify_cond G1. 1:{ kill G1. }
  step. step. step. step. if_cases G2; zify_cond G2.
  1:{ exfalso. revert G2. rewrite ?(unsigned_lit S) by lia. replace (0 <? S) with true by (symmetry; apply Z.ltb_lt; lia).
      replace (S + beg' <? 1) with false by (symmetry; apply Z.ltb_ge; lia). intros E; cbv in E; discriminate. }
  step. rewrite (unsigned_lit e'), (unsigned_lit beg') by lia. rewrite yswrap32_small by lia.
  step. step.
  apply evt_done. clear MU WM G1 G2.
  pose proof (zslice_length str beg' (e' - beg') ltac:(lia) ltac:(lia) ltac:(lia)) as ZL.
  destruct AFIN as (hb & HBI & HB1 & HB2).
  eapply (YAP (LK ++ REST) mb b AF (S + beg') (zslice str beg' (e' - beg')) lo B errv1 K);
    [ exact K0 | apply ua_append'; [exact MBS| lia] | apply RYST_split; split; [exact HK1| exact YS1] | exact BR | exact BI | exact YAF
    | exists hb; split; [apply in_or_app; right; exact HBI| lia]
    | apply bytes_at_zslice; [exact TB| lia]
    | apply Forall_zslice; exact SF
    | pose proof (proj1 TB); lia
    | rewrite ZL; lia
    | rewrite ZL; lia
    | rewrite ZL; destruct TR as [(bt & HBT & T1 & T2)|N0]; [left; exists bt; split; [apply in_or_app; right; exact HBT| lia]| right; right; right; lia]
    | lkr; exact YR
      | split; [exact AX|]; split; [rewrite ESP; lia|]; split; [rewrite ESP; exact STK|]; split; [exact CEIL|];
      split; [rewrite ESP; unfold RY_BUF_APPEND_STACK, RY_WRAP_STACK; lia|]; split; [rewrite (ry_errno_lit tp TP); exact ERR|]; split; [exact MI| exact TP]
    | reflexivity | reflexivity | rewrite ZL; reflexivity | ].
  cbv beta. intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 mo2 s2' b' mb' LK' POST.
  destruct POST as ((MI2 & STK2 & (errv2 & ERR2) & AX2 & HP2) & YAF2 & HLB & BR2 & MBS2 & LKE2 & RY2). apply lk_hide in LKE2.
  replace (ret_pc (Z_to_bv 64 95616)) with (Z_to_bv 64 95616) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  rewrite ESP in STK2, HP2. rewrite (ry_errno_lit tp TP) in ERR2. unfold RERRNO in ERR2.
  pose proof (str_pres _ _ _ _ HP2 ltac:(intros b0 Hb0; apply in_or_app; right; exact Hb0) TB) as TB2.
  apply ry_pres_nil in HP2. apply RYST_split in RY2. destruct RY2 as [HK2 YS2].
  pose proof (ypres_frame _ _ _ _ _ _ HP2 FR ltac:(lia)) as FR2. clear FR.
  assert (PRES2 : ry_pres REST (bv_unsigned sp) [] m m2).
  { eapply ry_pres_trans; [exact PRES|]. apply ry_pres_of_rheap_pres. eapply rheap_pres_weaken; [exact HP2| lia| intros b0 Hb0; apply in_or_app; right; exact Hb0]. }
  clear HP2 MI STK ERR AX HK1 YS1 PRES TB.
  pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
  rz_seg HKS HK2.
  step. step. step. step. step. step. step. step. step. step. step. step. step. step. step.
  apply evt_done. release_frame FR2 STK2 (bv_unsigned sp).
  eapply CONT with (LK := LK' ++ LK). unfold ystring_decode_rpost.
  split; [| split; [exact YAF2| split; [apply HL; exact HLB| split; [exact BR2| split; [| split; [exact TB2| split; [lk0|]]]]]]].
  - split; [exact MI2|]. split; [exact STK2|]. split; [exists errv2; rewrite (ry_errno_lit tp TP); exact ERR2|]. split; [exact AX2| exact PRES2].
  - destruct MBS as [M1 M2]. destruct MBS2 as [M3 M4]. split; congruence.
  - apply RYST_split. split; [| exact YS2]. rewrite <- app_assoc. exact HK2.
Qed.

Let WHOLE := ydecode_loop (decode_fuel n) db str n 0 0.

Lemma exit_leaf : forall b' beg' e', yleaf WHOLE (b', beg', e') ->
  forall bf, yleaf (ybuf_append b' (zslice str beg' (e' - beg'))) bf -> yleaf (ystring_decode db str n) bf.
Proof. intros b' beg' e' HW bf HA. unfold ystring_decode. eapply yleaf_bind; [exact HW|]. cbv beta iota. exact HA. Qed.

(* [comment removed for export] *)
Definition nS : Z := 18446744073709551615 - S.

(* [comment removed for export] *)
Definition head_ok (f : nat) : Prop :=
  forall (rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3v t3 t4 t5 t6 : word)
    (m1 : mem) (mo1 : Model) (s1' : PState) (errv1 : word) (b : ybuf) (mb : mbuf) (LK : list block) (beg e : Z) (j0 j88 : list byte),
  LK = [] -> HK s1' (buf_blocks mb b ++ LK ++ REST) m1 mo1 -> ystatics m1 ->
  rw_cells usegs m1 (bv_unsigned sp + -208) (dframe j0 j88) -> stk usegs m1 lo (bv_unsigned sp + -208) -> mem_inv usegs m1 -> rauxv_ok m1 B ->
  rw_cells usegs m1 RERRNO [C4 errv1] ->
  ry_pres REST (bv_unsigned sp) [] m m1 ->
  rw_cells usegs m1 AF (alloc_cells ryc) ->
  bytes_at usegs m1 S (zbytes str) ->
  buf_rep usegs m1 mb b AF -> buf_inv b -> mb_same mbd mb -> yb_used b <= beg ->
  0 <= beg <= e -> e < n -> sbody_ix str e n -> (Z.to_nat (n - e) < f)%nat ->
  (forall r, yleaf (ydecode_loop f b str n beg e) r -> yleaf WHOLE r) ->
  realizes_cfg acfg usegs (mkCfg (MS (mkR rav (wz (bv_unsigned sp + -208)) gp tp t0 t1 t2 (wz (mb_addr mb)) (wz S) a0 a1 a2 a3 a4 a5 a6 a7 (wz n) s3v (wz 64512) (wz nS) (wz 1) (wz 92) (wz 101) (wz beg) (wz e) (wz 113) t3 t4 t5 t6)
                           F (wz 0x17208) fc None m1 (seg_rom usegs)) mo1) K.

(* [comment removed for export] *)
Lemma decode_lit : forall f', head_ok f' ->
  forall (rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10v t3 t4 t5 t6 : word)
    (m1 : mem) (mo1 : Model) (s1' : PState) (errv1 : word) (b1 : ybuf) (mb1 : mbuf) (LK : list block) (p U : Z) (us slk : list Z) (j0 j88 : list byte),
  LK = [] -> HK s1' (buf_blocks mb1 b1 ++ LK ++ REST) m1 mo1 -> ystatics m1 ->
  rw_cells usegs m1 (bv_unsigned sp + -208) (dframe j0 j88) -> stk usegs m1 lo (bv_unsigned sp + -208) -> mem_inv usegs m1 -> rauxv_ok m1 B ->
  rw_cells usegs m1 RERRNO [C4 errv1] ->
  ry_pres REST (bv_unsigned sp) [] m m1 ->
  rw_cells usegs m1 AF (alloc_cells ryc) ->
  bytes_at usegs m1 S (zbytes str) ->
  buf_rep usegs m1 mb1 b1 AF -> buf_inv b1 -> mb_same mbd mb1 ->
  bytes_at usegs m1 U (zbytes (us ++ 0 :: slk)) -> Forall (fun c => 0 <= c < 256) (us ++ 0 :: slk) -> ~ In 0 us -> (1 <= length us <= 4)%nat ->
  (- (U + zlength us + 1)) mod 8 <= zlength slk -> U <> 0 ->
  ((65536 <= U /\ U + zlength us <= 77824) \/ bv_unsigned sp + -208 <= U) ->
  yb_used b1 + zlength us <= p + 1 -> 0 <= p -> p + 1 <= n -> sbody_ix str (p + 1) n -> (Z.to_nat (n - p) <= f')%nat ->
  (forall r, yleaf (b2 <- ybuf_append b1 us ;; ydecode_loop f' b2 str n (p + 1) (p + 1)) r -> yleaf WHOLE r) ->
  realizes_cfg acfg usegs (mkCfg (MS (mkR rav (wz (bv_unsigned sp + -208)) gp tp t0 t1 t2 (wz (mb_addr mb1)) (wz S) a0 a1 a2 a3 a4 a5 a6 a7 (wz n) (wz U) (wz 64512) (wz nS) (wz 1) (wz 92) (wz 101) (wz p) s10v (wz 113) t3 t4 t5 t6)
                           F (wz 0x17524) fc None m1 (seg_rom usegs)) mo1) K.
Proof.
  intros f' HEAD. intros until j88. intros ELK HK1 YS1 FR STK MI AX ERR PRES YAF TB BR BI MBS UB UF UN UL USL UNZ URG HUSED P0 PN SBP HF HL. apply lk_hide in ELK.
  unfold nS, wz in *. pose proof LO as LO'. unfold RY_DECODE_STACK, RY_BUF_APPEND_STACK, RY_WRAP_STACK, alloc_ceiling in LO'.
  pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
  unfold RERRNO in ERR. pose proof (zlength_nonneg str) as NL0.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -208)) = bv_unsigned sp + -208) by (apply unsigned_lit; lia).
  pose proof (bytes_at_bound _ _ _ _ UB) as UBB0. rewrite zbytes_length, length_app in UBB0. cbn [length] in UBB0.
  assert (UU : bv_unsigned (Z_to_bv 64 U) = U) by (apply unsigned_lit; lia).
  destruct (proj1 (Forall_app _ us (0 :: slk)) UF) as [UF1 UF2].
  assert (ZLU : zlength us <= 4) by (unfold zlength; lia). assert (ZLU1 : 1 <= zlength us) by (unfold zlength; lia).
  rewrite zbytes_app in UB. cbn [zbytes map app] in UB. change (map (Z_to_bv 8) slk) with (zbytes slk) in UB.
  destruct AFIN as (hb & HBI & HB1 & HB2).
  pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl usegs m1) as WM.
  rz_seg HKS HK1.
  step. step. call strlen_spec.
  1:{ rewrite UU. exact UB. }
  1:{ apply zbytes_no_nul; assumption. }
  1:{ rewrite UU, !zbytes_length. unfold zlength in USL. exact USL. }
  1:{ assumption. }
  rewrite UU in POST. rewrite zbytes_length. change (Z.of_nat (length us)) with (zlength us).
  lazymatch goal with H : bytes_at _ ?mx U _ |- _ => rename mx into m1' end.
  lazymatch goal with H : mem_inv _ m1' |- _ => rename H into MI1 end.
  step. rewrite (unsigned_lit (zlength us)) by lia. rewrite Z.add_0_r, yswrap32_small by lia.
  step. step. step.
  apply evt_done.
  pose proof (proj1 (proj1 (bytes_at_app _ _ _ _ _) POST)) as UB1. clear POST.
  assert (BR1 : buf_rep usegs m1' mb1 b1 AF) by (eapply buf_rep_transport; [exact BR| exact MU| exact WM| exact I| intros _; exact I]).
  assert (TB1 : bytes_at usegs m1' S (zbytes str)) by (first [exact TB| eapply (bytes_at_transport usegs); [exact TB| exact MU| exact I]]).
  destruct (yown_writes HK HKF _ _ _ _ _ _ B HK1 AX MU WM ltac:(constructor) ltac:(constructor)) as [HK2 AX2].
  pose proof (ystatics_munch _ _ _ YS1 MU WM ltac:(constructor)) as YS2.
  assert (PRES2 : ry_pres REST (bv_unsigned sp) [] m m1').
  { eapply ry_pres_trans; [exact PRES|]. eapply ryajl_pres_of_munch; [exact MU| exact WM|]. intros a _ _ _. exact I. }
  clear MU WM BR TB HK1 YS1 AX PRES.
  eapply (YAP (LK ++ REST) mb1 b1 AF U us lo B errv1 K);
    [ exact K0 | apply ua_append'; [exact MBS| lia] | apply RYST_split; split; [exact HK2| exact YS2] | exact BR1 | exact BI | exact YAF
    | exists hb; split; [apply in_or_app; right; exact HBI| lia]
    | exact UB1 | exact UF1 | intros _; exact UNZ | pose proof (bytes_at_bound _ _ _ _ UB1) as UBB; rewrite zbytes_length in UBB; unfold zlength; lia | lia
    | destruct URG as [UR|UR]; [right; left; lia| right; right; left; rewrite ESP; lia]
    | lkr; exact YR
      | split; [exact AX2|]; split; [rewrite ESP; lia|]; split; [rewrite ESP; exact STK|]; split; [exact CEIL|];
      split; [rewrite ESP; unfold RY_BUF_APPEND_STACK, RY_WRAP_STACK; lia|]; split; [rewrite (ry_errno_lit tp TP); exact ERR|]; split; [exact MI1| exact TP]
    | reflexivity | reflexivity | reflexivity | ].
  cbv beta. intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 mo2 s2' b2 mb2 LK2 POST.
  destruct POST as ((MI2 & STK2 & (errv2 & ERR2) & AX3 & HP2) & YAF2 & HLB & BR2 & MBS2 & LKE2 & RY2). apply lk_hide in LKE2.
  replace (ret_pc (Z_to_bv 64 95548)) with (Z_to_bv 64 95548) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  rewrite ESP in STK2, HP2. rewrite (ry_errno_lit tp TP) in ERR2. unfold RERRNO in ERR2.
  pose proof (str_pres _ _ _ _ HP2 ltac:(intros b0 Hb0; apply in_or_app; right; exact Hb0) TB1) as TB2.
  apply ry_pres_nil in HP2. apply RYST_split in RY2. destruct RY2 as [HK3 YS3].
  pose proof (ypres_frame _ _ _ _ _ _ HP2 FR ltac:(lia)) as FR2. clear FR.
  assert (PRES3 : ry_pres REST (bv_unsigned sp) [] m m2).
  { eapply ry_pres_trans; [exact PRES2|]. apply ry_pres_of_rheap_pres. eapply rheap_pres_weaken; [exact HP2| lia| intros b0 Hb0; apply in_or_app; right; exact Hb0]. }
  (* [comment removed for export] *)
  pose proof (ypost_yleaf _ _ _ (ybuf_append_post2 b1 us BI ltac:(lia)) HLB) as BF. cbv beta in BF. destruct BF as (BI2 & OK2 & NOK2).
  assert (UB2 : yb_used b2 <= p + 1).
  { destruct (yb_state b2); [destruct (OK2 eq_refl) as (_ & -> & _); lia| destruct (NOK2 ltac:(discriminate)) as [-> _]; lia| destruct (NOK2 ltac:(discriminate)) as [-> _]; lia]. }
  destruct MBS2 as [MID2 MAD2].
  clear HP2 MI1 STK ERR AX2 HK2 YS2 PRES2 TB1 BR1 UB1 YAF.
  pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
  rz_seg HKS HK3.
  step. rewrite (unsigned_lit p) by lia. rewrite yswrap32_small by lia.
  step.
  step. if_cases KB; zify_cond KB.
  - (* [comment removed for export] *)
    apply evt_done.
    rewrite <- MAD2.
    eapply (HEAD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 mo2 s2' errv2 b2 mb2 (LK2 ++ LK) (p + 1) (p + 1) j0 j88);
      [ lk0 | rewrite <- app_assoc; exact HK3 | exact YS3 | exact FR2 | exact STK2 | exact MI2 | exact AX3 | exact ERR2 | exact PRES3 | exact YAF2 | exact TB2
      | exact BR2 | exact BI2 | split; [destruct MBS as [M1 M2]; congruence| destruct MBS as [M1 M2]; congruence] | exact UB2
      | lia | revert KB; rewrite ?unsigned_lit by lia; intros KB; lia | exact SBP | lia | ].
    intros r Hr. apply HL. eapply yleaf_bind; [exact HLB| exact Hr].
  - (* [comment removed for export] *)
    step. apply evt_done.
    rewrite <- MAD2.
    assert (PN' : p + 1 = n) by (revert KB; rewrite ?unsigned_lit by lia; intros KB; lia).
    destruct f' as [|f'']; [exfalso; lia|].
    eapply (decode_exit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 mo2 s2' errv2 b2 mb2 (LK2 ++ LK) (p + 1) (p + 1) _);
      [ lk0 | rewrite <- app_assoc; exact HK3 | exact YS3 | exact (dframe_blob _ _ _ FR2) | exact STK2 | exact MI2 | exact AX3 | exact ERR2 | exact PRES3 | exact YAF2 | exact TB2
      | exact BR2 | exact BI2 | split; [destruct MBS as [M1 M2]; congruence| destruct MBS as [M1 M2]; congruence] | exact UB2
      | lia | lia | ].
    apply exit_leaf. apply HL. eapply yleaf_bind; [exact HLB|]. cbv beta. apply dlf_exit. lia.
Qed.


(* [comment removed for export] *)
Lemma dframe_join : forall mx j0 (surw cpw : word) pad (w0 w1 w2 w3 w4 : byte),
  rw_cells usegs mx (bv_unsigned sp + -208) (CB 8 j0 :: dlits) ->
  rw_cells usegs mx (bv_unsigned sp + -120) [C4 surw] -> rw_cells usegs mx (bv_unsigned sp + -116) [C4 cpw] ->
  rw_cells usegs mx (bv_unsigned sp + -112) (CB 3 pad :: C1 w0 :: C1 w1 :: C1 w2 :: C1 w3 :: C1 w4 :: dsaved) ->
  rw_cells usegs mx (bv_unsigned sp + -208) (dframe j0 (le4 surw ++ le4 cpw ++ pad ++ [w0; w1; w2; w3; w4])).
Proof.
  intros mx j0 surw cpw pad w0 w1 w2 w3 w4 F1 F2 F3 F4. unfold dframe, dsaved, dlits in *.
  pose proof (proj1 (proj1 F4)) as WF. cbn [cells_wf cell_wf] in WF. destruct WF as [LP _].
  assert (J : rw_cells usegs mx (bv_unsigned sp + -208)
    ((CB 8 j0 :: dlits) ++ [C4 surw; C4 cpw; CB 3 pad; C1 w0; C1 w1; C1 w2; C1 w3; C1 w4] ++ dsaved)).
  { unfold dlits, dsaved. apply (proj2 (ycells_app usegs _ _ _ _)). split; [exact F1|]. cbn [cells_size csize Nat.add].
    replace (bv_unsigned sp + -208 + Z.of_nat 88) with (bv_unsigned sp + -120) by lia.
    apply (proj2 (ycells_app usegs _ _ [C4 surw] _)). split; [exact F2|]. cbn [cells_size csize Nat.add].
    replace (bv_unsigned sp + -120 + Z.of_nat 4) with (bv_unsigned sp + -116) by lia.
    apply (proj2 (ycells_app usegs _ _ [C4 cpw] _)). split; [exact F3|]. cbn [cells_size csize Nat.add].
    replace (bv_unsigned sp + -116 + Z.of_nat 4) with (bv_unsigned sp + -112) by lia. exact F4. }
  apply rw_cells_merge in J. cbn [cells_size csize cells_bytes cbytes app Nat.add] in J. exact J.
Qed.

Lemma utf8_bytes : forall mx pad (w0 w1 w2 w3 w4 : byte),
  rw_cells usegs mx (bv_unsigned sp + -112) (CB 3 pad :: C1 w0 :: C1 w1 :: C1 w2 :: C1 w3 :: C1 w4 :: dsaved) ->
  bytes_at usegs mx (bv_unsigned sp + -109) ([w0; w1; w2; w3; w4] ++ le8 s11 ++ le8 s10).
Proof.
  intros mx pad w0 w1 w2 w3 w4 F4. unfold dsaved in F4.
  pose proof (proj1 (proj1 F4)) as WF. cbn [cells_wf cell_wf] in WF. destruct WF as [LP _].
  pose proof (rw_cells_bytes_at _ _ _ _ F4) as BY. cbn [cells_bytes cbytes app] in BY.
  apply bytes_at_app in BY. destruct BY as [_ BY]. rewrite LP in BY. replace (bv_unsigned sp + -112 + Z.of_nat 3) with (bv_unsigned sp + -109) in BY by lia.
  match type of BY with bytes_at _ _ _ (?a :: ?b :: ?c :: ?d :: ?e :: ?rest) =>
    change (a :: b :: c :: d :: e :: rest) with (([a; b; c; d; e] ++ le8 s11 ++ le8 s10) ++ (le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++ le8 s2 ++ le8 s1 ++ le8 s0 ++ le8 ra)) in BY end.
  apply bytes_at_app in BY. destruct BY as [BY _]. exact BY.
Qed.

(* [comment removed for export] *)
Lemma decode_u8 : forall f', head_ok f' ->
  forall (rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3v s10v t3 t4 t5 t6 : word)
    (m1 : mem) (mo1 : Model) (s1' : PState) (errv1 : word) (b1 : ybuf) (mb1 : mbuf) (LK : list block) (p : Z) (us : list Z)
    (j0 : list byte) (surw cpw : word) (pad : list byte) (jrest : list byte),
  LK = [] -> HK s1' (buf_blocks mb1 b1 ++ LK ++ REST) m1 mo1 -> ystatics m1 ->
  rw_cells usegs m1 (bv_unsigned sp + -208) (CB 8 j0 :: dlits) ->
  rw_cells usegs m1 (bv_unsigned sp + -120) [C4 surw] -> rw_cells usegs m1 (bv_unsigned sp + -116) [C4 cpw] ->
  rw_cells usegs m1 (bv_unsigned sp + -112) (CB 3 pad :: map C1 (zbytes us) ++ C1 (Z_to_bv 8 0) :: map C1 jrest ++ dsaved) -> length jrest = (4 - length us)%nat ->
  stk usegs m1 lo (bv_unsigned sp + -208) -> mem_inv usegs m1 -> rauxv_ok m1 B ->
  rw_cells usegs m1 RERRNO [C4 errv1] ->
  ry_pres REST (bv_unsigned sp) [] m m1 ->
  rw_cells usegs m1 AF (alloc_cells ryc) ->
  bytes_at usegs m1 S (zbytes str) ->
  buf_rep usegs m1 mb1 b1 AF -> buf_inv b1 -> mb_same mbd mb1 ->
  Forall (fun c => 0 < c < 256) us -> (1 <= length us <= 4)%nat ->
  yb_used b1 + zlength us <= p + 1 -> 0 <= p -> p + 1 <= n -> sbody_ix str (p + 1) n -> (Z.to_nat (n - p) <= f')%nat ->
  (forall r, yleaf (b2 <- ybuf_append b1 us ;; ydecode_loop f' b2 str n (p + 1) (p + 1)) r -> yleaf WHOLE r) ->
  realizes_cfg acfg usegs (mkCfg (MS (mkR rav (wz (bv_unsigned sp + -208)) gp tp t0 t1 t2 (wz (mb_addr mb1)) (wz S) a0 a1 a2 a3 a4 a5 a6 a7 (wz n) s3v (wz 64512) (wz nS) (wz 1) (wz 92) (wz 101) (wz p) s10v (wz 113) t3 t4 t5 t6)
                           F (wz 0x17520) fc None m1 (seg_rom usegs)) mo1) K.
Proof.
  intros f' HEAD. intros until jrest. intros ELK HK1 YS1 F1 F2 F3 F4 USZ STK MI AX ERR PRES YAF TB BR BI MBS UF UL HUSED P0 PN SBP HF HL. apply lk_hide in ELK.
  unfold dsaved, nS, wz in *. pose proof LO as LO'. unfold RY_DECODE_STACK, RY_BUF_APPEND_STACK, RY_WRAP_STACK, alloc_ceiling in LO'.
  pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'. unfold RERRNO in ERR.
  pose proof (proj1 (proj1 F4)) as WF4. cbn [cells_wf cell_wf] in WF4. destruct WF4 as (LP & _).
  assert (UF' : Forall (fun c => 0 <= c < 256) us) by (eapply Forall_impl; [| exact UF]; cbv beta; intros; lia).
  assert (UNZ : ~ In 0 us) by (intros HI; rewrite Forall_forall in UF; specialize (UF 0 HI); lia).
  pose proof (rw_cells_bound _ _ _ _ F4) as F4B.
  pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl usegs m1) as WM.
  unfold dlits in F1.
  destruct us as [|u0 [|u1 [|u2 [|u3 [|u4 us']]]]]; [exfalso; cbn in UL; clear -UL; lia| | | | | exfalso; cbn in UL; clear -UL; lia];
    cbn [length Nat.sub] in USZ;
    destruct jrest as [|r0 [|r1 [|r2 [|r3 jrest']]]]; try (exfalso; cbn in USZ; clear -USZ; lia);
    cbn [zbytes map app] in F4.
  all: pose proof (dframe_join m1 _ _ _ pad _ _ _ _ _ F1 F2 F3 F4) as FRJ; pose proof (utf8_bytes m1 pad _ _ _ _ _ F4) as UB; cbn [app] in UB.
  all: rz_seg HKS HK1.
  all: step; apply evt_done; clear MU WM.
  (* [comment removed for export] *)
  all: lazymatch goal with UB : bytes_at _ _ (bv_unsigned _ + -109) ?bs, FRJ : rw_cells _ _ _ (dframe _ ?j88) |- _ =>
    let rest := lazymatch bs with
                | _ :: Z_to_bv 8 0 :: ?r => r | _ :: _ :: Z_to_bv 8 0 :: ?r => r
                | _ :: _ :: _ :: Z_to_bv 8 0 :: ?r => r | _ :: _ :: _ :: _ :: Z_to_bv 8 0 :: ?r => r end in
    let us := lazymatch type of HL with context [ybuf_append _ ?us] => us end in
    eapply (decode_lit f' HEAD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 mo1 s1' errv1 b1 mb1 LK p (bv_unsigned sp + -109) us (map bv_unsigned rest) j0 j88);
      [ lk0 | exact HK1 | exact YS1 | exact FRJ | exact STK | exact MI | exact AX | exact ERR | exact PRES | exact YAF | exact TB
      | exact BR | exact BI | exact MBS
      | rewrite zbytes_app; cbn [zbytes map app]; change (map (Z_to_bv 8) (map bv_unsigned ?l)) with (zbytes (map bv_unsigned l)); rewrite zbytes_unbytes, ?zb8_unb; exact UB
      | apply Forall_app; split; [exact UF'| apply Forall_cons; [clear; split; [apply Z.le_refl| apply Z.ltb_lt; reflexivity]| apply Forall_unbytes]]
      | exact UNZ | exact UL
      | unfold zlength; rewrite length_map; cbn [length app]; rewrite ?length_app, ?length_le8; cbn [length Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add];
        match goal with |- ?x mod 8 <= _ => pose proof (Z.mod_pos_bound x 8 ltac:(reflexivity)); lia end
      | lia | right; lia | exact HUSED | exact P0 | exact PN | exact SBP | exact HF | exact HL ] end.
Qed.

(* [comment removed for export] *)
Lemma dframe_split : forall mx j0 j88,
  rw_cells usegs mx (bv_unsigned sp + -208) (dframe j0 j88) ->
  exists pad (w0 w1 w2 w3 w4 : byte),
    rw_cells usegs mx (bv_unsigned sp + -208) (CB 8 j0 :: dlits)
    /\ rw_cells usegs mx (bv_unsigned sp + -120) [C4 (le_bytes_to_word (take 4 j88))]
    /\ rw_cells usegs mx (bv_unsigned sp + -116) [C4 (le_bytes_to_word (take 4 (drop 4 j88)))]
    /\ rw_cells usegs mx (bv_unsigned sp + -112) (CB 3 pad :: C1 w0 :: C1 w1 :: C1 w2 :: C1 w3 :: C1 w4 :: dsaved).
Proof.
  intros mx j0 j88 FR. unfold dframe, dsaved in FR.
  pose proof (proj1 (proj1 FR)) as WF. cbn [cells_wf cell_wf app dlits] in WF. destruct WF as (L0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L88 & _).
  change (CB 8 j0 :: dlits ++ ?r) with ((CB 8 j0 :: dlits) ++ r) in FR.
  destruct (proj1 (ycells_app usegs _ _ _ _) FR) as [F1 FRr]. clear FR. cbn [cells_size csize Nat.add dlits app] in FRr.
  replace (bv_unsigned sp + -208 + Z.of_nat 88) with (bv_unsigned sp + -120) in FRr by lia.
  pose proof (rw_cells_split_CB usegs _ _ [] 16 j88 _ [4; 4; 3; 1; 1; 1; 1; 1]%nat FRr eq_refl) as FRs. clear FRr. cbn [app mk_CB_cells] in FRs.
  destruct (proj1 (ycells_app usegs _ _ [CB 4 (take 4 j88)] _) FRs) as [F2 FRs2]. clear FRs. cbn [cells_size csize Nat.add] in FRs2.
  replace (bv_unsigned sp + -120 + Z.of_nat 4) with (bv_unsigned sp + -116) in FRs2 by lia.
  destruct (proj1 (ycells_app usegs _ _ [CB 4 (take 4 (drop 4 j88))] _) FRs2) as [F3 F4]. clear FRs2. cbn [cells_size csize Nat.add] in F4.
  replace (bv_unsigned sp + -116 + Z.of_nat 4) with (bv_unsigned sp + -112) in F4 by lia.
  set (r8 := drop 4 (drop 4 j88)) in F4.
  assert (L8 : length r8 = 8%nat) by (unfold r8; rewrite !length_drop; lia).
  destruct r8 as [|p0 [|p1 [|p2 [|v0 [|v1 [|v2 [|v3 [|v4 [|x r9]]]]]]]]] eqn:ER; try (exfalso; cbn in L8; clear -L8; lia).
  cbn [take drop] in F4.
  exists [p0; p1; p2], v0, v1, v2, v3, v4.
  split; [exact F1|]. split; [| split].
  - apply (ycb4_c4_in _ _ []) in F2. exact F2.
  - apply (ycb4_c4_in _ _ []) in F3. exact F3.
  - eapply rw_cells_recast; [exact F4| cbn; repeat split; reflexivity| reflexivity| reflexivity].
Qed.

(* [comment removed for export] *)
Ltac after_u8 OWNU MU WM F1 F2 F3 :=
  let X := fresh "OW" in pose proof (OWNU _ MU WM) as X;
  destruct X as ([HK2 AX2] & YS2 & PRES2 & BR2 & TB2);
  lazymatch goal with F4' : rw_cells _ ?mx (bv_unsigned _ + -112) (CB 3 ?padx :: C1 ?v0 :: C1 ?v1 :: C1 ?v2 :: C1 ?v3 :: C1 ?v4 :: _) |- _ =>
    pose proof (dframe_join mx _ _ _ padx v0 v1 v2 v3 v4 ltac:(exact F1) ltac:(exact F2) ltac:(exact F3) F4') as FRJ;
    pose proof (utf8_bytes mx padx v0 v1 v2 v3 v4 F4') as UB; cbn [app] in UB end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma decode_cp : forall f', head_ok f' ->
  forall (rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3v t3 t4 t5 t6 : word)
    (m1 : mem) (mo1 : Model) (s1' : PState) (errv1 : word) (b1 : ybuf) (mb1 : mbuf) (LK : list block) (e p cp : Z)
    (j0 : list byte) (surw : word) (pad : list byte) (w0 w1 w2 w3 w4 : byte),
  LK = [] -> HK s1' (buf_blocks mb1 b1 ++ LK ++ REST) m1 mo1 -> ystatics m1 ->
  rw_cells usegs m1 (bv_unsigned sp + -208) (CB 8 j0 :: dlits) ->
  rw_cells usegs m1 (bv_unsigned sp + -120) [C4 surw] -> rw_cells usegs m1 (bv_unsigned sp + -116) [C4 (wz cp)] ->
  rw_cells usegs m1 (bv_unsigned sp + -112) (CB 3 pad :: C1 w0 :: C1 w1 :: C1 w2 :: C1 w3 :: C1 w4 :: dsaved) ->
  stk usegs m1 lo (bv_unsigned sp + -208) -> mem_inv usegs m1 -> rauxv_ok m1 B ->
  rw_cells usegs m1 RERRNO [C4 errv1] ->
  ry_pres REST (bv_unsigned sp) [] m m1 ->
  rw_cells usegs m1 AF (alloc_cells ryc) ->
  bytes_at usegs m1 S (zbytes str) ->
  buf_rep usegs m1 mb1 b1 AF -> buf_inv b1 -> mb_same mbd mb1 ->
  0 <= cp < 65536 -> p = e + 5 ->
  yb_used b1 + 4 <= p + 1 -> 0 <= e -> p + 1 <= n -> sbody_ix str (p + 1) n -> (Z.to_nat (n - p) <= f')%nat ->
  (forall r, yleaf (b2 <- ybuf_append b1 (u8enc cp) ;; ydecode_loop f' b2 str n (p + 1) (p + 1)) r -> yleaf WHOLE r) ->
  realizes_cfg acfg usegs (mkCfg (MS (mkR rav (wz (bv_unsigned sp + -208)) gp tp t0 t1 t2 (wz (mb_addr mb1)) (wz S) (wz cp) a1 a2 a3 a4 a5 a6 a7 (wz n) s3v (wz 64512) (wz nS) (wz 1) (wz 92) (wz 101) (wz p) (wz e) (wz 113) t3 t4 t5 t6)
                           F (wz 0x173c8) fc None m1 (seg_rom usegs)) mo1) K.
Proof.
  intros f' HEAD. intros until w4. intros ELK HK1 YS1 F1 F2 F3 F4 STK MI AX ERR PRES YAF TB BR BI MBS CPR PE HUSED P0 PN SBP HF HL. apply lk_hide in ELK.
  unfold dsaved, nS, wz in *. pose proof LO as LO'. unfold RY_DECODE_STACK, RY_BUF_APPEND_STACK, RY_WRAP_STACK, alloc_ceiling in LO'.
  pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'. unfold RERRNO in ERR.
  pose proof AFC as AFC'. unfold alloc_ceiling in AFC'. unfold alloc_cells in YAF. cbn [yc_malloc_w yc_realloc_w yc_free_w ryc] in YAF.
  unfold dlits in F1.
  pose proof (proj1 (proj1 F4)) as WF4. cbn [cells_wf cell_wf] in WF4. destruct WF4 as (LP & _).
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -208)) = bv_unsigned sp + -208) by (apply unsigned_lit; lia).
  destruct AFIN as (hb & HBI & HB1 & HB2).
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp + -109, bv_unsigned sp + -104)] m1) as MU. pose proof (wmono_refl usegs m1) as WM.
  assert (OWNU : forall mx, munch [(bv_unsigned sp + -109, bv_unsigned sp + -104)] m1 mx -> wmono usegs m1 mx ->
            (HK s1' (buf_blocks mb1 b1 ++ LK ++ REST) mx mo1 /\ rauxv_ok mx B) /\ ystatics mx /\ ry_pres REST (bv_unsigned sp) [] m mx
            /\ buf_rep usegs mx mb1 b1 AF /\ bytes_at usegs mx S (zbytes str)).
  { intros mx MU1 WM1. split; [| split; [| split; [| split]]].
    - eapply (yown_writes HK HKF); [exact HK1| exact AX| exact MU1| exact WM1| |].
      + constructor; [left; cbn; unfold alloc_ceiling; lia| constructor].
      + constructor; [cbn; unfold RAUXV_CELL; lia| constructor].
    - eapply ystatics_munch; [exact YS1| exact MU1| exact WM1|]. constructor; [cbn; unfold RY_CALLBACKS; lia| constructor].
    - eapply ry_pres_trans; [exact PRES|]. eapply ryajl_pres_of_munch; [exact MU1| exact WM1|].
      intros a Ha Hc _. cbn. split; [| exact I].
      destruct Hc as [Hc|[Hc|(bq & Hb & Hr)]]; [lia| unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in Hc; lia|].
      pose proof (all_range_In _ _ (proj1 (HK_blocks HK HKB _ _ _ _ HK1)) ltac:(apply in_or_app; right; apply in_or_app; right; exact Hb)) as Hbr.
      unfold rblock_range, alloc_ceiling in Hbr. lia.
    - eapply (buf_rep_transport_hi _ _ _ _ _ _ _ BR MU1 WM1); [exact (proj1 (HK_blocks HK HKB _ _ _ _ HK1))| intros bq Hq; apply in_or_app; left; exact Hq|].
      constructor; [cbn; unfold alloc_ceiling; lia| constructor].
    - eapply str_pres_munch; [exact MU1| | exact TB]. constructor; [cbn; unfold alloc_ceiling; lia| constructor]. }
  yhide TB. clear PRES BR.
  rz_seg HKS HK1.
  step. step. if_cases K1; zify_cond K1.
  - (* [comment removed for export] *)
    step. step. if_cases K2; zify_cond K2.
    + (* [comment removed for export] *)
      destruct (u8enc_3 cp ltac:(lia)) as (UE & R0 & R1 & R2).
      step. rewrite (unsigned_lit cp) by lia.
      step. if_cases K3; zify_cond K3.
      1:{ exfalso. apply K3. rewrite ?unsigned_lit by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
          rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. }
      pose proof (shiftr_range cp 12 16 ltac:(lia) ltac:(lia)) as SR12. change (2 ^ (16 - 12)) with 16 in SR12.
      step. step. rewrite !(unsigned_lit cp) by lia. rewrite (unsigned_lit (cp ≫ 12)) by lia. rewrite lead3 by lia.
      step. sb_store.
      step. step. step. if_cases G1; zify_cond G1. 1:{ exfalso. clear -G1 SPR LO'. lia. }
      step. step. rewrite !(unsigned_lit cp) by lia. rewrite yfield6 by lia. step.
      step. sb_store.
      step. step. if_cases G2; zify_cond G2. 1:{ exfalso. clear -G2 SPR LO'. lia. }
      step. rewrite !(unsigned_lit cp) by lia. step.
      step. sb_store.
      step. step. if_cases G3; zify_cond G3. 1:{ exfalso. clear -G3 SPR LO'. lia. }
      step. sb_store.
      step. apply evt_done. after_u8 OWNU MU WM F1 F2 F3.
      lazymatch goal with F4' : rw_cells _ ?mx (bv_unsigned _ + -112) _ |- _ =>
      eapply (decode_u8 f' HEAD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx mo1 s1' errv1 b1 mb1 LK p
                [Z.shiftr cp 12 + 224; Z.land (Z.shiftr cp 6) 63 + 128; Z.land cp 63 + 128] j0 surw (Z_to_bv 64 cp) pad [_]);
        [ lk0 | exact HK2 | exact YS2 | exact F1 | exact F2 | exact F3 | cbn [zbytes map app]; exact F4' | reflexivity
        | assumption | assumption | exact AX2 | assumption | exact PRES2 | exact YAF | exact TB2 | exact BR2 | exact BI | exact MBS
        | repeat constructor; lia | clear; cbn; lia
        | unfold zlength; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | exact PN | exact SBP | exact HF
        | rewrite <- UE; exact HL ] end.
    + (* [comment removed for export] *)
      destruct (u8enc_2 cp ltac:(lia)) as (UE & R0 & R1).
      pose proof (shiftr_range cp 6 11 ltac:(lia) ltac:(lia)) as SR6. change (2 ^ (11 - 6)) with 32 in SR6.
      step. step. rewrite !(unsigned_lit cp) by lia. rewrite (unsigned_lit (cp ≫ 6)) by lia. rewrite lead2 by lia.
      step. sb_store.
      step. step. step. if_cases G1; zify_cond G1. 1:{ exfalso. clear -G1 SPR LO'. lia. }
      step. rewrite !(unsigned_lit cp) by lia. step.
      step. sb_store.
      step. step. if_cases G2; zify_cond G2. 1:{ exfalso. clear -G2 SPR LO'. lia. }
      step. sb_store.
      step. apply evt_done. after_u8 OWNU MU WM F1 F2 F3.
      lazymatch goal with F4' : rw_cells _ ?mx (bv_unsigned _ + -112) _ |- _ =>
      eapply (decode_u8 f' HEAD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx mo1 s1' errv1 b1 mb1 LK p
                [Z.shiftr cp 6 + 192; Z.land cp 63 + 128] j0 surw (Z_to_bv 64 cp) pad [_; _]);
        [ lk0 | exact HK2 | exact YS2 | exact F1 | exact F2 | exact F3 | cbn [zbytes map app]; exact F4' | reflexivity
        | assumption | assumption | exact AX2 | assumption | exact PRES2 | exact YAF | exact TB2 | exact BR2 | exact BI | exact MBS
        | repeat constructor; lia | clear; cbn; lia
        | unfold zlength; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | exact PN | exact SBP | exact HF
        | rewrite <- UE; exact HL ] end.
  - (* [comment removed for export] *)
    step. sb_store.
    step. step. step. if_cases G1; zify_cond G1. 1:{ exfalso. clear -G1 SPR LO'. lia. }
    step. sb_store. step.
    step. if_cases K2; zify_cond K2.
    + (* [comment removed for export] *)
      rewrite (u8enc_1 cp) in HL by lia.
      apply evt_done. after_u8 OWNU MU WM F1 F2 F3.
      lazymatch goal with UB : bytes_at _ ?mx (bv_unsigned _ + -109) (_ :: _ :: ?r), FRJ : rw_cells _ _ _ (dframe _ ?j88) |- _ =>
      eapply (decode_lit f' HEAD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx mo1 s1' errv1 b1 mb1 LK p (bv_unsigned sp + -109) [cp] (map bv_unsigned r) j0 j88);
        [ lk0 | exact HK2 | exact YS2 | exact FRJ | assumption | assumption | exact AX2 | assumption | exact PRES2 | exact YAF | exact TB2
        | exact BR2 | exact BI | exact MBS
        | rewrite zbytes_app; cbn [zbytes map app]; change (map (Z_to_bv 8) (map bv_unsigned ?l)) with (zbytes (map bv_unsigned l)); rewrite zbytes_unbytes, ?zb8_unb; exact UB
        | apply Forall_app; split; [repeat constructor; lia| apply Forall_cons; [clear; split; [apply Z.le_refl| apply Z.ltb_lt; reflexivity]| apply Forall_unbytes]]
        | intros [X|[]]; lia | clear; cbn; lia
        | unfold zlength; rewrite length_map; cbn [length app]; rewrite ?length_app, ?length_le8; cbn [length Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add];
          match goal with |- ?x mod 8 <= _ => pose proof (Z.mod_pos_bound x 8 ltac:(reflexivity)); lia end
        | lia | right; lia | unfold zlength; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | exact PN | exact SBP | exact HF | exact HL ] end.
    + (* [comment removed for export] *)
      assert (CP0 : cp = 0) by lia.
      rewrite CP0 in HL. change (u8enc 0) with [0] in HL.
      step. step. step. step. apply evt_done. after_u8 OWNU MU WM F1 F2 F3.
      rewrite CP0 in UB, FRJ. clear MU WM HK1 YS1 AX OWNU F1 F2 F3.
      lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -112) _ |- _ => clear H end.
      lazymatch goal with H : mem_inv _ ?mx |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?my _) _) _ => rename H into MI2; rename my into m2' end.
      lazymatch goal with H : stk _ m2' _ _ |- _ => rename H into STK2 end.
      lazymatch goal with H : rw_cells _ m2' 218620 _ |- _ => rename H into ERR2 end.
      pose proof (proj1 (proj1 (bytes_at_app _ _ _ [Z_to_bv 8 0] _) UB)) as UB1. clear UB.
      eapply (YAP (LK ++ REST) mb1 b1 AF (bv_unsigned sp + -109) [0] lo B errv1 K);
        [ exact K0 | apply ua_append'; [exact MBS| lia] | apply RYST_split; split; [exact HK2| exact YS2] | exact BR2 | exact BI | exact YAF
        | exists hb; split; [apply in_or_app; right; exact HBI| lia]
        | exact UB1 | repeat constructor; clear; lia | intros _; lia | unfold zlength; cbn [length Z.of_nat Pos.of_succ_nat]; lia | unfold zlength; cbn [length Z.of_nat Pos.of_succ_nat]; lia
        | right; right; left; rewrite ESP; lia
        | lkr; exact YR
      | split; [exact AX2|]; split; [rewrite ESP; lia|]; split; [rewrite ESP; exact STK2|]; split; [exact CEIL|];
          split; [rewrite ESP; unfold RY_BUF_APPEND_STACK, RY_WRAP_STACK; lia|]; split; [rewrite (ry_errno_lit tp TP); exact ERR2|]; split; [exact MI2| exact TP]
        | reflexivity | reflexivity | reflexivity | ].
      cbv beta. intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m3 mo3 s3' b2 mb2 LK2 POST.
      destruct POST as ((MI3 & STK3 & (errv3 & ERR3) & AX3 & HP3) & YAF3 & HLB & BR3 & MBS2 & LKE3 & RY3). apply lk_hide in LKE3.
      replace (ret_pc (Z_to_bv 64 95228)) with (Z_to_bv 64 95228) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      rewrite ESP in STK3, HP3. rewrite (ry_errno_lit tp TP) in ERR3. unfold RERRNO in ERR3.
      pose proof (str_pres _ _ _ _ HP3 ltac:(intros b0 Hb0; apply in_or_app; right; exact Hb0) TB2) as TB3.
      apply ry_pres_nil in HP3. apply RYST_split in RY3. destruct RY3 as [HK3 YS3].
      pose proof (ypres_frame _ _ _ _ _ _ HP3 FRJ ltac:(lia)) as FR3. clear FRJ.
      assert (PRES3 : ry_pres REST (bv_unsigned sp) [] m m3).
      { eapply ry_pres_trans; [exact PRES2|]. apply ry_pres_of_rheap_pres. eapply rheap_pres_weaken; [exact HP3| lia| intros b0 Hb0; apply in_or_app; right; exact Hb0]. }
      pose proof (ypost_yleaf _ _ _ (ybuf_append_post2 b1 [0] BI ltac:(unfold zlength; cbn; lia)) HLB) as BF. cbv beta in BF. destruct BF as (BI2 & OK2 & NOK2).
      assert (UB2 : yb_used b2 <= p + 1).
      { destruct (yb_state b2); [destruct (OK2 eq_refl) as (_ & -> & _); unfold zlength; cbn; lia| destruct (NOK2 ltac:(discriminate)) as [-> _]; lia| destruct (NOK2 ltac:(discriminate)) as [-> _]; lia]. }
      destruct MBS2 as [MID2 MAD2].
      clear HP3 MI2 STK2 ERR2 AX2 HK2 YS2 PRES2 TB2 BR2 UB1 YAF.
      unfold dframe, dlits in FR3. cbn [app] in FR3.
      pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl usegs m3) as WM.
      rz_seg HKS HK3.
      step. rewrite (unsigned_lit e) by lia. rewrite yswrap32_small by lia. replace (e + 6) with (p + 1) by lia.
      step.
      step. if_cases KB; zify_cond KB.
      * apply evt_done. rewrite <- MAD2.
        eapply (HEAD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 mo3 s3' errv3 b2 mb2 (LK2 ++ LK) (p + 1) (p + 1) j0 _);
          [ lk0 | rewrite <- app_assoc; exact HK3 | exact YS3 | exact FR3 | exact STK3 | exact MI3 | exact AX3 | exact ERR3 | exact PRES3 | exact YAF3 | exact TB3
          | exact BR3 | exact BI2 | split; [destruct MBS as [M1 M2]; congruence| destruct MBS as [M1 M2]; congruence] | exact UB2
          | lia | revert KB; rewrite ?unsigned_lit by lia; intros KB; lia | exact SBP | lia | ].
        intros r Hr. apply HL. eapply yleaf_bind; [exact HLB| exact Hr].
      * step. apply evt_done. rewrite <- MAD2.
        assert (PN' : p + 1 = n) by (revert KB; rewrite ?unsigned_lit by lia; intros KB; lia).
        destruct f' as [|f'']; [exfalso; lia|].
        eapply (decode_exit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 mo3 s3' errv3 b2 mb2 (LK2 ++ LK) (p + 1) (p + 1) _);
          [ lk0 | rewrite <- app_assoc; exact HK3 | exact YS3 | exact (dframe_blob _ _ _ FR3) | exact STK3 | exact MI3 | exact AX3 | exact ERR3 | exact PRES3 | exact YAF3 | exact TB3
          | exact BR3 | exact BI2 | split; [destruct MBS as [M1 M2]; congruence| destruct MBS as [M1 M2]; congruence] | exact UB2
          | lia | lia | ].
        apply exit_leaf. apply HL. eapply yleaf_bind; [exact HLB|]. cbv beta. apply dlf_exit. lia.
Qed.
End Fn.
End S.
End RC__3.
