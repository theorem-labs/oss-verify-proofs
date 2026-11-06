(* The reader-level facts of the image-B walk of reac_segconf_model on fuzz_segconf.asan-ubsan
   (0x89e04). Adapted from image A's lib/A/Prog/reac_segconf_ignore_file_lem.v (commit
   62181ed287a7), for the one field this function loads.

   Two groups, both statement-level (no image module is Required, so the file is image-independent):
   - the field the function loads out of the entry reac_segconf_find returns: the 4-byte model_set flag at +0x3c,
     read through the ASan reader out of the contract's [sa_rconf] (lib/B/Prog/SegABase.v);
   - the transport of the contract's premises across writes that touch no byte below the allocator's ceiling:
     the function writes only its own 16-byte frame, which [astk_ok] keeps at or above alloc_ceiling, and every
     object [query_pre] and [arodata_okP] name lies below it. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec seg_query_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_segconf_find_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ============================ the model_set field, through the reader ============================ *)
Lemma mdl_nth_firstn : forall {A : Type} (l : list A) n k d, (k < n)%nat -> nth k (firstn n l) d = nth k l d.
Proof.
intros A l. induction l as [|x l IH]; intros n k d Hk; [rewrite firstn_nil; reflexivity|].
destruct n as [|n]; [lia|]. cbn [firstn]. destruct k as [|k]; [reflexivity|]. cbn [nth]. apply IH. lia.
Qed.
Lemma mdl_nth_skipn : forall {A : Type} (l : list A) off k d, nth k (skipn off l) d = nth (off + k) l d.
Proof.
intros A l off. revert l. induction off as [|off IH]; intros l k d; [reflexivity|].
destruct l as [|x l]; cbn [skipn Nat.add]; [now destruct k | apply IH].
Qed.
Lemma mdl_nth_fld : forall (l : list byte) off n k d, (k < n)%nat ->
nth k (seg_spec.fld off n l) d = nth (off + k) l d.
Proof. intros l off n k d Hk. unfold seg_spec.fld. rewrite mdl_nth_firstn by lia. apply mdl_nth_skipn. Qed.
(* a field of an entry is a field of the block *)
Lemma mdl_fld_fld_z : forall (l : list byte) off n b, 0 <= off -> 0 <= n -> off + n <= 356 ->
seg_spec.fldz off n (seg_spec.fld b 356 l) = seg_spec.fld (b + Z.to_nat off) (Z.to_nat n) l.
Proof. intros l off n b H1 H2 H3. unfold seg_spec.fldz. apply seg_query_facts.sq_fld_fld. lia. Qed.
(* the 4 bytes of an int field holding a C truth value *)
Lemma mdl_flag_byte : forall (b : bool) (f : list byte) k, seg_spec.flag_enc b f -> (k < 4)%nat ->
bv_unsigned (nth k f ZB0) = YO0f.le_byte (seg_spec.b2z b) 4 k.
Proof.
intros b f k Hf Hk. unfold seg_spec.flag_enc in Hf. subst f.
destruct b; (do 4 (destruct k as [|k]; [vm_compute; reflexivity|]); lia).
Qed.
(* a field of c->seg[i], read through the reader out of sa_rconf's bytes *)
Lemma mdl_field_rd : forall (rd : reader) c bs rcs i off n k,
sa_bytes rd c bs -> seg_spec.rconf_enc rcs bs -> (i < length (rc_seg rcs))%nat ->
0 <= off -> 0 < n -> off + n <= 356 -> (k < Z.to_nat n)%nat ->
rd (c + 356 * Z.of_nat i + off + Z.of_nat k)
= Some (bv_unsigned (nth k (seg_spec.fldz off n (seg_spec.fld (356 * i) 356 bs)) ZB0)).
Proof.
intros rd c bs rcs i off n k HB HE Hi Ho Hn Hon Hk.
destruct (seg_query_facts.sq_rconf_len rcs bs HE) as [HL HS].
unfold seg_spec.SEG_C_SIZE in HL.
rewrite mdl_fld_fld_z by lia. rewrite mdl_nth_fld by lia.
replace (c + 356 * Z.of_nat i + off + Z.of_nat k)
with (c + Z.of_nat (356 * i + Z.to_nat off + k)) by lia.
apply HB. lia.
Qed.
(* c->seg[i].model_set, the 4 bytes at +0x3c that the lw at 0x89e40 reads *)
Lemma mdl_set_rd : forall (rd : reader) c rcs i k,
sa_rconf rd c rcs -> (i < length (rc_seg rcs))%nat -> (k < 4)%nat ->
rd (c + 356 * Z.of_nat i + 60 + Z.of_nat k)
= Some (YO0f.le_byte (seg_spec.b2z (rs_model_set (r_seg rcs i))) 4 k).
Proof.
intros rd c rcs i k (bs & HB & HE) Hi Hk.
rewrite (mdl_field_rd rd c bs rcs i 60 4 k HB HE Hi) by lia.
f_equal.
destruct (seg_query_facts.sq_rseg rcs bs i HE Hi) as (_ & _ & _ & _ & _ & _ & _ & HF & _).
unfold seg_spec.RS_MODEL_SET in HF.
exact (mdl_flag_byte _ _ k HF Hk).
Qed.
(* the index found is an entry of the block, and the block holds at most 32 *)
Lemma mdl_find_lt : forall (rd : reader) c rcs nm i,
sa_rconf rd c rcs -> r_find rcs nm = Some i -> (i < length (rc_seg rcs))%nat /\ (i < 32)%nat.
Proof.
intros rd c rcs nm i (bs & _ & HE) HF.
destruct (seg_query_facts.sq_rconf_len rcs bs HE) as [_ HS].
pose proof (seg_query_facts.sq_find_lt rcs nm i HF). split; lia.
Qed.

(* ===================== what the reader gives a chunk of the symbolic state ===================== *)
Section v.
Variable segs : list Segment.
Lemma mdl_val_of_rd : forall (H : word -> bool) (mem : word -> option byte) a n v,
(forall k, (k < n)%nat -> aview segs H mem (a + Z.of_nat k) = Some (YO0f.le_byte v n k)) ->
val_mem segs (mrestrict H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn [option_map] in Hv; [|discriminate Hv].
injection Hv as Hb. f_equal. rewrite <- Hb. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
End v.

(* ======================= transport across writes above the allocator's ceiling ======================= *)
(* The function writes only [sp - 16, sp) of its own frame and, under the call, find's window; astk_ok puts the
   whole window at or above ly_stk_lo, which is at or above alloc_ceiling. Every object the contract names lies
   below alloc_ceiling (a heap block, a side-stack frame or an image byte), and so does every shadow byte of it. *)
Section k.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Definition mdl_lowkept (rd rd' : reader) : Prop := forall a, 0 <= a < alloc_ceiling -> rd' a = rd a.
Variable segs : list Segment.
Variable B : asyms.

Lemma mdl_shadow_bnd : forall s, 0 <= s < alloc_ceiling -> 0 <= SHADOW_OFF + s / 8 <= 17594332446721.
Proof.
intros s Hs. pose proof (@asan_consts rc) as (AC & _).
assert (H1 : 0 <= s / 8) by (apply Z.div_pos; lia).
assert (H2 : s / 8 < 17592184995841) by (apply Z.div_lt_upper_bound; lia).
unfold SHADOW_OFF. lia.
Qed.
Lemma mdl_div8_low : forall s, 0 <= s < alloc_ceiling -> 0 <= SHADOW_OFF + s / 8 < alloc_ceiling.
Proof.
intros s Hs. pose proof (@asan_consts rc) as (AC & _). pose proof (mdl_shadow_bnd s Hs). lia.
Qed.
Lemma mdl_gran_low : forall s, 0 <= s < alloc_ceiling -> 0 <= s / 8 * 8 /\ s / 8 * 8 <= s.
Proof.
intros s Hs. pose proof (Z.mul_div_le s 8 ltac:(lia)).
split; [apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia | lia].
Qed.
Lemma mdl_addr_kept : forall rd rd' q n, mdl_lowkept rd rd' -> 0 <= q -> 0 <= n -> q + n <= alloc_ceiling ->
sa_addr rd q n -> sa_addr rd' q n.
Proof.
intros rd rd' q n HK Hq Hn Hqn (A1 & A2 & A3 & A4 & A5).
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split.
- intros x Hx. destruct (A4 x Hx) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
  unfold shadow_of_addr in *. rewrite (HK (SHADOW_OFF + x / 8)); [exact Hsv | apply mdl_div8_low; lia].
- intros Hpos s Hs. unfold shadow_addr in Hs.
  pose proof (@asan_consts rc) as (AC & _).
  pose proof (mdl_shadow_bnd q ltac:(lia)) as D1.
  pose proof (mdl_shadow_bnd (q + n - 1) ltac:(lia)) as D2.
  pose proof (mdl_gran_low (SHADOW_OFF + q / 8) ltac:(lia)) as [G1 G2].
  pose proof (mdl_gran_low (SHADOW_OFF + (q + n - 1) / 8) ltac:(lia)) as [G3 G4].
  assert (HS2 : 0 <= s < alloc_ceiling) by lia. rewrite (HK s HS2). exact (A5 Hpos s Hs).
Qed.
Lemma mdl_bytes_kept : forall (rd rd' : reader) a bs lo hi,
(forall x, lo <= x < hi -> rd' x = rd x) -> lo <= a -> a + Z.of_nat (length bs) <= hi ->
sa_bytes rd a bs -> sa_bytes rd' a bs.
Proof.
intros rd rd' a bs lo hi HK Hlo Hhi HB i Hi.
assert (HR : lo <= a + Z.of_nat i < hi) by lia. rewrite (HK _ HR). exact (HB i Hi).
Qed.
Lemma mdl_zs_kept : forall (rd rd' : reader) a l lo hi,
(forall x, lo <= x < hi -> rd' x = rd x) -> lo <= a -> a + Z.of_nat (length l) <= hi ->
sa_zs rd a l -> sa_zs rd' a l.
Proof.
intros rd rd' a l lo hi HK Hlo Hhi HB i Hi.
assert (HR : lo <= a + Z.of_nat i < hi) by lia. rewrite (HK _ HR). exact (HB i Hi).
Qed.
Lemma mdl_rconf_kept : forall (rd rd' : reader) c rcs lo hi,
(forall x, lo <= x < hi -> rd' x = rd x) -> lo <= c -> c + seg_spec.SEG_C_SIZE <= hi ->
sa_rconf rd c rcs -> sa_rconf rd' c rcs.
Proof.
intros rd rd' c rcs lo hi HK Hlo Hhi (bs & HB & HE). exists bs. split; [|exact HE].
destruct (seg_query_facts.sq_rconf_len rcs bs HE) as [HL _].
eapply mdl_bytes_kept; [exact HK | exact Hlo | unfold seg_spec.SEG_C_SIZE in Hhi; lia | exact HB].
Qed.
Lemma mdl_str_kept : forall (rd rd' : reader) p s lo hi,
(forall x, lo <= x < hi -> rd' x = rd x) -> 0 <= lo -> lo <= p ->
p + Z.of_nat (length s) - (p + Z.of_nat (length s)) mod 8 + 8 <= hi ->
sa_str rd p s -> sa_str rd' p s.
Proof.
intros rd rd' p s lo hi HK Hlo Hlp Hhi ((HZ & HN) & HT).
pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)).
split; [split; [|exact HN]|].
- eapply mdl_zs_kept; [exact HK | exact Hlp | rewrite length_app; cbn [length]; lia | exact HZ].
- intros x Hx. assert (HR : lo <= x < hi) by lia. rewrite (HK x HR). exact (HT x Hx).
Qed.
(* where an object the contract names lies: below the allocator's ceiling *)
Lemma mdl_loc_low : forall ly S (W : world segs) mem md q n,
AR_laws segs B -> (forall a, in_img segs a -> 0 <= a < kLowMemEnd) ->
AR segs B ly S W mem md -> sa_loc segs B ly S q n -> 0 < n -> 0 <= q /\ q + n <= alloc_ceiling.
Proof.
intros ly S W mem md q n LAWS segs_low HAR HL Hn.
pose proof (@asan_consts rc) as (AC & _ & _ & _ & KLOW).
destruct HL as [(b & m & Hin & H1 & H2) | [(cid & pos & Hin & Hc & H1 & H2) | HI]].
- destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & H4096 & Hceil & _ & _ & _ & Hm).
  pose proof (req_size_pos m ltac:(lia)) as [_ Hreq]. lia.
- destruct (al_sep _ _ LAWS ly S W mem md HAR) as [_ HF].
  rewrite Forall_forall in HF. specialize (HF (cid, pos) Hin). cbn [fst snd] in HF. lia.
- pose proof (segs_low q (proj1 (HI q ltac:(lia)))) as Hq.
  pose proof (segs_low (q + n - 1) (proj1 (HI (q + n - 1) ltac:(lia)))) as Hq2. lia.
Qed.
Lemma mdl_heap_low : forall ly S (W : world segs) mem md q n,
AR_laws segs B -> AR segs B ly S W mem md -> sa_heap B ly S q n -> 0 <= q /\ q + n <= alloc_ceiling.
Proof.
intros ly S W mem md q n LAWS HAR (b & m & Hin & H1 & H2).
destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & H4096 & Hceil & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hreq]. lia.
Qed.
(* the query's premises hold again after a write that touches no byte below the ceiling *)
Lemma mdl_query_pre_kept : forall ly S (W : world segs) mem md rd rd' c name rcs nm,
AR_laws segs B -> (forall a, in_img segs a -> 0 <= a < kLowMemEnd) ->
AR segs B ly S W mem md -> mdl_lowkept rd rd' ->
query_pre segs B ly S rd c name rcs nm -> query_pre segs B ly S rd' c name rcs nm.
Proof.
intros ly S W mem md rd rd' c name rcs nm LAWS segs_low HAR HK
  (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10).
pose proof (@asan_consts rc) as (AC & _).
destruct (mdl_heap_low ly S W mem md c seg_spec.SEG_C_SIZE LAWS HAR Q4) as [Hc0 Hc1].
destruct (mdl_loc_low ly S W mem md name (Z.of_nat (length nm) + 1) LAWS segs_low HAR Q8 ltac:(lia))
  as [Hn0 Hn1].
pose proof (Z.mod_pos_bound (name + Z.of_nat (length nm)) 8 ltac:(lia)).
assert (HTL : name + Z.of_nat (length nm) - (name + Z.of_nat (length nm)) mod 8 + 8 <= alloc_ceiling).
{ pose proof (@alloc_ceiling_value rc) as [_ HAC4096].
  assert (Hlt : name + Z.of_nat (length nm) < alloc_ceiling) by lia.
  assert (Hge : 0 <= name + Z.of_nat (length nm)) by lia.
  clear - Hlt Hge HAC4096. Z.div_mod_to_equations. lia. }
split; [exact Q1|]. split; [exact Q2|].
split; [apply (mdl_rconf_kept rd rd' c rcs 0 alloc_ceiling);
  [exact HK | lia | unfold seg_spec.SEG_C_SIZE in *; lia | exact Q3]|].
split; [exact Q4|].
split; [apply (mdl_addr_kept rd rd' c seg_spec.SEG_C_SIZE);
  [exact HK | lia | unfold seg_spec.SEG_C_SIZE; lia | unfold seg_spec.SEG_C_SIZE in *; lia | exact Q5]|].
split; [exact Q6|].
split; [apply (mdl_str_kept rd rd' name nm 0 alloc_ceiling); [exact HK | lia | lia | lia | exact Q7]|].
split; [exact Q8|].
split; [apply (mdl_addr_kept rd rd' name (Z.of_nat (length nm) + 1));
  [exact HK | lia | lia | lia | exact Q9] | exact Q10].
Qed.
(* the image's read-only bytes are read again: every byte in_roP names lies below the ceiling *)
Lemma mdl_arodata_kept : forall rlo rhi (rd rd' : reader),
(forall a, in_roP segs rlo rhi a -> 0 <= a < alloc_ceiling) -> mdl_lowkept rd rd' ->
arodata_okP segs rlo rhi B rd -> arodata_okP segs rlo rhi B rd'.
Proof.
intros rlo rhi rd rd' HBound HK HR a Hro Ho He. rewrite (HK a (HBound a Hro)). exact (HR a Hro Ho He).
Qed.
End k.
