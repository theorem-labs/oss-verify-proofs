(* The image-B port of lib/A/Prog/check_model_lem.v (commit beed74b30c04): the pure facts the
   image-B walk of check_model (lib/B/Prog/check_model.v, fuzz_segconf.asan-ubsan) reads off its contract's
   encodings, over image B's kit copies (lib.B YG0f YG0n YG0d) and contract base (lib.B.Prog.SegABase). The
   statements and proofs are the A file's; only the Require lines differ. No image, no listing. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YP09 YK04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegABase.
Import ListNotations.
Open Scope Z_scope.

Lemma cm_nth_firstn : forall (A : Type) n (l : list A) i d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
intros A n. induction n as [|n IH]; intros l i d Hi; [lia|].
destruct l as [|x l]; [reflexivity|]. destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.

Lemma cm_nth_skipn : forall (A : Type) n (l : list A) i d, nth i (skipn n l) d = nth (n + i) l d.
Proof.
intros A n. induction n as [|n IH]; intros l i d; [reflexivity|].
destruct l as [|x l]; [destruct i; reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.

(* byte i of the field [off, off + n) of bs is byte off + i of bs *)
Lemma cm_nth_fldz : forall off n bs i d, 0 <= off -> (i < Z.to_nat n)%nat ->
  nth i (fldz off n bs) d = nth (Z.to_nat off + i) bs d.
Proof. intros off n bs i d Ho Hi. unfold fldz, fld. rewrite cm_nth_firstn by exact Hi. apply cm_nth_skipn. Qed.

(* what a reader over memory returns is a byte *)
Lemma cm_aview_byte : forall segs H mem a v, aview segs H mem a = Some v -> 0 <= v < 256.
Proof.
intros segs H mem a v Hv. unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) a) as [b|]; cbn [option_map] in Hv; [|discriminate Hv].
injection Hv as <-. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. exact R.
Qed.

(* the 4-byte flag want->model_set (seg_spec.MS_MODEL_SET = 0x20) holds 1 or 0 *)
Lemma cm_flag : forall rd a g bs, sa_bytes rd a bs -> mseg_enc g bs ->
  sa_val rd (a + MS_MODEL_SET) 4 (if ms_model_set g then 1 else 0).
Proof.
intros rd a g bs HB (LEN & _ & _ & _ & _ & _ & FM & _). unfold flag_enc in FM.
intros k Hk.
assert (Hi : (32 + k < length bs)%nat) by (rewrite LEN; lia).
specialize (HB (32 + k)%nat Hi).
replace (a + MS_MODEL_SET + Z.of_nat k) with (a + Z.of_nat (32 + k)) by (unfold MS_MODEL_SET; lia).
rewrite HB. f_equal.
replace (32 + k)%nat with (Z.to_nat MS_MODEL_SET + k)%nat by reflexivity.
rewrite <- (cm_nth_fldz MS_MODEL_SET 4 bs k ZB0) by (unfold MS_MODEL_SET; cbn; lia).
rewrite FM. destruct (ms_model_set g); do 4 (destruct k as [|k]; [vm_compute; reflexivity|]); lia.
Qed.

Lemma cm_nth_map_u : forall (l : list byte) i, nth i (map bv_unsigned l) 0 = bv_unsigned (nth i l ZB0).
Proof. induction l as [|x l IH]; intros [|i]; cbn [map nth]; [reflexivity | reflexivity | reflexivity | apply IH]. Qed.

(* the model text want->model (seg_spec.MS_MODEL = 0x24, char[24]) is a C string of the reader *)
Lemma cm_model_strz : forall rd a g bs, sa_bytes rd a bs -> mseg_enc g bs ->
  sa_strz rd (a + MS_MODEL) (ms_model g) /\ (length (ms_model g) < 24)%nat.
Proof.
intros rd a g bs HB (LEN & _ & _ & _ & _ & _ & _ & CM & _).
destruct CM as (Lf & Ls & NZ & Hp).
split; [|exact Ls]. split; [|exact NZ].
intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
assert (Hi2 : (36 + i < length bs)%nat) by (rewrite LEN; lia).
specialize (HB (36 + i)%nat Hi2).
replace (a + MS_MODEL + Z.of_nat i) with (a + Z.of_nat (36 + i)) by (unfold MS_MODEL; lia).
rewrite HB. f_equal.
rewrite <- Hp. rewrite cm_nth_firstn by lia. unfold zs.
rewrite cm_nth_map_u. f_equal.
replace (36 + i)%nat with (Z.to_nat MS_MODEL + i)%nat by reflexivity.
symmetry. apply cm_nth_fldz; [unfold MS_MODEL; lia | cbn; lia].
Qed.

(* a C string of a reader over memory, as the byte list the runtime contracts take (RtDefs.astr_at's shape) *)
Lemma cm_strz_bytes : forall segs H mem p s, sa_strz (aview segs H mem) p s ->
  sa_bytes (aview segs H mem) p (map (Z_to_bv 8) s ++ [ZB0]) /\ ~ In ZB0 (map (Z_to_bv 8) s) /\
  zs (map (Z_to_bv 8) s) = s.
Proof.
intros segs H mem p s [HZ NZ].
assert (RG : forall i, (i < length s)%nat -> 0 <= nth i s 0 < 256).
{ intros i Hi. assert (Hi' : (i < length (s ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
  specialize (HZ i Hi'). rewrite app_nth1 in HZ by exact Hi. exact (cm_aview_byte _ _ _ _ _ HZ). }
assert (RGI : forall z, In z s -> 0 <= z < 256).
{ intros z Hz. destruct (In_nth s z 0 Hz) as (i & Hi & <-). exact (RG i Hi). }
assert (ZS : zs (map (Z_to_bv 8) s) = s).
{ unfold zs. rewrite map_map. rewrite <- (map_id s) at 2. apply map_ext_in. intros z Hz.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact (RGI z Hz). }
split; [|split; [|exact ZS]].
- intros i Hi. rewrite length_app, length_map in Hi. cbn [length] in Hi.
  assert (Hi' : (i < length (s ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
  rewrite (HZ i Hi'). f_equal.
  replace (map (Z_to_bv 8) s ++ [ZB0]) with (map (Z_to_bv 8) (s ++ [0])) by (rewrite map_app; reflexivity).
  change ZB0 with (Z_to_bv 8 0). rewrite map_nth. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. symmetry. apply Z.mod_small.
  destruct (Nat.lt_ge_cases i (length s)) as [L|L].
  + rewrite app_nth1 by exact L. exact (RG i L).
  + rewrite app_nth2 by exact L. replace (i - length s)%nat with 0%nat by lia. cbn. lia.
- intros Hin. apply in_map_iff in Hin as (z & Hz & Hzin). apply NZ.
  assert (Hz0 : z = 0).
  { apply (f_equal bv_unsigned) in Hz. unfold ZB0 in Hz. rewrite !Z_to_bv_unsigned in Hz. unfold bv_wrap in Hz.
    change (bv_modulus 8) with 256 in Hz. rewrite Z.mod_small in Hz by exact (RGI z Hzin). exact Hz. }
  subst z. exact Hzin.
Qed.

(* SegModel.strcmp is 0 on two NUL-free texts only when they are equal *)
Lemma cm_strcmp_eq : forall s t, ~ In 0 s -> ~ In 0 t -> SegModel.strcmp s t = 0 -> s = t.
Proof.
induction s as [|a s IH]; intros [|b t] Ns Nt H; cbn [SegModel.strcmp] in H.
- reflexivity.
- exfalso. apply Nt. left. lia.
- exfalso. apply Ns. left. lia.
- destruct (Z.eqb_spec a b) as [<-|Hab]; destruct (Z.eqb_spec a 0) as [Ha0|Ha0]; cbn [andb negb] in H.
  + exfalso. apply Ns. left. lia.
  + f_equal. apply IH; [intros X; apply Ns; right; exact X | intros X; apply Nt; right; exact X | exact H].
  + lia.
  + lia.
Qed.

(* the bytes of a C string of a reader, through its NUL, are mapped *)
Lemma cm_strz_mapped : forall rd p s, sa_strz rd p s ->
  forall a, p <= a < p + Z.of_nat (length s) + 1 -> rd a <> None.
Proof.
intros rd p s [HZ _] a Ha.
assert (Hi : (Z.to_nat (a - p) < length (s ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
specialize (HZ _ Hi). rewrite Z2Nat.id in HZ by lia. replace (p + (a - p)) with a in HZ by lia.
rewrite HZ. discriminate.
Qed.

(* a sub-range of a range sa_addr states keeps its shadow facts *)
Lemma cm_addr_sub : forall rd q n x m, sa_addr rd q n -> q <= x -> 0 < m -> x + m <= q + n ->
  0 <= x /\ x + m <= 2 ^ 63 /\ amem_range x m /\ range_addressable rd SHADOW_OFF x m /\ shadow_hull_vis rd x m.
Proof.
intros rd q n x m (H0 & H1 & H2 & H3 & H4) Hx Hm Hxm.
split; [lia|]. split; [lia|]. split; [unfold amem_range in *; lia|]. split.
- intros y Hy. apply H3. lia.
- intros s Hs. apply H4; [lia|]. unfold shadow_addr in *.
  assert (D1 : (SHADOW_OFF + q / 8) / 8 * 8 <= (SHADOW_OFF + x / 8) / 8 * 8).
  { apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
    pose proof (Z.div_le_mono q x 8 ltac:(lia) Hx). lia. }
  assert (D2 : (SHADOW_OFF + (x + m - 1) / 8) / 8 * 8 <= (SHADOW_OFF + (q + n - 1) / 8) / 8 * 8).
  { apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
    pose proof (Z.div_le_mono (x + m - 1) (q + n - 1) 8 ltac:(lia) ltac:(lia)). lia. }
  lia.
Qed.
