(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW7bFacts.v at 25d4b718638 (the model of a
   case-0 turn: w7_join_part_small, w7_join4, w7_ent_build_0, w7_js_len, w7_ent_text_js; the frame patterns at G and
   J) and the string facts of proofs/reac-pw/fuzz_role/lib/A/RPgW7bCall.v at 25d4b718638 (w7_chs_nonzero, the param
   table cells and strings) for reac-pw/fuzz_headamp's image B: the definitions are HPgW7bBase's (hw7b_sepb, hw7b_pab,
   hw7b_js, hw7b_e62), the patterns lib/AU/HPgSeg.v's hsu_PG / hsu_PJ at image B's record against lib/AU/HPgMem.v's
   hmu_sh, the table, strings and globals image B's (lib/AU/HPgImgB.v); e62's bytes at J (hw7b_ent_mem_js) are new;
   w7_ -> hw7b_, module paths. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94): the facts the assembly of the walk of
   LLVMFuzzerTestOneInput from G 0x81afc to J 0x82618 uses besides its blocks: the model of case 0 (Model.ent_build on
   a case-0 turn is ent_headamp_key's key with its four parts joined uncut), e62's 104 bytes at J, the frame's shadow
   patterns at G and J, and image B's param table cells (ent_headamp_key.param at 0x9c600), strings and the
   registered global holding the table. Proves no function (kind: model lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgImgB HPgMem HPgSeg HPgW7bBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ====================== the model of a case-0 turn ====================== *)
Lemma hw7b_param_len : forall p, (length (hw7b_pab p) <= 9)%nat.
Proof.
intros p. unfold hw7b_pab. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as H.
assert (Hc : p mod 8 = 0 \/ p mod 8 = 1 \/ p mod 8 = 2 \/ p mod 8 = 3 \/ p mod 8 = 4 \/ p mod 8 = 5 \/ p mod 8 = 6 \/ p mod 8 = 7) by lia.
destruct Hc as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; vm_compute; lia.
Qed.
Lemma hw7b_sep_len : forall p, (length (hw7b_sepb p) <= 1)%nat.
Proof. intros p. unfold hw7b_sepb. destruct (Z.testbit p 7); vm_compute; lia. Qed.
Lemma hw7b_hpfx_len : length HPFX = 13%nat.
Proof. reflexivity. Qed.

Lemma hw7b_join_part_small : forall t s, (length t + length s < 96)%nat -> join_part t s = t ++ s.
Proof.
intros t s H. unfold join_part.
destruct (Nat.leb_spec 96 (length t + length s)) as [H1|H1]; [lia|]. rewrite firstn_all. reflexivity.
Qed.
Lemma hw7b_join4 : forall a b c d, (length a + length b + length c + length d < 96)%nat ->
join_parts [a; b; c; d] = a ++ b ++ c ++ d.
Proof.
intros a b c d H. unfold join_parts. cbn [fold_left].
rewrite (hw7b_join_part_small [] a) by (cbn; lia). cbn [app].
rewrite (hw7b_join_part_small a b) by lia.
rewrite (hw7b_join_part_small (a ++ b) c) by (rewrite length_app; lia).
rewrite (hw7b_join_part_small ((a ++ b) ++ c) d) by (rewrite !length_app in *; lia).
rewrite <- !app_assoc. reflexivity.
Qed.

Lemma hw7b_len4 : forall (chs : list byte) p, (length chs <= 21)%nat ->
(length HPFX + length chs + length (hw7b_sepb p) + length (hw7b_pab p) < 96)%nat.
Proof.
intros chs p H. pose proof (hw7b_param_len p) as H1. pose proof (hw7b_sep_len p) as H2.
rewrite hw7b_hpfx_len. lia.
Qed.

(* ent_build of a case-0 turn: the key ent_text makes of the four parts *)
Lemma hw7b_ent_build_0 : forall rr chs pb r, fst (Cursor.fuzz_u8 rr) mod 10 = 0 -> (chs, pb, r) = hsu_g_of rr ->
(length chs <= 21)%nat ->
ent_build rr = (ent_text (hw7b_js chs pb) true, r).
Proof.
intros rr chs pb r Hk Hg Hl. unfold ent_build. unfold hsu_g_of in Hg.
destruct (Cursor.fuzz_u8 rr) as [kd r1] eqn:E1. cbn [fst] in Hk. rewrite Hk. cbn [Z.to_nat].
unfold ent_headamp_key.
destruct (Cursor.fuzz_u8 r1) as [c r2]. destruct (Cursor.fuzz_u8 r2) as [p r3]. injection Hg as Hch Hpb Hr.
subst.
unfold hw7b_js. rewrite hw7b_join4; [reflexivity | exact (hw7b_len4 _ _ Hl)].
Qed.
Lemma hw7b_js_len : forall chs p, (length chs <= 21)%nat -> (length (hw7b_js chs p) <= 44)%nat.
Proof.
intros chs p H. unfold hw7b_js. rewrite !length_app, hw7b_hpfx_len.
pose proof (hw7b_param_len p). pose proof (hw7b_sep_len p). lia.
Qed.
Lemma hw7b_ent_text_js : forall chs p, (length chs <= 21)%nat ->
ent_text (hw7b_js chs p) true = Ent POD_STRING (Z.of_nat (length (hw7b_js chs p)) + 1) (hw7b_js chs p ++ [NUL]).
Proof.
intros chs p H. unfold ent_text. pose proof (hw7b_js_len chs p H).
rewrite firstn_all2 by lia. rewrite length_app. cbn [length]. f_equal. lia.
Qed.
(* e62's 104 bytes after the key is written: Layout.ent_mem of the pod *)
Lemma hw7b_ent_mem_js : forall chs p, (length chs <= 21)%nat ->
ent_mem (ent_text (hw7b_js chs p) true) = hw7b_e62 (hw7b_js chs p).
Proof.
intros chs p H. rewrite (hw7b_ent_text_js chs p H). pose proof (hw7b_js_len chs p H) as HL.
unfold ent_mem, hw7b_e62. cbn [e_type e_size e_body]. unfold POD_STRING.
rewrite length_app. cbn [length].
rewrite <- (app_assoc (hw7b_js chs p) [NUL]).
replace (96 - (length (hw7b_js chs p) + 1))%nat with (95 - length (hw7b_js chs p))%nat by lia.
reflexivity.
Qed.
Lemma hw7b_ent_wf_js : forall chs p, (length chs <= 21)%nat -> ent_wf (ent_text (hw7b_js chs p) true).
Proof.
intros chs p H. rewrite (hw7b_ent_text_js chs p H). pose proof (hw7b_js_len chs p H) as HL.
unfold ent_wf. cbn [e_type e_size e_body]. unfold POD_STRING.
rewrite length_app. cbn [length]. split; [lia|]. split; [lia | lia].
Qed.

(* ====================== the frame's shadow at G and at J ====================== *)
Lemma hw7b_PG : hsu_PG headamp_himg_B = hmu_sh true true false false false true false false.
Proof. vm_compute. reflexivity. Qed.
Lemma hw7b_PJ : hsu_PJ headamp_himg_B = hmu_sh false false false false false true false false.
Proof. vm_compute. reflexivity. Qed.

(* ====================== the key's first part ====================== *)
Lemma hw7b_dec64_chk : forallb (fun n => no_nul (dec64 (Z.of_nat n))) (seq 0 64) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma hw7b_no_nul_Forall : forall l, no_nul l = true -> Forall (fun b : byte => bv_unsigned b <> 0) l.
Proof.
intros l H. apply Forall_forall. intros b Hb. unfold no_nul in H.
pose proof (proj1 (forallb_forall _ _) H b Hb) as Hq. cbn beta in Hq.
apply negb_true_iff, Z.eqb_neq in Hq. exact Hq.
Qed.
Lemma hw7b_dec64_nz : forall v, 0 <= v < 64 -> Forall (fun b : byte => bv_unsigned b <> 0) (dec64 v).
Proof.
intros v Hv. apply hw7b_no_nul_Forall.
pose proof (proj1 (forallb_forall _ _) hw7b_dec64_chk (Z.to_nat v) ltac:(apply in_seq; lia)) as Hq.
cbv beta in Hq. rewrite Z2Nat.id in Hq by lia. exact Hq.
Qed.
Lemma hw7b_odd_nz : forall n, no_nul (nth n odd_ch []) = true.
Proof.
intros n. pose proof tables_no_nul as Ht. apply andb_true_iff in Ht as [Ht _].
apply andb_true_iff in Ht as [Ht _]. apply andb_true_iff in Ht as [Ht _]. apply andb_true_iff in Ht as [Ht _].
apply andb_true_iff in Ht as [_ Ho].
destruct (nth_in_or_default n odd_ch []) as [Hin | ->].
- exact (proj1 (forallb_forall _ _) Ho _ Hin).
- reflexivity.
Qed.
Lemma hw7b_chs_nonzero : forall rr chs pb r, (chs, pb, r) = hsu_g_of rr ->
Forall (fun b : byte => bv_unsigned b <> 0) chs.
Proof.
intros rr chs pb r H.
assert (Hc : chs = fst (fst (hsu_g_of rr))) by (rewrite <- H; reflexivity).
clear H. subst chs. unfold hsu_g_of.
destruct (Cursor.fuzz_u8 rr) as [k0 r1]. destruct (Cursor.fuzz_u8 r1) as [c r2] eqn:Ec.
destruct (Cursor.fuzz_u8 r2) as [pb' r3].
cbn [fst]. destruct (c <? 200).
- apply hw7b_dec64_nz. apply Z.mod_pos_bound. lia.
- apply hw7b_no_nul_Forall. exact (hw7b_odd_nz (Z.to_nat (c mod 14))).
Qed.
Lemma hw7b_chs_len : forall rr chs pb r, (chs, pb, r) = hsu_g_of rr -> (length chs <= 21)%nat.
Proof.
intros rr chs pb r H.
assert (Hc : chs = fst (fst (hsu_g_of rr))) by (rewrite <- H; reflexivity).
clear H. subst chs. unfold hsu_g_of.
destruct (Cursor.fuzz_u8 rr) as [k0 r1]. destruct (Cursor.fuzz_u8 r1) as [c r2].
destruct (Cursor.fuzz_u8 r2) as [pb' r3].
cbn [fst]. destruct (c <? 200).
- pose proof (dec64_len (c mod 64)). lia.
- apply nth_len_le. vm_compute. reflexivity.
Qed.
Lemma hw7b_pb_range : forall rr chs pb r, (chs, pb, r) = hsu_g_of rr -> 0 <= pb < 256.
Proof.
intros rr chs pb r H.
assert (Hc : pb = snd (fst (hsu_g_of rr))) by (rewrite <- H; reflexivity).
clear H. subst pb. unfold hsu_g_of.
destruct (Cursor.fuzz_u8 rr) as [k0 r1]. destruct (Cursor.fuzz_u8 r1) as [c r2].
pose proof (fuzz_u8_range r2) as Hr. destruct (Cursor.fuzz_u8 r2) as [pb' r3].
cbn [fst snd] in *. exact Hr.
Qed.

(* ====================== image B's param table, strings and separators ====================== *)
Ltac hw7b_in := repeat (first [left; vm_compute; reflexivity | right]).
(* the strings param[j] points to (ent_headamp_key.param, 0x9c600 + 8 j) *)
Definition hw7b_pptr (j : Z) : Z := nth (Z.to_nat j) [0x21380; 0x213a0; 0x213c0; 0x213e0; 0x21400; 0x21240; 0x21420; 0x21440] 0.
Lemma hw7b_mod8_cases : forall p, 0 <= p ->
p mod 8 = 0 \/ p mod 8 = 1 \/ p mod 8 = 2 \/ p mod 8 = 3 \/ p mod 8 = 4 \/ p mod 8 = 5 \/ p mod 8 = 6 \/ p mod 8 = 7.
Proof. intros p Hp. pose proof (Z.mod_pos_bound p 8 ltac:(lia)). lia. Qed.
Lemma hw7b_param_cell : forall p, 0 <= p -> In (HW7B_PTAB p, hw7b_pptr (p mod 8)) (hi_cells headamp_himg_B).
Proof.
intros p Hp. unfold HW7B_PTAB. cbn [hi_cells headamp_himg_B]. unfold headamp_B_cells. cbn [In].
destruct (hw7b_mod8_cases p Hp) as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; hw7b_in.
Qed.
Lemma hw7b_param_str : forall p, 0 <= p -> In (hw7b_pptr (p mod 8), hd_zbytes (hw7b_pab p)) (hi_strs headamp_himg_B).
Proof.
intros p Hp. unfold hw7b_pab. cbn [hi_strs headamp_himg_B]. unfold headamp_B_strs. cbn [In].
destruct (hw7b_mod8_cases p Hp) as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; hw7b_in.
Qed.
Lemma hw7b_hpfx_str : In (HW7B_HPFX, hd_zbytes HPFX) (hi_strs headamp_himg_B).
Proof. cbn [hi_strs headamp_himg_B]. unfold headamp_B_strs. cbn [In]. hw7b_in. Qed.
Lemma hw7b_sep_str : forall p, In (hw7b_sep p, hd_zbytes (hw7b_sepb p)) (hi_strs headamp_himg_B).
Proof.
intros p. unfold hw7b_sep, hw7b_sepb. cbn [hi_strs headamp_himg_B]. unfold headamp_B_strs.
destruct (Z.testbit p 7); cbn [In]; hw7b_in.
Qed.
Lemma hw7b_param_glob : forall p, 0 <= p ->
exists g, In g (hi_globs headamp_himg_B) /\ fst g <= HW7B_PTAB p /\ HW7B_PTAB p + 8 <= fst g + snd g.
Proof.
intros p Hp. exists (0x9c600, 64). split.
- cbn [hi_globs headamp_himg_B]. unfold headamp_B_globs. cbn [In]. hw7b_in.
- unfold HW7B_PTAB. cbn [fst snd]. pose proof (Z.mod_pos_bound p 8 ltac:(lia)). lia.
Qed.
Lemma hw7b_rz : hi_rz headamp_himg_B = [(0x180, 8)].
Proof. reflexivity. Qed.

Print Assumptions hw7b_ent_build_0.
Print Assumptions hw7b_ent_mem_js.
Print Assumptions hw7b_ent_wf_js.
Print Assumptions hw7b_PG.
Print Assumptions hw7b_PJ.
Print Assumptions hw7b_chs_nonzero.
Print Assumptions hw7b_chs_len.
Print Assumptions hw7b_pb_range.
Print Assumptions hw7b_param_cell.
Print Assumptions hw7b_param_str.
Print Assumptions hw7b_hpfx_str.
Print Assumptions hw7b_sep_str.
Print Assumptions hw7b_param_glob.
