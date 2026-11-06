(* reac-pw/fuzz_segconf, image A, _s18 (segment S09 of LLVMFuzzerTestOneInput's ASan walk): the pure and
   reader-level lemmas that give the premises of S09's callees (check_segments, reac_segconf_role, check_role,
   reac_segconf_model, check_model, reac_segconf_ignored, check_ignore, reac_segconf_role_file,
   reac_segconf_ignore_file, check_provenance) from the reader and model blocks (sa_rconf, sa_mconf) and from
   SegModel.segconf_agrees. Ported from the plain build's M02_bridge.v / MainBPure.v (memory bytes_at) to the
   reader forms of SegABase.v (sa_bytes, sa_str, sa_ostr, sa_val, sa_mseg, sa_addr). No machine semantics.
   rule 24: proves no function (kind: model lemma; reader-level encoding lemmas for segment S09). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ============================== lists ============================== *)
Lemma s18k_nth_firstn : forall {A} (l : list A) n i d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
  intros A l. induction l as [|x l IH]; intros n i d H.
  - destruct n; cbn [firstn]; destruct i; reflexivity.
  - destruct n as [|n]; [lia|]. cbn [firstn]. destruct i as [|i]; [reflexivity|]. cbn [nth]. apply IH. lia.
Qed.

Lemma s18k_nth_skipn : forall {A} (l : list A) k i d, nth i (skipn k l) d = nth (k + i) l d.
Proof.
  intros A l k. revert l. induction k as [|k IH]; intros l i d; [reflexivity|].
  destruct l as [|x l]; [cbn [skipn]; destruct i; reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.

Lemma s18k_fld_fld : forall (bs : list byte) k len off n, (off + n <= len)%nat ->
  seg_spec.fld off n (seg_spec.fld k len bs) = seg_spec.fld (k + off) n bs.
Proof.
  intros bs k len off n H. unfold seg_spec.fld.
  rewrite skipn_firstn_comm, firstn_firstn, skipn_skipn.
  replace (Nat.min n (len - off)) with n by lia. f_equal. f_equal. lia.
Qed.

Lemma s18k_nth_le : forall n z k, (k < n)%nat ->
  nth k (Z_to_le_bytes n z) ZB0 = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|].
  cbn [Z_to_le_bytes]. destruct k as [|k].
  - cbn [nth]. replace (8 * Z.of_nat 0) with 0 by reflexivity. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [nth]. rewrite IH by lia. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

Lemma s18k_le4_nth : forall v k, 0 <= v < 2 ^ 32 -> (k < 4)%nat ->
  bv_unsigned (nth k (Z_to_le_bytes 4 (bv_unsigned (Z_to_bv 64 v))) ZB0) = le_byte v 4 k.
Proof.
  intros v k Hv Hk. rewrite s18k_nth_le by exact Hk. rewrite !Z_to_bv_unsigned.
  unfold le_byte, bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. change (2 ^ Z.of_N 64) with 18446744073709551616.
  change (8 * Z.of_nat 4) with 32. change (2 ^ 32) with 4294967296 in *.
  rewrite (Z.mod_small v 18446744073709551616) by lia. rewrite (Z.mod_small v 4294967296) by lia.
  reflexivity.
Qed.

(* ============================== bytes and strings through the reader ============================== *)
Lemma s18k_bytes_fld : forall rd a bs k n, sa_bytes rd a bs -> (k + n <= length bs)%nat ->
  sa_bytes rd (a + Z.of_nat k) (seg_spec.fld k n bs).
Proof.
  intros rd a bs k n B Hk i Hi. unfold seg_spec.fld in *. rewrite length_firstn, length_skipn in Hi.
  rewrite s18k_nth_firstn by lia. rewrite s18k_nth_skipn.
  replace (a + Z.of_nat k + Z.of_nat i) with (a + Z.of_nat (k + i)) by lia. unfold sa_bytes in B. apply B. lia.
Qed.

Lemma s18k_nth_zs : forall f i, (i < length f)%nat -> nth i (seg_spec.zs f) 0 = bv_unsigned (nth i f ZB0).
Proof.
  unfold seg_spec.zs. induction f as [|b f IH]; intros i Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i]; cbn [map nth]; [reflexivity|]. apply IH. lia.
Qed.

Lemma s18k_strz : forall rd a f cap s, sa_bytes rd a f -> seg_spec.cstr_enc cap s f -> sa_strz rd a s.
Proof.
  intros rd a f cap s B (Lf & Ls & Nn & E). unfold sa_bytes in B. split; [|exact Nn].
  intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  rewrite B by lia. f_equal.
  rewrite <- E. rewrite s18k_nth_firstn by lia. rewrite s18k_nth_zs by lia. reflexivity.
Qed.

Lemma s18k_tail : forall rd a bs e, sa_bytes rd a bs -> a <= e -> e + 8 <= a + Z.of_nat (length bs) ->
  sa_tail rd e.
Proof.
  intros rd a bs e B H1 H2 x Hx. unfold sa_bytes in B.
  pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as M.
  assert (Hi : (Z.to_nat (x - a) < length bs)%nat) by lia.
  pose proof (B _ Hi) as R. rewrite Z2Nat.id in R by lia.
  replace (a + (x - a)) with x in R by lia. rewrite R. discriminate.
Qed.

(* A char[cap] field [k, k + cap) of the bytes bs at a holding s, with 8 bytes of the block after its NUL: the C
   string and its tail. *)
Lemma s18k_fld_str : forall rd a bs k cap s, sa_bytes rd a bs -> (k + cap <= length bs)%nat ->
  seg_spec.cstr_enc cap s (seg_spec.fld k cap bs) -> (k + length s + 8 <= length bs)%nat ->
  sa_str rd (a + Z.of_nat k) s.
Proof.
  intros rd a bs k cap s B Hk E Hl. split.
  - exact (s18k_strz rd _ _ cap s (s18k_bytes_fld rd a bs k cap B Hk) E).
  - apply (s18k_tail rd a bs _ B); lia.
Qed.

(* A u32 field [k, k + 4) of the bytes bs at a: its value as sa_val. *)
Lemma s18k_u32_val : forall rd a bs k v, sa_bytes rd a bs -> (k + 4 <= length bs)%nat ->
  seg_spec.u32_enc v (seg_spec.fld k 4 bs) -> sa_val rd (a + Z.of_nat k) 4 v.
Proof.
  intros rd a bs k v B Hk (Uv & Ue) j Hj.
  pose proof (s18k_bytes_fld rd a bs k 4 B Hk) as Bf. rewrite Ue in Bf. unfold sa_bytes in Bf.
  rewrite Bf by exact Hj. f_equal. exact (s18k_le4_nth v j Uv Hj).
Qed.

(* ============================== the reader's block, struct reac_segconf ============================== *)
Lemma s18k_rfind_go : forall l nm k i, SegModel.r_find_go l nm k = Some i -> (k <= i < k + length l)%nat.
Proof.
  induction l as [|s l IH]; intros nm k i H; cbn [SegModel.r_find_go] in H; [discriminate|].
  match type of H with context [if ?b then _ else _] => destruct b end;
    [injection H as <-; cbn [length]; lia|].
  apply IH in H. cbn [length]. lia.
Qed.

Lemma s18k_rfind_lt : forall rc nm i, SegModel.r_find rc nm = Some i -> (i < length (SegModel.rc_seg rc))%nat.
Proof. intros rc nm i H. unfold SegModel.r_find in H. apply s18k_rfind_go in H. lia. Qed.

(* A char[cap] field [off, off + cap) of the entry c->seg[i]: its C string with the tail, inside c's block. *)
Lemma s18k_rfield : forall rd c bs i off cap s, sa_bytes rd c bs -> Z.of_nat (length bs) = seg_spec.SEG_C_SIZE ->
  (i < 32)%nat -> (off + cap <= 356)%nat ->
  seg_spec.cstr_enc cap s (seg_spec.fld off cap (seg_spec.fld (356 * i) 356 bs)) ->
  sa_str rd (c + 356 * Z.of_nat i + Z.of_nat off) s /\
  c + 356 * Z.of_nat i + Z.of_nat off + Z.of_nat (length s) + 1 <= c + seg_spec.SEG_C_SIZE /\ (length s < cap)%nat.
Proof.
  intros rd c bs i off cap s B L Hi Ho E.
  rewrite s18k_fld_fld in E by lia. unfold seg_spec.SEG_C_SIZE in *.
  pose proof E as (Lf & Ls & _).
  replace (c + 356 * Z.of_nat i + Z.of_nat off) with (c + Z.of_nat (356 * i + off)) by lia.
  split; [apply (s18k_fld_str rd c bs (356 * i + off) cap s B); [lia | exact E | lia]|].
  split; lia.
Qed.

(* ============================== the checks (A1-A3) ============================== *)
Lemma s18k_bytes_ok : forall inp : list byte, Forall (fun b => 0 <= b < 256) (seg_spec.seg_in inp).
Proof.
  intros inp. unfold seg_spec.seg_in, seg_spec.zs. apply Forall_map, Forall_forall. intros b _.
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. exact R.
Qed.

Lemma s18k_harness_ok : forall inp : list byte, SegModel.harness_ok (seg_spec.seg_pay inp) = true.
Proof. intros inp. exact (SegModel.segconf_agrees (seg_spec.seg_in inp) (s18k_bytes_ok inp)). Qed.

Lemma s18k_checks_of : forall p, SegModel.harness_ok p = true ->
  SegModel.check_segments (seg_spec.seg_rc (SegModel.run p)) (seg_spec.seg_mc (SegModel.run p))
    (seg_spec.seg_ret (SegModel.run p)) = true /\
  forallb (SegModel.check_seg (seg_spec.seg_rc (SegModel.run p))) (SegModel.mc_seg (seg_spec.seg_mc (SegModel.run p)))
    = true.
Proof.
  intros p H. unfold SegModel.harness_ok in H. revert H. unfold seg_spec.seg_rc, seg_spec.seg_mc, seg_spec.seg_ret.
  destruct (SegModel.run p) as [[c m] ret]. cbn [fst snd]. intros H. cbv beta iota zeta in H.
  apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [H1 H2].
  split; assumption.
Qed.

Lemma s18_harness : forall pl : list byte,
  let p := seg_spec.seg_pay pl in
  SegModel.check_segments (seg_spec.seg_rc (SegModel.run p)) (seg_spec.seg_mc (SegModel.run p)) (seg_spec.seg_ret (SegModel.run p)) = true /\
  forallb (SegModel.check_seg (seg_spec.seg_rc (SegModel.run p))) (SegModel.mc_seg (seg_spec.seg_mc (SegModel.run p))) = true.
Proof. intros pl p. exact (s18k_checks_of p (s18k_harness_ok pl)). Qed.

Lemma s18_check_seg_nth : forall rc l i, forallb (SegModel.check_seg rc) l = true -> (i < length l)%nat ->
  SegModel.check_seg rc (nth i l SegModel.mseg_d) = true.
Proof.
  intros rc l i H Hi. rewrite forallb_forall in H. apply H. apply nth_In. exact Hi.
Qed.

Lemma s18_check_seg_split : forall rc g, SegModel.check_seg rc g = true ->
  (match SegModel.r_role rc (SegModel.ms_name g) with Some r => SegModel.ms_role_set g && (r =? SegModel.ms_role g) | None => negb (SegModel.ms_role_set g) end) = true /\
  SegModel.same_text (SegModel.r_model rc (SegModel.ms_name g)) (if SegModel.ms_model_set g then Some (SegModel.ms_model g) else None) = true /\
  Bool.eqb (SegModel.r_ignored rc (SegModel.ms_name g)) (SegModel.ms_ignore g) = true /\
  SegModel.same_text (SegModel.r_role_file rc (SegModel.ms_name g)) (if SegModel.ms_role_set g then Some (SegModel.ms_role_file g) else None) = true /\
  SegModel.same_text (SegModel.r_ignore_file rc (SegModel.ms_name g)) (if SegModel.ms_ignore_set g then Some (SegModel.ms_ignore_file g) else None) = true.
Proof.
  intros rc g H. unfold SegModel.check_seg in H. cbv zeta in H.
  apply andb_true_iff in H as [H H5]. apply andb_true_iff in H as [H H4].
  apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4 | exact H5].
Qed.

(* ============================== the model's block, struct mconf (A4) ============================== *)
Lemma s18_mconf_len : forall rd m mc, sa_mconf rd m mc -> (length (SegModel.mc_seg mc) <= 32)%nat.
Proof. intros rd m mc (bs & B & L & L32 & _). exact L32. Qed.

Lemma s18_mconf_n : forall rd m mc, sa_mconf rd m mc ->
  sa_val rd (m + seg_spec.MC_N) 4 (Z.of_nat (length (SegModel.mc_seg mc))).
Proof.
  intros rd m mc (bs & B & L & L32 & _ & UN & _).
  unfold seg_spec.SEG_M_SIZE in L. unfold seg_spec.fldz in UN. change (Z.to_nat 4) with 4%nat in UN.
  replace (m + seg_spec.MC_N) with (m + Z.of_nat (Z.to_nat seg_spec.MC_N)) by (unfold seg_spec.MC_N; lia).
  apply (s18k_u32_val rd m bs (Z.to_nat seg_spec.MC_N) _ B); [unfold seg_spec.MC_N; lia | exact UN].
Qed.

Lemma s18_mseg : forall rd m mc i, sa_mconf rd m mc -> (i < length (SegModel.mc_seg mc))%nat ->
  sa_mseg rd (seg_spec.mseg_addr m i) (nth i (SegModel.mc_seg mc) SegModel.mseg_d).
Proof.
  intros rd m mc i (bs & B & L & L32 & HS & _) Hi.
  exists (seg_spec.fld (256 * i) 256 bs). split; [|exact (HS i Hi)].
  unfold seg_spec.SEG_M_SIZE in L. unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE.
  replace (m + 256 * Z.of_nat i) with (m + Z.of_nat (256 * i)) by lia.
  apply s18k_bytes_fld; [exact B | lia].
Qed.

Lemma s18_mname : forall rd m mc i, sa_mconf rd m mc -> m mod 16 = 0 -> (i < length (SegModel.mc_seg mc))%nat ->
  sa_str rd (seg_spec.mseg_addr m i) (SegModel.ms_name (nth i (SegModel.mc_seg mc) SegModel.mseg_d)) /\
  (length (SegModel.ms_name (nth i (SegModel.mc_seg mc) SegModel.mseg_d)) < 16)%nat.
Proof.
  intros rd m mc i (bs & B & L & L32 & HS & _) _ Hi.
  destruct (HS i Hi) as (Lf & En & _).
  unfold seg_spec.SEG_M_SIZE in L.
  rewrite s18k_fld_fld in En by lia. rewrite Nat.add_0_r in En.
  pose proof En as (_ & Ls & _).
  unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE.
  replace (m + 256 * Z.of_nat i) with (m + Z.of_nat (256 * i)) by lia.
  split; [|exact Ls].
  apply (s18k_fld_str rd m bs (256 * i) 16 _ B); [lia | exact En | lia].
Qed.

(* ============================== the reader's block, struct reac_segconf (A5) ============================== *)
Lemma s18_role_rng : forall rd c rc nm v, sa_rconf rd c rc -> SegModel.r_role rc nm = Some v -> 0 <= v < 2 ^ 31.
Proof.
  intros rd c rc nm v (bs & B & L & L32 & HS & _) H. unfold SegModel.r_role in H.
  destruct (SegModel.r_find rc nm) as [i|] eqn:EF; [|discriminate].
  destruct (SegModel.rs_role_set (SegModel.r_seg rc i)); [|discriminate]. injection H as <-.
  pose proof (s18k_rfind_lt rc nm i EF) as Hi.
  destruct (HS i Hi) as (_ & _ & ((R1 & _) & R2) & _). unfold SegModel.r_seg. lia.
Qed.

Lemma s18_model_str : forall rd c rc nm, sa_rconf rd c rc -> c mod 16 = 0 -> 0 < c ->
  sa_ostr rd (seg_spec.model_ptr c rc nm) (SegModel.r_model rc nm) /\
  (forall s, SegModel.r_model rc nm = Some s -> c <= seg_spec.model_ptr c rc nm /\
     seg_spec.model_ptr c rc nm + Z.of_nat (length s) + 1 <= c + seg_spec.SEG_C_SIZE /\ (length s < 24)%nat).
Proof.
  intros rd c rc nm (bs & B & L & L32 & HS & _) _ Hc.
  unfold seg_spec.model_ptr, SegModel.r_model.
  destruct (SegModel.r_find rc nm) as [i|] eqn:EF; [|split; [reflexivity | discriminate]].
  pose proof (s18k_rfind_lt rc nm i EF) as Hi.
  destruct (HS i Hi) as (_ & _ & _ & _ & _ & _ & Em & _).
  unfold SegModel.r_seg.
  lazymatch goal with |- context [if ?b then Some _ else None] => destruct b end;
    [|split; [reflexivity | discriminate]].
  unfold seg_spec.fldz, seg_spec.RS_MODEL in Em.
  change (Z.to_nat 36) with 36%nat in Em. change (Z.to_nat 24) with 24%nat in Em.
  destruct (s18k_rfield rd c bs i 36 24 _ B L ltac:(lia) ltac:(lia) Em) as (Hs & Hb & Hl).
  cbv beta iota. unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE, seg_spec.RS_MODEL.
  change (Z.of_nat 36) with 36 in Hs, Hb.
  split; [split; [lia | exact Hs]|].
  intros s Es. injection Es as <-. split; [lia|]. split; [exact Hb | exact Hl].
Qed.

Lemma s18_role_file_str : forall rd c rc nm, sa_rconf rd c rc -> c mod 16 = 0 -> 0 < c ->
  sa_ostr rd (seg_spec.role_file_ptr c rc nm) (SegModel.r_role_file rc nm) /\
  (forall s, SegModel.r_role_file rc nm = Some s -> c <= seg_spec.role_file_ptr c rc nm /\
     seg_spec.role_file_ptr c rc nm + Z.of_nat (length s) + 1 <= c + seg_spec.SEG_C_SIZE /\ (length s < 96)%nat).
Proof.
  intros rd c rc nm (bs & B & L & L32 & HS & _) _ Hc.
  unfold seg_spec.role_file_ptr, SegModel.r_role_file.
  destruct (SegModel.r_find rc nm) as [i|] eqn:EF; [|split; [reflexivity | discriminate]].
  pose proof (s18k_rfind_lt rc nm i EF) as Hi.
  destruct (HS i Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Ef & _).
  unfold SegModel.r_seg.
  lazymatch goal with |- context [if ?b then Some _ else None] => destruct b end;
    [|split; [reflexivity | discriminate]].
  unfold seg_spec.fldz, seg_spec.RS_ROLE_FILE in Ef.
  change (Z.to_nat 160) with 160%nat in Ef. change (Z.to_nat 96) with 96%nat in Ef.
  destruct (s18k_rfield rd c bs i 160 96 _ B L ltac:(lia) ltac:(lia) Ef) as (Hs & Hb & Hl).
  cbv beta iota. unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE, seg_spec.RS_ROLE_FILE.
  change (Z.of_nat 160) with 160 in Hs, Hb.
  split; [split; [lia | exact Hs]|].
  intros s Es. injection Es as <-. split; [lia|]. split; [exact Hb | exact Hl].
Qed.

Lemma s18_ignore_file_str : forall rd c rc nm, sa_rconf rd c rc -> c mod 16 = 0 -> 0 < c ->
  sa_ostr rd (seg_spec.ignore_file_ptr c rc nm) (SegModel.r_ignore_file rc nm) /\
  (forall s, SegModel.r_ignore_file rc nm = Some s -> c <= seg_spec.ignore_file_ptr c rc nm /\
     seg_spec.ignore_file_ptr c rc nm + Z.of_nat (length s) + 1 <= c + seg_spec.SEG_C_SIZE /\ (length s < 96)%nat).
Proof.
  intros rd c rc nm (bs & B & L & L32 & HS & _) _ Hc.
  unfold seg_spec.ignore_file_ptr, SegModel.r_ignore_file.
  destruct (SegModel.r_find rc nm) as [i|] eqn:EF; [|split; [reflexivity | discriminate]].
  pose proof (s18k_rfind_lt rc nm i EF) as Hi.
  destruct (HS i Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ei & _).
  unfold SegModel.r_seg.
  lazymatch goal with |- context [if ?b then Some _ else None] => destruct b end;
    [|split; [reflexivity | discriminate]].
  unfold seg_spec.fldz, seg_spec.RS_IGNORE_FILE in Ei.
  change (Z.to_nat 256) with 256%nat in Ei. change (Z.to_nat 96) with 96%nat in Ei.
  destruct (s18k_rfield rd c bs i 256 96 _ B L ltac:(lia) ltac:(lia) Ei) as (Hs & Hb & Hl).
  cbv beta iota. unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE, seg_spec.RS_IGNORE_FILE.
  change (Z.of_nat 256) with 256 in Hs, Hb.
  split; [split; [lia | exact Hs]|].
  intros s Es. injection Es as <-. split; [lia|]. split; [exact Hb | exact Hl].
Qed.

Lemma s18_ptr_rng : forall rd c rc nm, sa_rconf rd c rc -> 0 <= c ->
  0 <= seg_spec.model_ptr c rc nm <= c + seg_spec.SEG_C_SIZE /\
  0 <= seg_spec.role_file_ptr c rc nm <= c + seg_spec.SEG_C_SIZE /\
  0 <= seg_spec.ignore_file_ptr c rc nm <= c + seg_spec.SEG_C_SIZE.
Proof.
  intros rd c rc nm (bs & B & L & L32 & _) Hc.
  unfold seg_spec.model_ptr, seg_spec.role_file_ptr, seg_spec.ignore_file_ptr, seg_spec.rseg_addr,
    seg_spec.RSEG_SIZE, seg_spec.RS_MODEL, seg_spec.RS_ROLE_FILE, seg_spec.RS_IGNORE_FILE, seg_spec.SEG_C_SIZE.
  destruct (SegModel.r_find rc nm) as [i|] eqn:EF; [|cbv beta iota; repeat split; lia].
  pose proof (s18k_rfind_lt rc nm i EF) as Hi.
  destruct (SegModel.r_model rc nm), (SegModel.r_role_file rc nm), (SegModel.r_ignore_file rc nm);
    cbv beta iota; repeat split; lia.
Qed.

(* ============================== the shadow facts (A6) ============================== *)
Lemma s18_sa_addr_sub : forall rd q n q' n', sa_addr rd q n -> q <= q' -> q' + n' <= q + n -> 0 <= n' ->
  sa_addr rd q' n'.
Proof.
  intros rd q n q' n' (H0 & H1 & H2 & H3 & H4) Hq Hn Hn'.
  split; [lia|]. split; [lia|]. split.
  { unfold amem_range in *. lia. }
  split.
  { unfold range_addressable in *. intros x Hx. apply H3. lia. }
  intros Hpos. unfold shadow_hull_vis in *. intros s Hs. apply H4; [lia|].
  assert (M : forall a b, a <= b -> shadow_addr a / 8 * 8 <= shadow_addr b / 8 * 8).
  { intros a b Hab. unfold shadow_addr. apply Z.mul_le_mono_nonneg_r; [lia|].
    apply Z.div_le_mono; [lia|]. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
  pose proof (M q q' Hq) as M1. pose proof (M (q' + n' - 1) (q + n - 1) ltac:(lia)) as M2.
  lia.
Qed.
