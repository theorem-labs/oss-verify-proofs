(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the kit of segment F of LLVMFuzzerTestOneInput's ASan walk (plugin-hostd/fuzz_command, 0x86974 .. 0x8699c: the three frees of the words blocks and the latch), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACbk.v (wcb_entry: the symbolic seed of a point of the function) and A/ACh2.v:122-290 (the step through a call and back, with the facts carried over it). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/LLVMFuzzerTestOneInput_s70.v, with its module paths changed; 855 of its 936 lines of code are new or changed and 347 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan, pin sha256 48c5355bdacb): the kit of file group _s24, segments
   S16 .. S20 of the test harness's entry function LLVMFuzzerTestOneInput (0x85bd0 .. 0x85c40). No function of the
   binary is proved here: these are the lemmas the segment file LLVMFuzzerTestOneInput_s24.v applies.

   - the model facts check_declared asks (m_declared's answer bounded, SegModel.segconf_agrees's last check, each
     table entry's parent a C string with its tail), from the plain / UBSan owner's SegModel and seg_spec;
   - the walk's own facts at a cut: the frame chain at sp = S1 with s0 = SP0 (fuzz_command's chain_words_s2.v
     cw2_chain at origin/ossv/recipes 501c0d516c69, the frame record ra / s0 at SP0 - 8 / SP0 - 16), the live
     blocks are distinct, a harness block's facts from AR (lt_hblk), what a cut keeps across a step (the stack
     [S1, SP0), the frame's header and flag words, its 36 shadow bytes, the image bytes the runtime does not own);
   - one free (fuzz_command's LLVMFuzzerTestOneInput_s70.v ltf_free): the run `mv a0, s<x>; jal free` at one of
     the four pcs 0x85c14, 0x85c1c, 0x85c24, 0x85c2c and the free wrapper's rule afree04_rule, back at pc + 8. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaNoChain PaDenot PaSB
  PaLibF.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_c SegInstA
  LLVMFuzzerTestOneInput_inst LLVMFuzzerTestOneInput_defs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
  reac_declared_vlan_add_c reac_segconf_declared_c check_declared_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_s10k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Local Open Scope Z_scope.

(* ================================== the model facts check_declared asks ================================== *)
(* m_declared's answer: -1 (the table filled up) or the entries added, at most one per segment *)
Lemma s24_mdecl_rng : forall ms tab cap a, 0 <= a ->
  fst (SegModel.m_decl_go ms tab cap a) = -1 \/
  a <= fst (SegModel.m_decl_go ms tab cap a) <= a + Z.of_nat (length ms).
Proof.
  induction ms as [|g r IH]; intros tab cap a Ha; cbn [SegModel.m_decl_go length].
  - right. cbn [fst]. lia.
  - destruct (SegModel.ms_ignore g).
    + destruct (IH tab cap a Ha) as [E | E]; [left; exact E | right; lia].
    + destruct (SegModel.m_split (SegModel.ms_name g)) as [[p v]|].
      * match goal with |- context [existsb ?f tab] => destruct (existsb f tab) end.
        -- destruct (IH tab cap a Ha) as [E | E]; [left; exact E | right; lia].
        -- destruct (cap <=? Z.of_nat (length tab)).
           ++ left. reflexivity.
           ++ destruct (IH (tab ++ [(p, v)]) cap (a + 1) ltac:(lia)) as [E | E]; [left; exact E | right; lia].
      * destruct (IH tab cap a Ha) as [E | E]; [left; exact E | right; lia].
Qed.

Lemma s24_mdecl_bnd : forall mc tab cap, (length (SegModel.mc_seg mc) <= 32)%nat ->
  - 2 ^ 31 <= fst (SegModel.m_declared mc tab cap) < 2 ^ 31.
Proof.
  intros mc tab cap Hl. unfold SegModel.m_declared.
  change (2 ^ 31) with 2147483648.
  destruct (s24_mdecl_rng (SegModel.mc_seg mc) tab cap 0 ltac:(lia)) as [E | E]; lia.
Qed.

(* the harness's last check (vlans_are of the two answers), from the agreement theorem on the decoded payload *)
Lemma s24_vlans : forall pl : list byte,
  SegModel.vlans_are
    (SegModel.r_declared (seg_spec.seg_rc (SegModel.run (seg_spec.seg_pay pl))) (seg_spec.seg_tab0 pl) (seg_spec.seg_cap pl))
    (SegModel.m_declared (seg_spec.seg_mc (SegModel.run (seg_spec.seg_pay pl))) (seg_spec.seg_tab0 pl) (seg_spec.seg_cap pl))
    (seg_spec.seg_cap pl) = true.
Proof.
  intros pl.
  assert (HF : Forall (fun b => 0 <= b < 256) (seg_spec.seg_in pl)).
  { unfold seg_spec.seg_in, seg_spec.zs. apply Forall_forall. intros z Hz.
    apply in_map_iff in Hz. destruct Hz as [b [Eb _]]. subst z.
    pose proof (bv_unsigned_in_range _ b) as R. change (bv_modulus 8) with 256 in R. lia. }
  assert (H : SegModel.harness_ok (seg_spec.seg_pay pl) = true) by exact (SegModel.segconf_agrees _ HF).
  unfold SegModel.harness_ok in H.
  unfold seg_spec.seg_tab0, seg_spec.seg_cap, seg_spec.seg_rc, seg_spec.seg_mc.
  revert H. destruct (SegModel.run (seg_spec.seg_pay pl)) as [[c m] ret]. intros H.
  cbv beta iota in H. cbn [fst snd].
  apply andb_prop in H. destruct H as [_ H]. exact H.
Qed.

Lemma s24m_nth_firstn : forall (A : Type) (l : list A) n j d, (j < n)%nat -> nth j (firstn n l) d = nth j l d.
Proof.
  intros A l. induction l as [|x l IH]; intros n j d Hj.
  - destruct n as [|n]; [lia|]. reflexivity.
  - destruct n as [|n]; [lia|]. destruct j as [|j]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.
Lemma s24m_nth_skipn : forall (A : Type) (l : list A) off j d, nth j (skipn off l) d = nth (off + j) l d.
Proof.
  intros A l off. revert l. induction off as [|off IH]; intros l j d; [reflexivity|].
  destruct l as [|x l].
  - cbn [skipn]. destruct j; reflexivity.
  - cbn [skipn]. rewrite IH. reflexivity.
Qed.
Lemma s24m_nth_fld : forall (bs : list byte) off n j d, (j < n)%nat ->
  nth j (seg_spec.fld off n bs) d = nth (off + j) bs d.
Proof.
  intros bs off n j d Hj. unfold seg_spec.fld. rewrite s24m_nth_firstn by exact Hj. apply s24m_nth_skipn.
Qed.
Lemma s24m_nth_zs : forall (g : list byte) j, (j < length g)%nat ->
  nth j (seg_spec.zs g) 0 = bv_unsigned (nth j g ZB0).
Proof.
  unfold seg_spec.zs. induction g as [|b g IH]; intros j Hj; cbn [length] in Hj; [lia|].
  destruct j as [|j]; cbn [nth map]; [reflexivity|]. apply IH. lia.
Qed.
Lemma s24m_bytes_fld : forall rd a (bs : list byte) off n, sa_bytes rd a bs ->
  sa_bytes rd (a + Z.of_nat off) (seg_spec.fld off n bs).
Proof.
  intros rd a bs off n H. unfold sa_bytes in *. intros j Hj.
  assert (Hl : length (seg_spec.fld off n bs) = Nat.min n (length bs - off)).
  { unfold seg_spec.fld. rewrite length_firstn, length_skipn. reflexivity. }
  rewrite Hl in Hj.
  rewrite s24m_nth_fld by lia.
  replace (a + Z.of_nat off + Z.of_nat j) with (a + Z.of_nat (off + j)) by lia.
  apply H. lia.
Qed.
Lemma s24m_strz_cstr : forall rd p (g : list byte) cap s, sa_bytes rd p g -> seg_spec.cstr_enc cap s g ->
  sa_strz rd p s.
Proof.
  intros rd p g cap s Hb (Hlg & Hls & Hn0 & Hf). unfold sa_bytes in Hb.
  unfold sa_strz, sa_zs. split; [|exact Hn0].
  intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
  rewrite <- Hf.
  rewrite s24m_nth_firstn by lia.
  rewrite s24m_nth_zs by lia.
  apply Hb. lia.
Qed.
(* each entry's parent of the reader's table (18-byte entries) and of the model's (20-byte entries) is a C string
   with its tail, the tail inside the block *)
Lemma s24_rtab_str : forall (rd : reader) (tab : Z) (t : list (list Z * Z)),
  sa_rtab rd tab t ->
  (forall x, tab <= x < tab + 18 * Z.of_nat (length t) + 5 -> rd x <> None) ->
  forall i, (i < length t)%nat -> sa_str rd (tab + seg_spec.RVLAN_SIZE * Z.of_nat i) (fst (nth i t ([], 0))).
Proof.
  intros rd tab t (bs & Hb & _ & Hent) Hm i Hi.
  destruct (Hent i Hi) as (_ & Hc & _).
  pose proof (s24m_bytes_fld rd tab bs (18 * i) 18 Hb) as Hb1.
  pose proof (s24m_bytes_fld rd _ _ 0 16 Hb1) as Hb2.
  assert (Ep : tab + Z.of_nat (18 * i) + Z.of_nat 0 = tab + seg_spec.RVLAN_SIZE * Z.of_nat i)
    by (unfold seg_spec.RVLAN_SIZE; lia).
  rewrite Ep in Hb2.
  pose proof (s24m_strz_cstr _ _ _ _ _ Hb2 Hc) as Hz.
  unfold sa_str. split; [exact Hz|].
  destruct Hc as (_ & Hls & _).
  unfold sa_tail. intros x Hx. apply Hm.
  assert (HL : 0 <= Z.of_nat (length (fst (nth i t ([], 0)))) < 16) by lia.
  unfold seg_spec.RVLAN_SIZE in Hx.
  revert HL Hx. generalize (Z.of_nat (length (fst (nth i t ([], 0))))) as L. intros L HL Hx.
  pose proof (Z.mod_pos_bound (tab + 18 * Z.of_nat i + L) 8 ltac:(lia)) as HM.
  revert HM Hx. generalize ((tab + 18 * Z.of_nat i + L) mod 8) as M. intros M HM Hx.
  lia.
Qed.
Lemma s24_mtab_str : forall (rd : reader) (mt : Z) (t : list (list Z * Z)),
  sa_mtab rd mt t ->
  (forall x, mt <= x < mt + 20 * Z.of_nat (length t) + 3 -> rd x <> None) ->
  forall i, (i < length t)%nat -> sa_str rd (mt + seg_spec.MVLAN_SIZE * Z.of_nat i) (fst (nth i t ([], 0))).
Proof.
  intros rd mt t (bs & Hb & _ & Hent) Hm i Hi.
  destruct (Hent i Hi) as (_ & Hc & _).
  pose proof (s24m_bytes_fld rd mt bs (20 * i) 20 Hb) as Hb1.
  pose proof (s24m_bytes_fld rd _ _ 0 16 Hb1) as Hb2.
  assert (Ep : mt + Z.of_nat (20 * i) + Z.of_nat 0 = mt + seg_spec.MVLAN_SIZE * Z.of_nat i)
    by (unfold seg_spec.MVLAN_SIZE; lia).
  rewrite Ep in Hb2.
  pose proof (s24m_strz_cstr _ _ _ _ _ Hb2 Hc) as Hz.
  unfold sa_str. split; [exact Hz|].
  destruct Hc as (_ & Hls & _).
  unfold sa_tail. intros x Hx. apply Hm.
  assert (HL : 0 <= Z.of_nat (length (fst (nth i t ([], 0)))) < 16) by lia.
  unfold seg_spec.MVLAN_SIZE in Hx.
  revert HL Hx. generalize (Z.of_nat (length (fst (nth i t ([], 0))))) as L. intros L HL Hx.
  pose proof (Z.mod_pos_bound (mt + 20 * Z.of_nat i + L) 8 ltac:(lia)) as HM.
  revert HM Hx. generalize ((mt + 20 * Z.of_nat i + L) mod 8) as M. intros M HM Hx.
  lia.
Qed.

(* ============================== readers that agree everywhere, and lists ============================== *)
Lemma s24_pzd_nodup : forall l, (forall x, In x l -> 0 < snd x) -> pairwise zdisjoint l -> List.NoDup l.
Proof.
induction l as [|x l IH]; intros Hp Hd; [constructor|]. destruct Hd as [Hx Hl]. constructor.
- intros Hin. rewrite Forall_forall in Hx. specialize (Hx x Hin). pose proof (Hp x (or_introl eq_refl)).
  unfold zdisjoint in Hx. lia.
- apply IH; [intros y Hy; exact (Hp y (or_intror Hy)) | exact Hl].
Qed.
(* free removes its block from the list at any place: what is left, against the cut's list *)
Lemma s24_perm_free : forall (bl bl2 O R : list (Z * Z)) x,
  Permutation bl ((x :: O) ++ R) ->
  (exists l1 l2, bl = l1 ++ x :: l2 /\ bl2 = l1 ++ l2) ->
  Permutation bl2 (O ++ R).
Proof.
intros bl bl2 O R x HP (l1 & l2 & E1 & E2). subst bl bl2.
apply (Permutation_cons_inv (a := x)).
eapply Permutation_trans; [apply Permutation_middle | exact HP].
Qed.
Lemma s24_sa_zs_ext : forall (rd rd' : reader) a l, (forall x, rd' x = rd x) -> sa_zs rd a l -> sa_zs rd' a l.
Proof. intros rd rd' a l HE H i Hi. rewrite HE. exact (H i Hi). Qed.
Lemma s24_sa_bytes_ext : forall (rd rd' : reader) a l, (forall x, rd' x = rd x) -> sa_bytes rd a l -> sa_bytes rd' a l.
Proof. intros rd rd' a l HE H i Hi. rewrite HE. exact (H i Hi). Qed.
Lemma s24_sa_val_ext : forall (rd rd' : reader) a n v, (forall x, rd' x = rd x) -> sa_val rd a n v -> sa_val rd' a n v.
Proof. intros rd rd' a n v HE H k Hk. rewrite HE. exact (H k Hk). Qed.
Lemma s24_rdword_ext : forall (rd rd' : reader) a, (forall x, rd' x = rd x) -> rdword rd' a = rdword rd a.
Proof. intros rd rd' a HE. apply rdword_ext. intros k _. apply HE. Qed.

(* ---------------- a block's size is its req_size ---------------- *)
Lemma s24n_req : forall n, 0 < n -> req_size n = n.
Proof. intros n Hn. unfold req_size. destruct (n =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity]. Qed.

(* the five registers the frame part of a cut reads (sp, gp, tp, s0, s1), kept from one state to a later one *)
Definition s24_fregs (regs regs2 : bvmap 5 word) : Prop :=
  forall r, (r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9) -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Lemma s24_fregs_of_pres : forall regs regs2, aregs_preserved regs regs2 -> s24_fregs regs regs2.
Proof. intros regs regs2 HP r Hr. apply HP. unfold acallee_saved. lia. Qed.
Lemma s24_fregs_trans : forall r1 r2 r3, s24_fregs r1 r2 -> s24_fregs r2 r3 -> s24_fregs r1 r3.
Proof. intros r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.
Lemma s24_w64_mod : forall z, w64 (z mod 2 ^ 64) = w64 z.
Proof.
intros z. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
apply Zmod_mod.
Qed.
Lemma s24_bytes_range : forall (rd rd' : reader) a (bs : list byte),
  sa_bytes rd a bs -> (forall i, 0 <= i < Z.of_nat (length bs) -> rd' (a + i) = rd (a + i)) -> sa_bytes rd' a bs.
Proof. intros rd rd' a bs H HK i Hi. rewrite HK by lia. exact (H i Hi). Qed.
Lemma s24_mtab_range : forall (rd rd' : reader) mt t,
  sa_mtab rd mt t -> (forall i, 0 <= i < 20 * Z.of_nat (length t) -> rd' (mt + i) = rd (mt + i)) -> sa_mtab rd' mt t.
Proof.
intros rd rd' mt t (bs & Hb & Hl & He) HK. exists bs. split; [|exact (conj Hl He)].
apply (s24_bytes_range rd rd' mt bs Hb). intros i Hi. apply HK. rewrite Hl in Hi. lia.
Qed.
Lemma s24_cm_ext : forall (rd rd' : reader) c m st, (forall x, rd' x = rd x) -> lt_cm rd c m st -> lt_cm rd' c m st.
Proof.
intros rd rd' c m st HE. unfold lt_cm, sa_rconf, sa_mconf, sa_mconfp.
intros [(bs1 & H1 & E1) (bs2 & H2 & E2)].
split; [exists bs1 | exists bs2]; (split; [eapply s24_sa_bytes_ext; eassumption | assumption]).
Qed.
(* the bytes reac_segconf_declared may write: entries of the table and, if it grew, the count cell *)
Lemma s24_vtab_in : forall tab n (t0 t1 : list (list Z * Z)) cap a,
  Z.of_nat (length t1) <= cap -> inFP (vtab_W tab n t0 t1) a ->
  (tab <= a < tab + 18 * (cap + 1)) \/ (n <= a < n + 4).
Proof.
intros tab n t0 t1 cap a Hl (r & Hr & Ha). unfold vtab_W in Hr. apply in_app_or in Hr as [Hr | Hr].
- left. destruct Hr as [<- | []]. cbn [fst snd] in Ha. unfold seg_spec.RVLAN_SIZE in Ha. lia.
- right. destruct (length t0 <? length t1)%nat; [|destruct Hr]. destruct Hr as [<- | []]. cbn [fst snd] in Ha. lia.
Qed.

(* vlans_are's parts the walk uses: the answers agree, the reader's table is not longer than cap *)
Lemma s24_vlans_parts : forall got want cap, SegModel.vlans_are got want cap = true ->
  fst got = fst want /\ Z.of_nat (length (snd got)) <= cap.
Proof.
intros got want cap H. unfold SegModel.vlans_are in H.
apply andb_prop in H as [H H4]. apply andb_prop in H as [H _]. apply andb_prop in H as [H1 _].
apply Z.eqb_eq in H1. apply Z.leb_le in H4. split; assumption.
Qed.
Lemma s24_rtab_ext : forall (rd rd' : reader) a t, (forall x, rd' x = rd x) -> sa_rtab rd a t -> sa_rtab rd' a t.
Proof. intros rd rd' a t HE (bs & Hb & He). exists bs. split; [eapply s24_sa_bytes_ext; eassumption | exact He]. Qed.
Lemma s24_mtab_ext : forall (rd rd' : reader) a t, (forall x, rd' x = rd x) -> sa_mtab rd a t -> sa_mtab rd' a t.
Proof. intros rd rd' a t HE (bs & Hb & He). exists bs. split; [eapply s24_sa_bytes_ext; eassumption | exact He]. Qed.
Lemma s24_guard_ext : forall (rd rd' : reader) tab cap, (forall x, rd' x = rd x) -> sa_guardtab rd tab cap ->
  sa_guardtab rd' tab cap.
Proof. intros rd rd' tab cap HE H. unfold sa_guardtab in *. eapply s24_sa_bytes_ext; eassumption. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a reader at a machine address only depends on the address mod 2 ^ 64 *)
Lemma s24_aview_wrap : forall H (m : word -> option byte) a, aview SEGS H m a = aview SEGS H m (a mod 2 ^ 64).
Proof.
intros H m a. unfold aview, mbyte.
replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Zmod_mod. reflexivity.
Qed.
Lemma s24_keep_all : forall H (m m' : word -> option byte),
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a) -> forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
intros H m m' HK a. rewrite (s24_aview_wrap H m' a), (s24_aview_wrap H m a). apply HK.
apply Z.mod_pos_bound. lia.
Qed.

Lemma s24_tabs_ext : forall cx (rd rd' : reader) tab mt t, (forall x, rd' x = rd x) ->
  lt_tabs cx rd tab mt t -> lt_tabs cx rd' tab mt t.
Proof.
intros cx rd rd' tab mt t HE. unfold lt_tabs, sa_rtab, sa_mtab, sa_guardtab.
intros (H1 & (bs & Hb & Hr) & Hg & Hv & (bs2 & Hb2 & Hm) & H6).
split; [exact H1|]. split; [exists bs; split; [eapply s24_sa_bytes_ext; eassumption | exact Hr]|].
split; [eapply s24_sa_bytes_ext; eassumption|].
split; [eapply s24_sa_val_ext; eassumption|].
split; [exists bs2; split; [eapply s24_sa_bytes_ext; eassumption | exact Hm] | exact H6].
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* the journal from the entry every cut from K84eb8 on holds (lt_frame's first conjunct) *)
Definition s24_J (cx : lcx) ly S (W : world SEGS) mem md (k : Z) : Prop :=
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k.

(* the entry's numbers: sp0 16-aligned, S1 = (sp0 - 320) & ~31 at most 351 below it, the stack window above the
   allocator's ceiling, below 2 ^ 47 *)
Lemma s24_nums : forall cx, lt_base B MT cx ->
  x_sp0 cx mod 16 = 0 /\ x_s1 cx mod 16 = 0 /\ x_sp0 cx - 352 <= x_s1 cx <= x_sp0 cx - 320 /\
  alloc_ceiling + 32768 <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\
  x_sp0 cx <= ly_top (x_ly cx) /\ ly_top (x_ly cx) <= 2 ^ 47.
Proof.
intros cx HB. destruct HB as (HPRE & _).
destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold STK_LLVMFuzzerTestOneInput in *.
unfold x_s1, x_sp0, LT_FRAME.
set (sp := spZ (x_regs cx)) in *.
pose proof (Z.mod_pos_bound (sp - 320) 32 ltac:(lia)) as Hm.
assert (E : sp - 320 - (sp - 320) mod 32 = 32 * ((sp - 320) / 32))
  by (pose proof (Z.div_mod (sp - 320) 32 ltac:(lia)); lia).
rewrite E.
split; [exact Hal16|].
split; [replace (32 * ((sp - 320) / 32)) with (2 * ((sp - 320) / 32) * 16) by ring; apply Z.mod_mul; lia|].
split; [rewrite <- E; lia|]. lia.
Qed.

(* the live blocks of a state are distinct *)
Lemma s24_nodup : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S W mem md HAR.
destruct (ablocks B ly S) as [|[p0 n0] bl] eqn:Eb; [constructor|].
assert (Hin0 : In (p0, n0) (ablocks B ly S)) by (rewrite Eb; left; reflexivity).
destruct (al_blocks _ _ LAWS ly S W mem md p0 n0 HAR Hin0) as (_ & _ & _ & _ & _ & Hpw & _).
rewrite <- Eb. apply (NoDup_map_inv (fun b : Z * Z => (fst b, req_size (snd b)))).
apply s24_pzd_nodup; [|exact Hpw].
intros [a q] Hx. apply in_map_iff in Hx as ([pb nb] & Hq & Hpb). cbn in Hq. injection Hq as <- <-.
destruct (al_blocks _ _ LAWS ly S W mem md pb nb HAR Hpb) as (_ & _ & _ & _ & _ & _ & Hn).
cbn [snd]. pose proof (req_size_pos nb ltac:(lia)). lia.
Qed.

(* the head of the cut's block list is live and is not one of the entry's blocks *)
Lemma s24_blk_head : forall cx ly S (W : world SEGS) mem md pa n O,
  AR SEGS B ly S W mem md -> lt_blocks B cx ly S ((pa, n) :: O) ->
  In (pa, n) (ablocks B ly S) /\ ~ In (pa, n) (x_bl0 B cx) /\ ~ In (pa, n) O.
Proof.
intros cx ly S W mem md pa n O HAR HP.
assert (HND : List.NoDup (ablocks B ly S)) by exact (s24_nodup ly S W mem md HAR).
pose proof (Permutation_NoDup HP HND) as HND2. cbn [app] in HND2.
apply NoDup_cons_iff in HND2 as [Hni _].
split; [apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity|].
split; intros Hb; apply Hni; apply in_or_app; [right | left]; exact Hb.
Qed.
Lemma s24_blk_in : forall cx ly S b O, lt_blocks B cx ly S O -> In b O -> In b (ablocks B ly S).
Proof. intros cx ly S b O HP Hb. apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hb. Qed.
(* the first two blocks of a cut's list are two different blocks *)
Lemma s24_blk_two : forall cx ly S (W : world SEGS) mem md x y O,
  AR SEGS B ly S W mem md -> lt_blocks B cx ly S (x :: y :: O) -> x <> y /\ ~ In x (x_bl0 B cx) /\ ~ In y (x_bl0 B cx).
Proof.
intros cx ly S W mem md x y O HAR HP.
assert (HND : List.NoDup (ablocks B ly S)) by exact (s24_nodup ly S W mem md HAR).
pose proof (Permutation_NoDup HP HND) as HND2. cbn [app] in HND2.
apply NoDup_cons_iff in HND2 as [Hx HND3]. apply NoDup_cons_iff in HND3 as [Hy _].
split; [intros E; subst y; apply Hx; left; reflexivity|].
split; [intros Hb; apply Hx; right; apply in_or_app; right; exact Hb|].
intros Hb; apply Hy; apply in_or_app; right; exact Hb.
Qed.

(* a harness block's facts at any state that holds it (lt_hblk), from AR *)
Lemma s24_hblk : forall ly S (W : world SEGS) mem md a n,
  AR SEGS B ly S W mem md -> In (a, n) (ablocks B ly S) -> lt_hblk B ly S (rdW W mem) a n.
Proof.
intros ly S W mem md a n HAR Hin.
destruct (al_blocks _ _ LAWS ly S W mem md a n HAR Hin) as (H16 & H4096 & Hceil & Happ & Hpres & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as [Hr1 Hr2].
pose proof asan_consts as (C1 & _).
split; [exact Hin|]. split; [exact H4096|]. split; [exact H16|].
unfold sa_addr. split; [lia|]. split; [lia|].
split; [eapply amem_range_of_block; first [eassumption | exact LAWS | lia]|].
split; [eapply range_addressable_of_block; first [eassumption | exact LAWS | lia]|].
intros Hn0. eapply shadow_hull_vis_of_block; first [eassumption | exact LAWS | lia].
Qed.

(* the frame chain at a call from sp = S1 with s0 = SP0: the frame record the prologue wrote (ra at SP0 - 8, the
   caller's s0 at SP0 - 16) pushed onto afn_pre's chain (chain_words_s2.v cw2_chain) *)
Lemma s24_chain : forall cx ly S (W : world SEGS) mem md k,
  lt_base B MT cx -> s24_J cx ly S W mem md k -> lt_saved cx (rdW W mem) ->
  exists ch, achain ly (rdW W mem) (x_s1 cx) (x_sp0 cx) ch.
Proof.
intros cx ly S W mem md k HB HJ HSV.
pose proof (s24_nums cx HB) as (Hal16 & Hs1al & Hs1 & Hceil & H47 & Htop & Htop2).
destruct HB as (HPRE & _).
destruct HPRE as (HAR0 & Hra0 & Hra4 & Hgp0 & Htp0 & Hstk & Hpres & Hch & HQT).
destruct HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & G1 & _).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & _).
unfold STK_LLVMFuzzerTestOneInput in *.
destruct (Z_lt_le_dec (x_sp0 cx) (ly_top (x_ly cx) - 16)) as [Hlt | Hge].
- exists ((spZ (x_regs cx), raZ (x_regs cx), s0Z (x_regs cx)) :: x_ch cx).
  apply (achain_ly_top (x_ly cx) ly _ _ _ _ Etop).
  pose proof (HSV 0%nat _ eq_refl) as H0. pose proof (HSV 1%nat _ eq_refl) as H1.
  change (Z.of_nat (Datatypes.S 0)) with 1 in H0. change (Z.of_nat (Datatypes.S 1)) with 2 in H1.
  unfold x_sp0 in *.
  apply (achain_push (x_ly cx) (rdW (x_W cx) (x_mem cx)) (rdW W mem) (spZ (x_regs cx)) (s0Z (x_regs cx))
    (raZ (x_regs cx)) (x_ch cx) (x_s1 cx) Hch).
  + lia.
  + intros a Ha. apply G1.
    * lia.
    * lia.
    * intros (r & Hr & Ha'). cbn [ltoi_PG In] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Ha'.
      unfold longlA, A_LONGL, LONGL_N in Ha'. lia.
  + replace (spZ (x_regs cx) - 8) with (spZ (x_regs cx) - 8 * 1) by lia. exact H0.
  + replace (spZ (x_regs cx) - 16) with (spZ (x_regs cx) - 8 * 2) by lia. exact H1.
  + exact Hra4.
  + lia.
  + pose proof (Z.div_mod (spZ (x_regs cx)) 16 ltac:(lia)) as Hd. rewrite Hal16, Z.add_0_r in Hd.
    rewrite Hd. replace (16 * (spZ (x_regs cx) / 16)) with (2 * (spZ (x_regs cx) / 16) * 8) by ring.
    apply Z.mod_mul. lia.
  + lia.
  + lia.
- exists []. left. split; [right; left; rewrite Etop; lia | reflexivity].
Qed.

(* what a step keeps that a cut reads: the stack [S1, SP0) (saved registers, slots), the frame's header words and
   flag word, its 36 shadow bytes, and every image byte the runtime does not own *)
Definition s24_kept (cx : lcx) (W : world SEGS) mem (W2 : world SEGS) mem2 : Prop :=
  (forall a, x_s1 cx <= a < x_sp0 cx -> rdW W2 mem2 a = rdW W mem a) /\
  (forall a, x_fr cx <= a < x_fr cx + 24 \/ x_fr cx + 504 <= a < x_fr cx + 512 -> rdW W2 mem2 a = rdW W mem a) /\
  (forall i, 0 <= i < 36 -> rdW W2 mem2 (x_sh cx + i) = rdW W mem (x_sh cx + i)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     rdW W2 mem2 a = rdW W mem a).
Lemma s24_kept_all : forall cx (W W2 : world SEGS) mem mem2,
  (forall a, rdW W2 mem2 a = rdW W mem a) -> s24_kept cx W mem W2 mem2.
Proof. intros cx W W2 mem mem2 H. repeat split; intros; apply H. Qed.
Lemma s24_kept_trans : forall cx (W W1 W2 : world SEGS) mem mem1 mem2,
  s24_kept cx W mem W1 mem1 -> s24_kept cx W1 mem1 W2 mem2 -> s24_kept cx W mem W2 mem2.
Proof.
intros cx W W1 W2 mem mem1 mem2 (A1 & A2 & A3 & A4) (B1 & B2 & B3 & B4).
split; [intros a Ha; rewrite (B1 a Ha); exact (A1 a Ha)|].
split; [intros a Ha; rewrite (B2 a Ha); exact (A2 a Ha)|].
split; [intros i Hi; rewrite (B3 i Hi); exact (A3 i Hi)|].
intros a H1 H2 H3. rewrite (B4 a H1 H2 H3). exact (A4 a H1 H2 H3).
Qed.

(* the frame part of a cut at a later state of the journal *)
Lemma s24_frame_kept : forall cx ly S (W : world SEGS) regs mem md k o ly2 S2 (W2 : world SEGS) regs2 mem2 md2 k2 o2,
  lt_base B MT cx -> lt_frame B cx ly S W regs mem md k o ->
  s24_J cx ly2 S2 W2 mem2 md2 k2 -> s24_fregs regs regs2 ->
  (forall a, x_s1 cx <= a < x_sp0 cx -> rdW W2 mem2 a = rdW W mem a) ->
  (forall a, x_fr cx <= a < x_fr cx + 24 \/ x_fr cx + 504 <= a < x_fr cx + 512 -> rdW W2 mem2 a = rdW W mem a) ->
  sa_zs (rdW W2 mem2) (x_sh cx) (lt_fsh o2) ->
  lt_frame B cx ly2 S2 W2 regs2 mem2 md2 k2 o2.
Proof.
intros cx ly S W regs mem md k o ly2 S2 W2 regs2 mem2 md2 k2 o2 HB HF HJ2 HP KS KF HSH2.
pose proof (s24_nums cx HB) as (Hal16 & Hs1al & Hs1 & Hceil & H47 & Htop & Htop2).
destruct HF as (_ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & HSB & _).
assert (P : forall r, (r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9) -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r))
  by exact HP.
split; [exact HJ2|].
split; [exact (eq_trans (P 2 ltac:(lia)) R2)|].
split; [exact (eq_trans (P 3 ltac:(lia)) R3)|].
split; [exact (eq_trans (P 4 ltac:(lia)) R4)|].
split; [exact (eq_trans (P 8 ltac:(lia)) R8)|].
split; [exact (eq_trans (P 9 ltac:(lia)) R9)|].
split.
{ intros i r Hi. rewrite <- (HSV i r Hi). apply rdword_ext. intros q Hq.
  assert (Hil : (i < 13)%nat) by (apply (proj1 (nth_error_Some LT_SAVED i)); rewrite Hi; discriminate).
  apply KS. lia. }
split; [rewrite <- HH0; apply rdword_ext; intros q Hq; apply KF; lia|].
split; [rewrite <- HH8; apply rdword_ext; intros q Hq; apply KF; lia|].
split; [rewrite <- HH16; apply rdword_ext; intros q Hq; apply KF; lia|].
split; [rewrite <- HFL; apply rdword_ext; intros q Hq; apply KF; unfold LT_FLAGW; lia|].
split; [rewrite <- HSB; apply rdword_ext; intros q Hq; apply KS; lia|].
exact HSH2.
Qed.
Lemma s24_fsh_kept : forall cx (W W2 : world SEGS) mem mem2 o,
  s24_kept cx W mem W2 mem2 -> sa_zs (rdW W mem) (x_sh cx) (lt_fsh o) -> sa_zs (rdW W2 mem2) (x_sh cx) (lt_fsh o).
Proof.
intros cx W W2 mem mem2 o (_ & _ & KH & _) H i Hi. rewrite lt_fsh_len in Hi.
rewrite (KH (Z.of_nat i)) by lia. exact (H i ltac:(rewrite lt_fsh_len; exact Hi)).
Qed.

(* slots of S1 at a later state that keeps the stack *)
Lemma s24_slots_kept : forall cx (W W2 : world SEGS) mem mem2 L,
  lt_base B MT cx -> lt_slots cx (rdW W mem) L -> (forall o v, In (o, v) L -> 0 <= o <= 312) ->
  s24_kept cx W mem W2 mem2 -> lt_slots cx (rdW W2 mem2) L.
Proof.
intros cx W W2 mem mem2 L HB HS HL (KS & _) o v Hin.
pose proof (s24_nums cx HB) as (Hal16 & Hs1al & Hs1 & Hceil & H47 & Htop & Htop2).
pose proof (HL o v Hin) as Ho.
rewrite <- (HS o v Hin). apply rdword_ext. intros q Hq. apply KS. lia.
Qed.

(* the budget around a free: an event is left, the meter allows a free, and the next cut's budget *)
Hypothesis MTL : ameter_laws MT.
Lemma s24_bud_free : forall cx ly S (W : world SEGS) mem md k acc rem,
  lt_base B MT cx -> s24_J cx ly S W mem md k -> lt_bud MT cx S k acc rem -> 1 <= rem ->
  st_nev S < EV_MAX /\ mo_ok MT S (mo_free MT) /\
  (forall S2, mo_le MT S S2 (mo_free MT) -> lt_bud MT cx S2 (k + 1) (acc + mo_free MT) (rem - 1)).
Proof.
intros cx ly S W mem md k acc rem HB HJ (Hk & Hrem & Hkr & Hle & Hacc & Hxm) Hr.
destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HEV & _ & HMO).
destruct HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
pose proof (mo_free_nonneg MT MTL) as Hf0. pose proof (mo_malloc_nonneg MT MTL 65536 ltac:(lia)) as Hm0.
assert (HU : mo_free MT <= LT_U MT) by (unfold LT_U; lia).
assert (HU0 : 0 <= LT_U MT) by (unfold LT_U; lia).
split; [lia|].
split.
{ apply (mok_station MT (x_S cx) S (XM_LTOI MT (x_pl cx)) acc (mo_free MT) MTL HMO Hle Hf0). nia. }
intros S2 HM. split; [lia|]. split; [lia|]. split; [lia|].
split; [exact (mo_le_trans MT MTL _ _ _ _ _ Hle HM)|]. split; [lia|]. nia.
Qed.
(* across a call of no allocator event that changes only the frames (sa_noalloc): the same budget *)
Hypothesis MTFL : ameter_fs_laws MT.
Lemma s24_bud_noalloc : forall cx S k acc rem f, lt_bud MT cx S k acc rem -> lt_bud MT cx (set_fs f S) k acc rem.
Proof.
intros cx S k acc rem f (Hk & Hrem & Hkr & Hle & Hacc & Hxm).
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact (mo_le_set_fs_r MT MTFL _ _ f _ Hle)|]. split; lia.
Qed.

(* ---- the cut after a step: frame, image, blocks and budget ---- *)
Hypothesis IMGS : s10_img.
Hypothesis BSYM : AF0m.SegBSyms B.
Lemma s24_core_step_f : forall cx ly S (W : world SEGS) regs mem md k acc rem o O ly2 S2 (W2 : world SEGS) regs2 mem2 md2
  k2 acc2 rem2 O2,
  lt_base B MT cx -> lt_core B MT cx ly S W regs mem md k acc rem o O ->
  s24_J cx ly2 S2 W2 mem2 md2 k2 -> s24_fregs regs regs2 -> s24_kept cx W mem W2 mem2 ->
  Permutation (ablocks B ly2 S2) (O2 ++ x_bl0 B cx) -> lt_bud MT cx S2 k2 acc2 rem2 ->
  lt_core B MT cx ly2 S2 W2 regs2 mem2 md2 k2 acc2 rem2 o O2.
Proof.
intros cx ly S W regs mem md k acc rem o O ly2 S2 W2 regs2 mem2 md2 k2 acc2 rem2 O2 HB (HF & HI & _ & _) HJ2 HP HK HP2 HBUD.
pose proof HF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSH).
split; [exact (s24_frame_kept cx ly S W regs mem md k o ly2 S2 W2 regs2 mem2 md2 k2 o HB HF HJ2 HP
  (proj1 HK) (proj1 (proj2 HK)) (s24_fsh_kept cx W W2 mem mem2 o HK HSH))|].
split; [|split; [exact HP2 | exact HBUD]].
destruct HK as (_ & _ & _ & KI).
exact (s10_lt_img_kept B IMGS BSYM cx W2 mem2 (rdW W mem) (proj1 HJ2) KI HI).
Qed.
Lemma s24_core_step : forall cx ly S (W : world SEGS) regs mem md k acc rem o O ly2 S2 (W2 : world SEGS) regs2 mem2 md2
  k2 acc2 rem2 O2,
  lt_base B MT cx -> lt_core B MT cx ly S W regs mem md k acc rem o O ->
  s24_J cx ly2 S2 W2 mem2 md2 k2 -> aregs_preserved regs regs2 -> s24_kept cx W mem W2 mem2 ->
  Permutation (ablocks B ly2 S2) (O2 ++ x_bl0 B cx) -> lt_bud MT cx S2 k2 acc2 rem2 ->
  lt_core B MT cx ly2 S2 W2 regs2 mem2 md2 k2 acc2 rem2 o O2.
Proof.
intros cx ly S W regs mem md k acc rem o O ly2 S2 W2 regs2 mem2 md2 k2 acc2 rem2 O2 HB HC HJ2 HP.
exact (s24_core_step_f cx ly S W regs mem md k acc rem o O ly2 S2 W2 regs2 mem2 md2 k2 acc2 rem2 O2 HB HC HJ2
  (s24_fregs_of_pres regs regs2 HP)).
Qed.

(* the frame (3, x_fpos cx) at a state of the journal: live, at x_fr cx *)
Lemma s24_frame_at : forall cx ly S (W : world SEGS) mem md k, s24_J cx ly S W mem md k ->
  In (3, x_fpos cx) (frames S) /\ frame_addr ly 3 (x_fpos cx) = x_fr cx /\
  4096 <= x_fr cx /\ x_fr cx + 512 <= alloc_ceiling /\ in_app (x_fr cx) 512 /\ x_fr cx mod 32 = 0 /\
  (forall a, x_fr cx <= a < x_fr cx + 512 -> apresent (w_H W) mem a) /\
  (forall i, 0 <= i < 64 -> apresent (w_H W) mem (x_sh cx + i)).
Proof.
intros cx ly S W mem md k HJ.
destruct HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
destruct Hly as (_ & _ & _ & _ & _ & EF & _).
assert (Hin : In (3, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EFA : frame_addr ly 3 (x_fpos cx) = x_fr cx) by (unfold x_fr, frame_addr, LT_FCLS; rewrite EF; reflexivity).
destruct (frames_bounds SEGS B LAWS ly S W mem md 3 (x_fpos cx) HAR Hin) as (H4 & Hc & Ha).
destruct (al_frames _ _ LAWS ly S W mem md 3 (x_fpos cx) HAR Hin) as (H32 & _ & Hp & Hsp).
rewrite EFA in H4, Hc, Ha, H32, Hp, Hsp. change (fs_frame_bytes 3) with 512 in H4, Hc, Ha, Hp, Hsp.
change (512 / 8) with 64 in Hsp.
split; [exact Hin|]. split; [exact EFA|]. split; [exact H4|]. split; [exact Hc|]. split; [exact Ha|].
split; [exact H32|]. split; [intros a Hr; exact (proj1 (Hp a Hr))|].
intros i Hi. exact (proj1 (Hsp i Hi)).
Qed.

(* a call's acall_kept (the free wrapper's post) gives what a cut keeps, when the bytes the call may change (E)
   miss the frame and its shadow *)
Lemma s24_kept_of_acall : forall cx ly S (W : world SEGS) mem md k (W2 : world SEGS) mem2 slo (Ex : Z -> Prop),
  lt_base B MT cx -> s24_J cx ly S W mem md k ->
  acall_kept SEGS B ly S W mem W2 mem2 slo (x_s1 cx) Ex ->
  (forall a, x_fr cx <= a < x_fr cx + 512 -> ~ Ex a) -> (forall i, 0 <= i < 36 -> ~ Ex (x_sh cx + i)) ->
  s24_kept cx W mem W2 mem2.
Proof.
intros cx ly S W mem md k W2 mem2 slo Ex HB HJ (K1 & _ & K3 & K4 & _) HEF HES.
pose proof (s24_nums cx HB) as (Hal16 & Hs1al & Hs1 & Hceil & H47 & Htop & Htop2).
destruct (s24_frame_at cx ly S W mem md k HJ) as (Hin & EFA & H4 & Hc & _).
split; [intros a Ha; apply K1; lia|].
split.
{ intros a Ha. apply (K4 3 (x_fpos cx) a Hin); [left | apply HEF; lia].
  unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 3) with 512. lia. }
split.
{ intros i Hi. apply (K4 3 (x_fpos cx) _ Hin); [right | apply HES; lia].
  unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 3 / 8) with 64. unfold x_sh. lia. }
exact K3.
Qed.

(* a live block misses the frame and the frame's shadow *)
Lemma s24_blk_apart : forall cx ly S (W : world SEGS) mem md k pa n,
  s24_J cx ly S W mem md k -> In (pa, n) (ablocks B ly S) ->
  (forall a, x_fr cx <= a < x_fr cx + 512 -> ~ (pa <= a < pa + req_size n)) /\
  (forall i, 0 <= i < 36 -> ~ (pa <= x_sh cx + i < pa + req_size n)).
Proof.
intros cx ly S W mem md k pa n HJ Hb.
pose proof (proj1 HJ) as HAR.
destruct (s24_frame_at cx ly S W mem md k HJ) as (Hin & EFA & H4 & Hc & Happ & _).
pose proof (sep_block_frame SEGS B LAWS ly S W mem md pa n 3 (x_fpos cx) HAR Hb Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA in Hd. change (fs_frame_bytes 3) with 512 in Hd.
destruct (al_blocks _ _ LAWS ly S W mem md pa n HAR Hb) as (_ & Hp4 & Hpc & Hpapp & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as Hrq.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (shadow_addr_bounds (x_fr cx) ltac:(lia)) as Hsh.
split; [intros a Ha Hab; lia|].
intros i Hi Hab. unfold x_sh, shadow_addr, SHADOW_OFF in Hab. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp.
clear Hsh. lia.
Qed.

(* the frame and its shadow sit below the stack window of any call from S1 (all below the allocator's ceiling) *)
Lemma s24_low : forall cx ly S (W : world SEGS) mem md k, lt_base B MT cx -> s24_J cx ly S W mem md k ->
  x_fr cx + 512 + ASTACK + 352 <= x_s1 cx /\ x_sh cx + 64 + ASTACK + 352 <= x_s1 cx /\
  alloc_ceiling + 32768 - 352 <= x_s1 cx.
Proof.
intros cx ly S W mem md k HB HJ.
pose proof (s24_nums cx HB) as (Hal16 & Hs1al & Hs1 & Hceil & H47 & Htop & Htop2).
destruct (s24_frame_at cx ly S W mem md k HJ) as (_ & _ & H4 & Hc & _).
pose proof asan_consts as (C1 & _).
unfold x_sh, shadow_addr, SHADOW_OFF, ASTACK. lia.
Qed.

(* check_declared's sa_kept (every byte outside its window [S1 - STK1, S1)) gives what a cut keeps *)
Lemma s24_kept_of_sa_kept : forall cx ly S (W : world SEGS) mem md k (W2 : world SEGS) mem2 (regs : bvmap 5 word) STK1,
  lt_base B MT cx -> s24_J cx ly S W mem md k -> spZ regs = x_s1 cx -> 0 <= STK1 <= ASTACK ->
  sa_kept SEGS W mem W2 mem2 regs STK1 (fun _ => False) -> s24_kept cx W mem W2 mem2.
Proof.
intros cx ly S W mem md k W2 mem2 regs STK1 HB HJ Hsp HS1 HK.
pose proof (s24_nums cx HB) as (Hal16 & Hs1al & Hs1 & Hceil & H47 & Htop & Htop2).
destruct (s24_low cx ly S W mem md k HB HJ) as (L1 & L2 & L3).
destruct (s24_frame_at cx ly S W mem md k HJ) as (_ & _ & H4 & Hc & _).
pose proof (pa_img_range (L := seg_listing) (PAImg := PI)) as HIR.
assert (Hsh0 : 0 <= x_sh cx) by (unfold x_sh, shadow_addr, SHADOW_OFF; pose proof (Z.div_pos (x_fr cx) 8 ltac:(lia) ltac:(lia)); lia).
pose proof asan_consts as (C1 & _).
unfold ASTACK in *.
split; [intros a Ha; apply HK; [lia | rewrite Hsp; lia | intros []]|].
split; [intros a Ha; apply HK; [lia | rewrite Hsp; lia | intros []]|].
split; [intros i Hi; apply HK; [lia | rewrite Hsp; lia | intros []]|].
intros a Hi _ _. pose proof (HIR a Hi) as Ha. unfold kImgEnd in Ha. apply HK; [lia | rewrite Hsp; lia | intros []].
Qed.

(* a call's inner journal from S1 whose footprint is in live blocks and the count cell n = FR + 256 gives what a
   cut keeps (the image bytes by the journal's image clause: a block or the frame holds no image byte) *)
Lemma s24_kept_of_journal : forall cx ly S (W : world SEGS) mem md k STK1 FP1 ly2 S2 (W2 : world SEGS) mem2 md2 k1,
  lt_base B MT cx -> s24_J cx ly S W mem md k ->
  ajournal SEGS B STK1 (x_s1 cx) FP1 ly S W mem md [] ly2 S2 W2 mem2 md2 k1 -> 0 <= STK1 <= ASTACK ->
  (forall a, inFP FP1 a -> (exists b n, In (b, n) (ablocks B ly S) /\ b <= a < b + req_size n) \/
     (x_fr cx + FO_N <= a < x_fr cx + FO_N + 4)) ->
  s24_kept cx W mem W2 mem2.
Proof.
intros cx ly S W mem md k STK1 FP1 ly2 S2 W2 mem2 md2 k1 HB HJ HJ1 HS1 HFP.
pose proof (s24_nums cx HB) as (Hal16 & Hs1al & Hs1 & Hceil & H47 & Htop & Htop2).
destruct (s24_low cx ly S W mem md k HB HJ) as (L1 & L2 & L3).
pose proof (proj1 HJ) as HAR.
destruct (s24_frame_at cx ly S W mem md k HJ) as (Hin & EFA & H4 & Hc & Happ & H32 & _).
destruct HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & F3 & F4 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
(* where a footprint byte can be: below the ceiling, apart from the frame's header / flag words and its shadow *)
assert (HLOW : forall a, inFP FP1 a -> 4096 <= a < alloc_ceiling).
{ intros a Ha. destruct (HFP a Ha) as [(b & n & Hb & Hr) | Hr].
  - destruct (al_blocks _ _ LAWS ly S W mem md b n HAR Hb) as (_ & Hb4 & Hbc & _). lia.
  - unfold FO_N in Hr. lia. }
assert (HNF : forall a, x_fr cx <= a < x_fr cx + 24 \/ x_fr cx + 504 <= a < x_fr cx + 512 -> ~ inFP FP1 a).
{ intros a Ha Hf. destruct (HFP a Hf) as [(b & n & Hb & Hr) | Hr].
  - destruct (s24_blk_apart cx ly S W mem md k b n HJ Hb) as (HA & _). exact (HA a ltac:(lia) Hr).
  - unfold FO_N in Hr. lia. }
assert (HNS : forall i, 0 <= i < 36 -> ~ inFP FP1 (x_sh cx + i)).
{ intros i Hi Hf. destruct (HFP _ Hf) as [(b & n & Hb & Hr) | Hr].
  - destruct (s24_blk_apart cx ly S W mem md k b n HJ Hb) as (_ & HA). exact (HA i Hi Hr).
  - unfold x_sh, shadow_addr, SHADOW_OFF, FO_N in Hr. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. lia. }
split.
{ intros a Ha. apply F1; [lia | lia | intros Hf; pose proof (HLOW a Hf); lia]. }
split.
{ intros a Ha. apply (F4 3 (x_fpos cx) a Hin); [left | exact (HNF a Ha)].
  unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 3) with 512. lia. }
split.
{ intros i Hi. apply (F4 3 (x_fpos cx) _ Hin); [right | exact (HNS i Hi)].
  unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 3 / 8) with 64. unfold x_sh. lia. }
intros a Hi Ho He. apply F3; [exact Hi | exact Ho | exact He |].
apply fp_spares_closed.
- intros (r & Hr & Hr0). assert (Hf : inFP FP1 0) by (exists r; split; [exact Hr | exact Hr0]).
  pose proof (HLOW 0 Hf). lia.
- intros Hf. destruct (HFP a Hf) as [(b & n & Hb & Hr) | Hr].
  + exact (blk_img SEGS B LAWS ly S W mem md b n a HAR Hb Hr Hi).
  + apply (frm_img SEGS B LAWS ly S W mem md 3 (x_fpos cx) a HAR Hin); [|exact Hi]. rewrite EFA.
    change (fs_frame_bytes 3) with 512. unfold FO_N in Hr. lia.
Qed.

(* a block the call's footprint misses keeps its bytes (the journal's block clause) *)
Lemma s24_blk_kept : forall cx ly S (W : world SEGS) mem md k STK1 FP1 ly2 S2 (W2 : world SEGS) mem2 md2 k1 p n,
  s24_J cx ly S W mem md k ->
  ajournal SEGS B STK1 (x_s1 cx) FP1 ly S W mem md [] ly2 S2 W2 mem2 md2 k1 ->
  In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly2 S2) ->
  (forall a, inFP FP1 a -> (exists b m, In (b, m) (ablocks B ly S) /\ (b, m) <> (p, n) /\ b <= a < b + req_size m) \/
     (x_fr cx + FO_N <= a < x_fr cx + FO_N + 4)) ->
  forall i, 0 <= i < req_size n -> rdW W2 mem2 (p + i) = rdW W mem (p + i).
Proof.
intros cx ly S W mem md k STK1 FP1 ly2 S2 W2 mem2 md2 k1 p n HJ HJ1 Hp Hp2 HFP i Hi.
pose proof (proj1 HJ) as HAR.
destruct HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
apply (F2 p n i Hp Hp2 Hi). intros Hf. destruct (HFP _ Hf) as [(b & m & Hb & Hne & Hr) | Hr].
- pose proof (sep_blocks SEGS B LAWS ly S W mem md b m p n HAR Hb Hp Hne) as Hd. unfold zdisjoint in Hd.
  cbn [fst snd] in Hd. lia.
- destruct (s24_blk_apart cx ly S W mem md k p n HJ Hp) as (HA & _). exact (HA (p + i) ltac:(unfold FO_N in Hr; lia) ltac:(lia)).
Qed.

(* a live block of a positive size, from AR: nonzero, 16-aligned, every sub-range sa_addr, every byte mapped *)
Lemma s24n_blk : forall ly S (W : world SEGS) mem md p n,
  AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> 0 < n ->
  p <> 0 /\ p mod 16 = 0 /\
  (forall a k, p <= a -> a + k <= p + n -> sa_addr (rdW W mem) a k) /\
  (forall a, p <= a < p + n -> rdW W mem a <> None).
Proof.
  intros ly S W mem md p n HAR Hin Hn.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (Hm16 & H4096 & Hceil & _ & Hpres & _).
  pose proof (s24n_req n Hn) as Er. rewrite Er in Hceil, Hpres.
  pose proof asan_consts as (C1 & _).
  split; [lia|]. split; [exact Hm16|]. split.
  - intros a k Ha Hk. unfold sa_addr. split; [lia|].
    split; [change (2 ^ 63) with 9223372036854775808; lia|].
    split; [apply (amem_range_of_block _ _ LAWS ly S W mem md p n a k HAR Hin Ha); rewrite Er; exact Hk|].
    split; [apply (range_addressable_of_block _ _ LAWS ly S W mem md p n a k HAR Hin Ha); rewrite Er; exact Hk|].
    intros Hk0. apply (shadow_hull_vis_of_block _ _ LAWS ly S W mem md p n a k HAR Hin Ha); [rewrite Er; exact Hk | exact Hk0].
  - intros a Ha. apply (aview_some_of_apresent SEGS). exact (proj1 (Hpres a Ha)).
Qed.

(* reac_segconf_declared's pre at the call 0x85bf0, and its room and events *)
Lemma s24_decl_pre : forall cx ly S (W : world SEGS) (regs : bvmap 5 word) mem md k acc (c m tab mt : Z),
  lt_base B MT cx ->
  lt_core B MT cx ly S W regs mem md k acc 4 LFO_N
    [(mt, x_mtn cx); (tab, x_tabn cx); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_cm (rdW W mem) c m (x_run cx) ->
  lt_tabs cx (rdW W mem) tab mt (snd (SegModel.m_declared (x_mcF cx) (x_tab0 cx) (x_cap cx))) ->
  declared_pre SEGS B ly S W mem regs c tab (x_cap cx) (x_fr cx + FO_N) (seg_spec.seg_rc (x_run cx)) (x_tab0 cx)
    gotwA guardA /\ sa_room S /\ st_nev S + EV_reac_segconf_declared <= EV_MAX.
Proof.
  intros cx ly S W regs mem md k acc c m tab mt HB HC Hcm HT.
  destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hfr0 & _ & Hnev0 & _).
  destruct HC as (HF & HI & HBl & HBud).
  destruct HF as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsh).
  destruct HJ as (HAR & Hly & _ & _ & _ & Hfrs & Hnev & _).
  destruct HI as (_ & Hh & _).
  destruct Hh as (_ & _ & _ & _ & _ & _ & _ & _ & Hssp & _).
  destruct HBud as (_ & _ & Hkr & _).
  destruct Hcm as (Hrc & _).
  destruct HT as (Hcap & Hrt & _ & Hval & _).
  unfold lt_blocks in HBl.
  pose proof asan_consts as (C1 & _).
  (* the class-3 frame and the count cell n = frame + 256 *)
  assert (HinF : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; apply in_or_app; left; left; reflexivity).
  assert (EF : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx).
  { unfold x_fr, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & HlyF & _). rewrite HlyF. reflexivity. }
  assert (E512 : fs_frame_bytes LT_FCLS = 512) by reflexivity.
  destruct (al_frames _ _ LAWS ly S W mem md _ _ HAR HinF) as (Hm32 & _ & _ & Hshp).
  destruct (frames_bounds _ _ LAWS ly S W mem md _ _ HAR HinF) as (Hf1 & Hf2 & Hf3).
  rewrite EF in Hm32, Hshp, Hf1, Hf2, Hf3. rewrite E512 in Hshp, Hf2, Hf3.
  unfold x_sh in Hsh.
  assert (H32 : rdW W mem (shadow_addr (x_fr cx) + 32) = Some 4)
    by exact (Hsh 32%nat ltac:(rewrite lt_fsh_len; lia)).
  assert (Hra : range_addressable (rdW W mem) SHADOW_OFF (x_fr cx + FO_N) 4).
  { intros x Hx. unfold FO_N in Hx. exists 4. split.
    - replace (shadow_of_addr SHADOW_OFF x) with (shadow_addr (x_fr cx) + 32); [exact H32|].
      unfold shadow_of_addr, shadow_addr. lia.
    - right. split; lia. }
  assert (Hhv : shadow_hull_vis (rdW W mem) (x_fr cx + FO_N) 4).
  { intros s Hs. unfold FO_N, shadow_addr, SHADOW_OFF in Hs.
    assert (Hi : 0 <= s - shadow_addr (x_fr cx) < 512 / 8) by (unfold shadow_addr, SHADOW_OFF; lia).
    destruct (Hshp _ Hi) as [Hp _].
    replace s with (shadow_addr (x_fr cx) + (s - shadow_addr (x_fr cx))) by lia.
    apply (aview_some_of_apresent SEGS). exact Hp. }
  assert (Hff : sa_fframe ly S (x_fr cx + FO_N) 4).
  { exists LT_FCLS, (x_fpos cx). split; [exact HinF|]. split; [unfold LT_FCLS; lia|].
    rewrite EF, E512. unfold FO_N. lia. }
  assert (Ham : amem_range (x_fr cx + FO_N) 4).
  { unfold amem_range, in_app, FO_N, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *. lia. }
  assert (Han : sa_addr (rdW W mem) (x_fr cx + FO_N) 4).
  { split; [unfold FO_N; lia|]. split; [unfold FO_N; change (2 ^ 63) with 9223372036854775808; lia|].
    split; [exact Ham|]. split; [exact Hra|]. intros _; exact Hhv. }
  (* the blocks c and tab *)
  assert (Hinc : In (c, seg_spec.SEG_C_SIZE) (ablocks B ly S)).
  { apply (Permutation_in _ (Permutation_sym HBl)). apply in_or_app. left. right. right. right. left. reflexivity. }
  assert (Hint : In (tab, x_tabn cx) (ablocks B ly S)).
  { apply (Permutation_in _ (Permutation_sym HBl)). apply in_or_app. left. right. left. reflexivity. }
  assert (Htn : 0 < x_tabn cx) by (unfold x_tabn, seg_spec.RVLAN_SIZE; lia).
  destruct (s24n_blk ly S W mem md c seg_spec.SEG_C_SIZE HAR Hinc ltac:(unfold seg_spec.SEG_C_SIZE; lia))
    as (Hc0 & Hc16 & Hcaddr & _).
  destruct (s24n_blk ly S W mem md tab (x_tabn cx) HAR Hint Htn) as (Ht0 & Ht16 & Htaddr & _).
  pose proof (Htaddr tab (seg_spec.RVLAN_SIZE * x_cap cx + 8) ltac:(lia)
    ltac:(unfold x_tabn, seg_spec.RVLAN_SIZE; lia)) as (_ & _ & Ham8 & _).
  pose proof (sep_block_frame _ _ LAWS ly S W mem md _ _ _ _ HAR Hinc HinF) as Dcf.
  pose proof (sep_block_frame _ _ LAWS ly S W mem md _ _ _ _ HAR Hint HinF) as Dtf.
  assert (Hne : (c, seg_spec.SEG_C_SIZE) <> (tab, x_tabn cx)).
  { intros E. injection E. intros E1 E2. unfold x_tabn, seg_spec.RVLAN_SIZE, seg_spec.SEG_C_SIZE in *. lia. }
  pose proof (sep_blocks _ _ LAWS ly S W mem md _ _ _ _ HAR Hinc Hint Hne) as Dct.
  unfold zdisjoint in Dcf, Dtf, Dct. cbn [fst snd] in Dcf, Dtf, Dct.
  rewrite EF, E512 in Dcf, Dtf.
  rewrite (s24n_req seg_spec.SEG_C_SIZE ltac:(unfold seg_spec.SEG_C_SIZE; lia)) in Dcf, Dct.
  rewrite (s24n_req (x_tabn cx) Htn) in Dtf, Dct.
  split; [|split].
  - unfold declared_pre.
    split; [exact Hc0|]. split; [exact Hc16|]. split; [exact Hrc|].
    split; [exists c, seg_spec.SEG_C_SIZE; split; [exact Hinc | lia]|].
    split; [apply Hcaddr; lia|].
    split.
    + unfold vtab_pre.
      split; [exact Ht0|]. split; [exact Ht16|]. split; [exact Hrt|].
      split; [change (2 ^ 31) with 2147483648; lia|].
      split; [exists tab, (x_tabn cx); split; [exact Hint | unfold x_tabn, seg_spec.RVLAN_SIZE; lia]|].
      split; [apply Htaddr; unfold x_tabn, seg_spec.RVLAN_SIZE; lia|].
      split; [exact Ham8|].
      split; [unfold FO_N; lia|].
      split; [unfold FO_N; lia|].
      split; [exact Hval|].
      split; [left; split; [exact Hff | exact Hra]|].
      split; [exact Han|].
      unfold sa_disj, FO_N, x_tabn, seg_spec.RVLAN_SIZE in *. lia.
    + split; [unfold sa_disj, x_tabn, seg_spec.RVLAN_SIZE in *; lia|].
      split; [unfold sa_disj, FO_N in *; lia|].
      exact Hssp.
  - unfold sa_room. rewrite Hfrs, Hfr0. cbn [length app]. lia.
  - unfold EV_reac_segconf_declared. lia.
Qed.

(* check_declared's pre at the call 0x85c10, after reac_segconf_declared returned *)
Lemma s24_chk_pre : forall cx ly2 S2 (W2 : world SEGS) mem2 md2 (tab mt got want : Z),
  lt_base B MT cx -> AR SEGS B ly2 S2 W2 mem2 md2 ->
  In (tab, x_tabn cx) (ablocks B ly2 S2) -> In (mt, x_mtn cx) (ablocks B ly2 S2) ->
  (length (SegModel.mc_seg (x_mcF cx)) <= 32)%nat ->
  got = fst (SegModel.r_declared (seg_spec.seg_rc (x_run cx)) (x_tab0 cx) (x_cap cx)) mod 2 ^ 64 ->
  want = fst (SegModel.m_declared (x_mcF cx) (x_tab0 cx) (x_cap cx)) mod 2 ^ 64 ->
  Z.of_nat (length (x_tab0 cx)) <= x_cap cx < 40 ->
  sa_rtab (rdW W2 mem2) tab (snd (SegModel.r_declared (seg_spec.seg_rc (x_run cx)) (x_tab0 cx) (x_cap cx))) ->
  sa_guardtab (rdW W2 mem2) tab (x_cap cx) ->
  sa_mtab (rdW W2 mem2) mt (snd (SegModel.m_declared (x_mcF cx) (x_tab0 cx) (x_cap cx))) ->
  Z.of_nat (length (snd (SegModel.m_declared (x_mcF cx) (x_tab0 cx) (x_cap cx)))) <= x_cap cx ->
  check_declared_pre B ly2 S2 (rdW W2 mem2) got want tab
    (Z.of_nat (length (snd (SegModel.r_declared (seg_spec.seg_rc (x_run cx)) (x_tab0 cx) (x_cap cx))))) mt
    (Z.of_nat (length (snd (SegModel.m_declared (x_mcF cx) (x_tab0 cx) (x_cap cx))))) (x_cap cx)
    (fst (SegModel.r_declared (seg_spec.seg_rc (x_run cx)) (x_tab0 cx) (x_cap cx)))
    (fst (SegModel.m_declared (x_mcF cx) (x_tab0 cx) (x_cap cx)))
    (snd (SegModel.r_declared (seg_spec.seg_rc (x_run cx)) (x_tab0 cx) (x_cap cx)))
    (snd (SegModel.m_declared (x_mcF cx) (x_tab0 cx) (x_cap cx))).
Proof.
  intros cx ly2 S2 W2 mem2 md2 tab mt got want _ HAR Hint Hinm Hlen Hgot Hwant Hcap Hrt Hg Hmt Hml.
  assert (HV : SegModel.vlans_are (SegModel.r_declared (seg_spec.seg_rc (x_run cx)) (x_tab0 cx) (x_cap cx))
                 (SegModel.m_declared (x_mcF cx) (x_tab0 cx) (x_cap cx)) (x_cap cx) = true)
    by (unfold x_mcF, x_run, x_tab0, x_cap; exact (s24_vlans (x_pl cx))).
  pose proof (s24_mdecl_bnd (x_mcF cx) (x_tab0 cx) (x_cap cx) Hlen) as Hbnd.
  revert HV Hbnd Hgot Hwant Hrt Hg Hmt Hml.
  generalize (SegModel.r_declared (seg_spec.seg_rc (x_run cx)) (x_tab0 cx) (x_cap cx)) as R.
  generalize (SegModel.m_declared (x_mcF cx) (x_tab0 cx) (x_cap cx)) as M.
  intros M R HV Hbnd Hgot Hwant Hrt Hg Hmt Hml.
  pose proof HV as HV'. unfold SegModel.vlans_are in HV'.
  apply andb_prop in HV' as [HV' Hle]. apply andb_prop in HV' as [HV' _]. apply andb_prop in HV' as [Hfst _].
  apply Z.eqb_eq in Hfst. apply Z.leb_le in Hle.
  destruct (s24n_blk ly2 S2 W2 mem2 md2 tab (x_tabn cx) HAR Hint ltac:(unfold x_tabn, seg_spec.RVLAN_SIZE; lia))
    as (Ht0 & Ht16 & Htaddr & Htvis).
  destruct (s24n_blk ly2 S2 W2 mem2 md2 mt (x_mtn cx) HAR Hinm ltac:(unfold x_mtn, seg_spec.MVLAN_SIZE; lia))
    as (Hm0 & Hm16 & Hmaddr & Hmvis).
  unfold check_declared_pre.
  unfold x_tabn, x_mtn, seg_spec.RVLAN_SIZE, seg_spec.MVLAN_SIZE in *.
  split; [exact Hgot|]. split; [exact Hwant|].
  split; [rewrite Hfst; exact Hbnd|]. split; [exact Hbnd|].
  split; [lia|].
  split; [exact Ht0|]. split; [exact Ht16|]. split; [exact Hrt|]. split; [exact Hg|].
  split; [do 2 eexists; split; [exact Hint | lia]|].
  split; [apply Htaddr; lia|].
  split.
  { intros i Hi. refine (s24_rtab_str _ _ _ Hrt _ i Hi). intros x Hx. apply Htvis. lia. }
  split; [reflexivity|].
  split; [exact Hm0|]. split; [exact Hm16|]. split; [exact Hmt|].
  split; [do 2 eexists; split; [exact Hinm | lia]|].
  split; [apply Hmaddr; lia|].
  split.
  { intros i Hi. refine (s24_mtab_str _ _ _ Hmt _ i Hi). intros x Hx. apply Hmvis. lia. }
  split; [exact Hml|]. split; [reflexivity|].
  rewrite <- !surjective_pairing. exact HV.
Qed.


End e.

(* ================================== one free: 0x85c14 / 0x85c1c / 0x85c24 / 0x85c2c ================================== *)
(* the symbolic seed of the two instructions `mv a0, s<x>; jal free`: every register its own atom, no region, no
   fact, no shadow entry (fuzz_command's LLVMFuzzerTestOneInput_Karity.v ka_seed_loc) *)
Definition s24_ss (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).
Definition S24x : sv := SOff 9 0.
Definition s24_span : Z * Z := (SB, SB + 2 ^ 44 - 1).
Lemma s24_seed : forall (W : world SEGS) (regs : bvmap 5 word) mem pc,
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (s24_ss pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))) /\
  sh_ok SEGS S24x [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem) /\
  img_env VAL A_LIM (Eimg (Ereg regs [])) /\ env_agree 32 (Ereg regs []) (Eimg (Ereg regs [])) /\
  (forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (Eimg (Ereg regs [])) n = getr regs rr).
Proof.
intros W regs mem pc.
split.
- unfold s24_ss. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_nil.
  + exact I.
  + unfold facts_ok. cbn. tauto.
- split; [apply Forall_nil|].
  split; [apply Eimg_env|].
  split; [split; [intros i Hi; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]|].
  intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.

Section fr.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Hypothesis TL : PALib B.
(* one free: the run from pc (mv a0, s<x>) to the free wrapper, the wrapper's rule, and back at pc + 8; the
   continuation gets the journal at k + 1, the registers kept, the block gone, the frames, what a cut keeps and the
   meter step (fuzz_command's LLVMFuzzerTestOneInput_s70.v ltf_free, with segconf's chain at s0 = SP0) *)
Lemma s24_free : forall cx ly S (W : world SEGS) regs mem md k pa n (pc : Z) (rr : bv 5) Q,
  lt_base B MT cx ->
  (pc = 0xee0 /\ rr = 22%bv) \/ (pc = 0xee8 /\ rr = 24%bv) \/ (pc = 0xef0 /\ rr = 19%bv) \/
  (pc = 0xef8 /\ rr = 18%bv) ->
  s24_J B cx ly S W mem md k ->
  getr regs 2 = w64 (x_s1 cx) -> getr regs 3 = getr (x_regs cx) 3 -> getr regs 4 = getr (x_regs cx) 4 ->
  getr regs 8 = w64 (x_sp0 cx) -> lt_saved cx (rdW W mem) -> getr regs rr = w64 pa ->
  In (pa, n) (ablocks B ly S) -> ~ In (pa, n) (x_bl0 B cx) ->
  st_nev S < EV_MAX -> mo_ok MT S (mo_free MT) ->
  (forall ly2 S2 (W2 : world SEGS) regs2 mem2 md2,
     s24_J B cx ly2 S2 W2 mem2 md2 (k + 1) -> aregs_preserved regs regs2 ->
     (exists l1 l2, ablocks B ly S = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) ->
     frames S2 = frames S -> s24_kept B cx W mem W2 mem2 -> mo_le MT S S2 (mo_free MT) ->
     SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + (pc + 8))) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS)) md) Q.
Proof.
intros cx ly S W regs mem md k pa n pc rr Q HBASE Hpc HJ R2 R3 R4 R8 HSV Hpa Hin Hnb0 Hnev MOK HC.
pose proof (paj_run B LAWS) as RUN.
pose proof (s24_nums B MT cx HBASE) as (Hal16 & Hs1al & Hs1 & Hceil & H47 & Htop & Htop2).
pose proof HBASE as (HPRE0 & _).
pose proof HPRE0 as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
destruct (s24_chain B MT cx ly S W mem md k HBASE HJ HSV) as (ch & HCH).
destruct (s24_blk_apart B cx ly S W mem md k pa n HJ Hin) as (HAF & HAS).
pose proof HJ as HJ'. unfold s24_J in HJ'.
pose proof HJ' as (_ & Hly & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBok. pose proof pa_base_lo as HBLO.
destruct (s24_seed W regs mem pc) as (HS & SHOK & HEI & HAE & EEo).
set (E := Eimg (Ereg regs [])) in *.
assert (E2 : ew E 2 = getr regs 2) by (apply EEo; reflexivity).
assert (E18 : ew E 18 = getr regs 18) by (apply EEo; reflexivity).
assert (E19 : ew E 19 = getr regs 19) by (apply EEo; reflexivity).
assert (E22 : ew E 22 = getr regs 22) by (apply EEo; reflexivity).
assert (E24 : ew E 24 = getr regs 24) by (apply EEo; reflexivity).
clearbody E. clear EEo.
assert (Hcov : In (pa, n) (ablocks B (x_ly cx) (x_S cx)) -> forall i, 0 <= i < req_size n ->
  inFP (ltoi_PG longlA) (pa + i)) by (intros Hb; exfalso; exact (Hnb0 Hb)).
destruct Hpc as [[-> ->] | [[-> ->] | [[-> ->] | [-> ->]]]];
  unfold s24_ss in HS;
  (paj_run_tok RUN HS HJ' SHOK s24_span; try solve [apply awr_ok_nil]);
  (lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end);
  pmkst HS;
  rewrite (pal_free B TL);
  prreg HS (1%bv : bv 5) P1; prreg HS (10%bv : bv 5) P10; prreg HS (2%bv : bv 5) P2.
all: lazymatch goal with
| HFr : frame_of ?E0 _ (mrestrict _ _) (mrestrict _ ?m1) |- _ =>
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> rdW W m1 a = rdW W mem a)
    by (intros a Ha; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr);
        [ intros b wlo whi a' Hin' Hrr'; vm_compute in Hin'; destruct Hin' | exact Ha | intros Hff; destruct Hff ])
end.
all: lazymatch goal with
| |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) _) _ =>
  assert (HPT1 : aregs_preserved regs rT)
    by (eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs [] HS); [exact HAE | vm_compute; reflexivity]);
  assert (HspT : spZ rT = x_s1 cx)
    by (unfold spZ; transitivity (bv_unsigned (w64 (x_s1 cx)));
        [f_equal; exact (eq_trans P2 (eq_trans E2 R2)) | unfold w64; apply unsigned_lit_small; lia]);
  assert (Ha0 : getr rT 10 = w64 pa)
    by (etransitivity; [exact P10|];
        first [ exact (eq_trans E22 Hpa) | exact (eq_trans E24 Hpa) | exact (eq_trans E19 Hpa)
              | exact (eq_trans E18 Hpa) ]);
  assert (Hgp' : getr rT 3 = w64 (as_gp B))
    by exact (eq_trans (HPT1 3 ltac:(unfold acallee_saved; lia)) (eq_trans R3 Hgp0));
  assert (Htp' : getr rT 4 = w64 (as_tp B))
    by exact (eq_trans (HPT1 4 ltac:(unfold acallee_saved; lia)) (eq_trans R4 Htp0));
  assert (H8' : getr rT 8 = w64 (x_sp0 cx)) by exact (eq_trans (HPT1 8 ltac:(unfold acallee_saved; lia)) R8);
  assert (Hs0 : s0Z rT = x_sp0 cx)
    by (unfold s0Z; transitivity (bv_unsigned (w64 (x_sp0 cx))); [f_equal; exact H8' | unfold w64; apply unsigned_lit_small; lia]);
  assert (HraT : YK0s.ret_ok (getr rT 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]);
  assert (HraZ : 4096 <= raZ rT)
    by (unfold raZ; change (4096 <= bv_unsigned (getr rT (1%bv : bv 5))); rewrite P1; rewrite unsigned_lit_small by lia; lia);
  assert (Hch : chain_pre ly (rdW W mT) rT ch)
    by (eapply achain_chain_pre;
        [ eapply achain_kept with (lo := 0); [exact HCH | lia | rewrite Etop; lia | exact KEEP]
        | rewrite HspT; lia | exact Hs0 | exact HraZ ])
end.
all: eapply SRr_bind;
  [ lazymatch goal with
    | |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
      exact (afree04_sub SEGS B LAWS pa_segs_low MT AFREE4 W rT mT STK_LLVMFuzzerTestOneInput (x_sp0 cx)
        (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S dT k pa n
        (x_s1 cx - x_sp0 cx) (getr rT 1) ch HJ' Hin Ha0 ltac:(rewrite HspT; lia)
        ltac:(rewrite Zminus_mod, Hs1al, Hal16; reflexivity) ltac:(lia)
        ltac:(unfold ASTACK, STK_LLVMFuzzerTestOneInput; lia)
        Hgp' Htp' eq_refl HraT Hnev Hch Hcov MOK)
    end
  | ].
all: cbv beta; intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hbl & Hfr2 & HK2 & MLE & HJin).
all: rewrite P1; apply (HC ly2 S2 W2 regs2 mem2 md2);
  [ exact HJ2 | exact (aregs_preserved_trans _ _ _ HPT1 HP2) | exact Hbl | exact Hfr2 | | exact MLE ].
all: lazymatch type of HK2 with acall_kept _ _ _ _ _ ?mT _ _ _ _ _ =>
  apply (s24_kept_trans B cx W W W2 mem mT mem2);
  [ apply s24_kept_all; exact (s24_keep_all (w_H W) mem mT KEEP)
  | replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) in HK2 by lia;
    exact (s24_kept_of_acall B MT cx ly S W mT mdv k W2 mem2 _ _ HBASE HJ' HK2 HAF HAS) ]
end.
Qed.
End fr.
End f.
End d.
