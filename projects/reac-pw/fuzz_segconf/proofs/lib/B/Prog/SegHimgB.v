(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): the twin of image A's
   lib/A/Prog/SegHimgA.v. The harness contract's image premise seg_himg (lib/B/Prog/LLVMFuzzerTestOneInput_c.v) at
   lib/B/Prog/SegInstB.v's terms, at any allocator state of a record B with SegBSyms (lib/B/YF0m.v) whose view keeps
   the read-only image (arodata_okP: the program interface's pre gives it at the call, YCfn's tfib_lib_pre_x, so the
   close's bridge lib/B/Prog/SegLibX.v applies seg_himg_at at the entry state). Every image number comes from image
   B's listing terms (SegInstB) and records (SegRecBase, SegRecImg, SegRecCells) and is checked by computation here.
   Three facts image A's listing states in SegInstB / SegRecCells are stated in this file over image B's terms:
   nonul_ok (no image number), img_mod40, img_roles (SegInstB's reader) and seg_ssp (SegRecCells.seg_rec_cells'
   guard conjunct, at SegInstB's gotwA / guardA).
   Where each conjunct comes from:
   - the bytes (the cap multiplier, every literal of both translation units, the catalogue's and m_key.words' row
     pointers and their tokens, m_key.role's entries): SegInstB's computations over the image reader img_rd, moved to
     the state's view by arodata_okP at bytes this file checks are read-only image bytes that the runtime does not own
     and that are not the errno cell (range_ok_b);
   - each literal's and token's slack after its NUL: SegABase.sa_tail_of_romtail from SegInstB's ROM tails;
   - the pins (sa_pinned): the listing's lib/A/Prog/SegRecBase.v, seg_lit_pinned over its seg_lit_objs (each
     literal's (address, size) is checked to be a row of it), seg_cat_pinned, and crf_rd_b_addr for m_key.words,
     m_key.role and longl (their seg_rd_b checks, by computation);
   - sa_img: in a loaded segment (crf_img_rangeb) and apart from the record's owned statics and errno cell (SegBSyms'
     ts_owned / ts_errno), by computation;
   - the stack-protector cells: seg_ssp below (SegRecCells.seg_rec_cells at the state); longl's ROM tail:
     SegInstB.longlA_romtail.
   proves no function (kind: image facts; the close's discharge of the bridge's seg_himg premise). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YM05 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0s YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YF0m YB1v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YE2k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegGlob SegRecBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegRecImg SegRecCells SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require LLVMFuzzerTestOneInput_c m_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ======================================= the checks ======================================= *)
(* [q, q + n) is read-only image (in_roP at the image window SEG_RLO .. SEG_RHI), apart from the owned statics and
   the errno cell of every record with SegBSyms *)
Definition range_ok_b (q n : Z) : bool :=
crf_ro_rangeb tfibsegs SEG_RLO SEG_RHI (q, n) && forallb (zr_disjointb (q, n)) Tfib_owned_static &&
zr_disjointb (q, n) (TFIB_ERRNO, 4).
(* [q, q + n) is in a loaded segment, apart from the owned statics and the errno cell (sa_img) *)
Definition img_ok_b (q n : Z) : bool :=
crf_img_rangeb tfibsegs (q, n) && forallb (zr_disjointb (q, n)) Tfib_owned_static &&
zr_disjointb (q, n) (TFIB_ERRNO, 4).
(* (q, n) is a row of the listing's seg_lit_objs, whose rows seg_lit_pinned pins *)
Definition in_lit_objs_b (q n : Z) : bool := existsb (fun e => (fst e =? q) && (snd e =? n)) seg_lit_objs.
(* the C string s at a, as sa_lit asks it, and apart from longl *)
Definition lit_ok_b (a : Z) (s : list Z) : bool :=
(0 <? a) && range_ok_b a (Z.of_nat (length s) + 1) && img_ok_b a (Z.of_nat (length s) + 1) &&
in_lit_objs_b a (Z.of_nat (length s) + 1) && SegInstB.img_bytes_b a (s ++ [0]) &&
negb (existsb (Z.eqb 0) s) && SegInstB.romtail_b (a + Z.of_nat (length s)) &&
(a + (Z.of_nat (length s) + 1) <=? SegInstB.longlA).
(* a table row: its 8 bytes are read-only image bytes, and the pointer they hold is the C string s *)
Definition row_ok_b (row : Z) (s : list Z) : bool :=
range_ok_b row 8 && match rdword SegInstB.img_rd row with Some tp => lit_ok_b tp s | None => false end.

Lemma in_lit_objs_ok : forall q n, in_lit_objs_b q n = true -> In (q, n) seg_lit_objs.
Proof.
intros q n H. apply existsb_exists in H as ([q' n'] & Hin & E). cbn [fst snd] in E.
apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. subst. exact Hin.
Qed.

(* image B's forms of three image-A listing facts (lib/A/Prog/SegInstA.v nonul_ok, img_mod40, img_roles) *)
Lemma nonul_ok : forall s, negb (existsb (Z.eqb 0) s) = true -> ~ In 0 s.
Proof.
intros s H Hin. apply negb_true_iff in H.
assert (existsb (Z.eqb 0) s = true) by (apply existsb_exists; exists 0; split; [exact Hin | apply Z.eqb_refl]).
congruence.
Qed.
Lemma img_mod40 : SegABase.sa_val SegInstB.img_rd SegInstB.mod40A 8 LLVMFuzzerTestOneInput_c.LTOI_MOD40.
Proof. intros k Hk. do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia. Qed.
Lemma img_roles : forall i, (i < 5)%nat -> SegABase.sa_val SegInstB.img_rd (SegInstB.rolesA + 4 * Z.of_nat i) 4 (Z.of_nat i).
Proof.
intros i Hi k Hk.
do 5 (destruct i as [|i]; [do 4 (destruct k as [|k]; [vm_compute; reflexivity|]); lia|]). lia.
Qed.

(* the computations, image B *)
Lemma lits_fz_ok :
forallb (fun s => lit_ok_b (SegInstB.seg_litA_fz s) s) LLVMFuzzerTestOneInput_c.LTOI_FZ_LITS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lits_rc_ok :
forallb (fun s => lit_ok_b (SegInstB.seg_litA_rc s) s) LLVMFuzzerTestOneInput_c.LTOI_RC_LITS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cat_rows_ok : forallb (fun i => row_ok_b (pin_spec.row_addr SegInstB.catA i)
  (seg_spec.zs (pin_spec.tok_bytes i))) (seq 0 pin_spec.CAT_N) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma words_rows_ok : forallb (fun i => row_ok_b (SegInstB.wordsA + 8 * Z.of_nat i)
  (nth i m_file_c.MF_ROLE_WORDS [])) (seq 0 5) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma tables_ok :
img_ok_b SegInstB.mod40A 8 && img_ok_b SegInstB.catA pin_spec.CAT_BYTES && img_ok_b SegInstB.wordsA 40 &&
img_ok_b SegInstB.rolesA 20 && img_ok_b SegInstB.longlA LLVMFuzzerTestOneInput_c.LONGL_N &&
range_ok_b SegInstB.mod40A 8 && range_ok_b SegInstB.rolesA 20 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma tables_rd_b :
seg_rd_b SegInstB.wordsA 40 && seg_rd_b SegInstB.rolesA 20 &&
seg_rd_b SegInstB.longlA LLVMFuzzerTestOneInput_c.LONGL_N = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cat_apart : SegInstB.catA + pin_spec.CAT_BYTES <= SegInstB.longlA.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

(* =================================== at a state of the record =================================== *)
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance YE2k.tfib_sink_head | 0.
Variable B : asyms.
Hypothesis HB : SegBSyms B.
Let LAWS : AR_laws tfibsegs B := YG0q.AR_laws_ok tfibsegs B.
Let IMG := SegRecImg.seg_img_facts_tfib B HB.

(* the stack-protector cells at SegInstB's terms: the guard conjunct of SegRecCells.seg_rec_cells (image B's GOT word
   0xa3e98 holds the guard's address 0x5ff838; image A's lib/A/Prog/SegRecCells.v seg_ssp) *)
Lemma seg_ssp : forall ly S (W : world tfibsegs) mem md, AR tfibsegs B ly S W mem md ->
  sa_ssp (aview tfibsegs (w_H W) mem) SegInstB.gotwA SegInstB.guardA.
Proof.
intros ly S W mem md HAR.
replace SegInstB.gotwA with 0xa3e98 by (vm_compute; reflexivity).
replace SegInstB.guardA with 0x5ff838 by (vm_compute; reflexivity).
exact (proj1 (proj2 (SegRecCells.seg_rec_cells tfibsegs B LAWS HB IMG ly S W mem md HAR))).
Qed.

Lemma unowned_of_b : forall q n, forallb (zr_disjointb (q, n)) Tfib_owned_static = true ->
  zr_disjointb (q, n) (TFIB_ERRNO, 4) = true -> forall x, q <= x < q + n ->
  ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4).
Proof.
intros q n H1 H2 x Hx. rewrite (ts_owned B HB), (ts_errno B HB). split.
- apply (crf_disj_notin (q, n)); [exact H1 | unfold in_zr; cbn [fst snd]; lia].
- intros He. unfold zr_disjointb in H2. cbn [fst snd] in H2.
  apply orb_prop in H2 as [H2|H2]; apply Z.leb_le in H2; lia.
Qed.

Lemma img_ok_sa_img : forall q n, img_ok_b q n = true -> sa_img tfibsegs B q n.
Proof.
intros q n H x Hx. unfold img_ok_b in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
destruct (unowned_of_b q n H2 H3 x Hx) as [Ho He]. split; [|split; assumption].
apply (crf_img_rangeb_ok tfibsegs (q, n) x H1). unfold in_zr. cbn [fst snd]. lia.
Qed.

(* at a read-only, unowned image byte the view is the image's byte *)
Lemma range_ok_view : forall (rd : reader), arodata_okP tfibsegs SEG_RLO SEG_RHI B rd ->
  forall q n, range_ok_b q n = true -> forall x, q <= x < q + n -> rd x = SegInstB.img_rd x.
Proof.
intros rd HRO q n H x Hx. unfold range_ok_b in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
destruct (unowned_of_b q n H2 H3 x Hx) as [Ho He].
assert (Hro : in_roP tfibsegs SEG_RLO SEG_RHI x)
  by (apply (crf_ro_rangeb_ok tfibsegs SEG_RLO SEG_RHI (q, n) x H1); unfold in_zr; cbn [fst snd]; lia).
rewrite (HRO x Hro Ho He). reflexivity.
Qed.

Lemma rdword_view : forall (rd : reader), arodata_okP tfibsegs SEG_RLO SEG_RHI B rd ->
  forall a, range_ok_b a 8 = true -> rdword rd a = rdword SegInstB.img_rd a.
Proof.
intros rd HRO a H. unfold rdword.
rewrite (range_ok_view rd HRO a 8 H a), (range_ok_view rd HRO a 8 H (a + 1)), (range_ok_view rd HRO a 8 H (a + 2)),
  (range_ok_view rd HRO a 8 H (a + 3)), (range_ok_view rd HRO a 8 H (a + 4)), (range_ok_view rd HRO a 8 H (a + 5)),
  (range_ok_view rd HRO a 8 H (a + 6)), (range_ok_view rd HRO a 8 H (a + 7)) by lia.
reflexivity.
Qed.

Lemma pinned_of_rd_b : forall q n, seg_rd_b q n = true -> sa_pinned tfibsegs B q n.
Proof. intros q n Hb ly S W mem md HAR. exact (crf_rd_b_addr tfibsegs B LAWS HB q n Hb ly S W mem md HAR). Qed.

Lemma lit_ok_sa_lit : forall H mem a s, arodata_okP tfibsegs SEG_RLO SEG_RHI B (aview tfibsegs H mem) ->
  lit_ok_b a s = true ->
  sa_lit tfibsegs B (aview tfibsegs H mem) a s /\
  sa_apart_all a (Z.of_nat (length s) + 1) (LLVMFuzzerTestOneInput_c.ltoi_PG SegInstB.longlA).
Proof.
intros H mem a s HRO Hok. unfold lit_ok_b in Hok.
apply andb_prop in Hok as [Hok Hlg]. apply andb_prop in Hok as [Hok Hrt]. apply andb_prop in Hok as [Hok Hnn].
apply andb_prop in Hok as [Hok Hby]. apply andb_prop in Hok as [Hok Hin]. apply andb_prop in Hok as [Hok Him].
apply andb_prop in Hok as [Hpos Hrg].
split.
- split; [apply Z.ltb_lt; exact Hpos|].
  split.
  + split; [split|].
    * intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
      rewrite (range_ok_view _ HRO a (Z.of_nat (length s) + 1) Hrg (a + Z.of_nat i)) by lia.
      apply (SegInstB.img_bytes_b_ok _ _ Hby). rewrite length_app. cbn [length]. exact Hi.
    * exact (nonul_ok s Hnn).
    * exact (sa_tail_of_romtail tfibsegs H mem _ (SegInstB.romtail_b_ok _ Hrt)).
  + split; [apply (seg_lit_pinned tfibsegs B LAWS HB); exact (in_lit_objs_ok _ _ Hin)|].
    split; [exact (SegInstB.romtail_b_ok _ Hrt) | exact (img_ok_sa_img _ _ Him)].
- unfold LLVMFuzzerTestOneInput_c.ltoi_PG, sa_apart_all. constructor; [|constructor].
  cbn [fst snd]. left. apply Z.leb_le in Hlg. lia.
Qed.

Lemma row_ok_lit : forall H mem row s, arodata_okP tfibsegs SEG_RLO SEG_RHI B (aview tfibsegs H mem) ->
  row_ok_b row s = true ->
  exists tp, rdword (aview tfibsegs H mem) row = Some tp /\ sa_lit tfibsegs B (aview tfibsegs H mem) tp s.
Proof.
intros H mem row s HRO Hok. unfold row_ok_b in Hok. apply andb_prop in Hok as [Hr Hm].
destruct (rdword SegInstB.img_rd row) as [tp|] eqn:E; [|discriminate Hm].
exists tp. split; [rewrite (rdword_view _ HRO row Hr); exact E | exact (proj1 (lit_ok_sa_lit H mem tp s HRO Hm))].
Qed.

(* the harness contract's image premise at a state of B whose view keeps the read-only image *)
Theorem seg_himg_at : forall ly S (W : world tfibsegs) mem md, AR tfibsegs B ly S W mem md ->
  arodata_okP tfibsegs SEG_RLO SEG_RHI B (aview tfibsegs (w_H W) mem) ->
  LLVMFuzzerTestOneInput_c.seg_himg tfibsegs B SegInstB.longlA SegInstB.mod40A SegInstB.catA SegInstB.wordsA
    SegInstB.rolesA SegInstB.gotwA SegInstB.guardA SegInstB.seg_litA_fz SegInstB.seg_litA_rc
    (aview tfibsegs (w_H W) mem).
Proof.
intros ly S W mem md HAR HRO.
pose proof tables_ok as HT.
apply andb_prop in HT as [HT Hr2]. apply andb_prop in HT as [HT Hr1]. apply andb_prop in HT as [HT Hl].
apply andb_prop in HT as [HT Hro]. apply andb_prop in HT as [HT Hw]. apply andb_prop in HT as [Hm Hc].
pose proof tables_rd_b as HP. apply andb_prop in HP as [HP Hpl]. apply andb_prop in HP as [Hpw Hpr].
unfold LLVMFuzzerTestOneInput_c.seg_himg.
split.
{ intros k Hk. rewrite (range_ok_view _ HRO _ 8 Hr1 (SegInstB.mod40A + Z.of_nat k)) by lia.
  exact (img_mod40 k Hk). }
split; [exact (img_ok_sa_img _ _ Hm)|].
split; [intros s Hs; exact (lit_ok_sa_lit (w_H W) mem _ s HRO (proj1 (forallb_forall _ _) lits_fz_ok s Hs))|].
split; [intros s Hs; exact (lit_ok_sa_lit (w_H W) mem _ s HRO (proj1 (forallb_forall _ _) lits_rc_ok s Hs))|].
split.
{ unfold sa_cat. split; [exact (seg_cat_pinned tfibsegs B LAWS HB)|]. split; [exact (img_ok_sa_img _ _ Hc)|].
  intros i Hi. apply (row_ok_lit (w_H W) mem _ _ HRO).
  exact (proj1 (forallb_forall _ _) cat_rows_ok i (proj2 (in_seq _ _ _) (conj (Nat.le_0_l i) Hi))). }
split.
{ unfold LLVMFuzzerTestOneInput_c.ltoi_PG, sa_apart_all. constructor; [|constructor].
  cbn [fst snd]. left. exact cat_apart. }
split.
{ unfold m_file_c.mf_words. split; [exact (pinned_of_rd_b _ _ Hpw)|]. split; [exact (img_ok_sa_img _ _ Hw)|].
  intros i Hi. apply (row_ok_lit (w_H W) mem _ _ HRO).
  exact (proj1 (forallb_forall _ _) words_rows_ok i (proj2 (in_seq _ _ _) (conj (Nat.le_0_l i) Hi))). }
split.
{ unfold m_file_c.mf_roles. split; [exact (pinned_of_rd_b _ _ Hpr)|]. split; [exact (img_ok_sa_img _ _ Hro)|].
  intros i Hi k Hk.
  rewrite (range_ok_view _ HRO _ 20 Hr2 (SegInstB.rolesA + 4 * Z.of_nat i + Z.of_nat k)) by lia.
  exact (img_roles i Hi k Hk). }
split; [exact (seg_ssp ly S W mem md HAR)|].
split; [exact (pinned_of_rd_b _ _ Hpl)|].
split; [exact SegInstB.longlA_romtail|].
split; [exact (img_ok_sa_img _ _ Hl)|].
unfold sa_disj, SegInstB.gotwA, SegInstB.guardA, SegInstB.mod40A, SegInstB.longlA, A_LONGL,
  LLVMFuzzerTestOneInput_c.LONGL_N.
repeat split; lia.
Qed.
End h.
