(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): segment A12 of reac_segconf_parse_file's walk, the part
   of the cut INV_KV (lib/A/Prog/pf_pieces.v) that lives in memory, and the fact that a runtime call keeps it.
   No machine step and no walk.

   a12_mem is everything of INV_KV read through a reader rd: the objects pf_obj, the 19 spill slots PF_SL and
   slot 0xb0 (at s1 + off, off >= 0), the frame's 144 shadow cells pf_fsh, the spine pf_st (c, cur_name), and
   the key and value strings in buf. a12_geo says where those objects lie; a12_geo_of reads it off INV_KV.
   a12_mem_kept: a call that writes only a window [lo, hi) with alloc_ceiling <= lo and hi <= s1 keeps
   a12_mem, because every address a12_mem reads is either below alloc_ceiling (the class-5 frame, the block c,
   the text, every shadow byte SHADOW_OFF + x / 8 of an x < 2 ^ 47, every image byte below kImgEnd) or in
   [s1, s1 + 0x140) (the slots).
   The shadow knowledge of A12's five inline checks: a12_ra_buf / a12_ra_cn (buf and cur_name addressable, their
   shadow cells being 0 in the scope PF_SC_LINE) and a12_shok1 / a12_shok2 (the SH lists a12_SH1 / a12_SH2 of
   lib/A/Prog/pf_a12_k.v hold).
   Segment A12's proof (the keep lemmas), by the G3 walk owner, 2026-10-30. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase refuse_c
  reac_segconf_parse_file_c SegInstA pf_pieces pf_a5_k pf_a12_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(** ** Arithmetic *)
(* a string's slack ends at the next 8-byte boundary, so it stays below an 8-aligned bound above its NUL *)
Lemma a12_tail_below : forall e ac, e < ac -> ac mod 8 = 0 -> e - e mod 8 + 8 <= ac.
Proof.
intros e ac He Hac.
pose proof (Z.div_mod e 8 ltac:(lia)) as De. pose proof (Z.div_mod ac 8 ltac:(lia)) as Da.
pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as Me.
rewrite Hac in Da. lia.
Qed.

(* the realigned locals base s1 = (sp0 - 0x140) & -32 of a stack window (astk_ok, STK = 12800) *)
Lemma a12_s1_rng : forall {rc : YM05.RunCeil} sp lo hi,
  alloc_ceiling <= lo -> lo + 12800 <= sp -> sp <= hi -> hi <= 2 ^ 47 ->
  alloc_ceiling <= (sp - 0x140) - (sp - 0x140) mod 32 /\ (sp - 0x140) - (sp - 0x140) mod 32 + 0x140 <= 2 ^ 47.
Proof. intros rc sp lo hi H1 H2 H3 H4. pose proof (Z.mod_pos_bound (sp - 0x140) 32 ltac:(lia)). lia. Qed.

Lemma a12_ac8 : forall {rc : YM05.RunCeil}, alloc_ceiling mod 8 = 0.
Proof.
intros rc. pose proof alloc_ceiling_value as (_ & H).
assert (D : (4096 | alloc_ceiling)) by (apply Z.mod_divide; [lia | exact H]).
apply Z.mod_divide; [lia|]. apply (Z.divide_trans 8 4096); [exists 512; reflexivity | exact D].
Qed.

(* the shadow byte of an address below 2 ^ 47 *)
Lemma a12_sh_rng : forall x, 0 <= x < 2 ^ 47 -> 0x7fff8000 <= shadow_addr x < 0x10007fff8000.
Proof.
intros x Hx. pose proof (shadow_addr_bounds x) as H.
unfold kLowMemEnd, kHighShadowEnd, kHighMemEnd in H. apply H. lia.
Qed.

(** ** A reader that agrees with rd on what a fact reads keeps the fact *)
Lemma a12_rdword_keep : forall (rd rd' : reader) a,
  (forall x, a <= x < a + 8 -> rd' x = rd x) -> rdword rd' a = rdword rd a.
Proof. intros rd rd' a K. unfold rdword. rewrite !K by lia. reflexivity. Qed.

Lemma a12_bytes_keep : forall (rd rd' : reader) a bs, sa_bytes rd a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> rd' x = rd x) -> sa_bytes rd' a bs.
Proof. intros rd rd' a bs H K i Hi. rewrite (K (a + Z.of_nat i)) by lia. exact (H i Hi). Qed.

(* a C string with its slack: the bytes, the NUL and the slack up to the next 8-byte boundary *)
Lemma a12_str_keep : forall (rd rd' : reader) p s, sa_str rd p s ->
  (forall x, p <= x < (p + Z.of_nat (length s)) - (p + Z.of_nat (length s)) mod 8 + 8 -> rd' x = rd x) ->
  sa_str rd' p s.
Proof.
intros rd rd' p s ((Hz & Hn) & Ht) K.
pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)) as Hm.
split; [split|].
- intros i Hi. pose proof Hi as Hi'. rewrite length_app in Hi'. cbn [length] in Hi'.
  rewrite (K (p + Z.of_nat i)) by lia. exact (Hz i Hi).
- exact Hn.
- intros x Hx. rewrite (K x) by lia. exact (Ht x Hx).
Qed.

(* the spill slots s1 + off, 0 <= off <= 0x138 *)
Lemma a12_sl_keep : forall (rd rd' : reader) b L, pf_sl rd b L ->
  forallb (fun ov => (0 <=? fst ov) && (fst ov <=? 0x138)) L = true ->
  (forall x, b <= x < b + 0x140 -> rd' x = rd x) -> pf_sl rd' b L.
Proof.
intros rd rd' b L H F K. unfold pf_sl in *.
rewrite Forall_forall in H |- *. rewrite forallb_forall in F.
intros ov Hin. pose proof (F ov Hin) as Fo. apply andb_prop in Fo as [F1 F2].
apply Z.leb_le in F1. apply Z.leb_le in F2.
rewrite (a12_rdword_keep rd rd' (b + fst ov)); [exact (H ov Hin)|].
intros x Hx. apply K. lia.
Qed.

(* the frame's 144 shadow cells *)
Lemma a12_fsh_keep : forall (rd rd' : reader) sh sc, pf_fsh rd sh sc ->
  (forall x, sh <= x < sh + 144 -> rd' x = rd x) -> pf_fsh rd' sh sc.
Proof. intros rd rd' sh sc H K i Hi. rewrite (K (sh + i)) by lia. exact (H i Hi). Qed.

(* printf's stack-protector cells at image A: the GOT word 0xa36d8 and the guard 0x5ff078 *)
Lemma a12_ssp_keep : forall (rd rd' : reader), sa_ssp rd gotwA guardA ->
  (forall x, 0 <= x < kImgEnd + 8 -> rd' x = rd x) -> sa_ssp rd' gotwA guardA.
Proof.
intros rd rd' (H1 & g & H2) K.
assert (E : gotwA = 0xa36d8 /\ guardA = 0x5ff078) by (split; reflexivity). destruct E as [E1 E2].
split.
- rewrite (a12_rdword_keep rd rd' gotwA); [exact H1|]. intros x Hx. apply K. unfold kImgEnd. lia.
- exists g. rewrite (a12_rdword_keep rd rd' guardA); [exact H2|]. intros x Hx. apply K. unfold kImgEnd. lia.
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* an addressable range [q, q + n): amem_range puts it below 2 ^ 47, so every shadow byte it reads is below
   SHADOW_OFF + 2 ^ 44, far below alloc_ceiling *)
Lemma a12_addr_keep : forall (rd rd' : reader) q n, sa_addr rd q n ->
  (forall x, 0 <= x < alloc_ceiling -> rd' x = rd x) -> sa_addr rd' q n.
Proof.
intros rd rd' q n (Hq & Hn & Hm & Hra & Hhv) K.
pose proof alloc_ceiling_value as (Hac & _).
assert (Hq47 : q + n <= 2 ^ 47 - 1).
{ unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hm. lia. }
refine (conj Hq (conj Hn (conj Hm (conj _ _)))).
- intros x Hx. destruct (Hra x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  assert (E : shadow_of_addr SHADOW_OFF x = shadow_addr x) by reflexivity.
  rewrite E in Hs |- *. rewrite (K (shadow_addr x)); [exact Hs|].
  pose proof (a12_sh_rng x ltac:(lia)). lia.
- intros Hn0 s Hs. rewrite (K s); [exact (Hhv Hn0 s Hs)|].
  pose proof (a12_sh_rng q ltac:(lia)) as H1.
  pose proof (a12_sh_rng (q + n - 1) ltac:(lia)) as H2.
  pose proof (Z.mul_div_le (shadow_addr (q + n - 1)) 8 ltac:(lia)) as H3.
  pose proof (Z.div_pos (shadow_addr q) 8 ltac:(lia) ltac:(lia)) as H4.
  lia.
Qed.

Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Section s.
Context {fx : YK11.FPState}.

(** *** The image objects: every byte read is an image byte (below kImgEnd) or its slack *)
Lemma a12_lit_keep : forall (rd rd' : reader) a s, sa_lit SEGS B rd a s ->
  (forall x, 0 <= x < kImgEnd + 8 -> rd' x = rd x) -> sa_lit SEGS B rd' a s.
Proof.
intros rd rd' a s (Ha & Hs & Hp & Hrt & Himg) K.
refine (conj Ha (conj _ (conj Hp (conj Hrt Himg)))).
apply (a12_str_keep rd rd' a s Hs). intros x Hx. apply K.
destruct (Himg (a + Z.of_nat (length s)) ltac:(lia)) as (Hi & _ & _).
pose proof (pa_img_range _ Hi) as Hr.
pose proof (Z.mod_pos_bound (a + Z.of_nat (length s)) 8 ltac:(lia)).
lia.
Qed.

Lemma a12_cat_keep : forall (rd rd' : reader) cat, sa_cat SEGS B rd cat ->
  (forall x, 0 <= x < kImgEnd + 8 -> rd' x = rd x) -> sa_cat SEGS B rd' cat.
Proof.
intros rd rd' cat (Hp & Hi & Hrows) K.
refine (conj Hp (conj Hi _)).
intros i Hlt. destruct (Hrows i Hlt) as (tp & Hw & Hl).
exists tp. split.
- rewrite (a12_rdword_keep rd rd' (pin_spec.row_addr cat i)); [exact Hw|].
  intros x Hx. apply K.
  unfold pin_spec.row_addr, pin_spec.CAT_ROW in Hx. unfold pin_spec.CAT_N in Hlt.
  destruct (Hi x ltac:(unfold pin_spec.CAT_BYTES; lia)) as (Hx' & _ & _).
  pose proof (pa_img_range _ Hx'). lia.
- exact (a12_lit_keep rd rd' tp _ Hl K).
Qed.

Lemma a12_ro_keep : forall (rd rd' : reader), arodata_okP SEGS RLO_A RHI_A B rd ->
  (forall x, 0 <= x < kImgEnd + 8 -> rd' x = rd x) -> arodata_okP SEGS RLO_A RHI_A B rd'.
Proof.
intros rd rd' H K a Hro Hns Hne.
rewrite (K a); [exact (H a Hro Hns Hne)|].
destruct Hro as [(sg & Hin & _ & Hlo) | Hr].
- pose proof (pa_img_range a) as Hb.
  assert (Hb' : 0x10000 <= a < kImgEnd) by (apply Hb; exists sg; split; assumption).
  lia.
- assert (E : RLO_A = 0xa14a0 /\ RHI_A = 0xa3748) by (split; reflexivity).
  unfold kImgEnd. lia.
Qed.

(** *** The caller's objects pf_obj: the text and c below alloc_ceiling, the image objects below kImgEnd *)
Lemma a12_obj_keep : forall v lyc Sc (rd rd' : reader),
  pf_obj B v lyc Sc rd ->
  4096 <= p_t v -> p_t v + Z.of_nat (length (p_s v)) + 1 <= alloc_ceiling ->
  (forall x, 0 <= x < alloc_ceiling -> rd' x = rd x) ->
  pf_obj B v lyc Sc rd'.
Proof.
intros v lyc Sc rd rd' (Hts & Hta & Hth & Hca & Hch & Hcat & Hlit & Hro & Hssp) Ht1 Ht2 LOW.
pose proof alloc_ceiling_value as (Hac & _).
assert (IMG : forall x, 0 <= x < kImgEnd + 8 -> rd' x = rd x).
{ intros x Hx. apply LOW. unfold kImgEnd in Hx. lia. }
refine (conj _ (conj _ (conj Hth (conj _ (conj Hch (conj _ (conj _ (conj _ _)))))))).
- apply (a12_str_keep rd rd' _ _ Hts). intros x Hx. apply LOW.
  assert (He : p_t v + Z.of_nat (length (p_s v)) < alloc_ceiling) by lia.
  pose proof (a12_tail_below _ _ He a12_ac8) as Htb.
  lia.
- exact (a12_addr_keep rd rd' _ _ Hta LOW).
- exact (a12_addr_keep rd rd' _ _ Hca LOW).
- exact (a12_cat_keep rd rd' _ Hcat IMG).
- intros x Hx. exact (a12_lit_keep rd rd' _ _ (Hlit x Hx) IMG).
- exact (a12_ro_keep rd rd' Hro IMG).
- exact (a12_ssp_keep rd rd' Hssp IMG).
Qed.

(** *** The spine pf_st: c (16616 bytes) and cur_name (16 bytes in the frame) *)
Lemma a12_st_keep : forall v pos (rd rd' : reader) cf cur nm k,
  pf_st v pos rd cf cur nm k ->
  4096 <= pf_F v pos -> pf_F v pos + 2048 <= alloc_ceiling ->
  4096 <= p_c v -> p_c v + seg_spec.SEG_C_SIZE <= alloc_ceiling ->
  (forall x, 0 <= x < alloc_ceiling -> rd' x = rd x) ->
  pf_st v pos rd' cf cur nm k.
Proof.
intros v pos rd rd' cf cur nm k ((bs & Hb & Henc) & Hcur & (f & Hf & Hfe) & Hcnt) HF1 HF2 Hc1 Hc2 LOW.
refine (conj _ (conj Hcur (conj _ Hcnt))).
- exists bs. split; [|exact Henc].
  apply (a12_bytes_keep rd rd' _ _ Hb). intros x Hx. apply LOW.
  destruct Henc as (Hlen & _). lia.
- exists f. split; [|exact Hfe].
  apply (a12_bytes_keep rd rd' _ _ Hf). intros x Hx. apply LOW.
  destruct Hfe as (Hlen & _). unfold PF_O_CN in Hx. lia.
Qed.

(** ** The memory part of the cut INV_KV *)
(** Everything of the cut INV_KV that lives in memory, read through rd. *)
Definition a12_mem (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (rd : reader)
  (cf : rconf) (nm : list Z) (k : nat) (gi : nat) (kp vp : Z) (key val : list Z) : Prop :=
  pf_obj B v lyc Sc rd /\
  pf_sl rd (pf_s1 v) (PF_SL v pos) /\
  pf_fsh rd (pf_SH v pos) PF_SC_LINE /\
  pf_st v pos rd cf (Some gi) nm k /\
  sa_str rd kp key /\ sa_str rd vp val /\
  pf_sl rd (pf_s1 v) [(0xb0, seg_spec.rseg_addr (p_c v) gi)].

(** Where the objects of the cut lie: the class-5 frame, the block c, the text, and the realigned locals base.
    The text's bound is its NUL's (sa_heap of length + 1 bytes in a block below alloc_ceiling); the slots reach
    s1 + 0xc0, and astk_ok gives s1 + 0x140 <= sp0 <= 2 ^ 47; the two strings are bounded as pf_inb bounds them. *)
Definition a12_geo (v : pfv) (pos : Z) (gi : nat) (kp vp : Z) (key val : list Z) : Prop :=
  4096 <= pf_F v pos /\ pf_F v pos + 2048 <= alloc_ceiling /\ pf_F v pos mod 32 = 0 /\
  4096 <= p_c v /\ p_c v + seg_spec.SEG_C_SIZE <= alloc_ceiling /\
  4096 <= p_t v /\ p_t v + Z.of_nat (length (p_s v)) + 1 <= alloc_ceiling /\
  alloc_ceiling <= pf_s1 v /\ pf_s1 v + 0x140 <= 2 ^ 47 /\
  (gi < 32)%nat /\
  pf_F v pos + PF_O_BUF <= kp /\ kp + Z.of_nat (length key) < pf_F v pos + PF_O_BUF + 512 /\
  pf_F v pos + PF_O_BUF <= vp /\ vp + Z.of_nat (length val) < pf_F v pos + PF_O_BUF + 512.

(** The geometry follows from the cut itself. *)
Lemma a12_geo_of : forall n v pos lyc Sc (Wc : world SEGS) rX memc mdc cf nm o ln d gi kp vp key val,
  INV_KV B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi kp vp key val ->
  a12_geo v pos gi kp vp key val.
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi kp vp key val HINV.
destruct HINV as ((_ & HFI & HOBJ & _ & _) & _ & HST & HKV & _ & _).
destruct HFI as (HJ & Hly & _).
subst lyc.
destruct HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
destruct Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (STKv : STK_reac_segconf_parse_file = 12800) by (vm_compute; reflexivity).
rewrite STKv in Hslo.
pose proof (a12_s1_rng (pf_sp0 v) _ _ Hceil Hslo Hshi H47) as Hs1.
(* the class-5 frame *)
assert (Hfin : In (5, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS (p_ly v) Sc Wc memc mdc 5 pos HAR Hfin) as (HF4096 & HFceil & _).
destruct (al_frames _ _ LAWS (p_ly v) Sc Wc memc mdc 5 pos HAR Hfin) as (HFal & _).
change (fs_frame_bytes 5) with 2048 in HFceil.
(* the blocks of the text and of c *)
destruct HOBJ as (_ & _ & HHt & _ & HHc & _).
destruct HHc as (bq & mq & Hinq & Hbq1 & Hbq2).
destruct (al_blocks _ _ LAWS (p_ly v) Sc Wc memc mdc bq mq HAR Hinq) as (_ & Hq4096 & Hqceil & _ & _ & _ & Hqm).
pose proof (req_size_pos mq ltac:(lia)) as [_ Hrq].
destruct HHt as (bt & mt & Hint & Hbt1 & Hbt2).
destruct (al_blocks _ _ LAWS (p_ly v) Sc Wc memc mdc bt mt HAR Hint) as (_ & Ht4096 & Htceil & _ & _ & _ & Htm).
pose proof (req_size_pos mt ltac:(lia)) as [_ Hrt].
unfold pf_len in Hbt2.
(* cur = Some gi is an entry of at most 32 *)
destruct HST as ((bs & _ & Henc) & Hcur & _ & _).
destruct Henc as (_ & Hn32 & _).
cbn [pf_cur_ok] in Hcur.
(* the key and the value in buf *)
destruct HKV as (_ & _ & Hkinb & _ & Hvinb).
unfold pf_inb in Hkinb, Hvinb.
unfold a12_geo.
refine (conj HF4096 (conj HFceil (conj HFal (conj _ (conj _ (conj _ (conj _ (conj (proj1 Hs1)
  (conj (proj2 Hs1) (conj _ (conj (proj1 Hkinb) (conj (proj2 Hkinb)
  (conj (proj1 Hvinb) (proj2 Hvinb)))))))))))))); lia.
Qed.

(** A call that writes only its own scratch window [lo, hi) below the locals base keeps all of it. *)
Lemma a12_mem_kept : forall v pos lyc Sc (rd rd' : reader) cf nm k gi kp vp key val lo hi,
  a12_mem v pos lyc Sc rd cf nm k gi kp vp key val ->
  a12_geo v pos gi kp vp key val ->
  alloc_ceiling <= lo -> hi <= pf_s1 v -> hi <= 2 ^ 64 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> rd' a = rd a) ->
  a12_mem v pos lyc Sc rd' cf nm k gi kp vp key val.
Proof.
intros v pos lyc Sc rd rd' cf nm k gi kp vp key val lo hi HM HG Hlo Hhi H64 K.
pose proof alloc_ceiling_value as (Hac & _).
destruct HG as (HF1 & HF2 & _ & Hc1 & Hc2 & Ht1 & Ht2 & Hs1 & Hs2 & _ & Hk1 & Hk2 & Hv1 & Hv2).
assert (LOW : forall x, 0 <= x < alloc_ceiling -> rd' x = rd x) by (intros x Hx; apply K; lia).
assert (HIGH : forall x, pf_s1 v <= x < pf_s1 v + 0x140 -> rd' x = rd x) by (intros x Hx; apply K; lia).
destruct HM as (HOBJ & HSL & HFSH & HST & HK & HV & HSLB).
refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
- exact (a12_obj_keep v lyc Sc rd rd' HOBJ Ht1 Ht2 LOW).
- apply (a12_sl_keep rd rd' _ _ HSL); [reflexivity | exact HIGH].
- apply (a12_fsh_keep rd rd' _ _ HFSH). intros x Hx. apply LOW.
  pose proof (a12_sh_rng (pf_F v pos) ltac:(lia)) as Hsh. unfold pf_SH in Hx. lia.
- exact (a12_st_keep v pos rd rd' cf (Some gi) nm k HST HF1 HF2 Hc1 Hc2 LOW).
- apply (a12_str_keep rd rd' _ _ HK). intros x Hx. apply LOW.
  pose proof (Z.mod_pos_bound (kp + Z.of_nat (length key)) 8 ltac:(lia)).
  unfold PF_O_BUF in Hk1, Hk2. lia.
- apply (a12_str_keep rd rd' _ _ HV). intros x Hx. apply LOW.
  pose proof (Z.mod_pos_bound (vp + Z.of_nat (length val)) 8 ltac:(lia)).
  unfold PF_O_BUF in Hv1, Hv2. lia.
- apply (a12_sl_keep rd rd' _ _ HSLB); [reflexivity | exact HIGH].
Qed.

(** ** The shadow knowledge of A12's five inline checks
    #22, #23, #24 read val[0] / val[1] in buf (load1); #33, #34 write cur->ignore / cur->ignore_set (store4).
    The token executor decides each check from an SH entry (lib/A/Prog/pf_a12_k.v a12_SH1 / a12_SH2 over the
    shadow base a12_Bx = s6); here each entry is shent_ok. *)
(* cur_name's two shadow cells (4, 5) are 0 in the scope PF_SC_LINE; buf's (8 .. 71) are pf_a5_k.v's a5_shb_in *)
Lemma a12_shb_cn : forall i, 4 <= i < 6 -> pf_shb PF_SC_LINE i = 0.
Proof.
intros i Hi. unfold pf_shb.
replace (i <? 4) with false by (symmetry; apply Z.ltb_ge; lia).
replace (i <? 6) with true by (symmetry; apply Z.ltb_lt; lia).
reflexivity.
Qed.

(* an object at F + o (o and its length n 8-aligned, inside the frame's first 1152 bytes) whose shadow cells
   are 0 is addressable *)
Lemma a12_ra_frame : forall v pos (rd : reader) sc o n,
  pf_F v pos mod 32 = 0 -> o mod 8 = 0 -> n mod 8 = 0 -> 0 <= o -> 0 <= n -> o + n <= 1152 ->
  pf_fsh rd (pf_SH v pos) sc ->
  (forall i, o / 8 <= i < o / 8 + n / 8 -> pf_shb sc i = 0) ->
  range_addressable rd SHADOW_OFF (pf_F v pos + o) n.
Proof.
intros v pos rd sc o n HF32 Ho Hn Ho0 Hn0 Hon HFSH HZ.
pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)) as DF. rewrite HF32, Z.add_0_r in DF.
pose proof (Z.div_mod o 8 ltac:(lia)) as DO. rewrite Ho, Z.add_0_r in DO.
pose proof (Z.div_mod n 8 ltac:(lia)) as DN. rewrite Hn, Z.add_0_r in DN.
assert (E8 : pf_F v pos / 8 = 4 * (pf_F v pos / 32)) by (symmetry; apply Z.div_unique_exact; lia).
assert (EFo : (pf_F v pos + o) / 8 = 4 * (pf_F v pos / 32) + o / 8) by (symmetry; apply Z.div_unique_exact; lia).
apply zero_shadow_range.
- replace (pf_F v pos + o) with ((4 * (pf_F v pos / 32) + o / 8) * 8) by lia. apply Z_mod_mult.
- exact Hn.
- intros i Hi. unfold shadow_of_addr. rewrite EFo.
  replace (SHADOW_OFF + (4 * (pf_F v pos / 32) + o / 8) + i) with (pf_SH v pos + (o / 8 + i))
    by (unfold pf_SH, shadow_addr; rewrite E8; ring).
  rewrite (HFSH (o / 8 + i)) by lia.
  f_equal. apply HZ. lia.
Qed.

(** buf's 512 bytes are addressable: its 64 shadow cells are 0 in the scope PF_SC_LINE. *)
Lemma a12_ra_buf : forall v pos (rd : reader),
  pf_F v pos mod 32 = 0 -> pf_fsh rd (pf_SH v pos) PF_SC_LINE ->
  range_addressable rd SHADOW_OFF (pf_F v pos + PF_O_BUF) 512.
Proof.
intros v pos rd HF HFSH. unfold PF_O_BUF.
apply (a12_ra_frame v pos rd PF_SC_LINE 0x40 512 HF eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(lia) HFSH).
intros i Hi. change (0x40 / 8) with 8 in Hi. change (512 / 8) with 64 in Hi.
rewrite (a5_shb_in PF_SC_LINE i) by lia. reflexivity.
Qed.

(** cur_name's 16 bytes, likewise (cells 4 and 5 are 0 in PF_SC_LINE). *)
Lemma a12_ra_cn : forall v pos (rd : reader),
  pf_F v pos mod 32 = 0 -> pf_fsh rd (pf_SH v pos) PF_SC_LINE ->
  range_addressable rd SHADOW_OFF (pf_F v pos + PF_O_CN) 16.
Proof.
intros v pos rd HF HFSH. unfold PF_O_CN.
apply (a12_ra_frame v pos rd PF_SC_LINE 0x20 16 HF eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(lia) HFSH).
intros i Hi. change (0x20 / 8) with 4 in Hi. change (16 / 8) with 2 in Hi.
apply a12_shb_cn. lia.
Qed.

(* one SH entry over a register atom m holding p, for an addressable range [p + lo, p + hi) of the application
   range (so outside the shadow band) *)
Lemma a12_shent : forall (E0 : env) (W : world SEGS) (mem : word -> option byte) (m : nat) p lo hi,
  U E0 a12_Bx = SHADOW_OFF -> U E0 (SOff m 0) = p -> lo < hi ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (p + lo) (hi - lo) ->
  in_app (p + lo) (hi - lo) ->
  shent_ok SEGS a12_Bx E0 (mrestrict (w_H W) mem) (mkSHE m lo hi).
Proof.
intros E0 W mem m p lo hi HB Hm Hlh HR Happ.
apply (shent_ok_of_range SEGS (w_H W) mem E0 a12_Bx m (p + lo) (hi - lo) p lo hi HR HB Hm); [lia | lia |].
intros x Hx. rewrite Z.min_l in Hx by lia. rewrite Z.max_r in Hx by lia.
unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

(** the SH list of a run that has not yet read the value's second byte *)
Lemma a12_shok1 : forall (E0 : env) (W : world SEGS) (mem : word -> option byte) v (pos : Z) gi vp,
  U E0 a12_Bx = SHADOW_OFF ->
  U E0 (SOff 25 0) = vp -> U E0 (SOff 20 0) = seg_spec.rseg_addr (p_c v) gi ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF vp 1 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF
    (seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_IGNORE) 8 ->
  in_app vp 1 -> in_app (seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_IGNORE) 8 ->
  sh_ok SEGS a12_Bx a12_SH1 E0 (mrestrict (w_H W) mem).
Proof.
intros E0 W mem v pos gi vp HB H25 H20 HRv HRc Hav Hac.
unfold sh_ok, a12_SH1. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply (a12_shent E0 W mem 25%nat vp 0 1 HB H25 ltac:(lia)).
  + rewrite Z.add_0_r. exact HRv.
  + rewrite Z.add_0_r. exact Hav.
- apply (a12_shent E0 W mem 20%nat _ seg_spec.RS_IGNORE (seg_spec.RS_IGNORE_SET + 4) HB H20
    ltac:(unfold seg_spec.RS_IGNORE, seg_spec.RS_IGNORE_SET; lia)); [exact HRc | exact Hac].
Qed.

(** the same once the first byte is known non-NUL, so the second byte is inside buf too *)
Lemma a12_shok2 : forall (E0 : env) (W : world SEGS) (mem : word -> option byte) v (pos : Z) gi vp,
  U E0 a12_Bx = SHADOW_OFF ->
  U E0 (SOff 25 0) = vp -> U E0 (SOff 20 0) = seg_spec.rseg_addr (p_c v) gi ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF vp 2 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF
    (seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_IGNORE) 8 ->
  in_app vp 2 -> in_app (seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_IGNORE) 8 ->
  sh_ok SEGS a12_Bx a12_SH2 E0 (mrestrict (w_H W) mem).
Proof.
intros E0 W mem v pos gi vp HB H25 H20 HRv HRc Hav Hac.
unfold sh_ok, a12_SH2. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply (a12_shent E0 W mem 25%nat vp 0 2 HB H25 ltac:(lia)).
  + rewrite Z.add_0_r. exact HRv.
  + rewrite Z.add_0_r. exact Hav.
- apply (a12_shent E0 W mem 20%nat _ seg_spec.RS_IGNORE (seg_spec.RS_IGNORE_SET + 4) HB H20
    ltac:(unfold seg_spec.RS_IGNORE, seg_spec.RS_IGNORE_SET; lia)); [exact HRc | exact Hac].
Qed.

End s.
End e.
End f.
End d.
