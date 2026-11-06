(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): segment B1 of
   reac_segconf_parse_file's walk (lib/B/Prog/pf_seg_B1.v), the cut's objects carried from the entry to FTAKEN.
   The B1 segment lane of the image-B G3 walk owner, 2026-10-30; the form of the image-A G3 walk owner's image-A segment kit lib/A/Prog/pf_a2_g.v
   (pa2_keep_obj / pa2_keep_lab / pa2_keep_rconf, commit c181e576cd21), re-derived for B1's step.
   B1 runs the prologue (stores only to its own stack slots, above alloc_ceiling) and calls __asan_stack_malloc_5,
   whose kit post (YG0d.v astack_malloc_realizes, through PaCall.v aj_stack_malloc_atS) keeps, of the bytes below
   alloc_ceiling, exactly the live blocks, the image bytes the runtime does not own and the side-stack frames of the
   entry state with their shadow (YCbq.v acall_kept with E = False). So each object of FTAKEN's pf_obj / pf_lab /
   sa_rconf is re-given at the new reader rd' from three keep clauses (b1_K) and the AR of the new state:
   - the bytes: the text, the block c and a heap label by the block clause, every literal, the catalogue words and an
     image label by the image clause (sa_img), a frame label by the frames clause;
   - the shadow: a heap object's from the new AR (reac_segconf_parse.v sa_addr_of_heap), a frame label's cells by the
     frames clause and its hull by PaLibF.v shadow_hull_vis_of_frame, an image object's by sa_pinned at the new AR;
   - a string's tail: a heap string's by YG0d_tail.v AR_block_word_vis at the new AR, a frame label's from the
     frame's presence (AR_frames_law), a literal's and an image label's from the ROM (sa_romtail, sa_pinned_tail);
   - arodata_okP by the image clause (in_roP is inside the image: reac_segconf_parse.v in_roP_img under VRO);
     the stack-protector cells by SSPX at the new AR (the image-A G3 walk owner's SSPX, the B parse walk's hypothesis of that name).
   b1_K_chain gives b1_K at FTAKEN's reader from the three steps of B1. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegAddr SegPa SegObj
  SegGlob PaLibF.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase refuse_c
  reac_segconf_parse_file_c SegInstB pf_pieces.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require reac_segconf_parse.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
(* the listing's read-only range (B's SegObj.v; the pinned instance gives it by computation) *)
Hypothesis VRO : seg_val_relro (PI := PI).
(* SSPX (the image-A G3 walk owner's hypothesis of the same name, at image B's cells; lib/B/Prog/reac_segconf_parse.v takes it too):
   the stack-protector cells at every AR state, which the allocator record pins; image B's stage-2 SegRecCells gives
   it from SegBSyms, as SegRecCells.seg_rec_cells does on image A *)
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* what B1 keeps of the entry reader rd0 at a later reader rd', state ly / S at the entry *)
Definition b1_K (ly : alayout) (S : astate) (rd0 rd' : reader) : Prop :=
  (forall b m i, In (b, m) (ablocks B ly S) -> 0 <= i < req_size m -> rd' (b + i) = rd0 (b + i)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     rd' a = rd0 a) /\
  (forall cid pos a, In (cid, pos) (frames S) ->
     (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
     rd' a = rd0 a).

(* the three steps of B1: the prologue run keeps every byte below alloc_ceiling, the stack malloc keeps what
   acall_kept keeps, the run after it keeps every byte *)
Lemma b1_K_chain : forall ly S (W : world SEGS) mem md mem1 mem2 mem3 lo hi,
  AR SEGS B ly S W mem md ->
  (forall a, 0 <= a < alloc_ceiling -> rdW W mem1 a = rdW W mem a) ->
  acall_kept SEGS B ly S W mem1 W mem2 lo hi (fun _ => False) ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW W mem3 a = rdW W mem2 a) ->
  b1_K ly S (rdW W mem) (rdW W mem3).
Proof.
intros ly S W mem md mem1 mem2 mem3 lo hi HAR KL HK K3.
destruct HK as (_ & KB & KI & KF & _ & _).
pose proof asan_consts as (C1 & C2 & _).
split; [|split].
- intros b m i Hb Hi.
  destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hb) as (_ & H4 & Hc & _).
  rewrite K3 by lia. rewrite (KB b m i Hb Hi) by (intros []). apply KL. lia.
- intros a Hi Ho He. pose proof (pa_img_range a Hi) as Hr. unfold kImgEnd in Hr.
  rewrite K3 by lia. rewrite (KI a Hi Ho He). apply KL. lia.
- intros cid pos a Hin Ha.
  destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (Hf0 & Hfc & _).
  assert (HR : 0 <= a < alloc_ceiling).
  { unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF in Ha. cbn [fst snd] in Ha.
    pose proof (fs_frame_bytes_nonneg cid).
    assert (frame_addr ly cid pos / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
    assert (fs_frame_bytes cid / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
    pose proof (Z.div_pos (frame_addr ly cid pos) 8 ltac:(lia) ltac:(lia)). lia. }
  rewrite K3 by lia. rewrite (KF cid pos a Hin Ha) by (intros []). apply KL. exact HR.
Qed.

Section k.
Context {fx : YK11.FPState}.
Variable v : pfv.
Variables (S2 : astate) (mem' : word -> option byte) (md' : Model).
#[local] Notation rd0 := (rdW (p_W v) (p_mem v)).
#[local] Notation rd' := (rdW (p_W v) mem').
Hypothesis HAR' : AR SEGS B (p_ly v) S2 (p_W v) mem' md'.
Hypothesis Eab : ablocks B (p_ly v) S2 = ablocks B (p_ly v) (p_S v).
Hypothesis Hfr : forall cid pos, In (cid, pos) (frames (p_S v)) -> In (cid, pos) (frames S2).
Hypothesis K : b1_K (p_ly v) (p_S v) rd0 rd'.

Lemma b1_k_img : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  rd' a = rd0 a.
Proof. exact (proj1 (proj2 K)). Qed.
Lemma b1_k_imgs : forall a n, sa_img SEGS B a n -> forall x, a <= x < a + n -> rd' x = rd0 x.
Proof. intros a n Hi x Hx. destruct (Hi x Hx) as (H1 & H2 & H3). exact (b1_k_img x H1 H2 H3). Qed.
Lemma b1_k_heap : forall q n, sa_heap B (p_ly v) (p_S v) q n -> forall x, q <= x < q + n -> rd' x = rd0 x.
Proof.
intros q n (b & m & Hb & H1 & H2) x Hx.
pose proof (req_size_pos m) as Hr.
destruct (Z_le_gt_dec 0 m) as [Hm|Hm]; [|lia].
specialize (Hr Hm).
replace x with (b + (x - b)) by lia. apply (proj1 K b m (x - b) Hb). lia.
Qed.
(* the heap block of a sa_heap range, at the new state *)
Lemma b1_heap2 : forall q n, sa_heap B (p_ly v) (p_S v) q n -> sa_heap B (p_ly v) S2 q n.
Proof. intros q n (b & m & Hb & H1 & H2). exists b, m. rewrite Eab. auto. Qed.
(* a heap string: bytes kept, tail visible at the new state *)
Lemma b1_k_hstr : forall p s, sa_heap B (p_ly v) (p_S v) p (Z.of_nat (length s) + 1) -> sa_str rd0 p s -> sa_str rd' p s.
Proof.
intros p s Hh [[Hz Hn] Ht].
split; [split; [|exact Hn]|].
- intros i Hi. pose proof Hi as Hi'. rewrite length_app in Hi'. cbn [length] in Hi'.
  rewrite (b1_k_heap p _ Hh) by lia. exact (Hz i Hi).
- intros x Hx. destruct Hh as (b & m & Hb & H1 & H2).
  pose proof (req_size_pos m) as Hr. destruct (Z_le_gt_dec 0 m) as [Hm|Hm]; [|lia]. specialize (Hr Hm).
  apply (AR_block_word_vis SEGS B (p_ly v) S2 (p_W v) mem' md' b m (p + Z.of_nat (length s)) x HAR');
    [rewrite Eab; exact Hb | lia | lia].
Qed.
Lemma b1_k_lit : forall a s, sa_lit SEGS B rd0 a s -> sa_lit SEGS B rd' a s.
Proof.
intros a s (Ha & ((Hz & Hn) & _) & Hp & Hr & Hi). split; [exact Ha|]. split; [|exact (conj Hp (conj Hr Hi))].
split; [split; [|exact Hn] | exact (sa_tail_of_romtail SEGS _ _ _ Hr)].
intros i Hi'. pose proof Hi' as Hl. rewrite length_app in Hl. cbn [length] in Hl.
rewrite (b1_k_imgs a _ Hi) by lia. exact (Hz i Hi').
Qed.
Lemma b1_k_cat : sa_cat SEGS B rd0 catA -> sa_cat SEGS B rd' catA.
Proof.
intros (Hp & Hi & Hrows). split; [exact Hp|]. split; [exact Hi|].
intros i Hn. destruct (Hrows i Hn) as (tp & Htp & Hl). exists tp. split; [|exact (b1_k_lit tp _ Hl)].
assert (Hn' : (Z.of_nat i < 11)) by (unfold pin_spec.CAT_N in Hn; lia).
rewrite (rdword_ext rd0 rd'); [exact Htp|]. intros k Hk. apply (b1_k_imgs catA _ Hi).
unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES. lia.
Qed.
Lemma b1_k_rod : arodata_okP SEGS RLO_A RHI_A B rd0 -> arodata_okP SEGS RLO_A RHI_A B rd'.
Proof.
intros H a Hro Ho He. rewrite (b1_k_img a (reac_segconf_parse.in_roP_img VRO a Hro) Ho He). exact (H a Hro Ho He).
Qed.

Lemma b1_keep_obj : pf_cx B v -> pf_obj B v (p_ly v) S2 rd'.
Proof.
intros HCX.
destruct HCX as (HPRE & HROD & _ & _ & _ & _ & _ & _ & (fe & HPF) & _ & _).
destruct HPF as (HRP & _).
destruct HRP as (C0 & C16 & RC & Hc & Ac & G1 & R1 & O1 & T0 & ST & LS & Ht & At & DJ & FR & SSP & CAT & LITS).
assert (Hc0 : 0 <= p_c v) by (destruct Ac; lia). assert (Ht0 : 0 <= p_t v) by (destruct At; lia).
split; [exact (b1_k_hstr _ _ Ht ST)|].
split; [exact (proj1 (reac_segconf_parse.sa_addr_of_heap B (p_ly v) S2 (p_W v) mem' md' _ _ HAR' (b1_heap2 _ _ Ht) Ht0 ltac:(lia)))|].
split; [exact (b1_heap2 _ _ Ht)|].
split; [exact (proj1 (reac_segconf_parse.sa_addr_of_heap B (p_ly v) S2 (p_W v) mem' md' _ _ HAR' (b1_heap2 _ _ Hc) Hc0
  ltac:(unfold seg_spec.SEG_C_SIZE; lia)))|].
split; [exact (b1_heap2 _ _ Hc)|].
split; [exact (b1_k_cat CAT)|].
split; [intros x Hx; exact (b1_k_lit _ _ (LITS x Hx))|].
split; [exact (b1_k_rod HROD)|].
exact (SSPX _ _ _ _ _ HAR').
Qed.

Lemma b1_keep_rconf : pf_cx B v -> sa_rconf rd' (p_c v) (p_rcs v).
Proof.
intros HCX.
destruct HCX as (_ & _ & _ & _ & _ & _ & _ & _ & (fe & HPF) & _ & _).
destruct HPF as (HRP & _).
destruct HRP as (C0 & C16 & RC & Hc & _).
destruct RC as (bs & Hb & Henc). exists bs. split; [|exact Henc].
pose proof Henc as Henc'. destruct Henc' as [Hl _].
intros i Hi. rewrite (b1_k_heap _ _ Hc) by (unfold seg_spec.SEG_C_SIZE in *; lia). exact (Hb i Hi).
Qed.

(* a range inside a side-stack frame of the entry state: its bytes, its shadow cells, its tail *)
Lemma b1_k_fframe : forall q n, sa_fframe (p_ly v) (p_S v) q n -> AR SEGS B (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) ->
  (forall x, q <= x < q + n -> rd' x = rd0 x) /\
  (forall x, q <= x < q + n -> rd' (shadow_of_addr SHADOW_OFF x) = rd0 (shadow_of_addr SHADOW_OFF x)) /\
  (forall e x, q <= e < q + n -> e < x < e - e mod 8 + 8 -> rd' x <> None).
Proof.
intros q n (cid & pos & Hin & Hc & H1 & H2) HAR.
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hin) as (H32 & _ & _ & _).
assert (Hin2 : In (cid, pos) (frames S2)) by exact (Hfr cid pos Hin).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR' Hin2) as (_ & _ & Hpres & _).
assert (H8 : fs_frame_bytes cid mod 64 = 0).
{ unfold fs_frame_bytes. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mul_comm. apply Z_mod_mult. }
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hin) as (Hf0 & Hfc & _).
assert (HF8 : frame_addr (p_ly v) cid pos mod 8 = 0).
{ apply Z.mod_divide in H32 as [qq Hq]; [|lia]. rewrite Hq. replace (qq * 32) with ((4 * qq) * 8) by lia. apply Z_mod_mult. }
pose proof (Z.div_mod (frame_addr (p_ly v) cid pos) 8 ltac:(lia)) as DF. rewrite HF8 in DF.
assert (Hfs8 : fs_frame_bytes cid mod 8 = 0).
{ apply Z.mod_divide in H8 as [qq Hq]; [|lia]. rewrite Hq. replace (qq * 64) with ((8 * qq) * 8) by lia. apply Z_mod_mult. }
pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)) as DS. rewrite Hfs8 in DS.
split; [|split].
- intros x Hx. apply (proj2 (proj2 K) cid pos x Hin). left. unfold in_zr, frame_rng. cbn [fst snd]. lia.
- intros x Hx. apply (proj2 (proj2 K) cid pos _ Hin). right. unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd].
  pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx. lia.
- intros e x He Hx HN.
  assert (Hx2 : frame_addr (p_ly v) cid pos <= x < frame_addr (p_ly v) cid pos + fs_frame_bytes cid).
  { pose proof (Z.div_mod e 8 ltac:(lia)) as De. pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as Me. lia. }
  exact (aview_some_of_apresent SEGS _ _ x (proj1 (Hpres x Hx2)) HN).
Qed.

Lemma b1_keep_lab : pf_cx B v -> pf_lab B v (p_ly v) S2 rd'.
Proof.
intros HCX.
destruct HCX as (HPRE & _ & _ & _ & _ & _ & _ & _ & (fe & HPF) & _ & _).
pose proof HPRE as (HAR & _).
destruct HPF as (_ & HLs & HLm).
unfold pf_lab. destruct (p_lab v) as [l|] eqn:El.
- destruct HLs as (Hlp & [[Hz Hn] Ht]).
  destruct HLm as (Hlen & Hloc & Haddr & _).
  pose proof Haddr as (Ha0 & Ha1 & Ha2 & Ha3 & Ha4).
  destruct Hloc as [Hh | [Hf | (Himg & Hpn & Hpt)]].
  + split; [split; [exact Hlp | exact (b1_k_hstr _ _ Hh (conj (conj Hz Hn) Ht))]|].
    split; [left; exact (b1_heap2 _ _ Hh)|].
    exact (proj1 (reac_segconf_parse.sa_addr_of_heap B (p_ly v) S2 (p_W v) mem' md' _ _ HAR' (b1_heap2 _ _ Hh) Ha0 ltac:(lia))).
  + destruct (b1_k_fframe _ _ Hf HAR) as (KB & KS & KT).
    split.
    { split; [exact Hlp|]. split; [split; [|exact Hn]|].
      - intros i Hi. pose proof Hi as Hi'. rewrite length_app in Hi'. cbn [length] in Hi'.
        rewrite KB by lia. exact (Hz i Hi).
      - intros x Hx. exact (KT (p_lp v + Z.of_nat (length l)) x ltac:(lia) Hx). }
    split.
    { right; left. destruct Hf as (cid & pos & Hin & Hc & H1 & H2). exists cid, pos. split; [exact (Hfr cid pos Hin)|]. auto. }
    split; [exact Ha0|]. split; [exact Ha1|]. split; [exact Ha2|].
    split.
    { intros x Hx. destruct (Ha3 x Hx) as (sv & Hs & Hok). exists sv. split; [|exact Hok]. rewrite KS by exact Hx. exact Hs. }
    intros Hn0. destruct Hf as (cid & pos & Hin & Hc & H1 & H2).
    exact (shadow_hull_vis_of_frame SEGS B LAWS (p_ly v) S2 (p_W v) mem' md' cid pos _ _ HAR' (Hfr cid pos Hin) H1 H2 Hn0).
  + split.
    { split; [exact Hlp|]. split; [split; [|exact Hn]|].
      - intros i Hi. pose proof Hi as Hi'. rewrite length_app in Hi'. cbn [length] in Hi'.
        rewrite (b1_k_imgs _ _ Himg) by lia. exact (Hz i Hi).
      - exact (Hpt _ _ _ _ _ HAR'). }
    split; [right; right; exact Himg|].
    exact (Hpn _ _ _ _ _ HAR').
- split; [exact HLs | exact I].
Qed.
End k.
End d.
