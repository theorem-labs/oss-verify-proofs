(* libreac/fuzz_boxreg: the bridge from a Theorem Labs lane's shared snprintf contract to boxreg's call-level contract.
   box_asnprintf_of_shared: sh_asnprintf_realizes segs B (pf_family (fun p => p = Ps)) (2 * ESTACK) gc gv img_lo img_hi
   cr pc -> asnprintf_realizes segs B pc (lib/A/Rt/SnprintfDef.v), image-generic (any segs, any B with AR_laws), and its
   instance for fuzz_boxreg.asan, box_asnprintf_of_shared_img (box_segs, the printf core's constants box_snp_cr, the
   canary cells BOX_SNP_GC -> BOX_SNP_GV, the writable globals BOX_GLOBALS_LO .. BOX_GLOBALS_TOP). The B build's twin is
   lib/B/Rt/SnprintfBridgeB.v. Rule 24: no function is proved here; the snprintf call stays the shared statement's
   hypothesis.
   The shared statement is a Theorem Labs lane's text verbatim: lib/A/Rt/FMsnprintfShared.v, FMsnprintfPf.v, FMupoison.v and
   FMsnprintfSx.v are a working branch 4de9999bfe7's proofs/omx-clap-core/fuzz_manifest/lib/A/<same>.v
   (img_lo img_hi, dest_off_globals, frm0_entry, the slot bound sp + 8 |xs| <= 2 ^ 47, the FP-existential post with its
   Sem.reg_get register clause) with module paths changed only (diff:
   a Theorem Labs lane's boxpa/fmshared-diff.txt).
   How boxreg's premises give the shared ones (T = s, xs = [], ws = a3 .. a7, w = sn_len (n - 1) s, 1 <= w <= n):
   - the format family: fmt "%s" = [37; 115] (ASN_FMT without its NUL), pf_parse [37; 115] = Some [Ps], args [APtr s],
     pf_text [Ps] [APtr s] = Some s, pf_prec_pos trivial; pf_arg_asan's |s| + 8 < 2 ^ 31 is boxreg's premise; a3 = x;
     str_end x s is asn_word_end x |s| (same text);
   - every destination premise is over the written part w <= n, so boxreg's full-n premises give the disjointness from
     the window and from the format / string; dest_ok, amem_range, range_addressable and shadow_hull_vis of (d, w) come
     from AR's block and shadow laws (al_blocks, al_shadow) for the heap block (p, m) (req_size m = m as 1 <= n <= m);
     0 < d and d + w <= 2 ^ 63 from the block law (4096 <= p, p + m <= alloc_ceiling).  Since a Theorem Labs lane's destination
     slack (00daeaf3796, relocated with FMsnprintfShared.v at 3e35620c52e) the shared contract asks amem_range d
     (w + 8), not amem_range d w: the block law's in_app and p + m <= alloc_ceiling give it by the same bound, since
     alloc_ceiling + 8 <= kHighMemEnd (snp_dest_facts);
   - the stack slot list xs = []: its zero-length range at sp is apart from (d, w) because the destination is outside
     the window, and the slot bound sp + 8 |[]| <= 2 ^ 47 is a Theorem Labs lane's va_slots_below_47_nil (FMsnprintfSx.v) from
     ecall_pre (sp <= ly_stk_hi ly <= kHighMemEnd = 2 ^ 47);
   - the image objects (the constants cr and the canary cells gc, gv) lie in the image's segments, which lie in
     ly_img ly (ALedger al_img); the window lies in the stack extent, which layout_ok's lo_disj keeps apart from ly_img;
     a heap block's bytes are outside ly_img (al_client_img); so each image object is apart from (sp - K, K) and (d, w);
   - dest_off_globals, zdisjoint (d, w) (img_lo, img_hi - img_lo): snp_dest_zd_img, through a Theorem Labs lane's
     dest_off_globals_of_ablocks (FMsnprintfSx.v) when the block lies at or above IMG_TOP, and directly when it lies
     wholly below IMG_LO (AR_client_img_law + the segments' tiling, snp_img_range);
   - frm0_entry, rounding mode 0 at entry: boxreg's contract takes the same proposition as its premise just before SRr
     (SnprintfDef.v), so it is handed through unchanged;
   - the post: both are FP-existential with the same clause, Sem.reg_get on the f registers (boxreg's SnprintfDef.v
     copies a Theorem Labs lane's verbatim); sn_bytes (n - 1) s is asn_out n s and sn_len (n - 1) s is |asn_out n s|
     (asn_out_sn_bytes: same text), so the shared post is boxreg's post.
   Side conditions, each a premise of box_asnprintf_of_shared (named):
   - snp_cr_rom segs cr (state-free, image): every range of cr is nonempty, inside [0, 2 ^ 63], and every byte of it is
     in a read-only segment; for fuzz_boxreg.asan proved by computation (box_snp_cr_rom);
   - snp_cr_not_owned B cr and snp_cr_not_errno B cr (state-free, the asyms instance's): no byte of cr is an owned static
     or an errno byte, so asn_rom_kept reads it as the image byte (consts_view). They stay premises over B here because
     boxreg's asyms instance (TfibB: lib/A/AD2l.v over the generated lib/A/AF0m.v) is not on this branch; for the
     generated Tfib_owned_static / TFIB_ERRNO they are checked by computation in a scratch build (reported with this
     file);
   - snp_img_word segs gc, snp_img_word segs gv (state-free, image): the two canary words are image bytes (seg_rom
     defined) below 2 ^ 63; proved by computation for this image (box_snp_img_gc / _gv; the guard is in .bss, which
     the image's last segment holds as zeros);
   - snp_canary_ar segs B gc gv (quantified over AR states): rdword gc = Some gv and the guard word reads as some cval.
     snp_canary_ar_of derives it from snp_canary_got B gc gv (the GOT word is a const cell of B: In (z8 (ANum gc) gv)
     (as_const B ly), so AR's am_const fixes it; the generated Tfib_const_abs holds the row z8 (ANum 0x99b40) 0x5f3f50)
     and snp_img_word segs gv (an image byte reads as Some in every state: the world's H is off the segments, w_Hoff,
     and mbyte falls back to seg_rom). So box_asnprintf_of_shared_img takes snp_canary_got B as its premise.
   - snp_img_range segs img_lo img_hi (state-free, image): IMG_LO <= img_lo < img_hi <= IMG_TOP and the segments tile
     [IMG_LO, IMG_TOP); proved for this image at (BOX_GLOBALS_LO, BOX_GLOBALS_TOP) = (0x98000, IMG_TOP), its two writable
     PT_LOADs (box_snp_img_range, by box_img_cover_all's vm_compute of the segment bounds).
   AR_laws segs B is the walks' standing hypothesis (Hypothesis LAWS of every spec).
   The constants (GXA-FIT.md, a Theorem Labs lane's boxreg/GXA-FIT.md, section 1; addresses identical in A
   and B): printf_core's jump table 0x21f38 (56 x 4 bytes), its second table 0x22018 (8 x 4 bytes: the switch at
   printf_core + 1696 takes it only for an index <= 7, `li a1,7; bltu a1,a0`, lib/CJ/RL/G/ProgAt3.v:5791-5799), STATES
   0x22080 (464 bytes; STATES0 is its first 58), XDIGITS 0x22250 (16) and the prefix "-+   0X0x" 0x10b54 (9); all in the
   read-only first segment. The canary: the .got word 0x99b40 (file bytes 0x5f3f50) and __stack_chk_guard 0x5f3f50
   (.bss).
   Discharged per image in a scratch build (a Theorem Labs lane, 2026-10-29, files kept at
   a Theorem Labs lane's boxpa/bridge-side/SnprintfSideA.v, built in the scratch tree
   s1-scratch with the generated lib/A/AF0m.v and a scratch lib/A/AF0l.v, rc=0 log
   s1x-build-20261029T031130Z.log): box_cr_not_owned and
   box_cr_not_errno (one vm_compute / one lia over Tfib_owned_static and TFIB_ERRNO), box_canary_in_const (the row
   z8 (ANum 0x99b40) 0x5f3f50 of Tfib_const_abs), hence box_snp_side_of_syms : BoxregSyms B -> the three premises, and
   box_asnprintf_of_shared_syms : AR_laws + BoxregSyms + the shared contract -> asnprintf_realizes. They are not on
   this branch because lib/A/AF0m.v, lib/A/AF0l.v and lib/A/AD2l.v are not; when they land, the file above drops in.
   Rule-24 record (2026-10-29, index v5 built 01:50Z from main f4cc67298b, ossv/recipes 5121fb8693, ossv/candidates
   ee89628c99, release/pau-projects-recipes b6a0088adc): `proof-index snprintf` (247 lines,
   a Theorem Labs lane's boxpa/bridge-r24/pi-snprintf.txt): no bridge from a shared SRr / AR snprintf
   statement to a unit's call contract anywhere; the nearest are jsoncons's interceptor walks (CJI/IcptSnprintfZ.v
   snprintf_icpt_ok) and the printf cores, none of which states this implication. git grep of every name this file
   adds over origin/main, origin/ossv/recipes, origin/ossv/candidates and origin/release/pau-projects-recipes under
   proofs/: 0 hits (bridge-r24/grep-main.txt). The cold-branch search did not finish: (an internal command)
   over 10362 refs and a git grep of the 853 cold tips moved since the names were coined
   (2026-10-29 02:30Z) each hit their time limit with no hit printed, so "no cold reference" is unverified. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import FMsnprintfPf FMsnprintfShared FMsnprintfSx SnprintfDef.
From OSSVerify.libreac.fuzz_boxreg.images Require Asan.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxImg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* The bytes the shared post writes are the bytes boxreg's post names. *)
Lemma asn_out_sn_bytes : forall n s, asn_out n s = sn_bytes (n - 1) s /\ Z.of_nat (length (asn_out n s)) = sn_len (n - 1) s.
Proof. intros n s. split; reflexivity. Qed.
Lemma snp_sn_len_bounds : forall n s, 1 <= n -> 1 <= sn_len (n - 1) s <= n.
Proof. intros n s Hn. unfold sn_len, sn_bytes. rewrite length_app, length_firstn. cbn [length]. lia. Qed.
Lemma snp_zd_of_pts : forall a la b lb, 0 < la -> 0 < lb ->
(forall z, a <= z < a + la -> b <= z < b + lb -> False) -> zdisjoint (a, la) (b, lb).
Proof.
intros a la b lb Ha Hb H. unfold zdisjoint; cbn [fst snd].
destruct (Z_le_gt_dec (a + la) b) as [E|E]; [left; exact E|].
destruct (Z_le_gt_dec (b + lb) a) as [F|F]; [right; exact F|].
exfalso. apply (H (Z.max a b)); lia.
Qed.
Lemma snp_pairwise_last2 : forall (l : list (Z * Z)) x y, pairwise zdisjoint (l ++ [x; y]) -> zdisjoint x y.
Proof.
induction l as [|h t IH]; intros x y H.
- destruct H as [H _]. exact (Forall_inv H).
- destruct H as [_ H]. exact (IH x y H).
Qed.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.
(* ---- the side conditions ---- *)
(* The constants cr: nonempty ranges below 2 ^ 63, every byte in a read-only segment of the image. *)
Definition snp_cr_rom (cr : list (Z * Z)) : Prop :=
Forall (fun r => 0 < snd r /\ 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr /\ (forall a, Exists (in_zr a) cr -> in_rom segs a).
(* No byte of cr is an owned static of B. *)
Definition snp_cr_not_owned (cr : list (Z * Z)) : Prop :=
forall a, Exists (in_zr a) cr -> ~ Exists (in_zr a) (as_owned_static B).
(* No byte of cr is an errno byte of B. *)
Definition snp_cr_not_errno (cr : list (Z * Z)) : Prop :=
forall a, Exists (in_zr a) cr -> ~ (as_errno B <= a < as_errno B + 4).
(* An 8-byte word of the image (its bytes are segment bytes), below 2 ^ 63. *)
Definition snp_img_word (a : Z) : Prop :=
0 <= a /\ a + 8 <= 2 ^ 63 /\ (forall k, 0 <= k < 8 -> seg_rom segs (Z_to_bv 64 (a + k)) <> None).
(* In every AR state the canary's GOT word gc holds gv and the guard word at gv is readable. *)
Definition snp_canary_ar (gc gv : Z) : Prop :=
forall ly S (W : world segs) mem md, AR segs B ly S W mem md ->
rdword (aview segs (w_H W) mem) gc = Some gv /\ exists cval, rdword (aview segs (w_H W) mem) gv = Some cval.
(* The canary's GOT word is a const cell of B holding gv. *)
Definition snp_canary_got (gc gv : Z) : Prop := forall ly, In (z8 (ANum gc) gv) (as_const B ly).
(* The writable-globals range (img_lo, img_hi) the caller passes: a nonempty part of the image range, and the image's
   segments tile [IMG_LO, IMG_TOP) (state-free, image). *)
Definition snp_img_range (img_lo img_hi : Z) : Prop :=
IMG_LO <= img_lo < img_hi /\ img_hi <= IMG_TOP /\ (forall a, IMG_LO <= a < IMG_TOP -> in_img segs a).
(* ---- image objects, the window and the destination ---- *)
Lemma snp_in_img_ly : forall ly S md a, ALedger segs ly S md -> in_img segs a -> in_zr a (ly_img ly).
Proof.
intros ly S md a LG (sg & Hin & Hr). destruct (al_img _ _ _ _ LG sg Hin) as [H1 H2]. unfold in_zr. lia.
Qed.
Lemma snp_rom_img : forall a, in_rom segs a -> in_img segs a.
Proof. intros a (sg & Hin & _ & Hr). exists sg. split; [exact Hin | exact Hr]. Qed.
Lemma snp_img_word_img : forall a, snp_img_word a -> forall z, a <= z < a + 8 -> in_img segs z.
Proof.
intros a (H0 & H8 & Hr) z Hz. apply seg_rom_in_img; [lia|].
replace z with (a + (z - a)) by lia. apply Hr. lia.
Qed.
Lemma snp_img_word_of_b : forall a, 0 <= a -> a + 8 <= 2 ^ 63 ->
forallb (fun k => match seg_rom segs (Z_to_bv 64 (a + k)) with Some _ => true | None => false end)
  [0; 1; 2; 3; 4; 5; 6; 7] = true ->
snp_img_word a.
Proof.
intros a H0 H8 Hb. split; [exact H0|]. split; [exact H8|]. intros k Hk.
assert (Hin : In k [0; 1; 2; 3; 4; 5; 6; 7]) by (cbn; lia).
rewrite forallb_forall in Hb. specialize (Hb k Hin).
cbv beta in Hb. destruct (seg_rom segs (Z_to_bv 64 (a + k))); [discriminate | discriminate Hb].
Qed.
Lemma snp_img_apart : forall ly S W mem md K sp p m d w lo len,
AR_laws segs B -> AR segs B ly S W mem md ->
0 < K -> ly_stk_lo ly + K <= sp -> sp <= ly_stk_hi ly ->
In (p, m) (ablocks B ly S) -> p <= d -> d + w <= p + req_size m -> 0 < w -> 0 < len ->
(forall z, lo <= z < lo + len -> in_img segs z) ->
Forall (zdisjoint (lo, len)) (snp_out K sp d w).
Proof.
intros ly S W mem md K sp p m d w lo len LAWS HAR HK Hlo Hhi Hin Hpd Hdw Hw Hlen Himg.
pose proof HAR as (HM & LG & _).
pose proof (am_layout _ _ _ _ HM) as LO.
assert (HD : zdisjoint (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) (ly_img ly)).
{ apply (snp_pairwise_last2 (owned_extents ly)). exact (lo_disj _ LO). }
unfold zdisjoint in HD; cbn [fst snd] in HD.
unfold snp_out. constructor; [|constructor; [|constructor]].
- apply snp_zd_of_pts; [exact Hlen | exact HK |]. intros z Hz1 Hz2.
  pose proof (snp_in_img_ly ly S md z LG (Himg z Hz1)) as Hz. unfold in_zr in Hz. lia.
- apply snp_zd_of_pts; [exact Hlen | exact Hw |]. intros z Hz1 Hz2.
  assert (Hc : ~ in_img segs z).
  { refine (proj2 (al_client_img _ _ LAWS ly S W mem md z HAR _)). left. exists p, m. split; [exact Hin | lia]. }
  exact (Hc (Himg z Hz1)).
Qed.
Lemma snp_cr_apart : forall cr ly S W mem md K sp p m d w,
AR_laws segs B -> AR segs B ly S W mem md -> snp_cr_rom cr ->
0 < K -> ly_stk_lo ly + K <= sp -> sp <= ly_stk_hi ly ->
In (p, m) (ablocks B ly S) -> p <= d -> d + w <= p + req_size m -> 0 < w ->
Forall (fun r => Forall (zdisjoint r) (snp_out K sp d w)) cr.
Proof.
intros cr ly S W mem md K sp p m d w LAWS HAR [HF Hrom] HK Hlo Hhi Hin Hpd Hdw Hw.
apply Forall_forall. intros [lo len] Hr. pose proof (proj1 (Forall_forall _ _) HF _ Hr) as (Hlen & _ & _).
cbn [fst snd] in Hlen.
apply (snp_img_apart ly S W mem md K sp p m d w lo len LAWS HAR HK Hlo Hhi Hin Hpd Hdw Hw Hlen).
intros z Hz. apply snp_rom_img. apply Hrom. apply Exists_exists. exists (lo, len). split; [exact Hr | exact Hz].
Qed.
Lemma snp_dest_facts : forall ly S W regs mem md p m d w,
AR_laws segs B -> AR segs B ly S W mem md ->
In (p, m) (ablocks B ly S) -> p <= d -> d + w <= p + req_size m -> 0 < w ->
(forall a, d <= a < d + w -> ~ (spZ regs - ESTACK <= a < spZ regs)) ->
0 < d /\ d + w <= 2 ^ 63 /\ dest_ok segs B ly S W regs mem d w /\ amem_range d (w + 8) /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF d w /\ shadow_hull_vis (aview segs (w_H W) mem) d w.
Proof.
intros ly S W regs mem md p m d w LAWS HAR Hin Hpd Hdw Hw Hwin.
destruct (al_blocks _ _ LAWS ly S W mem md p m HAR Hin) as (_ & H4096 & Hceil & Happ & Hby & _ & _).
destruct (al_shadow _ _ LAWS ly S W mem md p m HAR Hin) as [Hbs Hhull].
pose proof ASAN_CEIL_range as [[C1 C2] _]. unfold ASAN_CEIL in C1, C2.
split; [lia|]. split; [lia|]. split.
{ intros a Ha. destruct (Hby a ltac:(lia)) as [Hp Hno]. split; [|split; [exact Hno | exact (Hwin a Ha)]].
  destruct Hp as [Hh [b Hb]]. unfold writable_at, wview, mrestrict. rewrite Hh, Hb. discriminate. }
split.
{ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia. }
split; [exact (block_shadow_range _ _ p (req_size m) d w Hbs Hpd Hdw)|].
unfold shadow_hull_vis in Hhull |- *. intros s Hs. apply Hhull.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8).
{ intros u v Huv. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia. }
pose proof (Z.div_le_mono p d 8 ltac:(lia) Hpd) as M1.
pose proof (Z.div_le_mono (d + w - 1) (p + req_size m - 1) 8 ltac:(lia) ltac:(lia)) as M2.
unfold shadow_addr in *.
pose proof (R8 (SHADOW_OFF + p / 8) (SHADOW_OFF + d / 8) ltac:(lia)).
pose proof (R8 (SHADOW_OFF + (d + w - 1) / 8) (SHADOW_OFF + (p + req_size m - 1) / 8) ltac:(lia)).
lia.
Qed.
(* ---- the canary ---- *)
Lemma snp_aview_rom : forall (W : world segs) mem a, seg_rom segs (Z_to_bv 64 a) <> None ->
aview segs (w_H W) mem a <> None.
Proof.
intros W mem a Hr. unfold aview, mbyte, mrestrict. cbv beta.
destruct (w_H W (Z_to_bv 64 a)) eqn:EH.
- exfalso. apply Hr. eapply seg_rom_hidden; [exact (w_Hoff W) | exact EH].
- destruct (mem (Z_to_bv 64 a)) as [b|]; [cbv beta iota delta [option_map]; discriminate|].
  destruct (seg_rom segs (Z_to_bv 64 a)) as [b|]; [cbv beta iota delta [option_map]; discriminate | exfalso; exact (Hr eq_refl)].
Qed.
Lemma snp_canary_ar_of : forall gc gv, snp_canary_got gc gv -> snp_img_word gv -> snp_canary_ar gc gv.
Proof.
intros gc gv Hg (Hv0 & Hv8 & Hvr) ly S W mem md HAR.
split.
- pose proof HAR as (HM & _). pose proof (am_const _ _ _ _ HM) as HC.
  eapply rdword_cell; [lia|]. exact (proj1 (Forall_forall _ _) HC _ (Hg ly)).
- assert (R : forall k, 0 <= k < 8 -> aview segs (w_H W) mem (gv + k) <> None).
  { intros k Hk. apply snp_aview_rom. exact (Hvr k Hk). }
  pose proof (R 0 ltac:(lia)) as R0. rewrite Z.add_0_r in R0.
  pose proof (R 1 ltac:(lia)) as R1. pose proof (R 2 ltac:(lia)) as R2. pose proof (R 3 ltac:(lia)) as R3.
  pose proof (R 4 ltac:(lia)) as R4. pose proof (R 5 ltac:(lia)) as R5. pose proof (R 6 ltac:(lia)) as R6.
  pose proof (R 7 ltac:(lia)) as R7.
  unfold rdword.
  destruct (aview segs (w_H W) mem gv); [|exfalso; exact (R0 eq_refl)].
  destruct (aview segs (w_H W) mem (gv + 1)); [|exfalso; exact (R1 eq_refl)].
  destruct (aview segs (w_H W) mem (gv + 2)); [|exfalso; exact (R2 eq_refl)].
  destruct (aview segs (w_H W) mem (gv + 3)); [|exfalso; exact (R3 eq_refl)].
  destruct (aview segs (w_H W) mem (gv + 4)); [|exfalso; exact (R4 eq_refl)].
  destruct (aview segs (w_H W) mem (gv + 5)); [|exfalso; exact (R5 eq_refl)].
  destruct (aview segs (w_H W) mem (gv + 6)); [|exfalso; exact (R6 eq_refl)].
  destruct (aview segs (w_H W) mem (gv + 7)); [|exfalso; exact (R7 eq_refl)].
  eexists. reflexivity.
Qed.
(* ---- the constants ---- *)
Lemma snp_consts_view : forall cr (W : world segs) mem,
snp_cr_rom cr -> snp_cr_not_owned cr -> snp_cr_not_errno cr -> asn_rom_kept segs B W mem -> consts_view segs W mem cr.
Proof.
intros cr W mem [_ Hrom] Hno Hne Hk a Ha. apply Hk; [exact (Hrom a Ha) | exact (Hno a Ha) | exact (Hne a Ha)].
Qed.
(* ---- the destination is off the image's writable globals ----
   a Theorem Labs lane's next shared statement adds a premise of GXA's form (lib/CJ/RL/GXA/G_vsnprintf.v:176:
   D + dn <= 65536 \/ GLOBALS_TOP <= D). boxreg's destination is a field of the malloc'd registry
   (fuzz_boxreg.c:193; In (r, REG_SIZE) (ablocks B ly S)), so the bridge proves it instead of carrying it: a heap
   block's bytes are no image byte (AR_client_img_law), and the image's segments tile [IMG_LO, IMG_TOP) with no hole,
   so a run of block bytes lies wholly below IMG_LO (GXA's 65536, the same numeral) or at or above IMG_TOP, which is
   where the image's writable globals end. *)
Lemma snp_dest_off_img : forall ly S W mem md b m d w,
AR_laws segs B -> AR segs B ly S W mem md -> In (b, m) (ablocks B ly S) ->
b <= d -> d + w <= b + m -> 0 < w ->
(forall a, IMG_LO <= a < IMG_TOP -> in_img segs a) ->
d + w <= IMG_LO \/ IMG_TOP <= d.
Proof.
intros ly S W mem md b m d w LAWS HAR Hin Hbd Hdw Hw Hcov.
assert (Hm : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
assert (Hno : forall a, d <= a < d + w -> ~ in_img segs a).
{ intros a Ha. refine (proj2 (al_client_img _ _ LAWS ly S W mem md a HAR _)).
  left. exists b, m. split; [exact Hin | lia]. }
destruct (Z_lt_le_dec d IMG_LO) as [Hl|Hl].
- left. destruct (Z_le_gt_dec (d + w) IMG_LO) as [Hle|Hgt]; [exact Hle|].
  exfalso. apply (Hno IMG_LO ltac:(lia)). apply Hcov. lia.
- right. destruct (Z_le_gt_dec IMG_TOP d) as [Hge|Hlt]; [exact Hge|].
  exfalso. apply (Hno d ltac:(lia)). apply Hcov. lia.
Qed.
(* The same fact in the form a Theorem Labs lane's bundled statement asks for (a working branch 401616133a7:
   sh_asnprintf_realizes gains img_lo img_hi after gc gv, with the premise
   zdisjoint (d, sn_len (n - 1) T) (img_lo, img_hi - img_lo)), through a Theorem Labs lane's helper dest_off_globals_of_ablocks
   (lib/A/Rt/FMsnprintfSx.v, ad235a56db0, relocated). That helper asks img_hi <= b of the block; AR does not give
   it for every block (a block may lie below IMG_LO: AR_blocks_law has only 4096 <= b), so snp_dest_off_img on the
   whole block splits: at or above IMG_TOP (>= img_hi) the helper applies; wholly below IMG_LO (<= img_lo) the
   destination ends before img_lo. *)
Lemma snp_dest_zd_img : forall ly S W mem md b m d w img_lo img_hi,
AR_laws segs B -> AR segs B ly S W mem md -> In (b, m) (ablocks B ly S) ->
b <= d -> d + w <= b + m -> 0 < w -> snp_img_range img_lo img_hi ->
zdisjoint (d, w) (img_lo, img_hi - img_lo).
Proof.
intros ly S W mem md b m d w img_lo img_hi LAWS HAR Hin Hbd Hdw Hw (Hlo & Hhi & Hcov).
destruct (snp_dest_off_img ly S W mem md b m b m LAWS HAR Hin ltac:(lia) ltac:(lia) ltac:(lia) Hcov) as [Hbelow|Habove].
- unfold zdisjoint. cbn [fst snd]. left. lia.
- exact (dest_off_globals_of_ablocks B ly S b m d w img_lo img_hi Hin ltac:(lia) Hbd).
Qed.
(* ---- the bridge ---- *)
Theorem box_asnprintf_of_shared : forall gc gv img_lo img_hi cr pc,
AR_laws segs B ->
snp_cr_rom cr -> snp_cr_not_owned cr -> snp_cr_not_errno cr ->
snp_img_word gc -> snp_img_word gv -> snp_canary_ar gc gv -> snp_img_range img_lo img_hi ->
sh_asnprintf_realizes segs B (pf_family (fun p => p = Ps)) (2 * ESTACK) gc gv img_lo img_hi cr pc ->
asnprintf_realizes segs B pc.
Proof.
intros gc gv img_lo img_hi cr pc LAWS Hcr Hno Hne Hgc Hgv Hcan Himg HSH.
intros ly S W regs mem md d n f x s p m HPRE HK Hwin Ha0 Ha1 Ha2 Ha3 Hn Hin Hpd Hdn Hdwin
  Hfb Hf0 Hfm _ _ Hfwin Hfd Hfra Hfsh Hsb Hsl Hx0 Hsx Htail Hxm8 Hxwin Hxd Hxra Hxsh Hrk Hfrm.
(* R2 (abd0df80365): the premises 0x10000 <= f and f + 3 <= 0x99b40 are not needed here; pf_arg_asan's
   amem_range x (|s| + 1) is the contract's amem_range x (|s| + 8) cut short *)
assert (Hxm : amem_range x (Z.of_nat (length s) + 1)) by (unfold amem_range in Hxm8 |- *; lia).
pose proof HPRE as (HAR & _ & _ & Hslo & Hshi & _).
assert (EK : 2 * ESTACK = 8192) by reflexivity.
assert (EE : ESTACK = 4096) by reflexivity.
pose proof (snp_sn_len_bounds n s ltac:(lia)) as Hw0.
set (w := sn_len (n - 1) s) in *.
assert (Hw : 1 <= w <= n) by lia.
assert (Hm : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
assert (Hdw : d + w <= p + req_size m) by lia.
assert (Hdwin1 : forall a, d <= a < d + w -> ~ (spZ regs - ESTACK <= a < spZ regs)).
{ intros a Ha Hc. apply (Hdwin a); lia. }
destruct (snp_dest_facts ly S W regs mem md p m d w LAWS HAR Hin Hpd Hdw ltac:(lia) Hdwin1)
  as (Hd0 & Hd63 & Hdok & Hdam8 & Hdra & Hdsh).
(* dest_off_globals (401616133a7): the written part is apart from the image's writable globals *)
assert (HZG : zdisjoint (d, w) (img_lo, img_hi - img_lo))
  by exact (snp_dest_zd_img ly S W mem md p m d w img_lo img_hi LAWS HAR Hin Hpd ltac:(lia) ltac:(lia) Himg).
destruct (Hcan ly S W mem md HAR) as [Hgcv [cval Hcval]].
pose proof Hgc as (Hgc0 & Hgc8 & _). pose proof Hgv as (Hgv0 & Hgv8 & _).
(* the constants *)
assert (HCV : consts_view segs W mem cr) by exact (snp_consts_view cr W mem Hcr Hno Hne Hrk).
assert (HCB : Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr).
{ eapply Forall_impl; [|exact (proj1 Hcr)]. intros r (_ & H1 & H2). split; assumption. }
assert (HCD : Forall (fun r => Forall (zdisjoint r) (snp_out (2 * ESTACK) (spZ regs) d w)) cr)
  by exact (snp_cr_apart cr ly S W mem md (2 * ESTACK) (spZ regs) p m d w LAWS HAR Hcr ltac:(lia) HK Hshi Hin Hpd Hdw ltac:(lia)).
(* the canary cells *)
assert (HGC : Forall (zdisjoint (gc, 8)) (snp_out (2 * ESTACK) (spZ regs) d w)).
{ apply (snp_img_apart ly S W mem md (2 * ESTACK) (spZ regs) p m d w gc 8 LAWS HAR ltac:(lia) HK Hshi Hin Hpd Hdw
    ltac:(lia) ltac:(lia)).
  exact (snp_img_word_img gc Hgc). }
assert (HGV : Forall (zdisjoint (gv, 8)) (snp_out (2 * ESTACK) (spZ regs) d w)).
{ apply (snp_img_apart ly S W mem md (2 * ESTACK) (spZ regs) p m d w gv 8 LAWS HAR ltac:(lia) HK Hshi Hin Hpd Hdw
    ltac:(lia) ltac:(lia)).
  exact (snp_img_word_img gv Hgv). }
(* the arguments: a3 .. a7, no stack slot *)
assert (Ha3' : argZ regs 3 = x).
{ unfold argZ. assert (E : getr regs (Z_to_bv 5 (10 + 3)) = getr regs 13) by (f_equal; apply bv_eq; reflexivity).
  rewrite E, Ha3. unfold w64. rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|].
  change (bv_modulus 64) with (2 ^ 64). unfold amem_range, kHighMemEnd, kLowMemEnd, kHighMemBeg in Hxm. lia. }
assert (Hva : va_words regs (aview segs (w_H W) mem) (spZ regs) [] (map (argZ regs) [3; 4; 5; 6; 7] ++ [])).
{ split; [reflexivity|]. intros i Hi. cbn [length] in Hi. lia. }
assert (Hsp8 : spZ regs + 8 * Z.of_nat (length ([] : list Z)) <= 2 ^ 47).
{ apply (va_slots_below_47_nil segs B ly S [] W regs mem md). apply FMupoison.ecall_preU_nil. exact HPRE. }
assert (Hspd : Forall (zdisjoint (spZ regs, 8 * Z.of_nat (length ([] : list Z)))) (snp_out (2 * ESTACK) (spZ regs) d w)).
{ cbn [length Z.of_nat]. unfold snp_out. constructor; [|constructor; [|constructor]].
  - unfold zdisjoint; cbn [fst snd]. lia.
  - unfold zdisjoint; cbn [fst snd].
    destruct (Z_le_gt_dec (spZ regs) d) as [E1|E1]; [left; lia|]. right.
    destruct (Z_le_gt_dec (d + w) (spZ regs)) as [E2|E2]; [exact E2|].
    exfalso. apply (Hdwin (spZ regs - 1)); lia. }
(* the format family *)
assert (HFF : pf_family (fun p => p = Ps) (aview segs (w_H W) mem) (snp_out (2 * ESTACK) (spZ regs) d w) f
  (map (argZ regs) [3; 4; 5; 6; 7] ++ []) s).
{ exists [37; 115], [Ps], [APtr s].
  split; [|split; [reflexivity|split; [constructor; [reflexivity | constructor]|split; [|split]]]].
  - unfold fmt_at. change (Z.of_nat (length [37; 115]) + 1) with 3.
    split; [exact Hf0|]. split.
    { intros i Hi. change (Z.of_nat (length [37; 115])) with 2 in Hi. exact (Hfb i ltac:(lia)). }
    split.
    { unfold snp_out. constructor; [|constructor; [|constructor]].
      - apply snp_zd_of_pts; [lia | lia |]. intros z Hz1 Hz2. apply (Hfwin z Hz1). lia.
      - unfold zdisjoint; cbn [fst snd]. lia. }
    split; [exact Hfm|]. split; [exact Hfra | exact Hfsh].
  - cbn [map app pf_args_asan]. split; [|exact I]. rewrite Ha3'. cbn [pf_arg_asan].
    assert (HE : str_end x s = asn_word_end x (Z.of_nat (length s))) by reflexivity.
    pose proof (Z.mod_pos_bound (x + Z.of_nat (length s)) 8 ltac:(lia)) as Hmod.
    split; [exact Hsb|]. split; [exact Hx0|]. split; [exact Hsl|]. split; [exact Hsx|].
    split; [rewrite HE; exact Htail|].
    split.
    { rewrite HE. unfold snp_out. constructor; [|constructor; [|constructor]].
      - apply snp_zd_of_pts; [unfold asn_word_end; lia | lia |]. intros z Hz1 Hz2.
        apply (Hxwin z); lia.
      - unfold zdisjoint; cbn [fst snd]. lia. }
    split; [exact Hxm|]. split; [exact Hxra | exact Hxsh].
  - cbn [pf_text option_map]. rewrite app_nil_r. reflexivity.
  - cbn [pf_prec_pos]. exact I. }
(* the destination's pairwise disjointness *)
assert (HPW : pairwise zdisjoint (snp_out (2 * ESTACK) (spZ regs) d w)).
{ unfold snp_out. cbn [pairwise]. split; [|split; [constructor | exact I]]. constructor; [|constructor].
  apply snp_zd_of_pts; [lia | lia |]. intros z Hz1 Hz2. apply (Hdwin z); lia. }
assert (HTl : Z.of_nat (length s) < 2 ^ 31 - 1) by lia.
eapply SRr_mono.
{ exact (HSH ly S W regs mem md d n f [] (map (argZ regs) [3; 4; 5; 6; 7] ++ []) s cval
    HPRE HK Hwin Ha0 Ha1 Ha2 HCV HCB HCD Hgcv Hcval Hgc0 Hgc8 Hgv0 Hgv8 HGC HGV Hva Hsp8 Hspd HFF Hn HTl Hd0 Hd63 HPW
    Hdok Hdam8 Hdra Hdsh HZG Hfrm). }
intros W' c' _ HQ. exact HQ.
Qed.
End c.
End b.
(* ---- fuzz_boxreg.asan's instance ---- *)
(* The constants printf_core reads (GXA-FIT.md; header). *)
Definition box_snp_cr : list (Z * Z) := [(0x21f38, 224); (0x22018, 32); (0x22080, 464); (0x22250, 16); (0x10b54, 9)].
(* The canary: the .got word holding &__stack_chk_guard, and __stack_chk_guard. *)
Definition BOX_SNP_GC : Z := 0x99b40.
Definition BOX_SNP_GV : Z := 0x5f3f50.
Lemma box_snp_cr_rom : snp_cr_rom box_segs box_snp_cr.
Proof.
split.
- unfold box_snp_cr. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
- intros a Ha. exists Asan.Asan_segment_000. split; [left; reflexivity|]. split; [vm_compute; reflexivity|].
  match goal with |- Z.le ?lo a /\ Z.lt a (?lo' + ?sz) =>
    let l := eval vm_compute in lo in let h := eval vm_compute in sz in change lo with l; change sz with h end.
  apply Exists_exists in Ha as (r & Hr & Hz). unfold box_snp_cr in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; unfold in_zr in Hz; cbn [fst snd] in Hz; lia.
Qed.
Lemma box_snp_img_gc : snp_img_word box_segs BOX_SNP_GC.
Proof. apply snp_img_word_of_b; [unfold BOX_SNP_GC; lia | unfold BOX_SNP_GC; lia | vm_compute; reflexivity]. Qed.
Lemma box_snp_img_gv : snp_img_word box_segs BOX_SNP_GV.
Proof. apply snp_img_word_of_b; [unfold BOX_SNP_GV; lia | unfold BOX_SNP_GV; lia | vm_compute; reflexivity]. Qed.
(* fuzz_boxreg.asan's four loaded segments tile [IMG_LO, IMG_TOP) with no hole (bases and sizes read from
   images.Asan by vm_compute, so a change of the image breaks this proof, not a statement). *)
Lemma box_img_cover_all : forall a, IMG_LO <= a < IMG_TOP -> in_img box_segs a.
Proof.
intros a Ha. unfold in_img, box_segs, Asan.M.loaded_segments.
assert (E0 : Z.of_N (seg_base Asan.Asan_segment_000) = IMG_LO) by (vm_compute; reflexivity).
assert (S0 : Z.of_N (seg_base Asan.Asan_segment_000) + Z.of_N (seg_size Asan.Asan_segment_000) = 0x2f000)
  by (vm_compute; reflexivity).
assert (E1 : Z.of_N (seg_base Asan.Asan_segment_001) = 0x2f000) by (vm_compute; reflexivity).
assert (S1 : Z.of_N (seg_base Asan.Asan_segment_001) + Z.of_N (seg_size Asan.Asan_segment_001) = 0x98000)
  by (vm_compute; reflexivity).
assert (E2 : Z.of_N (seg_base Asan.Asan_segment_002) = 0x98000) by (vm_compute; reflexivity).
assert (S2 : Z.of_N (seg_base Asan.Asan_segment_002) + Z.of_N (seg_size Asan.Asan_segment_002) = 0x9a000)
  by (vm_compute; reflexivity).
assert (E3 : Z.of_N (seg_base Asan.Asan_segment_003) = 0x9a000) by (vm_compute; reflexivity).
assert (S3 : Z.of_N (seg_base Asan.Asan_segment_003) + Z.of_N (seg_size Asan.Asan_segment_003) = IMG_TOP)
  by (vm_compute; reflexivity).
destruct (Z_lt_le_dec a 0x2f000) as [H|H]; [exists Asan.Asan_segment_000; split; [left; reflexivity | lia]|].
destruct (Z_lt_le_dec a 0x98000) as [H'|H']; [exists Asan.Asan_segment_001; split; [right; left; reflexivity | lia]|].
destruct (Z_lt_le_dec a 0x9a000) as [H''|H'']; [exists Asan.Asan_segment_002; split; [right; right; left; reflexivity | lia]|].
exists Asan.Asan_segment_003. split; [do 3 right; left; reflexivity | lia].
Qed.
(* The end of this image's writable globals: its two writable PT_LOADs are [0x98000, 0x9a000) (.data.rel.ro, .got)
   and [0x9a000, IMG_TOP) (.data, asan_globals, .bss; last loaded byte 0x5f57f0, page-rounded by the loader), i.e.
   images.Asan's segments 002 and 003, the last of the image. So nothing writable of the image lies at or above
   IMG_TOP, and GLOBALS_TOP is IMG_TOP (lib/Reusable/YImgTop.v, the one place that names the image range). *)
Definition BOX_GLOBALS_TOP : Z := IMG_TOP.
(* Where they begin: images.Asan's segment 002, the first writable PT_LOAD. So the pair (img_lo, img_hi) that
   401616133a7's premise takes at this image is (BOX_GLOBALS_LO, BOX_GLOBALS_TOP). *)
Definition BOX_GLOBALS_LO : Z := 0x98000.
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* GXA's dest_off_globals for a destination inside a heap block: GXA writes the left disjunct as D + dn <= 65536,
   which is this IMG_LO. *)
Theorem box_dest_off_globals : forall B ly S W mem md b m d w,
AR_laws box_segs B -> AR box_segs B ly S W mem md -> In (b, m) (ablocks B ly S) ->
b <= d -> d + w <= b + m -> 0 < w ->
d + w <= IMG_LO \/ BOX_GLOBALS_TOP <= d.
Proof.
intros B ly S W mem md b m d w LAWS HAR Hin Hbd Hdw Hw.
exact (snp_dest_off_img box_segs B ly S W mem md b m d w LAWS HAR Hin Hbd Hdw Hw box_img_cover_all).
Qed.
End g.
(* The writable-globals range is a nonempty part of the image range, which the segments tile. *)
Lemma box_snp_img_range : snp_img_range box_segs BOX_GLOBALS_LO BOX_GLOBALS_TOP.
Proof.
split; [unfold BOX_GLOBALS_LO, BOX_GLOBALS_TOP; lia|]. split; [unfold BOX_GLOBALS_TOP; lia|]. exact box_img_cover_all.
Qed.
Section gz. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* 401616133a7's form of the same premise, at this image's writable-globals range. *)
Theorem box_dest_zd_globals : forall B ly S W mem md b m d w,
AR_laws box_segs B -> AR box_segs B ly S W mem md -> In (b, m) (ablocks B ly S) ->
b <= d -> d + w <= b + m -> 0 < w ->
zdisjoint (d, w) (BOX_GLOBALS_LO, BOX_GLOBALS_TOP - BOX_GLOBALS_LO).
Proof.
intros B ly S W mem md b m d w LAWS HAR Hin Hbd Hdw Hw.
exact (snp_dest_zd_img box_segs B ly S W mem md b m d w BOX_GLOBALS_LO BOX_GLOBALS_TOP LAWS HAR Hin Hbd Hdw Hw
  box_snp_img_range).
Qed.
(* The new premise exactly as 401616133a7 writes it at a call (T = s, w = sn_len (n - 1) T), from the call-site facts
   boxreg's asnprintf_realizes already gives: the destination is n bytes of the heap block (p, m). So the premise half
   of the bundled statement needs nothing new from the caller. *)
Theorem box_dest_zd_globals_call : forall B ly S W mem md p m d n (s : list Z),
AR_laws box_segs B -> AR box_segs B ly S W mem md -> In (p, m) (ablocks B ly S) ->
p <= d -> d + n <= p + m -> 1 <= n ->
zdisjoint (d, sn_len (n - 1) s) (BOX_GLOBALS_LO, BOX_GLOBALS_TOP - BOX_GLOBALS_LO).
Proof.
intros B ly S W mem md p m d n s LAWS HAR Hin Hpd Hdn Hn.
pose proof (snp_sn_len_bounds n s Hn) as Hw.
exact (box_dest_zd_globals B ly S W mem md p m d (sn_len (n - 1) s) LAWS HAR Hin Hpd ltac:(lia) ltac:(lia)).
Qed.
End gz.
Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The bridge on fuzz_boxreg.asan: what is left is the asyms instance's (cr no owned static, no errno byte; the GOT
   word a const cell). *)
Theorem box_asnprintf_of_shared_img : forall B pc,
AR_laws box_segs B ->
snp_cr_not_owned B box_snp_cr -> snp_cr_not_errno B box_snp_cr -> snp_canary_got B BOX_SNP_GC BOX_SNP_GV ->
sh_asnprintf_realizes box_segs B (pf_family (fun p => p = Ps)) (2 * ESTACK) BOX_SNP_GC BOX_SNP_GV
  BOX_GLOBALS_LO BOX_GLOBALS_TOP box_snp_cr pc ->
asnprintf_realizes box_segs B pc.
Proof.
intros B pc LAWS Hno Hne Hgot HSH.
apply (box_asnprintf_of_shared box_segs B BOX_SNP_GC BOX_SNP_GV BOX_GLOBALS_LO BOX_GLOBALS_TOP box_snp_cr pc LAWS
  box_snp_cr_rom Hno Hne box_snp_img_gc box_snp_img_gv
  (snp_canary_ar_of box_segs B BOX_SNP_GC BOX_SNP_GV Hgot box_snp_img_gv) box_snp_img_range HSH).
Qed.
End i.
