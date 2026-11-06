(* crtA_w_mid: the convert-loop piece of the cgif-form walk of check_round_trip (image A of libreac/fuzz_decode).
   crtA_mid_piece : crtA_at_loopout B MT RO_RD -> crtA_at_calloc B MT RO_RD (lib/A/Prog/crtA_cuts.v).
   From the state at CRT_RET_CALLOC it runs the three NULL tests and `blez nch` together with the one float
   instruction fmv.w.x (crt_seg4_F, lib/A/Prog/crtA_segs.v) and then the convert loop (the Section hypothesis LOOP,
   the statement crt_loop_stmt_F of lib/A/Prog/crtA_loop_stmt.v), lands at CRT_LOOP_OUT, re-establishes the inner
   journal across the loop's writes to the P and Q blocks (lib/Reusable/YCbq.v:636 ajournal_exec: the written bytes
   are blocks the call added, the in_tmp_block case of awr_byte), turns the loop's crt_inv into crtA_conv, and
   closes with crtA_at_loopout.

   The loop is a Section hypothesis so that this piece depends on no particular proof of crt_loop_stmt_F; the
   close passes one (lib/A/Prog/crtA_loop.v crt_loop_holds_F, or another).  After the Section closes the theorem
   reads @crtA_mid_piece fx rc B MT RO_RD LAWS LOOP.

   This file does NO float `step` itself: it only composes crt_seg4_F and the loop statement, so the global Ltac
   overrides of lib/Prog/RcBraidLib.v do not affect it, and lib/Lib/CrtEnc.v is never Required here.  LeafCgKit is
   Required, not Imported, because its in_img / apresent / cfg_at / w64 would shadow the allocator model's
   (YG0d / YG0n) names the journal is stated with. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n YK1b.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YG0v YCbq YC5d YGCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YImgTop YP09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Frame Cells Step ExecF Regs6ss FP.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import Img0 AsanCells DecodeTFIB DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import DecodeSyms DecodeAddr DecodeList.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import ReacDecodeLib crtA_iface crtA_segs crtA_conv
  crtA_loop_stmt crtA_cuts crtA_walk check_round_trip_cg.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require LeafCgKit.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import FloatExact.
Import ListNotations.
Open Scope Z_scope.
(* lib/Reusable/YM03.v (pulled in through crtA_iface) overrides lia and nia globally with slower tactics; restore,
   for this file only, the tactics lib/A/Prog/crtA_conv.v restores: lia as lib/Lib/LiaTwx2.v defines it (loaded
   through PropExec), falling back to Stdlib's, and nia as Stdlib defines it. *)
Local Ltac Lia.lia ::=
  first [ LiaTwx2.zify_prune; LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTwx2.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
Local Ltac Lia.nia ::= Zify.zify; xnia zchecker.
Module YKK := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YK11.
Module LCK := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.LeafCgKit.
Module AC := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.AsanCells.
Module AImg := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Img0.
Module GD := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YG0d.

(* ======================================================================== *)
(* Helpers that need no float state                                          *)
(* ======================================================================== *)

(* decodesegs0 (the world's segment list) and rsegs (mrd's / bytes_at's) are the same list. *)
Lemma segs_rsegs : decodesegs0 = AImg.rsegs.
Proof. reflexivity. Qed.

(* Every loaded byte of image A lies below the ASan low-shadow base. *)
Lemma crt_segs_low : forall a, GD.in_img decodesegs0 a -> 0 <= a < kLowMemEnd.
Proof.
  intros a (sg & Hin & Hr). unfold decodesegs0 in Hin.
  pose proof segs_in_asan as Hall. unfold segs_in in Hall.
  rewrite forallb_forall in Hall. specialize (Hall sg Hin).
  apply andb_prop in Hall as [H1 H2]. unfold seg_lo, seg_hi in *.
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof IMG_LO_val as E1. pose proof IMG_TOP_val as E2.
  pose proof (N2Z.is_nonneg (seg_base sg)). unfold kLowMemEnd. lia.
Qed.

Lemma dec_seg_rom_none : forall a, 0 <= a < 2 ^ 64 -> ~ GD.in_img decodesegs0 a ->
  YKK.seg_rom decodesegs0 (Z_to_bv 64 a) = None.
Proof.
  intros a Ha Hni. unfold YKK.seg_rom, memory_read.
  rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). cbn [Z.of_N].
  destruct (find_segment decodesegs0 a 1) as [sg|] eqn:E; [exfalso | reflexivity].
  apply find_segment_some_spec in E as (Hin & H1 & H2). apply Hni. exists sg. split; [exact Hin | lia].
Qed.

(* mrd reads the overlay at an address off the image. *)
Lemma dec_mrd_off : forall mem a, 0 <= a < 2 ^ 64 -> ~ GD.in_img decodesegs0 a ->
  mrd AImg.rsegs mem (wa a) = mem (Z_to_bv 64 a).
Proof.
  intros mem a Ha Hni. unfold mrd, wa.
  destruct (mem (Z_to_bv 64 a)) as [b|] eqn:Em; [reflexivity|].
  exact (dec_seg_rom_none a Ha Hni).
Qed.

(* A byte that bytes_at reads off the image is present in the overlay. *)
Lemma bytes_at_present : forall (m : word -> option byte) A (bs : list byte) i,
  bytes_at AImg.rsegs m A bs -> 0 <= i < Z.of_nat (length bs) ->
  ~ GD.in_img decodesegs0 (A + i) -> m (Z_to_bv 64 (A + i)) <> None.
Proof.
  intros m A bs i (HA & Hl & Hb) Hi Hni.
  specialize (Hb (Z.to_nat i) ltac:(lia)).
  rewrite Z2Nat.id in Hb by lia.
  rewrite (dec_mrd_off m (A + i) ltac:(lia) Hni) in Hb.
  rewrite Hb. intros Hn. apply nth_error_None in Hn. lia.
Qed.

Lemma byte_signed_small : forall b : byte, bv_unsigned b < 128 -> bv_signed b = bv_unsigned b.
Proof.
  intros b H. pose proof (bv_unsigned_in_range 8 b) as R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *.
  change (2 ^ Z.of_N 8) with 256 in *.
  Z.div_mod_to_equations. lia.
Qed.

Lemma pairwise_perm : forall {X} (R : X -> X -> Prop) (l l' : list X),
  (forall x y, R x y -> R y x) -> Permutation l l' -> pairwise R l -> pairwise R l'.
Proof.
  intros X R l l' Rsym HP. induction HP; intros HPW.
  - exact HPW.
  - destruct HPW as [HF HPW]. split.
    + rewrite Forall_forall in HF |- *. intros z Hz. apply HF.
      eapply Permutation_in; [apply Permutation_sym; exact HP | exact Hz].
    + apply IHHP. exact HPW.
  - destruct HPW as [HFy [HFx HPW]]. inversion HFy as [|u l0 Ryx HFy0]; subst.
    split; [| split].
    + constructor; [apply Rsym; exact Ryx | exact HFx].
    + exact HFy0.
    + exact HPW.
  - apply IHHP2, IHHP1, HPW.
Qed.

Lemma zdisjoint_sym : forall x y, zdisjoint x y -> zdisjoint y x.
Proof. intros x y H. unfold zdisjoint in *. lia. Qed.

Lemma bv_self : forall w : word, Z_to_bv 64 (bv_unsigned w) = w.
Proof.
  intros w. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  exact (bv_unsigned_in_range 64 w).
Qed.

Lemma uns_small : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a.
Proof.
  intros a Ha. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  change (bv_modulus 64) with (2 ^ 64). exact Ha.
Qed.

(* The frame the prologue writes is twelve words. *)
Lemma crt_fr_size : forall c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra,
  cells_size (crt_fr c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) = 96%nat.
Proof. reflexivity. Qed.

(* ======================================================================== *)
(* Helpers that mention the world's reader aview / the ASan ceiling           *)
(* ======================================================================== *)
Section ARhelpers.
Context {fx : YKK.FPState} {rc : YM05.RunCeil}.

(* A value aview reads off the image is the overlay byte, and that byte is not hidden. *)
Lemma aview_mrd_off : forall (Hd : word -> bool) mem a v,
  0 <= a < 2 ^ 64 -> ~ GD.in_img decodesegs0 a ->
  aview decodesegs0 Hd mem a = Some v ->
  Hd (Z_to_bv 64 a) = false /\ exists b, mem (Z_to_bv 64 a) = Some b /\ bv_unsigned b = v.
Proof.
  intros Hd mem a v Ha Hni Hav. unfold aview, mbyte, mrestrict in Hav.
  pose proof (dec_seg_rom_none a Ha Hni) as Hrom.
  destruct (Hd (Z_to_bv 64 a)) eqn:EH.
  - cbv beta iota in Hav. rewrite Hrom in Hav. cbn in Hav. discriminate.
  - destruct (mem (Z_to_bv 64 a)) as [b|] eqn:Em.
    + cbv beta iota in Hav. cbn in Hav. injection Hav as Hav.
      split; [reflexivity|]. exists b. split; [reflexivity | exact Hav].
    + cbv beta iota in Hav. rewrite Hrom in Hav. cbn in Hav. discriminate.
Qed.

(* The reverse: a present, unhidden byte is what aview reads. *)
Lemma aview_of_present : forall (Hd : word -> bool) mem a b,
  Hd (Z_to_bv 64 a) = false -> mem (Z_to_bv 64 a) = Some b ->
  aview decodesegs0 Hd mem a = Some (bv_unsigned b).
Proof.
  intros Hd mem a b EH Em. unfold aview, mbyte, mrestrict. rewrite EH, Em. reflexivity.
Qed.

Lemma in_app_app_mem : forall lo len a, in_app lo len -> lo <= a < lo + len -> AC.app_mem a.
Proof.
  intros lo len a Hia Ha. pose proof (@YG0f.ASAN_CEIL_range rc) as [CR _].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
  unfold AC.app_mem, AC.LOWMEM_END, AC.HIGHMEM_BEG, AC.APPMEM_END.
  destruct Hia as (H0 & [HL | [HH1 HH2]]); [left; lia | right; lia].
Qed.

Variable B : asyms.
Hypothesis LAWS : AR_laws decodesegs0 B.

(* The bytes of a live block are present and not hidden ... *)
Lemma ar_vis : forall ly S (W : world decodesegs0) mem md p n a,
  @AR rc decodesegs0 B ly S W mem md -> In (p, n) (ablocks B ly S) -> p <= a < p + req_size n ->
  w_H W (Z_to_bv 64 a) = false /\ exists b, mem (Z_to_bv 64 a) = Some b.
Proof.
  intros ly S W mem md p n a HAR Hin Ha.
  pose proof (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & Hpres & _).
  destruct (Hpres a Ha) as ([Hh Hb] & _). exact (conj Hh Hb).
Qed.

(* ... and lie off the image. *)
Lemma ar_off_img : forall ly S (W : world decodesegs0) mem md p n a,
  @AR rc decodesegs0 B ly S W mem md -> In (p, n) (ablocks B ly S) -> p <= a < p + req_size n ->
  ~ GD.in_img decodesegs0 a.
Proof.
  intros ly S W mem md p n a HAR Hin Ha.
  exact (proj2 (al_client_img _ _ LAWS ly S W mem md a HAR
                  (or_introl (ex_intro _ p (ex_intro _ n (conj Hin Ha)))))).
Qed.

(* A live block of the allocator invariant is ASan-addressable (its shadow is block_shadow, al_shadow). *)
Lemma ar_addressable : forall ly S (W : world decodesegs0) mem md p n,
  @AR rc decodesegs0 B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  AC.addressable mem p (req_size n).
Proof.
  intros ly S W mem md p n HAR Hin.
  pose proof (al_blocks _ _ LAWS ly S W mem md p n HAR Hin)
    as (Hmod & H4096 & Hceil & Happ & Hpres & _ & Hn).
  pose proof (al_shadow _ _ LAWS ly S W mem md p n HAR Hin) as (Hbs & _Hhull).
  pose proof (req_size_pos n ltac:(lia)) as (Hrs1 & Hrs2).
  pose proof (@YG0f.ASAN_CEIL_range rc) as [CR _]. unfold ASAN_CEIL in CR.
  split; [lia|]. split; [lia|]. split.
  { unfold AC.APPMEM_END. lia. }
  intros i Hi.
  assert (Happm : AC.app_mem (p + i)) by (apply (in_app_app_mem p (req_size n) (p + i) Happ); lia).
  split; [exact Happm|].
  pose proof (block_shadow_range (aview decodesegs0 (w_H W) mem) SHADOW_OFF p (req_size n) p (req_size n)
                Hbs ltac:(lia) ltac:(lia)) as RA.
  destruct (RA (p + i) ltac:(lia)) as (s & Hs & Hok).
  assert (Heqs : shadow_of_addr SHADOW_OFF (p + i) = AC.shadow_addr (p + i)).
  { unfold shadow_of_addr, AC.shadow_addr, SHADOW_OFF, AC.ASAN_K. lia. }
  rewrite Heqs in Hs.
  assert (Hsb : 0 <= AC.shadow_addr (p + i) < 2 ^ 64).
  { pose proof (shadow_range (p + i) Happm) as HR. unfold AC.shadow_addr. exact HR. }
  assert (Hni : ~ GD.in_img decodesegs0 (AC.shadow_addr (p + i))).
  { intros Him. pose proof (crt_segs_low _ Him) as HL.
    unfold AC.shadow_addr, AC.ASAN_K, kLowMemEnd in *. Z.div_mod_to_equations. lia. }
  pose proof (aview_mrd_off (w_H W) mem (AC.shadow_addr (p + i)) s Hsb Hni Hs) as (_ & b & Hmem & Hbv).
  exists b. split.
  { rewrite (dec_mrd_off mem (AC.shadow_addr (p + i)) Hsb Hni). exact Hmem. }
  unfold AC.shadow_ok. destruct Hok as [Hs0 | [Hlt Hhi]].
  - left. rewrite byte_signed_small by lia. lia.
  - right. rewrite byte_signed_small by lia. lia.
Qed.

(* The 8-aligned shadow cover of a sub-range of a live block is not hidden: it lies inside the block's shadow
   hull, which aview sees (al_shadow's shadow_hull_vis), and off the image. *)
Lemma ar_shadow_vis : forall ly S (W : world decodesegs0) mem md p n x len s,
  @AR rc decodesegs0 B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  p <= x -> 0 < len -> x + len <= p + req_size n ->
  AC.shadow_addr x / 8 * 8 <= s < AC.shadow_addr (x + len - 1) / 8 * 8 + 8 ->
  w_H W (Z_to_bv 64 s) = false.
Proof.
  intros ly S W mem md p n x len s HAR Hin Hpx Hlen Hxl Hs.
  pose proof (al_shadow _ _ LAWS ly S W mem md p n HAR Hin) as (_ & Hhull).
  pose proof (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & H4096 & Hceil & _ & _ & _ & Hn).
  pose proof (req_size_pos n ltac:(lia)) as (Hrs1 & Hrs2).
  pose proof (@YG0f.ASAN_CEIL_range rc) as [CR _]. unfold ASAN_CEIL in CR.
  assert (M1 : p / 8 <= x / 8) by (apply Z.div_le_mono; lia).
  assert (M2 : (x + len - 1) / 8 <= (p + req_size n - 1) / 8) by (apply Z.div_le_mono; lia).
  assert (L1 : (SHADOW_OFF + p / 8) / 8 <= (x / 8 + AC.ASAN_K) / 8)
    by (apply Z.div_le_mono; [lia | unfold SHADOW_OFF, AC.ASAN_K; lia]).
  assert (L2 : ((x + len - 1) / 8 + AC.ASAN_K) / 8 <= (SHADOW_OFF + (p + req_size n - 1) / 8) / 8)
    by (apply Z.div_le_mono; [lia | unfold SHADOW_OFF, AC.ASAN_K; lia]).
  assert (Hin_hull : YG0f.shadow_addr p / 8 * 8 <= s < YG0f.shadow_addr (p + req_size n - 1) / 8 * 8 + 8).
  { unfold YG0f.shadow_addr. unfold AC.shadow_addr in Hs. lia. }
  pose proof (Hhull s Hin_hull) as Hv.
  assert (Hlo : AC.ASAN_K <= s).
  { unfold AC.shadow_addr in Hs. unfold AC.ASAN_K in *. Z.div_mod_to_equations. lia. }
  assert (Hhi : s < 2 ^ 64).
  { unfold AC.shadow_addr in Hs. unfold AC.ASAN_K in *. Z.div_mod_to_equations. lia. }
  assert (Hni : ~ GD.in_img decodesegs0 s).
  { intros Him. pose proof (crt_segs_low s Him). unfold kLowMemEnd, AC.ASAN_K in *. lia. }
  destruct (w_H W (Z_to_bv 64 s)) eqn:EH; [exfalso | reflexivity].
  apply Hv. unfold aview, mbyte, mrestrict. rewrite EH. cbv beta iota.
  rewrite (dec_seg_rom_none s ltac:(unfold AC.ASAN_K in Hlo; lia) Hni). reflexivity.
Qed.
End ARhelpers.

(* ======================================================================== *)
(* The convert-loop piece                                                    *)
(* ======================================================================== *)
Section Mid.
Context {fx : YKK.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable RO_RD : list (Z * Z).
Hypothesis LAWS : AR_laws decodesegs0 B.
Hypothesis LOOP : crt_loop_stmt_F.

Local Notation segs := decodesegs0.

(* The rounding-mode predicates of the cuts (YK0o.v:13) and of the footprint runs (lib/Lib/FP.v:64) have the
   same body. *)
Lemma frm_zero_frm0 : forall f : bv 32, frm_zero f -> frm0 f.
Proof. intros f H. exact H. Qed.
Lemma frm0_frm_zero : forall f : bv 32, frm0 f -> frm_zero f.
Proof. intros f H. exact H. Qed.

Theorem crtA_mid_piece : crtA_at_loopout B MT RO_RD -> crtA_at_calloc B MT RO_RD.
Proof.
  intros HLO. unfold crtA_at_calloc.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs audio pcm nch ns bA nA bP nP T ch
         ly1 S1 W1 mem1 md1 regs1 P Q R
         HPRE HMID HREGS HPRELOOP H10 HFRM HBLK.
  pose proof HPRE as HPRE0. pose proof HBLK as HBLK0.
  destruct HPRE as (_HJ0 & _HRA_ok & _Hra4 & _Hgp & _Htp & _H10a & _H11a & _H12 & _H13 & _HCH &
                   _Hmod & _Hwlo & _Hwhi & _HEV & HN & HNS & HBND &
                   _HbA_in & _HbA_lo & _HbA_hi & HbP_in & HbP_lo & HbP_hi & _HBR &
                   _HEVB & _HLIVE & _HMO_OK & _HCOST & _HUM1 & _HUF2 & _HUFIX & _HROM_ON & _HROSC).
  destruct HMID as (HJ1 & HFRAMES & HMOLE & HCRT_FRAME & HROM1).
  destruct HBLK as (HPERM & HPpos & HQpos & HRpos).
  destruct HREGS as (HSP1 & HGP1 & HTP1 & HS0_1 & HS1_1 & HS2_1 & HS3_1 & HS4_1 & HS5_1 & _HS7_1 & HS8_1 & HS11_1).
  destruct HPRELOOP as (HS6_1 & _HS9_1 & _HS10_1).
  pose proof HJ1 as HJ1c.
  destruct HJ1 as (HAR1 & _Hly1 & _Hsecs1 & _Hwle1 & _Hio1 & _Hfrs1 & _Hnev1 & _Hk1
                   & _HJF1 & HJF2 & _HJF3 & _HJF4 & _HJgone & _HJpres & HJstat & _HJF5 & _HJQT).
  pose proof (@YG0f.ASAN_CEIL_range rc) as [CR _]. unfold ASAN_CEIL in CR.
  pose proof HJstat as (_Hal & _Hstk0 & Hceil_lo & Hlo_sp & _Hhi_sp & _H47 & _Hbot & _Htop2 & _Htop).
  (* ---- numeric facts ---- *)
  assert (HNNS : 0 < nch * ns) by nia.
  assert (H3NN : 3 * nch * ns = 3 * (nch * ns)) by ring.
  assert (H4NN : 4 * nch * ns = 4 * (nch * ns)) by ring.
  (* ---- the blocks in the post-call block list ---- *)
  assert (HPinS1 : In (P, 4 * (nch * ns)) (ablocks B ly1 S1)).
  { eapply Permutation_in; [apply Permutation_sym; exact HPERM | right; right; left; reflexivity]. }
  assert (HQinS1 : In (Q, 8 * nch) (ablocks B ly1 S1)).
  { eapply Permutation_in; [apply Permutation_sym; exact HPERM | right; left; reflexivity]. }
  assert (HRinS1 : In (R, 3 * (nch * ns)) (ablocks B ly1 S1)).
  { eapply Permutation_in; [apply Permutation_sym; exact HPERM | left; reflexivity]. }
  assert (HbPinS1 : In (bP, nP) (ablocks B ly1 S1)).
  { eapply Permutation_in; [apply Permutation_sym; exact HPERM | right; right; right; exact HbP_in]. }
  pose proof (al_blocks _ _ LAWS ly1 S1 W1 mem1 md1 P (4 * (nch * ns)) HAR1 HPinS1)
    as (HPmod & HP4096 & HPceil & _HPapp & _HPpres & HSEP & _HPn).
  pose proof (al_blocks _ _ LAWS ly1 S1 W1 mem1 md1 Q (8 * nch) HAR1 HQinS1)
    as (HQmod & HQ4096 & HQceil & _ & _ & _ & _).
  pose proof (al_blocks _ _ LAWS ly1 S1 W1 mem1 md1 R (3 * (nch * ns)) HAR1 HRinS1)
    as (_ & HR4096 & HRceil & _ & _ & _ & _).
  pose proof (al_blocks _ _ LAWS ly1 S1 W1 mem1 md1 bP nP HAR1 HbPinS1)
    as (_ & HbP4096 & HbPceil & _ & _ & _ & HbPn).
  assert (HPreq : req_size (4 * (nch * ns)) = 4 * (nch * ns))
    by (unfold req_size; destruct (Z.eqb_spec (4 * (nch * ns)) 0); [lia | reflexivity]).
  assert (HQreq : req_size (8 * nch) = 8 * nch)
    by (unfold req_size; destruct (Z.eqb_spec (8 * nch) 0); [lia | reflexivity]).
  assert (HRreq : req_size (3 * (nch * ns)) = 3 * (nch * ns))
    by (unfold req_size; destruct (Z.eqb_spec (3 * (nch * ns)) 0); [lia | reflexivity]).
  pose proof (req_size_pos nP ltac:(lia)) as (_ & HbPreq).
  rewrite HPreq in HPceil. rewrite HQreq in HQceil. rewrite HRreq in HRceil.
  assert (Hpcm_hi : pcm + 3 * (nch * ns) <= bP + req_size nP) by lia.
  (* ---- disjointness: the pairwise block ranges, carried through the permutation ---- *)
  pose proof (Permutation_map (fun b : Z * Z => (fst b, req_size (snd b))) HPERM) as HpermMap.
  pose proof (pairwise_perm zdisjoint _ _ zdisjoint_sym HpermMap HSEP) as Hpwp.
  cbn [map pairwise fst snd] in Hpwp.
  destruct Hpwp as (_HFR & HFQ & HFP & _).
  pose proof (Forall_inv HFQ) as HQP. pose proof (Forall_inv_tail HFQ) as HFQt.
  unfold zdisjoint in HQP. cbn [fst snd] in HQP. rewrite HQreq, HPreq in HQP.
  assert (HbPm : In (bP, req_size nP) (map (fun b : Z * Z => (fst b, req_size (snd b))) (ablocks B lyc Sc)))
    by (apply (in_map (fun b : Z * Z => (fst b, req_size (snd b))) _ (bP, nP)); exact HbP_in).
  pose proof (proj1 (Forall_forall _ _) HFP _ HbPm) as HPbP.
  pose proof (proj1 (Forall_forall _ _) HFQt _ HbPm) as HQbP.
  unfold zdisjoint in HPbP, HQbP. cbn [fst snd] in HPbP, HQbP. rewrite HPreq in HPbP. rewrite HQreq in HQbP.
  (* the two fresh blocks are not blocks of the caller *)
  assert (HPnew : ~ In (P, 4 * (nch * ns)) (ablocks B lyc Sc)).
  { intros Hin. assert (HPm : In (P, req_size (4 * (nch * ns)))
                         (map (fun b : Z * Z => (fst b, req_size (snd b))) (ablocks B lyc Sc)))
      by (apply (in_map (fun b : Z * Z => (fst b, req_size (snd b))) _ (P, 4 * (nch * ns))); exact Hin).
    pose proof (proj1 (Forall_forall _ _) HFP _ HPm) as HPP. unfold zdisjoint in HPP. cbn [fst snd] in HPP.
    rewrite HPreq in HPP. lia. }
  assert (HQnew : ~ In (Q, 8 * nch) (ablocks B lyc Sc)).
  { intros Hin. assert (HQm : In (Q, req_size (8 * nch))
                         (map (fun b : Z * Z => (fst b, req_size (snd b))) (ablocks B lyc Sc)))
      by (apply (in_map (fun b : Z * Z => (fst b, req_size (snd b))) _ (Q, 8 * nch)); exact Hin).
    pose proof (proj1 (Forall_forall _ _) HFQt _ HQm) as HQQ. unfold zdisjoint in HQQ. cbn [fst snd] in HQQ.
    rewrite HQreq in HQQ. lia. }
  assert (DPQ : P + 4 * nch * ns <= Q \/ Q + 8 * nch <= P) by lia.
  assert (DPC : P + 4 * nch * ns <= pcm \/ pcm + 3 * nch * ns <= P) by lia.
  assert (DQC : Q + 8 * nch <= pcm \/ pcm + 3 * nch * ns <= Q) by lia.
  (* ---- the loop's address premises at mem1 ---- *)
  pose proof (ar_addressable B LAWS ly1 S1 W1 mem1 md1 P (4 * (nch * ns)) HAR1 HPinS1) as HADP.
  pose proof (ar_addressable B LAWS ly1 S1 W1 mem1 md1 Q (8 * nch) HAR1 HQinS1) as HADQ.
  pose proof (ar_addressable B LAWS ly1 S1 W1 mem1 md1 bP nP HAR1 HbPinS1) as HADbP.
  rewrite HPreq in HADP. rewrite HQreq in HADQ.
  assert (HADC : AC.addressable mem1 pcm (3 * nch * ns)).
  { destruct HADbP as (Hp0 & Hn0 & Hend & HA).
    split; [lia|]. split; [lia|]. split; [lia|].
    intros i Hi. specialize (HA (pcm - bP + i) ltac:(lia)).
    replace (bP + (pcm - bP + i)) with (pcm + i) in HA by ring. exact HA. }
  assert (HWP : wr_at AImg.rsegs mem1 P (4 * nch * ns)).
  { split; [lia|]. split; [lia|].
    intros i Hi. destruct (ar_vis B LAWS ly1 S1 W1 mem1 md1 P _ (P + i) HAR1 HPinS1 ltac:(rewrite HPreq; lia))
      as (_ & b & Hb).
    unfold wview, wa. rewrite Hb. discriminate. }
  assert (HWQ : wr_at AImg.rsegs mem1 Q (8 * nch)).
  { split; [lia|]. split; [lia|].
    intros i Hi. destruct (ar_vis B LAWS ly1 S1 W1 mem1 md1 Q _ (Q + i) HAR1 HQinS1 ltac:(rewrite HQreq; lia))
      as (_ & b & Hb).
    unfold wview, wa. rewrite Hb. discriminate. }
  (* ---- the pcm bytes the loop reads: pb ---- *)
  pose (pb := fun i : Z => match mem1 (Z_to_bv 64 (pcm + i)) with Some b => b | None => Z_to_bv 8 0 end).
  assert (Hpcm_vis : forall i, 0 <= i < 3 * nch * ns ->
            w_H W1 (Z_to_bv 64 (pcm + i)) = false /\ mem1 (Z_to_bv 64 (pcm + i)) = Some (pb i)).
  { intros i Hi. destruct (ar_vis B LAWS ly1 S1 W1 mem1 md1 bP nP (pcm + i) HAR1 HbPinS1 ltac:(lia))
      as (Hh & b & Hb).
    split; [exact Hh|]. cbv [pb]. rewrite Hb. reflexivity. }
  assert (Hpcm_off : forall i, 0 <= i < 3 * nch * ns -> ~ GD.in_img decodesegs0 (pcm + i)).
  { intros i Hi. exact (ar_off_img B LAWS ly1 S1 W1 mem1 md1 bP nP (pcm + i) HAR1 HbPinS1 ltac:(lia)). }
  assert (HPB : forall i, 0 <= i < 3 * nch * ns -> mrd AImg.rsegs mem1 (wa (pcm + i)) = Some (pb i)).
  { intros i Hi. rewrite (dec_mrd_off mem1 (pcm + i) ltac:(lia) (Hpcm_off i Hi)).
    exact (proj2 (Hpcm_vis i Hi)). }
  (* the entry's reader of the pcm bytes is pb: the caller block bP is kept by the inner journal *)
  assert (Hrd : forall i, 0 <= i < 3 * nch * ns ->
            aview segs (w_H W) memc (pcm + i) = Some (bv_unsigned (pb i))).
  { intros i Hi.
    pose proof (HJF2 bP nP (pcm - bP + i) HbP_in HbPinS1 ltac:(lia) ltac:(intros (rg & [] & _))) as E.
    replace (bP + (pcm - bP + i)) with (pcm + i) in E by ring.
    rewrite <- E. destruct (Hpcm_vis i Hi) as (Hh & Hb).
    exact (aview_of_present (w_H W1) mem1 (pcm + i) (pb i) Hh Hb). }
  (* ---- the footprint the walk gives the run, and the six ranges the loop needs ---- *)
  set (RNG := LCK.RNG_W (world segs) (@w_H segs) W1).
  assert (Hrng : forall lo len, 0 <= lo -> lo + len <= 2 ^ 64 ->
            (forall a, lo <= a < lo + len -> w_H W1 (Z_to_bv 64 a) = false) -> ExecF.rng RNG lo len).
  { intros lo len Hlo Hlen Hv. split; [exact Hlo|]. split; [exact Hlen|].
    intros b j Hb Hj. unfold RNG, LCK.RNG_W, LCK.range_avoids, LCK.woff. intros kk Hkk.
    rewrite (uns_small b ltac:(lia)). apply Hv. lia. }
  assert (RP : ExecF.rng RNG P (4 * nch * ns)).
  { apply Hrng; [lia | lia |]. intros a Ha.
    exact (proj1 (ar_vis B LAWS ly1 S1 W1 mem1 md1 P _ a HAR1 HPinS1 ltac:(rewrite HPreq; lia))). }
  assert (RQ : ExecF.rng RNG Q (8 * nch)).
  { apply Hrng; [lia | lia |]. intros a Ha.
    exact (proj1 (ar_vis B LAWS ly1 S1 W1 mem1 md1 Q _ a HAR1 HQinS1 ltac:(rewrite HQreq; lia))). }
  assert (RC : ExecF.rng RNG pcm (3 * nch * ns)).
  { apply Hrng; [lia | lia |]. intros a Ha. replace a with (pcm + (a - pcm)) by ring.
    exact (proj1 (Hpcm_vis (a - pcm) ltac:(lia))). }
  assert (Hsh_rng : forall p n X len, In (p, n) (ablocks B ly1 S1) -> p <= X -> 0 < len ->
            X + len <= p + req_size n ->
            ExecF.rng RNG (AC.shadow_addr X / 8 * 8)
              (AC.shadow_addr (X + len - 1) / 8 * 8 + 8 - AC.shadow_addr X / 8 * 8)).
  { intros p n X len Hin HpX Hlen HXl.
    pose proof (al_blocks _ _ LAWS ly1 S1 W1 mem1 md1 p n HAR1 Hin) as (_ & Hp4096 & Hpceil & _ & _ & _ & Hpn).
    pose proof (req_size_pos n ltac:(lia)) as (_ & _).
    apply Hrng.
    - unfold AC.shadow_addr, AC.ASAN_K. Z.div_mod_to_equations. lia.
    - unfold AC.shadow_addr, AC.ASAN_K. Z.div_mod_to_equations. lia.
    - intros a Ha.
      replace (AC.shadow_addr X / 8 * 8 + (AC.shadow_addr (X + len - 1) / 8 * 8 + 8 - AC.shadow_addr X / 8 * 8))
        with (AC.shadow_addr (X + len - 1) / 8 * 8 + 8) in Ha by ring.
      exact (ar_shadow_vis B LAWS ly1 S1 W1 mem1 md1 p n X len a HAR1 Hin HpX Hlen HXl Ha). }
  assert (RSP := Hsh_rng P (4 * (nch * ns)) P (4 * nch * ns) HPinS1 ltac:(lia) ltac:(lia)
                   ltac:(rewrite HPreq; lia)).
  assert (RSQ := Hsh_rng Q (8 * nch) Q (8 * nch) HQinS1 ltac:(lia) ltac:(lia) ltac:(rewrite HQreq; lia)).
  assert (RSC := Hsh_rng bP nP pcm (3 * nch * ns) HbPinS1 ltac:(lia) ltac:(lia) ltac:(lia)).
  (* ---- the registers at the cut, in the form ms_of_regs reads them ---- *)
  assert (E8 : YKK.getr regs1 (Z_to_bv 5 8) = Z_to_bv 64 P) by exact HS0_1.
  assert (E21 : YKK.getr regs1 (Z_to_bv 5 21) = Z_to_bv 64 Q) by exact HS5_1.
  assert (E10 : YKK.getr regs1 (Z_to_bv 5 10) = Z_to_bv 64 R) by exact H10.
  assert (E19 : YKK.getr regs1 (Z_to_bv 5 19) = Z_to_bv 64 nch) by exact HS3_1.
  assert (E18 : YKK.getr regs1 (Z_to_bv 5 18) = Z_to_bv 64 ns) by exact HS2_1.
  assert (E22 : YKK.getr regs1 (Z_to_bv 5 22) = Z_to_bv 64 pcm) by exact HS6_1.
  assert (E24 : YKK.getr regs1 (Z_to_bv 5 24) = Z_to_bv 64 ASAN_K) by exact HS8_1.
  (* ---- the run: seg4 then the convert loop, carried into the walk by crtA_run ---- *)
  eapply (crtA_run (fx := fx) W1 regs1 mem1 md1 CRT_RET_CALLOC).
  { unfold LCK.ms_of_regs. fold RNG.
    eapply ExecF.evtF_cut.
    { eapply crt_seg4_F with (P := P) (Q := Q) (R := R) (nch := nch) (ns := ns);
        [exact E8 | exact E21 | exact E10 | exact E19 | exact E18 | lia | lia | lia | lia | lia]. }
    intros ms1 (a0' & a1' & F' & -> & F15 & _FK).
    rewrite E8, E22, E18, E19, E21, E24.
    pose proof LOOP as HL. unfold crt_loop_stmt_F in HL.
    eapply HL with (pb := pb) (P := P) (Q := Q) (pcm := pcm) (nch := nch) (ns := ns);
      first [ exact HPmod | exact HQmod | exact HPB | exact HWP | exact HWQ
            | exact HADQ | exact HADC | exact DPQ | exact DPC | exact DQC
            | exact F15 | exact (frm_zero_frm0 _ HFRM)
            | exact RP | exact RQ | exact RC | exact RSP | exact RSQ | exact RSC
            | (rewrite H4NN; exact HADP) | lia ]. }
  (* ---- the continuation: the state at CRT_LOOP_OUT ---- *)
  intros ms' md' (ms0 & HP0 & Heqv) Hmat.
  destruct HP0 as (lt0 & lt1 & lt2 & la0 & la1 & la2 & ls6 & ls9 & ls10 & lt3 & lt4 & lt5 & lt6 &
                   F'' & fc' & m & -> & FRM' & CI).
  pose proof CI as (MU & WM & HPd & HQd).
  set (fx1 := YKK.mkFP F'' fc').
  pose proof (crtA_ms_shape (fx := fx1) _ _ _ ms' Heqv) as Hshape.
  rewrite Hshape.
  apply (HLO STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs audio pcm nch ns bA nA bP nP T ch
           ly1 S1 W1 m md' (ms_regs ms') P Q R fx1 HPRE0).
  - (* crtA_mid at the loop-out memory *)
    split; [| split; [exact HFRAMES | split; [exact HMOLE | split]]].
    + (* the inner journal across the loop's writes *)
      eapply (ajournal_exec decodesegs0 B LAWS crt_segs_low) with
        (Wr := fun a => (P <= a < P + 4 * nch * ns) \/ (Q <= a < Q + 8 * nch));
        [exact HJ1c | | | | exact Hmat |].
      * intros x HnW. cbv beta in HnW. unfold mrestrict. destruct (w_H W1 x); [reflexivity|].
        apply MU. unfold crt_W. cbn [outside].
        split; [|split; [|exact I]]; intros HH; apply HnW; [left | right]; exact HH.
      * intros x Hx. unfold mrestrict in *. destruct (w_H W1 x) eqn:EH; [exact Hx|].
        pose proof (bv_unsigned_in_range 64 x) as Hx64. change (bv_modulus 64) with (2 ^ 64) in Hx64.
        set (a := bv_unsigned x) in *.
        assert (Hxa : x = Z_to_bv 64 a) by (unfold a; symmetry; apply bv_self).
        assert (Hcase : (P <= a < P + 4 * nch * ns) \/ (Q <= a < Q + 8 * nch) \/
                        (~ (P <= a < P + 4 * nch * ns) /\ ~ (Q <= a < Q + 8 * nch))) by lia.
        destruct Hcase as [HaP | [HaQ | [HnP HnQ]]].
        -- (* in the P block: the loop wrote its four bytes *)
           assert (Hk : 0 <= (a - P) / 4 < nch * ns)
             by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
           pose proof (bytes_at_present m _ _ ((a - P) mod 4) (HPd _ Hk)) as HPr.
           rewrite length_Z_to_le_bytes in HPr.
           assert (Heq : P + 4 * ((a - P) / 4) + (a - P) mod 4 = a)
             by (pose proof (Z.div_mod (a - P) 4 ltac:(lia)); lia).
           rewrite Heq in HPr. rewrite Hxa. apply HPr.
           ++ pose proof (Z.mod_pos_bound (a - P) 4 ltac:(lia)). change (Z.of_nat 4) with 4. lia.
           ++ exact (ar_off_img B LAWS ly1 S1 W1 mem1 md1 P _ a HAR1 HPinS1 ltac:(rewrite HPreq; lia)).
        -- (* in the Q block: the loop wrote its eight bytes *)
           assert (Hc : 0 <= (a - Q) / 8 < nch)
             by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
           pose proof (bytes_at_present m _ _ ((a - Q) mod 8) (HQd _ Hc)) as HPr.
           rewrite length_le8 in HPr.
           assert (Heq : Q + 8 * ((a - Q) / 8) + (a - Q) mod 8 = a)
             by (pose proof (Z.div_mod (a - Q) 8 ltac:(lia)); lia).
           rewrite Heq in HPr. rewrite Hxa. apply HPr.
           ++ pose proof (Z.mod_pos_bound (a - Q) 8 ltac:(lia)). change (Z.of_nat 8) with 8. lia.
           ++ exact (ar_off_img B LAWS ly1 S1 W1 mem1 md1 Q _ a HAR1 HQinS1 ltac:(rewrite HQreq; lia)).
        -- (* outside both blocks: the memory is kept *)
           rewrite (MU x). exact Hx.
           unfold crt_W. cbn [outside]. split; [exact HnP | split; [exact HnQ | exact I]].
      * intros x HH.
        apply MU. unfold crt_W. cbn [outside]. split; [|split; [|exact I]]; intros [Ha Hb].
        -- pose proof (ar_vis B LAWS ly1 S1 W1 mem1 md1 P _ (bv_unsigned x) HAR1 HPinS1
                         ltac:(rewrite HPreq; lia)) as (Hh & _).
           rewrite bv_self in Hh. congruence.
        -- pose proof (ar_vis B LAWS ly1 S1 W1 mem1 md1 Q _ (bv_unsigned x) HAR1 HQinS1
                         ltac:(rewrite HQreq; lia)) as (Hh & _).
           rewrite bv_self in Hh. congruence.
      * intros a HWa. cbv beta in HWa. right; right; left.
        destruct HWa as [HaP | HaQ].
        -- exists P, (4 * (nch * ns)). split; [exact HPinS1|]. split; [exact HPnew|]. rewrite HPreq. lia.
        -- exists Q, (8 * nch). split; [exact HQinS1|]. split; [exact HQnew|]. rewrite HQreq. lia.
    + (* the frame: the loop writes no stack byte (the frame is above alloc_ceiling, the blocks below) *)
      unfold crtA_frame in HCRT_FRAME |- *.
      eapply rw_cells_transport; [exact HCRT_FRAME | exact MU | exact WM |].
      unfold crt_W. rewrite crt_fr_size. cbn [disjoint_from].
      unfold DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in Hlo_sp. unfold CRT_FRAME.
      split; [|split; [|exact I]]; right; lia.
    + (* the read-only bytes the callees read: image bytes, hence off the two write windows *)
      intros a HinRO Hinrom.
      rewrite <- (HROM1 a HinRO Hinrom).
      apply aview_eq_of. unfold mrestrict. destruct (w_H W1 (Z_to_bv 64 a)); [reflexivity|].
      destruct Hinrom as (sg & Hin & _ & Hr).
      assert (Him : GD.in_img segs a) by (exists sg; split; [exact Hin | lia]).
      pose proof (crt_segs_low a Him) as Hlow.
      apply MU. rewrite (uns_small a ltac:(unfold kLowMemEnd in Hlow; lia)).
      unfold crt_W. cbn [outside]. split; [|split; [|exact I]]; intros Ha.
      * exact (ar_off_img B LAWS ly1 S1 W1 mem1 md1 P _ a HAR1 HPinS1 ltac:(rewrite HPreq; lia) Him).
      * exact (ar_off_img B LAWS ly1 S1 W1 mem1 md1 Q _ a HAR1 HQinS1 ltac:(rewrite HQreq; lia) Him).
  - (* the registers at CRT_LOOP_OUT, read off the loop's post state *)
    unfold crtA_regs.
    repeat match goal with |- _ /\ _ => split end;
      (rewrite (crtA_ms_reg _ _ _ _ _ _ _ _ _ Heqv) by reflexivity);
      first [ reflexivity | exact HSP1 | exact HGP1 | exact HTP1 | exact HS1_1 | exact HS4_1 | exact HS11_1 ].
  - exact HBLK0.
  - exact (frm0_frm_zero _ FRM').
  - (* crtA_conv: the loop's crt_inv, at the entry's reader *)
    split.
    + intros c Hc. exact (HQd c Hc).
    + intros kk Hkk.
      assert (Ecv : cv pb kk = crtA_cv (aview segs (w_H W) memc) pcm kk).
      { unfold cv, crtA_cv, crtA_pb.
        rewrite (Hrd (3 * kk) ltac:(lia)), (Hrd (3 * kk + 1) ltac:(lia)), (Hrd (3 * kk + 2) ltac:(lia)).
        reflexivity. }
      rewrite <- Ecv. exact (HPd kk Hkk).
Qed.
End Mid.
