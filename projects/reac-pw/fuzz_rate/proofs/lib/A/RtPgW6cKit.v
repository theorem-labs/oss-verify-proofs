(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6cKit.v at 4c23b042570d for reac-pw/fuzz_rate's
   image A: module paths changed; role's RPgSeg / RPgMem vocabulary (e_R, e_F, e_pp, e_src, e_left, rl_inw, rm_) becomes
   rate's (q_R, q_F, q_pp, q_src, q_left, rt_inw, rtm_); the segment pre is rate's rt_seg_pre, which does not carry the
   frame's prologue shadow, so rs_wr_shadow and rs_in_now take it as a premise (rs_start_M01 gives it); the image's
   first write range hi_w1 has six ranges; the frame's shadow pattern has 56 bytes; the real frame is 0x1e0 bytes. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, same loaded bytes): the kit of the walk piece
   "ent_build C" of LLVMFuzzerTestOneInput (0x80714): ent_build's cases 6, 7 and 8 (pod.h:340-366), from their
   switch entries 0x81880 / 0x81754 / 0x818d0 to the join J 0x81e00. Proves no function (kind: segment lemma).

   PART 1. A SEGMENT'S START FACTS AT A CUT. rate_build_contract states the input bytes, their shadow bytes and the
   read-only data at the segment's start memory (RtPgSeg rs_in, rs_pre); a piece runs at a cut's memory. rs_in_now
   and rs_rom_now carry them across what the segment may have written (RtPgSeg rs_core: every byte outside the
   callees' stack [R - T_SEG_STK, R) and outside rs_E1 is the start's), with RtPgMem section 9's address facts:
   the input's shadow bytes lie in the shadow band, so outside F, pp, R's cells and the stack; they are outside
   [shF, shF + 56) because every byte of the prologue's pattern P0 is >= 8 and the input is addressable at the
   start; the 8-aligned hull of those shadow bytes may reach into [shF, shF + 56), which every cut keeps present
   (its rs_fsh_at). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YP08.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgImgA RtPgMem RtPgSteps RtPgSeg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.

(* ===================================== PART 1. start facts at a cut ===================================== *)
(* what a cut may have changed since the segment's start: outside [0, 2^64), the callees' stack, rs_E1 *)
Definition rs_wr (cx : rs_scx segs) (a : Z) : Prop :=
(a < 0 \/ 2 ^ 64 <= a) \/ (q_R (x_e segs cx) - T_SEG_STK <= a < q_R (x_e segs cx)) \/ rs_E1 segs cx a.

(* the address facts of the segment's start: R above the shadow band, F and pp in the application's memory *)
Lemma rs_pre_geom : forall cx, rs_pre segs B cx ->
spZ (x_regs segs cx) = q_R (x_e segs cx) /\
kHighMemBeg <= q_R (x_e segs cx) - T_SEG_STK /\ q_R (x_e segs cx) + 0x1e0 <= 2 ^ 47 /\
In (3, x_pos segs cx) (frames (x_Sc segs cx)) /\ q_F (x_e segs cx) = frame_addr (x_lyc segs cx) 3 (x_pos segs cx) /\
in_app (q_F (x_e segs cx)) 512 /\ q_F (x_e segs cx) mod 32 = 0 /\
in_app (q_pp (x_e segs cx)) Layout.PP_SIZE.
Proof.
intros [STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc RLO RHI e pos] HP.
unfold rs_pre, rt_seg_pre in HP.
cbn [x_STK x_sp0 x_FP x_ly x_S x_W0 x_mem0 x_md0 x_own x_k x_regs x_lyc x_Sc x_W x_memc x_mdc x_RLO x_RHI x_e x_pos] in *.
destruct HP as (HJ & _ & Hsp & _ & _ & HeS & HR16 & HRS & HSTK & Hown & HF & _ & Hpp & _).
cbn [hi_cid hi_rsz rate_himg_A] in *.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & HSTK0 & Hceil & Hlo & Hhi & H47 & _).
pose proof alloc_ceiling_value as (Hc1 & _).
assert (Hin3 : In (3, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ (AR_laws_ok segs B) lyc Sc W memc mdc 3 pos HAR Hin3) as (HF32 & HFapp & _).
destruct (al_blocks _ _ (AR_laws_ok segs B) lyc Sc W memc mdc (q_pp e) Layout.PP_SIZE HAR Hpp) as (_ & _ & _ & Happ & _).
change (fs_frame_bytes 3) with 512 in HFapp. rewrite <- HF in HFapp, HF32.
replace (req_size Layout.PP_SIZE) with Layout.PP_SIZE in Happ by reflexivity.
assert (HR0 : 0 <= q_R e < 2 ^ 64) by (unfold T_SEG_STK, ASTACK in HSTK; unfold kHighMemBeg; lia).
split; [unfold spZ; rewrite Hsp; unfold w64; apply unsigned_lit_small; lia|].
split; [unfold T_SEG_STK, ASTACK in *; unfold kHighMemBeg; lia|].
split; [lia|].
split; [exact Hin3|]. split; [exact HF|]. split; [exact HFapp|]. split; [exact HF32 | exact Happ].
Qed.

Lemma rs_core_kept : forall cx ly2 S2 W2 regs2 mem2 md2,
rs_pre segs B cx -> rs_core segs B MT cx (rs_E1 segs cx) ly2 S2 W2 regs2 mem2 md2 ->
forall a, ~ rs_wr cx a -> aview segs (w_H W2) mem2 a = aview segs (w_H (x_W segs cx)) (x_memc segs cx) a.
Proof.
intros cx ly2 S2 W2 regs2 mem2 md2 HP HC a Ha.
destruct (rs_pre_geom cx HP) as (Hsp & _).
destruct HC as (_ & _ & _ & _ & _ & _ & HK). unfold rs_wr in Ha.
apply HK; [lia | rewrite Hsp; intros X; apply Ha; right; left; exact X | intros X; apply Ha; right; right; exact X].
Qed.

(* a shadow byte of an application address is never in rs_E1 or the callees' stack *)
Lemma rs_wr_shadow : forall cx x, rs_pre segs B cx ->
rt_fsh segs (w_H (x_W segs cx)) (x_memc segs cx) (q_F (x_e segs cx)) rate_A_shA ->
0 <= x < kHighMemEnd ->
range_addressable (aview segs (w_H (x_W segs cx)) (x_memc segs cx)) SHADOW_OFF x 1 ->
~ rs_wr cx (shadow_of_addr SHADOW_OFF x).
Proof.
intros cx x HP Hfsh Hx Hra.
destruct (rs_pre_geom cx HP) as (_ & HRk & _ & _ & _ & HFapp & _ & Happ).
pose proof (rtm_shadow_band x Hx) as Hb.
pose proof (rtm_ra_not_fsh segs _ _ _ _ x 1 Hra Hfsh rtm_sh_P0_big x ltac:(lia)) as Hnf.
change (Z.of_nat (length rate_A_shA)) with 56 in Hnf.
unfold rs_wr, rs_E1, rt_inw. cbn [hi_w1 rate_himg_A].
intros [H|[H|[H|H]]].
- unfold kLowMemEnd, kHighMemBeg in Hb. lia.
- unfold kHighMemBeg in *. lia.
- apply Exists_exists in H. destruct H as (w & Hw & Hin). cbn [In] in Hw.
  destruct Hw as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd rt_xv] in Hin.
  + apply (rtm_shadow_not_app x (q_F (x_e segs cx)) 512 Hx HFapp). lia.
  + apply Hnf. lia.
  + unfold kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
  + unfold kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
  + unfold kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
  + unfold kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
- apply (rtm_shadow_not_app x (q_pp (x_e segs cx)) Layout.PP_SIZE Hx Happ). exact H.
Qed.

Lemma rs_in_now : forall cx rest pat ly2 S2 W2 regs2 mem2 md2,
rs_pre segs B cx -> rt_fsh segs (w_H (x_W segs cx)) (x_memc segs cx) (q_F (x_e segs cx)) rate_A_shA ->
rs_in segs cx rest -> rs_core segs B MT cx (rs_E1 segs cx) ly2 S2 W2 regs2 mem2 md2 ->
rs_fsh_at segs cx W2 mem2 pat -> length pat = 56%nat ->
garr8 segs (mrestrict (w_H W2) mem2) (q_src (x_e segs cx)) (rs_u8s rest) /\
range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF (q_src (x_e segs cx)) (q_left (x_e segs cx)) /\
(0 < q_left (x_e segs cx) -> shadow_hull_vis (aview segs (w_H W2) mem2) (q_src (x_e segs cx)) (q_left (x_e segs cx))).
Proof.
intros cx rest pat ly2 S2 W2 regs2 mem2 md2 HP Hfsh0 HI HC Hfsh2 Hpat.
pose proof (rs_core_kept cx ly2 S2 W2 regs2 mem2 md2 HP HC) as HK.
destruct (rs_pre_geom cx HP) as (_ & HRk & _ & _ & _ & HFapp & _ & Happ).
destruct HI as (Hleft & Hbytes & Hra & Hhull & Hamr & Hsrc0 & Hsrc63 & Hdisj).
set (src := q_src (x_e segs cx)) in *. set (n := q_left (x_e segs cx)) in *.
assert (Hx : forall x, src <= x < src + n -> 0 <= x < kHighMemEnd).
{ intros x Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia. }
split.
- apply (rtm_bytes_kept_wr segs (rs_wr cx) _ _ _ _ src rest Hbytes HK).
  intros x Hx'. rewrite <- Hleft in Hx'. fold n in Hx'. destruct (Hdisj x Hx') as (D1 & D2 & D3).
  unfold rs_wr, rs_E1. intros [H|[H|[H|H]]]; [lia | exact (D1 H) | exact (D2 H) | exact (D3 H)].
- split.
  + apply (rtm_ra_kept_wr segs (rs_wr cx) _ _ _ _ SHADOW_OFF src n Hra HK).
    intros x Hx'. apply rs_wr_shadow; [exact HP | exact Hfsh0 | exact (Hx x Hx') |].
    apply (range_addressable_sub _ _ src n); [exact Hra | lia | lia].
  + intros Hn. apply (rtm_hull_kept segs _ _ _ _ src n (Hhull Hn)).
    intros s Hs Hnone.
    destruct (base.decide (rs_wr cx s)) as [Hw|Hw].
    2:{ rewrite (HK s Hw). exact Hnone. }
    assert (Hsb : SHADOW_OFF <= s < kHighMemBeg).
    { pose proof (Hx src ltac:(lia)). pose proof (Hx (src + n - 1) ltac:(lia)).
      unfold shadow_addr, SHADOW_OFF, kHighMemBeg, kHighMemEnd in *.
      pose proof (Z.div_pos src 8 ltac:(lia) ltac:(lia)).
      assert (2147450880 <= (2147450880 + src / 8) / 8 * 8).
      { assert (268431360 <= (2147450880 + src / 8) / 8) by (apply Z.div_le_lower_bound; lia). lia. }
      assert ((src + n - 1) / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
      assert ((2147450880 + (src + n - 1) / 8) / 8 < 2199291686912) by (apply Z.div_lt_upper_bound; lia).
      lia. }
    unfold rs_wr, rs_E1, rt_inw in Hw. cbn [hi_w1 rate_himg_A] in Hw.
    destruct Hw as [H|[H|[H|H]]].
    * exfalso. unfold SHADOW_OFF, kHighMemBeg in Hsb. lia.
    * exfalso. unfold kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
    * apply Exists_exists in H. destruct H as (w & Hw & Hin). cbn [In] in Hw.
      destruct Hw as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd rt_xv] in Hin.
      -- exfalso. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
      -- unfold rs_fsh_at, rt_fsh in Hfsh2. rewrite Hpat in Hfsh2.
         replace s with (shadow_addr (q_F (x_e segs cx)) + (s - shadow_addr (q_F (x_e segs cx)))) by lia.
         rewrite (Hfsh2 (s - shadow_addr (q_F (x_e segs cx))) ltac:(cbn; lia)). discriminate.
      -- exfalso. unfold kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
      -- exfalso. unfold kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
      -- exfalso. unfold kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
      -- exfalso. unfold kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
    * exfalso. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

(* rom_view at a cut: the image lies below the shadow band, outside every block and frame *)
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Lemma rs_rom_now : forall cx ly2 S2 W2 regs2 mem2 md2,
rs_pre segs B cx -> rs_core segs B MT cx (rs_E1 segs cx) ly2 S2 W2 regs2 mem2 md2 -> rom_view segs W2 mem2.
Proof.
intros cx ly2 S2 W2 regs2 mem2 md2 HP HC.
pose proof (rs_core_kept cx ly2 S2 W2 regs2 mem2 md2 HP HC) as HK.
destruct (rs_pre_geom cx HP) as (_ & HRk & _ & Hin3 & HF & HFapp & _ & Happ).
assert (Hrom : rom_view segs (x_W segs cx) (x_memc segs cx)).
{ destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. }
assert (HAR : AR segs B (x_lyc segs cx) (x_Sc segs cx) (x_W segs cx) (x_memc segs cx) (x_mdc segs cx)).
{ destruct HP as (HJ & _). exact (proj1 HJ). }
assert (Hpp : In (q_pp (x_e segs cx), Layout.PP_SIZE) (ablocks B (x_lyc segs cx) (x_Sc segs cx))).
{ destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. }
apply (rtm_rom_kept_wr segs (rs_wr cx) (x_W segs cx) W2 (x_memc segs cx) mem2 Hrom HK).
intros a (sg & Hsg & _ & Ha). assert (Himg : in_img segs a) by (exists sg; split; [exact Hsg | exact Ha]).
pose proof (segs_low a Himg) as Hlow.
pose proof (al_client_img _ _ (AR_laws_ok segs B) _ _ _ _ _ a HAR) as Hcl.
unfold rs_wr, rs_E1, rt_inw. cbn [hi_w1 rate_himg_A].
intros [H|[H|[H|H]]].
- unfold kLowMemEnd in Hlow. lia.
- unfold kLowMemEnd, kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
- apply Exists_exists in H. destruct H as (w & Hw & Hin). cbn [In] in Hw.
  destruct Hw as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd rt_xv] in Hin.
  + assert (HinF : frame_addr (x_lyc segs cx) 3 (x_pos segs cx) <= a <
      frame_addr (x_lyc segs cx) 3 (x_pos segs cx) + fs_frame_bytes 3)
      by (rewrite <- HF; change (fs_frame_bytes 3) with 512; lia).
    apply (proj2 (Hcl (or_intror (or_introl (ex_intro _ 3 (ex_intro _ (x_pos segs cx) (conj Hin3 HinF))))))).
    exact Himg.
  + unfold shadow_addr, SHADOW_OFF, kLowMemEnd in *. pose proof (Z.div_pos (q_F (x_e segs cx)) 8). unfold in_app in HFapp. lia.
  + unfold kLowMemEnd, kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
  + unfold kLowMemEnd, kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
  + unfold kLowMemEnd, kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
  + unfold kLowMemEnd, kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
- assert (Hinp : q_pp (x_e segs cx) <= a < q_pp (x_e segs cx) + req_size Layout.PP_SIZE)
    by (change (req_size Layout.PP_SIZE) with Layout.PP_SIZE; lia).
  apply (proj2 (Hcl (or_introl (ex_intro _ (q_pp (x_e segs cx)) (ex_intro _ Layout.PP_SIZE (conj Hpp Hinp)))))).
  exact Himg.
Qed.

End d.
End c.
End b.

Print Assumptions rs_in_now.
Print Assumptions rs_rom_now.
