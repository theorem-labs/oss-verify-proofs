(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6cKit.v at 876d0cb3d0d; part 1 (the start facts at a cut) only, for reac-pw/fuzz_headamp image A: module paths and the rs_ / rl_ / rm_ prefixes renamed to hs_ / hd_ / hm_, the frame for locals of class 4 (1024 bytes, 80 shadow bytes in hi_w1), the real frame of 0x1e0 bytes, hd_seg_pre's conjunct order (pp's block from hd_fresh_block), hs_pre at the start pattern hi_shA. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, same loaded bytes except .note.gnu.build-id): the start facts of the
   build segment M01 of LLVMFuzzerTestOneInput (0x80bc0) at a cut, shared by the walk pieces of that segment.
   Proves no function (kind: segment lemma).

   A SEGMENT'S START FACTS AT A CUT. headamp_build_contract states the input bytes, their shadow bytes and the
   read-only data at the segment's start memory (HPgSeg hs_in, hs_pre); a piece runs at a cut's memory. hs_in_now
   and hs_rom_now carry them across what the segment may have written (HPgSeg hs_core: every byte outside the
   callees' stack [R - T_SEG_STK, R) and outside hs_E1 is the start's), with HPgMem section 9's address facts:
   the input's shadow bytes lie in the shadow band, so outside F, pp, R's cells and the stack; they are outside
   [shF, shF + 80) because every byte of the prologue's pattern P0 is >= 8 and the input is addressable at the
   start; the 8-aligned hull of those shadow bytes may reach into [shF, shF + 80), which every cut keeps present
   (its hs_fsh_at). The segment's start is HPgSeg.hs_start_M01's, so the frame's shadow at the start is
   hi_shA headamp_himg_A = P0. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YP08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgMem HPgSteps HPgSeg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* lia without the disjunctions of the context *)
Local Ltac zl := repeat match goal with H : _ \/ _ |- _ => clear H end; lia.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.

(* ===================================== PART 1. start facts at a cut ===================================== *)
(* what a cut may have changed since the segment's start: outside [0, 2^64), the callees' stack, hs_E1 *)
Definition hs_wr (cx : hs_scx segs) (a : Z) : Prop :=
(a < 0 \/ 2 ^ 64 <= a) \/ (e_R (x_e segs cx) - T_SEG_STK <= a < e_R (x_e segs cx)) \/ hs_E1 segs cx a.

(* the address facts of the segment's start: R above the shadow band, F and pp in the application's memory *)
Lemma hs_pre_geom : forall cx, hs_pre segs B cx (hi_shA headamp_himg_A) ->
spZ (x_regs segs cx) = e_R (x_e segs cx) /\
kHighMemBeg <= e_R (x_e segs cx) - T_SEG_STK /\ e_R (x_e segs cx) + 0x1e0 <= 2 ^ 47 /\
In (4, x_pos segs cx) (frames (x_Sc segs cx)) /\ e_F (x_e segs cx) = frame_addr (x_lyc segs cx) 4 (x_pos segs cx) /\
in_app (e_F (x_e segs cx)) 1024 /\ e_F (x_e segs cx) mod 32 = 0 /\
in_app (e_pp (x_e segs cx)) Layout.PP_SIZE.
Proof.
intros [STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc RLO RHI e pos] HP.
unfold hs_pre in HP. cbn [x_STK x_sp0 x_FP x_ly x_S x_W0 x_mem0 x_md0 x_own x_k x_regs x_lyc x_Sc x_W x_memc x_mdc x_RLO x_RHI x_e x_pos] in *.
destruct HP as (HJ & _ & Hsp & _ & _ & HeS & HR32 & HRS & HSTK & Hown & HF & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hpp & _)).
cbn [hi_cid hi_rsz headamp_himg_A] in *.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & HSTK0 & Hceil & Hlo & Hhi & H47 & _).
pose proof alloc_ceiling_value as (Hc1 & _).
assert (Hin3 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ (AR_laws_ok segs B) lyc Sc W memc mdc 4 pos HAR Hin3) as (HF32 & HFapp & _).
destruct (al_blocks _ _ (AR_laws_ok segs B) lyc Sc W memc mdc (e_pp e) Layout.PP_SIZE HAR Hpp) as (_ & _ & _ & Happ & _).
change (fs_frame_bytes 4) with 1024 in HFapp. rewrite <- HF in HFapp, HF32.
replace (req_size Layout.PP_SIZE) with Layout.PP_SIZE in Happ by reflexivity.
assert (HR0 : 0 <= e_R e < 2 ^ 64) by (unfold T_SEG_STK, ASTACK in HSTK; unfold kHighMemBeg; lia).
split; [unfold spZ; rewrite Hsp; unfold w64; apply unsigned_lit_small; lia|].
split; [unfold T_SEG_STK, ASTACK in *; unfold kHighMemBeg; lia|].
split; [lia|].
split; [exact Hin3|]. split; [exact HF|]. split; [exact HFapp|]. split; [exact HF32 | exact Happ].
Qed.

Lemma hs_core_kept : forall cx ly2 S2 W2 regs2 mem2 md2,
hs_pre segs B cx (hi_shA headamp_himg_A) -> hs_core segs B MT cx (hs_E1 segs cx) ly2 S2 W2 regs2 mem2 md2 ->
forall a, ~ hs_wr cx a -> aview segs (w_H W2) mem2 a = aview segs (w_H (x_W segs cx)) (x_memc segs cx) a.
Proof.
intros cx ly2 S2 W2 regs2 mem2 md2 HP HC a Ha.
destruct (hs_pre_geom cx HP) as (Hsp & _).
destruct HC as (_ & _ & _ & _ & _ & _ & HK). unfold hs_wr in Ha.
apply HK; [lia | rewrite Hsp; intros X; apply Ha; right; left; exact X | intros X; apply Ha; right; right; exact X].
Qed.

(* a shadow byte of an application address is never in hs_E1 or the callees' stack *)
Lemma hs_wr_shadow : forall cx x, hs_pre segs B cx (hi_shA headamp_himg_A) -> 0 <= x < kHighMemEnd ->
range_addressable (aview segs (w_H (x_W segs cx)) (x_memc segs cx)) SHADOW_OFF x 1 ->
~ hs_wr cx (shadow_of_addr SHADOW_OFF x).
Proof.
intros cx x HP Hx Hra.
destruct (hs_pre_geom cx HP) as (_ & HRk & _ & _ & _ & HFapp & _ & Happ).
pose proof (hm_shadow_band x Hx) as Hb.
assert (Hfsh : hd_fsh segs (w_H (x_W segs cx)) (x_memc segs cx) (e_F (x_e segs cx)) headamp_A_shA).
{ destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. }
pose proof (hm_ra_not_fsh segs _ _ _ _ x 1 Hra Hfsh hm_sh_P0_big x ltac:(lia)) as Hnf.
change (Z.of_nat (length headamp_A_shA)) with 80 in Hnf.
unfold hs_wr, hs_E1, hd_inw. cbn [hi_w1 headamp_himg_A].
intros [H|[H|[H|H]]].
- unfold kLowMemEnd, kHighMemBeg in Hb. lia.
- unfold kHighMemBeg in *. lia.
- apply Exists_cons in H as [H|H]; [|apply Exists_cons in H as [H|H]; [|apply Exists_cons in H as [H|H]; [|apply Exists_nil in H; destruct H]]];
  cbn [fst snd hd_xv] in H.
  + apply (hm_shadow_not_app x (e_F (x_e segs cx)) 1024 Hx HFapp). lia.
  + apply Hnf. unfold shadow_addr in *. lia.
  + unfold kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
- apply (hm_shadow_not_app x (e_pp (x_e segs cx)) Layout.PP_SIZE Hx Happ). exact H.
Qed.

Lemma hs_in_now : forall cx rest pat ly2 S2 W2 regs2 mem2 md2,
hs_pre segs B cx (hi_shA headamp_himg_A) -> hs_in segs cx rest -> hs_core segs B MT cx (hs_E1 segs cx) ly2 S2 W2 regs2 mem2 md2 ->
hs_fsh_at segs cx W2 mem2 pat -> length pat = 80%nat ->
garr8 segs (mrestrict (w_H W2) mem2) (e_src (x_e segs cx)) (hd_zbytes rest) /\
range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF (e_src (x_e segs cx)) (e_left (x_e segs cx)) /\
(0 < e_left (x_e segs cx) -> shadow_hull_vis (aview segs (w_H W2) mem2) (e_src (x_e segs cx)) (e_left (x_e segs cx))).
Proof.
intros cx rest pat ly2 S2 W2 regs2 mem2 md2 HP HI HC Hfsh2 Hpat.
pose proof (hs_core_kept cx ly2 S2 W2 regs2 mem2 md2 HP HC) as HK.
destruct (hs_pre_geom cx HP) as (_ & HRk & _ & _ & _ & HFapp & _ & Happ).
destruct HI as (Hleft & Hbytes & Hra & Hhull & Hamr & Hsrc0 & Hsrc63 & Hdisj).
set (src := e_src (x_e segs cx)) in *. set (n := e_left (x_e segs cx)) in *.
assert (Hx : forall x, src <= x < src + n -> 0 <= x < kHighMemEnd).
{ intros x Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia. }
split.
- apply (hm_bytes_kept_wr segs (hs_wr cx) _ _ _ _ src rest Hbytes HK).
  intros x Hx'. rewrite <- Hleft in Hx'. fold n in Hx'. destruct (Hdisj x Hx') as (D1 & D2 & D3).
  unfold hs_wr, hs_E1. intros [H|[H|[H|H]]]; [lia | exact (D1 H) | exact (D2 H) | exact (D3 H)].
- split.
  + apply (hm_ra_kept_wr segs (hs_wr cx) _ _ _ _ SHADOW_OFF src n Hra HK).
    intros x Hx'. apply hs_wr_shadow; [exact HP | exact (Hx x Hx') |].
    apply (range_addressable_sub _ _ src n); [exact Hra | lia | lia].
  + intros Hn. apply (hm_hull_kept segs _ _ _ _ src n (Hhull Hn)).
    intros s Hs Hnone.
    destruct (base.decide (hs_wr cx s)) as [Hw|Hw].
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
    unfold hs_wr, hs_E1, hd_inw in Hw. cbn [hi_w1 headamp_himg_A] in Hw.
    destruct Hw as [H|[H|[H|H]]].
    * exfalso. unfold SHADOW_OFF, kHighMemBeg in Hsb. lia.
    * exfalso. unfold kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
    * apply Exists_cons in H as [H|H]; [|apply Exists_cons in H as [H|H]; [|apply Exists_cons in H as [H|H]; [|apply Exists_nil in H; destruct H]]];
      cbn [fst snd hd_xv] in H.
      -- exfalso. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
      -- unfold hs_fsh_at, hd_fsh in Hfsh2. rewrite Hpat in Hfsh2.
         replace s with (shadow_addr (e_F (x_e segs cx)) + (s - shadow_addr (e_F (x_e segs cx)))) by lia.
         rewrite (Hfsh2 (s - shadow_addr (e_F (x_e segs cx))) ltac:(cbn; lia)). discriminate.
      -- exfalso. unfold kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
    * exfalso. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

(* rom_view at a cut: the image lies below the shadow band, outside every block and frame *)
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Lemma hs_rom_now : forall cx ly2 S2 W2 regs2 mem2 md2,
hs_pre segs B cx (hi_shA headamp_himg_A) -> hs_core segs B MT cx (hs_E1 segs cx) ly2 S2 W2 regs2 mem2 md2 -> rom_view segs W2 mem2.
Proof.
intros cx ly2 S2 W2 regs2 mem2 md2 HP HC.
pose proof (hs_core_kept cx ly2 S2 W2 regs2 mem2 md2 HP HC) as HK.
destruct (hs_pre_geom cx HP) as (_ & HRk & _ & Hin3 & HF & HFapp & _ & Happ).
assert (Hrom : rom_view segs (x_W segs cx) (x_memc segs cx)).
{ destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. }
assert (HAR : AR segs B (x_lyc segs cx) (x_Sc segs cx) (x_W segs cx) (x_memc segs cx) (x_mdc segs cx)).
{ destruct HP as (HJ & _). exact (proj1 HJ). }
assert (Hpp : In (e_pp (x_e segs cx), Layout.PP_SIZE) (ablocks B (x_lyc segs cx) (x_Sc segs cx))).
{ destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & H & _)). exact H. }
apply (hm_rom_kept_wr segs (hs_wr cx) (x_W segs cx) W2 (x_memc segs cx) mem2 Hrom HK).
intros a (sg & Hsg & _ & Ha). assert (Himg : in_img segs a) by (exists sg; split; [exact Hsg | exact Ha]).
pose proof (segs_low a Himg) as Hlow.
pose proof (al_client_img _ _ (AR_laws_ok segs B) _ _ _ _ _ a HAR) as Hcl.
unfold hs_wr, hs_E1, hd_inw. cbn [hi_w1 headamp_himg_A].
intros [H|[H|[H|H]]].
- unfold kLowMemEnd in Hlow. lia.
- unfold kLowMemEnd, kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
- apply Exists_cons in H as [H|H]; [|apply Exists_cons in H as [H|H]; [|apply Exists_cons in H as [H|H]; [|apply Exists_nil in H; destruct H]]];
  cbn [fst snd hd_xv] in H.
  + assert (HinF : frame_addr (x_lyc segs cx) 4 (x_pos segs cx) <= a <
      frame_addr (x_lyc segs cx) 4 (x_pos segs cx) + fs_frame_bytes 4)
      by (rewrite <- HF; change (fs_frame_bytes 4) with 1024; lia).
    apply (proj2 (Hcl (or_intror (or_introl (ex_intro _ 4 (ex_intro _ (x_pos segs cx) (conj Hin3 HinF))))))).
    exact Himg.
  + unfold shadow_addr, SHADOW_OFF, kLowMemEnd in *. pose proof (Z.div_pos (e_F (x_e segs cx)) 8). unfold in_app in HFapp. lia.
  + unfold kLowMemEnd, kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
- assert (Hinp : e_pp (x_e segs cx) <= a < e_pp (x_e segs cx) + req_size Layout.PP_SIZE)
    by (change (req_size Layout.PP_SIZE) with Layout.PP_SIZE; lia).
  apply (proj2 (Hcl (or_introl (ex_intro _ (e_pp (x_e segs cx)) (ex_intro _ Layout.PP_SIZE (conj Hpp Hinp)))))).
  exact Himg.
Qed.

End d.
End c.
End b.
