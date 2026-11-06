(* Modified by Theorem Labs, 2026-10: the proof of cmd_strtol of proofs/plugin-hostd/fuzz_command/lib/A/Rt/RtLStrtol.v
   and of art_post_clean of lib/A/Rt/RtBzAdaptP.v at origin/ossv/recipes 2d2ff01bb6f (ported to this unit as
   lib/A/Rt/RtLStrtol.v and RtBzAdaptP.v), re-run for the hole form of the strtol contract, lib/A/HPgHole.v
   hd_astrtol_hole; the frame step is HPgHole.v's ARH_frame argument (al_frame over the unpoisoned memories). *)
(* Modified by Theorem Labs, 2026-10: derived from lib/A/Rt/RtLStrtolH.v of this library by derive_y.py b7b132fb12a7: module paths lib.A -> lib.AU, the image module Asan -> AsanUbsan and Img0 -> Img0U, addresses moved from fuzz_headamp's asan image to its asan-ubsan image. The Modified-by lines above describe how lib/A/Rt/RtLStrtolH.v was made and quote that file's asan-image values; the code below carries the asan-ubsan values. *)
(* The strtol interceptor of fuzz_headamp.asan-ubsan (trampoline 0x41ca8) inside a frame hole: HPgHole.v's
   hd_astrtol_hole at 0x41ca8, and astrtol_realizes at 0x41ca8 with the frame law closed (hd_strtol).

   The parse (image B 0x849ac) calls strtol at 0x84ddc while eight shadow bytes of its own real-stack frame, the
   hole hU fr pat = the shadow of [fr, fr + 64) with fr = sp' + 0x40, read f1 f1 f1 f1 00 f3 f3 f3. The kit's AR
   asks every shadow byte of the stack range to read 0, so AR holds of the memory read with the hole as 0,
   unpoison (hU fr pat) mem, not of mem; hd_astrtol_hole takes ecall_pre of that memory and states every other
   premise over mem.

   The walk (A/Bz/A/I_strtolw.v istrtol_spec) runs on the real memory mem, as in cmd_strtol. What it reads of the
   shadow (I_qck.v chk_ok = acc /\ qc_words /\ rng_ok, at I_strtolfix.v sfixE_spec):
   - the end pointer's cell e (8 bytes, e mod 8 = 0): its own shadow byte shad(e) = e / 8 + 0x7fff8000, which must
     read 0 (acc; awrite_ok's range_addressable gives it, and at the parse's call it is the hole's byte 4, 00), and
     the aligned 8-byte shadow word al8(shad(e)) (qc_words), read with its value free: at the parse's call that word
     is the whole hole, f1 f1 f1 f1 00 f3 f3 f3;
   - the string x: the shadow byte of every byte of [x, x + nn), 1 <= nn <= len + 1 (acc: addressable), and the
     aligned shadow words al8(shad(x)) and al8(shad(x + nn - 1)) (qc_words), value free.
   No other shadow byte of the caller's frame is read.

   What changes from cmd_strtol: the facts cmd_strtol reads off AR (the record's constant cells, the read-only
   bytes the runtime owns, the stack window) are read off AR of unpoison (hU fr pat) mem and carried to mem, where
   they sit at addresses outside the hole: the image's cells and read-only bytes are below kHighShadowBeg, the
   stack window at or above ly_stk_lo (HPgHole.v hole_band). The post's AR is AR of unpoison (hU fr pat) mem' with
   the pattern kept (hpat): the walk writes its stack window, the end pointer's cell (amem_range e 16: low or high
   application memory) and the errno cell (in the image), none of them a hole byte. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YK11 YK0s YK0i YK15 YK0j YK18 YP09 YK04 YK14 YK1b YP03 YA0i YA0n YA0o YG00 YG0a YG01 YG0f YG0v YG0n YG0d
YI00 YI04 YK06 YM05 YI16 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import YB1v YF0m YF0x.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import RtDefs RtNumber.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.Rt Require Import
RtBzHBase RtBzLift RtBzPre RtBzClean RtBzAdapt RtBzAdaptP RtLStrtol.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require YE2y.
Require OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt.FMupoison.
Require OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.HPgHole.
Require OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.Bz.A.D_kit.
Require OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.__intscan_c.
Require OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.Prog.__intscan_c.
Require OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.Bz.A.I_strtolw.
Require OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.Bz.A.I_strtolfix.
Require OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.Bz.A.R_isPoisoned.
Require OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.Prog.strtol_wrap_sb.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module FU := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt.FMupoison.
Module HH := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.HPgHole.
Module BzD := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.Bz.A.D_kit.
Module HLPIS := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.__intscan_c.
Module HAPIS := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.Prog.__intscan_c.
Module HSW := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.Bz.A.I_strtolw.
Module HRIP := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.Bz.A.R_isPoisoned.
Module HSBP := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.Prog.strtol_wrap_sb.

(* ---- the hole's place ---- *)
Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.

(* every hole byte is a high-shadow byte (HPgHole.v hole_band), so nothing below kHighShadowBeg and nothing at or
   above kHighShadowEnd (= kHighMemBeg, the stack's floor) is one *)
Lemma not_hole : forall ly fr pat a, layout_ok ly -> HH.hstack_ok ly fr pat ->
  a < kHighShadowBeg \/ kHighShadowEnd <= a -> FU.in_ush (HH.hU fr pat) a = false.
Proof.
  intros ly fr pat a LO OK Ha. apply HH.in_hU_false. intros Hs.
  pose proof (HH.hole_band ly fr pat LO OK a Hs) as (Hb & _). lia.
Qed.

Lemma tfib_segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd.
Proof.
  assert (E : forallb (fun sg => Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <=? kLowMemEnd) tfibsegs = true)
    by (vm_compute; reflexivity).
  intros a (sg & Hin & Hr). rewrite forallb_forall in E. specialize (E sg Hin). apply Z.leb_le in E.
  pose proof (N2Z.is_nonneg (seg_base sg)). lia.
Qed.

(* a read-only byte of the image reads the same with the hole as 0 *)
Lemma rom_unp : forall ly fr pat H mem a, layout_ok ly -> HH.hstack_ok ly fr pat -> in_rom tfibsegs a ->
  aview tfibsegs H (FU.unpoison (HH.hU fr pat) mem) a = aview tfibsegs H mem a.
Proof.
  intros ly fr pat H mem a LO OK Hrom. apply FU.aview_unpoison_out.
  assert (Hi : in_img tfibsegs a) by (destruct Hrom as (sg & Hs & _ & Ha); exists sg; split; [exact Hs | exact Ha]).
  pose proof (tfib_segs_low a Hi) as La.
  rewrite unsigned_lit_small by (unfold kLowMemEnd in La; lia).
  apply (not_hole ly fr pat a LO OK). left. unfold kLowMemEnd, kHighShadowBeg in *. lia.
Qed.

End i.

(* ---- the post of a cleaned walk inside the hole (RtBzAdaptP.v art_post_clean, with HPgHole.v ARH_frame) ---- *)
Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

Theorem art_post_cleanH : forall (stk K : Z) ly S (W : world tfibsegs) regs mem md (fr : Z) (pat : list Z)
  (E : Z -> Prop) (Q : bvmap 5 word -> (word -> option byte) -> Prop) msc ms' model',
  HH.ecall_preH tfibsegs B stk ly S fr pat W regs mem md -> 0 <= K <= stk ->
  hclean Dc msc ->
  R6.ms_eqv (unrestrict Dc (mrestrict (w_H W) mem) msc) ms' ->
  same_but_materialized md model' ->
  ms_pc_val msc = LMS.ret_pc (getr regs 1) -> ms_fregs msc = fp_regs -> ms_svc_pending msc = None ->
  ms_resv msc = None -> ms_fcsr msc = fp_csr -> ms_rom msc = seg_rom tfibsegs ->
  (forall r, acallee_saved r -> getr (ms_regs msc) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  (forall x : word, ~ (spZ regs - K <= bv_unsigned x < spZ regs) -> ~ E (bv_unsigned x) ->
     ms_mem msc x = clean (mrestrict (w_H W) mem) x) ->
  (forall a, spZ regs - K <= a < spZ regs -> ms_mem msc (Z_to_bv 64 a) <> None) ->
  YK1b.mem_grows (clean (mrestrict (w_H W) mem)) (ms_mem msc) ->
  (forall a, E a -> ~ aowned B ly S a /\ 0 <= a < 2 ^ 64 /\ Dc (Z_to_bv 64 a) = false /\
             w_H W (Z_to_bv 64 a) = false) ->
  (* E holds no hole byte *)
  (forall a, E a -> FU.in_ush (HH.hU fr pat) a = false) ->
  (forall regs' mem',
     (forall r : bv 5, getr regs' r = getr (ms_regs msc) r) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - stk <= a < spZ regs) -> ~ E a ->
        aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
     (forall a, E a ->
        aview tfibsegs (w_H W) mem' a =
        option_map (fun b : byte => bv_unsigned b) (BM.mrd BI.asegs (ms_mem msc) (BM.wa a))) ->
     Q regs' mem') ->
  W = W /\ exists regs' mem' md',
    mkCfg (unrestrict (w_H W) mem ms') model' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
    AR tfibsegs B ly S W (FU.unpoison (HH.hU fr pat) mem') md' /\ HH.hpat tfibsegs W mem' fr pat /\
    aregs_preserved regs regs' /\ same_but_materialized md md' /\
    Q regs' mem' /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - stk <= a < spZ regs) -> ~ E a ->
       aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
    (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
    (forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W) mem' a).
Proof.
  intros stk K ly S W regs mem md fr pat E Q msc ms' model' HPRE HK Hcl Heqv Hsbm
    P0 F0 S0 R0 C0 RO0 KEEP MOUT MIN GROW HE HEH HQ.
  destruct HPRE as (HEP & HOK & HPAT & Hslo & HpresS).
  pose proof HEP as (HAR & Hra & _ & Hlo & Hshi & _ & _ & _).
  pose proof (am_layout _ _ _ _ (proj1 HAR)) as LO.
  set (U := HH.hU fr pat) in *.
  set (H := w_H W) in *.
  set (m0 := mrestrict H mem) in *.
  set (ms0 := unrestrict Dc m0 msc) in *.
  pose proof Heqv as (_ & _ & _ & _ & _ & _ & Emem & _).
  set (mem' := munrestrict H mem (ms_mem ms')) in *.
  assert (MS0 : forall x : word, ms_mem ms0 x = if Dc x then m0 x else ms_mem msc x).
  { intros x. unfold ms0. rewrite unrestrict_mem. reflexivity. }
  assert (MEM' : forall x : word, mem' x = if H x then mem x else ms_mem ms0 x).
  { intros x. unfold mem'. rewrite <- Emem. reflexivity. }
  assert (OUT0 : forall x : word, ~ (spZ regs - K <= bv_unsigned x < spZ regs) -> ~ E (bv_unsigned x) ->
            ms_mem ms0 x = m0 x).
  { intros x Hx HEx. rewrite MS0. destruct (Dc x) eqn:ED; [reflexivity|].
    rewrite (MOUT x Hx HEx). unfold clean, mrestrict. rewrite ED. reflexivity. }
  assert (OUTM : forall x : word, ~ (spZ regs - K <= bv_unsigned x < spZ regs) -> ~ E (bv_unsigned x) ->
            mem' x = mem x).
  { intros x Hx HEx. rewrite MEM'. destruct (H x) eqn:EH; [reflexivity|].
    rewrite (OUT0 x Hx HEx). unfold m0, mrestrict. rewrite EH. reflexivity. }
  assert (GR0 : forall x : word, m0 x <> None -> ms_mem ms0 x <> None).
  { intros x Hx. rewrite MS0. destruct (Dc x) eqn:ED; [exact Hx|].
    apply GROW. unfold clean, mrestrict. rewrite ED. exact Hx. }
  assert (VIS : forall a, aview tfibsegs H mem a <> None -> aview tfibsegs H mem' a <> None).
  { intros a Hv. rewrite (RtBzLift.aview_mod H mem' a). rewrite (RtBzLift.aview_mod H mem a) in Hv.
    pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Hr. set (a' := a mod 2 ^ 64) in *.
    unfold aview, mbyte, mrestrict in Hv |- *.
    destruct (H (Z_to_bv 64 a')) eqn:EH.
    - exact Hv.
    - destruct (mem (Z_to_bv 64 a')) as [b|] eqn:EM.
      + assert (HN : ms_mem ms0 (Z_to_bv 64 a') <> None)
          by (apply GR0; unfold m0, mrestrict; rewrite EH, EM; discriminate).
        rewrite (MEM' (Z_to_bv 64 a')), EH.
        destruct (ms_mem ms0 (Z_to_bv 64 a')) as [c|] eqn:EC; [cbn; discriminate|].
        exfalso. exact (HN eq_refl).
      + rewrite (MEM' (Z_to_bv 64 a')), EH.
        destruct (ms_mem ms0 (Z_to_bv 64 a')) as [c|] eqn:EC; [cbn; discriminate|].
        cbn in Hv |- *. exact Hv. }
  assert (PRS : forall a, apresent H mem a -> apresent H mem' a).
  { intros a [Hh [b Hb]]. split; [exact Hh|].
    rewrite (MEM' (Z_to_bv 64 a)), Hh.
    assert (HN : ms_mem ms0 (Z_to_bv 64 a) <> None)
      by (apply GR0; unfold m0, mrestrict; rewrite Hh, Hb; discriminate).
    destruct (ms_mem ms0 (Z_to_bv 64 a)) as [c|] eqn:EC; [exists c; reflexivity|].
    exfalso. exact (HN eq_refl). }
  assert (AVOUT : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - stk <= a < spZ regs) -> ~ E a ->
            aview tfibsegs H mem' a = aview tfibsegs H mem a).
  { intros a Ha Hs HEa. apply RtBzLift.aview_same.
    apply OUTM; rewrite unsigned_lit_small by lia; [lia | exact HEa]. }
  assert (AVOWN : forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a ->
            aview tfibsegs H mem' a = aview tfibsegs H mem a).
  { intros a Ha Hown. apply AVOUT; [exact Ha | | intros HEa; exact (proj1 (HE a HEa) Hown)].
    intros Hsc.
    exact (al_stack _ _ LAWS ly S W (FU.unpoison U mem) md a HAR ltac:(lia) Hown). }
  assert (AVE : forall a, E a ->
            aview tfibsegs H mem' a =
            option_map (fun b : byte => bv_unsigned b) (BM.mrd BI.asegs (ms_mem msc) (BM.wa a))) .
  { intros a HEa. destruct (HE a HEa) as (_ & Ha & EDc & EHh).
    unfold aview. rewrite <- RtBzPre.mrd_mbyte. f_equal.
    unfold BM.mrd, BM.wa, mrestrict. rewrite EHh.
    rewrite (MEM' (Z_to_bv 64 a)), EHh, (MS0 (Z_to_bv 64 a)), EDc. reflexivity. }
  (* the hole keeps its pattern: no hole byte is in the window or in E *)
  assert (HPAT' : HH.hpat tfibsegs W mem' fr pat).
  { intros i Hi. pose proof (HH.hole_band ly fr pat LO HOK (shadow_addr fr + i) ltac:(lia)) as (_ & Hst & _ & _ & Hr).
    assert (Hn : ~ E (shadow_addr fr + i)).
    { intros HEa. pose proof (HEH _ HEa) as Hn. unfold U in Hn.
      rewrite (proj2 (HH.in_hU fr pat (shadow_addr fr + i)) ltac:(lia)) in Hn. discriminate Hn. }
    exact (eq_trans (AVOUT (shadow_addr fr + i) Hr ltac:(lia) Hn) (HPAT i Hi)). }
  (* AR of the unpoisoned memory survives the call *)
  destruct (same_but_materialized_frame md model' Hsbm)
    as (_ & E1 & E2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E3).
  assert (HAR' : AR tfibsegs B ly S W (FU.unpoison U mem') model').
  { apply (al_frame _ _ LAWS ly S W (FU.unpoison U mem) md (FU.unpoison U mem') model' HAR);
      [| |exact E1|exact E2|exact E3|].
    - intros a Ha Hown. destruct (FU.in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:Ei.
      + apply FU.aview_unpoison_in. exact Ei.
      + rewrite !FU.aview_unpoison_out by exact Ei. exact (AVOWN a Ha Hown).
    - intros a Hv. destruct (FU.in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:Ei.
      + rewrite (FU.aview_unpoison_in tfibsegs _ U mem' mem a Ei). exact Hv.
      + rewrite FU.aview_unpoison_out in Hv |- * by exact Ei. exact (VIS a Hv).
    - intros a _ Hh. unfold FU.unpoison. destruct (FU.in_ush U (bv_unsigned (w64 a))); [reflexivity|].
      rewrite (MEM' (w64 a)). replace (H (w64 a)) with true by (symmetry; exact Hh). reflexivity. }
  split; [reflexivity|].
  exists (ms_regs ms'), mem', model'.
  split.
  { unfold cfg_at. f_equal.
    exact (RtBzLift.unrestrict_ret regs H mem ms0 ms' Heqv Hra P0 F0 S0 R0 C0 RO0). }
  split; [exact HAR'|].
  split; [exact HPAT'|].
  split; [intros r Hr; rewrite (RtBzLift.ms_eqv_getr ms0 ms' _ Heqv); exact (KEEP r Hr)|].
  split; [exact Hsbm|].
  split; [exact (HQ (ms_regs ms') mem'
                   (fun r => RtBzLift.ms_eqv_getr ms0 ms' r Heqv) AVOUT AVE)|].
  split; [exact AVOUT|].
  split; [exact PRS|].
  intros a Ha. apply PRS. exact (HpresS a Ha).
Qed.

End p.

(* ---- the contracts ---- *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis TB : TfibSyms B.

(* astrtol_realizes at 0x41ca8 with the frame law (cmd_strtol's Section hypothesis LAWS) closed by the kit *)
Theorem hd_strtol : astrtol_realizes tfibsegs B 0x41ca8 0x9d478 0x5f8210.
Proof. exact (cmd_strtol B (AR_laws_ok tfibsegs B) TB). Qed.

(* the hole form: HPgHole.v hd_astrtol_hole at 0x41ca8 *)
Theorem hd_strtol_hole : HH.hd_astrtol_hole tfibsegs B 0x41ca8 0x9d478 0x5f8210.
Proof.
  unfold HH.hd_astrtol_hole.
  intros ly S W regs mem md x e str ev fr pat HG HPREH G10 G11 G12 Hx0 He0 SX HXL RDX AMX _ WR AME SEPXE SEPEERR
    EAL EOUT SEPXERR RDE HROM.
  pose proof HPREH as (HEPu & HOK & HPAT & HSLO & HPRS).
  pose proof HEPu as (HARu & _ & _ & Hlo & Hshi & _ & _ & G4).
  pose proof HARu as (_ & HLED & _).
  pose proof (am_layout _ _ _ _ (proj1 HARu)) as LO.
  pose proof (lo_top _ LO) as (_ & _ & _ & T4 & _ & _ & T7).
  set (mu := FU.unpoison (HH.hU fr pat) mem) in *.
  assert (NH : forall a, a < kHighShadowBeg \/ kHighShadowEnd <= a -> FU.in_ush (HH.hU fr pat) a = false)
    by (intros a Ha; exact (not_hole ly fr pat a LO HOK Ha)).
  assert (EX : astr_len str = Z.of_nat (length str)) by reflexivity.
  pose proof (amem_top x _ AMX) as AMX'.
  pose proof (amem_top e _ AME) as AME'.
  pose proof (end_le str) as HEND.
  pose proof RDX as (_ & _ & HXN & _).
  pose proof WR as (_ & _ & _ & HWB & _).
  rewrite (ts_errno B TB) in SEPEERR, SEPXERR, RDE.
  (* the stack window: at or above the stack's floor, so outside the hole *)
  assert (HPREu : ecall_pre_stk tfibsegs B (3 * ESTACK) ly S W regs mu md).
  { split; [exact HEPu|]. split; [exact HSLO|]. intros a Ha. unfold ascratch_stk in Ha.
    destruct (HPRS a Ha) as (Hh & b & Hb). split; [exact Hh|]. exists b. unfold mu.
    rewrite FU.unpoison_out; [exact Hb|].
    rewrite unsigned_lit_small by (unfold kHighMemBeg, kHighMemEnd in *; lia).
    apply NH. right. unfold kHighShadowEnd, kHighMemBeg in *. lia. }
  (* 0. the end pointer's cell lies outside the image *)
  destruct (img_lo_hi ly S md HLED) as (IL & IH).
  assert (EOUT' : e + 8 <= 0x10000 \/ 0x5fa000 <= e).
  { destruct (Z_lt_le_dec e 0x10000) as [L1|L1].
    - destruct (Z_le_gt_dec (e + 8) 0x10000) as [L2|L2]; [left; exact L2|].
      exfalso. apply (EOUT 0x10000 ltac:(lia)). unfold in_zr. lia.
    - destruct (Z_lt_le_dec e 0x5fa000) as [L2|L2]; [|right; exact L2].
      exfalso. apply (EOUT e ltac:(lia)). unfold in_zr. lia. }
  assert (NIMG : forall a, e <= a < e + 8 -> ~ in_img tfibsegs a)
    by (intros a Ha; exact (not_img_of_out ly S md a HLED (EOUT a Ha))).
  assert (DCE : forall a, e <= a < e + 8 -> RtBzClean.Dc (BM.wa a) = false).
  { intros a Ha. apply RtBzClean.Dc_false; [exact (ro_off a ltac:(lia) (NIMG a Ha))|].
    rewrite BM.wa_unsigned by lia. unfold BM.UTOP. lia. }
  assert (RW0 : exists v0, rdword (aview tfibsegs (w_H W) mem) e = Some v0).
  { apply rdword_ex. intros k Hk.
    destruct (byte_of_writable_off (mrestrict (w_H W) mem) (e + k) ltac:(lia) (NIMG (e + k) ltac:(lia))
                (proj1 (HWB (e + k) ltac:(lia)))) as (b & Hb).
    exists (bv_unsigned b). exact (view_of_store (w_H W) mem (e + k) b Hb). }
  destruct RW0 as (v0 & RW0).
  (* 1. the read-only views: the owned half from AR of mu, carried to mem (no read-only byte is a hole byte) *)
  pose proof (RtBzAdapt.rom_viewO_of_ARm B TB ly S W mu (proj1 HARu)) as HOu.
  assert (HO : rom_viewO tfibsegs B W mem).
  { intros a Hrom Hown. rewrite <- (rom_unp ly fr pat (w_H W) mem a LO HOK Hrom). exact (HOu a Hrom Hown). }
  pose proof (RtBzAdapt.romN_of_rt B W mem HROM) as HN.
  pose proof (RtBzClean.rom_eq_of_views B W mem TB HN HO) as RE.
  assert (HROMu : rt_rom_view tfibsegs B W mu).
  { intros a H1 H2 H3. unfold mu. rewrite (rom_unp ly fr pat (w_H W) mem a LO HOK H1). exact (HROM a H1 H2 H3). }
  pose proof (RtBzAdapt.rom_eq_of_rt B TB ly S W mu md HARu HROMu) as REu.
  pose proof (mem_inv_clean (mrestrict (w_H W) mem)) as MI.
  assert (ECELL : BS.rw_cells BI.asegs (clean (mrestrict (w_H W) mem)) e [BC.C8 (Z_to_bv 64 v0)]).
  { apply (ecell_clean W mem e v0 RE ltac:(lia) ltac:(lia)); [|exact RW0].
    intros a Ha. split; [exact (proj1 (HWB a Ha)) | exact (DCE a Ha)]. }
  pose proof (errno_cell_clean (w_H W) mem ev RE RDE) as ERRC.
  (* the cleaned stores of mu and mem agree off the hole *)
  assert (LA : forall P : Z -> Prop, (forall a, P a -> a < kHighShadowBeg \/ kHighShadowEnd <= a) ->
            BzD.agree_on P (clean (mrestrict (w_H W) mu)) (clean (mrestrict (w_H W) mem))).
  { intros P HP a Ha. unfold clean, mrestrict. destruct (Dc a); [reflexivity|].
    destruct (w_H W a); [reflexivity|].
    unfold mu. rewrite FU.unpoison_out; [reflexivity|]. apply NH. exact (HP _ Ha). }
  (* 2. the stack window *)
  destruct (RtBzAdapt.stk_of_stk_pre B (3 * ESTACK) ly S W regs mu md HPREu ltac:(unfold ESTACK; lia))
    as (ST0u & HC0 & HCs & Hsp47).
  assert (ST0 : BF.stk BI.asegs (mrestrict (w_H W) mem) (spZ regs - 3 * ESTACK) (spZ regs)).
  { apply (BzD.stk_agree_nw BI.asegs _ _ _ _ ST0u). intros a Ha. unfold mrestrict.
    destruct (w_H W a); [reflexivity|].
    unfold mu. rewrite FU.unpoison_out; [reflexivity|]. apply NH. right.
    unfold kHighShadowEnd, kHighMemBeg in *. lia. }
  assert (ST : BF.stk BI.asegs (clean (mrestrict (w_H W) mem)) (spZ regs - 3 * ESTACK) (spZ regs)).
  { apply (stk_clean (mrestrict (w_H W) mem) (spZ regs - 3 * ESTACK) (spZ regs));
      [unfold TFIB_IMG_END; lia | unfold BM.UTOP; lia | exact ST0]. }
  (* 3. the string *)
  pose proof (RtBzAdapt.bz_str_bytes W mem x str SX ltac:(lia) ltac:(lia)) as BYXm.
  assert (BYX : BM.bytes_at BI.asegs (clean (mrestrict (w_H W) mem)) x (str ++ [Z_to_bv 8 0])).
  { apply (bytes_at_clean _ x _ RE); [rewrite length_app; cbn [length]; unfold BM.UTOP; lia | exact BYXm]. }
  (* 4. the stack-protector pair musl's strtol reads *)
  destruct (RtBzAdapt.bz_guard_bytes W mem 0x9d478 0x5f8210 HG ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as (GOTm & can & CANm).
  assert (GOT : BM.bytes_at BI.asegs (clean (mrestrict (w_H W) mem)) 0x9d478 (BM.le8 (Z_to_bv 64 0x5f8210))).
  { apply (bytes_at_clean _ _ _ RE); [rewrite BM.length_le8; unfold BM.UTOP; lia | exact GOTm]. }
  assert (CAN : BM.bytes_at BI.asegs (clean (mrestrict (w_H W) mem)) 0x5f8210 (BM.le8 can)).
  { apply (bytes_at_clean _ _ _ RE); [rewrite BM.length_le8; unfold BM.UTOP; lia | exact CANm]. }
  (* 5. the range checks: every prefix of the string with its NUL, and the end pointer's cell, on mem *)
  assert (CKX : forall nn, 1 <= nn <= Z.of_nat (length str) + 1 ->
                  BQ.chk_ok (clean (mrestrict (w_H W) mem)) x nn).
  { intros nn Hnn. apply (chk_ok_clean _ x _ RE); [lia | lia |].
    exact (RtBzAdapt.chk_of_read (3 * ESTACK) W regs mem x (astr_len str + 1) nn (astr_len str)
             RDX AMX ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (CKE : BQ.chk_ok (clean (mrestrict (w_H W) mem)) e 8).
  { apply (chk_ok_clean _ e _ RE); [lia | lia |].
    exact (RtBzAdapt.chk_of_write B (3 * ESTACK) ly S W regs mem e 8 8 8 WR AME ltac:(lia) ltac:(lia) ltac:(lia)). }
  (* 6. the string and the end pointer's cell lie outside the callee's window *)
  pose proof (RtBzAdapt.sep_of_read (3 * ESTACK) W regs mem x (astr_len str + 1)
                ltac:(unfold ESTACK; lia) ltac:(lia) RDX) as SEPX.
  pose proof (RtBzAdapt.sep_of_write B (3 * ESTACK) ly S W regs mem e 8
                ltac:(unfold ESTACK; lia) ltac:(lia) WR) as SEPE.
  (* 7. the fixed cells: read off AR of mu, carried to mem (image addresses, below kHighShadowBeg) *)
  pose proof (m2s_of_ARm_clean B TB ly S (w_H W) mu REu (proj1 HARu)) as M2Su.
  pose proof (inited_clean B TB ly S (w_H W) mu REu (proj1 HARu)) as AIu.
  pose proof (icells_sx_clean B TB ly S (w_H W) mu REu (proj1 HARu)) as ICXu.
  destruct (slots_clean B TB ly S (w_H W) mu REu (proj1 HARu)) as (RSLOTu & AFSLOTu & AF29u).
  assert (M2S : BR.m2s_cells (clean (mrestrict (w_H W) mem))).
  { destruct M2Su as (C1 & C2 & C3). split; [|split];
      [ apply (BzD.rw_cells_agree_nw BI.asegs _ _ _ _ C1)
      | apply (BzD.rw_cells_agree_nw BI.asegs _ _ _ _ C2)
      | apply (BzD.rw_cells_agree_nw BI.asegs _ _ _ _ C3) ];
      apply LA; intros a Ha; left; simpl in Ha; clear - Ha; unfold kHighShadowBeg; lia. }
  assert (AI : BS.rw_cells BI.asegs (clean (mrestrict (w_H W) mem)) 0xa5f18 [BC.C1 (Z_to_bv 8 1)]).
  { apply (BzD.rw_cells_agree_nw BI.asegs _ _ _ _ AIu).
    apply LA; intros a Ha; left; simpl in Ha; clear - Ha; unfold kHighShadowBeg; lia. }
  assert (ICX : SFX.icells_sx (clean (mrestrict (w_H W) mem))).
  { unfold SFX.icells_sx in ICXu |- *. destruct ICXu as (I1 & I2). split;
      [ apply (BzD.ro_cells_agree BI.asegs _ _ _ _ I1)
      | apply (BzD.ro_cells_agree BI.asegs _ _ _ _ I2) ];
      apply LA; intros a Ha; left; simpl in Ha; clear - Ha; unfold kHighShadowBeg; lia. }
  assert (RSLOT : BM.bytes_at BI.asegs (clean (mrestrict (w_H W) mem)) 0x9e630 (BM.le8 (Z_to_bv 64 0x95770))).
  { apply (BzD.bytes_at_agree BI.asegs _ _ _ _ RSLOTu).
    apply LA; intros a Ha; left; rewrite BM.length_le8 in Ha; clear - Ha; unfold kHighShadowBeg; lia. }
  assert (AFSLOT : BM.bytes_at BI.asegs (clean (mrestrict (w_H W) mem)) 0x9c7e8 (BM.le8 (Z_to_bv 64 0xa2a38))).
  { apply (BzD.bytes_at_agree BI.asegs _ _ _ _ AFSLOTu).
    apply LA; intros a Ha; left; rewrite BM.length_le8 in Ha; clear - Ha; unfold kHighShadowBeg; lia. }
  assert (AF29 : BM.bytes_at BI.asegs (clean (mrestrict (w_H W) mem)) 0xa2a55 [Z_to_bv 8 1]).
  { apply (BzD.bytes_at_agree BI.asegs _ _ _ _ AF29u).
    apply LA; intros a Ha; left; simpl in Ha; clear - Ha; unfold kHighShadowBeg; lia. }
  (* 8. the registers the walk names *)
  assert (G4' : reg_get regs 4 = Z_to_bv 64 TFIB_TP) by (rewrite <- (ts_tp B TB); exact G4).
  assert (ETP : bv_unsigned (reg_get regs 4) = TFIB_TP)
    by (rewrite G4'; apply unsigned_lit_small; unfold TFIB_TP; lia).
  assert (ESP : bv_unsigned (reg_get regs 2) = spZ regs) by reflexivity.
  assert (R10 : reg_get regs 10 = Z_to_bv 64 x) by exact G10.
  assert (R11 : reg_get regs 11 = Z_to_bv 64 e) by exact G11.
  assert (R12 : reg_get regs 12 = Z_to_bv 64 10) by exact G12.
  set (lo := spZ regs - 3 * ESTACK) in *.
  assert (Elo : lo = spZ regs - 12288) by (unfold lo, ESTACK; lia).
  assert (KH : BR.kHighShadowEnd < lo) by (unfold BR.kHighShadowEnd; lia).
  (* 9. the run, on the real memory *)
  eapply (bz_run_clean B TB W 0x41ca8 regs mem md _ _ HN HO).
  - eapply RtBzAdaptP.evt_grows. apply bz_canon. rewrite R10, R11, R12.
    apply HSW.istrtol_spec with (A := x) (Ep := e) (str := str)
      (fv := fun s => Z_to_bv 64 (HAPIS.s10_val s)) (fe := HAPIS.s10_end) (fr := fun s w => HAPIS.s10_errno s w)
      (ev := Z_to_bv 64 ev) (can := can) (e0 := Z_to_bv 64 v0) (lo := lo).
    + exact HRIP.rip_proof.
    + exact HSBP.sb_proof.
    + exact BYX.
    + lia.
    + lia.
    + lia.
    + exact EAL.
    + lia.
    + exact ECELL.
    + exact CKE.
    + rewrite ETP. exact ERRC.
    + exact GOT.
    + exact CAN.
    + rewrite ESP. exact ST.
    + rewrite ESP. unfold HSW.ISTRTOL_DEPTH. lia.
    + exact KH.
    + rewrite ESP. exact Hsp47.
    + lia.
    + exact CKX.
    + rewrite ESP. destruct SEPX; lia.
    + rewrite ESP. destruct SEPE; lia.
    + rewrite ETP, ESP. left. unfold TFIB_TP. lia.
    + rewrite ETP. unfold TFIB_TP, TFIB_ERRNO in *. lia.
    + rewrite ESP. left. unfold HSW.STRTOL_SSP_GOT. lia.
    + rewrite ESP. left. unfold HSW.STRTOL_SSP_GUARD. lia.
    + rewrite ETP. right. unfold HSW.STRTOL_SSP_GUARD, TFIB_TP. lia.
    + unfold HSW.STRTOL_SSP_GUARD. destruct EOUT'; lia.
    + lia.
    + destruct EOUT'; lia.
    + exact M2S.
    + exact ICX.
    + exact AI.
    + exact MI.
    + exact RSLOT.
    + exact AFSLOT.
    + exact AF29.
    + exact HEND.
    + rewrite ETP. left. unfold TFIB_TP. lia.
    + rewrite ETP. right. unfold TFIB_TP. lia.
    + rewrite ETP. unfold TFIB_TP, TFIB_ERRNO in *. lia.
  - intros msc ms' model' (HQ & GROW) Hcl Heqv Hsbm _.
    unfold HSW.istrtol_post in HQ.
    destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Emsc & MU & WM & MI'
                    & ST' & CE & CR).
    cbv beta in CE, CR.
    rewrite ETP in MU, CR. rewrite ESP in MU, ST'.
    unfold HSW.ISTRTOL_DEPTH in MU.
    cbv beta.
    apply (art_post_cleanH B (3 * ESTACK) 2272 ly S W regs mem md fr pat
             (fun a => (e <= a < e + 8) \/ (as_errno B <= a < as_errno B + 4))
             (fun regs' mem' => getr regs' 10 = w64 (HLPIS.s10_val str) /\
                rdword (aview tfibsegs (w_H W) mem') e = Some (x + HLPIS.s10_end str) /\
                rd32 (aview tfibsegs (w_H W) mem') (as_errno B) (bv_unsigned (HLPIS.s10_errno str (Z_to_bv 64 ev))))
             msc ms' model' HPREH ltac:(unfold ESTACK; lia) Hcl Heqv Hsbm).
    all: subst msc.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + keep_regs.
    + (* outside the window and E the walk kept the cleaned store *)
      intros y Hy HEy. apply MU. cbn [BF.outside].
      split; [exact Hy|]. split; [intros Hc; apply HEy; cbv beta; left; exact Hc|].
      split; [|exact I]. intros Hc. apply HEy. cbv beta. right. rewrite (ts_errno B TB).
      unfold TFIB_ERRNO, TFIB_TP in Hc |- *. lia.
    + exact (win_in m' (spZ regs) 2272 lo ST' ltac:(lia) ltac:(unfold TFIB_IMG_END; lia)).
    + exact GROW.
    + (* E: the end pointer's cell and the errno cell *)
      intros a [Ha|Ha].
      * destruct (HWB a Ha) as (HWa & HNo & _).
        split; [exact HNo|]. split; [lia|]. split; [exact (DCE a Ha)|].
        exact (RtBzAdapt.wH_false_of_writable W mem a HWa).
      * rewrite (ts_errno B TB) in Ha.
        split; [exact (errno_unowned B (AR_laws_ok tfibsegs B) TB ly S W mu md a HARu Ha)|].
        split; [unfold TFIB_ERRNO in Ha; lia|].
        split; [exact (errno_dc a Ha) | exact (errno_wh W a Ha)].
    + (* E holds no hole byte: the end pointer's cell is application memory (amem_range), errno is in the image *)
      intros a [Ha|Ha]; apply NH.
      * clear - Ha AME. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, kHighShadowBeg, kHighShadowEnd in *. lia.
      * rewrite (ts_errno B TB) in Ha. left. clear - Ha. unfold TFIB_ERRNO, kHighShadowBeg in *. lia.
    + (* the answer *)
      intros regs' mem' HR _ HE'. split; [|split].
      * rewrite (HR _). transitivity (Z_to_bv 64 (HAPIS.s10_val str)); [reflexivity|].
        unfold w64. rewrite s10_val_same. reflexivity.
      * apply (rdword_of_E (w_H W) mem' m' e (x + HLPIS.s10_end str)).
        -- lia.
        -- destruct CE as ((_ & BYE') & _). cbn [BC.cells_bytes BC.cbytes] in BYE'. rewrite app_nil_r in BYE'.
           exact BYE'.
        -- intros k Hk. apply HE'. cbv beta. left. lia.
      * rewrite (ts_errno B TB).
        apply (rd32_of_E (w_H W) mem' m' TFIB_ERRNO (HLPIS.s10_errno str (Z_to_bv 64 ev))).
        -- destruct CR as ((_ & BYR) & _). cbn [BC.cells_bytes BC.cbytes] in BYR. rewrite app_nil_r in BYR.
           exact BYR.
        -- intros k Hk. apply HE'. cbv beta. right. rewrite (ts_errno B TB). lia.
Qed.

End s.
