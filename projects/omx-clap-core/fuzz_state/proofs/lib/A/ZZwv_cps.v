(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v; 1536 of its 1692 lines of code are new or changed and 1217 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_write_value.v, with its module names changed; 222 of its 422 lines of code are new or changed and 1492 lines of the source are left out. *)
(* write_value's CONTAINER arms (fs.asan image A, write_value 0x83d84): the OBJECT arm's per-item call of put_string on
   the i-th member's key (returning to WVC_R_KEY = 0x84058, ZZwv_defs' measured return). From the loop invariant at the
   return of the per-item indent (ZZwv_inv.wvc_inv at WVC_R_IND), the run to the call (ZZwv_runs2.wvc_seg_ind_obj),
   put_string's contract (FSH_Fn_writer.put_string_spec, a premise), and the return step (ZZwv_step.wvc_ret_inv), the
   loop invariant at WVC_R_KEY with the key's pieces WriterSpec.spieces nm appended.
   put_string's visited-frame clause is discharged as a Theorem Labs lane's FSW_write_value.wv_ps_chain does it (statement and
   proof copied below as wvp_ps_chain, its wv_chain_o clause written out): at this call s0 = o, whose one-node chain
   stops by bad_next (nfp < alloc_ceiling <= o) or is empty, so every visited fp is <= o. The key string's cstr_ok is
   FSW_write_value.wv_cstr_ok_block's statement and proof (copied below as wvp_cstr_ok_block, with its three helpers).
   Rule 24: no function proved here (a call-site step inside write_value's container arms; write_value's lookup:
   lane record (internal path), CHECKER CONFIRM a Theorem Labs lane). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat
FSH_Fn_writer FSH_Fn_alloc FSW_K FSW_K3 FSW_ret FSW_rres FSW_writer_tbl FSW_writer_model FSW_writer_kit
FSH_Fn_reader FSW_rd FSupoisonStack FSW_pj ZZwv_defs ZZwv_inv ZZwv_kit ZZwv_comp ZZwv_tree ZZwv_call ZZwv_call2
ZZwv_call3 ZZwv_res ZZwv_ret ZZwv_runs2 ZZwv_step.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require AF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp WriterValue PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* membership in a concrete list, element by element *)
Ltac wvp_in := repeat (first [left; reflexivity | right]).

Section P. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ================= the key string's cstr_ok (FSW_write_value.v Section cs, statements and proofs) ================= *)
(* a byte visible in the unpoisoned memory is visible in the machine memory: a user-poisoned shadow byte reads 0xf7 *)
Lemma wvp_vis_of_unpoison : forall ly S U (W : world tfibsegs) mem md a,
  ARU tfibsegs B ly S U W mem md ->
  aview tfibsegs (w_H W) (unpoison U mem) a <> None -> aview tfibsegs (w_H W) mem a <> None.
Proof.
intros ly S U W mem md a H Hv.
destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:E.
- pose proof (ARU_poisoned tfibsegs B ly S U W mem md H _ E) as P.
  rewrite Z_to_bv_unsigned in P. unfold bv_wrap in P. change (bv_modulus 64) with (2 ^ 64) in P.
  rewrite aview_mod, P. discriminate.
- rewrite (aview_unpoison_out tfibsegs (w_H W) U mem a E) in Hv. exact Hv.
Qed.

(* under fs_heads, the shadow byte of a block's byte past its 16-byte head is not user-poisoned *)
Lemma wvp_ush_user_out : forall ly S U (W : world tfibsegs) mem md q m x,
  ARU tfibsegs B ly S U W mem md -> fs_heads B ly S U ->
  In (q, m) (ablocks B ly S) -> q + 16 <= x < q + req_size m ->
  in_ush U (shadow_addr x) = false.
Proof.
intros ly S U W mem md q m x H FH Hb Hx.
destruct (in_ush U (shadow_addr x)) eqn:E; [|reflexivity]. exfalso.
apply in_ush_spec in E as (r & Hr & Hs).
destruct (FH r Hr) as (E16 & m' & Hm' & M16).
destruct (upoison_ok_In B ly S U r (ARU_ok tfibsegs B ly S U W mem md H) Hr) as (A8 & _).
destruct r as [h len]. cbn [fst snd] in *. subst len.
assert (Hhx : h <= x < h + 16).
{ apply Z.mod_divide in A8 as [t Ht]; [|lia]. subst h. unfold shadow_addr in Hs.
  rewrite Z.div_mul in Hs by lia. change (16 / 8) with 2 in Hs.
  pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia. }
pose proof (al_blocks tfibsegs B (AR_laws_ok tfibsegs B) ly S W (unpoison U mem) md q m
  (ARU_AR tfibsegs B ly S U W mem md H) Hb) as (_ & _ & _ & _ & _ & PW & _).
destruct (Z.eq_dec h q) as [->|NE]; [lia|].
assert (I1 : In (h, req_size m') (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)))
  by (apply (in_map (fun b => (fst b, req_size (snd b))) _ (h, m')); exact Hm').
assert (I2 : In (q, req_size m) (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)))
  by (apply (in_map (fun b => (fst b, req_size (snd b))) _ (q, m)); exact Hb).
destruct (pairwise_In2 zdisjoint _ _ _ PW I1 I2 ltac:(intros E'; injection E'; intros _ E''; exact (NE E'')))
  as [D|D]; unfold zdisjoint in D; cbn [fst snd] in D; lia.
Qed.

(* the 8-aligned shadow hull grows with the range *)
Lemma wvp_hull_mono : forall a b, a <= b -> shadow_addr a / 8 * 8 <= shadow_addr b / 8 * 8.
Proof.
intros a b Hab. unfold shadow_addr. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
pose proof (Z.div_le_mono a b 8 ltac:(lia) Hab). lia.
Qed.

(* a NUL-terminated string at the start of a live reader block: cstr_ok on the machine memory *)
Lemma wvp_cstr_ok_block : forall ly S U (W : world tfibsegs) mem md p k (s : list Z),
  ARU tfibsegs B ly S U W mem md -> FSupoisonU.fs_heads B ly S U ->
  fs_rblock tfibsegs B ly S W mem p k ->
  PjStruct.pj_cbytes tfibsegs (rdW W mem) p s -> Z.of_nat (length s) + 1 <= k ->
  cstr_ok tfibsegs W mem p s.
Proof.
intros ly S U W mem md p k s H FH (Hb & P16 & K0 & _) (HF & HBY) Hk.
unfold HEAD in Hb. unfold cstr_ok.
set (n := Z.of_nat (length s)) in *.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (ARU_AR tfibsegs B ly S U W mem md H) as HAR.
pose proof (proj1 HAR) as M.
assert (RQ : req_size (k + 16) = k + 16) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia).
destruct (al_blocks tfibsegs B LAWS ly S W (unpoison U mem) md (p - 16) (k + 16) HAR Hb)
  as (A16 & A4096 & ACEIL & AAPP & APRES & _ & AMAX).
rewrite RQ in ACEIL, AAPP, APRES.
pose proof ASAN_CEIL_range as [CR _].
(* the chunk of the block *)
destruct (ablock_chunk B ly S (p - 16) (k + 16) Hb) as (ck & Hck & Hu & Hrq).
pose proof (chunk_facts B ly S _ ck M Hck) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
rewrite Hu in G4. rewrite Hrq, RQ in G8.
assert (CH : (ck_base B ly ck + ck_extent ck) mod 8 = 0 /\ p + n + 8 <= alloc_ceiling).
{ revert G9. destruct (ck_beg ck) as [|off|r o|cid pos]; intros G9; cbv beta iota zeta in G9;
    [contradiction | | | contradiction].
  - destruct G9 as (C1 & FP & CC & CX & CB & X0 & XM & XA & RA1 & RA2).
    pose proof (class_ok (prim_class off) ltac:(lia)) as (K1 & K2 & _).
    pose proof (region_in_prim ly (prim_class off) (am_layout B ly S _ M) ltac:(lia)) as (_ & _ & _ & R4 & R5).
    split.
    + apply Z.mod_divide; [lia|]. pose proof G3 as G3'. apply Z.mod_divide in G3' as [u Hu']; [|lia].
      apply Z.mod_divide in K2 as [v Hv]; [|lia]. exists (2 * u + 4 * v). rewrite CX. lia.
    + unfold kFreeArrayOffset in RA2. unfold ASAN_CEIL in R5. lia.
  - destruct G9 as (O & FP & CB & CX & IN & PA & RL).
    rewrite Hrq in CX, FP. unfold sec_map_size in CX.
    assert (RZ : ck_rz ck = rz_size (k + 16)) by (unfold ck_rz; rewrite Hrq; reflexivity).
    pose proof (round_up_ge (needed_size (k + 16)) kPage ltac:(unfold kPage; lia)) as ((RU1 & RU2) & RU3).
    assert (ND : needed_size (k + 16) = rounded_size (k + 16) + rz_size (k + 16) + rz_size (k + 16))
      by (unfold needed_size, needed_primary; rewrite FP; ring).
    pose proof (rounded_size_bounds (k + 16) ltac:(lia)) as ((RS1 & _) & _).
    pose proof (rz_size_bounds (k + 16)) as ((RZ1 & _) & _).
    pose proof (Z.le_max_l (k + 16) 8) as MX.
    split.
    + apply Z.mod_divide; [lia|]. pose proof G3 as G3'. apply Z.mod_divide in G3' as [u Hu']; [|lia].
      apply Z.mod_divide in RU3 as [v Hv]; [|unfold kPage; lia]. exists (2 * u + 512 * v). rewrite CX.
      unfold kPage in *. lia.
    + unfold ASAN_CEIL in G2. lia. }
unfold ASAN_CEIL in CR.
refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
- (* cstr: the bytes and the NUL, from pj_cbytes *)
  assert (FB : Forall (fun c => 0 <= c < 256) (s ++ [0])).
  { apply Forall_app. split; [eapply Forall_impl; [|exact HF]; intros c Hc; cbv beta in Hc |- *; lia | constructor; [cbv beta; lia | constructor]]. }
  destruct HBY as (_ & _ & BY). unfold cstr. split.
  + intros j Hj.
    assert (Hb8 : 0 <= nth j (s ++ [0]) 0 < 256) by (rewrite Forall_forall in FB; apply FB; apply nth_In; exact Hj).
    split; [|exact Hb8].
    intros i Hi. destruct i as [|i]; [| exfalso; apply Nat.succ_lt_mono in Hi; exact (Nat.nlt_0_r _ Hi)].
    pose proof (BY j ltac:(rewrite length_map; exact Hj)) as Bj.
    rewrite nth_error_map, (nth_error_nth' _ 0 Hj) in Bj. cbn [option_map] in Bj.
    change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
    assert (E : mbyte tfibsegs (rdW W mem) (p + Z.of_nat j) = Some (Z_to_bv 8 (nth j (s ++ [0]) 0))) by exact Bj.
    replace (YO0f.le_byte (nth j (s ++ [0]) 0) 1 0) with (nth j (s ++ [0]) 0); [exact E|].
    unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
    rewrite Z.shiftr_0_r. change (2 ^ 8) with 256.
    rewrite (Z.mod_small (nth j (s ++ [0]) 0) 256) by lia. rewrite Z.mod_small by lia. reflexivity.
  + eapply Forall_impl; [|exact HF]. intros c Hc. cbv beta in Hc |- *. lia.
- (* 4096 <= p *)
  lia.
- (* below the allocation ceiling (cstr_ok asks p + n + 1; the chunk gives p + n + 8) *)
  pose proof (proj2 CH) as CH2. lia.
- (* len < 2 ^ 32: a block is below MALLOC_MAX = 2 ^ 28 *)
  unfold MALLOC_MAX in AMAX. lia.
- (* amem_range: the block is in application memory *)
  unfold amem_range. unfold in_app in AAPP. unfold ASAN_CEIL in AAPP.
  destruct AAPP as [_ [AL | [AH1 AH2]]]; [left | right]; unfold kLowMemEnd, kLowShadowBeg, kHighMemBeg, kHighMemEnd in *; lia.
- (* range_addressable over len + 1, on the machine memory *)
  unfold range_addressable. intros x Hx.
  destruct (range_addressable_of_block tfibsegs B LAWS ly S W (unpoison U mem) md (p - 16) (k + 16) p (n + 1)
    HAR Hb ltac:(lia) ltac:(rewrite RQ; lia) x Hx) as (sv & Hsv & Hok).
  exists sv. split; [|exact Hok].
  assert (HU : in_ush U (bv_unsigned (Z_to_bv 64 (shadow_of_addr SHADOW_OFF x))) = false).
  { rewrite wz by (unfold shadow_of_addr, SHADOW_OFF; pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia));
      pose proof (Z.div_le_upper_bound x 8 x ltac:(lia) ltac:(lia)); lia).
    change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x).
    apply (wvp_ush_user_out ly S U W mem md (p - 16) (k + 16) x H FH Hb). rewrite RQ. lia. }
  rewrite <- (aview_unpoison_out tfibsegs (w_H W) U mem _ HU). exact Hsv.
- (* shadow_hull_vis over len + 1: the block's hull, visible on the machine memory *)
  destruct (al_shadow tfibsegs B LAWS ly S W (unpoison U mem) md (p - 16) (k + 16) HAR Hb) as [_ HH].
  rewrite RQ in HH. unfold shadow_hull_vis in HH |- *. intros sa Hsa.
  apply (wvp_vis_of_unpoison ly S U W mem md sa H). apply HH.
  pose proof (wvp_hull_mono (p - 16) p ltac:(lia)).
  pose proof (wvp_hull_mono (p + (n + 1) - 1) (p - 16 + (k + 16) - 1) ltac:(lia)). lia.
- (* the rest of the NUL's 8-byte word visible: block bytes, then the chunk's tail junk *)
  intros a Ha. apply (wvp_vis_of_unpoison ly S U W mem md a H).
  destruct (Z_lt_le_dec a (p + k)) as [Lk|Lk].
  + apply aview_some_of_apresent. exact (proj1 (APRES a ltac:(lia))).
  + assert (AE : a < ck_base B ly ck + ck_extent ck).
    { destruct CH as [C8 _].
      pose proof (Z.div_mod (p + n) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (p + n) 8 ltac:(lia)) as D2.
      pose proof (Z.div_mod (ck_base B ly ck + ck_extent ck) 8 ltac:(lia)) as D3. rewrite C8 in D3. lia. }
    assert (INJ : In (aoff (sptr_exp (ck_beg ck)) (ck_rz ck + ck_n ck), ck_extent ck - ck_rz ck - ck_n ck)
                     (ajunk B ly S)).
    { unfold ajunk. right. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
      apply in_flat_map. exists ck. split; [exact Hck|].
      unfold chunk_junk. cbv zeta. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
      left. reflexivity. }
    pose proof (proj1 (Forall_forall _ _) (am_junk B ly S _ M) _ INJ) as V.
    unfold range_vis in V. cbn [fst snd] in V.
    assert (NS : forall e', sptr_exp (ck_beg ck) <> ASh e') by (intros e'; destruct (ck_beg ck); cbn; discriminate).
    rewrite (aeval_aoff B ly _ _ NS) in V.
    change (aeval B ly (sptr_exp (ck_beg ck))) with (ck_base B ly ck) in V.
    assert (CKN : ck_n ck = k + 16) by (unfold ck_n; rewrite Hrq; exact RQ).
    specialize (V (a - (p + k)) ltac:(lia)).
    replace (ck_base B ly ck + (ck_rz ck + ck_n ck) + (a - (p + k))) with a in V by lia.
    exact V.
Qed.

(* ================= put_string's visited-frame clause (FSW_write_value.v wv_ps_chain, statement and proof) ================= *)
(* every frame pointer fpchain VISITS (s0, and each record's nfp that bad_next lets it follow) is <= o or >= o + 48:
   s0 < alloc_ceiling forces ch = [] (achain's second disjunct needs sp + 16 <= s0, and sp >= alloc_ceiling); s0 = o
   gives the one-node chain at o (at o = sp + 8 achain is its first disjunct), whose record's nfp < alloc_ceiling <= o;
   o + 48 <= s0: the records' fps rise from s0 (YCbq.fpchain_fps_increase), and a followed nfp lies above its record's
   fp. The fourth premise is FSH_Fn_writer's one-node chain clause at o (FSW_write_value.wv_chain_o), written out. *)
Lemma wvp_ps_chain : forall STK ly S U (W : world tfibsegs) regs mem md ch o,
  fpreU tfibsegs B STK ly S U W regs mem md ch -> spZ regs <= o ->
  (s0Z regs < alloc_ceiling \/ s0Z regs = o \/ o + 48 <= s0Z regs) ->
  (o = spZ regs + 8 /\ raZ regs < alloc_ceiling \/
   spZ regs + 16 <= o /\ exists ra nfp, rdword (aview tfibsegs (w_H W) (unpoison U mem)) (o - 8) = Some ra /\
     rdword (aview tfibsegs (w_H W) (unpoison U mem)) (o - 16) = Some nfp /\ (ra < 4096 \/ nfp < alloc_ceiling)) ->
  forall fp, fp = s0Z regs \/ (exists r, In r ch /\ snd r = fp /\ bad_next (fst (fst r)) (ly_top ly) fp = false) ->
  fp <= o \/ o + 48 <= fp.
Proof.
intros STK ly S U W regs mem md ch o ((HAP & _) & _) Hspo HS0w HCHO fp Hfp.
pose proof HAP as (_ & _ & _ & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (_ & HSTK0 & Hceil & Hslo & _).
destruct Hch as [(_ & ->) | (H16 & Htopv & Hal & Hfc & _)].
- destruct Hfp as [-> | (r & [] & _)]. lia.
- destruct HS0w as [Hlo | [Ho | Hhi]].
  + lia.
  + destruct HCHO as [(Ho8 & _) | (_ & ra & nfp & Hra8 & Hnfp & Hend)]; [lia|].
    destruct Hfp as [-> | (r & Hin & Hsnd & _)]; [lia|].
    destruct ch as [|[[fp1 ra1] nfp1] rest]; [destruct Hin|].
    cbn [fpchain] in Hfc. destruct Hfc as (E1 & _ & H8 & H16' & Hra1 & Hrest).
    subst fp1. rewrite Ho in H8, H16'. rewrite Hra8 in H8. rewrite Hnfp in H16'.
    injection H8 as Era. injection H16' as Enfp.
    assert (Hbn : bad_next (s0Z regs) (ly_top ly) nfp1 = true).
    { unfold bad_next. apply Bool.orb_true_iff. left. apply Bool.orb_true_iff. left. apply Z.leb_le. lia. }
    rewrite Hbn in Hrest. subst rest.
    destruct Hin as [<- | []]. cbn [snd] in Hsnd. left. lia.
  + destruct Hfp as [-> | (r & Hin & _ & Hbn)]; [right; lia|].
    pose proof (fpchain_fps_increase _ _ _ _ Hfc) as Hinc.
    rewrite Forall_forall in Hinc. specialize (Hinc r Hin).
    unfold bad_next in Hbn. apply Bool.orb_false_elim in Hbn as [Hbn _]. apply Bool.orb_false_elim in Hbn as [Hbn _].
    apply Z.leb_gt in Hbn. right. lia.
Qed.
End P.

Section A. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Hypothesis HSS : FsShadowSyms B.
(* the arm instance: its fixed data and the entry state *)
Variable F : wvc_fix.
Variables (ly0 : alayout) (S0 : astate) (U0 : list (Z * Z)) (W0 : world tfibsegs) (mem0 : word -> option byte)
  (md0 : Model) (regs0 : bvmap 5 word).
(* the entry facts the arms' callers discharge once *)
Hypothesis HE_sp16 : wf_sp F mod 16 = 0.
Hypothesis HE_ot16 : wf_ot F mod 16 = 0.
Hypothesis HE_oot : wf_o F + 32 <= wf_ot F.
Hypothesis HE_o8 : wf_o F mod 8 = 0.
Hypothesis HE_top : wf_ot F <= ly_top ly0.
Hypothesis HE_top47 : ly_top ly0 <= 2 ^ 47.
Hypothesis HE_lo : alloc_ceiling + STK_write_value (wf_m F) <= wf_sp F.
Hypothesis HE_gp : YK11.getr regs0 3%bv = w64 (as_gp B).
Hypothesis HE_tp : YK11.getr regs0 4%bv = w64 (as_tp B).
Hypothesis HE_cap0 : 0 <= wf_cap0 F.
Hypothesis HE_capl : wf_cap0 F <= wf_live F.
Hypothesis HE_cnt0 : 0 <= wf_cnt0 F.
Hypothesis HE_p : 0 <= wf_p F < alloc_ceiling.
Hypothesis HE_d : 0 <= wf_d F.
Hypothesis HE_dd : wf_d F + Z.of_nat (PjTree.depth (wf_t F)) <= 2 ^ 31 - 1.
Hypothesis HE_room : Z.of_nat (length (wf_text0 F)) + Z.of_nat (length (concat (wvc_WP F))) + 1 <= WMAX.
Hypothesis HE_bud : wbudget_pre S0 (wf_cap0 F) (wf_cnt0 F) (wf_live F) (WriterApp.putN (wvc_st0 F) (wvc_WP F)).
Hypothesis HE_frl : Z.of_nat (length (frames S0)) <= FRL_CRT_CALLEE.
Hypothesis HE_foot : forall x, wf_o F <= x < wf_ot F -> ~ PjStruct.pj_foot (wf_v F) (wf_D F) x.
Hypothesis HE_plain : jv_plain (wf_t F).
Hypothesis HE_ty :
  (wf_ty F = 5 /\ exists items, wf_t F = PjTree.JArr items /\ wf_n F = Z.of_nat (length items) /\ wf_keys F = 0) \/
  (wf_ty F = 6 /\ exists members, wf_t F = PjTree.JObj members /\ wf_n F = Z.of_nat (length members)).
Hypothesis HE_hdr : exists num capn,
  PjStruct.pj_hdr tfibsegs (rdW W0 mem0) (wf_v F) (wf_ty F) num (wf_str F) (wf_kids F) (wf_keys F) (wf_n F) capn.
Hypothesis HE_n : 0 <= wf_n F < 2 ^ 54.
Hypothesis HE_kk : 0 <= wf_kids F /\ wf_kids F + 56 * wf_n F <= alloc_ceiling /\
                   0 <= wf_keys F /\ wf_keys F + 8 * wf_n F <= alloc_ceiling.

(* ================= the object arm's per-item indent returned: put_string of the i-th member's key ================= *)
Lemma wvc_ind_key : forall i ke key Pd Rest ly S U (W : world tfibsegs) ms mdc buf members nm u
    (Q : world tfibsegs -> config -> Prop),
  put_string_spec B tfibsegs ->
  wvc_WP F = Pd ++ WriterSpec.spieces nm ++ Rest ->
  wvc_inv B F WVC_R_IND i ke key Pd ly0 S0 U0 W0 mem0 md0 regs0 W ms mdc ly S U buf ->
  wf_t F = PjTree.JObj members -> nth_error members (Z.to_nat i) = Some (nm, u) ->
  (forall ly' S' U' (W' : world tfibsegs) regs' mem' md' buf' key',
     wvc_inv B F WVC_R_KEY i ke key' (Pd ++ WriterSpec.spieces nm) ly0 S0 U0 W0 mem0 md0 regs0
       W' (mkst regs' (Z_to_bv 64 WVC_R_KEY) mem' (seg_rom tfibsegs)) md' ly' S' U' buf' ->
     SRr tfibsegs W' (cfg_at tfibsegs WVC_R_KEY regs' mem' md') Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros i ke key Pd Rest ly S U W ms mdc buf members nm u Q HPS HWP HINV Ht Hnth K.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HWF : WVC_F = 176) by reflexivity.
pose proof (wvc_stk (wf_m F)) as (HSTKF & _ & _ & HSTKps & _).
assert (HSTK0 : 0 <= STK_put_string) by (vm_compute; discriminate).
assert (Hty : wf_ty F = 6).
{ destruct HE_ty as [(_ & items & Ht' & _) | (H6 & _)]; [rewrite Ht in Ht'; discriminate | exact H6]. }
assert (Hlo' : alloc_ceiling <= wf_sp F - WVC_F) by lia.
pose proof HE_kk as (Hk0 & Hkn & Hy0 & Hyn).
unfold wvc_inv in HINV. cbv zeta in HINV.
destruct HINV as (HAT & HSEM & R8 & R9 & R19 & R21 & R25 & R3 & R4 & R18 & R20 & R22 & R23 & R24 & R26 & R27 &
  Hsp & Hi & Hke).
set (E := wvc_E F regs0 (ms_regs ms) ke key).
change (Ereg (ms_regs ms) (fs_extraT ++ wvc_xs regs0 (wf_str F) (wf_kids F) (wf_keys F) (wf_n F) (wf_d F) ke key))
  with E in HAT.
rewrite Hty in HAT.
set (st := wvc_stP F Pd) in *.
pose proof (wvc_sem_o_sp B F ly0 S0 U0 W0 mem0 regs0 ly S U W (ms_mem ms) buf st HSEM) as Hosp.
(* the key pointer in the key slot keys + 8 * i, read off the loop state's key region *)
set (v := bv_unsigned (ew E (xatom 19))).
assert (Hv : 0 <= v < 2 ^ 64) by apply u64_range.
assert (E18 : ew E (xatom 18) = Z_to_bv 64 ke) by (unfold E; rewrite wvc_E_x; reflexivity).
assert (HKV : val_mem tfibsegs (rdW W (ms_mem ms)) ke 8 v).
{ pose proof (AF0x.st_ok_chunk_val (w_H W) E (wvc_ssL 6 (wf_p F) WVC_R_IND) ms 4%nat wvc_keyR 0%nat 0 8%N
    (SOff (xatom 19) 0) v (proj1 HAT) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
    ltac:(rewrite fsw_SOff0; unfold v; symmetry; apply Z_to_bv_bv_unsigned)
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hv) ltac:(cbn [Z.of_N]; lia)) as H.
  change (base_val E (YP09.r_base wvc_keyR)) with (bv_unsigned (ew E (xatom 18))) in H.
  change (N.to_nat 8) with 8%nat in H.
  rewrite E18, unsigned_lit_small, Z.add_0_r in H by lia. exact H. }
(* the run to the call *)
apply (wvc_seg_ind_obj B W ms mdc E (wf_p F) (wvc_STK F) (wf_ot F) (wf_sp F) (wvc_FP F) ly0 S0 W0
  (unpoison U0 mem0) md0 [] ly S U (wevk (wf_cap0 F) st) Q HAT).
{ unfold E. rewrite (wvc_E_r F regs0 (ms_regs ms) ke key 2%bv 2 eq_refl). exact Hsp. }
{ lia. }
{ unfold wvc_STK. lia. }
intros ms' mdc' Ems HJ HARU HFR HCH R1 R10 R11 R2 RK.
rewrite Ems.
set (regsC := ms_regs ms') in *. set (memC := ms_mem ms') in *.
change (mkCfg (mkst regsC (w64 A_put_string) memC (seg_rom tfibsegs)) mdc')
  with (cfg_at tfibsegs A_put_string regsC memC mdc').
(* the registers at the call *)
assert (RC : forall q z, In q [3;4;8;9;18;19;20;21;22;23;24;25;26;27]%bv -> YK11.getr (ms_regs ms) q = z ->
  YK11.getr regsC q = z) by (intros q z Hq Ez; rewrite (RK q Hq); exact Ez).
pose proof (RC 3%bv _ ltac:(wvp_in) R3) as R3c. pose proof (RC 4%bv _ ltac:(wvp_in) R4) as R4c.
pose proof (RC 8%bv _ ltac:(wvp_in) R8) as R8c. pose proof (RC 9%bv _ ltac:(wvp_in) R9) as R9c.
pose proof (RC 18%bv _ ltac:(wvp_in) R18) as R18c. pose proof (RC 19%bv _ ltac:(wvp_in) R19) as R19c.
pose proof (RC 20%bv _ ltac:(wvp_in) R20) as R20c. pose proof (RC 21%bv _ ltac:(wvp_in) R21) as R21c.
pose proof (RC 22%bv _ ltac:(wvp_in) R22) as R22c. pose proof (RC 23%bv _ ltac:(wvp_in) R23) as R23c.
pose proof (RC 24%bv _ ltac:(wvp_in) R24) as R24c. pose proof (RC 25%bv _ ltac:(wvp_in) R25) as R25c.
pose proof (RC 26%bv _ ltac:(wvp_in) R26) as R26c. pose proof (RC 27%bv _ ltac:(wvp_in) R27) as R27c.
assert (Hsp' : spZ regsC = wf_sp F - WVC_F) by (unfold spZ; rewrite R2; exact Hsp).
(* the writer facts at the call's memory: the run wrote write_value's frame only *)
assert (HSEMC : wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly S U W memC buf st)
  by exact (wvc_sem_run B F ly0 S0 U0 W0 mem0 regs0 ly S U W (ms_mem ms) memC mdc' buf st HSEM HARU HFR Hlo'
    ltac:(lia) ltac:(lia)).
(* case 1 of the chain clause at o: the word at sp - 8 is write_value's saved ra (frame offset 168, xatom 17) *)
assert (HC1 : wf_o F = wf_sp F + 8 ->
  rdword (aview tfibsegs (w_H W) (unpoison U memC)) (wf_sp F - 8) = Some (raZ regs0)).
{ intros _.
  assert (Hin : In (YP09.mkChunk 168 (CVal 8 (SOff (xatom 17) 0))) (wvc_csL (wf_p F))).
  { unfold wvc_csL, wvc_cs0. cbn [seq map app]. wvp_in. }
  pose proof (proj1 (Forall_forall _ _) HCH _ Hin) as Hck.
  pose proof (val_of_chunk_ok tfibsegs E (rdW W memC) (wf_sp F - WVC_F) 168 8 (SOff (xatom 17) 0) (raZ regs0) Hck
    ltac:(rewrite fsw_SOff0; unfold E; rewrite wvc_E_x; cbn [nth wvc_xs app map wvc_saved]; unfold raZ;
          symmetry; apply Z_to_bv_bv_unsigned)
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold raZ; apply u64_range)
    ltac:(cbn [Z.of_N]; lia)) as Hvm.
  change (N.to_nat 8) with 8%nat in Hvm.
  replace (wf_sp F - WVC_F + 168) with (wf_sp F - 8) in Hvm by lia.
  rewrite (rdword_ext (aview tfibsegs (w_H W) memC) (aview tfibsegs (w_H W) (unpoison U memC)) (wf_sp F - 8)).
  - exact (AF0x.val_mem_rdword (w_H W) memC (wf_sp F - 8) (raZ regs0) ltac:(unfold raZ; apply u64_range) Hvm).
  - intros k Hk. apply aview_unpoison_out. apply (zwk_p_stack_not_ush B ly S U W memC mdc'); [exact HARU | lia]. }
assert (Hret : YK0s.ret_ok (YK11.getr regsC 1%bv))
  by (rewrite R1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity).
assert (Hra4 : 4096 <= raZ regsC)
  by (unfold raZ; rewrite R1; unfold w64, WVC_R_KEY; rewrite unsigned_lit_small by lia; lia).
assert (Hgp : YK11.getr regsC 3%bv = w64 (as_gp B)) by (rewrite R3c; exact HE_gp).
assert (Htp : YK11.getr regsC 4%bv = w64 (as_tp B)) by (rewrite R4c; exact HE_tp).
assert (Hs0 : s0Z regsC = wf_o F) by (unfold s0Z; rewrite R8c; unfold w64; apply unsigned_lit_small; lia).
assert (Hottop : wf_ot F <= ly_top ly).
{ pose proof HJ as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). lia. }
(* the callee's fpreU, the chain clause at o, the window presence *)
destruct (wvc_callpre B F ly0 S0 U0 W0 mem0 md0 regs0 ly S U W memC mdc' (wevk (wf_cap0 F) st) buf st regsC
  STK_put_string HJ HARU HSEMC HC1 Hsp' HE_sp16 HE_ot16 ltac:(lia) HSTK0 HSTKps Hret Hra4 Hgp Htp Hs0 HE_oot Hottop
  HE_o8 Hlo') as (ch & _ & HPRE & HCHO & HPRES).
(* put_string's visited-frame clause: at this call s0 = o *)
pose proof (wvp_ps_chain B STK_put_string ly S U W regsC memC mdc' ch (wf_o F) HPRE ltac:(lia)
  (or_intror (or_introl Hs0)) HCHO) as HVIS.
assert (Hfr : Z.of_nat (length (frames S)) <= FRL_CRT_CALLEE).
{ pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. cbn [app]. exact HE_frl. }
(* the i-th member: its key slot, the key string and its block, at the call's memory *)
pose proof HSEMC as (HOUT & HGL & HHD & HUS & HBS & HBK & HCNT & HWK & HN & HPO & HNB & HUL & HD & HROOT & HBIN &
  HB0 & HRO & H8 & HC & HU0).
destruct (wvc_hdr_at B F ly0 S0 U0 W0 mem0 regs0 HE_hdr ly S U W memC buf st HSEMC) as (num & capn & HHDR).
rewrite Ht in HN.
destruct (wv_obj_mem _ _ _ _ _ _ _ _ HN Hnth) as (num2 & kids2 & keys2 & n2 & cap2 & Di & Dpre & x & kk & Du &
  Dpost & HH2 & _ & _ & _ & _ & _ & _ & _ & Hx & HCS & _ & _ & HinD & _).
assert (Ekeys : keys2 = wf_keys F).
{ destruct HH2 as (_ & _ & _ & _ & _ & Hk2 & _). destruct HHDR as (_ & _ & _ & _ & _ & Hk1 & _).
  exact (PjStruct.pj_u64_uniq _ _ _ _ _ Hk2 Hk1). }
subst keys2. rewrite Z2Nat.id in Hx by lia. rewrite <- Hke in Hx.
assert (HKVC : val_mem tfibsegs (rdW W memC) ke 8 v).
{ intros j Hj. unfold mbyte. rewrite HFR; [exact (HKV j Hj)|].
  rewrite unsigned_lit_small by lia. lia. }
assert (Exv : x = v).
{ apply (PjStruct.pj_u64_uniq _ _ _ _ _ Hx). apply fsw_val_pj_u64; [exact HKVC | exact Hv | lia | lia]. }
assert (R10c : YK11.getr regsC 10%bv = w64 (wf_o F)).
{ rewrite R10. unfold E. rewrite (wvc_E_r F regs0 (ms_regs ms) ke key 8%bv 8 eq_refl). exact R8. }
assert (R11c : YK11.getr regsC 11%bv = w64 x).
{ rewrite R11, Exv. unfold v, w64. symmetry. apply Z_to_bv_bv_unsigned. }
pose proof (HUL x kk HinD) as HRB.
destruct (HD x kk HinD) as (_ & Hxbuf).
pose proof HCS as (_ & Hlen & HCB).
assert (HCSOK : cstr_ok tfibsegs W memC x nm)
  by exact (wvp_cstr_ok_block B ly S U W memC mdc' x kk nm HARU HHD HRB HCB Hlen).
pose proof HCSOK as (_ & Hx4096 & Hxc & _).
assert (HSRC : wsrc_kept B tfibsegs ly S U W memC buf x (nm ++ [0])).
{ right; left. exists x, kk. split; [exact Hxbuf|]. split; [exact HRB|]. split; [lia|].
  rewrite length_app. cbn [length]. lia. }
pose proof HCB as (Hbytes & _).
assert (Hbok : WriterSpec.bytes_ok nm).
{ unfold WriterSpec.bytes_ok. eapply Forall_impl; [|exact Hbytes]. intros c Hc'. cbn beta in Hc'. lia. }
assert (Hnz : WriterSpec.no_zero nm).
{ unfold WriterSpec.no_zero. eapply Forall_impl; [|exact Hbytes]. intros c Hc'. cbn beta in Hc'. lia. }
assert (Hplain : plain_bytes nm).
{ pose proof HE_plain as HP0. rewrite Ht in HP0. exact (proj1 (wv_plain_mem members (Z.to_nat i) nm u HP0 Hnth)). }
(* the room, the cap and the budget of this call *)
assert (Hroom : Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length (WriterSpec.wstr nm)) + 1 <= WMAX).
{ pose proof (wv_room_mid (wvc_st0 F) Pd (WriterSpec.spieces nm ++ Rest)) as HRM.
  pose proof HE_room as HR0. rewrite HWP in HR0.
  unfold WriterSpec.wstr. rewrite concat_app, length_app in HRM.
  change (WriterApp.w_text (wvc_st0 F)) with (wf_text0 F) in HRM.
  unfold st, wvc_stP. lia. }
pose proof HBK as (Hcapw & Hbb & _).
destruct HGL as (peak & Hpk & HG).
assert (Hbud : wbudget_pre S (WriterApp.w_cap st) (WriterApp.w_cnt st) (wf_live F + WriterApp.w_cap st - wf_cap0 F)
  (WriterApp.putN (WriterApp.mkW (WriterApp.w_failed st) (WriterApp.w_text st) (WriterApp.w_cap st)
     (WriterApp.w_cnt st) (WriterApp.w_fail st) []) (WriterSpec.spieces nm))).
{ pose proof HE_bud as HB0'. rewrite HWP, app_assoc in HB0'.
  pose proof (wv_budget_pre_prefix S0 (wf_cap0 F) (wf_cnt0 F) (wf_live F) (wf_failed0 F) (wf_text0 F) (wf_fail0 F)
    (Pd ++ WriterSpec.spieces nm) Rest HE_cap0 HB0') as HB1.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
  pose proof (wv_budget_pre_mid S0 S (wf_cap0 F) (wf_cnt0 F) (wf_live F) (wf_failed0 F) (wf_text0 F) (wf_fail0 F)
    Pd (WriterSpec.spieces nm) HE_cap0 HB1 Hnev Hbb HCNT) as HB2.
  replace (wf_live F + WriterApp.w_cap st - wf_cap0 F) with (wf_live F - wf_cap0 F + WriterApp.w_cap st) by lia.
  exact HB2. }
(* the call *)
eapply SRr_bind.
{ exact (HPS ly S U W regsC memC mdc' ch (wf_ot F) (wf_o F) x buf (WriterApp.w_cap st) (WriterApp.w_failed st)
    (WriterApp.w_text st) nm (wf_live F + WriterApp.w_cap st - wf_cap0 F) peak (WriterApp.w_cnt st)
    (WriterApp.w_fail st) HPRE HHD Hfr R10c R11c HOUT HG HU0 ltac:(lia) HE_oot HE_ot16 Hottop HCHO HVIS HPRES
    HCSOK HSRC Hbok Hnz Hplain ltac:(left; lia) Hroom Hcapw ltac:(lia) Hbud). }
(* the return: the loop invariant at WVC_R_KEY *)
intros W' c' _ (st' & buf' & U' & Est & HUS' & HWPs).
unfold wpost, fpostU in HWPs.
destruct HWPs as (ly' & S' & regs' & mem' & md' & Ec & HJc & OK' & PO' & HP & HOUT' & HBK' & HBS' & HWK' & _ & HGL').
subst c' st'.
destruct (wvc_ret_inv B HSS F ly0 S0 U0 W0 mem0 md0 regs0 HE_sp16 HE_oot HE_top HE_top47 HE_lo HE_cap0 HE_cnt0 HE_p
  HE_d HE_dd HE_bud HE_ty HE_hdr HE_n HE_kk WVC_R_KEY i Pd (WriterSpec.spieces nm) Rest ly S U W memC mdc' buf regsC
  (ms_regs ms) ke key STK_put_string peak ly' S' U' W' regs' mem' md' buf' HWP HJ HARU HSEMC Hpk HCH R9 Hsp' R8c R9c
  R19c R21c R25c R22c R3c R4c R18c R20c R23c R24c R26c R27c Hi HJc OK' PO' HP HSTK0 HSTKps HUS' HOUT' HBK' HBS' HWK'
  HGL') as (key' & HINV').
rewrite <- Hke in HINV'.
rewrite R1.
exact (K ly' S' U' W' regs' mem' md' buf' key' HINV').
Qed.

End A.
