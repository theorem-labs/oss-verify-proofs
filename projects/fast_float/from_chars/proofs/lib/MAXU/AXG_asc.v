(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfSlot.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngWb MngWk MngGeoX MngLt MngSurgery MngExc MngNtfC MngGM MngShape.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import MngNtfM MngNtfS MngMWP MngMW0 MngMW1 AXG_as1 AXG_as5 AXG_as7.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Lemma pcg_of_Inv : forall X R U s, Inv X R U s -> XNU X s -> pcg s.
Proof.
  intros X R U s HI HU g am Mg Hp. apply (inv_pcg HI g am); [|exact Hp].
  apply usedX_intro; [|exact Mg]. destruct (memb g X) eqn:E; [|reflexivity]. exfalso. exact (HU g (memb_In' g X E) am Mg).
Qed.

Lemma rgeoA_regions : forall HTOP L s s', st_regions s' = st_regions s -> rgeoA HTOP L s -> rgeoA HTOP L s'.
Proof. intros HTOP L s s' E H r rg Hr Hl. unfold region_of in Hr. rewrite E in Hr. exact (H r rg Hr Hl). Qed.

Lemma rdisj_regions : forall L s s', st_regions s' = st_regions s -> rdisj L s -> rdisj L s'.
Proof. intros L s s' E H r1 r2 rg1 rg2 Hne H1 H2. unfold region_of in H1, H2. rewrite E in H1, H2. exact (H r1 r2 rg1 rg2 Hne H1 H2). Qed.

Lemma RMONO_regions : forall s s', st_regions s' = st_regions s -> RMONO s s'.
Proof.
  intros s s' E. split; [rewrite E; lia|]. intros r rg Hr Hl. exists rg. unfold region_of in *. rewrite E.
  split; [exact Hr|]. split; [exact Hl|]. split; [reflexivity | lia].
Qed.

(* [comment removed for export] *)
Lemma GROW_shape : forall HTOP X R U L s m s' m' sp0 K, CUT HTOP X R U L s m sp0 K -> SHP s s' -> FRM L s sp0 K m m' ->
  GROW sp0 K L s m L s' m'.
Proof.
  intros HTOP X R U L s m s' m' sp0 K C SH FR. pose proof C as [HI HX N HG HD HT HTB].
  pose proof (nc_ctx _ _ _ _ _ _ _ N) as Hctx. pose proof (nc_sp1 _ _ _ _ _ _ _ N) as Hsp1.
  assert (PLACE : forall c, In c (image s) -> (0x97c98 <= loc_addr L (mc_loc c) /\ loc_addr L (mc_loc c) + Z.of_nat (mc_w c) <= 0x98038) \/
                    loc_addr L (mc_loc c) + Z.of_nat (mc_w c) <= 0x10000 \/ 0x99000 <= loc_addr L (mc_loc c)).
  { intros c Hc. exact (cells_place HTOP X R U s L HTB HI HX HG HD Hctx c Hc). }
  split; [apply lext_refl|]. split; [exact (RMONO_regions s s' (proj1 (proj2 SH)))|].
  split; [exact (image_persist L s s' SH)|]. split.
  - intros x Hx Hnc. destruct (decide (m' (wa x) = m (wa x))) as [E|E]; [exact E|]. exfalso.
    destruct (FR x ltac:(lia) E) as [A | (c & Hc & _ & Hin)]; [clear - A Hx Hsp1; lia|].
    pose proof (PLACE c Hc) as P. unfold in_rng, cell_range in Hin. cbn [fst snd] in Hin. clear - P Hin Hx Hnc. lia.
  - intros x Hx Hne. destruct (FR x Hx Hne) as [A | (c & Hc & _ & Hin)]; [left; exact A|]. right. left.
    destruct (image_persist L s s' SH c Hc) as (c' & Hc' & E). exists c'. split; [exact Hc'|]. rewrite E. exact Hin.
Qed.

Section ASC.
Context {fx : FPState}.

#[using="Type"] Theorem as_cut : forall HTOP X U L s m regs rom sp0 K sc req fuel,
  CUT HTOP X None U L s m sp0 K -> 0 <= sc < 48 -> getr regs 2 = wa sp0 -> getr regs 10 = wa sc -> getr regs 11 = wa req ->
  0 <= req <= 2^26 -> DBT m ->
  exists R m' first s', try_avail sc s = IRet (first, s') /\ DBT m' /\ GROW sp0 K L s m L s' m' /\ mem_grows m m' /\
    (forall c, 0 <= c -> c <> sc -> active_hd s' c = active_hd s c) /\ ub_same s s' /\
    ((exists g am, first <> 0 /\ CUT HTOP X (Some (g, ctz32 first)) U L s' m' sp0 K /\ active_hd s' sc = Some g /\ usedX X s' g am /\
        am_sc am = sc /\ class_size sc <= stride_of am /\ 0 <= ctz32 first <= am_last am /\
        msteps SEGS (mkst regs (wa 0x540a8) m rom) (mkst R (wa 0x54944) m' rom) /\ getr R 10 = wa (ctz32 first) /\
        (forall k, In k callee_as -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
        alloc_slot (S fuel) sc req s = IRet (ctz32 first, s')) \/
     (first = 0 /\ CUT HTOP X None U L s' m' sp0 K /\ active_hd s' sc = None /\
        msteps SEGS (mkst regs (wa 0x540a8) m rom) (mkst R (wa 0x54288) m' rom) /\
        (exists can, as_frame R m' sp0 sc req can (bv_unsigned (getr regs 1)) (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9))
           (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19)) (bv_unsigned (getr regs 20)) (bv_unsigned (getr regs 21))
           (bv_unsigned (getr regs 22)) (bv_unsigned (getr regs 23)) (bv_unsigned (getr regs 24)) (bv_unsigned (getr regs 25))) /\
        (forall k, In k [3;4;26;27]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
        alloc_slot (S fuel) sc req s = as_group fuel sc req s')).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros HTOP X U L s m regs rom sp0 K sc req fuel C Hsc R2 R10 R11 Rreq Mdb.
  pose proof C as [HI HX N HG HD HT HTB].
  assert (XU : XNU X s) by exact (XNU_of_XNM X s HX).
  destruct (as_walk X U L s m regs rom sp0 K sc req fuel HI Hsc (pcg_of_Inv X None U s HI XU) XU N R2 R10 R11 Rreq Mdb)
    as (R & m' & first & s' & Et & N' & _ & Gm & FR & Mdb' & Br).
  assert (SH : SHP s s') by exact (try_avail_shape sc s first s' Et).
  assert (EG : GROW sp0 K L s m L s' m') by exact (GROW_shape HTOP X None U L s m s' m' sp0 K C SH FR).
  assert (QM : (first = 0 -> Inv X None U s' /\ active_hd s' sc = None /\ (forall c, 0 <= c -> c <> sc -> active_hd s' c = active_hd s c) /\ ub_same s s') /\
               (first <> 0 -> ta_post X U s sc first s')).
  { pose proof (try_avail_spec X U s sc (fun r => (fst r = 0 -> Inv X None U (snd r) /\ active_hd (snd r) sc = None /\
        (forall c, 0 <= c -> c <> sc -> active_hd (snd r) c = active_hd s c) /\ ub_same s (snd r)) /\ (fst r <> 0 -> ta_post X U s sc (fst r) (snd r)))
      HI Hsc) as H.
    rewrite Et in H. cbn [itok fst snd] in H. apply H.
    - intros s1 HI1 Hh1 Hc1 UB1. cbn [fst snd]. split; [intros _; auto | intros E; exfalso; exact (E eq_refl)].
    - intros f s1 TP. cbn [fst snd]. split; [intros E; exfalso; destruct TP as (Hf & _); exact (Hf E) | intros _; exact TP]. }
  assert (XU' : XNU X s') by exact (XNU_shape X s s' SH XU).
  assert (HG' : rgeoA HTOP L s') by exact (rgeoA_regions HTOP L s s' (proj1 (proj2 SH)) HG).
  assert (HD' : rdisj L s') by exact (rdisj_regions L s s' (proj1 (proj2 SH)) HD).
  exists R, m', first, s'. split; [exact Et|]. split; [exact Mdb'|]. split; [exact EG|]. split; [exact Gm|].
  destruct Br as [(Hf & Hms & Q10 & QK & Eas) | (Hf & Hms & Hfr & QK & Eas)].
  - destruct (proj2 QM Hf) as (_ & g & am & HI' & Hhd & Hu & Hsca & Hstr & Hidx & Hoth & UB).
    split; [exact Hoth|]. split; [exact UB|]. left. exists g, am. split; [exact Hf|].
    split; [constructor; try assumption; exact (XNM_of_Xok X s' (inv_X HI') XU')|].
    repeat (split; [assumption|]). exact Eas.
  - destruct (proj1 QM Hf) as (HI' & Hhd & Hoth & UB).
    split; [exact Hoth|]. split; [exact UB|]. right. split; [exact Hf|].
    split; [constructor; try assumption; exact (XNM_of_Xok X s' (inv_X HI') XU')|].
    repeat (split; [assumption|]). exact Eas.
Qed.
End ASC.
