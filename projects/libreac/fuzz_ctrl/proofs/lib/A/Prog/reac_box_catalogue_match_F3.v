(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths, module names and addresses changed; 687 of its 728 lines of code are new or changed and 207 lines of the source are left out. *)
(* Footprint (_F) re-run of stretch S3 of reac_box_catalogue_match.v (source commit d69f7c708f6, proved on FACTS
   ed6b6b7b0ab) by the same script over lib/Lib/StepF; image fuzz_ctrl v1.9.0 asan, ELF fuzz_ctrl.debug sha256
   78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd; route (a) of 22:20Z; for the cgif-form walk
   C_reac_box_catalogue_match.v only.

   Stretch S3: the silent run from the return of reac_ctrl_parse (0x84688) to the 11-row loop head (0x846ac) when
   the parse result is 9, or through the no-row tail (0x84700) and the no-match join (0x84704) to the exit cut
   (0x84724) when it is not. It re-runs, over StepF's step and under a universally quantified footprint RNG:
     - the part of cm_parse AFTER the `jal reac_ctrl_parse` at 0x84684 (cm_parse_F): the source lemma runs THROUGH
       that call (its script applies the Section hypothesis HPC inside the run), so the script is split at the call:
       the facts reac_ctrl_parse_contract's post gives at the return are the premises of cm_parse_F, and the
       instruction steps 0x84688 .. 0x846ac / 0x84700 are unchanged;
     - cm_tail restricted to its first leg 0x84704 -> 0x84724 (cm_tail_F): the source lemma runs through the exit
       cut by `eapply cm_exit`, so the script is split there and the exit's state is the premise cmXCF;
     - cm_none_holds (cm_none_F), which steps 0x84700 -> 0x84704 and joins cm_tail_F.
   cm_parse_S3_F composes them into the whole stretch.

   The source proof's Section Match is NOT re-based: its auxiliary lemmas are used as they are (they are stated over
   an arbitrary reached memory mc), applied to this file's Section variables through the abbreviations below.

   rng premises: the 9 instructions 0x84688 .. 0x846a8 and the `li s3,0` at 0x84700 are register-only (instruction
   fetch is not an access), so cm_parse_F and cm_none_F add none of their own; the five `sb a0,k(s6)` of 0x84708 ..
   0x84718 write the frame's shadow bytes 4 .. 8, so cm_tail_F adds the single premise
   `rng RNG (shadow_addr fr + 4) 5` (region (a): the shadow of the frame named by its own cmInv premise).
   No access of this stretch was reported uncovered by StepF.

   <r>_of_F (ExecF.rng_all): the _F statement at the footprint that admits every access is the statement of the
   stretch with no footprint premise left, so the _F form asks for nothing beyond the proved run. The continuation
   premises stay in _F form there: Exec.evt does not give ExecF.evtF back, so an evt continuation cannot be lifted.

   Route (C) (F-on-spec.md (a working note, not in this delivery), a Theorem Labs lane's frozen form): Section MatchFOn below re-runs every lemma of this file with
   Section MatchF's premise SR : shadow_rw m narrowed to SR_on : shadow_rw_on R m, R =
   reac_box_catalogue_match_shadow_R f len S FS, over reac_box_catalogue_match_on.v's names (lemma X -> X_on, cut
   state D -> D_on); Section MatchF keeps every old statement, each old lemma now a corollary of its X_on.

   reac_box_catalogue_match.v and its theorem are unchanged. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcBox RcBoxLib RcSynth RcParse
  RcMatch RcMatchLib RcAsan RcAsanLib RcLay.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT asan_stack_malloc_c RcAsanFP RcAsanFPLib
  memcmp_c bcmp_wrap_c reac_ctrl_parse_c reac_box_model_block_c reac_box_model_block
  reac_box_catalogue_match_c reac_box_catalogue_match_lib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_box_catalogue_match.
(* Route (C): the narrowed premise and the `_on` re-run of the source (Required, not Imported), for Section MatchFOn. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_box_catalogue_match_on.
(* Last: StepF's step / store_done (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.
(* The store hook the scripts below use (StepF's store_done calls it): also transport rd_mono across a store. Text of
   lib/A/Prog/MemMono.v (at head lib/A/Prog/MemMono.v:207-217; from a working branch 8bac67328ab), Local here. *)
Local Ltac footprint_after_store segs m a bs ::=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU; [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | RMo : rd_mono ?mq m |- _ => apply (rd_mono_write mq m (wa a) bs) in RMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq; [ | lia | simpl_sizes; slia ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

Module CM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_catalogue_match.
Module CMO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_catalogue_match_on.

(* ==== route (C): the `_on` forms of this stretch (F-on-spec.md) ====

   Section MatchFOn is Section MatchF below with SR : shadow_rw m replaced by SR_on : shadow_rw_on R m (R =
   reac_box_catalogue_match_shadow_R f len S FS), the other Variables and Hypotheses unchanged, in the same order.
   The names reac_box_catalogue_match_on.v re-proves are taken from it (cmInv_on, fk_facts_on, cm_inv_step_on,
   cm_inv_mu_on, cm_Wc_rd_on, cm_Wc_sh_out_on, cm_Wc_rd_R); the others from the old plain file, as in Section MatchF.
   Each X_on is X's script with these steps changed:
     - the three cut states cmLHF_on / cmNoneF_on / cmXCF_on carry cmInv_on in place of cmInv;
     - cm_parse_F's premise `shadow_rw m2` (reac_ctrl_parse_contract's post) is the callee's `_on` post
       `forall P, shadow_rw_on P mc -> shadow_rw_on P m2`, and its cm_Wc_rd step is cm_Wc_rd_on on the region that
       cm_Wc_rd_R puts inside R, as in reac_box_catalogue_match_on.v's cm_parse_on.
   cmInv_on_of_cmInv / cmInv_of_cmInv_on convert the invariant for Section MatchF's corollaries. *)
Section MatchFOn.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (f len S FS : Z) (fb : list byte).
Hypothesis Rf : 0 <= f < 2^64.
Hypothesis Rlen : 0 <= len < 2^64.
Hypothesis RS : S < 2^64.
Hypothesis S16 : S mod 16 = 0.
Hypothesis HK : 9136 <= S.
Hypothesis ST : stk rsegs m (S - 9136) S.
Hypothesis Hfb : length fb = 50%nat.
Hypothesis SR_on : shadow_rw_on (reac_box_catalogue_match_shadow_R f len S FS) m.
Hypothesis HHM : HIGHMEM_BEG <= S - 9136.
Hypothesis HAE : S <= APPMEM_END.
Hypothesis AW : addressable m (S - 9136) 9136.
Hypothesis FP0 : fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (S - 9136) S
  (reac_box_catalogue_match_W S) (reac_box_catalogue_match_D f len).

(* Section MatchF's abbreviations, the re-proved names pointing to reac_box_catalogue_match_on.v (on-api.md's
   prefixes, SR_on in SR's place). *)
Local Abbreviation CA := (CM.CA S).
Local Abbreviation cmFK := (CM.cmFK S FS).
Local Abbreviation cmWc := (CM.cmWc FS).
Local Abbreviation cmHF := (CM.cmHF S).
Local Abbreviation cmInv := (CM.cmInv ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS).
Local Abbreviation cmInv_on := (CMO.cmInv_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS).
Local Abbreviation cm_geo := (CM.cm_geo tp m f len S FS fb Rf Rlen S16 HK Hfb FP0).
Local Abbreviation fk_facts_on := (CMO.fk_facts_on tp m f len S FS fb Rf Rlen S16 HK ST Hfb SR_on AW FP0).
Local Abbreviation cm_fr_bounds := (CM.cm_fr_bounds tp m f len S FS fb Rf Rlen S16 HK Hfb HHM FP0).
Local Abbreviation cm_Wc_rd_on := (CMO.cm_Wc_rd_on tp m f len S FS fb Rf Rlen HK Hfb FP0).
Local Abbreviation cm_Wc_rd_R := (CMO.cm_Wc_rd_R tp m f len S FS fb Rf Rlen S16 HK Hfb FP0).
Local Abbreviation cm_inv_mu_on := (CMO.cm_inv_mu_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS fb
  Rf Rlen HK Hfb HAE FP0).
Local Abbreviation cm_inv_step_on := (CMO.cm_inv_step_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS fb
  Rf Rlen S16 HK ST Hfb SR_on HHM HAE AW FP0).
Local Abbreviation cm_Wc_sub := (CM.cm_Wc_sub tp m f len S FS fb Rf Rlen S16 HK Hfb FP0).
Local Abbreviation cm_cls_keep := (CM.cm_cls_keep f len S FS fb Rf Rlen HK Hfb).
Local Abbreviation cm_cls_fp := (CM.cm_cls_fp FS).
Local Abbreviation cm_cls_out_Wc := (CM.cm_cls_out_Wc tp m f len S FS fb Rf Rlen S16 HK Hfb HHM HAE FP0).
Local Abbreviation cm_Wc_sh_out_on := (CMO.cm_Wc_sh_out_on tp m f len S FS fb Rf Rlen S16 HK ST Hfb SR_on HHM HAE
  AW FP0).
Local Abbreviation cm_Wc_saves := (CM.cm_Wc_saves tp m f len S FS fb Rf Rlen S16 HK Hfb HHM HAE FP0).
Local Abbreviation cm_Wc_flag := (CM.cm_Wc_flag tp m f len S FS fb Rf Rlen S16 HK Hfb HHM HAE FP0).

(* Section MatchF's cm_wv / cm_wst (an Ltac of a Section is not exported), same text. *)
Ltac cm_wv :=
  let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
  match goal with
  | |- wview _ _ (wa ?x) <> None =>
    first
      [ match goal with H : forall a, _ -> wview rsegs m (wa a) <> None |- _ => apply H; lia end
      | match goal with H : forall k, 0 <= k < 192 -> wview rsegs m (wa (?fr + k)) <> None |- _ =>
          replace x with (fr + (x - fr)) by lia; apply H; lia end
      | match goal with H : forall k, 0 <= k < 24 -> wview rsegs m (wa (?s + k)) <> None |- _ =>
          replace x with (s + (x - s)) by lia; apply H; lia end ]
  end.

Ltac cm_wst a n :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      let HS := fresh "HS" in
      assert (HS : store_ok rsegs mm (wa a) n = true)
        by (eapply wv_store_ok;
            [ cm_wv | eassumption
            | try unfold ASAN_K; Z.div_mod_to_equations; lia
            | try unfold ASAN_K; Z.div_mod_to_equations; lia ])
  end.

(* The invariant both ways: the old one gives the `_on` one (its shadow conjunct by shadow_rw_on_of_shadow_rw); the
   `_on` one gives the old one when the entry memory m has shadow_rw (shadow_rw_mono along its wmono / rd_mono). *)
Lemma cmInv_on_of_cmInv : forall fr sp2 jj nn mc, cmInv fr sp2 jj nn mc -> cmInv_on fr sp2 jj nn mc.
Proof.
  intros fr sp2 jj nn mc (FK & MU & WM & RM & MI & AC & SRc & REST).
  exact (conj FK (conj MU (conj WM (conj RM (conj MI (conj AC (conj (shadow_rw_on_of_shadow_rw _ mc SRc) REST))))))).
Qed.

Lemma cmInv_of_cmInv_on : shadow_rw m ->
  forall fr sp2 jj nn mc, cmInv_on fr sp2 jj nn mc -> cmInv fr sp2 jj nn mc.
Proof.
  intros SRm fr sp2 jj nn mc (FK & MU & WM & RM & MI & AC & _ & REST).
  exact (conj FK (conj MU (conj WM (conj RM (conj MI (conj AC (conj (shadow_rw_mono m mc SRm WM RM) REST))))))).
Qed.

(* ---- the three cut states over cmInv_on ---- *)

(* cmLHF with cmInv_on: the 11-row loop head (pc 0x846ac), row i. *)
Definition cmLHF_on (RNG : footprint) (i : nat) (Q : machine_state -> Prop) (fr sp2 jj nn : Z) : Prop :=
  forall (mc : word -> option byte)
         (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
    RcMatch.cm_gate len fb = true -> (forall j, (j < i)%nat -> nth j DECLS [] <> cm_blk fb) ->
    cmInv_on fr sp2 jj nn mc ->
    evtF rsegs RNG Q
      (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
               ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 (CM_T + 296 * Z.of_nat i))
               (Z_to_bv 64 (fr + 112)) (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr)
               (Z_to_bv 64 (11 - Z.of_nat i)) (Z_to_bv 64 1) (Z_to_bv 64 (-8)) s11 rt3 rt4 rt5 rt6)
           F (Z_to_bv 64 0x846ac) fc None mc (seg_rom rsegs)).

(* cmNoneF with cmInv_on: the no-row tail (pc 0x84700). *)
Definition cmNoneF_on (RNG : footprint) (Q : machine_state -> Prop) (fr sp2 jj nn : Z) : Prop :=
  forall (mc : word -> option byte)
         (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs3 rs4 rs5 rs8 rs9 rs10 rt3 rt4 rt5 rt6 : word),
    want CM_T len fb = 0 -> cmInv_on fr sp2 jj nn mc ->
    evtF rsegs RNG Q
      (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
               ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) rs3 rs4 rs5 (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr)
               rs8 rs9 rs10 s11 rt3 rt4 rt5 rt6)
           F (Z_to_bv 64 0x84700) fc None mc (seg_rom rsegs)).

(* cmXCF with cmInv_on: the exit cut (pc 0x84724). *)
Definition cmXCF_on (RNG : footprint) (Q : machine_state -> Prop) (fr sp2 jj nn : Z) : Prop :=
  forall (mc : word -> option byte) (r : Z)
         (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 : word),
    r = want CM_T len fb -> cmInv_on fr sp2 jj nn mc ->
    evtF rsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 CA) y0 y1 y2 y3 y4 y5 y6 y7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 r) z4 z5 (Z_to_bv 64 (shadow_addr fr))
               (Z_to_bv 64 fr) z8 z9 z10 s11 u3 u4 u5 u6)
           F (Z_to_bv 64 0x84724) fc None mc (seg_rom rsegs)).

(* ---- the stretch lemmas over cmInv_on ---- *)

(* cm_parse_F with the callee's `_on` post for reac_ctrl_parse's shadow_rw post. *)
Lemma cm_parse_F_on : forall (RNG : footprint) (Q : machine_state -> Prop) (fr sp2 jj nn : Z),
  cmLHF_on RNG 0 Q fr sp2 jj nn -> cmNoneF_on RNG Q fr sp2 jj nn ->
  forall (mc m2 : word -> option byte)
         (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
  50 <= len -> cp_v fb 12 = 0x88 -> cp_v fb 13 = 0x19 -> cp_v fb 16 = 0xcd -> cp_v fb 17 = 0xea ->
  cmInv_on fr sp2 jj nn mc ->
  munch (reac_ctrl_parse_fp (fr + 32) sp2 ++ fp_w [1%nat] FS ++
         [(shadow_addr (sp2 - REAC_CTRL_PARSE_K), shadow_addr sp2)]) mc m2 ->
  wmono rsegs mc m2 -> mem_inv rsegs m2 ->
  stk rsegs m2 (sp2 - REAC_CTRL_PARSE_K) sp2 ->
  (fr + 32 <> 0 -> rw_cells rsegs m2 (fr + 32) [CB 36 (snd (ctrlparse len fb))]) ->
  asan_cells m2 -> (forall P, shadow_rw_on P mc -> shadow_rw_on P m2) ->
  addressable m2 (sp2 - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
  fp [1%nat] m2 (bv_unsigned tp) FS (sp2 - REAC_CTRL_PARSE_K) sp2
     (reac_ctrl_parse_W (fr + 32) sp2) (reac_ctrl_parse_D f len (fr + 32)) ->
  evtF rsegs RNG Q
    (MS (mkR (Z_to_bv 64 0x84688) (Z_to_bv 64 sp2) gp tp t0' t1' t2' (Z_to_bv 64 S) (Z_to_bv 64 CA)
             (Z_to_bv 64 (fst (ctrlparse len fb))) a1' a2' a3' a4' a5' a6' a7'
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
             (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) s8 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x84688) fc None m2 (seg_rom rsegs)).
Proof.
  intros RNG Q fr sp2 jj nn KL KN mc m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
    L E12 E13 E16 E17 INV MU2 WM2 MI2 ST2 RO2 AC2 SW2 AW2 FP2.
  pose proof INV as INVk.
  destruct INV as (FK & MUg & WMg & RMg & MIg & ACg & SRg & FPg & TLg & ADg & AWXg & SVg & FLg).
  pose proof (cm_geo fr sp2 jj nn FK) as (G8 & Gfs & G16 & Gsp & Gc).
  pose proof (fk_facts_on fr sp2 jj nn FK) as (_ & FRpos & _ & _ & FAP & _ & _).
  specialize (RO2 ltac:(clear -FRpos; lia)).
  unfold reac_ctrl_parse_fp, REAC_CTRL_PARSE_K in MU2, ST2, AW2.
  replace (fr + 32 =? 0) with false in MU2 by (symmetry; apply Z.eqb_neq; clear -FRpos; lia).
  cbn [app] in MU2.
  assert (MUc : munch (cmWc fr sp2 8800 32 36 1%nat) mc m2) by exact MU2. clear MU2.
  destruct (cm_bytes_of_rw rsegs m2 (fr + 32) 36 _ RO2) as (BO2 & LO2).
  assert (RDB : forall y, fr + 32 <= y < fr + 32 + 36 -> exists b, mrd rsegs m2 (wa y) = Some b).
  { intros y Hy. apply (acl_bytes_rd m2 (fr + 32) _ y BO2). rewrite LO2.
    change (Z.of_nat 36) with 36. clear -Hy. lia. }
  pose proof FP2 as (DTx & TSx & Cx & Tx & DBx & kx & _ & _ & (_ & _ & _ & _ & STFS2) & _).
  assert (APPw : forall a, sp2 - 8800 <= a < sp2 -> app_mem a).
  { intros a Ha. replace a with (sp2 - 8800 + (a - (sp2 - 8800))) by (clear -Ha; lia).
    apply (acl_app_in mc (sp2 - 8800) 8800); [exact ADg | clear -Ha; lia]. }
  assert (RM2 : rd_mono mc m2).
  { apply (cm_Wc_rd_on fr sp2 8800 32 36 1%nat mc m2 ltac:(clear; lia) MUc RDB ST2 STFS2
             (shadow_rw_on_mono _ _ m2 (cm_Wc_rd_R sp2 8800 1%nat ltac:(clear; lia) ltac:(clear -Gsp; lia)
                ltac:(clear -Gsp; lia)) (SW2 _ SRg)) APPw
             ltac:(clear -G16; Z.div_mod_to_equations; lia)). }
  pose proof FPg as FPc.
  destruct FPc as (DT0 & TS0 & C0 & T0 & DB0 & kk0 & HT0 & HTP0 & HPl0 & H880 & H960 & HCL0 & HFS0 & HApp0 & HWd0
                   & HDd0).
  rewrite Forall_forall in HCL0.
  assert (INV2 : cmInv_on fr sp2 jj nn m2).
  { apply (cm_inv_mu_on fr sp2 jj nn mc m2 (cmWc fr sp2 8800 32 36 1%nat) INVk MUc WM2 RM2 MI2).
    - exact (cm_Wc_sub fr sp2 jj nn 8800 32 36 1%nat FK ltac:(cbn; tauto) ltac:(clear; lia) ltac:(clear; lia)
               ltac:(clear; lia) ltac:(clear; lia)).
    - intros c Hc. destruct Hc as [<-|[<-|[<-|[]]]].
      + apply (cm_cls_keep 0%nat mc m2 (cmWc fr sp2 8800 32 36 1%nat) (HCL0 0%nat ltac:(cbn; tauto)) MUc).
        * intros x Hx. exact (cm_cls_out_Wc fr sp2 jj nn 8800 32 36 1%nat 0%nat x FK ltac:(clear; lia)
            ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
            (or_introl Hx)).
        * intros x Hx. exact (cm_cls_out_Wc fr sp2 jj nn 8800 32 36 1%nat 0%nat x FK ltac:(clear; lia)
            ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
            (or_intror Hx)).
      + exact (cm_cls_fp 1%nat m2 (bv_unsigned tp) (sp2 - 8800) sp2 _ _ FP2).
      + apply (cm_cls_keep 2%nat mc m2 (cmWc fr sp2 8800 32 36 1%nat) (HCL0 2%nat ltac:(cbn; tauto)) MUc).
        * intros x Hx. exact (cm_cls_out_Wc fr sp2 jj nn 8800 32 36 1%nat 2%nat x FK ltac:(clear; lia)
            ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
            (or_introl Hx)).
        * intros x Hx. exact (cm_cls_out_Wc fr sp2 jj nn 8800 32 36 1%nat 2%nat x FK ltac:(clear; lia)
            ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
            (or_intror Hx)).
    - exact AW2.
    - intros x Hx _ Hx2.
      exact (cm_Wc_sh_out_on fr sp2 jj nn 8800 32 36 1%nat x FK ltac:(cbn; tauto) ltac:(clear; lia)
               ltac:(clear; reflexivity) ltac:(clear; lia) ltac:(clear; lia) Hx Hx2).
    - intros x Hx. exact (cm_Wc_saves fr sp2 jj nn 8800 32 36 1%nat x FK ltac:(cbn; tauto) ltac:(clear; lia)
                            ltac:(clear; lia) ltac:(clear; lia) Hx).
    - intros Enn x Hx. exact (cm_Wc_flag fr sp2 jj nn 8800 32 36 1%nat x FK Enn ltac:(clear; lia)
                                ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) Hx). }
  (* 0x84688 li a1,9 ; 0x8468c bne a0,a1,0x84700 *)
  step. step.
  pose proof (ctrlparse_kind_range len fb) as KR.
  rewrite cm_eqb_lit by (clear -KR; lia).
  destruct (Z.eqb_spec (fst (ctrlparse len fb)) 9) as [K9|K9]; cbn [negb]; cbv iota.
  - assert (G : RcMatch.cm_gate len fb = true).
    { unfold RcMatch.cm_gate. rewrite (proj2 (Z.leb_le 50 len) L), E12, E13, E16, E17, K9. reflexivity. }
    (* 0x84690 .. 0x846a8: s4 = s7 + 112, s5 = s3 + 18, s8 = 11, a0 = auipc, s9 = 1, s3 = 0x9e800, s10 = -8 *)
    do 7 step.
    eapply KL; [exact G | intros j Hj; clear -Hj; lia | exact INV2].
  - eapply KN; [| exact INV2].
    apply cm_gate_false. unfold RcMatch.cm_gate. rewrite (proj2 (Z.eqb_neq _ _) K9).
    rewrite !andb_false_r. reflexivity.
Qed.

(* cm_tail_F over cmInv_on. *)
Lemma cm_tail_F_on : forall (RNG : footprint) (Q : machine_state -> Prop) (fr sp2 jj nn : Z),
  cmXCF_on RNG Q fr sp2 jj nn ->
  forall (mc : word -> option byte) (r : Z)
         (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 : word),
  r = want CM_T len fb -> cmInv_on fr sp2 jj nn mc ->
  rng RNG (shadow_addr fr + 4) 5 ->
  evtF rsegs RNG Q
    (MS (mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 CA) y0 y1 y2 y3 y4 y5 y6 y7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 r) z4 z5 (Z_to_bv 64 (shadow_addr fr))
             (Z_to_bv 64 fr) z8 z9 z10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x84704) fc None mc (seg_rom rsegs)).
Proof.
  intros RNG Q fr sp2 jj nn KX mc r x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 Er INVk RSH.
  pose proof INVk as INV.
  destruct INV as (FK & MUg & WMg & RMg & MIg & ACg & SRg & FPg & TLg & ADg & AWXg & SVg & FLg).
  clear MUg.
  pose proof (fk_facts_on fr sp2 jj nn FK) as (FR8 & FRpos & FR192 & FW & FAP & FSW & _).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (FRgt & FRhi).
  assert (SHlo : 0 <= shadow_addr fr).
  { unfold shadow_addr. assert (D : 0 <= fr / 8) by (apply Z.div_pos; clear -FRpos; lia).
    unfold ASAN_K. clear -D. lia. }
  assert (SHhi : shadow_addr fr + 24 <= 2 ^ 64).
  { unfold shadow_addr, ASAN_K. clear -FRpos FRhi RS. Z.div_mod_to_equations. lia. }
  assert (FSW' : forall k, 0 <= k < 24 -> wview rsegs m (wa (shadow_addr fr + k)) <> None) by exact FSW.
  clear FSW.
  assert (MUh : munch (cmHF fr) mc mc) by apply munch_refl.
  assert (WMh : wmono rsegs mc mc) by apply wmono_refl.
  assert (RMh : rd_mono mc mc) by apply rd_mono_refl.
  unfold CM.cmHF in MUh.
  (* 0x84704 li a0,-8 ; 0x84708 .. 0x84718 sb a0,4..8(s6) ; 0x8471c j 0x84724 *)
  step.
  cm_wst (shadow_addr fr + 4) 1%nat. step. store_done.
  cm_wst (shadow_addr fr + 5) 1%nat. step. store_done.
  cm_wst (shadow_addr fr + 6) 1%nat. step. store_done.
  cm_wst (shadow_addr fr + 7) 1%nat. step. store_done.
  cm_wst (shadow_addr fr + 8) 1%nat. step. store_done.
  step.
  eapply (KX _ r); [exact Er|].
  eapply cm_inv_step_on; [exact INVk | exact MUh | exact WMh | exact RMh | exact MIg].
Qed.

(* cm_none_F over cmInv_on. *)
Lemma cm_none_F_on : forall (RNG : footprint) (Q : machine_state -> Prop) (fr sp2 jj nn : Z),
  cmXCF_on RNG Q fr sp2 jj nn ->
  rng RNG (shadow_addr fr + 4) 5 ->
  cmNoneF_on RNG Q fr sp2 jj nn.
Proof.
  intros RNG Q fr sp2 jj nn KX RSH mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs3 rs4 rs5 rs8 rs9 rs10
    rt3 rt4 rt5 rt6 Hw INVk.
  (* 0x84700 li s3,0 *)
  step.
  exact (cm_tail_F_on RNG Q fr sp2 jj nn KX mc 0 rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs4 rs5 rs8 rs9
           rs10 rt3 rt4 rt5 rt6 ltac:(symmetry; exact Hw) INVk RSH).
Qed.

(* cm_parse_S3_F over cmInv_on, with the callee's `_on` post. *)
Lemma cm_parse_S3_F_on : forall (RNG : footprint) (Q : machine_state -> Prop) (fr sp2 jj nn : Z),
  cmLHF_on RNG 0 Q fr sp2 jj nn -> cmXCF_on RNG Q fr sp2 jj nn ->
  rng RNG (shadow_addr fr + 4) 5 ->
  forall (mc m2 : word -> option byte)
         (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
  50 <= len -> cp_v fb 12 = 0x88 -> cp_v fb 13 = 0x19 -> cp_v fb 16 = 0xcd -> cp_v fb 17 = 0xea ->
  cmInv_on fr sp2 jj nn mc ->
  munch (reac_ctrl_parse_fp (fr + 32) sp2 ++ fp_w [1%nat] FS ++
         [(shadow_addr (sp2 - REAC_CTRL_PARSE_K), shadow_addr sp2)]) mc m2 ->
  wmono rsegs mc m2 -> mem_inv rsegs m2 ->
  stk rsegs m2 (sp2 - REAC_CTRL_PARSE_K) sp2 ->
  (fr + 32 <> 0 -> rw_cells rsegs m2 (fr + 32) [CB 36 (snd (ctrlparse len fb))]) ->
  asan_cells m2 -> (forall P, shadow_rw_on P mc -> shadow_rw_on P m2) ->
  addressable m2 (sp2 - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
  fp [1%nat] m2 (bv_unsigned tp) FS (sp2 - REAC_CTRL_PARSE_K) sp2
     (reac_ctrl_parse_W (fr + 32) sp2) (reac_ctrl_parse_D f len (fr + 32)) ->
  evtF rsegs RNG Q
    (MS (mkR (Z_to_bv 64 0x84688) (Z_to_bv 64 sp2) gp tp t0' t1' t2' (Z_to_bv 64 S) (Z_to_bv 64 CA)
             (Z_to_bv 64 (fst (ctrlparse len fb))) a1' a2' a3' a4' a5' a6' a7'
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
             (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) s8 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x84688) fc None m2 (seg_rom rsegs)).
Proof.
  intros RNG Q fr sp2 jj nn KL KX RSH.
  apply (cm_parse_F_on RNG Q fr sp2 jj nn KL (cm_none_F_on RNG Q fr sp2 jj nn KX RSH)).
Qed.

(* cm_parse_rb_F over cmInv_on (the base memory m carries cmInv_on). *)
Lemma cm_parse_rb_F_on : forall (RNG : footprint) (Q : machine_state -> Prop) (fr sp2 jj nn : Z),
  cmLHF_on RNG 0 Q fr sp2 jj nn -> cmNoneF_on RNG Q fr sp2 jj nn ->
  forall (rr t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
  50 <= len -> cp_v fb 12 = 0x88 -> cp_v fb 13 = 0x19 -> cp_v fb 16 = 0xcd -> cp_v fb 17 = 0xea ->
  cmInv_on fr sp2 jj nn m ->
  evtF rsegs RNG Q
    (MS (mkR rr (Z_to_bv 64 sp2) gp tp t0' t1' t2' (Z_to_bv 64 S) (Z_to_bv 64 CA)
             (Z_to_bv 64 (fst (ctrlparse len fb))) a1' a2' a3' a4' a5' a6' a7'
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
             (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) s8 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x84688) fc None m (seg_rom rsegs)).
Proof.
  intros RNG Q fr sp2 jj nn KL KN rr t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
    L E12 E13 E16 E17 INV2.
  (* 0x84688 li a1,9 ; 0x8468c bne a0,a1,0x84700 *)
  step. step.
  pose proof (ctrlparse_kind_range len fb) as KR.
  rewrite cm_eqb_lit by (clear -KR; lia).
  destruct (Z.eqb_spec (fst (ctrlparse len fb)) 9) as [K9|K9]; cbn [negb]; cbv iota.
  - assert (G : RcMatch.cm_gate len fb = true).
    { unfold RcMatch.cm_gate. rewrite (proj2 (Z.leb_le 50 len) L), E12, E13, E16, E17, K9. reflexivity. }
    (* 0x84690 .. 0x846a8: s4 = s7 + 112, s5 = s3 + 18, s8 = 11, a0 = auipc, s9 = 1, s3 = 0x9e800, s10 = -8 *)
    do 7 step.
    eapply KL; [exact G | intros j Hj; clear -Hj; lia | exact INV2].
  - eapply KN; [| exact INV2].
    apply cm_gate_false. unfold RcMatch.cm_gate. rewrite (proj2 (Z.eqb_neq _ _) K9).
    rewrite !andb_false_r. reflexivity.
Qed.

(* cm_parse_S3_rb_F over cmInv_on: the whole re-based stretch. *)
Lemma cm_parse_S3_rb_F_on : forall (RNG : footprint) (Q : machine_state -> Prop) (fr sp2 jj nn : Z),
  cmLHF_on RNG 0 Q fr sp2 jj nn -> cmXCF_on RNG Q fr sp2 jj nn ->
  rng RNG (shadow_addr fr + 4) 5 ->
  forall (rr t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
  50 <= len -> cp_v fb 12 = 0x88 -> cp_v fb 13 = 0x19 -> cp_v fb 16 = 0xcd -> cp_v fb 17 = 0xea ->
  cmInv_on fr sp2 jj nn m ->
  evtF rsegs RNG Q
    (MS (mkR rr (Z_to_bv 64 sp2) gp tp t0' t1' t2' (Z_to_bv 64 S) (Z_to_bv 64 CA)
             (Z_to_bv 64 (fst (ctrlparse len fb))) a1' a2' a3' a4' a5' a6' a7'
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
             (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) s8 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x84688) fc None m (seg_rom rsegs)).
Proof.
  intros RNG Q fr sp2 jj nn KL KX RSH.
  apply (cm_parse_rb_F_on RNG Q fr sp2 jj nn KL (cm_none_F_on RNG Q fr sp2 jj nn KX RSH)).
Qed.

(* cm_parse_of_F over cmInv_on, with the callee's `_on` post. *)
Corollary cm_parse_of_F_on : forall (Q : machine_state -> Prop) (fr sp2 jj nn : Z),
  cmLHF_on RNG_all 0 Q fr sp2 jj nn -> cmNoneF_on RNG_all Q fr sp2 jj nn ->
  forall (mc m2 : word -> option byte)
         (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
  50 <= len -> cp_v fb 12 = 0x88 -> cp_v fb 13 = 0x19 -> cp_v fb 16 = 0xcd -> cp_v fb 17 = 0xea ->
  cmInv_on fr sp2 jj nn mc ->
  munch (reac_ctrl_parse_fp (fr + 32) sp2 ++ fp_w [1%nat] FS ++
         [(shadow_addr (sp2 - REAC_CTRL_PARSE_K), shadow_addr sp2)]) mc m2 ->
  wmono rsegs mc m2 -> mem_inv rsegs m2 ->
  stk rsegs m2 (sp2 - REAC_CTRL_PARSE_K) sp2 ->
  (fr + 32 <> 0 -> rw_cells rsegs m2 (fr + 32) [CB 36 (snd (ctrlparse len fb))]) ->
  asan_cells m2 -> (forall P, shadow_rw_on P mc -> shadow_rw_on P m2) ->
  addressable m2 (sp2 - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
  fp [1%nat] m2 (bv_unsigned tp) FS (sp2 - REAC_CTRL_PARSE_K) sp2
     (reac_ctrl_parse_W (fr + 32) sp2) (reac_ctrl_parse_D f len (fr + 32)) ->
  evt rsegs Q
    (MS (mkR (Z_to_bv 64 0x84688) (Z_to_bv 64 sp2) gp tp t0' t1' t2' (Z_to_bv 64 S) (Z_to_bv 64 CA)
             (Z_to_bv 64 (fst (ctrlparse len fb))) a1' a2' a3' a4' a5' a6' a7'
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
             (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) s8 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x84688) fc None m2 (seg_rom rsegs)).
Proof.
  intros Q fr sp2 jj nn KL KN mc m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'.
  intros L E12 E13 E16 E17 INV MU2 WM2 MI2 ST2 RO2 AC2 SW2 AW2 FP2.
  eapply evtF_evt.
  exact (cm_parse_F_on RNG_all Q fr sp2 jj nn KL KN mc m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
           L E12 E13 E16 E17 INV MU2 WM2 MI2 ST2 RO2 AC2 SW2 AW2 FP2).
Qed.

(* cm_tail_of_F over cmInv_on. *)
Corollary cm_tail_of_F_on : forall (Q : machine_state -> Prop) (fr sp2 jj nn : Z),
  cmXCF_on RNG_all Q fr sp2 jj nn ->
  forall (mc : word -> option byte) (r : Z)
         (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 : word),
  r = want CM_T len fb -> cmInv_on fr sp2 jj nn mc ->
  evt rsegs Q
    (MS (mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 CA) y0 y1 y2 y3 y4 y5 y6 y7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 r) z4 z5 (Z_to_bv 64 (shadow_addr fr))
             (Z_to_bv 64 fr) z8 z9 z10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x84704) fc None mc (seg_rom rsegs)).
Proof.
  intros Q fr sp2 jj nn KX mc r x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 Er INVk.
  pose proof INVk as INV. destruct INV as (FK & _).
  pose proof (fk_facts_on fr sp2 jj nn FK) as (_ & FRpos & _).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (FRgt & FRhi).
  eapply evtF_evt.
  apply (cm_tail_F_on RNG_all Q fr sp2 jj nn KX mc r x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5
           u6 Er INVk).
  apply rng_all; unfold shadow_addr, ASAN_K; clear -FRpos FRhi RS; Z.div_mod_to_equations; lia.
Qed.

(* cm_none_of_F over cmInv_on. *)
Corollary cm_none_of_F_on : forall (Q : machine_state -> Prop) (fr sp2 jj nn : Z),
  cmXCF_on RNG_all Q fr sp2 jj nn -> cmNoneF_on RNG_all Q fr sp2 jj nn.
Proof.
  intros Q fr sp2 jj nn KX mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs3 rs4 rs5 rs8 rs9 rs10
    rt3 rt4 rt5 rt6 Hw INVk.
  pose proof INVk as INV. destruct INV as (FK & _).
  pose proof (fk_facts_on fr sp2 jj nn FK) as (_ & FRpos & _).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (FRgt & FRhi).
  assert (RSH : rng RNG_all (shadow_addr fr + 4) 5)
    by (apply rng_all; unfold shadow_addr, ASAN_K; clear -FRpos FRhi RS; Z.div_mod_to_equations; lia).
  exact (cm_none_F_on RNG_all Q fr sp2 jj nn KX RSH mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs3 rs4 rs5
           rs8 rs9 rs10 rt3 rt4 rt5 rt6 Hw INVk).
Qed.

End MatchFOn.

(* Section MatchF's corollaries: an old continuation K (over cmInv) gives the `_on` one (over cmInv_on), C being
   cmInv_of_cmInv_on at a shadow_rw of the entry memory. *)
Local Ltac cm_cont_of K C := hnf; intros; eapply K; try eassumption; apply C; eassumption.

Section MatchF.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (f len S FS : Z) (fb : list byte).
(* The Section hypotheses of reac_box_catalogue_match.v that this stretch's lemmas need. The four callee contracts
   (HPC / HMB / HBC / HSM) are not among them: this stretch calls nothing. *)
Hypothesis Rf : 0 <= f < 2^64.
Hypothesis Rlen : 0 <= len < 2^64.
Hypothesis RS : S < 2^64.
Hypothesis S16 : S mod 16 = 0.
Hypothesis HK : 9136 <= S.
Hypothesis ST : stk rsegs m (S - 9136) S.
Hypothesis Hfb : length fb = 50%nat.
Hypothesis SR : shadow_rw m.
Hypothesis HHM : HIGHMEM_BEG <= S - 9136.
Hypothesis HAE : S <= APPMEM_END.
Hypothesis AW : addressable m (S - 9136) 9136.
Hypothesis FP0 : fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (S - 9136) S
  (reac_box_catalogue_match_W S) (reac_box_catalogue_match_D f len).

(* The source's Section names at this Section's state: each one is the exported constant applied to the Section
   variables and hypotheses it was generalized over, so the proof scripts below read as they do in the source. *)
Local Notation CA := (CM.CA S).
Local Notation cmFK := (CM.cmFK S FS).
Local Notation cmWc := (CM.cmWc FS).
Local Notation cmHF := (CM.cmHF S).
Local Notation cmInv := (CM.cmInv ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS).
Local Notation cm_geo := (CM.cm_geo tp m f len S FS fb Rf Rlen S16 HK Hfb FP0).
Local Notation fk_facts := (CM.fk_facts tp m f len S FS fb Rf Rlen S16 HK ST Hfb SR AW FP0).
Local Notation cm_fr_bounds := (CM.cm_fr_bounds tp m f len S FS fb Rf Rlen S16 HK Hfb HHM FP0).
Local Notation cm_Wc_rd := (CM.cm_Wc_rd tp m f len S FS fb Rf Rlen HK Hfb FP0).
Local Notation cm_inv_mu := (CM.cm_inv_mu ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS fb
  Rf Rlen HK Hfb HAE FP0).
Local Notation cm_inv_step := (CM.cm_inv_step ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS fb
  Rf Rlen S16 HK ST Hfb SR HHM HAE AW FP0).
Local Notation cm_Wc_sub := (CM.cm_Wc_sub tp m f len S FS fb Rf Rlen S16 HK Hfb FP0).
Local Notation cm_cls_keep := (CM.cm_cls_keep f len S FS fb Rf Rlen HK Hfb).
Local Notation cm_cls_fp := (CM.cm_cls_fp FS).
Local Notation cm_cls_out_Wc := (CM.cm_cls_out_Wc tp m f len S FS fb Rf Rlen S16 HK Hfb HHM HAE FP0).
Local Notation cm_Wc_sh_out := (CM.cm_Wc_sh_out tp m f len S FS fb Rf Rlen S16 HK ST Hfb SR HHM HAE AW FP0).
Local Notation cm_Wc_saves := (CM.cm_Wc_saves tp m f len S FS fb Rf Rlen S16 HK Hfb HHM HAE FP0).
Local Notation cm_Wc_flag := (CM.cm_Wc_flag tp m f len S FS fb Rf Rlen S16 HK Hfb HHM HAE FP0).

(* reac_box_catalogue_match.v's file-local cm_wv / cm_wst, with evtF in the goal pattern (StepF's step leaves an
   evtF goal); the tactic text is otherwise that of the source (lines 639-658). *)
Ltac cm_wv :=
  let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
  match goal with
  | |- wview _ _ (wa ?x) <> None =>
    first
      [ match goal with H : forall a, _ -> wview rsegs m (wa a) <> None |- _ => apply H; lia end
      | match goal with H : forall k, 0 <= k < 192 -> wview rsegs m (wa (?fr + k)) <> None |- _ =>
          replace x with (fr + (x - fr)) by lia; apply H; lia end
      | match goal with H : forall k, 0 <= k < 24 -> wview rsegs m (wa (?s + k)) <> None |- _ =>
          replace x with (s + (x - s)) by lia; apply H; lia end ]
  end.

Ltac cm_wst a n :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      let HS := fresh "HS" in
      assert (HS : store_ok rsegs mm (wa a) n = true)
        by (eapply wv_store_ok;
            [ cm_wv | eassumption
            | try unfold ASAN_K; Z.div_mod_to_equations; lia
            | try unfold ASAN_K; Z.div_mod_to_equations; lia ])
  end.

(* ---- the three cut states of this stretch, as ExecF.evtF continuations under RNG ---- *)

(* The 11-row loop head (pc 0x846ac), row i: cmLH's state. *)
Definition cmLHF (RNG : footprint) (i : nat) (Q : machine_state -> Prop) (fr sp2 jj nn : Z) : Prop :=
  forall (mc : word -> option byte)
         (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
    RcMatch.cm_gate len fb = true -> (forall j, (j < i)%nat -> nth j DECLS [] <> cm_blk fb) ->
    cmInv fr sp2 jj nn mc ->
    evtF rsegs RNG Q
      (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
               ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 (CM_T + 296 * Z.of_nat i))
               (Z_to_bv 64 (fr + 112)) (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr)
               (Z_to_bv 64 (11 - Z.of_nat i)) (Z_to_bv 64 1) (Z_to_bv 64 (-8)) s11 rt3 rt4 rt5 rt6)
           F (Z_to_bv 64 0x846ac) fc None mc (seg_rom rsegs)).

(* The no-row tail (pc 0x84700): cmNone's state. *)
Definition cmNoneF (RNG : footprint) (Q : machine_state -> Prop) (fr sp2 jj nn : Z) : Prop :=
  forall (mc : word -> option byte)
         (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs3 rs4 rs5 rs8 rs9 rs10 rt3 rt4 rt5 rt6 : word),
    want CM_T len fb = 0 -> cmInv fr sp2 jj nn mc ->
    evtF rsegs RNG Q
      (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
               ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) rs3 rs4 rs5 (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr)
               rs8 rs9 rs10 s11 rt3 rt4 rt5 rt6)
           F (Z_to_bv 64 0x84700) fc None mc (seg_rom rsegs)).

(* The exit cut (pc 0x84724): the start state of cm_exit, which is stretch S6's start. *)
Definition cmXCF (RNG : footprint) (Q : machine_state -> Prop) (fr sp2 jj nn : Z) : Prop :=
  forall (mc : word -> option byte) (r : Z)
         (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 : word),
    r = want CM_T len fb -> cmInv fr sp2 jj nn mc ->
    evtF rsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 CA) y0 y1 y2 y3 y4 y5 y6 y7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 r) z4 z5 (Z_to_bv 64 (shadow_addr fr))
               (Z_to_bv 64 fr) z8 z9 z10 s11 u3 u4 u5 u6)
           F (Z_to_bv 64 0x84724) fc None mc (seg_rom rsegs)).

(* ---- 0x84688 -> 0x846ac (parse result 9) or 0x84700 (not 9): cm_parse after the call ---- *)

(* The premises are reac_ctrl_parse_contract's post at this call site (o := fr + 32, S := sp2, n := len, fr := fb),
   which is what the source script destructs at the return; the state is the post's state with ra = 0x84688
   (ret_pc_even) and a0 = fst (ctrlparse len fb). The run is `li a1,9`, `bne a0,a1,0x84700` and, on the equal side,
   the seven register instructions that set up row 0 (s4 = fr + 112, s5 = f + 18, s8 = 11, s9 = 1,
   s3 = CM_T = BOX_CATALOGUE, s10 = -8); none of them accesses memory. *)
Lemma cm_parse_F : forall (RNG : footprint) (Q : machine_state -> Prop) (fr sp2 jj nn : Z),
  cmLHF RNG 0 Q fr sp2 jj nn -> cmNoneF RNG Q fr sp2 jj nn ->
  forall (mc m2 : word -> option byte)
         (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
  50 <= len -> cp_v fb 12 = 0x88 -> cp_v fb 13 = 0x19 -> cp_v fb 16 = 0xcd -> cp_v fb 17 = 0xea ->
  cmInv fr sp2 jj nn mc ->
  munch (reac_ctrl_parse_fp (fr + 32) sp2 ++ fp_w [1%nat] FS ++
         [(shadow_addr (sp2 - REAC_CTRL_PARSE_K), shadow_addr sp2)]) mc m2 ->
  wmono rsegs mc m2 -> mem_inv rsegs m2 ->
  stk rsegs m2 (sp2 - REAC_CTRL_PARSE_K) sp2 ->
  (fr + 32 <> 0 -> rw_cells rsegs m2 (fr + 32) [CB 36 (snd (ctrlparse len fb))]) ->
  asan_cells m2 -> shadow_rw m2 ->
  addressable m2 (sp2 - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
  fp [1%nat] m2 (bv_unsigned tp) FS (sp2 - REAC_CTRL_PARSE_K) sp2
     (reac_ctrl_parse_W (fr + 32) sp2) (reac_ctrl_parse_D f len (fr + 32)) ->
  evtF rsegs RNG Q
    (MS (mkR (Z_to_bv 64 0x84688) (Z_to_bv 64 sp2) gp tp t0' t1' t2' (Z_to_bv 64 S) (Z_to_bv 64 CA)
             (Z_to_bv 64 (fst (ctrlparse len fb))) a1' a2' a3' a4' a5' a6' a7'
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
             (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) s8 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x84688) fc None m2 (seg_rom rsegs)).
Proof.
  intros RNG Q fr sp2 jj nn KL KN.
  assert (KL' : cmLHF_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb RNG 0 Q fr sp2 jj nn)
    by (cm_cont_of KL (cmInv_of_cmInv_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS SR)).
  assert (KN' : cmNoneF_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb RNG Q fr sp2 jj nn)
    by (cm_cont_of KN (cmInv_of_cmInv_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS SR)).
  intros mc m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
    L E12 E13 E16 E17 INV MU2 WM2 MI2 ST2 RO2 AC2 SW2 AW2 FP2.
  exact (cm_parse_F_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb
           Rf Rlen S16 HK ST Hfb (shadow_rw_on_of_shadow_rw _ m SR) HHM HAE AW FP0
           RNG Q fr sp2 jj nn KL' KN' mc m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
           L E12 E13 E16 E17
           (cmInv_on_of_cmInv ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS fr sp2 jj nn mc INV)
           MU2 WM2 MI2 ST2 RO2 AC2 (fun P _ => shadow_rw_on_of_shadow_rw P m2 SW2) AW2 FP2).
Qed.

(* ---- 0x84704 -> 0x84724: cm_tail up to the exit cut ---- *)

(* The five shadow bytes 4 .. 8 of the frame (the parse buffer) are set to 0xf8, then the run joins the exit at
   0x84724 (cmXCF; the source hands it to cm_exit there). *)
Lemma cm_tail_F : forall (RNG : footprint) (Q : machine_state -> Prop) (fr sp2 jj nn : Z),
  cmXCF RNG Q fr sp2 jj nn ->
  forall (mc : word -> option byte) (r : Z)
         (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 : word),
  r = want CM_T len fb -> cmInv fr sp2 jj nn mc ->
  rng RNG (shadow_addr fr + 4) 5 ->
  evtF rsegs RNG Q
    (MS (mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 CA) y0 y1 y2 y3 y4 y5 y6 y7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 r) z4 z5 (Z_to_bv 64 (shadow_addr fr))
             (Z_to_bv 64 fr) z8 z9 z10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x84704) fc None mc (seg_rom rsegs)).
Proof.
  intros RNG Q fr sp2 jj nn KX.
  assert (KX' : cmXCF_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb RNG Q fr sp2 jj nn)
    by (cm_cont_of KX (cmInv_of_cmInv_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS SR)).
  intros mc r x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 Er INVk RSH.
  exact (cm_tail_F_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb
           Rf Rlen RS S16 HK ST Hfb (shadow_rw_on_of_shadow_rw _ m SR) HHM HAE AW FP0
           RNG Q fr sp2 jj nn KX' mc r x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 Er
           (cmInv_on_of_cmInv ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS fr sp2 jj nn mc INVk) RSH).
Qed.

(* ---- 0x84700 -> 0x84704: cm_none_holds ---- *)

(* The result register s3 is set to 0 and the run joins the no-match join (cm_tail_F) with r = 0 = want CM_T len fb.
   The rng premise is cm_tail_F's, at this lemma's own frame parameter. *)
Lemma cm_none_F : forall (RNG : footprint) (Q : machine_state -> Prop) (fr sp2 jj nn : Z),
  cmXCF RNG Q fr sp2 jj nn ->
  rng RNG (shadow_addr fr + 4) 5 ->
  cmNoneF RNG Q fr sp2 jj nn.
Proof.
  intros RNG Q fr sp2 jj nn KX RSH.
  assert (KX' : cmXCF_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb RNG Q fr sp2 jj nn)
    by (cm_cont_of KX (cmInv_of_cmInv_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS SR)).
  intros mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs3 rs4 rs5 rs8 rs9 rs10 rt3 rt4 rt5 rt6 Hw INVk.
  exact (cm_none_F_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb
           Rf Rlen RS S16 HK ST Hfb (shadow_rw_on_of_shadow_rw _ m SR) HHM HAE AW FP0
           RNG Q fr sp2 jj nn KX' RSH mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs3 rs4 rs5 rs8 rs9 rs10
           rt3 rt4 rt5 rt6 Hw
           (cmInv_on_of_cmInv ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS fr sp2 jj nn mc INVk)).
Qed.

(* ---- the whole stretch S3 ---- *)

(* 0x84688 -> 0x846ac (parse result 9), or 0x84688 -> 0x84700 -> 0x84704 -> the exit cut 0x84724 (not 9). *)
Lemma cm_parse_S3_F : forall (RNG : footprint) (Q : machine_state -> Prop) (fr sp2 jj nn : Z),
  cmLHF RNG 0 Q fr sp2 jj nn -> cmXCF RNG Q fr sp2 jj nn ->
  rng RNG (shadow_addr fr + 4) 5 ->
  forall (mc m2 : word -> option byte)
         (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
  50 <= len -> cp_v fb 12 = 0x88 -> cp_v fb 13 = 0x19 -> cp_v fb 16 = 0xcd -> cp_v fb 17 = 0xea ->
  cmInv fr sp2 jj nn mc ->
  munch (reac_ctrl_parse_fp (fr + 32) sp2 ++ fp_w [1%nat] FS ++
         [(shadow_addr (sp2 - REAC_CTRL_PARSE_K), shadow_addr sp2)]) mc m2 ->
  wmono rsegs mc m2 -> mem_inv rsegs m2 ->
  stk rsegs m2 (sp2 - REAC_CTRL_PARSE_K) sp2 ->
  (fr + 32 <> 0 -> rw_cells rsegs m2 (fr + 32) [CB 36 (snd (ctrlparse len fb))]) ->
  asan_cells m2 -> shadow_rw m2 ->
  addressable m2 (sp2 - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
  fp [1%nat] m2 (bv_unsigned tp) FS (sp2 - REAC_CTRL_PARSE_K) sp2
     (reac_ctrl_parse_W (fr + 32) sp2) (reac_ctrl_parse_D f len (fr + 32)) ->
  evtF rsegs RNG Q
    (MS (mkR (Z_to_bv 64 0x84688) (Z_to_bv 64 sp2) gp tp t0' t1' t2' (Z_to_bv 64 S) (Z_to_bv 64 CA)
             (Z_to_bv 64 (fst (ctrlparse len fb))) a1' a2' a3' a4' a5' a6' a7'
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
             (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) s8 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x84688) fc None m2 (seg_rom rsegs)).
Proof.
  intros RNG Q fr sp2 jj nn KL KX RSH.
  assert (KL' : cmLHF_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb RNG 0 Q fr sp2 jj nn)
    by (cm_cont_of KL (cmInv_of_cmInv_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS SR)).
  assert (KX' : cmXCF_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb RNG Q fr sp2 jj nn)
    by (cm_cont_of KX (cmInv_of_cmInv_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS SR)).
  intros mc m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
    L E12 E13 E16 E17 INV MU2 WM2 MI2 ST2 RO2 AC2 SW2 AW2 FP2.
  exact (cm_parse_S3_F_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb
           Rf Rlen RS S16 HK ST Hfb (shadow_rw_on_of_shadow_rw _ m SR) HHM HAE AW FP0
           RNG Q fr sp2 jj nn KL' KX' RSH mc m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
           L E12 E13 E16 E17
           (cmInv_on_of_cmInv ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS fr sp2 jj nn mc INV)
           MU2 WM2 MI2 ST2 RO2 AC2 (fun P _ => shadow_rw_on_of_shadow_rw P m2 SW2) AW2 FP2).
Qed.

(* ---- the re-based form of the stretch (a Theorem Labs lane's rebase-interfaces.md 2.2 (a working note, not in this delivery)) ---- *)

(* The walk re-bases the stretch by taking this Section's entry memory `m` to be the BASE memory of the stretch
   (the normalized return memory of the reac_ctrl_parse event), so the pre-call memory mc and the plain parse post
   disappear: the only thing the dropped premises fed was the cm_inv_mu / cm_Wc_rd rebuild of cmInv at the return
   memory (in cm_parse_F_on above), which the base gives directly as `cmInv fr sp2 jj nn m`. x1 is free (`rr`):
   the cgif core does not preserve the link register (G2). The body is the instruction run of cm_parse_F unchanged. *)
Lemma cm_parse_rb_F : forall (RNG : footprint) (Q : machine_state -> Prop) (fr sp2 jj nn : Z),
  cmLHF RNG 0 Q fr sp2 jj nn -> cmNoneF RNG Q fr sp2 jj nn ->
  forall (rr t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
  50 <= len -> cp_v fb 12 = 0x88 -> cp_v fb 13 = 0x19 -> cp_v fb 16 = 0xcd -> cp_v fb 17 = 0xea ->
  cmInv fr sp2 jj nn m ->
  evtF rsegs RNG Q
    (MS (mkR rr (Z_to_bv 64 sp2) gp tp t0' t1' t2' (Z_to_bv 64 S) (Z_to_bv 64 CA)
             (Z_to_bv 64 (fst (ctrlparse len fb))) a1' a2' a3' a4' a5' a6' a7'
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
             (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) s8 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x84688) fc None m (seg_rom rsegs)).
Proof.
  intros RNG Q fr sp2 jj nn KL KN rr t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
    L E12 E13 E16 E17 INV2.
  (* The base memory's shadow_rw comes from INV2 itself: this lemma takes no Section hypothesis, nor does its
     corollary proof. *)
  pose proof INV2 as (_ & _ & _ & _ & _ & _ & SRm & _).
  assert (KL' : cmLHF_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb RNG 0 Q fr sp2 jj nn)
    by (cm_cont_of KL (cmInv_of_cmInv_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS SRm)).
  assert (KN' : cmNoneF_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb RNG Q fr sp2 jj nn)
    by (cm_cont_of KN (cmInv_of_cmInv_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS SRm)).
  exact (cm_parse_rb_F_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb
           RNG Q fr sp2 jj nn KL' KN' rr t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
           L E12 E13 E16 E17
           (cmInv_on_of_cmInv ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS fr sp2 jj nn m INV2)).
Qed.

(* The whole re-based stretch: 0x84688 -> 0x846ac, or 0x84688 -> 0x84700 -> 0x84704 -> the exit cut 0x84724. *)
Lemma cm_parse_S3_rb_F : forall (RNG : footprint) (Q : machine_state -> Prop) (fr sp2 jj nn : Z),
  cmLHF RNG 0 Q fr sp2 jj nn -> cmXCF RNG Q fr sp2 jj nn ->
  rng RNG (shadow_addr fr + 4) 5 ->
  forall (rr t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
  50 <= len -> cp_v fb 12 = 0x88 -> cp_v fb 13 = 0x19 -> cp_v fb 16 = 0xcd -> cp_v fb 17 = 0xea ->
  cmInv fr sp2 jj nn m ->
  evtF rsegs RNG Q
    (MS (mkR rr (Z_to_bv 64 sp2) gp tp t0' t1' t2' (Z_to_bv 64 S) (Z_to_bv 64 CA)
             (Z_to_bv 64 (fst (ctrlparse len fb))) a1' a2' a3' a4' a5' a6' a7'
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
             (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) s8 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x84688) fc None m (seg_rom rsegs)).
Proof.
  intros RNG Q fr sp2 jj nn KL KX RSH.
  assert (KL' : cmLHF_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb RNG 0 Q fr sp2 jj nn)
    by (cm_cont_of KL (cmInv_of_cmInv_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS SR)).
  assert (KX' : cmXCF_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb RNG Q fr sp2 jj nn)
    by (cm_cont_of KX (cmInv_of_cmInv_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS SR)).
  intros rr t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' L E12 E13 E16 E17 INV2.
  exact (cm_parse_S3_rb_F_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb
           Rf Rlen RS S16 HK ST Hfb (shadow_rw_on_of_shadow_rw _ m SR) HHM HAE AW FP0
           RNG Q fr sp2 jj nn KL' KX' RSH rr t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
           L E12 E13 E16 E17
           (cmInv_on_of_cmInv ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS fr sp2 jj nn m INV2)).
Qed.

(* ---- the corollaries at ExecF.rng_all ---- *)

(* cm_parse_F adds no footprint premise, so at RNG_all it is the stretch's Exec.evt statement itself. *)
Corollary cm_parse_of_F : forall (Q : machine_state -> Prop) (fr sp2 jj nn : Z),
  cmLHF RNG_all 0 Q fr sp2 jj nn -> cmNoneF RNG_all Q fr sp2 jj nn ->
  forall (mc m2 : word -> option byte)
         (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
  50 <= len -> cp_v fb 12 = 0x88 -> cp_v fb 13 = 0x19 -> cp_v fb 16 = 0xcd -> cp_v fb 17 = 0xea ->
  cmInv fr sp2 jj nn mc ->
  munch (reac_ctrl_parse_fp (fr + 32) sp2 ++ fp_w [1%nat] FS ++
         [(shadow_addr (sp2 - REAC_CTRL_PARSE_K), shadow_addr sp2)]) mc m2 ->
  wmono rsegs mc m2 -> mem_inv rsegs m2 ->
  stk rsegs m2 (sp2 - REAC_CTRL_PARSE_K) sp2 ->
  (fr + 32 <> 0 -> rw_cells rsegs m2 (fr + 32) [CB 36 (snd (ctrlparse len fb))]) ->
  asan_cells m2 -> shadow_rw m2 ->
  addressable m2 (sp2 - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
  fp [1%nat] m2 (bv_unsigned tp) FS (sp2 - REAC_CTRL_PARSE_K) sp2
     (reac_ctrl_parse_W (fr + 32) sp2) (reac_ctrl_parse_D f len (fr + 32)) ->
  evt rsegs Q
    (MS (mkR (Z_to_bv 64 0x84688) (Z_to_bv 64 sp2) gp tp t0' t1' t2' (Z_to_bv 64 S) (Z_to_bv 64 CA)
             (Z_to_bv 64 (fst (ctrlparse len fb))) a1' a2' a3' a4' a5' a6' a7'
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
             (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) s8 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x84688) fc None m2 (seg_rom rsegs)).
Proof.
  intros Q fr sp2 jj nn KL KN.
  assert (KL' : cmLHF_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb RNG_all 0 Q fr sp2 jj nn)
    by (cm_cont_of KL (cmInv_of_cmInv_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS SR)).
  assert (KN' : cmNoneF_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb RNG_all Q fr sp2 jj nn)
    by (cm_cont_of KN (cmInv_of_cmInv_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS SR)).
  intros mc m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'.
  intros L E12 E13 E16 E17 INV MU2 WM2 MI2 ST2 RO2 AC2 SW2 AW2 FP2.
  exact (cm_parse_of_F_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb
           Rf Rlen S16 HK ST Hfb (shadow_rw_on_of_shadow_rw _ m SR) HHM HAE AW FP0
           Q fr sp2 jj nn KL' KN' mc m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
           L E12 E13 E16 E17
           (cmInv_on_of_cmInv ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS fr sp2 jj nn mc INV)
           MU2 WM2 MI2 ST2 RO2 AC2 (fun P _ => shadow_rw_on_of_shadow_rw P m2 SW2) AW2 FP2).
Qed.

(* cm_tail_F's one rng premise holds at RNG_all by ExecF.rng_all, from the bounds its own premises carry (the frame
   is positive and below S, so its 24 shadow bytes are in [0, 2^64)). *)
Corollary cm_tail_of_F : forall (Q : machine_state -> Prop) (fr sp2 jj nn : Z),
  cmXCF RNG_all Q fr sp2 jj nn ->
  forall (mc : word -> option byte) (r : Z)
         (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 : word),
  r = want CM_T len fb -> cmInv fr sp2 jj nn mc ->
  evt rsegs Q
    (MS (mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 CA) y0 y1 y2 y3 y4 y5 y6 y7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 r) z4 z5 (Z_to_bv 64 (shadow_addr fr))
             (Z_to_bv 64 fr) z8 z9 z10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x84704) fc None mc (seg_rom rsegs)).
Proof.
  intros Q fr sp2 jj nn KX.
  assert (KX' : cmXCF_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb RNG_all Q fr sp2 jj nn)
    by (cm_cont_of KX (cmInv_of_cmInv_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS SR)).
  intros mc r x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 Er INVk.
  exact (cm_tail_of_F_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb
           Rf Rlen RS S16 HK ST Hfb (shadow_rw_on_of_shadow_rw _ m SR) HHM HAE AW FP0
           Q fr sp2 jj nn KX' mc r x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 Er
           (cmInv_on_of_cmInv ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS fr sp2 jj nn mc INVk)).
Qed.

Corollary cm_none_of_F : forall (Q : machine_state -> Prop) (fr sp2 jj nn : Z),
  cmXCF RNG_all Q fr sp2 jj nn -> cmNoneF RNG_all Q fr sp2 jj nn.
Proof.
  intros Q fr sp2 jj nn KX.
  assert (KX' : cmXCF_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb RNG_all Q fr sp2 jj nn)
    by (cm_cont_of KX (cmInv_of_cmInv_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS SR)).
  intros mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs3 rs4 rs5 rs8 rs9 rs10 rt3 rt4 rt5 rt6 Hw INVk.
  exact (cm_none_of_F_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb
           Rf Rlen RS S16 HK ST Hfb (shadow_rw_on_of_shadow_rw _ m SR) HHM HAE AW FP0
           Q fr sp2 jj nn KX' mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs3 rs4 rs5 rs8 rs9 rs10
           rt3 rt4 rt5 rt6 Hw
           (cmInv_on_of_cmInv ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS fr sp2 jj nn mc INVk)).
Qed.

End MatchF.

(* Route (C) audit: the `_on` stretch lemmas (cm_parse_S3_rb_F_on with cmLHF_on / cmXCF_on is the glue's). *)
Print Assumptions cm_parse_F_on.
Print Assumptions cm_tail_F_on.
Print Assumptions cm_none_F_on.
Print Assumptions cm_parse_S3_F_on.
Print Assumptions cm_parse_rb_F_on.
Print Assumptions cm_parse_S3_rb_F_on.
Print Assumptions cm_parse_of_F_on.
Print Assumptions cm_tail_of_F_on.
Print Assumptions cm_none_of_F_on.
