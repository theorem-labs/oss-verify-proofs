(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 321 of its 350 lines of code are new or changed and 219 lines of the source are left out. *)
(* Stretch S4 (loop head 0x846ac -> the reac_box_model_block call at 0x846c8) of the footprint (_F) re-run of
   reac_box_catalogue_match.v (source commit d69f7c708f6, proved on FACTS ed6b6b7b0ab) by the same script over
   lib/Lib/StepF; image fuzz_ctrl v1.9.0 asan, ELF fuzz_ctrl.debug sha256
   78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd; route (a) of 22:20Z; for the cgif-form walk
   C_reac_box_catalogue_match.v only.

   The source run lemma is reac_box_catalogue_match.cm_model (cmBC i Q -> cmLH i Q), whose script runs THROUGH the
   reac_box_model_block call (it applies the Section hypothesis HMB there). Route (a) splits that script at the
   call: cm_model_S4_F stops at the `jal` 0x846c8 BEFORE it executes, with the state facts the script has there
   (cmMB: the invariant rebuilt at the written memory and the model buffer addressable); the walk calls the callee
   itself and the next stretch (S5) starts at the return 0x846cc. Same tactics, a new lemma boundary: the four
   un-poisoning stores of the model buffer's shadow (bytes 14..17 of the frame's 24 shadow bytes), cm_inv_step at
   the written memory, cm_model_addr, then `mv a0,s3; li a1,0; mv a2,s4`.

   One rng premise, the only region the run reads or writes: the frame's 24 shadow bytes
   [shadow_addr fr, shadow_addr fr + 24), the shadow range the lemma's own header footprint (cmHF fr) names
   (instruction fetch is not an access; the three register moves access no memory).

   cm_model_S4_of_F re-derives the old Exec.evt form of the same boundary at ExecF.RNG_all (the check that the _F
   statement is the old one plus the footprint premise, nothing weaker).

   Route (C) (F-on-spec.md (a working note, not in this delivery), a Theorem Labs lane's frozen form): Section MatchFOn below re-runs cmMB / cmMB_evt / cmLH_F and the
   two lemmas with Section MatchF's premise SR : shadow_rw m narrowed to SR_on : shadow_rw_on R m, R =
   reac_box_catalogue_match_shadow_R f len S FS, over reac_box_catalogue_match_on.v's names (X -> X_on); Section
   MatchF keeps every old statement, each old lemma now a corollary of its X_on. cm_jal_mb_F_on is cm_jal_mb_F's
   statement (it has no shadow premise), under the name the glue's `_on` walk cites.

   reac_box_catalogue_match.v is unchanged apart from comment text; this file Requires it and the engines only. *)
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
  reac_box_catalogue_match_c reac_box_catalogue_match_lib reac_box_catalogue_match.
(* Route (C): the narrowed premise and the `_on` re-run of the source (Required, not Imported), for Section MatchFOn. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_box_catalogue_match_on.
(* Last: StepF's step / store_done (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF ExecF_all StepF.
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

Module RBCM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_catalogue_match.
Module RBCMO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_catalogue_match_on.

(* ==== route (C): the `_on` forms of this stretch (F-on-spec.md) ====

   Section MatchFOn is Section MatchF below with SR : shadow_rw m replaced by SR_on : shadow_rw_on R m (R =
   reac_box_catalogue_match_shadow_R f len S FS), the other Variables and Hypotheses unchanged, in the same order.
   Its Lets mirror Section MatchF's: fk_facts_on / cm_inv_step_on from reac_box_catalogue_match_on.v (SR_on in SR's
   place), the others from the old plain file. Each X_on is X's script over cmInv_on (cmMB_on, cmMB_evt_on,
   cmLH_F_on, and reac_box_catalogue_match_on.v's cmLH_on for cm_model_S4_of_F_on); the four shadow stores and the
   register moves are unchanged. cmInv_on_of_cmInv / cmInv_of_cmInv_on convert the invariant for Section MatchF's
   corollaries. *)
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

Local Abbreviation CA := (RBCM.CA S).
Local Abbreviation cmHF := (RBCM.cmHF S).
Local Abbreviation cmInv := (RBCM.cmInv ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS).
Local Abbreviation cmInv_on := (RBCMO.cmInv_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS).
Local Abbreviation cmLH_on := (RBCMO.cmLH_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb).

(* Section MatchF's Lets, the re-proved names from reac_box_catalogue_match_on.v (on-api.md's prefixes). *)
Let cm_geo := RBCM.cm_geo tp m f len S FS fb Rf Rlen S16 HK Hfb FP0.
Let fk_facts_on := RBCMO.fk_facts_on tp m f len S FS fb Rf Rlen S16 HK ST Hfb SR_on AW FP0.
Let cm_fr_bounds := RBCM.cm_fr_bounds tp m f len S FS fb Rf Rlen S16 HK Hfb HHM FP0.
Let acl_fs := RBCM.acl_fs tp m f len S FS FP0.
Let cm_inv_step_on :=
  RBCMO.cm_inv_step_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS fb
    Rf Rlen S16 HK ST Hfb SR_on HHM HAE AW FP0.
Let cm_model_addr := RBCM.cm_model_addr f len S fb Rf Rlen Hfb.

(* Section MatchF's store tactics (an Ltac of a Section is not exported), same text. *)
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

Ltac cm_keep HB :=
  lazymatch goal with
  | |- evtF ?segs _ ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?mm ?a ?bs) ?ro) =>
      let E := addr_expr a in
      change (write_to_mem mm a bs) with (write_to_mem mm (wa E) bs);
      assert (HB : bytes_at segs (write_to_mem mm (wa E) bs) E bs)
        by (apply bytes_at_write_same; simpl_sizes; lia);
      store_done
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

(* cmMB with cmInv_on: the state at the reac_box_model_block call (pc 0x846c8), row i, before the `jal`. *)
Definition cmMB_on (RNG : ExecF.footprint) (i : nat) (Q : machine_state -> Prop) (fr sp2 jj nn : Z) : Prop :=
  forall (mc : word -> option byte)
         (rra rt0 rt1 rt2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
    RcMatch.cm_gate len fb = true -> (i < 11)%nat -> (forall j, (j < i)%nat -> nth j DECLS [] <> cm_blk fb) ->
    cmInv_on fr sp2 jj nn mc -> addressable mc (fr + 112) 32 ->
    evtF rsegs RNG Q
      (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
               (Z_to_bv 64 (CM_T + 296 * Z.of_nat i)) (Z_to_bv 64 0) (Z_to_bv 64 (fr + 112))
               ra3 ra4 ra5 ra6 ra7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 (CM_T + 296 * Z.of_nat i))
               (Z_to_bv 64 (fr + 112)) (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr)
               (Z_to_bv 64 (11 - Z.of_nat i)) (Z_to_bv 64 1) (Z_to_bv 64 (-8)) s11 rt3 rt4 rt5 rt6)
           F (Z_to_bv 64 0x846c8) fc None mc (seg_rom rsegs)).

(* cmMB_evt with cmInv_on. *)
Definition cmMB_evt_on (i : nat) (Q : machine_state -> Prop) : Prop :=
  forall (fr sp2 jj nn : Z) (mc : word -> option byte)
         (rra rt0 rt1 rt2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
    RcMatch.cm_gate len fb = true -> (i < 11)%nat -> (forall j, (j < i)%nat -> nth j DECLS [] <> cm_blk fb) ->
    cmInv_on fr sp2 jj nn mc -> addressable mc (fr + 112) 32 ->
    evt rsegs Q
      (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
               (Z_to_bv 64 (CM_T + 296 * Z.of_nat i)) (Z_to_bv 64 0) (Z_to_bv 64 (fr + 112))
               ra3 ra4 ra5 ra6 ra7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 (CM_T + 296 * Z.of_nat i))
               (Z_to_bv 64 (fr + 112)) (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr)
               (Z_to_bv 64 (11 - Z.of_nat i)) (Z_to_bv 64 1) (Z_to_bv 64 (-8)) s11 rt3 rt4 rt5 rt6)
           F (Z_to_bv 64 0x846c8) fc None mc (seg_rom rsegs)).

(* cmLH_F with cmInv_on: the loop head (pc 0x846ac) as a footprint run. *)
Definition cmLH_F_on (RNG : ExecF.footprint) (i : nat) (Q : machine_state -> Prop) (fr sp2 jj nn : Z) : Prop :=
  forall (mc : word -> option byte)
         (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
    RcMatch.cm_gate len fb = true -> (forall j, (j < i)%nat -> nth j DECLS [] <> cm_blk fb) ->
    cmInv_on fr sp2 jj nn mc ->
    rng RNG (shadow_addr fr) 24 ->
    evtF rsegs RNG Q
      (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
               ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 (CM_T + 296 * Z.of_nat i))
               (Z_to_bv 64 (fr + 112)) (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr)
               (Z_to_bv 64 (11 - Z.of_nat i)) (Z_to_bv 64 1) (Z_to_bv 64 (-8)) s11 rt3 rt4 rt5 rt6)
           F (Z_to_bv 64 0x846ac) fc None mc (seg_rom rsegs)).

(* cm_model_S4_F over cmInv_on: S4, loop head 0x846ac -> the reac_box_model_block call 0x846c8. *)
Lemma cm_model_S4_F_on : forall (RNG : ExecF.footprint) (i : nat) (Q : machine_state -> Prop) (fr sp2 jj nn : Z),
  (i < 11)%nat -> cmMB_on RNG i Q fr sp2 jj nn -> cmLH_F_on RNG i Q fr sp2 jj nn.
Proof.
  intros RNG i Q fr sp2 jj nn Hi KB mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6
    G Hnd INV RSH.
  pose proof INV as INVk.
  destruct INV as (FK & MUg & WMg & RMg & MIg & ACg & SRg & FPg & TLg & ADg & AWXg & SVg & FLg).
  pose proof (cm_geo fr sp2 jj nn FK) as (G8 & Gfs & G16 & Gsp & Gc).
  pose proof (fk_facts_on fr sp2 jj nn FK) as (FR8 & FRpos & FR192 & FW & FAP & FSW & _).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (FRgt & FRhi).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & FSdj).
  clear MUg.
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
  unfold RBCM.cmHF in MUh.
  cm_wst (shadow_addr fr + 14) 1%nat. step. cm_keep B14.
  cm_wst (shadow_addr fr + 15) 1%nat. step. cm_keep B15.
  cm_wst (shadow_addr fr + 16) 1%nat. step. cm_keep B16.
  cm_wst (shadow_addr fr + 17) 1%nat. step. cm_keep B17.
  pose proof (cm_inv_step_on fr sp2 jj nn mc _ INVk MUh WMh RMh MIg) as INV1.
  pose proof INV1 as INV1k.
  destruct INV1 as (_ & MU1 & WM1 & RM1 & MI1 & AC1 & SR1 & FP1 & TL1 & AD1 & AWX1 & SV1 & FL1).
  assert (ADm : addressable m1 (fr + 112) 32).
  { apply (cm_model_addr m1 fr FR8 ltac:(clear -FRpos; lia)
             ltac:(clear -FRhi HAE; unfold APPMEM_END in *; lia));
      [ intros k Hk; replace (fr + 112 + k) with (fr + (112 + k)) by (clear -Hk; lia); apply FAP; clear -Hk; lia
      | exact B14 | exact B15 | exact B16 | exact B17 ]. }
  (* 0x846bc mv a0,s3 ; 0x846c0 li a1,0 ; 0x846c4 mv a2,s4 : the run stops at the `jal` 0x846c8. *)
  do 3 step.
  eapply KB; [exact G | exact Hi | exact Hnd | exact INV1k | exact ADm].
Qed.

(* cm_model_S4_of_F over cmInv_on: the Exec.evt form at ExecF.RNG_all, ending in reac_box_catalogue_match_on.v's
   cmLH_on. *)
Lemma cm_model_S4_of_F_on : forall (i : nat) (Q : machine_state -> Prop),
  (i < 11)%nat -> cmMB_evt_on i Q -> cmLH_on i Q.
Proof.
  intros i Q Hi KB fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 G Hnd INV.
  pose proof INV as INVk.
  destruct INV as (FK & _).
  pose proof (fk_facts_on fr sp2 jj nn FK) as (_ & FRpos & _).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (_ & FRhi).
  assert (KBF : cmMB_on RNG_all i Q fr sp2 jj nn).
  { intros mc' rra' rt0' rt1' rt2' ra3' ra4' ra5' ra6' ra7' rt3' rt4' rt5' rt6'
      G' Hi' Hnd' INV' AD'.
    apply evt_evtF_all. exact (KB fr sp2 jj nn mc' rra' rt0' rt1' rt2' ra3' ra4' ra5' ra6' ra7'
                                 rt3' rt4' rt5' rt6' G' Hi' Hnd' INV' AD'). }
  assert (RSH : rng RNG_all (shadow_addr fr) 24).
  { apply rng_all.
    - unfold shadow_addr. assert (D : 0 <= fr / 8) by (apply Z.div_pos; clear -FRpos; lia).
      unfold ASAN_K. clear -D. lia.
    - unfold shadow_addr, ASAN_K. clear -FRpos FRhi RS. Z.div_mod_to_equations. lia. }
  exact (evtF_evt rsegs RNG_all _ _
           (cm_model_S4_F_on RNG_all i Q fr sp2 jj nn Hi KBF mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
              rt3 rt4 rt5 rt6 G Hnd INVk RSH)).
Qed.

End MatchFOn.

(* Section MatchF's corollaries: an old continuation K (over cmInv) gives the `_on` one (over cmInv_on), C being
   cmInv_of_cmInv_on at a shadow_rw of the entry memory. *)
Local Ltac cm_cont_of K C := hnf; intros; eapply K; try eassumption; apply C; eassumption.

Section MatchF.
(* The Section variables and the hypotheses of reac_box_catalogue_match.v's Section Match that this stretch's
   script uses (Rocq discharges a lemma over the used ones only; HPC / HBC / HSM / HMB, HT / AT / ABC / the cell
   premises / MI / AC / TLS0 / Hwin / HF / AFU belong to the stretches that read those regions or call those
   callees, not to this one). *)
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (f len S FS : Z) (fb : list byte).
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

(* The source file's Section constants at this Section's variables (the statements are the source's, not copies). *)
Local Notation CA := (RBCM.CA S).
Local Notation cmHF := (RBCM.cmHF S).
Local Notation cmInv := (RBCM.cmInv ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS).
Local Notation cmLH := (RBCM.cmLH ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb).

(* The source file's helper lemmas at this Section's variables and hypotheses, under their source names. *)
Let cm_geo := RBCM.cm_geo tp m f len S FS fb Rf Rlen S16 HK Hfb FP0.
Let fk_facts := RBCM.fk_facts tp m f len S FS fb Rf Rlen S16 HK ST Hfb SR AW FP0.
Let cm_fr_bounds := RBCM.cm_fr_bounds tp m f len S FS fb Rf Rlen S16 HK Hfb HHM FP0.
Let acl_fs := RBCM.acl_fs tp m f len S FS FP0.
Let cm_inv_step :=
  RBCM.cm_inv_step ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS fb
    Rf Rlen S16 HK ST Hfb SR HHM HAE AW FP0.
Let cm_model_addr := RBCM.cm_model_addr f len S fb Rf Rlen Hfb.

(* reac_box_catalogue_match.v's file-local store tactics (an Ltac of a Section is not exported), with StepF's
   evtF goal shape and StepF's store_done. The text is otherwise that of the source. *)
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

Ltac cm_keep HB :=
  lazymatch goal with
  | |- evtF ?segs _ ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?mm ?a ?bs) ?ro) =>
      let E := addr_expr a in
      change (write_to_mem mm a bs) with (write_to_mem mm (wa E) bs);
      assert (HB : bytes_at segs (write_to_mem mm (wa E) bs) E bs)
        by (apply bytes_at_write_same; simpl_sizes; lia);
      store_done
  end.

(* The register state at the reac_box_model_block call (pc 0x846c8), row i, BEFORE the `jal` executes: the loop
   registers of cmLH with a0 = the row address T + 296 i, a1 = 0 and a2 = fr + 112 (the model buffer) set by
   `mv a0,s3; li a1,0; mv a2,s4`; the invariant holds at the memory the four un-poisoning stores wrote and the
   model buffer is addressable there. This is the post predicate of stretch S4 and the pre of stretch S5. *)
Definition cmMB (RNG : ExecF.footprint) (i : nat) (Q : machine_state -> Prop) (fr sp2 jj nn : Z) : Prop :=
  forall (mc : word -> option byte)
         (rra rt0 rt1 rt2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
    RcMatch.cm_gate len fb = true -> (i < 11)%nat -> (forall j, (j < i)%nat -> nth j DECLS [] <> cm_blk fb) ->
    cmInv fr sp2 jj nn mc -> addressable mc (fr + 112) 32 ->
    evtF rsegs RNG Q
      (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
               (Z_to_bv 64 (CM_T + 296 * Z.of_nat i)) (Z_to_bv 64 0) (Z_to_bv 64 (fr + 112))
               ra3 ra4 ra5 ra6 ra7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 (CM_T + 296 * Z.of_nat i))
               (Z_to_bv 64 (fr + 112)) (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr)
               (Z_to_bv 64 (11 - Z.of_nat i)) (Z_to_bv 64 1) (Z_to_bv 64 (-8)) s11 rt3 rt4 rt5 rt6)
           F (Z_to_bv 64 0x846c8) fc None mc (seg_rom rsegs)).

(* The same state in the old (Exec.evt) form, for the _of_F corollary. *)
Definition cmMB_evt (i : nat) (Q : machine_state -> Prop) : Prop :=
  forall (fr sp2 jj nn : Z) (mc : word -> option byte)
         (rra rt0 rt1 rt2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
    RcMatch.cm_gate len fb = true -> (i < 11)%nat -> (forall j, (j < i)%nat -> nth j DECLS [] <> cm_blk fb) ->
    cmInv fr sp2 jj nn mc -> addressable mc (fr + 112) 32 ->
    evt rsegs Q
      (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
               (Z_to_bv 64 (CM_T + 296 * Z.of_nat i)) (Z_to_bv 64 0) (Z_to_bv 64 (fr + 112))
               ra3 ra4 ra5 ra6 ra7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 (CM_T + 296 * Z.of_nat i))
               (Z_to_bv 64 (fr + 112)) (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr)
               (Z_to_bv 64 (11 - Z.of_nat i)) (Z_to_bv 64 1) (Z_to_bv 64 (-8)) s11 rt3 rt4 rt5 rt6)
           F (Z_to_bv 64 0x846c8) fc None mc (seg_rom rsegs)).

(* The loop head (pc 0x846ac) of reac_box_catalogue_match.cmLH as a footprint run: the same premises, plus the one
   rng premise of the region this stretch writes (the frame's 24 shadow bytes). *)
Definition cmLH_F (RNG : ExecF.footprint) (i : nat) (Q : machine_state -> Prop) (fr sp2 jj nn : Z) : Prop :=
  forall (mc : word -> option byte)
         (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
    RcMatch.cm_gate len fb = true -> (forall j, (j < i)%nat -> nth j DECLS [] <> cm_blk fb) ->
    cmInv fr sp2 jj nn mc ->
    rng RNG (shadow_addr fr) 24 ->
    evtF rsegs RNG Q
      (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
               ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 (CM_T + 296 * Z.of_nat i))
               (Z_to_bv 64 (fr + 112)) (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr)
               (Z_to_bv 64 (11 - Z.of_nat i)) (Z_to_bv 64 1) (Z_to_bv 64 (-8)) s11 rt3 rt4 rt5 rt6)
           F (Z_to_bv 64 0x846ac) fc None mc (seg_rom rsegs)).

(* S4: the run from the loop head at 0x846ac (row i) to the reac_box_model_block call at 0x846c8, by the script of
   reac_box_catalogue_match.cm_model over StepF's step, cut at the call. *)
Lemma cm_model_S4_F : forall (RNG : ExecF.footprint) (i : nat) (Q : machine_state -> Prop) (fr sp2 jj nn : Z),
  (i < 11)%nat -> cmMB RNG i Q fr sp2 jj nn -> cmLH_F RNG i Q fr sp2 jj nn.
Proof.
  intros RNG i Q fr sp2 jj nn Hi KB.
  assert (KB' : cmMB_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb RNG i Q fr sp2 jj nn)
    by (cm_cont_of KB (cmInv_of_cmInv_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS SR)).
  intros mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 G Hnd INV RSH.
  exact (cm_model_S4_F_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb
           Rf Rlen RS S16 HK ST Hfb (shadow_rw_on_of_shadow_rw _ m SR) HHM HAE AW FP0
           RNG i Q fr sp2 jj nn Hi KB' mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 G Hnd
           (cmInv_on_of_cmInv ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS fr sp2 jj nn mc INV) RSH).
Qed.

(* The old (Exec.evt) form of the same boundary, from the footprint form at ExecF.RNG_all: the rng premise by
   ExecF.rng_all (the frame's 24 shadow bytes lie in [0, 2^64) by fk_facts / cm_fr_bounds), the evt continuation by
   ExecF_all.evt_evtF_all and the conclusion by ExecF.evtF_evt. So the _F statement is the old one plus the
   footprint premise, nothing weaker. *)
Lemma cm_model_S4_of_F : forall (i : nat) (Q : machine_state -> Prop),
  (i < 11)%nat -> cmMB_evt i Q -> cmLH i Q.
Proof.
  intros i Q Hi KB.
  assert (KB' : cmMB_evt_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb i Q)
    by (cm_cont_of KB (cmInv_of_cmInv_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS SR)).
  intros fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 G Hnd INV.
  exact (cm_model_S4_of_F_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb
           Rf Rlen RS S16 HK ST Hfb (shadow_rw_on_of_shadow_rw _ m SR) HHM HAE AW FP0
           i Q Hi KB' fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 G Hnd
           (cmInv_on_of_cmInv ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS fr sp2 jj nn mc INV)).
Qed.

End MatchF.

(* The single `jal reac_box_model_block` step at 0x846c8, the event between stretch S4 (which stops BEFORE it) and
   stretch S5 (which starts at the return 0x846cc): one StepF step to the callee entry 0x85b44 with ra set, so the
   walk's TMB rule can start at `BASE + AF_reac_box_model_block`. Generic in every register and the memory; a jal
   makes no memory access, so there is no rng premise. Statement text: rebase-interfaces.md sec. 2.5 (a working note, not in this delivery) (a Theorem Labs lane).
   Image check: `846c8: 47c010ef jal 85b44 <reac_box_model_block>` (objdump of fuzz_ctrl.debug, sha256
   78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd). *)
Lemma cm_jal_mb_F : forall (RNG : ExecF.footprint) (Q : machine_state -> Prop)
    (x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (mc : word -> option byte),
  Q (MS (mkR (Z_to_bv 64 0x846cc) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6) F (Z_to_bv 64 0x85b44) fc None mc (seg_rom rsegs)) ->
  evtF rsegs RNG Q
    (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x846c8) fc None mc (seg_rom rsegs)).
Proof.
  intros RNG Q x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc mc HQ.
  step.
  replace (ret_pc (Z_to_bv 64 0x846cc)) with (Z_to_bv 64 0x846cc)
    by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
  apply evtF_done. exact HQ.
Qed.

(* cm_jal_mb_F under the `_on` name the glue's narrowed walk cites: the step has no shadow premise (no Section
   variable, no memory fact), so the statement is cm_jal_mb_F's. *)
Lemma cm_jal_mb_F_on : forall (RNG : ExecF.footprint) (Q : machine_state -> Prop)
    (x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (mc : word -> option byte),
  Q (MS (mkR (Z_to_bv 64 0x846cc) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6) F (Z_to_bv 64 0x85b44) fc None mc (seg_rom rsegs)) ->
  evtF rsegs RNG Q
    (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x846c8) fc None mc (seg_rom rsegs)).
Proof. exact cm_jal_mb_F. Qed.

(* Route (C) audit: the glue's `_on` lemmas of this stretch. *)
Print Assumptions cm_model_S4_F_on.
Print Assumptions cm_model_S4_of_F_on.
Print Assumptions cm_jal_mb_F_on.
