(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 646 of its 686 lines of code are new or changed and 208 lines of the source are left out. *)
(* Route (C) `_on` forms of stretch S5 (reac_box_catalogue_match_F5.v, unchanged): the same run with the narrowed
   shadow premise `SR_on : shadow_rw_on (reac_box_catalogue_match_shadow_R f len S FS) m` in place of
   `SR : shadow_rw m`, and the bcmp wrapper's `_on` footprint contract `bcmp_wrap_contract_F_on`
   (lib/A/Prog/bcmp_wrap_c_on.v, a Definitions-only leaf) in place of `bcmp_wrap_contract_F`.

   F5 takes a callee contract (HBCF) as a Section hypothesis, so its declarations stay byte-identical with their own
   proofs, and their `_on` forms are this NEW file (F-on-spec.md item 4). Every declaration of F5 is re-stated here as
   `<name>_on`: each one depends on SR (directly, through fk_facts / cm_inv_step / cm_Wc_sh_out / cm_Wc_sh_buf /
   cm_ad_join, or through the invariant cmInv). No declaration of F5 is SR-free, so this file cites none of F5's.

   The scripts are F5's, with these changes only (as reac_box_catalogue_match_on.v changes the plain file's):
     - cmInv / cmLH / cmNone / cmHit / cmBC -> cmInv_on / cmLH_on / cmNone_on / cmHit_on / cmBC_on, and the SR-dependent
       names fk_facts / cm_stk_win / cm_inv_step / cm_inv_mu / cm_Wc_sh_out / cm_Wc_sh_buf / cm_ad_join -> their `_on`
       forms (reac_box_catalogue_match_on.v, at this Section's variables with SR_on in place of SR);
     - the bcmp call takes HBCF_on; its shadow premise is the invariant's `shadow_rw_on R mc` narrowed to the wrapper's
       region by shadow_rw_on_mono and cm_R_bcmp; its post is bcmp_wrap_post_on;
     - the stretch's start takes reac_box_model_block_post_on (post `forall P, shadow_rw_on P m1 -> shadow_rw_on P m2`);
       cm_Wc_rd -> cm_Wc_rd_on with the shadow premise `shadow_rw_on_mono _ _ m2 (cm_Wc_rd_R ...) (SW2 _ SR1)`, as in
       reac_box_catalogue_match_on.v's cm_model_on. *)
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
(* The narrowed premise, the bcmp wrapper's `_on` Definition leaf, and the `_on` run (Required, not Imported: its
   Section names are re-used below at this file's Section variables). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import bcmp_wrap_c_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_box_catalogue_match_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import RngBytes.
(* Last: StepF's step / if_cases / store_done / finish (evtF goals) shadow Step's and Tac's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* MemMono.v's store-footprint hook, Local here (a Theorem Labs lane made MemMono's `::=` Local at 8bac67328ab; a Theorem Labs lane
   sanctioned this copy of MemMono.v:207-217's body): the store_done steps of the re-proved scripts carry munch /
   wmono / rd_mono / stk across each store by it, as reac_box_catalogue_match.v's scripts do. *)
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

Module RB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_catalogue_match.
Module CMO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_catalogue_match_on.

Section MatchFOn.
(* reac_box_catalogue_match_F5.v's Section MatchF variables and hypotheses, in its order, with HBCF replaced by its
   `_on` contract and SR replaced by SR_on. *)
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (f len S FS : Z) (fb : list byte).
Hypothesis HBCF_on : bcmp_wrap_contract_F_on.
Hypothesis Rf : 0 <= f < 2^64.
Hypothesis Rlen : 0 <= len < 2^64.
Hypothesis RS : S < 2^64.
Hypothesis S16 : S mod 16 = 0.
Hypothesis HK : 9136 <= S.
Hypothesis ST : stk rsegs m (S - 9136) S.
Hypothesis Hfb : length fb = 50%nat.
Hypothesis HF : 50 <= len -> 0 < f /\ f + 50 <= 2^64 /\ bytes_at rsegs m f fb /\ (f + 50 <= S - 9136 \/ S <= f).
Hypothesis SR_on : shadow_rw_on (reac_box_catalogue_match_shadow_R f len S FS) m.
Hypothesis HHM : HIGHMEM_BEG <= S - 9136.
Hypothesis HAE : S <= APPMEM_END.
Hypothesis AW : addressable m (S - 9136) 9136.
Hypothesis AFU : 50 <= len -> addressable m f 50 /\ app_mem (f + 50).
Hypothesis HBCMP : bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)).
Hypothesis HMEMCMP : bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)).
Hypothesis HGOT : bytes_at rsegs m GOT_CF (le8 (wa CF)).
Hypothesis HCF254 : bytes_at rsegs m (CF + 254) [Z_to_bv 8 1].
Hypothesis HCF255 : bytes_at rsegs m (CF + 255) [Z_to_bv 8 1].
Hypothesis FP0 : fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (S - 9136) S
  (reac_box_catalogue_match_W S) (reac_box_catalogue_match_D f len).

(* The plain file's SR-free names (F5's lines, unchanged) and the `_on` file's re-proved names (on-api.md prefixes,
   SR_on in place of SR). *)
Local Abbreviation CA := (RB.CA S).
Local Abbreviation aWc := (RB.aWc S FS).
Local Abbreviation cmFK := (RB.cmFK S FS).
Local Abbreviation cmHF := (RB.cmHF S).
Local Abbreviation cmWc := (RB.cmWc FS).
Local Abbreviation cmInv_on := (CMO.cmInv_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS).
Local Abbreviation cmLH_on := (CMO.cmLH_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb).
Local Abbreviation cmNone_on := (CMO.cmNone_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb).
Local Abbreviation cmHit_on := (CMO.cmHit_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb).
Local Abbreviation cmBC_on := (CMO.cmBC_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb).
Local Abbreviation acl_fs := (RB.acl_fs tp m f len S FS FP0).
Local Abbreviation fk_facts_on := (CMO.fk_facts_on tp m f len S FS fb Rf Rlen S16 HK ST Hfb SR_on AW FP0).
Local Abbreviation cm_fr_bounds := (RB.cm_fr_bounds tp m f len S FS fb Rf Rlen S16 HK Hfb HHM FP0).
Local Abbreviation cm_geo := (RB.cm_geo tp m f len S FS fb Rf Rlen S16 HK Hfb FP0).
Local Abbreviation cm_FB := (RB.cm_FB tp m f len S FS fb Rf Rlen HK Hfb HF HAE AFU FP0).
Local Abbreviation cm_AF := (RB.cm_AF tp m f len S FS fb Rf Rlen S16 HK Hfb HF HHM HAE AFU FP0).
Local Abbreviation cm_stk_win_on := (CMO.cm_stk_win_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS ST).
Local Abbreviation cm_lo_bytes := (RB.cm_lo_bytes tp m f len S FS fb Rf Rlen HK Hfb HHM HAE FP0).
Local Abbreviation cm_inv_step_on :=
  (CMO.cm_inv_step_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS fb Rf Rlen S16 HK ST Hfb SR_on HHM HAE AW
     FP0).
Local Abbreviation cm_inv_mu_on :=
  (CMO.cm_inv_mu_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS fb Rf Rlen HK Hfb HAE FP0).
Local Abbreviation cm_cls_keep := (RB.cm_cls_keep f len S FS fb Rf Rlen HK Hfb).
Local Abbreviation cm_cls_fp := (RB.cm_cls_fp FS).
Local Abbreviation cm_cls_out_Wc := (RB.cm_cls_out_Wc tp m f len S FS fb Rf Rlen S16 HK Hfb HHM HAE FP0).
Local Abbreviation cm_Wc_sub := (RB.cm_Wc_sub tp m f len S FS fb Rf Rlen S16 HK Hfb FP0).
Local Abbreviation cm_Wc_swap := (RB.cm_Wc_swap f len FS Rf Rlen).
Local Abbreviation cm_Wc_rd_on := (CMO.cm_Wc_rd_on tp m f len S FS fb Rf Rlen HK Hfb FP0).
Local Abbreviation cm_Wc_rd_R := (CMO.cm_Wc_rd_R tp m f len S FS fb Rf Rlen S16 HK Hfb FP0).
Local Abbreviation cm_R_bcmp := (CMO.cm_R_bcmp tp m f len S FS fb Rf Rlen S16 HK Hfb FP0).
Local Abbreviation cm_Wc_sh_out_on :=
  (CMO.cm_Wc_sh_out_on tp m f len S FS fb Rf Rlen S16 HK ST Hfb SR_on HHM HAE AW FP0).
Local Abbreviation cm_Wc_sh_buf_on :=
  (CMO.cm_Wc_sh_buf_on tp m f len S FS fb Rf Rlen S16 HK ST Hfb SR_on HHM HAE AW FP0).
Local Abbreviation cm_Wc_saves := (RB.cm_Wc_saves tp m f len S FS fb Rf Rlen S16 HK Hfb HHM HAE FP0).
Local Abbreviation cm_Wc_flag := (RB.cm_Wc_flag tp m f len S FS fb Rf Rlen S16 HK Hfb HHM HAE FP0).
Local Abbreviation cm_ad_join_on :=
  (CMO.cm_ad_join_on tp m f len S FS fb Rf Rlen S16 HK ST Hfb SR_on HHM HAE AW FP0).

(* F5's store tactics over an evtF goal (same bodies). *)
Ltac cmF_wv :=
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

Ltac cmF_wst a n :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      let HS := fresh "HS" in
      assert (HS : store_ok rsegs mm (wa a) n = true)
        by (eapply wv_store_ok;
            [ cmF_wv | eassumption
            | try unfold ASAN_K; Z.div_mod_to_equations; lia
            | try unfold ASAN_K; Z.div_mod_to_equations; lia ])
  end.

(* ===================== the continuation predicates (F5's, over cmInv_on) ===================== *)

Definition cmXt_F_on (RNG : ExecF.footprint) (Q : machine_state -> Prop) (fr sp2 jj nn : Z) : Prop :=
  forall (mc : word -> option byte) (r : Z)
         (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 : word),
    r = want CM_T len fb -> cmInv_on fr sp2 jj nn mc ->
    evtF rsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 CA) y0 y1 y2 y3 y4 y5 y6 y7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 r) z4 z5 (Z_to_bv 64 (shadow_addr fr))
               (Z_to_bv 64 fr) z8 z9 z10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x84724) fc None mc (seg_rom rsegs)).

Definition cmNone_F_on (RNG : ExecF.footprint) (Q : machine_state -> Prop) (fr sp2 jj nn : Z) : Prop :=
  forall (mc : word -> option byte)
         (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs3 rs4 rs5 rs8 rs9 rs10 rt3 rt4 rt5 rt6 : word),
    want CM_T len fb = 0 -> cmInv_on fr sp2 jj nn mc ->
    rng RNG (shadow_addr fr) 24 ->
    evtF rsegs RNG Q
      (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
               ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) rs3 rs4 rs5 (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr)
               rs8 rs9 rs10 s11 rt3 rt4 rt5 rt6)
          F (Z_to_bv 64 0x84700) fc None mc (seg_rom rsegs)).

Definition cmHit_F_on (RNG : ExecF.footprint) (Q : machine_state -> Prop) (fr sp2 jj nn : Z) : Prop :=
  forall (r : Z) (mc : word -> option byte)
         (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs4 rs5 rs8 rs9 rs10 rt3 rt4 rt5 rt6 : word),
    want CM_T len fb = r -> cmInv_on fr sp2 jj nn mc ->
    rng RNG (shadow_addr fr) 24 ->
    evtF rsegs RNG Q
      (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
               ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 r) rs4 rs5
               (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) rs8 rs9 rs10 s11 rt3 rt4 rt5 rt6)
          F (Z_to_bv 64 0x84864) fc None mc (seg_rom rsegs)).

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

Definition cmBC_F_on (RNG : ExecF.footprint) (i : nat) (Q : machine_state -> Prop) (fr sp2 jj nn : Z) : Prop :=
  forall (mc : word -> option byte)
         (rra rt0 rt1 rt2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
    RcMatch.cm_gate len fb = true -> (i < 11)%nat -> (forall j, (j < i)%nat -> nth j DECLS [] <> cm_blk fb) ->
    cmInv_on fr sp2 jj nn mc -> addressable mc (fr + 112) 32 ->
    bytes_at rsegs mc (fr + 112) (nth i DECLS []) ->
    rng_bytes RNG ->
    rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    rng RNG (sp2 - BCMP_WRAP_K) BCMP_WRAP_K ->
    rng RNG (f + 18) 32 ->
    rng RNG (8 * (shadow_addr (f + 18) / 8))
            (8 * (shadow_addr (f + 18 + 32 - 1) / 8) + 8 - 8 * (shadow_addr (f + 18) / 8)) ->
    rng RNG (fr + 112) 32 ->
    rng RNG (8 * (shadow_addr (fr + 112) / 8))
            (8 * (shadow_addr (fr + 112 + 32 - 1) / 8) + 8 - 8 * (shadow_addr (fr + 112) / 8)) ->
    rng RNG (shadow_addr fr) 24 ->
    evtF rsegs RNG Q
      (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
               (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (fr + 112)) (Z_to_bv 64 32) ra3 ra4 ra5 ra6 ra7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 (CM_T + 296 * Z.of_nat i))
               (Z_to_bv 64 (fr + 112)) (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr)
               (Z_to_bv 64 (11 - Z.of_nat i)) (Z_to_bv 64 1) (Z_to_bv 64 (-8)) s11 rt3 rt4 rt5 rt6)
          F (Z_to_bv 64 0x846dc) fc None mc (seg_rom rsegs)).

(* ===================== the tails: 0x84704 / 0x84700 / 0x84864 -> the exit cut ===================== *)

(* cm_tail_F's run: the no-match join 0x84704 sets the five shadow bytes 4 .. 8 of the frame to 0xf8 and reaches
   the exit cut 0x84724 (cmXt_F_on). *)
Lemma cm_tail_F_on : forall (RNG : ExecF.footprint) (Q : machine_state -> Prop) (fr sp2 jj nn : Z),
  cmXt_F_on RNG Q fr sp2 jj nn ->
  forall (mc : word -> option byte) (r : Z)
    (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 : word),
  r = want CM_T len fb -> cmInv_on fr sp2 jj nn mc ->
  rng RNG (shadow_addr fr) 24 ->
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
  unfold RB.cmHF in MUh.
  step.
  cmF_wst (shadow_addr fr + 4) 1%nat. step. store_done.
  cmF_wst (shadow_addr fr + 5) 1%nat. step. store_done.
  cmF_wst (shadow_addr fr + 6) 1%nat. step. store_done.
  cmF_wst (shadow_addr fr + 7) 1%nat. step. store_done.
  cmF_wst (shadow_addr fr + 8) 1%nat. step. store_done.
  step.
  eapply (KX _ r); [exact Er|].
  eapply (cm_inv_step_on fr sp2 jj nn mc); [exact INVk | exact MUh | exact WMh | exact RMh | exact MIg].
Qed.

(* cm_none_holds_F's run: the no-row tail 0x84700 sets s3 to 0 and joins the tail (cm_tail_F_on). *)
Lemma cm_none_holds_F_on : forall (RNG : ExecF.footprint) (Q : machine_state -> Prop) (fr sp2 jj nn : Z),
  cmXt_F_on RNG Q fr sp2 jj nn -> cmNone_F_on RNG Q fr sp2 jj nn.
Proof.
  intros RNG Q fr sp2 jj nn KX mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs3 rs4 rs5 rs8 rs9 rs10
    rt3 rt4 rt5 rt6 Hw INVk RSH.
  step.
  exact (cm_tail_F_on RNG Q fr sp2 jj nn KX mc 0 rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs4 rs5 rs8 rs9 rs10
           rt3 rt4 rt5 rt6 ltac:(symmetry; exact Hw) INVk RSH).
Qed.

(* cm_hit_holds_F's run: the row-match tail 0x84864 sets the model buffer's shadow bytes 14 .. 17 to 0xf8 again
   and joins the tail (cm_tail_F_on). *)
Lemma cm_hit_holds_F_on : forall (RNG : ExecF.footprint) (Q : machine_state -> Prop) (fr sp2 jj nn : Z),
  cmXt_F_on RNG Q fr sp2 jj nn -> cmHit_F_on RNG Q fr sp2 jj nn.
Proof.
  intros RNG Q fr sp2 jj nn KX r mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs4 rs5 rs8 rs9 rs10
    rt3 rt4 rt5 rt6 Hw INVk RSH.
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
  unfold RB.cmHF in MUh.
  step.
  cmF_wst (shadow_addr fr + 14) 1%nat. step. store_done.
  cmF_wst (shadow_addr fr + 15) 1%nat. step. store_done.
  cmF_wst (shadow_addr fr + 16) 1%nat. step. store_done.
  cmF_wst (shadow_addr fr + 17) 1%nat. step. store_done.
  step.
  eapply (cm_tail_F_on RNG Q fr sp2 jj nn KX _ r); [symmetry; exact Hw | | exact RSH].
  eapply (cm_inv_step_on fr sp2 jj nn mc); [exact INVk | exact MUh | exact WMh | exact RMh | exact MIg].
Qed.

(* ===================== the bcmp call and the back edge ===================== *)

Lemma cm_lh_eq_F_on : forall (RNG : ExecF.footprint) (i : nat) (Q : machine_state -> Prop) (fr sp2 jj nn : Z),
  cmLH_F_on RNG i Q fr sp2 jj nn ->
  forall (mc : word -> option byte)
         (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 w3 w8 : word),
    w3 = Z_to_bv 64 (CM_T + 296 * Z.of_nat i) -> w8 = Z_to_bv 64 (11 - Z.of_nat i) ->
    RcMatch.cm_gate len fb = true -> (forall j, (j < i)%nat -> nth j DECLS [] <> cm_blk fb) ->
    cmInv_on fr sp2 jj nn mc ->
    rng RNG (shadow_addr fr) 24 ->
    evtF rsegs RNG Q
      (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
               ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) w3
               (Z_to_bv 64 (fr + 112)) (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr)
               w8 (Z_to_bv 64 1) (Z_to_bv 64 (-8)) s11 rt3 rt4 rt5 rt6)
          F (Z_to_bv 64 0x846ac) fc None mc (seg_rom rsegs)).
Proof.
  intros RNG i Q fr sp2 jj nn K mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 w3 w8 -> ->.
  apply K.
Qed.

(* cm_bcmp_F's run: the bcmp wrapper call at 0x846dc by HBCF_on (its shadow premise: the invariant's R narrowed to
   the wrapper's region, cm_R_bcmp), the invariant rebuilt at its return (cm_inv_mu_on), then the row-match tail
   (cmHit_F_on), the loop head of row i + 1 (cmLH_F_on) or the no-row tail (cmNone_F_on). *)
Lemma cm_bcmp_F_on : forall (RNG : ExecF.footprint) (i : nat) (Q : machine_state -> Prop) (fr sp2 jj nn : Z),
  (i < 11)%nat ->
  ((i + 1 < 11)%nat -> cmLH_F_on RNG (i + 1)%nat Q fr sp2 jj nn) ->
  cmNone_F_on RNG Q fr sp2 jj nn -> cmHit_F_on RNG Q fr sp2 jj nn -> cmBC_F_on RNG i Q fr sp2 jj nn.
Proof.
  intros RNG i Q fr sp2 jj nn Hi KL KN KH mc rra rt0 rt1 rt2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6
    G _ Hnd INV ADb BB RB1 RB2 RB3 RB4 RB5 RB6 RB7 RB8.
  pose proof INV as INVk.
  destruct INV as (FK & MUg & WMg & RMg & MIg & ACg & SRg & FPg & TLg & ADg & AWXg & SVg & FLg).
  pose proof (cm_geo fr sp2 jj nn FK) as (G8 & Gfs & G16 & Gsp & Gc).
  pose proof (fk_facts_on fr sp2 jj nn FK) as (FR8 & FRpos & FR192 & FW & FAP & FSW & _).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (FRgt & FRhi).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & FSdj). unfold FS_SIZE in FShi.
  assert (L : 50 <= len).
  { destruct (Z.leb_spec 50 len) as [L|L]; [exact L|]. exfalso. unfold RcMatch.cm_gate in G.
    rewrite (proj2 (Z.leb_gt 50 len) L) in G. cbn [andb] in G. discriminate G. }
  destruct (HF L) as (Hf0 & Hf50 & _ & Hfd). destruct (AFU L) as (_ & Af50).
  pose proof (cm_FB mc L MUg) as BF. pose proof (cm_AF mc L MUg) as AF.
  pose proof (bytes_at_sub rsegs mc f fb 18 32 BF ltac:(rewrite Hfb; clear; lia)) as BK.
  apply (bytes_at_addr rsegs mc _ (f + 18)) in BK; [|clear; lia].
  fold (cm_blk fb) in BK.
  assert (LK : length (cm_blk fb) = 32%nat)
    by (unfold cm_blk; rewrite length_firstn, length_skipn, Hfb; clear; lia).
  destruct (memcmp_model_total (cm_blk fb) (nth i DECLS []) 32 ltac:(rewrite LK; clear; lia)
              ltac:(rewrite (cm_decl_len i Hi); clear; lia)) as [v Hv].
  pose proof (mm_spec 32 (cm_blk fb) (nth i DECLS []) v LK (cm_decl_len i Hi) Hv) as [MM VR].
  pose proof (cm_stk_win_on fr sp2 jj nn mc INVk) as STW.
  destruct (stk_split rsegs mc (S - 9136) (sp2 - 4560) S STW ltac:(clear -Gsp; lia)) as (_ & STW2).
  destruct (stk_split rsegs mc (sp2 - 4560) sp2 S STW2 ltac:(clear -Gsp; lia)) as (STc & _).
  clear STW STW2.
  step.
  eapply evtF_cut.
  { eapply HBCF_on with (ls := cm_blk fb) (rs := nth i DECLS []) (v := v) (lo := sp2 - 4560);
      cbv zeta; rewrite ?unsigned_lit by (clear -Hf0 Hf50 FRpos FRhi RS Gsp HK; lia); unfold BCMP_WRAP_K.
    - exact BK.
    - exact BB.
    - exact Hv.
    - exact MIg.
    - clear. lia.
    - exact (acl_addr_sub mc f 50 (f + 18) 32 AF ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)).
    - exact ADb.
    - unfold end_in_app. right. replace (f + 18 + 32) with (f + 50) by (clear; lia). exact Af50.
    - unfold end_in_app. right. replace (fr + 112 + 32) with (fr + 144) by (clear; lia). apply FAP. clear; lia.
    - right. replace (f + 18 + 7) with (f + 25) by (clear; lia). exact (acl_app_in mc f 50 25 AF ltac:(clear; lia)).
    - right. replace (fr + 112 + 7) with (fr + 119) by (clear; lia). apply FAP. clear; lia.
    - clear -Hfd Gsp. lia.
    - clear -Gc Gsp. destruct Gc as [(_ & E & _)|(_ & _ & _ & _ & E)]; lia.
    - exact STc.
    - clear. lia.
    - clear -Gsp HHM. unfold HIGHMEM_BEG in *. lia.
    - clear -Gsp HAE. lia.
    - exact ACg.
    - exact (shadow_rw_on_mono _ _ mc (cm_R_bcmp fr sp2 jj nn FK L) SRg).
    - apply (cm_lo_bytes mc _ _ MUg HBCMP); unfold REAL_BCMP, ASAN_GT; [lia | rewrite length_le8; lia].
    - apply (cm_lo_bytes mc _ _ MUg HMEMCMP); unfold REAL_MEMCMP, ASAN_GT; [lia | rewrite length_le8; lia].
    - apply (cm_lo_bytes mc _ _ MUg HGOT); unfold GOT_CF, ASAN_GT; [lia | rewrite length_le8; lia].
    - apply (cm_lo_bytes mc _ _ MUg HCF254); unfold CF, ASAN_GT; cbn [length Z.of_nat Pos.of_succ_nat]; lia.
    - apply (cm_lo_bytes mc _ _ MUg HCF255); unfold CF, ASAN_GT; cbn [length Z.of_nat Pos.of_succ_nat]; lia.
    - exact RB1.
    - exact RB2.
    - exact RB3.
    - exact RB4.
    - right. exact RB5.
    - exact RB6.
    - right. exact RB7. }
  intros ms' Hpost. unfold bcmp_wrap_post_on in Hpost.
  rewrite (unsigned_lit sp2) in Hpost by (clear -Gsp RS HK; lia).
  destruct Hpost as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6''
                     & m2 & E2 & MU2 & WM2 & MI2 & ST2 & AC2 & SW2 & _ & _).
  subst ms'. unfold BCMP_WRAP_K in MU2.
  assert (SUBb : sub_fp [(sp2 - 4560, sp2)] aWc).
  { intros x Hx. unfold RB.aWc in Hx. cbn [outside] in Hx |- *. destruct Hx as (Hw & _).
    split; [clear -Hw Gsp; lia | exact I]. }
  assert (RM2 : rd_mono mc m2).
  { apply (rd_mono_list _ mc m2 MU2). constructor; [|constructor]. cbn [fst snd].
    intros y Hy. exact (rd_of_stk m2 _ _ ST2 y Hy). }
  pose proof FPg as FPc.
  destruct FPc as (DT0 & TS0 & C0 & T0 & DB0 & kk0 & HT0 & HTP0 & HPl0 & H880 & H960 & HCL0 & HFS0 & HApp0 & HWd0
                   & HDd0).
  rewrite Forall_forall in HCL0.
  assert (OB : forall x, x < S - 9136 \/ S - 96 <= x -> outside [(sp2 - 4560, sp2)] x).
  { intros x Hx. cbn [outside]. split; [clear -Hx Gsp; lia | exact I]. }
  assert (INV2 : cmInv_on fr sp2 jj nn m2).
  { apply (cm_inv_mu_on fr sp2 jj nn mc m2 [(sp2 - 4560, sp2)] INVk MU2 WM2 RM2 MI2 SUBb).
    - intros c Hc. apply (cm_cls_keep c mc m2 _ (HCL0 c Hc) MU2).
      + intros x Hx. apply OB. left. clear -Hx Hc FShi FSpos. unfold fs_hint in Hx.
        destruct Hc as [<-|[<-|[<-|[]]]]; cbn [Z.of_nat Pos.of_succ_nat] in Hx; lia.
      + intros x Hx. apply OB. left. clear -Hx Hc FShi FSpos. unfold fs_flag, fs_M in Hx.
        destruct Hc as [<-|[<-|[<-|[]]]]; cbn [Z.of_nat Pos.of_succ_nat] in Hx; lia.
    - apply (addr_munch _ mc m2 (sp2 - 8800) 8800 ADg MU2). intros k Hk.
      apply (fl_shadow_out [(sp2 - 4560, sp2)] (sp2 - 4560) sp2);
        [intros x Hx; exact Hx | clear -Gsp HHM; unfold HIGHMEM_BEG in *; lia |].
      apply rt_app_shadow. exact (acl_app_in mc (sp2 - 8800) 8800 k ADg Hk).
    - intros x Hx _ _. apply (fl_shadow_out [(sp2 - 4560, sp2)] (sp2 - 4560) sp2);
        [intros y Hy; exact Hy | clear -Gsp HHM; unfold HIGHMEM_BEG in *; lia |].
      apply rt_app_shadow. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END.
      right. pose proof HHM as HHMb. pose proof HAE as HAEb.
      unfold HIGHMEM_BEG, APPMEM_END in HHMb, HAEb. clear -Hx HHMb HAEb. lia.
    - intros x Hx. apply OB. right. clear -Hx. lia.
    - intros Enn x Hx. apply OB. left. clear -Hx Gc Enn. destruct Gc as [(E & _)|(_ & _ & _ & _ & E)]; lia. }
  replace (ret_pc (Z_to_bv 64 0x846e0)) with (Z_to_bv 64 0x846e0)
    by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
  step.
  rewrite cm_eqb0 by (clear -VR; lia).
  destruct (Z.eqb_spec v 0) as [V0|V0]; cbv iota.
  - eapply KH; [| exact INV2 | exact RB8].
    apply cm_want_hit; [exact G | exact Hi | symmetry; apply MM; exact V0 | exact Hnd].
  - assert (Hne : nth i DECLS [] <> cm_blk fb) by (intros Hq; apply V0; apply MM; symmetry; exact Hq).
    assert (SHlo : 0 <= shadow_addr fr).
    { unfold shadow_addr. assert (D : 0 <= fr / 8) by (apply Z.div_pos; clear -FRpos; lia).
      unfold ASAN_K. clear -D. lia. }
    assert (SHhi : shadow_addr fr + 24 <= 2 ^ 64).
    { unfold shadow_addr, ASAN_K. clear -FRpos FRhi RS. Z.div_mod_to_equations. lia. }
    assert (FSW' : forall k, 0 <= k < 24 -> wview rsegs m (wa (shadow_addr fr + k)) <> None) by exact FSW.
    clear FSW.
    pose proof INV2 as INV2k.
    destruct INV2 as (_ & MUa & WMa & _).
    clear MUa MUg MU2.
    assert (MUh : munch (cmHF fr) m2 m2) by apply munch_refl.
    assert (WMh : wmono rsegs m2 m2) by apply wmono_refl.
    assert (RMh : rd_mono m2 m2) by apply rd_mono_refl.
    unfold RB.cmHF in MUh.
    cmF_wst (shadow_addr fr + 14) 1%nat. step. store_done.
    cmF_wst (shadow_addr fr + 15) 1%nat. step. store_done.
    cmF_wst (shadow_addr fr + 16) 1%nat. step. store_done.
    cmF_wst (shadow_addr fr + 17) 1%nat. step. store_done.
    pose proof (cm_inv_step_on fr sp2 jj nn m2 _ INV2k MUh WMh RMh MI2) as INV3.
    step. step. step.
    rewrite cm_eqb_lit by (clear -Hi; lia).
    destruct (Z.eqb_spec (11 - Z.of_nat i + -1) 0) as [K0|K0]; cbn [negb]; cbv iota.
    + eapply KN; [| exact INV3 | exact RB8].
      apply cm_want_none. intros j Hj.
      destruct (Nat.eq_dec j i) as [->|Hji]; [exact Hne | apply Hnd; clear -K0 Hj Hji; lia].
    + assert (HS11 : (i + 1 < 11)%nat).
      { destruct (Nat.ltb_spec i 10) as [Hlt|Hge]; [clear -Hlt; lia|].
        exfalso. apply K0. replace i with 10%nat by (clear -Hge Hi; lia). vm_compute. reflexivity. }
      eapply (cm_lh_eq_F_on RNG (i + 1)%nat Q fr sp2 jj nn (KL HS11));
        [ f_equal; clear; lia | f_equal; clear; lia | exact G | | exact INV3 | exact RB8 ].
      intros j Hj. destruct (Nat.eq_dec j i) as [->|Hji]; [exact Hne | apply Hnd; clear -Hj Hji; lia].
Qed.

(* ===================== the start of the stretch: the return at 0x846cc ===================== *)

(* cm_model_ret_F's run from reac_box_model_block_post_on at 0x846cc: the invariant is rebuilt at the returned memory
   m2 (cm_inv_mu_on; rd_mono by cm_Wc_rd_on, whose shadow premise is the post's transport of the invariant's R at m1,
   narrowed by cm_Wc_rd_R), `bne a0,s9` falls through, and a0 / a1 / a2 are set for the bcmp wrapper (cmBC_F_on). *)
Lemma cm_model_ret_F_on : forall (RNG : ExecF.footprint) (i : nat) (Q : machine_state -> Prop) (fr sp2 jj nn : Z),
  (i < 11)%nat ->
  cmBC_F_on RNG i Q fr sp2 jj nn ->
  forall (m1 : word -> option byte)
         (rra rt0 rt1 rt2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word) (ms' : machine_state),
  RcMatch.cm_gate len fb = true -> (forall j, (j < i)%nat -> nth j DECLS [] <> cm_blk fb) ->
  cmInv_on fr sp2 jj nn m1 -> addressable m1 (fr + 112) 32 ->
  rng_bytes RNG ->
  rng RNG IMG_LO (IMG_HI - IMG_LO) ->
  rng RNG (sp2 - BCMP_WRAP_K) BCMP_WRAP_K ->
  rng RNG (f + 18) 32 ->
  rng RNG (8 * (shadow_addr (f + 18) / 8))
          (8 * (shadow_addr (f + 18 + 32 - 1) / 8) + 8 - 8 * (shadow_addr (f + 18) / 8)) ->
  rng RNG (fr + 112) 32 ->
  rng RNG (8 * (shadow_addr (fr + 112) / 8))
          (8 * (shadow_addr (fr + 112 + 32 - 1) / 8) + 8 - 8 * (shadow_addr (fr + 112) / 8)) ->
  rng RNG (shadow_addr fr) 24 ->
  reac_box_model_block_post_on (Z_to_bv 64 0x846cc) (Z_to_bv 64 sp2) gp tp (Z_to_bv 64 S) (Z_to_bv 64 CA)
    (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 (CM_T + 296 * Z.of_nat i)) (Z_to_bv 64 (fr + 112))
    (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) (Z_to_bv 64 (11 - Z.of_nat i))
    (Z_to_bv 64 1) (Z_to_bv 64 (-8)) s11 F fc m1 (CM_T + 296 * Z.of_nat i) 0 (fr + 112) FS (cm_row i) [] ms' ->
  evtF rsegs RNG Q ms'.
Proof.
  intros RNG i Q fr sp2 jj nn Hi KB m1 rra rt0 rt1 rt2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 ms'
    G Hnd INV1k ADm RB1 RB2 RB3 RB4 RB5 RB6 RB7 RB8 Hpost.
  pose proof INV1k as INV1.
  destruct INV1 as (FK & MU1 & WM1 & RM1 & MI1 & AC1 & SR1 & FP1 & TL1 & AD1 & AWX1 & SV1 & FL1).
  pose proof (cm_geo fr sp2 jj nn FK) as (G8 & Gfs & G16 & Gsp & Gc).
  pose proof (fk_facts_on fr sp2 jj nn FK) as (FR8 & FRpos & FR192 & FW & FAP & FSW & _).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (FRgt & FRhi).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & FSdj).
  unfold reac_box_model_block_post_on in Hpost.
  rewrite (unsigned_lit sp2) in Hpost by (clear -Gsp RS HK; lia).
  destruct Hpost as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6''
                     & m2 & E2 & PB & WM2 & MI2 & ST2 & AC2 & SW2 & AW2 & FP2 & TL2).
  subst ms'.
  assert (Z0 : (CM_T + 296 * Z.of_nat i =? 0) || (fr + 112 =? 0) = false)
    by (apply orb_false_iff; split; apply Z.eqb_neq; [unfold CM_T; clear -Hi; lia | clear -FRpos; lia]).
  rewrite Z0 in PB |- *. destruct PB as (BB & MU2).
  destruct (cm_rc i (@nil byte) Hi) as (RC & SY). rewrite RC. rewrite SY in BB.
  unfold reac_box_model_block_X, REAC_BOX_MODEL_BLOCK_K in MU2, ST2, AW2. cbn [app] in MU2.
  assert (MUc : munch (cmWc fr sp2 4272 112 32 0%nat) m1 m2)
    by exact (munch_weaken _ _ m1 m2 (cm_Wc_swap fr sp2 4272 112 32 0%nat) MU2).
  clear MU2.
  pose proof (cm_decl_len i Hi) as LD.
  assert (RDB : forall y, fr + 112 <= y < fr + 112 + 32 -> exists b, mrd rsegs m2 (wa y) = Some b).
  { intros y Hy. apply (acl_bytes_rd m2 (fr + 112) _ y BB). rewrite LD.
    change (Z.of_nat 32) with 32. clear -Hy. lia. }
  pose proof FP2 as (DTx & TSx & Cx & Tx & DBx & kx & _ & _ & (_ & _ & _ & _ & STFS2) & _).
  assert (APPw : forall a, sp2 - 4272 <= a < sp2 -> app_mem a).
  { intros a Ha. replace a with (sp2 - 8800 + (a - (sp2 - 8800))) by (clear -Ha; lia).
    apply (acl_app_in m1 (sp2 - 8800) 8800); [exact AD1 | clear -Ha; lia]. }
  assert (RM2 : rd_mono m1 m2).
  { apply (cm_Wc_rd_on fr sp2 4272 112 32 0%nat m1 m2 ltac:(clear; lia) MUc RDB ST2 STFS2
             (shadow_rw_on_mono _ _ m2 (cm_Wc_rd_R sp2 4272 0%nat ltac:(clear; lia) ltac:(clear -Gsp; lia)
                ltac:(clear -Gsp; lia)) (SW2 _ SR1)) APPw
             ltac:(clear -G16; Z.div_mod_to_equations; lia)). }
  pose proof FP1 as FPc.
  destruct FPc as (DT0 & TS0 & C0 & T0 & DB0 & kk0 & HT0 & HTP0 & HPl0 & H880 & H960 & HCL0 & HFS0 & HApp0 & HWd0
                   & HDd0).
  rewrite Forall_forall in HCL0.
  assert (AD2 : addressable m2 (sp2 - 8800) 8800)
    by exact (cm_ad_join_on fr sp2 jj nn 4272 112 32 0%nat m1 m2 FK ltac:(cbn; tauto) ltac:(clear; lia)
                ltac:(clear; reflexivity) ltac:(clear; lia) ltac:(clear; lia) AD1 MUc AW2).
  assert (INV2 : cmInv_on fr sp2 jj nn m2).
  { apply (cm_inv_mu_on fr sp2 jj nn m1 m2 (cmWc fr sp2 4272 112 32 0%nat) INV1k MUc WM2 RM2 MI2).
    - exact (cm_Wc_sub fr sp2 jj nn 4272 112 32 0%nat FK ltac:(cbn; tauto) ltac:(clear; lia) ltac:(clear; lia)
               ltac:(clear; lia) ltac:(clear; lia)).
    - intros c Hc. destruct Hc as [<-|[<-|[<-|[]]]].
      + exact (cm_cls_fp 0%nat m2 (bv_unsigned tp) (sp2 - 4272) sp2 _ _ FP2).
      + apply (cm_cls_keep 1%nat m1 m2 (cmWc fr sp2 4272 112 32 0%nat) (HCL0 1%nat ltac:(cbn; tauto)) MUc).
        * intros x Hx. exact (cm_cls_out_Wc fr sp2 jj nn 4272 112 32 0%nat 1%nat x FK ltac:(clear; lia)
            ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
            (or_introl Hx)).
        * intros x Hx. exact (cm_cls_out_Wc fr sp2 jj nn 4272 112 32 0%nat 1%nat x FK ltac:(clear; lia)
            ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
            (or_intror Hx)).
      + apply (cm_cls_keep 2%nat m1 m2 (cmWc fr sp2 4272 112 32 0%nat) (HCL0 2%nat ltac:(cbn; tauto)) MUc).
        * intros x Hx. exact (cm_cls_out_Wc fr sp2 jj nn 4272 112 32 0%nat 2%nat x FK ltac:(clear; lia)
            ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
            (or_introl Hx)).
        * intros x Hx. exact (cm_cls_out_Wc fr sp2 jj nn 4272 112 32 0%nat 2%nat x FK ltac:(clear; lia)
            ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
            (or_intror Hx)).
    - exact AD2.
    - intros x Hx _ Hx2.
      exact (cm_Wc_sh_out_on fr sp2 jj nn 4272 112 32 0%nat x FK ltac:(cbn; tauto) ltac:(clear; lia)
               ltac:(clear; reflexivity) ltac:(clear; lia) ltac:(clear; lia) Hx Hx2).
    - intros x Hx. exact (cm_Wc_saves fr sp2 jj nn 4272 112 32 0%nat x FK ltac:(cbn; tauto) ltac:(clear; lia)
                            ltac:(clear; lia) ltac:(clear; lia) Hx).
    - intros Enn x Hx. exact (cm_Wc_flag fr sp2 jj nn 4272 112 32 0%nat x FK Enn ltac:(clear; lia)
                                ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) Hx). }
  assert (ADm2 : addressable m2 (fr + 112) 32).
  { apply (acl_addr_munch (cmWc fr sp2 4272 112 32 0%nat) m1 m2 (fr + 112) 32 ADm MUc).
    intros k Hk. exact (cm_Wc_sh_buf_on fr sp2 jj nn 4272 112 32 0%nat k FK ltac:(clear; lia) ltac:(clear; lia)
                          ltac:(clear; reflexivity) ltac:(clear; lia) ltac:(clear; lia) Hk). }
  replace (ret_pc (Z_to_bv 64 0x846cc)) with (Z_to_bv 64 0x846cc)
    by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
  step.
  rewrite cm_eqb_lit by (clear; lia).
  replace (1 =? 1) with true by reflexivity. cbn [negb]. cbv iota.
  do 3 step.
  eapply KB; [exact G | exact Hi | exact Hnd | exact INV2 | exact ADm2 | exact BB
             | exact RB1 | exact RB2 | exact RB3 | exact RB4 | exact RB5 | exact RB6 | exact RB7 | exact RB8].
Qed.

(* cm_model_ret_rb_F's RE-BASED form (the walk's base memory `m` at the reac_box_model_block return of row i), over
   cmInv_on; the body is F5's (it makes no shadow step). *)
Lemma cm_model_ret_rb_F_on : forall (RNG : ExecF.footprint) (i : nat) (Q : machine_state -> Prop) (fr sp2 jj nn : Z),
  (i < 11)%nat ->
  cmBC_F_on RNG i Q fr sp2 jj nn ->
  forall (rr rt0 rt1 rt2 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
  RcMatch.cm_gate len fb = true -> (forall j, (j < i)%nat -> nth j DECLS [] <> cm_blk fb) ->
  cmInv_on fr sp2 jj nn m -> addressable m (fr + 112) 32 ->
  bytes_at rsegs m (fr + 112) (synth (cm_row i) 0 []) ->
  rng_bytes RNG ->
  rng RNG IMG_LO (IMG_HI - IMG_LO) ->
  rng RNG (sp2 - BCMP_WRAP_K) BCMP_WRAP_K ->
  rng RNG (f + 18) 32 ->
  rng RNG (8 * (shadow_addr (f + 18) / 8))
          (8 * (shadow_addr (f + 18 + 32 - 1) / 8) + 8 - 8 * (shadow_addr (f + 18) / 8)) ->
  rng RNG (fr + 112) 32 ->
  rng RNG (8 * (shadow_addr (fr + 112) / 8))
          (8 * (shadow_addr (fr + 112 + 32 - 1) / 8) + 8 - 8 * (shadow_addr (fr + 112) / 8)) ->
  rng RNG (shadow_addr fr) 24 ->
  evtF rsegs RNG Q
    (MS (mkR rr (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
             (Z_to_bv 64 (rc (cm_row i) 0)) ra1 ra2 ra3 ra4 ra5 ra6 ra7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 (CM_T + 296 * Z.of_nat i))
             (Z_to_bv 64 (fr + 112)) (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr)
             (Z_to_bv 64 (11 - Z.of_nat i)) (Z_to_bv 64 1) (Z_to_bv 64 (-8)) s11 rt3 rt4 rt5 rt6)
        F (Z_to_bv 64 0x846cc) fc None m (seg_rom rsegs)).
Proof.
  intros RNG i Q fr sp2 jj nn Hi KB rr rt0 rt1 rt2 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6
    G Hnd INV2 ADm2 BB RB1 RB2 RB3 RB4 RB5 RB6 RB7 RB8.
  destruct (cm_rc i (@nil byte) Hi) as (RC & SY). rewrite RC. rewrite SY in BB.
  step.
  rewrite cm_eqb_lit by (clear; lia).
  replace (1 =? 1) with true by reflexivity. cbn [negb]. cbv iota.
  do 3 step.
  eapply KB; [exact G | exact Hi | exact Hnd | exact INV2 | exact ADm2 | exact BB
             | exact RB1 | exact RB2 | exact RB3 | exact RB4 | exact RB5 | exact RB6 | exact RB7 | exact RB8].
Qed.

(* ===================== the `_on` statements back at ExecF.RNG_all ===================== *)

Lemma cmF_rngs_all_on : forall (fr sp2 jj nn : Z) (mc : word -> option byte),
  RcMatch.cm_gate len fb = true -> cmInv_on fr sp2 jj nn mc ->
  rng_bytes RNG_all /\
  rng RNG_all IMG_LO (IMG_HI - IMG_LO) /\
  rng RNG_all (sp2 - BCMP_WRAP_K) BCMP_WRAP_K /\
  rng RNG_all (f + 18) 32 /\
  rng RNG_all (8 * (shadow_addr (f + 18) / 8))
              (8 * (shadow_addr (f + 18 + 32 - 1) / 8) + 8 - 8 * (shadow_addr (f + 18) / 8)) /\
  rng RNG_all (fr + 112) 32 /\
  rng RNG_all (8 * (shadow_addr (fr + 112) / 8))
              (8 * (shadow_addr (fr + 112 + 32 - 1) / 8) + 8 - 8 * (shadow_addr (fr + 112) / 8)) /\
  rng RNG_all (shadow_addr fr) 24.
Proof.
  intros fr sp2 jj nn mc G INVk.
  assert (L : 50 <= len).
  { destruct (Z.leb_spec 50 len) as [L|L]; [exact L|]. exfalso. unfold RcMatch.cm_gate in G.
    rewrite (proj2 (Z.leb_gt 50 len) L) in G. cbn [andb] in G. discriminate G. }
  destruct (HF L) as (Hf0 & Hf50 & _ & _).
  pose proof INVk as INV. destruct INV as (FK & _).
  pose proof (cm_geo fr sp2 jj nn FK) as (G8 & Gfs & G16 & Gsp & Gc).
  pose proof (fk_facts_on fr sp2 jj nn FK) as (FR8 & FRpos & FR192 & _).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (FRgt & FRhi).
  pose proof HK as HKb. pose proof RS as RSb. pose proof HAE as HAEb. unfold APPMEM_END in HAEb.
  assert (RB1 : rng_bytes RNG_all) by (intros b j _ _ _; exact I).
  assert (RB2 : rng RNG_all IMG_LO (IMG_HI - IMG_LO)) by (apply rng_all; unfold IMG_LO, IMG_HI; lia).
  assert (RB3 : rng RNG_all (sp2 - BCMP_WRAP_K) BCMP_WRAP_K)
    by (apply rng_all; unfold BCMP_WRAP_K; clear -Gsp HKb RSb; lia).
  assert (RB4 : rng RNG_all (f + 18) 32) by (apply rng_all; clear -Hf0 Hf50; lia).
  assert (RB5 : rng RNG_all (8 * (shadow_addr (f + 18) / 8))
                  (8 * (shadow_addr (f + 18 + 32 - 1) / 8) + 8 - 8 * (shadow_addr (f + 18) / 8)))
    by (apply rng_all; unfold shadow_addr, ASAN_K; clear -Hf0 Hf50; Z.div_mod_to_equations; lia).
  assert (RB6 : rng RNG_all (fr + 112) 32) by (apply rng_all; clear -FRpos FRhi RSb; lia).
  assert (RB7 : rng RNG_all (8 * (shadow_addr (fr + 112) / 8))
                  (8 * (shadow_addr (fr + 112 + 32 - 1) / 8) + 8 - 8 * (shadow_addr (fr + 112) / 8)))
    by (apply rng_all; unfold shadow_addr, ASAN_K; clear -FRpos FRhi RSb; Z.div_mod_to_equations; lia).
  assert (RB8 : rng RNG_all (shadow_addr fr) 24)
    by (apply rng_all; unfold shadow_addr, ASAN_K; clear -FRpos FRhi RSb; Z.div_mod_to_equations; lia).
  exact (conj RB1 (conj RB2 (conj RB3 (conj RB4 (conj RB5 (conj RB6 (conj RB7 RB8))))))).
Qed.

Lemma cmF_sh24_all_on : forall (fr sp2 jj nn : Z) (mc : word -> option byte),
  cmInv_on fr sp2 jj nn mc -> rng RNG_all (shadow_addr fr) 24.
Proof.
  intros fr sp2 jj nn mc INVk.
  pose proof INVk as INV. destruct INV as (FK & _).
  pose proof (fk_facts_on fr sp2 jj nn FK) as (FR8 & FRpos & _).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (_ & FRhi).
  pose proof RS as RSb.
  apply rng_all; unfold shadow_addr, ASAN_K; clear -FRpos FRhi RSb; Z.div_mod_to_equations; lia.
Qed.

Corollary cm_tail_of_F_on : forall (Q : machine_state -> Prop) (fr sp2 jj nn : Z),
  cmXt_F_on RNG_all Q fr sp2 jj nn ->
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
  apply (evtF_evt rsegs RNG_all).
  exact (cm_tail_F_on RNG_all Q fr sp2 jj nn KX mc r x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6
           Er INVk (cmF_sh24_all_on fr sp2 jj nn mc INVk)).
Qed.

Corollary cm_none_holds_of_F_on : forall (Q : machine_state -> Prop),
  (forall (fr sp2 jj nn : Z), cmXt_F_on RNG_all Q fr sp2 jj nn) -> cmNone_on Q.
Proof.
  intros Q KX fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs3 rs4 rs5 rs8 rs9 rs10
    rt3 rt4 rt5 rt6 Hw INVk.
  apply (evtF_evt rsegs RNG_all).
  exact (cm_none_holds_F_on RNG_all Q fr sp2 jj nn (KX fr sp2 jj nn) mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6
           ra7 rs3 rs4 rs5 rs8 rs9 rs10 rt3 rt4 rt5 rt6 Hw INVk (cmF_sh24_all_on fr sp2 jj nn mc INVk)).
Qed.

Corollary cm_hit_holds_of_F_on : forall (Q : machine_state -> Prop),
  (forall (fr sp2 jj nn : Z), cmXt_F_on RNG_all Q fr sp2 jj nn) -> cmHit_on Q.
Proof.
  intros Q KX fr sp2 jj nn r mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs4 rs5 rs8 rs9 rs10
    rt3 rt4 rt5 rt6 Hw INVk.
  apply (evtF_evt rsegs RNG_all).
  exact (cm_hit_holds_F_on RNG_all Q fr sp2 jj nn (KX fr sp2 jj nn) r mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6
           ra7 rs4 rs5 rs8 rs9 rs10 rt3 rt4 rt5 rt6 Hw INVk (cmF_sh24_all_on fr sp2 jj nn mc INVk)).
Qed.

Corollary cm_bcmp_of_F_on : forall (i : nat) (Q : machine_state -> Prop), (i < 11)%nat ->
  (forall (fr sp2 jj nn : Z),
     ((i + 1 < 11)%nat -> cmLH_F_on RNG_all (i + 1)%nat Q fr sp2 jj nn) /\
     cmNone_F_on RNG_all Q fr sp2 jj nn /\ cmHit_F_on RNG_all Q fr sp2 jj nn) ->
  cmBC_on i Q.
Proof.
  intros i Q Hi K fr sp2 jj nn mc rra rt0 rt1 rt2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 G Hi11 Hnd INV ADb BB.
  destruct (K fr sp2 jj nn) as (KL & KN & KH).
  destruct (cmF_rngs_all_on fr sp2 jj nn mc G INV) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
  apply (evtF_evt rsegs RNG_all).
  exact (cm_bcmp_F_on RNG_all i Q fr sp2 jj nn Hi KL KN KH mc rra rt0 rt1 rt2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6
           G Hi11 Hnd INV ADb BB R1 R2 R3 R4 R5 R6 R7 R8).
Qed.

Corollary cm_model_ret_of_F_on : forall (i : nat) (Q : machine_state -> Prop) (fr sp2 jj nn : Z), (i < 11)%nat ->
  cmBC_F_on RNG_all i Q fr sp2 jj nn ->
  forall (m1 : word -> option byte)
         (rra rt0 rt1 rt2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word) (ms' : machine_state),
  RcMatch.cm_gate len fb = true -> (forall j, (j < i)%nat -> nth j DECLS [] <> cm_blk fb) ->
  cmInv_on fr sp2 jj nn m1 -> addressable m1 (fr + 112) 32 ->
  reac_box_model_block_post_on (Z_to_bv 64 0x846cc) (Z_to_bv 64 sp2) gp tp (Z_to_bv 64 S) (Z_to_bv 64 CA)
    (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 (CM_T + 296 * Z.of_nat i)) (Z_to_bv 64 (fr + 112))
    (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) (Z_to_bv 64 (11 - Z.of_nat i))
    (Z_to_bv 64 1) (Z_to_bv 64 (-8)) s11 F fc m1 (CM_T + 296 * Z.of_nat i) 0 (fr + 112) FS (cm_row i) [] ms' ->
  evt rsegs Q ms'.
Proof.
  intros i Q fr sp2 jj nn Hi KB m1 rra rt0 rt1 rt2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 ms' G Hnd INV1k ADm Hpost.
  destruct (cmF_rngs_all_on fr sp2 jj nn m1 G INV1k) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
  apply (evtF_evt rsegs RNG_all).
  exact (cm_model_ret_F_on RNG_all i Q fr sp2 jj nn Hi KB m1 rra rt0 rt1 rt2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 ms'
           G Hnd INV1k ADm R1 R2 R3 R4 R5 R6 R7 R8 Hpost).
Qed.

End MatchFOn.

(* `Check N.` before each `Print Assumptions N.`: the build log attributes each Axioms block to its name. *)
Check cm_tail_F_on.
Print Assumptions cm_tail_F_on.
Check cm_none_holds_F_on.
Print Assumptions cm_none_holds_F_on.
Check cm_hit_holds_F_on.
Print Assumptions cm_hit_holds_F_on.
Check cm_bcmp_F_on.
Print Assumptions cm_bcmp_F_on.
Check cm_model_ret_F_on.
Print Assumptions cm_model_ret_F_on.
Check cm_model_ret_rb_F_on.
Print Assumptions cm_model_ret_rb_F_on.
