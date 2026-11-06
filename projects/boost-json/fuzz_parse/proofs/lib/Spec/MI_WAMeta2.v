(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Read MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4
  MI_WFree2 MI_Ledger MI_WAMeta.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~06mstate37Corelib4Init9Datatypesk64bool0bc_init_done03ctx04mctx08s_secret0dset_init_done0aset_secret07upd_ctx46Stdlib6ZArith6BinInt1Zqb3eqb79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4SpecaMI_WAMeta2~~~~~~s97am_initk64list37Corelib4Init5Logichhc3and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MI_Inv~~~~~~hj74INVLhhc2eq37Corelib7Numbers7BinNumsho31Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4KInv~~~~~~hq14mledhj73blkhj76extras79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec9MI_WAMeta~~~~~~hv68AM_frame04aptr05lhead05s_ctxk63natho31N35stdpp7numbers1Nim26eq_dec35stdpp7numbers1Zind6eq_dec04area25stdpp9countableipebN_countableipebZ_countableipeeprod_countable25stdpp9decidableitfbprod_eq_dechhc2ex25stdpp4gmapjg54gmapk64Nonek63nilk66option37Corelib4Init5Peanojif2le07s_areas25stdpp4basejl24size25stdpp8fin_mapsjm68map_sizejg59gmap_foldk61Sk66lengthhj77x_freshhj76x_idlehj76x_pendhj76x_zomb05LFree0h2c_avail_meta_counthhc2ors94SNAPs95AREAS89OSSVerify6Proofsaboost_jsonafuzz_parse3lib4SpecaMI_WAMeta22AM~~~~~~jv67SNAPPRE79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec7MI_Tree~~~~~~kk65ftreehv67L_frame07am_takeqb2lt04metak64Somek63snd04PGSZqb2lejl26lookupjg5bgmap_lookuphj75mslot79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec8MI_Pres4~~~~~~ku76xfreshhv6acarve_rest06NSLOTS04aadd0h2c_avail_meta_areas04optr07s_metasqb6modulok64true09am_finish0h7c_avail_meta_area_count0cam_after_brkk64prodhq1dlbrk_pages_okhq19ld_brkreghq19ld_groupshq18ld_metashq17ld_resv0aalloc_metak64conshhc3not79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec8MI_Pres3~~~~~~mh75xidle36Stdlib5Lists4Listmm02In" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition am_init : ltac2:(zQ "10!je>2st$0$0") := ltac2:(zQ "a0!le!je!m5!n2!n7!nd!o7!p6!q2!s3\2st$1M0\0$0$1@2$9@1$2@1$3^1Z@2$8\1c$4@2$6+1@2$7@1$5^2^1^1^1").

Lemma INVL_am_init : ltac2:(zQ "f0!hgb!hh5!hj0!hn5!hnd!hpc!htd!hu5!huc!ij7!ik3!m5!ik9!je!il0>1X$8>2st$d>1L$6>2BL@1$1$7>2LS>0$c@1$1$a>0@5$3^5^4^3^2^1@2$2@5$3^6@1$0^5^4^3^2@2$2@3$4$5@1$b@1$e@1$0^5+1@2$9^5@1$0^5").
Proof. intros X st L BL LS.
  intros INV. pose proof INV as (IR & IA & IM & IL & IG & IS & ISH). unfold am_init, ctx.
  destruct (ia_secret _ IA) as [S0 [(I0 & C0 & A0)|(I1 & C1)]].
  - rewrite I0. cbn. set (st' := upd_ctx _ st).
    split; [| split; [reflexivity| constructor; cbn; auto; first [reflexivity| lia]]].
    split; [| split; [| split; [| split; [| split; [| split]]]]].
    + destruct IR; constructor; try assumption.
    + destruct IA; constructor; try assumption.
      * cbn. split; [exact S0|]. right. auto.
      * intros a ar Ha. change (s_areas st') with (s_areas st) in Ha. rewrite A0 in Ha. rewrite lookup_empty in Ha. discriminate.
    + apply (inv_M_ext X st st'); [reflexivity| reflexivity| exact IM].
    + apply (inv_L_ext st st'); [reflexivity| reflexivity| intros h; destruct h; reflexivity| exact IL].
    + destruct IG as [G1 G2 G3 G4 G5 GOE]; constructor; try assumption.
      intros m b ai Hb. apply (group_ok_ext X st st'); [reflexivity| reflexivity| auto| exact (G1 m b ai Hb)].
    + apply (inv_S_ext X st st' BL); [reflexivity| reflexivity| reflexivity| apply blk_regions_kept_refl; reflexivity| exact IS].
    + apply (inv_SH_view st st'); try reflexivity. exact ISH.
  - rewrite I1. cbn. split; [exact INV|]. split; [exact I1| apply amf_refl].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition SNAP : ltac2:(zQ "40!hh5!il7!hu5!je>1N$1>2BL@1$0$2>2s1$3P") := ltac2:(zQ "i73!ik3!hpc!ild!in3!ioe!ip8!hj0!iqf!ire!isd!iv0!hh5!hnd!ivf!jh1!je!jh9!ji0!ji6!jk3!htd!huc!ik9!jk9!jle!jn6!jo2!jof!jp3!il7!hn5!hu5!jpc!jq7!jr1!jrb!js5!jsc!il0&@4$e$0@4$a$2$3$1$4@6$9$2$3$7$1$4$8$5&@4$ha$0@4$a$2$3$1$4@6$9$2$3$7$1$4$8$5&@4$h9$0$5~0~1\1N$hd\2BL@1$b$hf\2s1$f@2$d$h5\2Xc$h5@2$d$f\3stc$f@2$d$h4\2Lc$h4@2$d>0$h6@1$b$0\3LSc>0$h6@1$b$0@2$6@5$he^4^3^2^6^1@2$6@3$c@1$b$0@1^1$i4@1$h1$0@2$6@3$c$1@1$i5@1$i6^3Z@2$6@2$h3@2$hc$0@1$i1^4^7@2$6@3$c@1$b$0@1$i3^4@1$h1$0@2$6@3$c@1$h2$0@1$i2^4@1$h0$0@2$6@3$c@1$h2$0@1$i0^4@1$h0$0@2$h3@3$h8~0~2@1$h7^5@1$hb@3$h8~0~2@1$h7^3").
Definition AREAS : ltac2:(zQ "40!je!hh5!il7!hu5>1N$2>2BL@1$1$3>2s0$0>2s1$0P") := ltac2:(zQ "h63!ild!hpc!in3!ioe!ik3!ip8!iqf!ire!isd!iv0!jh1!je!jk9!jle!jn6!jo2!hh5!il7!ju1!jk3!hu5!ju7&@4$a$4@4$9$0$2$1$3@6$8$0$2$6$1$3$7$5&@4$f$4@4$9$0$2$1$3@6$8$0$2$6$1$3$7$5&@4$e$4$5~0~1\1N$h1\2BL@1$h0$h4\2s0$b\2s1$b@2$h2@2$h3@3$d~0~2@1$c^1@3$d~0~2@1$c^2@3$h5^4^3^1").

Lemma AREAS_refl : ltac2:(zQ "50!hh5!il7!hu5!jue!je>1N$1>2BL@1$0$2>1s$4@4$3^3^2^1^1"). Proof. intros N BL s. left. lia. Qed.
Lemma AREAS_eq : ltac2:(zQ "h20!ild!hpc!je!jk9!in3!ioe!hh5!il7!hnd!hu5!jue!ik3!ip8!iqf!ire!isd!iv0!jh1>1N$7>2BL@1$6$9>2s0$2>2s1$2>0@3$8@4$h1$b@4$h0$0$4$1$5@6$f$0$4$d$1$5$e$c@1$3^1@1$3^2@4$a^5^4^3^2"). Proof. intros N BL s0 s1. intros E. left. rewrite E. lia. Qed.
Lemma SNAP_le : ltac2:(zQ "h53!ild!hpc!in3!ioe!ik3!ip8!iqf!ire!isd!iv0!jh1!ju7!je!jk9!jle!jn6!jo2!hh5!il7!jk3!hu5&@4$a$4@4$9$0$2$1$3@6$8$0$2$6$1$3$7$5&@4$h0$4@4$9$0$2$1$3@6$8$0$2$6$1$3$7$5&@4$f$4$5~0~1>1N$h2>2BL@1$h1$h4>2s1$c>2s2$c>0@3$b^4^3^2>0@2$h3@3$e~0~2@1$d^2@3$e~0~2@1$d^3@3$b^6^5^3").
Proof. intros N BL s1 s2. intros (Xc & stc & Lc & LSc & A & B & C & D & E & F & G & H) LE. exists Xc, stc, Lc, LSc. split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [exact D|]. split; [exact E|]. split; [exact F|]. split; [exact G| lia]. Qed.
Lemma AREAS_trans : ltac2:(zQ "50!jue!je!hh5!il7!hu5>1N$3>2BL@1$2$4>2s0$1>2s1$1>2s2$1>0@4$0^5^4^3^2>0@4$0^6^5^3^2@4$0^7^6^5^3").
Proof. intros N BL s0 s1 s2.
  intros A B. destruct B as [B|B]; [| right; exact B].
  destruct A as [A|A]; [left; lia| right; exact (SNAP_le N BL s1 s2 A B)].
Qed.
Lemma AREAS_eq_r : ltac2:(zQ "h20!je!ild!hpc!jue!jk9!in3!ioe!hh5!il7!hnd!hu5!ik3!ip8!iqf!ire!isd!iv0!jh1>1N$8>2BL@1$7$a>2s0$0>2s1$0>2s2$0>0@4$3^5^4^3^2>0@3$9@4$h1$b@4$h0$1$5$2$6@6$f$1$5$d$2$6$e$c@1$4^2@1$4^3@4$3^7^6^5^3").
Proof. intros N BL s0 s1 s2. intros A E. eapply AREAS_trans; [exact A| apply AREAS_eq; exact E]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AM.
Variables (T : Type) (BL : list blk) (Post : mled -> T -> Prop) (k : mstate -> optr -> M T) (bail : M T).
Variables (X : extras) (st0 : mstate) (L0 : mled) (N : nat).
Hypothesis HXF : ltac2:(zQ "50!ik3!jh9!ji6!hnd!jpc@3$3@1$2$0@1$4?1X@1$1$0").   (* [comment removed for export] *)
Hypothesis HXI : ltac2:(zQ "40!jp3!jk3!jq7!ik3@2$1@2$0$3@1$2?1X?1N").   (* [comment removed for export] *)
Hypothesis HXZ : ltac2:(zQ "50!ik3!hh5!ji0!hnd!jrb@3$3@1$1$0@1$4?1X@1$2$0").
Hypothesis HXP : ltac2:(zQ "50!ik3!jh9!ji6!hnd!jr1@3$3@1$2$0@1$4?1X@1$1$0").
Hypothesis KN : ltac2:(zQ "b0!ik3!jh9!hh5!htd!hn5!ko5!ij7!koe!jue!ik9!je>3st1$a>2L1$3>3LS1>0$9@1$2$0>0@5$4?1X^3^2?2BL^1>0@2$6?3st0^4>0@2$7?2L0^4>0@4$8?1N?2BL?3st0^6@4$5?1T^6@2?1k^7@1$1$0?4Post").
Hypothesis KS : ltac2:(zQ "h00!ik3!jq7!kqd!mg9!hh5!mh0!htd!hn5!ml7!ko5!ij7!koe!jue!ik9!je!mn3>3st1$e>2L1$6>3LS1>0$d@1$4$0>1m$0>0@5$7@2$8?1X@3$3$0^1@1$1?1X^4^3?2BL^2>0@1$5@3$f$0^2@1$1?1X>0@2$a?3st0^6>0@2$b?2L0^6>0@4$c?1N?2BL?3st0^8@4$9?1T^8@2?1k^9@2$2$0^6?4Post").

(* [comment removed for export] *)
Definition SNAPPRE : ltac2:(zQ "10!je>1s$0P") := ltac2:(zQ "h80!ik3!hh5!hj0!hnd!ivf!hpc!je!ild!htd!ik9!jk9!in3!ioe!ji0!hn5!js5!ip8!jsc!il0!iqf!ire!isd!iv0!jh1\1s$6@2$4$6\3stc$6@2$4$8\2Lc$8@2$4>0$9@1$1$0\3LSc>0$9@1$1$0@2$2@5$e?1X^3^2?2BL^1@2$2@3$3@1$1$0@1^1$f@1$d$0@2$2@3$3$5@1$h1@1$h2^3Z@3$3@4$h7$0@4$h6$7$b$5$c@6$h5$7$b$h3$5$c$h4$h0@1$a^4@1$a^3").
Lemma SNAPPRE_eq : ltac2:(zQ "f0!ild!hpc!kjb!je!jk9!in3!ioe!hnd!ik3!ip8!iqf!ire!isd!iv0!jh1>1s$3>2s'$3>0@1$2^2>0@3$7@4$e$8@4$d$0$5$1$6@6$c$0$5$a$1$6$b$9@1$4^2@1$4^3@1$2^3").
Proof. intros s s'. intros (stc & Lc & LSc & A & B & C & D) E. exists stc, Lc, LSc. rewrite E. auto. Qed.
Lemma SNAPPRE_snap : ltac2:(zQ "h53!ild!hpc!in3!ioe!ik3!ip8!iqf!ire!isd!iv0!jh1!je!jk9!jle!jn6!jo2!jof!il7!hnd!kjb!ju7&@4$a$4@4$9$0$2$1$3@6$8$0$2$6$1$3$7$5&@4$f$4@4$9$0$2$1$3@6$8$0$2$6$1$3$7$5&@4$e$4$5~0~1>1s$b>2s'$b>0@1$h3^2>0@3$h2$h1@3$d~0~2@1$c^2@1$h0@3$d~0~2@1$c^3@3$h4?1N?2BL^3").
Proof. intros s s'.
  intros (stc & Lc & LSc & A & B & C & D) E. exists X, stc, Lc, LSc. rewrite E, D. split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [exact HXI|]. split; [exact HXZ|]. split; [exact HXP|]. split; [exact HXF| lia].
Qed.

Lemma am_take_ft : ltac2:(zQ "e0!hh5!htd!hn5!ko5!ij7!koe!jue!kp9!ik3!jsc!ik9!je!il0!kq2>2st$b>1L$1>2LS>0$a@1$0$8>0@5$2?1X^3^2?2BL^1>0@2$4?3st0^4>0@2$5?2L0^4>0@4$6?1N?2BL?3st0^6>0@2$dZ@1$9@1$c^7@4$3?1T^7@4$7?1T^8?1k?4bail?4Post").
Proof. intros st L LS.
  intros INV AF LF AR HC. destruct (am_take_ok X st L BL LS INV HC k bail) as (m & st2 & -> & INV2 & AF2 & NI & EA).
  eapply KS; [exact INV2| exact NI| exact (amf_trans _ _ _ AF AF2)| exact LF| exact (AREAS_eq_r _ _ _ _ _ AR EA)].
Qed.

Lemma am_carve_ft : ltac2:(zQ "ie0!hpc!ild!ik3!in3!ioe!hnd!ip8!kq7!iqf!ire!isd!iv0!il0!jh9!kqd!ji6!kr4!kra!ks0!ks5!jh1!ksf!hh5!hj0!htd!hn5!kte!li7!ko5!ij7!koe!lj1!kjb!ljf!lk7!kp9!lkd!jsc!m5!ik9!je!lm2!jk9!lm8!kq2!ln1>1s$i8>1p$2>1L$h8>2LS>0$i7@1$h6$2>0@5$h9@2$hb?1X@2$e$2^3^4^2?2BL^1>0@3$5$i9@1$i4@1$c^5@2$e$2@2$i2^4+hgg0>0@3$5@1$f$6@6$h3$2$6@4$h4$2@4$b$1$3$0$4@6$a$1$3$8$0$4$9$6@4$h5$2@4$b$1$3$0$4@6$a$1$3$8$0$4$9$6^5@1$ia^6@1$d$6>0>1k$0>0@2$h7@2$h2Z^1@2$ic^1$i1@3$5@1$f$7@6$h3$2$7@4$h4$2@4$b$1$3$0$4@6$a$1$3$8$0$4$9$7@4$h5$2@4$b$1$3$0$4@6$a$1$3$8$0$4$9$7@2$ha^8^2@1$ib^9@1$d$7>0@2$h2$h1@3$h0$1$0^7>0@3$5$0@2$id@3$h0$1$0^8$h1Z>0@3$5$0@1$i6@1$c^a+1>0@3$5$0@1$i5@1$c^bZ>0@1$i0^c>0@2$hd?3st0^d>0@2$he?2L0^c@4$hc?1T^d@4$i3?1T@2$hf^f^e?1k?4bail?4Post").
Proof. intros s p L LS.
  intros INV H1 H2 H3 H4 H5 H6 HZ SN AF LF. destruct (INVL_carve (xfresh X (Some p)) s L BL LS p INV H1 H2 H3 H4 H5 H6 eq_refl HZ) as (INV' & AF' & HC & SZ).
  replace (xfresh (xfresh X (Some p)) None) with X in INV' by (destruct X; cbn in HXF |- *; subst; reflexivity).
  eapply am_take_ft; [exact INV'| exact (amf_trans _ _ _ AF AF')| exact LF| right; exact (SNAPPRE_snap _ _ SN SZ)| exact HC].
Qed.

Lemma am_finish_ft : ltac2:(zQ "h40!il0!hnd!hpc!hh5!lna!htd!hn5!ko5!ij7!koe!kjb!jue!lo1!ik3!loc!jsc!m5!ik9!je!kq2>2st$h2>1L$5>2LS>0$h1@1$3$d>0@5$6?1X^3^2?2BL^1>0@2$8?3st0^4>0@2$9?2L0^4>0@2$h3Z@1$e@1$0^6>0@3$1$2@1$h0@1$0^7+1>0@3$1$2@1$f@1$0^8Z>0@1$a^9>0@4$b?1N?2BL?3st0^a@4$7?1T^a@5$c?1T^b$4?1k?4bail?4Post").
Proof. intros st L LS.
  intros INV AF LF HC HI HZ SN AR.
  destruct (ir_cursor _ _ _ (proj1 INV)) as (C1 & C2 & C3).
  destruct (c_avail_meta_areas (ctx st)) as [[rid off]|] eqn:EC; [| exfalso; exact (C2 HC EC)].
  destruct (C3 _ _ EC) as (r & Hr & K & P1 & P2 & P3 & P4).
  unfold am_finish. rewrite EC. cbn [snd]. rewrite (proj2 (Z.eqb_eq _ _) P2). cbn [negb].
  apply ftree_vis; [reflexivity| reflexivity| exact (ma_event_pre X st L BL LS rid off INV EC HC)| |].
  - intros a Ha. cbn in Ha. rewrite Ha. cbn [negb].
    change (if (a =? 0) || (a =? TWO64 - ENOSYS) then am_carve st (rid, off) k bail else k st None)
      with (if (a =? 0) || (a =? TWO64 - ENOSYS) then am_carve st (rid, off) k bail else k st None).
    cbn [event_post]. destruct ((a =? 0) || (a =? TWO64 - ENOSYS)).
    + rewrite am_carve_eq.
      destruct (INVL_meta_adv X st L BL LS rid off INV EC HC HXF) as (INV' & F1 & F2 & F3 & F4 & F5 & F6 & AF').
      eapply am_carve_ft; [exact INV'| exact F1| exact F2| exact F3| exact F4| exact F5| rewrite F6; exact HI| exact HZ| apply (SNAPPRE_eq st); [exact SN| reflexivity]| exact (amf_trans _ _ _ AF AF')|].
      destruct LF; constructor; assumption.
    + eapply KN; [exact INV| exact AF| exact LF| exact AR].
  - intros a Ha. cbn in Ha. rewrite Ha. exact I.
Qed.

Lemma am_after_brk_ft : ltac2:(zQ "h20!hnd!hpc!il0!hh5!lna!htd!hn5!ko5!ij7!koe!kjb!jue!lq6!ik3!jsc!m5!ik9!je>2st$h1>1L$5>2LS>0$h0@1$3$d>0@5$6?1X^3^2?2BL^1>0@2$8?3st0^4>0@2$9?2L0^4>0@3$0$1@1$f@1$2^6+1>0@3$0$1@1$e@1$2^7Z>0@1$a^8>0@4$b?1N?2BL?3st0^9@4$7?1T^9@5$c?1T^a$4?1k?4bail?4Post").
Proof. intros st L LS.
  intros INV AF LF HI HZ SN AR. unfold am_after_brk.
  destruct (Z.eqb_spec (c_avail_meta_area_count (ctx st)) 0) as [HC|HC].
  - apply ftree_vis; [reflexivity| reflexivity| exact (nm_event_pre X st L BL LS INV)| |].
    + intros a Ha. unfold answer_ok in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [andb] in Ha.
      rewrite (mmap_answer_ok_eq X st L (proj1 INV)) in Ha. unfold ctx. rewrite Ha. cbn [negb].
      unfold event_post. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_NONE =? PROT_NONE) with true. cbn [andb].
      destruct (is_err a) eqn:NE.
      * eapply KN; [exact INV| exact AF| exact LF| exact AR].
      * destruct (INVL_new_meta X st L BL LS a INV HC Ha NE) as (INV' & HC' & HI' & AF').
        eapply am_finish_ft; [exact INV'| exact (amf_trans _ _ _ AF AF')| destruct LF; constructor; assumption| exact HC'| rewrite HI'; exact HI| exact HZ
                             | apply (SNAPPRE_eq st); [exact SN| reflexivity]| apply (AREAS_eq_r _ _ _ _ _ AR); reflexivity].
    + intros a Ha. unfold answer_ok in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [andb] in Ha.
      rewrite (mmap_answer_ok_eq X st L (proj1 INV)) in Ha. unfold ctx. rewrite Ha. exact I.
  - eapply am_finish_ft; [exact INV| exact AF| exact LF| pose proof (proj1 (ir_cursor _ _ _ (proj1 INV))); unfold ctx in HC; lia| exact HI| exact HZ| exact SN| exact AR].
Qed.

Lemma lbrk_pages_ok_ext : ltac2:(zQ "c0!hpc!lr4!hnd!hh5!lrb!lsc!lt9!lu6!lv2!htd!le!ji6>2L1$9>2L2$9>2lo$0>3len$0>0@3$2@1$3@2$1$0$0@1$8^4@1$8^3>0@3$2@1$3@2$1$0$0@1$6^5@1$6^4>0@3$2@1$3@2$1@2$1$0$0$0@1$7^6@1$7^5>0@3$2@1$b@2$1$0$0@1$5^7@1$5^6@3$2$a@3$4^8^6^5@3$4^7^6^5").
Proof. intros L1 L2 lo len. intros E1 E2 E3 E4. unfold lbrk_pages_ok, lranges. rewrite E1, E2, E3, E4. reflexivity. Qed.

Theorem alloc_meta_ft : ltac2:(zQ "b0!hh5!htd!hn5!ko5!ij7!koe!jue!lvd!ik3!ik9!je>2st$a>1L$1>2LS>0$9@1$0$8>0@5$2?1X^3^2?2BL^1>0@2$4?3st0^4>0@2$5?2L0^4>0@4$6?1N?2BL?3st0^6@4$3?1T^6@4$7?1T^7?1k?4bail?4Post").
Proof. intros st L LS.
  intros INV0 AF0 LF AR0.
  destruct (INVL_am_init X st L BL LS INV0) as (INV & HI & AFi).
  pose proof (amf_trans _ _ _ AF0 AFi) as AF.
  assert (AR : AREAS N BL st0 (am_init st)) by (apply (AREAS_eq_r _ _ _ _ _ AR0); unfold am_init; destruct (c_init_done (ctx st) =? 0); reflexivity).
  clear AF0 AFi INV0 AR0.
  unfold alloc_meta. fold (am_init st). set (s := am_init st) in *. clearbody s.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  (* [comment removed for export] *)
  destruct (c_free_meta_head (ctx s)) as [m|] eqn:EFH.
  { pose proof (il_head _ _ IL LFree) as HH. cbn in HH. unfold ctx in EFH. rewrite EFH in HH.
    destruct (LS LFree) as [|m' rest] eqn:ELS; [discriminate|]. cbn in HH. inversion HH. subst m'.
    pose proof (INVL_dequeue X (xidle X (m :: x_idle X)) s L BL LS m LFree [] rest INV ltac:(rewrite ELS; reflexivity) ltac:(right; split; reflexivity)) as INV1.
    destruct (dequeue_frame LFree m s) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & FC).
    eapply KS; [exact INV1| | | exact LF| exact (AREAS_eq_r _ _ _ _ _ AR F4)].
    { intros Hin. apply (proj2 (im_idle _ _ _ IM m Hin)). exists LFree. rewrite ELS. left. reflexivity. }
    eapply amf_trans; [exact AF|]. destruct FC. constructor; auto; try congruence.
    all: try (intros sc; change (active (dequeue LFree m s) sc) with (get_head (dequeue LFree m s) (LActive sc)); rewrite dequeue_head;
              destruct (decide (LActive sc = LFree)); [discriminate| reflexivity]).
    all: try (intros sc; unfold usage, ctx; rewrite cb_usage; reflexivity).
    all: try (intros rid r H _; rewrite F1; exact H).
    all: rewrite ?F3; lia. }
  (* [comment removed for export] *)
  destruct (Z.eqb_spec (c_avail_meta_count (ctx s)) 0) as [HAC|HAC]; cbn [negb].
  2:{ eapply am_take_ft; [exact INV| exact AF| exact LF| exact AR| pose proof (proj1 (ia_avail _ IA)); unfold ctx in HAC; lia]. }
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (SN : SNAPPRE s).
  { exists s, L, LS. split; [exact INV|]. split; [| split; [unfold ctx in HAC; exact HAC| reflexivity]].
    pose proof (il_head _ _ IL LFree) as HH. cbn in HH. unfold ctx in EFH. rewrite EFH in HH. destruct (LS LFree); [reflexivity| discriminate]. }
  destruct (Z.eqb_spec (c_avail_meta_area_count (ctx s)) 0) as [HC|HC]; cbn [andb].
  2:{ eapply am_after_brk_ft; [exact INV| exact AF| exact LF| exact HI| unfold ctx in HAC; exact HAC| exact SN| exact AR]. }
  pose proof (ir_brk _ _ _ IR) as IBK. unfold ctx. destruct (c_brk (s_ctx s)) as [| |rid off] eqn:EBRK; cbn [negb].
  - (* [comment removed for export] *)
    destruct IBK as [BP NB].
    apply ftree_vis; [reflexivity| reflexivity| left; auto| |].
    2:{ intros cur Hc. cbn in Hc. rewrite Hc. exact I. }
    intros cur Hc. cbn in Hc. rewrite Hc. cbn [negb]. cbn [event_post Z.eqb].
    set (L1 := KInv.set_brkph (BPQueried cur) L).
    set (base := round_up_pg cur). set (new := base + 2 * PGSZ).
    assert (NZ : (new =? 0) = false).
    { apply Z.eqb_neq. unfold new, base. pose proof (round_up_ge cur). unfold brk0_answer_ok in Hc.
      apply Bool.andb_true_iff in Hc as [Hc _]. apply Bool.andb_true_iff in Hc as [Hc _]. apply Z.ltb_lt in Hc. unfold PGSZ. lia. }
    apply ftree_vis; [reflexivity| reflexivity| right; left; exists cur; split; reflexivity| |].
    + intros r Hr. unfold answer_ok in Hr. rewrite NZ in Hr. unfold L1 in Hr. cbn [KInv.ld_brk KInv.set_brkph] in Hr.
      apply Bool.andb_true_iff in Hr as [Hb Hp]. rewrite Hb. cbn [negb].
      unfold event_post. rewrite NZ. unfold L1. cbn [KInv.ld_brk KInv.set_brkph].
      destruct (Z.eqb_spec r new) as [->|NE]; cbn [negb].
      * cbn [negb orb] in Hp.
        rewrite (lbrk_pages_ok_ext (KInv.set_brkph (BPQueried cur) L) L) in Hp by reflexivity.
        rewrite (brk_pages_ok_eq X s L IR) in Hp. fold base in Hp. rewrite Hp. cbn [negb].
        apply ftree_vis; [reflexivity| reflexivity| right; exists cur; cbn; repeat split; reflexivity| |].
        -- intros rg Hg. unfold answer_ok in Hg. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false in Hg. cbn [andb] in Hg.
           fold base in Hg. rewrite Hg. cbn [negb]. unfold event_post. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false. cbn [andb].
           set (st1 := new_region RKBrk base (2 * PGSZ) s). destruct st1 as [s1 rid] eqn:ES1.
           assert (Erid : rid = s_next_rid s) by (unfold st1, new_region in ES1; inversion ES1; reflexivity).
           assert (Es1 : s1 = fst (new_region RKBrk base (2 * PGSZ) s)) by (unfold st1 in ES1; rewrite <- ES1 || idtac; unfold new_region in *; inversion ES1; reflexivity).
           subst rid s1.
           unfold am_after_brk, ctx. cbn [c_avail_meta_area_count s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk Z.eqb].
           unfold am_finish, ctx. cbn [c_avail_meta_areas s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk snd].
           change (PGSZ mod PGSZ =? 0) with true. cbn [negb].
           rewrite am_carve_eq.
           destruct (INVL_brk_first X s L BL LS cur INV EBRK HC ltac:(exact Hp) HXF (KInv.set_brkph (BPGuard cur) (KInv.set_brkph (BPQueried cur) L)) ltac:(repeat split; reflexivity))
             as (INV' & G1 & G2 & G3 & G4 & G5 & G6 & AF').
           eapply am_carve_ft; [exact INV'| exact G1| exact G2| exact G3| exact G4| exact G5| rewrite G6; exact HI| unfold ctx in HAC; exact HAC| apply (SNAPPRE_eq s); [exact SN| reflexivity]| exact (amf_trans _ _ _ AF AF')|].
           destruct LF; constructor; assumption.
        -- intros rg Hg. unfold answer_ok in Hg. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false in Hg. cbn [andb] in Hg.
           fold base in Hg. rewrite Hg. exact I.
      * destruct (INVL_brk_dead X s L (KInv.set_brkph BPDead (KInv.set_brkph (BPQueried cur) L)) BL LS INV eq_refl eq_refl eq_refl eq_refl eq_refl) as [INV' AF'].
        eapply am_after_brk_ft; [exact INV'| exact (amf_trans _ _ _ AF AF')| destruct LF; constructor; assumption| cbn; exact HI| cbn; unfold ctx in HAC; exact HAC
                                | apply (SNAPPRE_eq s); [exact SN| reflexivity]| apply (AREAS_eq_r _ _ _ _ _ AR); reflexivity].
    + intros r Hr. unfold answer_ok in Hr. rewrite NZ in Hr. unfold L1 in Hr. cbn [KInv.ld_brk KInv.set_brkph] in Hr.
      apply Bool.andb_false_iff in Hr. destruct Hr as [Hb|Hp].
      * rewrite Hb. exact I.
      * destruct (brk_answer_ok cur new r); [| exact I]. cbn [negb].
        apply Bool.orb_false_iff in Hp as [Hn Hp]. apply Bool.negb_false_iff in Hn. rewrite Hn. cbn [negb].
        rewrite (lbrk_pages_ok_ext (KInv.set_brkph (BPQueried cur) L) L) in Hp by reflexivity.
        rewrite (brk_pages_ok_eq X s L IR) in Hp. fold base in Hp. rewrite Hp. exact I.
  - (* [comment removed for export] *) eapply am_after_brk_ft; [exact INV| exact AF| exact LF| exact HI| unfold ctx in HAC; exact HAC| exact SN| exact AR].
  - (* [comment removed for export] *)
    destruct IBK as [BP (r & Hr & K & Elen)].
    pose proof (bg_event_pre X s L BL LS rid off INV EBRK) as PRE.
    set (old := conc s (rid, off)) in *. set (new := old + PGSZ) in *.
    assert (NZ : (new =? 0) = false).
    { apply Z.eqb_neq. unfold new, old, conc, get_region. rewrite Hr. cbn [fst snd]. pose proof (ir_shape _ _ _ IR _ _ Hr) as (S1 & _ & S3 & _). unfold PGSZ. lia. }
    assert (BR : ld_brkreg L = Some (r_base r, off)).
    { apply (proj2 (ir_brkreg _ _ _ IR (r_base r) off)). exists rid, r. auto. }
    assert (Eold : old = r_base r + off) by (unfold old, conc, get_region; rewrite Hr; cbn [fst snd]; reflexivity).
    apply ftree_vis; [reflexivity| reflexivity| exact PRE| |].
    + intros z Hz. unfold answer_ok in Hz. rewrite NZ, BP, BR in Hz. rewrite <- Eold in Hz.
      apply Bool.andb_true_iff in Hz as [Hb Hp]. rewrite Hb. cbn [negb].
      unfold event_post. rewrite NZ, BP, BR.
      destruct (Z.eqb_spec z new) as [->|NE]; cbn [negb].
      * cbn [negb orb] in Hp. rewrite (brk_pages_ok_eq X s L IR) in Hp. rewrite Hp. cbn [negb].
        unfold am_after_brk, ctx. cbn [c_avail_meta_area_count s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk Z.eqb].
        unfold am_finish, ctx. cbn [c_avail_meta_areas s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk snd].
        destruct (bg_region X s L BL LS rid off INV EBRK) as (r' & _ & _ & _ & _ & _ & _ & _ & OM & _).
        rewrite (proj2 (Z.eqb_eq _ _) OM). cbn [negb].
        rewrite am_carve_eq.
        destruct (INVL_brk_grow X s L BL LS rid off INV EBRK HC HXF ltac:(exact Hp)) as (INV' & G1 & G2 & G3 & G4 & G5 & [G6 G7] & AF').
        replace (conc s (rid, off) - off) with (r_base r) in INV' by (unfold conc, get_region; rewrite Hr; cbn [fst snd]; lia).
        eapply am_carve_ft; [exact INV'| exact G1| exact G2| exact G3| exact G4| exact G5| rewrite G6; exact HI| rewrite G7; unfold ctx in HAC; exact HAC| | exact (amf_trans _ _ _ AF AF')|].
        { apply (SNAPPRE_eq s); [exact SN|]. destruct (bg_region X s L BL LS rid off INV EBRK) as (r0 & Hr0 & _). unfold adv. cbn -[upd_region]. unfold upd_region, get_region. rewrite Hr0. reflexivity. }
        destruct LF; constructor; assumption.
      * destruct (INVL_brk_dead X s L (KInv.set_brkph BPDead L) BL LS INV eq_refl eq_refl eq_refl eq_refl eq_refl) as [INV' AF'].
        eapply am_after_brk_ft; [exact INV'| exact (amf_trans _ _ _ AF AF')| destruct LF; constructor; assumption| cbn; exact HI| cbn; unfold ctx in HAC; exact HAC
                                | apply (SNAPPRE_eq s); [exact SN| reflexivity]| apply (AREAS_eq_r _ _ _ _ _ AR); reflexivity].
    + intros z Hz. unfold answer_ok in Hz. rewrite NZ, BP, BR in Hz. rewrite <- Eold in Hz.
      apply Bool.andb_false_iff in Hz. destruct Hz as [Hb|Hp].
      * rewrite Hb. exact I.
      * destruct (brk_answer_ok old new z); [| exact I]. cbn [negb].
        apply Bool.orb_false_iff in Hp as [Hn Hp]. apply Bool.negb_false_iff in Hn. rewrite Hn. cbn [negb].
        rewrite (brk_pages_ok_eq X s L IR) in Hp. rewrite Hp. exact I.
Qed.
End AM.
(* [comment removed for export] *)
