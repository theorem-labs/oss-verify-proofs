(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Read MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4
  MI_WFree2 MI_Ledger MI_WAMeta.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_MI_WAMeta2 () : Init.string Init.list := ["OSSVerify.KrLib.Heap.MI_Inv.INVL"; "Corelib.Init.Logic.and"; "am_init"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Heap.Malloc.c_init_done"; "OSSVerify.KrLib.Heap.Malloc.s_ctx"; "OSSVerify.KrLib.Heap.MI_WAMeta.AM_frame"; "OSSVerify.KrLib.Heap.Malloc.mstate"; "OSSVerify.KrLib.Heap.KInv.mled"; "OSSVerify.KrLib.Heap.Malloc.lhead"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "OSSVerify.KrLib.Heap.MI_WAMeta.L_frame"; "OSSVerify.KrLib.Heap.MI_Tree.ftree"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Heap.MI_Pres3.xidle"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Heap.MI_Inv.x_idle"; "Corelib.Init.Logic.not"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.Some"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.Heap.Malloc.c_avail_meta_count"; "OSSVerify.KrLib.Heap.Malloc.am_take"; "OSSVerify.KrLib.Heap.Malloc.optr"; "OSSVerify.KrLib.Heap.Malloc.c_avail_meta_areas"; "OSSVerify.KrLib.Heap.Malloc.aadd"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.Heap.Malloc.area"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.decidable.prod_eq_dec"; "Corelib.Numbers.BinNums.N"; "stdpp.numbers.N.eq_dec"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.N_countable"; "stdpp.countable.Z_countable"; "stdpp.gmap.gmap_lookup"; "OSSVerify.KrLib.Heap.Malloc.s_areas"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Heap.Malloc.NSLOTS"; "OSSVerify.KrLib.Heap.Malloc.meta"; "OSSVerify.KrLib.Heap.MI_Inv.mslot"; "OSSVerify.KrLib.Heap.Malloc.s_metas"; "OSSVerify.KrLib.Heap.Malloc.PGSZ"; "Corelib.Init.Datatypes.snd"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.Heap.MI_WAMeta.carve_rest"; "OSSVerify.KrLib.Heap.Malloc.c_avail_meta_area_count"; "OSSVerify.KrLib.Heap.Malloc.am_finish"; "Corelib.Init.Datatypes.true"; "OSSVerify.KrLib.Heap.Malloc.am_after_brk"; "Corelib.Init.Datatypes.prod"; "OSSVerify.KrLib.Heap.KInv.ld_resv"; "OSSVerify.KrLib.Heap.KInv.ld_groups"; "OSSVerify.KrLib.Heap.KInv.ld_metas"; "OSSVerify.KrLib.Heap.KInv.ld_brkreg"; "OSSVerify.KrLib.Heap.KInv.ld_ceil"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.Heap.KInv.lbrk_pages_ok"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition am_init (st : mstate) : mstate :=
  if c_init_done (ctx st) =? 0 then upd_ctx (fun c => set_init_done 1 (set_secret (s_secret st) c)) st else st.

Lemma INVL_am_init X st L BL LS : ltac2:(CDefT.buildp (gd_tbl_MI_WAMeta2 ()) "P,(0.O5.O4.O3.O2.O1.)(1.(0.O5.(2.O4.)O3.O2.O1.)(1.(3.$4.(5.(6.(2.O4.)))+1.)(7.O4.(2.O4.))))")
(* [comment removed for export] *).
Proof.
  intros INV. dpose INV as (IR & IA & IM & IL & IG & IS & ISH). unfold am_init, ctx.
  destruct (ia_secret _ IA) as [S0 [(I0 & C0 & A0)|(I1 & C1)]].
  - rewrite I0. cbn. set (st' := upd_ctx _ st).
    split; [| split; [reflexivity| constructor; cbn; auto; first [reflexivity| lia]]].
    split; [| split; [| split; [| split; [| split; [| split]]]]].
    + destruct IR; constructor; try assumption;
      try (etransitivity; [exact ir_ceil|]; first [reflexivity | cbn; reflexivity]).
    + destruct IA; constructor; try assumption.
      * cbn. split; [exact S0|]. right. auto.
      * intros a ar Ha. change (s_areas st') with (s_areas st) in Ha. rewrite A0 in Ha. rewrite lookup_empty in Ha. discriminate.
    + apply (inv_M_ext X st st'); [reflexivity| reflexivity| exact IM].
    + apply (inv_L_ext st st'); [reflexivity| reflexivity| intros h; destruct h; reflexivity| exact IL].
    + destruct IG as [G1 G2 G3 G4 G5]; constructor; try assumption.
      intros m b ai Hb. apply (group_ok_ext X st st'); [reflexivity| reflexivity| auto| exact (G1 m b ai Hb)].
    + apply (inv_S_ext X st st' BL); [reflexivity| reflexivity| reflexivity| exact IS].
    + apply (inv_SH_view st st'); try reflexivity. exact ISH.
  - rewrite I1. cbn. split; [exact INV|]. split; [exact I1| apply amf_refl].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AM.
Variables (T : Type) (BL : list blk) (Post : mled -> T -> Prop) (k : mstate -> optr -> M T) (bail : M T).
Variables (X : extras) (st0 : mstate) (L0 : mled).
Hypothesis KN : ltac2:(CDefT.buildp (gd_tbl_MI_WAMeta2 ()) "Pst1,$8.PL1,$9.PLS1,P,$:.(;.$<.)P,(0.VX,R3.R2.VBL,R1.)P,(7.Vst0,R4.)P,(=.VL0,R4.)(>.VT,R5.A2.Vk,R6.(?.$<.)VPost,)")
(* [comment removed for export] *).
Hypothesis KS : ltac2:(CDefT.buildp (gd_tbl_MI_WAMeta2 ()) "Pst1,$8.PL1,$9.PLS1,P,$:.(;.$<.)Pm,$<.P,(0.(10.VX,(11.$<.R1.(12.VX,)))R4.R3.VBL,R2.)P,(13.(14.$<.R2.(12.VX,)))P,(7.Vst0,R6.)P,(=.VL0,R6.)(>.VT,R7.A2.Vk,R8.(15.$<.R5.)VPost,)")
(* [comment removed for export] *).

#[using="KS"] Lemma am_take_ft st L LS : ltac2:(CDefT.buildp (gd_tbl_MI_WAMeta2 ()) "P,(0.VX,O3.O2.VBL,O1.)P,(7.Vst0,O3.)P,(=.VL0,O2.)P,(16.=(17.(6.O3.)))(>.VT,O2.(18.VT,O3.Vk,Vbail,)VPost,)")
(* [comment removed for export] *).
Proof.
  intros INV AF LF HC. ddestruct (am_take_ok X st L BL LS INV HC k bail) as (m & st2 & -> & INV2 & AF2 & NI).
  eapply KS; [exact INV2| exact NI| exact (amf_trans _ _ _ AF AF2)| exact LF].
Qed.

#[using="KS"] Lemma am_carve_ft s p L LS : ltac2:(CDefT.buildp (gd_tbl_MI_WAMeta2 ()) "P,(0.VX,O4.O2.VBL,O1.)P,(3.$19.(1:.(6.O4.))(15.$<.(1;.O3.+1000.)))P,(3.(1<.$1=.)(1>.$<.$1=.(1?.$<.(20.$21.$22.$4.$23.)(24.$21.$22.$25.$4.$23.$26.)$1=.)(27.$<.(20.$21.$22.$4.$23.)(24.$21.$22.$25.$4.$23.$26.)$1=.)O3.(28.O4.))(?.$1=.))P,Pk,$4.P,(1.(29.=R1.)(16.R1.$2:.))(3.(1<.$2;.)(1>.$<.$2;.(1?.$<.(20.$21.$22.$4.$23.)(24.$21.$22.$25.$4.$23.$26.)$2;.)(27.$<.(20.$21.$22.$4.$23.)(24.$21.$22.$25.$4.$23.$26.)$2;.)(2<.O3.R2.)(2=.O4.))(?.$2;.))P,(29.$2>.(2?.$21.$4.O3.))P,(3.$4.(30.(2?.$21.$4.O3.)$2>.)=)P,(3.$4.(5.(6.O4.))+1.)P,(7.Vst0,O4.)P,(=.VL0,O2.)(>.VT,O2.(18.VT,(31.O4.O3.)Vk,Vbail,)VPost,)")
(* [comment removed for export] *).
Proof.
  intros INV H1 H2 H3 H4 H5 H6 AF LF. ddestruct (INVL_carve X s L BL LS p INV H1 H2 H3 H4 H5 H6) as (INV' & AF' & HC).
  eapply am_take_ft; [exact INV'| exact (amf_trans _ _ _ AF AF')| exact LF| exact HC].
Qed.

#[using="KN KS"] Lemma am_finish_ft st L LS : ltac2:(CDefT.buildp (gd_tbl_MI_WAMeta2 ()) "P,(0.VX,O3.O2.VBL,O1.)P,(7.Vst0,O3.)P,(=.VL0,O2.)P,(16.=(32.(6.O3.)))P,(3.$4.(5.(6.O3.))+1.)(>.VT,O2.(33.VT,O3.$34.Vk,Vbail,)VPost,)")
(* [comment removed for export] *).
Proof.
  intros INV AF LF HC HI.
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
      ddestruct (INVL_meta_adv X st L BL LS rid off INV EC HC) as (INV' & F1 & F2 & F3 & F4 & F5 & F6 & AF').
      eapply am_carve_ft; [exact INV'| exact F1| exact F2| exact F3| exact F4| exact F5| rewrite F6; exact HI| exact (amf_trans _ _ _ AF AF')|].
      destruct LF; constructor; assumption.
    + eapply KN; [exact INV| exact AF| exact LF].
  - intros a Ha. cbn in Ha. rewrite Ha. exact I.
Qed.

#[using="KN KS"] Lemma am_after_brk_ft st L LS : ltac2:(CDefT.buildp (gd_tbl_MI_WAMeta2 ()) "P,(0.VX,O3.O2.VBL,O1.)P,(7.Vst0,O3.)P,(=.VL0,O2.)P,(3.$4.(5.(6.O3.))+1.)(>.VT,O2.(35.VT,O3.$34.Vk,Vbail,)VPost,)")
(* [comment removed for export] *).
Proof.
  intros INV AF LF HI. unfold am_after_brk.
  destruct (Z.eqb_spec (c_avail_meta_area_count (ctx st)) 0) as [HC|HC].
  - apply ftree_vis; [reflexivity| reflexivity| exact (nm_event_pre X st L BL LS INV)| |].
    + intros a Ha. unfold answer_ok in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [andb] in Ha.
      rewrite (mmap_answer_ok_eq X st L (proj1 INV)) in Ha. unfold ctx. rewrite Ha. cbn [negb].
      unfold event_post. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_NONE =? PROT_NONE) with true. cbn [andb].
      destruct (is_err a) eqn:NE.
      * eapply KN; [exact INV| exact AF| exact LF].
      * ddestruct (INVL_new_meta X st L BL LS a INV HC Ha NE) as (INV' & HC' & HI' & AF').
        eapply am_finish_ft; [exact INV'| exact (amf_trans _ _ _ AF AF')| destruct LF; constructor; assumption| exact HC'| rewrite HI'; exact HI].
    + intros a Ha. unfold answer_ok in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [andb] in Ha.
      rewrite (mmap_answer_ok_eq X st L (proj1 INV)) in Ha. unfold ctx. rewrite Ha. exact I.
  - eapply am_finish_ft; [exact INV| exact AF| exact LF| pose proof (proj1 (ir_cursor _ _ _ (proj1 INV))); unfold ctx in HC; lia| exact HI].
Qed.

#[using="Type"] Lemma lbrk_pages_ok_ext L1 L2 lo len : ltac2:(CDefT.buildp (gd_tbl_MI_WAMeta2 ()) "P,(3.(;.(36.$4.$4.))(37.O4.)(37.O3.))P,(3.(;.(36.$4.$4.))(38.O4.)(38.O3.))P,(3.(;.(36.(36.$4.$4.)$4.))(39.O4.)(39.O3.))P,(3.(1<.(36.$4.$4.))(3:.O4.)(3:.O3.))P,(3.$4.(3;.O4.)(3;.O3.))(3.$3<.(3=.O4.O2.O1.)(3=.O3.O2.O1.))")
(* [comment removed for export] *).
Proof. intros E1 E2 E3 E4 E5. unfold lbrk_pages_ok, lranges. rewrite E1, E2, E3, E4, E5. reflexivity. Qed.

#[using="KN KS"] Theorem alloc_meta_ft st L LS : INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L -> ftree L (alloc_meta st k bail) Post.
Proof.
  intros INV0 AF0 LF.
  ddestruct (INVL_am_init X st L BL LS INV0) as (INV & HI & AFi).
  pose proof (amf_trans _ _ _ AF0 AFi) as AF. clear AF0 AFi INV0.
  unfold alloc_meta. fold (am_init st). set (s := am_init st) in *. clearbody s.
  dpose INV as (IR & IA & IM & IL & IG & IS & ISH).
  (* [comment removed for export] *)
  destruct (c_free_meta_head (ctx s)) as [m|] eqn:EFH.
  { pose proof (il_head _ _ IL LFree) as HH. cbn in HH. unfold ctx in EFH. rewrite EFH in HH.
    destruct (LS LFree) as [|m' rest] eqn:ELS; [discriminate|]. cbn in HH. inversion HH. subst m'.
    pose proof (INVL_dequeue X (xidle X (m :: x_idle X)) s L BL LS m LFree [] rest INV ltac:(rewrite ELS; reflexivity) ltac:(right; split; reflexivity)) as INV1.
    ddestruct (dequeue_frame LFree m s) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & FC).
    eapply KS; [exact INV1| | | exact LF].
    { intros Hin. apply (proj2 (im_idle _ _ _ IM m Hin)). exists LFree. rewrite ELS. left. reflexivity. }
    eapply amf_trans; [exact AF|]. destruct FC. constructor; auto; try congruence.
    all: try (intros sc; change (active (dequeue LFree m s) sc) with (get_head (dequeue LFree m s) (LActive sc)); rewrite dequeue_head;
              destruct (decide (LActive sc = LFree)); [discriminate| reflexivity]).
    all: try (intros sc; unfold usage, ctx; rewrite cb_usage; reflexivity).
    all: try (intros rid r H _; rewrite F1; exact H).
    all: rewrite ?F3; lia. }
  (* [comment removed for export] *)
  destruct (Z.eqb_spec (c_avail_meta_count (ctx s)) 0) as [HAC|HAC]; cbn [negb].
  2:{ eapply am_take_ft; [exact INV| exact AF| exact LF| pose proof (proj1 (ia_avail _ IA)); unfold ctx in HAC; lia]. }
  (* [comment removed for export] *)
  destruct (Z.eqb_spec (c_avail_meta_area_count (ctx s)) 0) as [HC|HC]; cbn [andb].
  2:{ eapply am_after_brk_ft; [exact INV| exact AF| exact LF| exact HI]. }
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
           ddestruct (INVL_brk_first X s L BL LS cur INV EBRK HC ltac:(exact Hp) (KInv.set_brkph (BPGuard cur) (KInv.set_brkph (BPQueried cur) L)) ltac:(repeat split; reflexivity))
             as (INV' & G1 & G2 & G3 & G4 & G5 & G6 & AF').
           eapply am_carve_ft; [exact INV'| exact G1| exact G2| exact G3| exact G4| exact G5| rewrite G6; exact HI| exact (amf_trans _ _ _ AF AF')|].
           destruct LF; constructor; assumption.
        -- intros rg Hg. unfold answer_ok in Hg. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false in Hg. cbn [andb] in Hg.
           fold base in Hg. rewrite Hg. exact I.
      * destruct (INVL_brk_dead X s L (KInv.set_brkph BPDead (KInv.set_brkph (BPQueried cur) L)) BL LS INV eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as [INV' AF'].
        eapply am_after_brk_ft; [exact INV'| exact (amf_trans _ _ _ AF AF')| destruct LF; constructor; assumption| cbn; exact HI].
    + intros r Hr. unfold answer_ok in Hr. rewrite NZ in Hr. unfold L1 in Hr. cbn [KInv.ld_brk KInv.set_brkph] in Hr.
      apply Bool.andb_false_iff in Hr. destruct Hr as [Hb|Hp].
      * rewrite Hb. exact I.
      * destruct (brk_answer_ok cur new r); [| exact I]. cbn [negb].
        apply Bool.orb_false_iff in Hp as [Hn Hp]. apply Bool.negb_false_iff in Hn. rewrite Hn. cbn [negb].
        rewrite (lbrk_pages_ok_ext (KInv.set_brkph (BPQueried cur) L) L) in Hp by reflexivity.
        rewrite (brk_pages_ok_eq X s L IR) in Hp. fold base in Hp. rewrite Hp. exact I.
  - (* [comment removed for export] *) eapply am_after_brk_ft; [exact INV| exact AF| exact LF| exact HI].
  - (* [comment removed for export] *)
    destruct IBK as [BP (r & Hr & K & Elen)].
    pose proof (bg_event_pre X s L BL LS rid off INV EBRK) as PRE.
    set (old := conc s (rid, off)) in *. set (new := old + PGSZ) in *.
    assert (NZ : (new =? 0) = false).
    { apply Z.eqb_neq. unfold new, old, conc, get_region. rewrite Hr. cbn [fst snd]. pose proof (ir_shape _ _ _ IR _ _ Hr) as (S1 & _ & S3 & _). unfold PGSZ. lia. }
    assert (BR : ld_brkreg L = Some (r_base r, off)).
    { apply (proj2 (ir_brkreg _ _ _ IR (r_base r) off)). dexists rid, r. auto. }
    assert (Eold : old = r_base r + off) by (unfold old, conc, get_region; rewrite Hr; cbn [fst snd]; reflexivity).
    apply ftree_vis; [reflexivity| reflexivity| exact PRE| |].
    + intros z Hz. unfold answer_ok in Hz. rewrite NZ, BP, BR in Hz. rewrite <- Eold in Hz.
      apply Bool.andb_true_iff in Hz as [Hb Hp]. rewrite Hb. cbn [negb].
      unfold event_post. rewrite NZ, BP, BR.
      destruct (Z.eqb_spec z new) as [->|NE]; cbn [negb].
      * cbn [negb orb] in Hp. rewrite (brk_pages_ok_eq X s L IR) in Hp. rewrite Hp. cbn [negb].
        unfold am_after_brk, ctx. cbn [c_avail_meta_area_count s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk Z.eqb].
        unfold am_finish, ctx. cbn [c_avail_meta_areas s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk snd].
        ddestruct (bg_region X s L BL LS rid off INV EBRK) as (r' & _ & _ & _ & _ & _ & _ & _ & OM & _).
        rewrite (proj2 (Z.eqb_eq _ _) OM). cbn [negb].
        rewrite am_carve_eq.
        ddestruct (INVL_brk_grow X s L BL LS rid off INV EBRK HC ltac:(exact Hp)) as (INV' & G1 & G2 & G3 & G4 & G5 & G6 & AF').
        replace (conc s (rid, off) - off) with (r_base r) in INV' by (unfold conc, get_region; rewrite Hr; cbn [fst snd]; lia).
        eapply am_carve_ft; [exact INV'| exact G1| exact G2| exact G3| exact G4| exact G5| rewrite G6; exact HI| exact (amf_trans _ _ _ AF AF')|].
        destruct LF; constructor; assumption.
      * destruct (INVL_brk_dead X s L (KInv.set_brkph BPDead L) BL LS INV eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as [INV' AF'].
        eapply am_after_brk_ft; [exact INV'| exact (amf_trans _ _ _ AF AF')| destruct LF; constructor; assumption| cbn; exact HI].
    + intros z Hz. unfold answer_ok in Hz. rewrite NZ, BP, BR in Hz. rewrite <- Eold in Hz.
      apply Bool.andb_false_iff in Hz. destruct Hz as [Hb|Hp].
      * rewrite Hb. exact I.
      * destruct (brk_answer_ok old new z); [| exact I]. cbn [negb].
        apply Bool.orb_false_iff in Hp as [Hn Hp]. apply Bool.negb_false_iff in Hn. rewrite Hn. cbn [negb].
        rewrite (brk_pages_ok_eq X s L IR) in Hp. rewrite Hp. exact I.
Qed.
End AM.
