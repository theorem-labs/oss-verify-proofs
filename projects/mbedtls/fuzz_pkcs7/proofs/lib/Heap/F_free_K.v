(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  Arr ITree Nodes Decode.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_syscalls MallocRep F_malloc_free MallocTree MallocBlocks MallocFacts_B.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocKit_B MallocKit_B2 MallocModel_B MallocKit_B3 MallocFacts_Bpres.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_F_free_K () : Init.string Init.list := ["Corelib.Init.Logic.or"; "Corelib.Init.Logic.ex"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.N"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Heap.Malloc.ghdr"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "stdpp.decidable.prod_eq_dec"; "stdpp.numbers.N.eq_dec"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.N_countable"; "stdpp.countable.Z_countable"; "stdpp.gmap.gmap_lookup"; "OSSVerify.KrLib.Heap.Malloc.s_groups"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.fst"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.snd"; "OSSVerify.KrLib.Heap.Malloc.IB"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.Heap.MallocFacts_B.hosts"; "OSSVerify.KrLib.Heap.Malloc.m_last_idx"; "OSSVerify.KrLib.Heap.Malloc.get_meta_rec"; "OSSVerify.KrLib.Heap.MallocFacts_B.sstart_of"; "OSSVerify.KrLib.Heap.MallocBlocks.block"; "Stdlib.Lists.List.In"; "OSSVerify.KrLib.Heap.MallocBlocks.blk_slot"; "OSSVerify.KrLib.Heap.MallocBlocks.blk_addr"; "OSSVerify.KrLib.Heap.Malloc.conc"; "PROT"; "OSSVerify.KrLib.Heap.Malloc.cellval"; "OSSVerify.KrLib.Heap.Malloc.cell_read"; "OSSVerify.KrLib.Heap.Malloc.get_shadow"; "OSSVerify.KrLib.Heap.MallocFacts_B.hdr_known"; "OSSVerify.KrLib.Heap.Malloc.region"; "OSSVerify.KrLib.Heap.Malloc.s_regions"; "hdr_st"; "OSSVerify.KrLib.Heap.Malloc.area"; "OSSVerify.KrLib.Heap.Malloc.s_areas"; "OSSVerify.KrLib.Heap.Malloc.s_slots"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Heap.Malloc.s_reserved"; "OSSVerify.KrLib.Heap.Malloc.mctx"; "OSSVerify.KrLib.Heap.Malloc.s_ctx"; "OSSVerify.KrLib.Heap.Malloc.s_tick"; "OSSVerify.KrLib.Heap.Malloc.meta"; "OSSVerify.KrLib.Heap.Malloc.s_metas"; "OSSVerify.KrLib.Heap.Malloc.s_next_rid"; "OSSVerify.KrLib.Heap.MallocRep.ticks_ok"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.Heap.Malloc.Known"; "OSSVerify.KrLib.Heap.MallocFacts_B.CINV"; "OSSVerify.KrLib.Heap.MallocFacts_Bpres.KINV"; "OSSVerify.KrLib.Heap.Malloc.cptr"; "OSSVerify.KrLib.Heap.Malloc.r_base"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.Heap.MallocFacts_B.ci_slots"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.Heap.MallocFacts_B.slot_free"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Heap.Malloc.m_sizeclass"; "OSSVerify.KrLib.Heap.MallocFacts_Bpres.LPRE"; "stdpp.base.filter"; "stdpp.list_basics.list.list_filter"; "Stdlib.Bool.Bool.Is_true"; "Corelib.Init.Datatypes.negb"; "OSSVerify.KrLib.Heap.Malloc.aptr_eqb"; "stdpp.decidable.Is_true_dec"; "OSSVerify.KrLib.Heap.MallocFacts_B.ci_mptrs"; "OSSVerify.KrLib.Heap.Malloc.optr"; "OSSVerify.KrLib.Heap.MallocFacts_Bpres.amc"; "OSSVerify.KrLib.Heap.Malloc.ctx"].


(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cell_read_wr8 st p v rid o :
  ticks_ok st -> 0 <= v < 256 ->
  cell_read (get_shadow (wr8 p v st) rid) o =
  if (N.eqb rid (fst p) && Z.eqb o (snd p))%bool then Known v else cell_read (get_shadow st rid) o.
Proof.
  intros TK Hv. destruct (N.eqb_spec rid (fst p)) as [->|NE]; cbn [andb].
  - destruct (Z.eqb_spec o (snd p)) as [->|NEo]; [apply cell_read_wr8_same; assumption| apply cell_read_wr8_other; exact NEo].
  - rewrite get_shadow_wr8_other by exact NE. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition PROT (st : mstate) (LB : list block) (rid : N) (o : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_F_free_K ()) "(0.(1.(2.$3.$4.)Lb,(2.$3.$4.)(1.$5.Lgh,$5.(6.(7.(8.$5.)(9.(2.$3.$4.)$5.(:.$;.(<.$3.$=.$4.$>.)(?.$3.$=.$10.$4.$>.$11.)$5.)(12.$;.(<.$3.$=.$4.$>.)(?.$3.$=.$10.$4.$>.$11.)$5.)R2.(13.O4.))(14.$5.R1.))(6.(7.$3.(15.$3.$4.R2.)O2.)(6.(16.(17.(18.$3.$4.R2.)$19.)O1.)(1:.O1.(1;.(18.$3.$4.R2.)+<.)))))))(0.(1.$;.Lb,$;.(1.$;.Lg,$;.(1.$4.Li,$4.(6.(1<.O4.R3.R2.)(6.(7.$3.(15.$3.$4.R3.)O2.)(6.(6.(16.=R1.)(16.R1.(1=.(1>.O4.R2.))))(7.$4.O1.(17.(1?.(1>.O4.R2.)R1.)$19.))))))))(1.$20.Lblk,$20.(6.(21.$20.R1.O3.)(6.(7.$3.(15.$3.$4.(22.R1.))O2.)(6.(16.(17.(1;.(18.$3.$4.(22.R1.))(17.(23.R1.)(24.O4.(22.R1.))))$19.)O1.)(1:.O1.(1;.(18.$3.$4.(22.R1.))(17.(23.R1.)(24.O4.(22.R1.)))))))))))")
(* [comment removed for export] *).

Section KSH.
Variables (st st' : mstate) (LB : list block).
Hypothesis ER : s_regions st' = s_regions st.
Hypothesis EA : s_areas st' = s_areas st.
Hypothesis EG : s_groups st' = s_groups st.
Hypothesis ESL : s_slots st' = s_slots st.
Hypothesis EC : s_ctx st' = s_ctx st.
Hypothesis EM : forall q, get_meta_rec st' q = get_meta_rec st q.
Hypothesis TK' : ticks_ok st'.
Hypothesis SHP : ltac2:(CDefT.buildp (gd_tbl_F_free_K ()) "Prid,$3.Po,$4.P,(25.Vst,VLB,R2.R1.)(7.$26.(27.(28.Vst',R3.)R2.)(27.(28.Vst,R3.)R2.))")
(* [comment removed for export] *).

#[using="EG"] Lemma hosts_sh b q : hosts st' b q <-> hosts st b q.
Proof. unfold hosts. rewrite EG. tauto. Qed.
#[using="EG"] Lemma is_gm_sh q : is_gm st' q <-> is_gm st q.
Proof. unfold is_gm. split; intros [b H]; exists b; apply hosts_sh; exact H. Qed.
#[using="ER"] Lemma conc_sh q : conc st' q = conc st q.
Proof. unfold conc, get_region. rewrite ER. reflexivity. Qed.

#[using="SHP"] Lemma hdr_known_sh p b1 i1 rid : ltac2:(CDefT.buildp (gd_tbl_F_free_K ()) "P,(7.$3.(15.$3.$4.O4.)O1.)P,Pk,$4.P,(6.(16.+1.R1.)(16.R1.+3.))(25.Vst,VLB,O1.(17.(18.$3.$4.O4.)R2.))P,(29.Vst,O4.O3.O2.)(29.Vst',O4.O3.O2.)")
(* [comment removed for export] *).
Proof.
  (intros <- HP dd_H; ddestruct dd_H as (v3 & lo & hi & H3 & I3 & H2 & H1 & E)). dexists v3, lo, hi.
  rewrite !SHP by (apply HP; lia). auto 10.
Qed.

#[using="ER EA EG ESL EC EM TK' SHP"] Lemma KINV_shadow c : KINV st LB c -> KINV st' LB c.
Proof.
  intros K. pose proof (ki_gmetas _ _ _ K) as CG. pose proof (ki_slts _ _ _ K) as CS.
  assert (GMO : forall b g, hosts st b g -> gmeta_ok st' g b).
  { intros b g HB. pose proof (CG b g HB) as GO. constructor; rewrite ?EM, ?ER, ?ESL; try (destruct GO; assumption).
    - unfold meta_slot. rewrite EA. exact (go_slot _ _ _ GO).
    - intros ML. destruct (go_nest _ _ _ GO ML) as (g1 & i1 & b1 & SL & HB1 & FB & EQB & I1 & NF1 & LT & HK).
      dexists g1, i1, b1. rewrite ?EM. split; [exact SL|]. split; [apply hosts_sh; exact HB1|]. split; [exact FB|]. split; [exact EQB|].
      split; [exact I1|]. split; [exact NF1|]. split; [exact LT|].
      eapply hdr_known_sh; [reflexivity| | exact HK].
      intros k Hk. left. destruct HB as [ai Hai]. dexists b, (mkGhdr (Some g) ai). split; [exact Hai|]. split; [reflexivity|]. unfold IB. lia. }
  constructor.
  - apply (links_ext st st' EA); [intros q; rewrite EM; auto| exact (ki_links _ _ _ K)].
  - apply (heads_lx st st' EG); [intros q; rewrite EM; auto| intros sc; unfold active, ctx; rewrite EC; reflexivity| unfold ctx; rewrite EC; reflexivity| intros q _; rewrite EM; auto| exact (ki_heads _ _ _ K)].
  - apply (homog_lx st st' EG); [intros q; rewrite EM; auto| intros q _; rewrite EM; auto| exact (ki_links _ _ _ K)| exact (ki_hom _ _ _ K)].
  - intros b g HB. apply GMO. apply hosts_sh. exact HB.
  - intros b gh Hb. rewrite EG in Hb. destruct (ki_grps _ _ _ K b gh Hb) as (g & Hg & Hai). exists g. rewrite EM. auto.
  - intros b1 b2 g H1 H2. apply (ki_ginj _ _ _ K b1 b2 g); apply hosts_sh; assumption.
  - intros s g i Hs. rewrite ESL in Hs. rewrite EM. ddestruct (CS s g i Hs) as (GM & E & I). split; [apply is_gm_sh; exact GM| auto].
  - intros b g i HB Hi. rewrite ESL, EM. apply hosts_sh in HB. rewrite EM in Hi. exact (ki_sltt _ _ _ K b g i HB Hi).
  - intros b gh o Hb Ho. rewrite EG in Hb. rewrite SHP; [exact (ki_unk _ _ _ K b gh o Hb Ho)|].
    left. dexists b, gh. split; [exact Hb|]. split; [reflexivity|]. unfold IB. lia.
  - intros g b i HB Hi. apply hosts_sh in HB. rewrite EM in Hi |- *. rewrite SHP; [exact (ki_h0 _ _ _ K g b i HB Hi)|].
    right; left. dexists b, g, i. auto.
  - apply Forall_forall. intros blk Hin. pose proof (proj1 (Forall_forall _ _) (ki_blks _ _ _ K) blk Hin) as BK.
    ddestruct BK as [(g & i & b & SL & HB & FB & I & NFR & (off & O0 & OA & OS & OK & HK)) NG SZ].
    assert (Hin' : In blk LB) by (first [exact Hin | apply (proj1 (list_elem_of_In _ _)); exact Hin]).
    constructor; [| rewrite EG; exact NG| exact SZ].
    dexists g, i, b. rewrite ESL, EM, conc_sh. split; [exact SL|]. split; [apply hosts_sh; exact HB|]. split; [exact FB|]. split; [exact I|]. split; [exact NFR|].
    exists off. split; [exact O0|]. split; [exact OA|]. split; [exact OS|]. split.
    + rewrite SHP; [exact OK|]. right; right. exists blk. split; [exact Hin'|]. split; [reflexivity|]. rewrite OA. unfold UNIT, IB in *. lia.
    + eapply hdr_known_sh; [reflexivity| | exact HK]. intros k Hk. right; right. exists blk. split; [exact Hin'|]. split; [reflexivity|].
      cbn [aadd snd]. rewrite OA. unfold UNIT, IB in *. lia.
  - exact (ki_nodup _ _ _ K).
  - pose proof (ki_cx _ _ _ K) as X. unfold kctx, bounces, unmap_seq, ctx in *. rewrite EC. exact X.
  - intros sc Hsc. unfold usage, ctx. rewrite EC. exact (ki_usage _ _ _ K sc Hsc).
  - intros rid off Hb. unfold ctx in Hb. rewrite EC in Hb. rewrite ER. exact (ki_bk _ _ _ K rid off Hb).
  - exact TK'.
Qed.
End KSH.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition hdr_st (st : mstate) (pf : aptr) : mstate := wr16 (aadd pf (-2)) 0 (wr8 (aadd pf (-3)) 255 st).

Lemma hdr_st_tables st pf : ltac2:(CDefT.buildp (gd_tbl_F_free_K ()) "(6.(7.(:.$3.$=.$10.$2:.)(2;.(2<.O2.O1.))(2;.O2.))(6.(7.(:.$;.(<.$3.$=.$4.$>.)(?.$3.$=.$10.$4.$>.$11.)$2=.)(2>.(2<.O2.O1.))(2>.O2.))(6.(7.(:.$;.(<.$3.$=.$4.$>.)(?.$3.$=.$10.$4.$>.$11.)$5.)(13.(2<.O2.O1.))(13.O2.))(6.(7.(:.$;.(<.$3.$=.$4.$>.)(?.$3.$=.$10.$4.$>.$11.)(2.$;.$4.))(2?.(2<.O2.O1.))(2?.O2.))(6.(7.(30.(2.$4.$4.))(31.(2<.O2.O1.))(31.O2.))(6.(7.$32.(33.(2<.O2.O1.))(33.O2.))(6.(7.$3.(34.(2<.O2.O1.))(34.O2.))(6.Pq,$;.(7.$35.(1>.(2<.O2.O1.)R1.)(1>.O2.R1.))(6.(7.(:.$;.(<.$3.$=.$4.$>.)(?.$3.$=.$10.$4.$>.$11.)$35.)(36.(2<.O2.O1.))(36.O2.))(7.$3.(37.(2<.O2.O1.))(37.O2.)))))))))))")
(* [comment removed for export] *).
Proof. repeat split; reflexivity. Qed.

Lemma ticks_ok_hdr_st st pf : ticks_ok st -> ticks_ok (hdr_st st pf).
Proof. intros TK. unfold hdr_st, wr16. repeat apply ticks_ok_wr8. exact TK. Qed.

Lemma hdr_st_cell_read st pf rid o : ticks_ok st ->
  cell_read (get_shadow (hdr_st st pf) rid) o =
    if (N.eqb rid (fst pf) && ((o =? snd pf - 1) || (o =? snd pf - 2) || (o =? snd pf - 3)))%bool
    then Known (if o =? snd pf - 3 then 255 else 0)
    else cell_read (get_shadow st rid) o.
Proof.
  intros TK. unfold hdr_st, wr16. change (Z.shiftr 0 8) with 0.
  rewrite (cell_read_wr8 _ _ 0 rid o) by (first [repeat apply ticks_ok_wr8; exact TK | lia]).
  rewrite (cell_read_wr8 _ _ 0 rid o) by (first [repeat apply ticks_ok_wr8; exact TK | lia]).
  rewrite (cell_read_wr8 _ _ 255 rid o) by (first [exact TK | lia]).
  cbn [aadd fst snd].
  destruct (N.eqb_spec rid (fst pf)); cbn [andb]; [| reflexivity].
  destruct (Z.eqb_spec o (snd pf + -2 + 1)); destruct (Z.eqb_spec o (snd pf - 1)); try lia;
  destruct (Z.eqb_spec o (snd pf + -2)); destruct (Z.eqb_spec o (snd pf - 2)); try lia;
  destruct (Z.eqb_spec o (snd pf + -3)); destruct (Z.eqb_spec o (snd pf - 3)); try lia; cbn [orb]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hdr_st_cell_read_other st pf rid o : ltac2:(CDefT.buildp (gd_tbl_F_free_K ()) "P,(38.O4.)P,(0.(39.(7.$3.O2.(15.$3.$4.O3.)))(0.(1:.O1.(17.(18.$3.$4.O3.)+3.))(16.(18.$3.$4.O3.)O1.)))(7.$26.(27.(28.(2<.O4.O3.)O2.)O1.)(27.(28.O4.O2.)O1.))")
(* [comment removed for export] *).
Proof.
  intros TK H. rewrite hdr_st_cell_read by exact TK.
  destruct (N.eqb_spec rid (fst pf)); cbn [andb]; [| reflexivity].
  destruct (Z.eqb_spec o (snd pf - 1)); [lia|]. destruct (Z.eqb_spec o (snd pf - 2)); [lia|]. destruct (Z.eqb_spec o (snd pf - 3)); [lia|].
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hdr_st_known_back st pf rid o v : ltac2:(CDefT.buildp (gd_tbl_F_free_K ()) "P,(38.O5.)P,Pk,$4.P,(6.(16.+1.R1.)(16.R1.+3.))(1.$4.Lw,$4.(7.$26.(27.(28.O5.(15.$3.$4.O4.))(17.(18.$3.$4.O4.)R3.))(3:.R1.)))P,(7.$26.(27.(28.(2<.O5.O4.)O3.)O2.)(3:.O1.))(1.$4.Lw,$4.(7.$26.(27.(28.O5.O3.)O2.)(3:.R1.)))")
(* [comment removed for export] *).
Proof.
  intros TK HK H. rewrite hdr_st_cell_read in H by exact TK.
  destruct (N.eqb_spec rid (fst pf)); cbn [andb] in H; [| exists v; exact H].
  destruct (Z.eqb_spec o (snd pf - 1)); [subst; apply (HK 1); lia|].
  destruct (Z.eqb_spec o (snd pf - 2)); [subst; apply (HK 2); lia|].
  destruct (Z.eqb_spec o (snd pf - 3)); [subst; apply (HK 3); lia|].
  cbn [orb] in H. exists v; exact H.
Qed.


Lemma ZINV_hdr_st st pf Zs : ZINV st Zs -> ZINV (hdr_st st pf) Zs.
Proof. apply ZINV_ext; reflexivity. Qed.

(* [comment removed for export] *)
Lemma KINV_hdr_st st LB LB' c (pf : aptr) (blk : block) r : ltac2:(CDefT.buildp (gd_tbl_F_free_K ()) "P,(3;.O7.O6.)P,(21.$20.O2.O6.)P,(3<.O7.O5.O4.)P,Pb',$20.P,(21.$20.R1.O5.)(6.(21.$20.R2.O6.)(39.(7.$3=.(22.R2.)(22.O2.))))P,(7.$3.(15.$3.$4.O3.)(15.$3.$4.(22.O2.)))P,(7.(8.$2:.)(9.$3.$2:.(:.$3.$=.$10.$2:.)(12.$3.$=.$10.$2:.)(15.$3.$4.O3.)(2;.O7.))(14.$2:.O1.))P,(7.$4.(1;.(3>.O1.)(18.$3.$4.O3.))(23.O2.))P,(7.$4.(3?.(18.$3.$4.O3.)+10.)=)(3<.(2<.O7.O3.)O5.O4.)")
(* [comment removed for export] *).
Proof.
  intros C Hin K HLB Hfst Hr Hpo PM.
  pose proof (ci_ticks _ _ C) as TK.
  pose proof (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk Hin) as BC.
  pose proof (bk_size _ _ (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) blk Hin)) as SZ.
  destruct BC as [(r0 & Hr0 & Kr0 & A16 & AEND & AL & UNK) HD BB].
  rewrite <- Hfst, Hr in Hr0. assert (r0 = r) by congruence. subst r0.
  ddestruct (hdr_st_tables st pf) as (ER & EA & EG & ESL & ERS & EC & ET & EM & _).
  apply (KINV_shadow st (hdr_st st pf) LB' ER EA EG ESL EC EM (ticks_ok_hdr_st st pf TK)); [| exact K].
  intros rid o HP. apply hdr_st_cell_read_other; [exact TK|].
  destruct (N.eq_dec rid (fst pf)) as [->|NE]; [right| left; exact NE].
  pose proof (ki_gmetas _ _ _ K) as CG.
  destruct HP as [HP|[HP|HP]].
  - ddestruct HP as (b & gh & Hb & Fb & Ho).
    specialize (HD b gh Hb ltac:(rewrite Fb, Hfst; reflexivity)).
    rewrite (conc_region' st b r) in HD by (rewrite Fb; exact Hr). unfold IB in *. lia.
  - ddestruct HP as (b & g & i & HB & Fb & Hi & ->).
    pose proof (CG b g HB) as GO. destruct (go_region _ _ _ GO) as (rb & Hrb & _ & B0 & B16 & _). pose proof (go_stride _ _ _ GO) as [S16 SM].
    pose proof (go_mem _ _ _ GO) as MEM. unfold sstart_of. rewrite MEM. cbn [default id].
    assert (SIM : (get_stride (get_meta_rec st g) * i) mod 16 = 0).
    { unfold UNIT in SM. rewrite Z.mul_mod, SM, Z.mul_0_l by lia. reflexivity. }
    set (si := get_stride (get_meta_rec st g) * i) in *. clearbody si.
    unfold UNIT, IB in *. Z.div_mod_to_equations. lia.
  - ddestruct HP as (blk' & Hin' & Fb' & Ho). destruct (HLB blk' Hin') as [HinL NEs].
    specialize (BB blk' HinL NEs ltac:(rewrite Fb', Hfst; reflexivity)).
    pose proof (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' HinL) as BC'.
    pose proof (bk_size _ _ (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) blk' HinL)) as SZ'.
    destruct BC' as [(r1 & Hr1 & _ & A16' & _ & _ & _) _ _]. rewrite Fb', Hr in Hr1. assert (r1 = r) by congruence. subst r1.
    rewrite (conc_region' st (blk_slot blk') r) in Ho by (rewrite Fb'; exact Hr).
    unfold IB in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma In_filter_iff {A} (P : A -> Prop) `{forall x, Decision (P x)} (l : list A) x :
  In x (filter P l) <-> In x l /\ P x.
Proof.
  rewrite <- list_elem_of_In, list_elem_of_filter.
  pose proof (list_elem_of_In l x) as E. tauto.
Qed.

Lemma NoDup_list_filter {A} (P : A -> Prop) `{forall x, Decision (P x)} (l : list A) :
  List.NoDup l -> List.NoDup (filter P l).
Proof.
  induction l as [|x l IH]; intros ND; [constructor|].
  rewrite filter_cons. inversion ND; subst. destruct (decide (P x)); [| apply IH; assumption].
  constructor; [| apply IH; assumption]. intros Hin. apply In_filter_iff in Hin. tauto.
Qed.

Lemma map_filter_slot (f : aptr -> bool) (LB : list block) :
  map blk_slot (filter (fun b => f (blk_slot b)) LB) = filter f (map blk_slot LB).
Proof.
  induction LB as [|b LB IH]; [reflexivity|]. cbn [map]. rewrite !filter_cons.
  destruct (decide (f (blk_slot b))); cbn [map]; rewrite IH; reflexivity.
Qed.

Lemma KINV_filter_slot st LB c (f : aptr -> bool) : KINV st LB c -> KINV st (filter (fun b => f (blk_slot b)) LB) c.
Proof.
  intros K. pose proof (ki_blks _ _ _ K) as BL. pose proof (ki_nodup _ _ _ K) as ND. destruct K; constructor; auto.
  - apply List.Forall_forall. intros blk Hin. apply In_filter_iff in Hin. destruct Hin as [Hin _].
    exact (proj1 (List.Forall_forall _ _) BL blk Hin).
  - rewrite map_filter_slot. apply NoDup_list_filter. exact ND.
Qed.

Lemma LPRE_intro st LB c g p i (blk : block) : ltac2:(CDefT.buildp (gd_tbl_F_free_K ()) "P,(40.O7.)P,(1<.O7.O3.O4.)P,(7.(8.(2.$;.$4.))(9.$3=.(2.$;.$4.)(:.$;.(<.$3.$=.$4.$>.)(?.$3.$=.$10.$4.$>.$11.)(2.$;.$4.))(12.$;.(<.$3.$=.$4.$>.)(?.$3.$=.$10.$4.$>.$11.)(2.$;.$4.))(22.O1.)(2?.O7.))(14.(2.$;.$4.)(41.$;.$4.O4.O2.)))P,(39.(42.(1>.O7.O4.)O2.))P,(7.(8.$5.)(9.$3=.$5.(:.$;.(<.$3.$=.$4.$>.)(?.$3.$=.$10.$4.$>.$11.)$5.)(12.$;.(<.$3.$=.$4.$>.)(?.$3.$=.$10.$4.$>.$11.)$5.)(22.O1.)(13.O7.))(43.$5.))P,(16.O5.(44.(1>.O7.O4.)))(45.O7.(46.$20.(30.$20.)(47.$20.)Lb,$20.(48.(49.(4:.(22.R1.)(22.O1.))))Lx,$20.(4;.(49.(4:.(22.R1.)(22.O1.))))O6.)O5.O4.O3.O2.)")
(* [comment removed for export] *).
Proof.
  intros CS HB SL NF NG HC. destruct (CS _ _ _ SL) as (GM & E & I).
  constructor; auto.
  - rewrite <- E. exact NG.
  - apply List.Forall_forall. intros b' Hin. apply In_filter_iff in Hin. destruct Hin as [_ Hb'].
    rewrite <- E. intros EQ. rewrite EQ, aptr_eqb_refl in Hb'. exact Hb'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section DROP.
Variables (st : mstate) (rid : N).
Let st' := drop_region rid st.
Hypothesis PTR : ptrs_in (fun x => x <> rid) st.


End DROP.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ci_mptrs_frame st st2 : ltac2:(CDefT.buildp (gd_tbl_F_free_K ()) "P,(4<.O2.)P,(7.(2.(2.(2.(2.(2.(2.(2.(2.$4=.$4=.)$4=.)$4=.)$4.)$4.)$4.)$4.)$4.)(4>.(4?.O1.))(4>.(4?.O2.)))P,(7.(:.$;.(<.$3.$=.$4.$>.)(?.$3.$=.$10.$4.$>.$11.)$2=.)(2>.O1.)(2>.O2.))P,(7.(:.$3.$=.$10.$2:.)(2;.O1.)(2;.O2.))(4<.O1.)")
(* [comment removed for export] *).
Proof.
  (intros dd_H; ddestruct dd_H as (M1 & M2 & M3 & M4 & M5); intros EC EA ER).
  assert (NG : forall p, ng_ptr st p -> ng_ptr st2 p) by (intros [q|]; cbn; [rewrite ER|]; auto).
  unfold amc in EC. inversion EC.
  unfold ci_mptrs. rewrite H0, H1, H2, H3, EA. repeat split; auto. intros a ar Ha. apply NG. exact (M5 a ar Ha).
Qed.

