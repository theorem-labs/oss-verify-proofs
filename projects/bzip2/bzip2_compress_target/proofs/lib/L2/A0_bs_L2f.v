(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout RT_iface D_defs D_kit I_read.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2 Require Import L2Kit L2Act L2Stmt A0_fs_L2f.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzArr BzCMem BzCState BzCSortF BzCSortM BzCBlock BzArrD CmpMem CmpCut CmpCutMS BzCLemmasFs BzCFactsFs CmpFsKit0 CmpMsKit AsanKit AsanKit2 AsanCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCFactsBs BzCPermM BzCFactsBs2 BzCLemmasMs BzCLemmasMs2 BzCLemmasMs4 BzCLemmasMs6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_fsS A0_cmp_fsP A0_cmp_msV A0_cmp_msW A0_cmp_msS A0_cmp_bsV A0_cmp_bsP A0_cmp_bsJ A0_cmp_bsI A0_cmp_bsK A0_cmp_bsF A0_cmp_bsG A0_cmp_bsE A0_cmp_bsH A0_cmp_bsQ A0_cmp_msO A0_cmp_bsM.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0_cmp_bs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).
Strategy 1000 [ms_ftab_zero ms_radix1 ms_overshoot ms_accum ms_radix2 ms_ro_init ms_sh_shift ms_sh_pass ms_shell ms_step1 ms_copy_init ms_copy_fwd ms_copy_bwd
               ms_mark ms_shifts ms_quad ms_big ms_bigs mainSort blockSort mainQSort3 mqs_loop mainSimpleSort find_orig fallbackSort].

Ltac split_at_cb8 cs :=
  lazymatch cs with
  | CB 8 ?bs :: ?post => constr:((@nil cell, bs, post))
  | ?c :: ?rest => let r := split_at_cb8 rest in lazymatch r with (?pre, ?bs, ?post) => constr:((c :: pre, bs, post)) end
  end.
Ltac cb8_all H :=
  repeat (lazymatch type of H with rw_cells ?segs ?m ?A ?cs =>
            let r := split_at_cb8 cs in
            lazymatch r with (?pre, ?bs, ?post) => apply (CmpHmKit.rw_cells_CB8_C8 segs m A pre bs post) in H; cbn [app] in H end end).
Lemma In_f8 : In 248 set_shadow_vals. Proof. unfold set_shadow_vals. do 12 right. left. reflexivity. Qed.
Lemma In_00 : In 0 set_shadow_vals. Proof. left. reflexivity. Qed.

(* [comment removed for export] *)
Lemma stk_joinL : forall segs (m : mem) a b b' c, stk segs m a b -> stk segs m b' c -> b = b' -> a <= b <= c -> stk segs m a c.
Proof. intros segs m a b b' c H1 H2 -> Hle. eapply stk_merge; [exact H1| exact H2| exact Hle]. Qed.
Ltac stk_addL ST K :=
  lazymatch type of K with stk _ _ ?b' ?c =>
  lazymatch type of ST with stk ?segs ?m ?lo ?b =>
    let H := fresh in pose proof (stk_joinL segs m lo b b' c ST K ltac:(lia) ltac:(lia)) as H; clear ST K; rename H into ST end end.
Ltac stk_eatL ST H :=
  let K := fresh "Kst" in
  pose proof (stk_of_rw_cells a0segs _ _ _ H) as K; cbn [cells_size csize Nat.add] in K;
  lazymatch type of K with stk _ _ _ (?A + Z.of_nat ?k) => let z := eval cbv in (Z.of_nat k) in change (Z.of_nat k) with z in K end;
  stk_addL ST K; clear H.

Section BSG.
Context {BZP : BzParams} {ACEIL__ : ACeil}.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis SSH : forall v, In v set_shadow_vals -> set_shadow_contract RT v.
Hypothesis MSET : memset_icontract RT e_asan_memset.
Hypothesis SFREE : stack_free_contract RT 7.
Hypothesis FSC : fallbackSort_contract RT fs_facts.

(* [comment removed for export] *)
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (cx : cctx) (g : eg) (e : est) (lo qE q1 q2 qF qsp qo qq : Z) (m0 : mem).
Notation XE F fc := (ME ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (c_E cx) (c_A1 cx) (c_A2 cx) (c_FT cx) (e_nblock e) qo lo qE q1 q2 qF qsp qq
                        (e_arr1 e) (e_arr2 e) (e_ftab e) (Z_to_bv 64 0) m0).
Variable F0 : bvmap 5 word. Variable fc0 : bv 32.
Hypothesis XOK1 : msenv_ok1 (XE F0 fc0). Hypothesis XSEP : msenv_sep (XE F0 fc0).
Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx. Hypothesis IMG : cctx_img (aci_c A0C) cx.
Hypothesis TP : tp = Z_to_bv 64 0x5fc0d8.
Hypothesis QOD : qo = e_nblock e + Z.land (e_nblock e) 1 + 34. Hypothesis QOR : e_nblock e + 34 <= qo <= e_nblock e + 35. Hypothesis QOQ : qo = 2 * qq.
Hypothesis EQOF : bp_qoff e = qo.
Notation usp := (bv_unsigned sp).
Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation FT := (c_FT cx). Notation n := (e_nblock e).
Notation Wbs := [(E + 48, E + 52); (A1, A1 + ARR1_SIZE); (A2, A2 + ARR2_SIZE); (FT, FT + 262148)].
Notation cSB := (Z_to_bv 64 2147450880).
Notation SAVEDr := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma XOKF : forall F fc, msenv_ok1 (XE F fc). Proof. intros. exact XOK1. Qed.
Lemma XSEPF : forall F fc, msenv_sep (XE F fc). Proof. intros. exact XSEP. Qed.

Section Act.
Variables (PMc : Model -> Prop) (Y : amenv) (SHF : Z) (fr : list (Z * nat)) (live0 : list (Z * Z)) (sp0 : Z).
Hypothesis FDO : fdfs_only PMc. Hypothesis MST : mat_stable PMc.
Hypothesis YOK : amenv_ok (XE F0 fc0) Y. Hypothesis YSEP : amenv_sep (XE F0 fc0) Y. Hypothesis YOFF : amenv_offsh (XE F0 fc0) Y. Hypothesis YSF : amenv_shf Y SHF.
Notation P := (am_P Y). Notation FB := (am_FB Y).
Notation SLO := (am_SLO Y). Notation SHI := (am_SHI Y). Notation SD := (am_SD Y).
Notation RO := (am_RO Y). Notation BD := (am_BD Y). Notation CS := (am_CS Y). Notation CE := (am_CE Y).
Hypothesis G : act_geom RT lo P usp sp0 true 7 FB SHF 8192 1024 fr live0 Wbs.
Hypothesis ACE : alloc_ceiling = sp0 - STACK_WIN.
Hypothesis ROOM : lo + RT_STACK + 1408 <= P.
Hypothesis FRMX : (length fr + 1 < FRAMES_MAX)%nat.
Hypothesis LIVE : In (E, 55768) live0. Hypothesis LIV1 : In (A1, ARR1_SIZE) live0. Hypothesis LIV2 : In (A2, ARR2_SIZE) live0. Hypothesis LIVF : In (FT, 262148) live0.
(* [comment removed for export] *)
Hypothesis GFE : E + 55768 <= FB \/ FB + 8192 <= E. Hypothesis GFA1 : A1 + ARR1_SIZE <= FB \/ FB + 8192 <= A1.
Hypothesis GFA2 : A2 + ARR2_SIZE <= FB \/ FB + 8192 <= A2. Hypothesis GFFT : FT + 262148 <= FB \/ FB + 8192 <= FT.
Hypothesis GLSE : E + 55768 <= SHF \/ SHF + 1024 <= E. Hypothesis GLSA1 : A1 + ARR1_SIZE <= SHF \/ SHF + 1024 <= A1.
Hypothesis GLSA2 : A2 + ARR2_SIZE <= SHF \/ SHF + 1024 <= A2. Hypothesis GLSFT : FT + 262148 <= SHF \/ SHF + 1024 <= FT.
Hypothesis GSELF : FB + 8192 <= SHF \/ SHF + 1024 <= FB.
Variable mi : mem.   (* [comment removed for export] *)
Notation PRESI := (PRESI usp fr live0 Wbs mi).

Lemma YOKF : forall F fc, amenv_ok (XE F fc) Y. Proof. intros. exact YOK. Qed.
Lemma YSEPF : forall F fc, amenv_sep (XE F fc) Y. Proof. intros. exact YSEP. Qed.
Lemma YOFFF : forall F fc, amenv_offsh (XE F fc) Y. Proof. intros. exact YOFF. Qed.
Lemma YSHXF : forall F fc, amenv_shx (XE F fc) Y SHF. Proof. intros. exact (amenv_shx_of1 _ Y SHF XOK1 YOK YSF YOFF). Qed.

(* [comment removed for export] *)
Definition bs_shsep : Prop :=
  (E + 55768 <= A1 \/ A1 + ARR1_SIZE <= E) /\
  (E + 55768 <= A2 \/ A2 + ARR2_SIZE <= E) /\
  (E + 55768 <= FT \/ FT + 262148 <= E) /\
  (A1 + ARR1_SIZE <= A2 \/ A2 + ARR2_SIZE <= A1) /\
  (A1 + ARR1_SIZE <= FT \/ FT + 262148 <= A1) /\
  (A2 + ARR2_SIZE <= FT \/ FT + 262148 <= A2) /\
  (E + 55768 <= FB \/ FB + 8192 <= E) /\
  (E + 55768 <= SLO \/ SLO + 400 <= E) /\
  (E + 55768 <= SHI \/ SHI + 400 <= E) /\
  (E + 55768 <= SD \/ SD + 400 <= E) /\
  (E + 55768 <= RO \/ RO + 1024 <= E) /\
  (E + 55768 <= BD \/ BD + 256 <= E) /\
  (E + 55768 <= CS \/ CS + 1024 <= E) /\
  (E + 55768 <= CE \/ CE + 1024 <= E) /\
  (A1 + ARR1_SIZE <= FB \/ FB + 8192 <= A1) /\
  (A1 + ARR1_SIZE <= SLO \/ SLO + 400 <= A1) /\
  (A1 + ARR1_SIZE <= SHI \/ SHI + 400 <= A1) /\
  (A1 + ARR1_SIZE <= SD \/ SD + 400 <= A1) /\
  (A1 + ARR1_SIZE <= RO \/ RO + 1024 <= A1) /\
  (A1 + ARR1_SIZE <= BD \/ BD + 256 <= A1) /\
  (A1 + ARR1_SIZE <= CS \/ CS + 1024 <= A1) /\
  (A1 + ARR1_SIZE <= CE \/ CE + 1024 <= A1) /\
  (A2 + ARR2_SIZE <= FB \/ FB + 8192 <= A2) /\
  (A2 + ARR2_SIZE <= SLO \/ SLO + 400 <= A2) /\
  (A2 + ARR2_SIZE <= SHI \/ SHI + 400 <= A2) /\
  (A2 + ARR2_SIZE <= SD \/ SD + 400 <= A2) /\
  (A2 + ARR2_SIZE <= RO \/ RO + 1024 <= A2) /\
  (A2 + ARR2_SIZE <= BD \/ BD + 256 <= A2) /\
  (A2 + ARR2_SIZE <= CS \/ CS + 1024 <= A2) /\
  (A2 + ARR2_SIZE <= CE \/ CE + 1024 <= A2) /\
  (FT + 262148 <= FB \/ FB + 8192 <= FT) /\
  (FT + 262148 <= SLO \/ SLO + 400 <= FT) /\
  (FT + 262148 <= SHI \/ SHI + 400 <= FT) /\
  (FT + 262148 <= SD \/ SD + 400 <= FT) /\
  (FT + 262148 <= RO \/ RO + 1024 <= FT) /\
  (FT + 262148 <= BD \/ BD + 256 <= FT) /\
  (FT + 262148 <= CS \/ CS + 1024 <= FT) /\
  (FT + 262148 <= CE \/ CE + 1024 <= FT) /\
  (E + 55768 <= SHF \/ SHF + 1024 <= E) /\
  (A1 + ARR1_SIZE <= SHF \/ SHF + 1024 <= A1) /\
  (A2 + ARR2_SIZE <= SHF \/ SHF + 1024 <= A2) /\
  (FT + 262148 <= SHF \/ SHF + 1024 <= FT) /\
  (FB + 8192 <= SHF \/ SHF + 1024 <= FB) /\
  (SLO + 400 <= SHF \/ SHF + 1024 <= SLO) /\
  (SHI + 400 <= SHF \/ SHF + 1024 <= SHI) /\
  (SD + 400 <= SHF \/ SHF + 1024 <= SD) /\
  (RO + 1024 <= SHF \/ SHF + 1024 <= RO) /\
  (BD + 256 <= SHF \/ SHF + 1024 <= BD) /\
  (CS + 1024 <= SHF \/ SHF + 1024 <= CS) /\
  (CE + 1024 <= SHF \/ SHF + 1024 <= CE) /\
  E + 55768 <= P /\ A1 + ARR1_SIZE <= P /\ A2 + ARR2_SIZE <= P /\ FT + 262148 <= P /\ FB + 8192 <= P /\ SHF + 1024 <= P /\ FB + 24 <= SLO /\ SLO + 400 <= SHI /\ SHI + 400 <= SD /\ SD + 400 <= RO /\ RO + 1024 <= BD /\ BD + 256 <= CS /\ CS + 1024 <= CE /\ CE + 1024 <= FB + 5216 /\ 17594333495296 + 65536 <= P /\ 0x61e000 <= E /\ 0x61e000 <= A1 /\ 0x61e000 <= A2 /\ 0x61e000 <= FT.
Lemma bs_shsep_ok : bs_shsep.
Proof.
  msenv_open1 XOK1. amenv_open YOK. pose proof G as [_ _ _ _ GLOW GLOR _ _ _ GFR GSH GSP0 _ _]. unfold RT_STACK, STACK_WIN, SEGTOP_A, USTACK_TOP in *.
  cbn [me_E me_A1 me_A2 me_FT me_lo me_sp me_n] in *.
  pose proof XSEP as (SA1A2 & SA1FT & SA2FT & SEA1 & SEA2 & SEFT). unfold apartm in *. cbn [me_E me_A1 me_A2 me_FT] in *.
  pose proof alloc_ceiling_range as ACR.
  unfold bs_shsep.
  split; [exact SEA1|].
  split; [exact SEA2|].
  split; [exact SEFT|].
  split; [exact SA1A2|].
  split; [exact SA1FT|].
  split; [exact SA2FT|].
  split; [exact GFE|].
  split; [clear - GFE YSLO; lia|].
  split; [clear - GFE YSHI; lia|].
  split; [clear - GFE YSD; lia|].
  split; [clear - GFE YRO; lia|].
  split; [clear - GFE YBD; lia|].
  split; [clear - GFE YCS; lia|].
  split; [clear - GFE YCE; lia|].
  split; [exact GFA1|].
  split; [clear - GFA1 YSLO; lia|].
  split; [clear - GFA1 YSHI; lia|].
  split; [clear - GFA1 YSD; lia|].
  split; [clear - GFA1 YRO; lia|].
  split; [clear - GFA1 YBD; lia|].
  split; [clear - GFA1 YCS; lia|].
  split; [clear - GFA1 YCE; lia|].
  split; [exact GFA2|].
  split; [clear - GFA2 YSLO; lia|].
  split; [clear - GFA2 YSHI; lia|].
  split; [clear - GFA2 YSD; lia|].
  split; [clear - GFA2 YRO; lia|].
  split; [clear - GFA2 YBD; lia|].
  split; [clear - GFA2 YCS; lia|].
  split; [clear - GFA2 YCE; lia|].
  split; [exact GFFT|].
  split; [clear - GFFT YSLO; lia|].
  split; [clear - GFFT YSHI; lia|].
  split; [clear - GFFT YSD; lia|].
  split; [clear - GFFT YRO; lia|].
  split; [clear - GFFT YBD; lia|].
  split; [clear - GFFT YCS; lia|].
  split; [clear - GFFT YCE; lia|].
  split; [exact GLSE|].
  split; [exact GLSA1|].
  split; [exact GLSA2|].
  split; [exact GLSFT|].
  split; [exact GSELF|].
  split; [clear - GSELF YSLO; lia|].
  split; [clear - GSELF YSHI; lia|].
  split; [clear - GSELF YSD; lia|].
  split; [clear - GSELF YRO; lia|].
  split; [clear - GSELF YBD; lia|].
  split; [clear - GSELF YCS; lia|].
  split; [clear - GSELF YCE; lia|].
  clear SA1A2 SA1FT SA2FT SEA1 SEA2 SEFT GFE GFA1 GFA2 GFFT GLSE GLSA1 GLSA2 GLSFT GSELF. repeat split; lia.
Qed.
Ltac shsep_open :=
  let H := fresh "SHS" in pose proof bs_shsep_ok as H; unfold bs_shsep in H;
  destruct H as (?DEA1 & ?DEA2 & ?DEFT & ?DA1A2 & ?DA1FT & ?DA2FT & ?DEFB & ?DESLO & ?DESHI & ?DESD & ?DERO & ?DEBD & ?DECS & ?DECE & ?DA1FB & ?DA1SLO & ?DA1SHI & ?DA1SD & ?DA1RO & ?DA1BD & ?DA1CS & ?DA1CE & ?DA2FB & ?DA2SLO & ?DA2SHI & ?DA2SD & ?DA2RO & ?DA2BD & ?DA2CS & ?DA2CE & ?DFTFB & ?DFTSLO & ?DFTSHI & ?DFTSD & ?DFTRO & ?DFTBD & ?DFTCS & ?DFTCE & ?DESH & ?DA1SH & ?DA2SH & ?DFTSH & ?DFBSH & ?DSLOSH & ?DSHISH & ?DSDSH & ?DROSH & ?DBDSH & ?DCSSH & ?DCESH & ?XL1 & ?XL2 & ?XL3 & ?XL4 & ?XL5 & ?XL6 & ?XL7 & ?XL8 & ?XL9 & ?XL10 & ?XL11 & ?XL12 & ?XL13 & ?XL14 & ?XL15 & ?XL16 & ?XL17 & ?XL18 & ?XL19);
  box_ors.

(* [comment removed for export] *)
Ltac bs_keys :=
  pose proof (ck_intro P CStack) as KP; pose proof (ck_intro usp CStack) as KU; pose proof (ck_intro FB CFrame) as KFB; pose proof (ck_intro SLO CFrame) as KSLO;
  pose proof (ck_intro SHI CFrame) as KSHI; pose proof (ck_intro SD CFrame) as KSD; pose proof (ck_intro RO CFrame) as KRO; pose proof (ck_intro BD CFrame) as KBD;
  pose proof (ck_intro CS CFrame) as KCS; pose proof (ck_intro CE CFrame) as KCE; pose proof (ck_intro SHF CShadow) as KSH;
  pose proof (ck_intro E (CLive E 55768)) as KE; pose proof (ck_intro A1 (CLive A1 ARR1_SIZE)) as KA1; pose proof (ck_intro A2 (CLive A2 ARR2_SIZE)) as KA2;
  pose proof (ck_intro FT (CLive FT 262148)) as KFT.
Ltac fp_ours := per_interval; cbn [outside]; lia.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation WMN := [(c_A1 cx, c_A1 cx + ARR1_SIZE); (c_A2 cx, c_A2 cx + ARR2_SIZE); (c_FT cx, c_FT cx + 262148); (am_P Y + 16, am_P Y + 104); (am_P Y + 152, am_P Y + 200);
                 (am_P Y + 216, am_P Y + 384); (am_P Y + 436, am_P Y + 440); (am_P Y - 16, am_P Y); (am_SLO Y, am_SLO Y + 400); (am_SHI Y, am_SHI Y + 400);
                 (am_SD Y, am_SD Y + 400); (am_RO Y, am_RO Y + 1024); (am_BD Y, am_BD Y + 256); (am_CS Y, am_CS Y + 1024); (am_CE Y, am_CE Y + 1024);
                 (SHF + 4, SHF + 170)].
Lemma In_incs : In (139040, 56) ACC_LITS.
Proof. unfold ACC_LITS. repeat (first [left; reflexivity | right]). Qed.

Lemma bs_bsviews : forall (Σ : rts RT) F fc (m : mem) (v384 : word),
  sig_ok RT sp0 true 7 FB fr live0 Σ -> ART RT Σ m ->
  rw_cells a0segs m (P + 384) (scc_cells (XE F fc)) -> rw_cells a0segs m (P + 200) [C8 (Z_to_bv 64 (SHF + 506))] ->
  bytes_at a0segs m (SHF + 178) (repeat z8 128) -> rw_cells a0segs m (SHF + 322) (shcB z8) ->
  bytes_at a0segs m (SHF + 362) (repeat z8 128) -> bytes_at a0segs m (SHF + 506) (repeat z8 128) ->
  bsviews (XE F fc) Y SHF m.
Proof.
  intros Σ F fc m v384 SOK ART0 C384 C200a SHZ1 SHCB SHZ2 SHZ3.
  msenv_open1 XOK1. amenv_open YOK. cbn [me_E me_A1 me_A2 me_FT me_lo me_sp me_n] in *.
  pose proof bs_shsep_ok as SHS. unfold bs_shsep in SHS.
  destruct SHS as (DEA1 & DEA2 & DEFT & DA1A2 & DA1FT & DA2FT & DEFB & DESLO & DESHI & DESD & DERO & DEBD & DECS & DECE & DA1FB & DA1SLO & DA1SHI & DA1SD & DA1RO & DA1BD & DA1CS & DA1CE & DA2FB & DA2SLO & DA2SHI & DA2SD & DA2RO & DA2BD & DA2CS & DA2CE & DFTFB & DFTSLO & DFTSHI & DFTSD & DFTRO & DFTBD & DFTCS & DFTCE & DESH & DA1SH & DA2SH & DFTSH & DFBSH & DSLOSH & DSHISH & DSDSH & DROSH & DBDSH & DCSSH & DCESH & XL1 & XL2 & XL3 & XL4 & XL5 & XL6 & XL7 & XL8 & XL9 & XL10 & XL11 & XL12 & XL13 & XL14 & XL15 & XL16 & XL17 & XL18 & XL19).
  pose proof alloc_ceiling_range as ACR.
  pose proof G as [_ _ _ _ GLOW GLOR GPUS GSPT GSPA GFR GSH GSP0 _ _]. unfold USTACK_TOP, RT_STACK, STACK_WIN, SEGTOP_A in GLOW, GLOR, GSPT, GFR, GSH, GSP0.
  pose proof SOK as (FRM & SP0E & LIVS).
  pose proof (LIVS _ LIV1) as LV1. pose proof (LIVS _ LIV2) as LV2. pose proof (LIVS _ LIVF) as LVF.
  destruct YSF as (AX & YSl & YSh). pose proof AX as [AX1 AX2]. unfold SH_LO, SH_HI in YSl, YSh.
  destruct YOFF as (O1 & O2 & O3 & O4). cbn [me_A1 me_A2 me_FT] in O1, O2, O3.
  assert (OP : forall a b, P - 16 <= a -> b <= SH_LO \/ SH_HI <= a) by (intros a b Ha; right; unfold SH_HI; clear - Ha XL15; lia).
  assert (OO : forall a b, FB <= a -> b <= FB + 5216 -> b <= SH_LO \/ SH_HI <= a) by (intros a b Ha Hb; clear - O4 Ha Hb; lia).
  assert (GEN : forall lo' hi', 0 <= lo' -> hi' <= 2^47 -> (hi' <= FB + 32 \/ FB + 1360 <= lo') ->
            forall x, lo' <= x < hi' -> disjoint_from WMN (x / 8 + 2147450880) 1).
  { intros lo' hi' H0 H47 DJ x Hx. cbn [disjoint_from].
    assert (X47 : 0 <= x < 2^47) by (clear - H0 H47 Hx; lia).
    split; [apply shd_app; [exact X47| exact O1]|]. split; [apply shd_app; [exact X47| exact O2]|]. split; [apply shd_app; [exact X47| exact O3]|].
    split; [apply shd_app; [exact X47| apply OP; clear; lia]|]. split; [apply shd_app; [exact X47| apply OP; clear; lia]|].
    split; [apply shd_app; [exact X47| apply OP; clear; lia]|]. split; [apply shd_app; [exact X47| apply OP; clear; lia]|].
    split; [apply shd_app; [exact X47| apply OP; clear; lia]|].
    split; [apply shd_app; [exact X47| apply OO; [clear - YSLO; lia| clear - YSLO; lia]]|]. split; [apply shd_app; [exact X47| apply OO; [clear - YSHI; lia| clear - YSHI; lia]]|].
    split; [apply shd_app; [exact X47| apply OO; [clear - YSD; lia| clear - YSD; lia]]|]. split; [apply shd_app; [exact X47| apply OO; [clear - YRO; lia| clear - YRO; lia]]|].
    split; [apply shd_app; [exact X47| apply OO; [clear - YBD; lia| clear - YBD; lia]]|]. split; [apply shd_app; [exact X47| apply OO; [clear - YCS; lia| clear - YCS; lia]]|].
    split; [apply shd_app; [exact X47| apply OO; [clear - YCE; lia| clear - YCE; lia]]|].
    split; [| exact I]. apply (shd_anchor FB SHF 4 170 x AX). clear - DJ Hx. lia. }
  destruct (af_acc_live RT AF Σ m A1 ARR1_SIZE ART0 LV1) as [_ ACC1]. destruct (af_acc_live RT AF Σ m A2 ARR2_SIZE ART0 LV2) as [_ ACC2].
  destruct (af_acc_live RT AF Σ m FT 262148 ART0 LVF) as [_ ACCF].
  pose proof (af_acc_stack RT AF Σ m (P + 436) 4 ART0 ltac:(rewrite SP0E; unfold STACK_WIN; clear - GLOW GLOR; lia) ltac:(unfold USTACK_TOP; clear - GSPT GPUS YPh; lia)) as ACCB.
  pose proof (proj1 (Forall_forall _ _) (af_acc_lits RT AF Σ m ART0) _ In_incs) as ACCI. cbn [fst snd] in ACCI.
  pose proof (acc_of_zero_shadow a0segs m FB SHF 178 128 AX1 AX2 ltac:(clear - YFl; lia) ltac:(clear; lia) SHZ1) as ACCR.
  replace (FB + 8 * 178) with RO in ACCR by (clear - YRO; lia). change (8 * Z.of_nat 128) with 1024 in ACCR.
  assert (SHZB : bytes_at a0segs m (SHF + 322) (repeat z8 32)) by exact (proj2 (proj1 SHCB)).
  pose proof (acc_of_zero_shadow a0segs m FB SHF 322 32 AX1 AX2 ltac:(clear - YFl; lia) ltac:(clear; lia) SHZB) as ACCD.
  replace (FB + 8 * 322) with BD in ACCD by (clear - YBD; lia). change (8 * Z.of_nat 32) with 256 in ACCD.
  pose proof (acc_of_zero_shadow a0segs m FB SHF 362 128 AX1 AX2 ltac:(clear - YFl; lia) ltac:(clear; lia) SHZ2) as ACCS.
  replace (FB + 8 * 362) with CS in ACCS by (clear - YCS; lia). change (8 * Z.of_nat 128) with 1024 in ACCS.
  pose proof (acc_of_zero_shadow a0segs m FB SHF 506 128 AX1 AX2 ltac:(clear - YFl; lia) ltac:(clear; lia) SHZ3) as ACCE.
  replace (FB + 8 * 506) with CE in ACCE by (clear - YCE; lia). change (8 * Z.of_nat 128) with 1024 in ACCE.
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _ & _).
  unfold bsviews. cbn [me_A1 me_A2 me_FT].
  split; [split; [| split]| split; [split; [| split; [| split; [| split; [| split]]]]| split; [| split; [| split]]]].
  - apply (frdW_intro a0segs _ m _ _ C384). unfold scc_cells. cbn [disjoint_from cells_size csize Nat.add]. change (Z.of_nat 32) with 32.
    repeat (split; [first [right; clear - XL1 XL2 XL3 XL4 XL5 XL6 YSLO YSHI YSD YRO YBD YCS YCE; lia| left; clear; lia| right; clear; lia]|]). exact I.
  - apply (frdW_intro a0segs _ m _ _ C200a). cbn [disjoint_from cells_size csize Nat.add]. change (Z.of_nat 8) with 8.
    repeat (split; [first [right; clear - XL1 XL2 XL3 XL4 XL5 XL6 YSLO YSHI YSD YRO YBD YCS YCE; lia| left; clear; lia| right; clear; lia]|]). exact I.
  - apply acoW_intro; [split; [exact (ro_C8_KN m _ _ G1)| exact (ro_C8_KN m _ _ G2)]| |];
      cbn [disjoint_from aci_got_sh aci_shvar A0C]; repeat (split; [left; clear - XL17 XL18 XL19 YFl YSLO YSHI YSD YRO YBD YCS YCE YSl XL15; lia|]); exact I.
  - apply (shzW_of_acc_gen a0segs WMN m A1 ARR1_SIZE A1 (A1 + ARR1_SIZE) ACC1); [clear - XA1l; lia| clear; lia| clear - AL1; Z.div_mod_to_equations; lia|].
    apply GEN; [clear - XA1l; lia| clear - XA1h ACR; lia| clear - DA1FB; lia].
  - apply (shzW_of_acc_gen a0segs WMN m A2 ARR2_SIZE A2 (A2 + ARR2_SIZE) ACC2); [clear - XA2l; lia| clear; lia| clear - AL2; Z.div_mod_to_equations; lia|].
    apply GEN; [clear - XA2l; lia| clear - XA2h ACR; lia| clear - DA2FB; lia].
  - apply (shzW_of_acc_gen a0segs WMN m FT 262148 FT (FT + 262144) ACCF); [clear - XFl; lia| clear; lia| clear - ALF; Z.div_mod_to_equations; lia|].
    apply GEN; [clear - XFl; lia| clear - XFh ACR; lia| clear - DFTFB; lia].
  - apply (shpW_of_acc_gen a0segs WMN m FT 262148 ACCF). apply GEN; [clear - XFl; lia| clear - XFh ACR; lia| clear - DFTFB; lia].
  - assert (HB : shpW a0segs WMN m (P + 436) (P + 436 + 4)).
    { apply (shpW_of_acc_gen a0segs WMN m (P + 436) 4 ACCB).
      apply GEN; [clear - XL15; lia| unfold USTACK_TOP in *; clear - GSPT GPUS YPh; lia| right; clear - XL5; lia]. }
    replace (P + 436 + 4) with (P + 440) in HB by (clear; lia). exact HB.
  - apply (shzW_of_acc_gen a0segs WMN m 139040 56 139040 139096 ACCI); [clear; lia| clear; lia| reflexivity|].
    apply GEN; [clear; lia| clear; lia| left; clear - YFl; lia].
  - apply (shzW_of_acc_gen a0segs WMN m RO 1024 RO (RO + 1024) ACCR); [clear - YFl YRO; lia| clear; lia| clear - YRO AX1; Z.div_mod_to_equations; lia|].
    apply GEN; [clear - YFl YRO; lia| clear - YFh YRO ACR; lia| right; clear - YRO; lia].
  - apply (shzW_of_acc_gen a0segs WMN m BD 256 BD (BD + 256) ACCD); [clear - YFl YBD; lia| clear; lia| clear - YBD AX1; Z.div_mod_to_equations; lia|].
    apply GEN; [clear - YFl YBD; lia| clear - YFh YBD ACR; lia| right; clear - YBD; lia].
  - apply (shzW_of_acc_gen a0segs WMN m CS 1024 CS (CS + 1024) ACCS); [clear - YFl YCS; lia| clear; lia| clear - YCS AX1; Z.div_mod_to_equations; lia|].
    apply GEN; [clear - YFl YCS; lia| clear - YFh YCS ACR; lia| right; clear - YCS; lia].
  - apply (shzW_of_acc_gen a0segs WMN m CE 1024 CE (CE + 1024) ACCE); [clear - YFl YCE; lia| clear; lia| clear - YCE AX1; Z.div_mod_to_equations; lia|].
    apply GEN; [clear - YFl YCE; lia| clear - YFh YCE ACR; lia| right; clear - YCE; lia].
Qed.


(* [comment removed for export] *)
Ltac cutL R k H nb :=
  let T := fresh "T" in
  lazymatch type of R with rw_cells ?segs ?m ?A ?cs =>
    destruct (rw_cells_cutZ segs m A cs k R) as [H T]; clear R; rename T into R;
    cbn [firstn skipn cells_size csize Nat.add] in H, R;
    lazymatch type of R with rw_cells _ _ ?A' _ => replace A' with nb in R by (cbn; lia) end
  end.
(* [comment removed for export] *)
Ltac glueL H1 H2 H :=
  lazymatch type of H1 with rw_cells ?segs ?m ?A ?cs1 => lazymatch type of H2 with rw_cells _ _ ?B ?cs2 =>
    assert (H : rw_cells segs m A (cs1 ++ cs2))
      by (apply (proj2 (rw_cells_app_iff_c segs m A cs1 cs2)); split; [exact H1| cbn [cells_size csize Nat.add];
          lazymatch goal with |- rw_cells _ _ ?A' _ => replace A' with B by (cbn; lia) end; exact H2]);
    cbn [app] in H; clear H1 H2 end end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bs_tail : forall (Σc : rts RT) (a1f a2f ftf : zarr) (SHn : Z) (m : mem) (v384 vmg : word)
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x26 x28 x29 x30 x31 : word) Fc fcc T c0,
  sig_ok RT sp0 true 7 FB fr live0 Σc ->
  zbok a1f -> (exists k, 0 <= k < n /\ rd32 a1f k = 0) -> saddr (E + 108) SHn ->
  stk a0segs m P (P + 384) -> rw_cells a0segs m (P + 384) [C8 v384; C8 (Z_to_bv 64 A2); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 A1)] ->
  stk a0segs m (P + 416) (usp + -104) -> rw_cells a0segs m (usp + -104) SAVEDr ->
  rw_cells a0segs m E (EHEAD1 cx g e) -> rw_cells a0segs m (E + 640) (EHEAD2 cx g e) ->
  u8arr a0segs m A1 (zb8 a1f ARR1_SIZE) -> u8arr a0segs m A2 (zb8 a2f ARR2_SIZE) -> u32arr a0segs m FT (zw32 ftf 65537) ->
  rw_cells a0segs m FB [C8 vmg] ->
  ART RT Σc m -> KMem.mem_inv asegs m -> stk asegs m lo P -> PRESI m ->
  ASTA RT Σc PMc (eq (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 sp (Z_to_bv 64 P) x10 x11 x12 x13 x14 x15 x16 x17
                              (Z_to_bv 64 (E + 108)) cSB x20 (Z_to_bv 64 FB) x22 x23 (Z_to_bv 64 FB) (Z_to_bv 64 E) x26 (Z_to_bv 64 SHn) x28 x29 x30 x31)
                         Fc (Z_to_bv 64 0x9a37c) fcc None m (seg_rom a0segs))) c0 ->
  (forall c' (Σ2 : rts RT) (m' : mem) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc',
     ASTA RT Σ2 PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F' (ret_pc ra) fc' None m' (seg_rom a0segs))) c' ->
     rt_frames RT Σ2 = fr -> rt_live RT Σ2 = rt_live RT Σc -> rt_sp0 RT Σ2 = sp0 -> rt_credit RT Σ2 = rt_credit RT Σc ->
     ART RT Σ2 m' -> KMem.mem_inv asegs m' -> stk asegs m' lo usp ->
     (let e' := est_sorted e a1f a2f ftf in let g' := EG (g_aie g) true (g_mtf g) (g_bs g) (g_zbits g) in
      rw_cells a0segs m' E (EHEAD1 cx g' e') /\ rw_cells a0segs m' (E + 640) (EHEAD2 cx g' e') /\ CmpCut.amem cx a0segs e' m') ->
     PRESI m' -> realizes asegs c' T) ->
  realizes asegs c0 T.
Proof.
  intros Σc a1f a2f ftf SHn m v384 vmg x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x26 x28 x29 x30 x31 Fc fcc T c0
    SOK OK1 EXO ASN FRA C384 FRB SAV EH1 EH2 AR1 AR2 FTB HD0 ART0 MI0 ST0 PR0 Hc0 Hk.
  msenv_open1 XOK1. amenv_open YOK. cbn [me_E me_A1 me_A2 me_FT me_lo me_sp me_n] in *. shsep_open. bs_keys.
  pose proof alloc_ceiling_range as ACR.
  pose proof G as [_ _ _ _ GLOW GLOR GPUS GSPT GSPA GFR GSH GSP0 _ _]. unfold USTACK_TOP, RT_STACK, STACK_WIN, SEGTOP_A in GLOW, GLOR, GSPT, GFR, GSH, GSP0.
  pose proof SOK as (FRM & SP0E & LIVS).
  pose proof (LIVS _ LIVE) as LVE. pose proof (LIVS _ LIV1) as LV1. pose proof (LIVS _ LIV2) as LV2. pose proof (LIVS _ LIVF) as LVF.
  (* [comment removed for export] *)
  unfold EHEAD1 in EH1.
  cutL EH1 8%nat EPRE (E + 48). cutL EH1 1%nat EOP (E + 52). cutL EH1 10%nat EMID (E + 108). cutL EH1 1%nat ENB (E + 112). rename EH1 into ERST.
  (* [comment removed for export] *)
  destruct (af_acc_live RT AF Σc m E 55768 ART0 LVE) as [_ ACCE]. destruct (af_acc_live RT AF Σc m A1 ARR1_SIZE ART0 LV1) as [_ ACC1].
  pose proof (af_live_offshadow RT AF Σc m E 55768 ART0 LVE) as OFE. pose proof (af_live_offshadow RT AF Σc m A1 ARR1_SIZE ART0 LV1) as OF1.
  destruct YOFF as (_ & _ & _ & OFB). unfold SH_LO, SH_HI in OFB.
  assert (AFW : app_fp [(E + 48, E + 52); (FB, FB + 8)]) by (cbn [app_fp]; unfold SH_LO, SH_HI; split; [clear - OFE; lia| split; [clear - OFB; lia| exact I]]).
  assert (SHE : shzW a0segs [(E + 48, E + 52); (FB, FB + 8)] m E (E + 55768)).
  { apply (shzW_of_acc a0segs _ m E 55768 E (E + 55768) ACCE AFW); [lia| lia| lia|]. clear - ALE. Z.div_mod_to_equations. lia. }
  assert (SH1 : shzW a0segs [(E + 48, E + 52); (FB, FB + 8)] m A1 (A1 + ARR1_SIZE)).
  { apply (shzW_of_acc a0segs _ m A1 ARR1_SIZE A1 (A1 + ARR1_SIZE) ACC1 AFW); [lia| lia| lia|]. clear - AL1. Z.div_mod_to_equations. lia. }
  clear ACCE ACC1 OFE OF1 AFW OFB.
  eapply (l1_realizes RT AF Σc PMc _ T c0 MST Hc0).
  eapply (A0_bs_E5 (XE Fc fcc) Y _ (XOKF Fc fcc) (XSEPF Fc fcc) (YOKF Fc fcc) (YSEPF Fc fcc) SHn a1f _ vmg v384 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m m);
    [exact ASN| exact OK1| exact EXO| exact AR1| exact EOP| exact ENB| exact HD0| exact C384| exact (kmem_inv_N _ _ MI0)| apply munch_refl| apply wmono_refl| exact SHE| exact SH1|].
  clear AR1 EOP ENB HD0 C384 SHE SH1.
  intros m1 k y5 y6 y7 y12 y13 y14 y15 y16 y17 Hk1 Zk FO AR1 EOP ENB HD0 C384 NMI1 MU1 WM1. apply evt_done. intros c1 Hc1.
  cbn [me_E me_A1 me_A2 me_FT me_n me_sp me_lo] in AR1, EOP, ENB, HD0, C384, NMI1, MU1, WM1, Hk1, FO.
  lazymatch type of MU1 with munch ?W _ _ => destruct (after_l1 AF G Σc W m m1 SOK ART0 MI0 ST0 PR0 NMI1 MU1 WM1 ltac:(fp_ours)) as (ART1 & MI1 & ST1 & PR1 & _) end.
  xfer_l1 m m1 MU1 WM1. clear NMI1 MU1 WM1.
  (* [comment removed for export] *)
  eapply (sfree_call G PMc FDO MST Σc 5216 m1); [exact SFREE| right; reflexivity| exact SOK| reflexivity| exact ART1| exact MI1| exact ST1| exact PR1| exact Hc1|].
  clear Hc1. intros c2 Σ2 m2 q0 q1' q2' vr g1 g2 g3 g4 g5 g6 g7 q3 q4 q5 q6 F2 fc2 Hc2 FRS2 LVE2 SP2 CR2 ART2 MI2 ST2 WM2 PR2 STEP2.
  rewrite (KMState.ret_pc_even 0x9a444 ltac:(lia) eq_refl) in Hc2.
  assert (LIVa : In (E, 55768) (rt_live RT Σ2)) by (rewrite LVE2; exact LVE).
  assert (LIVb : In (A1, ARR1_SIZE) (rt_live RT Σ2)) by (rewrite LVE2; exact LV1).
  assert (LIVc : In (A2, ARR2_SIZE) (rt_live RT Σ2)) by (rewrite LVE2; exact LV2).
  assert (LIVd : In (FT, 262148) (rt_live RT Σ2)) by (rewrite LVE2; exact LVF).
  clear HD0.
  xfer_rt G I STEP2 WM2 m1 m2.
  (* [comment removed for export] *)
  eapply (l1_realizes RT AF Σ2 PMc _ T c2 MST Hc2).
  eapply (A0_bs_E6 (XE F2 fc2) Y _ (XOKF F2 fc2) m2); [exact SAV| exact (kmem_inv_N _ _ MI2)|].
  apply evt_done. intros c3 Hc3.
  (* [comment removed for export] *)
  assert (STu : stk asegs m2 lo usp).
  { pose proof ST2 as STa. stk_addL STa FRA. stk_eatL STa C384. stk_addL STa FRB. stk_eatL STa SAV.
    lazymatch type of STa with stk _ _ _ ?hi => replace hi with usp in STa by lia end. exact STa. }
  (* [comment removed for export] *)
  glueL EPRE EOP EH1a. glueL EH1a EMID EH1b. glueL EH1b ENB EH1c. glueL EH1c ERST EH1.
  eapply (Hk c3 Σ2 m2); [exact Hc3| exact FRS2| exact LVE2| exact SP2| exact CR2| exact ART2| exact MI2| exact STu| | exact PR2].
  cbv zeta. split; [| split; [| split; [exact AR1| split; [exact AR2| exact FTB]]]].
  - unfold EHEAD1. cbn [est_sorted e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos e_nInUse
                          e_bw g_aie g_sort g_mtf g_bs g_zbits]. rewrite FO. exact EH1.
  - unfold EHEAD2 in *. cbn [est_sorted e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF g_aie g_sort g_mtf g_bs g_zbits]. exact EH2.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bs_act : forall (Σ1 : rts RT) (v0 v8 : word) (v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 : word) (v104 v112 v120 v128 v136 v144 : word) (v152 v160 v168 v176 v184 v192 : word) (v200 v208 : word)
    (v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336 v344 v352 v360 v368 v376 : word) (v384 v392 v400 v408 v416 v424 : word) (j432 jbud : list byte)
    (u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 : word) F1 fc1 T c1,
  sig_ok RT sp0 true 7 FB fr live0 Σ1 -> 1 <= rt_credit RT Σ1 ->
  bsX e -> est_ok e -> 1 <= n <= NBLOCKMAX + 9 ->
  rw_cells a0segs mi P [C8 v0; C8 v8] -> rw_cells a0segs mi (P + 16) [C8 v16; C8 v24; C8 v32; C8 v40; C8 v48; C8 v56; C8 v64; C8 v72; C8 v80; C8 v88; C8 v96] ->
  rw_cells a0segs mi (P + 104) [C8 v104; C8 v112; C8 v120; C8 v128; C8 v136; C8 v144] -> rw_cells a0segs mi (P + 152) [C8 v152; C8 v160; C8 v168; C8 v176; C8 v184; C8 v192] ->
  rw_cells a0segs mi (P + 200) [C8 v200; C8 v208] ->
  rw_cells a0segs mi (P + 216) [C8 v216; C8 v224; C8 v232; C8 v240; C8 v248; C8 v256; C8 v264; C8 v272; C8 v280; C8 v288; C8 v296; C8 v304; C8 v312; C8 v320; C8 v328; C8 v336; C8 v344; C8 v352; C8 v360; C8 v368; C8 v376] ->
  rw_cells a0segs mi (P + 384) [C8 v384; C8 v392; C8 v400; C8 v408] -> rw_cells a0segs mi (P + 416) [C8 v416] -> rw_cells a0segs mi (P + 424) [C8 v424] ->
  rw_cells a0segs mi (P + 432) [CB 4 j432] -> rw_cells a0segs mi (P + 436) [CB 4 jbud] ->
  stk a0segs mi (P + 440) (usp + -104) -> rw_cells a0segs mi (usp + -104) SAVEDr ->
  rw_cells a0segs mi E (EHEAD1 cx g e) -> rw_cells a0segs mi (E + 640) (EHEAD2 cx g e) ->
  u8arr a0segs mi A1 (zb8 (e_arr1 e) ARR1_SIZE) -> u8arr a0segs mi A2 (zb8 (e_arr2 e) ARR2_SIZE) -> u32arr a0segs mi FT (zw32 (e_ftab e) 65537) ->
  ART RT Σ1 mi -> KMem.mem_inv asegs mi -> stk asegs mi lo P -> wr_at asegs mi FB 8184 -> wr_at asegs mi SHF 1024 ->
  ASTA RT Σ1 PMc (eq (MS (mkR (Z_to_bv 64 0x975fc) (Z_to_bv 64 P) gp tp u0 u1 u2 sp (Z_to_bv 64 P) (Z_to_bv 64 FB) e1 e2 e3 e4 e5 e6 e7
                              s2 cSB s4 s5 s6 s7 s8 (Z_to_bv 64 E) s10 s11 u3 u4 u5 u6)
                         F1 (Z_to_bv 64 0x975fc) fc1 None mi (seg_rom a0segs))) c1 ->
  (forall c' (Σ2 : rts RT) (m' : mem) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc',
     ASTA RT Σ2 PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F' (ret_pc ra) fc' None m' (seg_rom a0segs))) c' ->
     rt_frames RT Σ2 = fr -> rt_live RT Σ2 = rt_live RT Σ1 -> rt_sp0 RT Σ2 = sp0 -> rt_credit RT Σ1 - 1 <= rt_credit RT Σ2 <= rt_credit RT Σ1 ->
     ART RT Σ2 m' -> KMem.mem_inv asegs m' -> stk asegs m' lo usp ->
     (let e' := fst (fst (fst (blockSort e znew))) in let g' := EG (g_aie g) true (g_mtf g) (g_bs g) (g_zbits g) in
      rw_cells a0segs m' E (EHEAD1 cx g' e') /\ rw_cells a0segs m' (E + 640) (EHEAD2 cx g' e') /\ CmpCut.amem cx a0segs e' m') ->
     PRESI m' -> realizes asegs c' T) ->
  realizes asegs c1 T.
Proof.
  intros Σ1 v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336 v344 v352 v360 v368 v376 v384 v392 v400 v408 v416 v424 j432 jbud
    u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F1 fc1 T c1 SOK CRED BSX EOK NB C0 C16 C104 C152 C200 C216 C384 C416 C424 C432 BUD GAP SAV EH1 EH2 AR1 AR2 FTB
    ART1 MI1 ST1 WRF WRS Hc1 Hk.
  msenv_open1 XOK1. amenv_open YOK. bz_params. cbn [me_E me_A1 me_A2 me_FT me_lo me_sp me_n] in *. shsep_open. bs_keys.
  pose proof alloc_ceiling_range as ACR.
  pose proof G as [_ _ _ _ GLOW GLOR GPUS GSPT GSPA GFR GSH GSP0 _ _]. unfold USTACK_TOP, RT_STACK, STACK_WIN, SEGTOP_A in GLOW, GLOR, GSPT, GFR, GSH, GSP0.
  pose proof SOK as (FRM & SP0E & LIVS).
  pose proof (LIVS _ LIVE) as LVE. pose proof (LIVS _ LIV1) as LV1. pose proof (LIVS _ LIV2) as LV2. pose proof (LIVS _ LIVF) as LVF.
  destruct YSF as (AX & YSl & YSh). pose proof AX as [AX1 AX2]. unfold SH_LO, SH_HI in YSl, YSh.
  destruct BSX as (FSM & FHI & FBIGS). destruct EOK as (EA1OK & EA2OK & EFTW & _).
  assert (PR1 : PRESI mi) by (intros a _; reflexivity).
  (* [comment removed for export] *)
  destruct (n_wr_at_rw_CB mi FB 24 (wr_at_sub asegs mi FB 8184 FB 24 WRF ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jh & HDj).
  change (Z.to_nat 24) with 24%nat in HDj.
  apply (rw_cells_split_CB a0segs _ _ [] 24 _ [] [8;8;8]%nat) in HDj; [| reflexivity]. cbn [mk_CB_cells app] in HDj. cb8_all HDj.
  destruct (n_wr_at_rw_CB mi SHF 178 (wr_at_sub asegs mi SHF 1024 SHF 178 WRS ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (j178 & RZ).
  change (Z.to_nat 178) with 178%nat in RZ.
  eapply (l1_realizes RT AF Σ1 PMc _ T c1 MST Hc1).
  eapply (A0_bs_P2 (XE F1 fc1) Y SHF _ (XOKF F1 fc1) (YOKF F1 fc1) (conj AX (conj YSl YSh)) (YOFFF F1 fc1) (YSHXF F1 fc1) mi mi); [exact HDj| exact RZ| exact C424| exact (kmem_inv_N _ _ MI1)| apply munch_refl| apply wmono_refl|]. clear HDj RZ C424.
  intros m2 y12_2 y13_2 y14_2 HD SHC3 C424 NMI2 MU2 WM2 . apply evt_done. intros c2 Hc2.
  cbn [me_E me_A1 me_A2 me_FT me_n me_sp me_lo me_qo] in HD, SHC3, C424, NMI2, MU2, WM2.
  lazymatch type of MU2 with munch ?W _ _ => destruct (after_l1 AF G Σ1 W mi m2 SOK ART1 MI1 ST1 PR1 NMI2 MU2 WM2 ltac:(fp_ours)) as (ART2 & MI2 & ST2 & PR2 & _) end.
  xfer_l1 mi m2 MU2 WM2. clear NMI2 MU2 WM2.
  (* [comment removed for export] *)
  eapply (ss_call G PMc FDO MST Σ1 248 178 128 m2); [exact SSH| exact SOK| exact In_f8| reflexivity| exact ART2| exact MI2| exact ST2| exact WRS| exact Hc2|].
  clear Hc2. intros c3 m3 w0_3 w1_3 w2_3 r0_3 d1_3 d2_3 d3_3 d4_3 d5_3 d6_3 d7_3 w3_3 w4_3 w5_3 w6_3 F3 fc3 Hc3 ART3 MI3 ST3 WM3 BY3 STEP3.
  pose proof (pres_step_ours G Σ1 _ _ m2 m3 SOK PR2 STEP3 ltac:(right; right; lia)) as PR3.
  xfer_rt G SOK STEP3 WM3 m2 m3.
  clear STEP3 WM3 BY3.
  rewrite (KMState.ret_pc_even 0x97948 ltac:(lia) eq_refl) in Hc3.
  (* [comment removed for export] *)
  destruct (n_wr_at_rw_CB m3 (SHF + 306) 56 (wr_at_sub asegs m3 SHF 1024 (SHF + 306) 56 WRS ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jz3 & RZ).
  change (Z.to_nat 56) with 56%nat in RZ.
  eapply (l1_realizes RT AF Σ1 PMc _ T c3 MST Hc3).
  eapply (A0_bs_P3 (XE F3 fc3) Y SHF _ (XOKF F3 fc3) (YOKF F3 fc3) (YSHXF F3 fc3) m3 m3); [exact RZ| exact C200| exact (kmem_inv_N _ _ MI3)| apply munch_refl| apply wmono_refl|]. clear RZ C200.
  intros m4 SHCB C200 NMI4 MU4 WM4 . apply evt_done. intros c4 Hc4.
  cbn [me_E me_A1 me_A2 me_FT me_n me_sp me_lo me_qo] in SHCB, C200, NMI4, MU4, WM4.
  lazymatch type of MU4 with munch ?W _ _ => destruct (after_l1 AF G Σ1 W m3 m4 SOK ART3 MI3 ST3 PR3 NMI4 MU4 WM4 ltac:(fp_ours)) as (ART4 & MI4 & ST4 & PR4 & _) end.
  xfer_l1 m3 m4 MU4 WM4. clear NMI4 MU4 WM4.
  (* [comment removed for export] *)
  eapply (ss_call G PMc FDO MST Σ1 248 362 128 m4); [exact SSH| exact SOK| exact In_f8| reflexivity| exact ART4| exact MI4| exact ST4| exact WRS| exact Hc4|].
  clear Hc4. intros c5 m5 w0_5 w1_5 w2_5 r0_5 d1_5 d2_5 d3_5 d4_5 d5_5 d6_5 d7_5 w3_5 w4_5 w5_5 w6_5 F5 fc5 Hc5 ART5 MI5 ST5 WM5 BY5 STEP5.
  pose proof (pres_step_ours G Σ1 _ _ m4 m5 SOK PR4 STEP5 ltac:(right; right; lia)) as PR5.
  xfer_rt G SOK STEP5 WM5 m4 m5.
  clear STEP5 WM5 BY5.
  rewrite (KMState.ret_pc_even 0x97a38 ltac:(lia) eq_refl) in Hc5.
  (* [comment removed for export] *)
  destruct (n_wr_at_rw_CB m5 (SHF + 490) 16 (wr_at_sub asegs m5 SHF 1024 (SHF + 490) 16 WRS ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jz5 & RZ).
  change (Z.to_nat 16) with 16%nat in RZ.
  eapply (l1_realizes RT AF Σ1 PMc _ T c5 MST Hc5).
  eapply (A0_bs_P4 (XE F5 fc5) Y SHF _ (XOKF F5 fc5) (YOKF F5 fc5) (YSHXF F5 fc5) m5 m5); [exact RZ| exact C200| exact (kmem_inv_N _ _ MI5)| apply munch_refl| apply wmono_refl|]. clear RZ C200.
  intros m6 C200 NMI6 MU6 WM6 . apply evt_done. intros c6 Hc6.
  cbn [me_E me_A1 me_A2 me_FT me_n me_sp me_lo me_qo] in C200, NMI6, MU6, WM6.
  lazymatch type of MU6 with munch ?W _ _ => destruct (after_l1 AF G Σ1 W m5 m6 SOK ART5 MI5 ST5 PR5 NMI6 MU6 WM6 ltac:(fp_ours)) as (ART6 & MI6 & ST6 & PR6 & _) end.
  xfer_l1 m5 m6 MU6 WM6. clear NMI6 MU6 WM6.
  (* [comment removed for export] *)
  eapply (ss_call G PMc FDO MST Σ1 248 506 128 m6); [exact SSH| exact SOK| exact In_f8| reflexivity| exact ART6| exact MI6| exact ST6| exact WRS| exact Hc6|].
  clear Hc6. intros c7 m7 w0_7 w1_7 w2_7 r0_7 d1_7 d2_7 d3_7 d4_7 d5_7 d6_7 d7_7 w3_7 w4_7 w5_7 w6_7 F7 fc7 Hc7 ART7 MI7 ST7 WM7 BY7 STEP7.
  pose proof (pres_step_ours G Σ1 _ _ m6 m7 SOK PR6 STEP7 ltac:(right; right; lia)) as PR7.
  xfer_rt G SOK STEP7 WM7 m6 m7.
  clear STEP7 WM7 BY7.
  rewrite (KMState.ret_pc_even 0x97a88 ltac:(lia) eq_refl) in Hc7.
  (* [comment removed for export] *)
  destruct (n_wr_at_rw_CB m7 (SHF + 634) 18 (wr_at_sub asegs m7 SHF 1024 (SHF + 634) 18 WRS ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jz7 & RZ).
  change (Z.to_nat 18) with 18%nat in RZ.
  (* [comment removed for export] *)
  pose proof EH1 as EHc. unfold EHEAD1 in EHc.
  cutL EHc 7%nat Ea (E + 40). cutL EHc 1%nat EFT (E + 48). cutL EHc 2%nat Eb (E + 56). cutL EHc 2%nat EPB (E + 72). cutL EHc 2%nat Ec (E + 88).
  cutL EHc 1%nat EWF (E + 92). cutL EHc 4%nat Ed (E + 108). cutL EHc 1%nat ENB (E + 112). clear Ea Eb Ec Ed EHc.
  pose proof EH2 as EHd. unfold EHEAD2 in EHd. cutL EHd 4%nat Ee (E + 656). cutL EHd 1%nat EVB (E + 660). clear Ee EHd.
  assert (SHE : shzW a0segs [(P + 8, P + 16); (P + 248, P + 256); (P + 392, P + 416); (P + 436, P + 440); (SHF + 634, SHF + 652)] m7 E (E + 55768)).
  { destruct (af_acc_live RT AF Σ1 m7 E 55768 ART7 LVE) as [_ ACCE].
    apply (shzW_of_acc_gen a0segs _ m7 E 55768 E (E + 55768) ACCE); [clear - XEl; lia| clear; lia| clear - ALE; Z.div_mod_to_equations; lia|].
    intros x Hx. cbn [disjoint_from]. assert (X47 : 0 <= x < 2^47) by (clear - Hx XEl XEh ACR; lia).
    assert (OP : forall a b, P <= a -> b <= SH_LO \/ SH_HI <= a) by (intros a b Ha; right; unfold SH_HI; clear - Ha XL15; lia).
    split; [apply shd_app; [exact X47| apply OP; clear; lia]|]. split; [apply shd_app; [exact X47| apply OP; clear; lia]|].
    split; [apply shd_app; [exact X47| apply OP; clear; lia]|]. split; [apply shd_app; [exact X47| apply OP; clear; lia]|].
    split; [| exact I]. apply (shd_anchor FB SHF 634 652 x AX). pose proof DEFB as DJ. unfold id in DJ. clear - DJ Hx. lia. }
  eapply (l1_realizes RT AF Σ1 PMc _ T c7 MST Hc7).
  eapply (A0_bs_P5 (XE F7 fc7) Y SHF _ (XOKF F7 fc7) (YOKF F7 fc7) ltac:(cbn [me_lo]; clear - YSh XLO ACR; lia) ltac:(cbn [me_E]; pose proof DESH as DJ; unfold id in DJ; clear - DJ; lia) m7);
    [exact C0| exact C216| exact C384| exact BUD| exact RZ| exact EFT| exact EPB| exact EWF| exact ENB| exact EVB| exact (kmem_inv_N _ _ MI7)| exact SHE| |];
    clear C0 C216 C384 BUD RZ EFT EPB EWF ENB EVB SHE Hc7.
  - (* [comment removed for export] *)
    intros m8 SHn y12 Hn ASN C0 C216 C384 BUD EFT EPB EWF ENB EVB NMI8 MU8 WM8. apply evt_done. intros c8 Hc8.
    cbn [me_E me_A1 me_A2 me_FT me_n me_sp me_lo me_qo] in C0, C216, C384, BUD, NMI8, MU8, WM8, Hn, ASN. clear EFT EPB EWF ENB EVB.
    lazymatch type of MU8 with munch ?W _ _ => destruct (after_l1 AF G Σ1 W m7 m8 SOK ART7 MI7 ST7 PR7 NMI8 MU8 WM8 ltac:(fp_ours)) as (ART8 & MI8 & ST8 & PR8 & _) end.
    xfer_l1 m7 m8 MU8 WM8. clear NMI8 MU8 WM8.
    assert (XOKB : forall F fc, msenv_ok (XE F fc)).
    { intros F fc. pose proof XOK1 as XK. unfold msenv_ok1 in XK. cbv zeta in XK. unfold msenv_ok. cbv zeta. cbn [me_E me_A1 me_A2 me_FT me_lo me_sp me_n me_qo me_qE me_q1 me_q2 me_qF me_qsp me_qq me_a1 me_a2 me_ft] in *.
      destruct XK as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17 & K18 & K19 & K20).
      repeat (split; [first [assumption| clear - K17 Hn QOR QOQ; lia]|]). exact K20. }
    destruct (FBIGS Hn) as (FA & FBIG & FPR). clear FBIGS FSM.
    (* [comment removed for export] *)
    eapply (ss_call G PMc FDO MST Σ1 0 178 128 m8); [exact SSH| exact SOK| exact In_00| reflexivity| exact ART8| exact MI8| exact ST8| exact WRS| exact Hc8|].
    clear Hc8. intros c9 m9 w0_9 w1_9 w2_9 r0_9 d1_9 d2_9 d3_9 d4_9 d5_9 d6_9 d7_9 w3_9 w4_9 w5_9 w6_9 F9 fc9 Hc9 ART9 MI9 ST9 WM9 BY9 STEP9.
    pose proof (pres_step_ours G Σ1 _ _ m8 m9 SOK PR8 STEP9 ltac:(right; right; lia)) as PR9.
    xfer_rt G SOK STEP9 WM9 m8 m9.
    change (bytes_at a0segs m9 (SHF + 178) (repeat z8 128)) in BY9. rename BY9 into SHZ1.
    clear STEP9 WM9.
    rewrite (KMState.ret_pc_even 0x97be4 ltac:(lia) eq_refl) in Hc9.
    (* [comment removed for export] *)
    assert (V200 : frdW a0segs [(SHF + 322, SHF + 354)] m9 (P + 200) [C8 (Z_to_bv 64 (SHF + 506)); C8 (Z_to_bv 64 (SHF + 362))])
      by (apply (frdW_intro a0segs _ m9 _ _ C200); cbn [disjoint_from cells_size csize Nat.add]; split; [right; clear - XL6; lia| exact I]).
    eapply (l1_realizes RT AF Σ1 PMc _ T c9 MST Hc9).
    eapply (A0_bs_P6 (XE F9 fc9) Y SHF _ m9 m9 f8b); [exact SHCB| exact (kmem_inv_N _ _ MI9)| apply munch_refl| apply wmono_refl| exact V200|]. clear SHCB V200.
    intros m10 SHCB NMI10 MU10 WM10 . apply evt_done. intros c10 Hc10.
    cbn [me_E me_A1 me_A2 me_FT me_n me_sp me_lo me_qo] in SHCB, NMI10, MU10, WM10.
    lazymatch type of MU10 with munch ?W _ _ => destruct (after_l1 AF G Σ1 W m9 m10 SOK ART9 MI9 ST9 PR9 NMI10 MU10 WM10 ltac:(fp_ours)) as (ART10 & MI10 & ST10 & PR10 & _) end.
    xfer_l1 m9 m10 MU10 WM10. clear NMI10 MU10 WM10.
    (* [comment removed for export] *)
    eapply (ss_call G PMc FDO MST Σ1 0 362 128 m10); [exact SSH| exact SOK| exact In_00| reflexivity| exact ART10| exact MI10| exact ST10| exact WRS| exact Hc10|].
    clear Hc10. intros c11 m11 w0_11 w1_11 w2_11 r0_11 d1_11 d2_11 d3_11 d4_11 d5_11 d6_11 d7_11 w3_11 w4_11 w5_11 w6_11 F11 fc11 Hc11 ART11 MI11 ST11 WM11 BY11 STEP11.
    pose proof (pres_step_ours G Σ1 _ _ m10 m11 SOK PR10 STEP11 ltac:(right; right; lia)) as PR11.
    xfer_rt G SOK STEP11 WM11 m10 m11.
    change (bytes_at a0segs m11 (SHF + 362) (repeat z8 128)) in BY11. rename BY11 into SHZ2.
    clear STEP11 WM11.
    rewrite (KMState.ret_pc_even 0x97c70 ltac:(lia) eq_refl) in Hc11.
    (* [comment removed for export] *)
    destruct (rw_cells_cutZ a0segs _ _ _ 1%nat C200) as [C200a _]. cbn [firstn] in C200a.
    eapply (l1_realizes RT AF Σ1 PMc _ T c11 MST Hc11).
    eapply (A0_bs_P7 (XE F11 fc11) Y SHF _ m11); [exact C200a| exact (kmem_inv_N _ _ MI11)|].
    apply evt_done. clear Hc11. intros c11z Hc11.
    clear C200a.
    (* [comment removed for export] *)
    eapply (ss_call G PMc FDO MST Σ1 0 506 128 m11); [exact SSH| exact SOK| exact In_00| reflexivity| exact ART11| exact MI11| exact ST11| exact WRS| exact Hc11|].
    clear Hc11. intros c12 m12 w0_12 w1_12 w2_12 r0_12 d1_12 d2_12 d3_12 d4_12 d5_12 d6_12 d7_12 w3_12 w4_12 w5_12 w6_12 F12 fc12 Hc12 ART12 MI12 ST12 WM12 BY12 STEP12.
    pose proof (pres_step_ours G Σ1 _ _ m11 m12 SOK PR11 STEP12 ltac:(right; right; lia)) as PR12.
    xfer_rt G SOK STEP12 WM12 m11 m12.
    change (bytes_at a0segs m12 (SHF + 506) (repeat z8 128)) in BY12. rename BY12 into SHZ3.
    clear STEP12 WM12.
    rewrite (KMState.ret_pc_even 0x97c7c ltac:(lia) eq_refl) in Hc12.
    (* [comment removed for export] *)
    pose proof C216 as C216c. cutL C216c 4%nat Ca (P + 248). cutL C216c 1%nat V248 (P + 256). clear Ca C216c.
    eapply (l1_realizes RT AF Σ1 PMc _ T c12 MST Hc12).
    eapply (A0_bs_P8 (XE F12 fc12) Y SHF _ (XOKB F12 fc12) (YOKF F12 fc12) m12 m12 SHn); [exact C104| exact C152| exact V248| exact (kmem_inv_N _ _ MI12)| apply munch_refl| apply wmono_refl|]. clear C104 C152 V248.
    intros m13 C104 C152 V248 NMI13 MU13 WM13 . apply evt_done. intros c13 Hc13.
    cbn [me_E me_A1 me_A2 me_FT me_n me_sp me_lo me_qo] in C104, C152, V248, NMI13, MU13, WM13.
    clear V248.
    lazymatch type of MU13 with munch ?W _ _ => destruct (after_l1 AF G Σ1 W m12 m13 SOK ART12 MI12 ST12 PR12 NMI13 MU13 WM13 ltac:(fp_ours)) as (ART13 & MI13 & ST13 & PR13 & _) end.
    xfer_l1 m12 m13 MU13 WM13. clear NMI13 MU13 WM13.
    (* [comment removed for export] *)
    eapply (memset_call G PMc FDO MST Σ1 FT 262148 z8 m13); [exact MSET| exact SOK| clear - XFl XFh ACR; lia| clear; lia| | exact ART13| exact MI13| exact ST13| exact Hc13|].
    { apply (cdst_live AF G Σ1 m13 FT 262148 FT 262148 ART13 LVF); clear; lia. }
    clear Hc13. intros c14 m14 w0_14 w1_14 w2_14 d1_14 d2_14 d3_14 d4_14 d5_14 d6_14 d7_14 w3_14 w4_14 w5_14 w6_14 F14 fc14 Hc14 ART14 MI14 ST14 WM14 BY14 STEP14.
    pose proof (pres_step G Σ1 _ m13 m14 SOK PR13 STEP14 ltac:(per_interval; right; cbn [outside]; lia)) as PR14.
    clear FTB. xfer_rt G SOK STEP14 WM14 m13 m14. clear STEP14 WM14.
    rewrite (KMState.ret_pc_even 0x97cb8 ltac:(lia) eq_refl) in Hc14.
    assert (FTB : u32arr a0segs m14 FT (zw32 (bp_ft0 e) 65537)).
    { destruct (af_acc_live RT AF Σ1 m14 FT 262148 ART14 LVF) as [WRFT _].
      pose proof (n_rw_CB_of_bytes m14 FT (repeat z8 (Z.to_nat 262148)) BY14 ltac:(rewrite repeat_length; exact WRFT)) as FTZ.
      rewrite repeat_length in FTZ. change (Z.to_nat 262148) with (Z.to_nat (4 * 65537)) in FTZ.
      rewrite (zw32_ext (bp_ft0 e) znew 65537). 2:{ intros i Hi. rewrite (E_ft0 e), (mft1_get (bp_ft e) i), zget_znew by lia. reflexivity. }
      eapply (zw32_init a0segs _ _ 65537 _ FTZ); [clear; lia| apply repeat_zero_nth]. }
    clear BY14.
    (* [comment removed for export] *)
    destruct (bs_radix_facts e qo FA EQOF) as [FACC FR2].
    assert (FT0 : forall v, 0 <= v <= 65536 -> zget (bp_ft0 e) v = 0) by (intros v Hv; rewrite (E_ft0 e); apply mft1_get; exact Hv).
    assert (FTNN : forall v, 0 <= zget (bp_ft0 e) v < 4294967296).
    { intros v. unfold bp_ft0, bp_ft. rewrite ms_ftab_zero_get, of_nat_65537. destruct (_ && _); [clear; lia| apply EFTW]. }
    cutL C104 4%nat C104a (P + 136). cutL C104 1%nat C136 (P + 144). rename C104 into C144.
    destruct (af_acc_live RT AF Σ1 m14 A1 ARR1_SIZE ART14 LV1) as [_ ACC1]. destruct (af_acc_live RT AF Σ1 m14 A2 ARR2_SIZE ART14 LV2) as [_ ACC2].
    destruct (af_acc_live RT AF Σ1 m14 FT 262148 ART14 LVF) as [_ ACCF].
    assert (AFW : app_fp [(A1, A1 + ARR1_SIZE); (A2, A2 + ARR2_SIZE); (FT, FT + 262148); (P + 16, P + 104); (P + 136, P + 144); (P + 152, P + 200); (P + 216, P + 384); (P + 384, P + 416)]).
    { destruct YOFF as (O1 & O2 & O3 & _). cbn [me_A1 me_A2 me_FT] in O1, O2, O3. cbn [app_fp].
      split; [exact O1|]. split; [exact O2|]. split; [exact O3|]. unfold SH_LO, SH_HI.
      repeat (split; [right; clear - XL15; lia|]). exact I. }
    assert (SH1 : shzW a0segs _ m14 A1 (A1 + ARR1_SIZE)) by (apply (shzW_of_acc a0segs _ m14 A1 ARR1_SIZE A1 (A1 + ARR1_SIZE) ACC1 AFW); [clear - XA1l; lia| clear - XA1h ACR; lia| clear; lia| clear - AL1; Z.div_mod_to_equations; lia]).
    assert (SH2 : shzW a0segs _ m14 A2 (A2 + ARR2_SIZE)) by (apply (shzW_of_acc a0segs _ m14 A2 ARR2_SIZE A2 (A2 + ARR2_SIZE) ACC2 AFW); [clear - XA2l; lia| clear - XA2h ACR; lia| clear; lia| clear - AL2; Z.div_mod_to_equations; lia]).
    assert (SHFz : shzW a0segs _ m14 FT (FT + 262144)) by (apply (shzW_of_acc a0segs _ m14 FT 262148 FT (FT + 262144) ACCF AFW); [clear - XFl; lia| clear - XFh ACR; lia| clear; lia| clear - ALF; Z.div_mod_to_equations; lia]).
    assert (SHFp : shpW a0segs _ m14 FT (FT + 262148)) by (apply (shpW_of_acc a0segs _ m14 FT 262148 ACCF AFW); [clear - XFl; lia| clear - XFh ACR; lia]).
    clear ACC1 ACC2 ACCF AFW.
    eapply (l1_realizes RT AF Σ1 PMc _ T c14 MST Hc14).
    eapply (A0_bs_seg1 (XE F14 fc14) Y SHF _ (XOKB F14 fc14) (XSEPF F14 fc14) (YOKF F14 fc14) (Z.to_nat (n / 4)) (Z.to_nat (n mod 4)) (e_arr1 e) (e_arr2 e) (bp_ft0 e)); [exact QOD| cbn [me_n]; clear - LNB; Z.div_mod_to_equations; lia| cbn [me_n]; clear - LNB; Z.div_mod_to_equations; lia| exact EA1OK| exact EA2OK| exact FT0| exact FTNN| exact FACC| exact FR2| exact AR1| exact AR2| exact FTB| exact C16| exact C136| exact C152| exact C216| exact C384| exact (kmem_inv_N _ _ MI14)| apply munch_refl| apply wmono_refl| exact SH1| exact SH2| exact SHFz| exact SHFp|]. clear AR1 AR2 FTB C16 C136 C152 C216 C384 SH1 SH2 SHFz SHFp FACC FR2.
    intros m15 SH2 a2b ftb a1c ftc jb sc y5_15 y6_15 y13_15 y14_15 y15_15 y16_15 y17_15 y24_15 ASA2 Er a2o Eqn OK1c OKo FTCc LOWo AR1 AR2 FTB C16 C136 C152 C216 C384 NMI15 MU15 WM15 . apply evt_done. intros c15 Hc15.
    cbn [me_E me_A1 me_A2 me_FT me_n me_sp me_lo me_qo] in SH2, ASA2, Er, Eqn, OK1c, OKo, FTCc, LOWo, AR1, AR2, FTB, C16, C136, C152, C216, C384, NMI15, MU15, WM15.
    cbn [me_n me_qo me_A1 me_A2 me_FT] in Er, Eqn, a2o.
    lazymatch type of MU15 with munch ?W _ _ => destruct (after_l1 AF G Σ1 W m14 m15 SOK ART14 MI14 ST14 PR14 NMI15 MU15 WM15 ltac:(fp_ours)) as (ART15 & MI15 & ST15 & PR15 & _) end.
    xfer_l1 m14 m15 MU15 WM15. clear NMI15 MU15 WM15.
    (* [comment removed for export] *)
    pose proof (nm_mono e qo a2b ftb jb a1c ftc sc EQOF Er Eqn FA) as MONO.
    pose proof (nm_pr e qo a2b ftb jb a1c ftc sc EQOF Er Eqn FPR) as PRc.
    pose proof (nm_exit_false e qo a2b ftb jb a1c ftc sc EQOF Er Eqn) as FIN0.
    pose proof (nm_exit_true e qo a2b ftb jb a1c ftc sc EQOF Er Eqn) as FIN1.
    (* [comment removed for export] *)
    assert (SHZB : bytes_at a0segs m15 (SHF + 322) (repeat z8 32)) by exact (proj2 (proj1 SHCB)).
    pose proof (acc_of_zero_shadow a0segs m15 FB SHF 322 32 AX1 AX2 ltac:(clear - YFl; lia) ltac:(clear; lia) SHZB) as ACCD.
    replace (FB + 8 * 322) with BD in ACCD by (clear - YBD; lia). change (8 * Z.of_nat 32) with 256 in ACCD. clear SHZB.
    assert (WRBD : wr_at asegs m15 BD 256) by exact (wr_at_sub asegs m15 FB 8184 BD 256 WRF ltac:(clear - YBD; lia) ltac:(clear - YBD; lia) ltac:(clear; lia)).
    eapply (memset_call G PMc FDO MST Σ1 BD 256 z8 m15); [exact MSET| exact SOK| clear - YFl YFh YBD ACR; lia| clear; lia| | exact ART15| exact MI15| exact ST15| exact Hc15|].
    { apply (cdst_frame G Σ1 m15 BD 256 SOK ACCD WRBD); clear - YBD; lia. }
    clear Hc15 ACCD. intros c16 m16 w0_16 w1_16 w2_16 d1_16 d2_16 d3_16 d4_16 d5_16 d6_16 d7_16 w3_16 w4_16 w5_16 w6_16 F16 fc16 Hc16 ART16 MI16 ST16 WM16 BY16 STEP16.
    pose proof (pres_step_ours G Σ1 _ _ m15 m16 SOK PR15 STEP16 ltac:(right; left; clear - YBD; lia)) as PR16.
    xfer_rt G SOK STEP16 WM16 m15 m16. clear STEP16 WM16.
    rewrite (KMState.ret_pc_even 0x984d4 ltac:(lia) eq_refl) in Hc16.
    assert (BDB : u8arr a0segs m16 BD (zb8 bp_bd5 256)).
    { pose proof (n_rw_CB_of_bytes m16 BD (repeat z8 (Z.to_nat 256)) BY16 ltac:(rewrite repeat_length; exact WRBD)) as BDZ.
      rewrite repeat_length in BDZ.
      rewrite (zb8_ext bp_bd5 znew 256) by (intros i _; rewrite bd5_zero; symmetry; apply zget_znew).
      eapply (zb8_init a0segs _ _ 256 _ BDZ); [clear; lia| apply repeat_zero_nth]. }
    clear BY16 WRBD.
    (* [comment removed for export] *)
    destruct (n_wr_at_rw_CB m16 RO 1024 (wr_at_sub asegs m16 FB 8184 RO 1024 WRF ltac:(clear - YRO; lia) ltac:(clear - YRO; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (jro & ROJ).
    destruct (n_wr_at_rw_CB m16 SLO 400 (wr_at_sub asegs m16 FB 8184 SLO 400 WRF ltac:(clear - YSLO; lia) ltac:(clear - YSLO; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (Jlo & SLJ).
    destruct (n_wr_at_rw_CB m16 SHI 400 (wr_at_sub asegs m16 FB 8184 SHI 400 WRF ltac:(clear - YSHI; lia) ltac:(clear - YSHI; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (Jhi & SHJ).
    destruct (n_wr_at_rw_CB m16 SD 400 (wr_at_sub asegs m16 FB 8184 SD 400 WRF ltac:(clear - YSD; lia) ltac:(clear - YSD; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (Jd & SDJ).
    destruct (n_wr_at_rw_CB m16 CS 1024 (wr_at_sub asegs m16 FB 8184 CS 1024 WRF ltac:(clear - YCS; lia) ltac:(clear - YCS; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (jcs & CSJ).
    destruct (n_wr_at_rw_CB m16 CE 1024 (wr_at_sub asegs m16 FB 8184 CE 1024 WRF ltac:(clear - YCE; lia) ltac:(clear - YCE; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (jce & CEJ).
    assert (Ljro : Z.of_nat (length jro) = 1024) by (pose proof (proj1 (proj1 (proj1 ROJ))) as W; cbn in W; clear - W; lia).
    assert (LJlo : Z.of_nat (length Jlo) = 400) by (pose proof (proj1 (proj1 (proj1 SLJ))) as W; cbn in W; clear - W; lia).
    assert (LJhi : Z.of_nat (length Jhi) = 400) by (pose proof (proj1 (proj1 (proj1 SHJ))) as W; cbn in W; clear - W; lia).
    assert (LJd : Z.of_nat (length Jd) = 400) by (pose proof (proj1 (proj1 (proj1 SDJ))) as W; cbn in W; clear - W; lia).
    change (Z.to_nat 1024) with (Z.to_nat (4 * 256)) in ROJ, CSJ, CEJ. change (Z.to_nat 400) with (Z.to_nat (4 * 100)) in SLJ, SHJ, SDJ.
    pose proof (ovw_init a0segs m16 RO 256 jro ROJ ltac:(clear; lia)) as ROA. pose proof (ovw_init a0segs m16 SLO 100 Jlo SLJ ltac:(clear; lia)) as SLOB.
    pose proof (ovw_init a0segs m16 SHI 100 Jhi SHJ ltac:(clear; lia)) as SHIB. pose proof (ovw_init a0segs m16 SD 100 Jd SDJ ltac:(clear; lia)) as SDB.
    pose proof (S0_cmp_bs.zw32_of_junk a0segs m16 CS 256 jcs CSJ ltac:(clear; lia)) as CSB. pose proof (S0_cmp_bs.zw32_of_junk a0segs m16 CE 256 jce CEJ ltac:(clear; lia)) as CEB.
    clear ROJ SLJ SHJ SDJ CSJ CEJ.
    pose proof (nm_big e qo a2b ftb jb a1c ftc sc EQOF Er Eqn FBIG (S0_cmp_bs.zarr_of_junkw jcs 256) (S0_cmp_bs.zarr_of_junkw jce 256) znew znew znew) as BF.
    assert (Hb9 : 0 <= n * budget_q < 2147483648) by (pose proof (budget0_rng n ltac:(clear - LNB BZbsL__ BZbsH__; lia)) as BQ; clear - BQ; lia).
    destruct (rw_cells_cutZ a0segs _ _ _ 1%nat C200) as [C200a _]. cbn [firstn] in C200a.
    pose proof (bs_bsviews Σ1 F16 fc16 m16 v384 SOK ART16 C384 C200a SHZ1 SHCB SHZ2 SHZ3) as BSV. clear C200a.
    change (rw_cells a0segs m16 (SHF + 4) (shc3 f8b)) with (id (rw_cells a0segs m16 (SHF + 4) (shc3 f8b))) in SHC3.
    eapply (l1_realizes RT AF Σ1 PMc _ T c16 MST Hc16).
    eapply (A0_bs_main (XE F16 fc16) Y SHF _ (XOKB F16 fc16) (XSEPF F16 fc16) (YOKF F16 fc16) (amenv_sepx_of1 _ Y (XOKF F16 fc16) (YOKF F16 fc16) (YSEPF F16 fc16))
              (conj AX (conj YSl YSh)) (YOFFF F16 fc16) (YSHXF F16 fc16) (n * budget_q) 0 a1c a2o ftc bp_bd5 (S0_cmp_bs.zarr_of_junkw jcs 256) (S0_cmp_bs.zarr_of_junkw jce 256)
              znew znew znew znew znew znew jro Jlo Jhi Jd);
      [exact MONO| exact Hb9| exact BF| exact OK1c| exact OKo| exact bd5_zbok| exact PRc| exact Ljro| exact LJlo| exact LJhi| exact LJd
      | exact AR1| exact AR2| exact FTB| exact BDB| exact CSB| exact CEB| exact SLOB| exact SHIB| exact SDB| exact ROA| exact C16| exact C152| exact C216| exact BUD
      | exact ST16| exact SHC3| exact (kmem_inv_N _ _ MI16)| apply munch_refl| apply wmono_refl| exact BSV|].
    clear AR1 AR2 FTB BDB CSB CEB SLOB SHIB SDB ROA C16 C152 C216 BUD SHC3 BSV Hc16 BF MONO.
    intros ex m17 a1' a2' ft' bd' cs' ce' sl' sh' sd' nl' nh' nd' b' nqs' y5_17 y6_17 y7_17 y12_17 y13_17 y14_17 y15_17 y16_17 y17_17 y18_17 y20_17 y21_17 y24_17 y25_17 y26_17 y28_17 y29_17 y30_17 y31_17
      EB Hb' OK1' OK2' BDOK' PR' RK6 MLM C16 C152 C192 MU17 WM17. apply evt_done. intros c17 Hc17.
    destruct MLM as (AR1 & AR2 & FTB & BDB & CSB & CEB & SLOB & SHIB & SDB & ROB & (scl' & w184' & sq' & SCL & HIC & SCQ) & BUD & STn & SHC3 & NMI17).
    cbn [me_E me_A1 me_A2 me_FT me_n me_sp me_lo me_qo] in AR1, AR2, FTB, BDB, CSB, CEB, SLOB, SHIB, SDB, ROB, SCL, HIC, SCQ, BUD, STn, SHC3, NMI17, C16, C152, C192, MU17, WM17, EB.
    lazymatch type of MU17 with munch ?W _ _ =>
      destruct (after_l1_leaf AF G Σ1 W 16 m16 m17 SOK ART16 MI16 PR16 NMI17 MU17 WM17 ltac:(clear; lia) ltac:(pose proof ROOM as R'; unfold RT_STACK in R' |- *; clear - R'; lia) ltac:(fp_ours)) as (ART17 & MI17 & PR17 & _) end.
    assert (ST17 : stk asegs m17 lo P) by exact STn. clear STn ST16.
    unfold id in SHC3.
    xfer_l1 m16 m17 MU17 WM17. clear NMI17 MU17 WM17.
    clear SHZ3.
    (* [comment removed for export] *)
    eapply (ss_call G PMc FDO MST Σ1 248 506 128 m17); [exact SSH| exact SOK| exact In_f8| reflexivity| exact ART17| exact MI17| exact ST17| exact WRS| exact Hc17|].
    clear Hc17. intros c18 m18 w0_18 w1_18 w2_18 r0_18 d1_18 d2_18 d3_18 d4_18 d5_18 d6_18 d7_18 w3_18 w4_18 w5_18 w6_18 F18 fc18 Hc18 ART18 MI18 ST18 WM18 BY18 STEP18.
    pose proof (pres_step_ours G Σ1 _ _ m17 m18 SOK PR17 STEP18 ltac:(right; right; lia)) as PR18.
    xfer_rt G SOK STEP18 WM18 m17 m18.
    clear STEP18 WM18 BY18.
    rewrite (KMState.ret_pc_even 0x9a26c ltac:(lia) eq_refl) in Hc18.
    (* [comment removed for export] *)
    eapply (l1_realizes RT AF Σ1 PMc _ T c18 MST Hc18).
    eapply (A0_bs_E2 (XE F18 fc18) Y SHF _ m18); [exact C200| exact (kmem_inv_N _ _ MI18)|].
    apply evt_done. clear Hc18. intros c18z Hc18.
    clear SHZ2.
    (* [comment removed for export] *)
    eapply (ss_call G PMc FDO MST Σ1 248 362 128 m18); [exact SSH| exact SOK| exact In_f8| reflexivity| exact ART18| exact MI18| exact ST18| exact WRS| exact Hc18|].
    clear Hc18. intros c19 m19 w0_19 w1_19 w2_19 r0_19 d1_19 d2_19 d3_19 d4_19 d5_19 d6_19 d7_19 w3_19 w4_19 w5_19 w6_19 F19 fc19 Hc19 ART19 MI19 ST19 WM19 BY19 STEP19.
    pose proof (pres_step_ours G Σ1 _ _ m18 m19 SOK PR18 STEP19 ltac:(right; right; lia)) as PR19.
    xfer_rt G SOK STEP19 WM19 m18 m19.
    clear STEP19 WM19 BY19.
    rewrite (KMState.ret_pc_even 0x9a278 ltac:(lia) eq_refl) in Hc19.
    (* [comment removed for export] *)
    pose proof C104a as C104c. cutL C104c 3%nat C104v (P + 128). clear C104c.
    assert (V104 : frdW a0segs [(SHF + 322, SHF + 354)] m19 (P + 104) [C8 (Z_to_bv 64 SHn); C8 (Z_to_bv 64 (E + 108)); C8 (Z_to_bv 64 (SHF + 178))])
      by (apply (frdW_intro a0segs _ m19 _ _ C104v); cbn [disjoint_from cells_size csize Nat.add]; split; [right; clear - XL6; lia| exact I]).
    clear C104v.
    eapply (l1_realizes RT AF Σ1 PMc _ T c19 MST Hc19).
    eapply (A0_bs_E3 (XE F19 fc19) Y SHF _ m19 m19 z8); [exact SHCB| exact (kmem_inv_N _ _ MI19)| apply munch_refl| apply wmono_refl| exact V104|]. clear SHCB V104.
    intros m20 SHCB NMI20 MU20 WM20 . apply evt_done. intros c20 Hc20.
    cbn [me_E me_A1 me_A2 me_FT me_n me_sp me_lo me_qo] in SHCB, NMI20, MU20, WM20.
    lazymatch type of MU20 with munch ?W _ _ => destruct (after_l1 AF G Σ1 W m19 m20 SOK ART19 MI19 ST19 PR19 NMI20 MU20 WM20 ltac:(fp_ours)) as (ART20 & MI20 & ST20 & PR20 & _) end.
    xfer_l1 m19 m20 MU20 WM20. clear NMI20 MU20 WM20.
    clear SHZ1.
    (* [comment removed for export] *)
    eapply (ss_call G PMc FDO MST Σ1 248 178 128 m20); [exact SSH| exact SOK| exact In_f8| reflexivity| exact ART20| exact MI20| exact ST20| exact WRS| exact Hc20|].
    clear Hc20. intros c21 m21 w0_21 w1_21 w2_21 r0_21 d1_21 d2_21 d3_21 d4_21 d5_21 d6_21 d7_21 w3_21 w4_21 w5_21 w6_21 F21 fc21 Hc21 ART21 MI21 ST21 WM21 BY21 STEP21.
    pose proof (pres_step_ours G Σ1 _ _ m20 m21 SOK PR20 STEP21 ltac:(right; right; lia)) as PR21.
    xfer_rt G SOK STEP21 WM21 m20 m21.
    clear STEP21 WM21 BY21.
    rewrite (KMState.ret_pc_even 0x9a308 ltac:(lia) eq_refl) in Hc21.
    (* [comment removed for export] *)
    glueL C104a C136 C104b. glueL C104b C144 C104.
    pose proof EH1 as EHc. unfold EHEAD1 in EHc. cutL EHc 5%nat Ea (E + 24). cutL EHc 2%nat EC (E + 40). clear Ea EHc.
    assert (SHE0 : shzW a0segs [] m21 E (E + 55768)).
    { destruct (af_acc_live RT AF Σ1 m21 E 55768 ART21 LVE) as [_ ACCE].
      apply (shzW_of_acc a0segs [] m21 E 55768 E (E + 55768) ACCE I); [clear - XEl; lia| clear - XEh ACR; lia| clear; lia| clear - ALE; Z.div_mod_to_equations; lia]. }
    assert (Hbr : -2147483648 < b' < 2147483648) by (destruct ex; clear - Hb' Hb9; lia).
    unfold scc_cells in C384. cbn [me_A1 me_A2 me_n me_qo] in C384.
    eapply (l1_realizes RT AF Σ1 PMc _ T c21 MST Hc21).
    eapply (A0_bs_E4 (XE F21 fc21) Y _ (XOKB F21 fc21) (YOKF F21 fc21) m21 SHn b'); [exact ASN| exact Hbr| exact C104| exact SCQ| exact C384| exact BUD| exact EC| exact (kmem_inv_N _ _ MI21)| exact SHE0| |];
      clear EC SHE0 Hc21.
    + (* [comment removed for export] *)
      intros y10 y11 Hb0. apply evt_done. intros c22 Hc22.
      destruct ex; [exfalso; clear - Hb' Hb0; lia|].
      destruct (FIN0 _ _ _ _ _ _ _ _ _ _ _ _ OK1c OKo RK6 EB FHI Hn eq_refl) as [EXO EEf]. pose proof (EEf Hb0) as EE. clear EEf FIN0 FIN1.
      (* [comment removed for export] *)
      destruct (rw_cells_cutZ a0segs _ FB _ 1%nat HD) as [HD0 _]. cbn [firstn] in HD0.
      clear HD SHC3 SHCB WRF WRS BDB CSB CEB SLOB SHIB SDB ROB.
      assert (FRA : stk a0segs m21 P (P + 384)).
      { pose proof (stk_of_rw_cells a0segs _ _ _ C0) as STa. cbn [cells_size csize Nat.add] in STa. change (Z.of_nat 16) with 16 in STa.
        unfold sc0_cells in C16. unfold scl_cells in SCL. unfold sck_cells in C152. unfold scq_cells in SCQ.
        stk_eatL STa C16. stk_eatL STa SCL. stk_eatL STa C104. stk_eatL STa C152. stk_eatL STa HIC. stk_eatL STa C192. stk_eatL STa C200. stk_eatL STa SCQ.
        lazymatch type of STa with stk _ _ _ ?hi => replace hi with (P + 384) in STa by (clear; lia) end. exact STa. }
      assert (FRB : stk a0segs m21 (P + 416) (usp + -104)).
      { pose proof (stk_of_rw_cells a0segs _ _ _ C416) as STa. cbn [cells_size csize Nat.add] in STa. change (Z.of_nat 8) with 8 in STa.
        stk_eatL STa C424. stk_eatL STa C432. stk_eatL STa BUD. stk_addL STa GAP. exact STa. }
      clear C0 C416 C424 C432 GAP.
      eapply (bs_tail Σ1 a1' a2' ft' SHn m21); [exact SOK| exact OK1'| exact EXO| exact ASN| exact FRA| exact C384| exact FRB| exact SAV| exact EH1| exact EH2| exact AR1| exact AR2| exact FTB| exact HD0
                                         | exact ART21| exact MI21| exact ST21| exact PR21| exact Hc22|].
      intros c' Σ2 m' z0 z1 z2 h0 h1 h2 h3 h4 h5 h6 h7 z3 z4 z5 z6 F' fc' Hc' FRS2 LVE2 SP2 CR2 ART' MI' ST' POST PRz.
      eapply (Hk c' Σ2 m'); [exact Hc'| exact FRS2| exact LVE2| exact SP2| rewrite CR2; clear; lia| exact ART'| exact MI'| exact ST'| | exact PRz].
      cbv zeta. rewrite EE. exact POST.
    + (* [comment removed for export] *)
      intros Hbn. apply evt_done. intros c22 Hc22.
      destruct ex; [| exfalso; clear - Hb' Hbn; lia].
      destruct (FIN1 _ _ _ _ _ _ _ _ _ _ _ _ OK1c OKo RK6 EB FHI Hn eq_refl Hbn) as (FTW' & FS' & EE). cbv zeta in EE. clear FIN0 FIN1.
      destruct FS' as (FSF' & OKfm' & EXO').
      (* [comment removed for export] *)
      refine (cps_realizes asegs _ _ T c22 (FSC Σ1 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m21 cx (est_sorted e a1' a2' ft') n lo FDO MST eq_refl eq_refl eq_refl eq_refl eq_refl TP
                ltac:(rewrite SP0E; exact ACE) AR1 AR2 FTB LV1 LV2 LVF ltac:(rewrite FRM; cbn [length app]; clear - FRMX; unfold FRAMES_MAX in *; lia) CRED ART21 MI21
                ltac:(rewrite (P_unsigned G); exact ST21) ltac:(rewrite SP0E; exact GLOW) ltac:(rewrite (P_unsigned G); exact ROOM)
                ltac:(rewrite (P_unsigned G); unfold USTACK_TOP; clear - GSPT GPUS; lia) ltac:(rewrite (P_unsigned G); exact GSPA) CX SEP IMG OK1' OK2' FTW' ltac:(clear - NB; lia) FSF') Hc22 _).
      clear Hc22. intros c23 (Σf & Hq & LVf & FRf & SPf & CRf).
      destruct (ASTA_unpack RT Σf _ _ c23 Hq) as (msf & (m22 & q0 & q1' & q2' & g0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & q3 & q4 & q5 & q6 & Ff & fcf & -> & ARTf & MIf & STf & ARRS & STEPf) & Hcf).
      clear Hq. cbv zeta in ARRS. destruct ARRS as (AR1f & AR2f & FTBf).
      rewrite (P_unsigned G) in STf, STEPf. unfold FTAB_WORDS in STEPf, FTBf. change (4 * 65537) with 262148 in STEPf.
      rewrite (ret_pc_even 0x9a37c ltac:(lia) eq_refl) in Hcf.
      destruct (after_call G Σ1 Σf _ m21 m22 SOK LVf FRf SPf PR21 STEPf ltac:(per_interval; right; cbn [outside]; lia)) as (SOKf & PRf).
      clear AR1 AR2 FTB.
      xfer_rtf G SOK STEPf m21 m22. clear STEPf.
      (* [comment removed for export] *)
      destruct (rw_cells_cutZ a0segs _ FB _ 1%nat HD) as [HD0 _]. cbn [firstn] in HD0.
      clear HD SHC3 SHCB WRF WRS BDB CSB CEB SLOB SHIB SDB ROB.
      assert (FRA : stk a0segs m22 P (P + 384)).
      { pose proof (stk_of_rw_cells a0segs _ _ _ C0) as STa. cbn [cells_size csize Nat.add] in STa. change (Z.of_nat 16) with 16 in STa.
        unfold sc0_cells in C16. unfold scl_cells in SCL. unfold sck_cells in C152. unfold scq_cells in SCQ.
        stk_eatL STa C16. stk_eatL STa SCL. stk_eatL STa C104. stk_eatL STa C152. stk_eatL STa HIC. stk_eatL STa C192. stk_eatL STa C200. stk_eatL STa SCQ.
        lazymatch type of STa with stk _ _ _ ?hi => replace hi with (P + 384) in STa by (clear; lia) end. exact STa. }
      assert (FRB : stk a0segs m22 (P + 416) (usp + -104)).
      { pose proof (stk_of_rw_cells a0segs _ _ _ C416) as STa. cbn [cells_size csize Nat.add] in STa. change (Z.of_nat 8) with 8 in STa.
        stk_eatL STa C424. stk_eatL STa C432. stk_eatL STa BUD. stk_addL STa GAP. exact STa. }
      clear C0 C416 C424 C432 GAP.
      eapply (bs_tail Σf _ _ _ SHn m22); [exact SOKf| exact OKfm'| exact EXO'| exact ASN| exact FRA| exact C384| exact FRB| exact SAV| exact EH1| exact EH2| exact AR1f| exact AR2f| exact FTBf| exact HD0
                                         | exact ARTf| exact MIf| exact STf| exact PRf| exact Hcf|].
      intros c' Σ2 m' z0 z1 z2 h0 h1 h2 h3 h4 h5 h6 h7 z3 z4 z5 z6 F' fc' Hc' FRS2 LVE2 SP2 CR2 ART' MI' ST' POST PRz.
      eapply (Hk c' Σ2 m'); [exact Hc'| exact FRS2| rewrite LVE2; exact LVf| exact SP2| rewrite CR2, CRf; clear; lia| exact ART'| exact MI'| exact ST'| | exact PRz].
      cbv zeta. rewrite EE. exact POST.
  - (* [comment removed for export] *)
    intros m8 SHn y10 y11 y12 Hn ASN C0 C216 C384 BUD EFT EPB EWF ENB EVB NMI8 MU8 WM8. apply evt_done. intros c8 Hc8.
    cbn [me_E me_A1 me_A2 me_FT me_n me_sp me_lo me_qo] in C0, C216, C384, BUD, NMI8, MU8, WM8, Hn, ASN. clear EFT EPB EWF ENB EVB.
    lazymatch type of MU8 with munch ?W _ _ => destruct (after_l1 AF G Σ1 W m7 m8 SOK ART7 MI7 ST7 PR7 NMI8 MU8 WM8 ltac:(fp_ours)) as (ART8 & MI8 & ST8 & PR8 & _) end.
    xfer_l1 m7 m8 MU8 WM8. clear NMI8 MU8 WM8.
    (* [comment removed for export] *)
    destruct (rw_cells_cutZ a0segs _ FB _ 1%nat HD) as [HD0 _]. cbn [firstn] in HD0. clear HD SHC3 SHCB WRF WRS.
    (* [comment removed for export] *)
    pose proof EH1 as EHc. unfold EHEAD1 in EHc. cutL EHc 5%nat Ea (E + 24). cutL EHc 2%nat EC (E + 40). clear Ea EHc.
    assert (SHE0 : shzW a0segs [] m8 E (E + 55768)).
    { destruct (af_acc_live RT AF Σ1 m8 E 55768 ART8 LVE) as [_ ACCE].
      apply (shzW_of_acc a0segs [] m8 E 55768 E (E + 55768) ACCE I); [clear - XEl; lia| clear - XEh ACR; lia| clear; lia| clear - ALE; Z.div_mod_to_equations; lia]. }
    eapply (l1_realizes RT AF Σ1 PMc _ T c8 MST Hc8).
    eapply (A0_bs_E4s (XE F7 fc7) Y _ (XOKF F7 fc7) (YOKF F7 fc7) m8); [exact C216| exact C384| exact EC| exact (kmem_inv_N _ _ MI8)| exact SHE0|].
    apply evt_done. clear Hc8 EC SHE0. intros c9 Hc9.
    destruct (FSM Hn) as (FSF & OKfm & EXO).
    (* [comment removed for export] *)
    refine (cps_realizes asegs _ _ T c9 (FSC Σ1 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m8 cx e n lo FDO MST eq_refl eq_refl eq_refl eq_refl eq_refl TP
              ltac:(rewrite SP0E; exact ACE) AR1 AR2 FTB LV1 LV2 LVF ltac:(rewrite FRM; cbn [length app]; clear - FRMX; unfold FRAMES_MAX in *; lia) CRED ART8 MI8
              ltac:(rewrite (P_unsigned G); exact ST8) ltac:(rewrite SP0E; exact GLOW) ltac:(rewrite (P_unsigned G); exact ROOM)
              ltac:(rewrite (P_unsigned G); unfold USTACK_TOP; clear - GSPT GPUS; lia) ltac:(rewrite (P_unsigned G); exact GSPA) CX SEP IMG EA1OK EA2OK EFTW ltac:(clear - NB; lia) FSF) Hc9 _).
    clear Hc9. intros c10 (Σf & Hq & LVf & FRf & SPf & CRf).
    destruct (ASTA_unpack RT Σf _ _ c10 Hq) as (msf & (m9 & q0 & q1' & q2' & g0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & q3 & q4 & q5 & q6 & Ff & fcf & -> & ARTf & MIf & STf & ARRS & STEPf) & Hcf).
    clear Hq. cbv zeta in ARRS. destruct ARRS as (AR1f & AR2f & FTBf).
    rewrite (P_unsigned G) in STf, STEPf. unfold FTAB_WORDS in STEPf, FTBf. change (4 * 65537) with 262148 in STEPf.
    rewrite (ret_pc_even 0x9a37c ltac:(lia) eq_refl) in Hcf.
    destruct (after_call G Σ1 Σf _ m8 m9 SOK LVf FRf SPf PR8 STEPf ltac:(per_interval; right; cbn [outside]; lia)) as (SOKf & PRf).
    clear AR1 AR2 FTB.
    xfer_rtf G SOK STEPf m8 m9. clear STEPf.
    (* [comment removed for export] *)
    assert (FRA : stk a0segs m9 P (P + 384)).
    { pose proof (stk_of_rw_cells a0segs _ _ _ C0) as STa. cbn [cells_size csize Nat.add] in STa. change (Z.of_nat 16) with 16 in STa.
      stk_eatL STa C16. stk_eatL STa C104. stk_eatL STa C152. stk_eatL STa C200. stk_eatL STa C216.
      lazymatch type of STa with stk _ _ _ ?hi => replace hi with (P + 384) in STa by lia end. exact STa. }
    assert (FRB : stk a0segs m9 (P + 416) (usp + -104)).
    { pose proof (stk_of_rw_cells a0segs _ _ _ C416) as STa. cbn [cells_size csize Nat.add] in STa. change (Z.of_nat 8) with 8 in STa.
      stk_eatL STa C424. stk_eatL STa C432. stk_eatL STa BUD. stk_addL STa GAP. exact STa. }
    clear C0 C16 C104 C152 C200 C216 C416 C424 C432 BUD GAP.
    pose proof (nm_blockSort_small e Hn) as EE. cbv zeta in EE.
    eapply (bs_tail Σf _ _ _ SHn m9); [exact SOKf| exact OKfm| exact EXO| exact ASN| exact FRA| exact C384| exact FRB| exact SAV| exact EH1| exact EH2| exact AR1f| exact AR2f| exact FTBf| exact HD0
                                       | exact ARTf| exact MIf| exact STf| exact PRf| exact Hcf|].
    intros c' Σ2 m' z0 z1 z2 h0 h1 h2 h3 h4 h5 h6 h7 z3 z4 z5 z6 F' fc' Hc' FRS2 LVE2 SP2 CR2 ART' MI' ST' POST PR'.
    eapply (Hk c' Σ2 m'); [exact Hc'| exact FRS2| rewrite LVE2; exact LVf| exact SP2| rewrite CR2, CRf; clear; lia| exact ART'| exact MI'| exact ST'| | exact PR'].
    cbv zeta. rewrite EE. exact POST.
Qed.

End Act.
End BSG.
