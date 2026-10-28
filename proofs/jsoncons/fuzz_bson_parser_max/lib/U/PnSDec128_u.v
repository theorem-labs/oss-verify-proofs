(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     AxSymExec3 PmLayout PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PnStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep PnKeep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u PnCertKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmFrame PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u
     PnTxtKit_u PnSrcSMemmove_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnDecFacts PnDecBv PnMemW. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSDec128Defs_u PnSDec128OP_u PnSDec128Rnd_u PnSDec128Rnd2_u PnSDec128Mid_u PnSDec128Out_u
     PnSDec128Ent_u PnSDec128Spc_u PnSDec128Rdx_u PnSPushBackShort_u PnSFromInt_u Bs0_code_37f10_37f14_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNSDEC.
Import PMS.
Abbreviation AN := PnLayoutS_u.NADDR_S.
Abbreviation AD := PnLayoutS_u.ADDR_S.
Local Ltac lia := PMK.alia.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Lemma sub_in (KS l : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) l = true -> forall k, In k l -> In k KS.
Proof.
  intros H k Hk. rewrite forallb_forall in H. specialize (H k Hk). apply existsb_exists in H. destruct H as (x & Hx & E). apply Nat.eqb_eq in E. subst x. exact Hx.
Qed.
Lemma to_bv_mod a : Z_to_bv 64 (a mod 2 ^ 64) = Z_to_bv 64 a.
Proof. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia. Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.

Lemma callee_ag LBc sp' scr' W' M M' : L5C.hpres L LBc sp' scr' W' M M' -> L5C.stk (hl_sptop L) M sp' scr' -> 0 <= scr' ->
  forall a, sp' <= a < 2 ^ 64 -> ~ PMK.inW W' a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Proof.
  intros HP STK S0 a Ha N. apply (L5C.hpres_kept L LBc sp' scr' W' M M' a HP).
  apply (PMKP.kept_stack RSEGS L KL LBc M sp' scr' W' a STK S0 Ha). apply PMFR.outside_of_not_inW. exact N.
Qed.
(* [comment removed for export] *)
Lemma callee_ag_block LBc sp' scr' W' M M' B n : L5C.hpres L LBc sp' scr' W' M M' -> In (B, n) LBc -> 0 <= B -> B + n <= hl_ceil L ->
  (B + n <= hl_img_lo L \/ hl_img_hi L <= B) -> hl_sptop L <= 2 ^ 47 ->
  forall a, B <= a < B + n -> ~ PMK.inW W' a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Proof.
  intros HP Hin H0 Hc Hh Hs a Ha N. apply (L5C.hpres_kept L LBc sp' scr' W' M M' a HP).
  apply (PMKP.kept_block RSEGS L KL LBc sp' scr' W' B n a Hin Ha H0 Hc Hh Hs). apply PMFR.outside_of_not_inW. exact N.
Qed.
Lemma SFN : forall iv a, In iv (PNL.pn_d128_foot AN) -> fst iv <= a < snd iv -> PMKP.cstatic L a.
Proof. intros iv a Hin H. apply (PMKS.cstatic_S L LY). cbn in Hin. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in H; lia. Qed.
(* [comment removed for export] *)
Lemma cwr_dec LB a : 0xc8580 <= a < 0xea228 -> PMK.cwr L LB a.
Proof.
  intros Ha. right. right. rewrite (ly_img_lo L LY), (ly_img_hi L LY). split; [clear -Ha; lia|]. split.
  - intros X. apply (ly_static L LY) in X. clear -Ha X; lia.
  - intros X. apply (ly_ro_foot L LY a X). clear -Ha; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model : Model) (K : TSet) (LB : list (Z * Z)) (cr : credit) (first vp S r : Z) (ax : PNST.bax).
Variables (Bb mb : Z).
Hypothesis MOK : PMSP.model_ok model.
Hypothesis K0 : K [].
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rgp0 : getr R0 (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (pa_tp AD).
Hypothesis STK0 : L5C.stk (hl_sptop L) M0 S 18432.
Hypothesis A10 : getr R0 (reg 10) = Z_to_bv 64 first.
Hypothesis A11 : getr R0 (reg 11) = Z_to_bv 64 (first + 42).
Hypothesis A12 : getr R0 (reg 12) = Z_to_bv 64 vp.
Hypothesis HBin : In (Bb, mb) LB.
Hypothesis HB1 : Bb <= first.
Hypothesis HB2 : first + 42 <= Bb + mb.
Hypothesis DEFf : L5.defined M0 first 42.
Hypothesis Hvp1 : S <= vp.
Hypothesis Hvp2 : vp + 16 <= hl_sptop L.
Hypothesis DEFv : L5.defined M0 vp 16.
Hypothesis Hvp8 : vp mod 8 = 0.
Hypothesis BASE : PMST.base_ok RSEGS AD M0.
Hypothesis BERR : PNST.berr_ok RSEGS AD AN M0 ax.
Hypothesis BRLB : PMFR.brange L LB.
Hypothesis LBhi : forall b, In b LB -> fst b + snd b <= hl_ceil L.
Hypothesis PBS : PNRS.str_push_back_short_spec L HI.
Hypothesis FI : PNRS.from_int_spec L HI.
Definition W : list L5.range := (first, 42) :: (if PNST.bax_dec ax then [] else PNST.dec_W AD AN).
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (ptr : Z),
        regs_preserved R0 R' -> getr R' 10%bv = Z_to_bv 64 ptr -> first <= ptr <= first + 42 ->
        L5.defined M' first 42 -> PNST.berr_ok RSEGS AD AN M' (PNST.bax_add_dec ax) ->
        L5C.hpres L LB S 18432 W M0 M' ->
        hi_heap HI LB cr M' (m_vmmaps model) ->
        srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model) K.

(* [comment removed for export] *)
Definition RADIX_stmt : Prop := forall (sigma e : Z) fx R M z sd,
  0 <= sigma <= 1 -> 0 <= e <= 6175 ->
  0 <= r < 2 ^ 47 -> 140735332483408 <= S <= 140737488355328 -> S mod 16 = 0 -> 4096 <= first <= 140737488355286 ->
  (first + 42 <= 65536 \/ 962560 <= first) -> first + 42 <= S - 18432 ->
  PNSDD.stQ R0 S first sigma e z sd R -> PNSDD.MI R0 S first r M -> L5.defined M (S - 216) 144 -> 0 <= z -> 1 <= sd -> z + sd <= 36 -> 6171 <= sd + e ->
  exists fx' R' M' ptr, msteps RSEGS (st fx R 0x38e44 M) (st fx' R' 0x38f6c M') /\ mem_grows M M'
    /\ PNSDD.agree_but (PNSDD.in_out first) M M' /\ PNSDD.stE R0 S ptr R' /\ first <= ptr <= first + 42 /\ PNSDD.MI R0 S first r M'.
Hypothesis RDX : RADIX_stmt.

(* [comment removed for export] *)
Lemma nfacts : 0 <= r < 2 ^ 47 /\ 140735332483408 <= S <= 140737488355328 /\ S mod 16 = 0 /\ 4096 <= first <= 140737488355286
  /\ (first + 42 <= 65536 \/ 962560 <= first) /\ first + 42 <= S - 18432 /\ 4096 <= vp <= 140737488355312 /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47
  /\ 0 <= Bb /\ (Bb + mb <= hl_img_lo L \/ hl_img_hi L <= Bb) /\ Bb + mb <= hl_ceil L.
Proof.
  pose proof RAok as (R1 & R2). pose proof STK0 as (S16 & SB & SC & SD & SW).
  pose proof (BRLB Bb mb HBin) as (Q0 & Q1 & Q2). pose proof Q1 as Q1'. rewrite (ly_img_lo L LY), (ly_img_hi L LY) in Q1'.
  unfold L5.ra_ok in *. repeat split; try lia.
Qed.

(* [comment removed for export] *)
Lemma finish fx R M ptr :
  getr R (reg 1) = Z_to_bv 64 r -> getr R (reg 2) = Z_to_bv 64 S -> getr R (reg 10) = Z_to_bv 64 ptr ->
  (forall k, In k PNSDD.CS -> getr R (reg k) = getr R0 (reg k)) -> first <= ptr <= first + 42 ->
  PMK.ek L LB S 18432 W M0 M -> PMK.dk L LB S 18432 M0 M -> L5C.stk (hl_sptop L) M S 18432 ->
  PNST.berr_ok RSEGS AD AN M (PNST.bax_add_dec ax) -> hi_heap HI LB cr M (m_vmmaps model) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x38f98 M model) K.
Proof.
  intros B1 B2 B10 CS Hptr EK DK STK ERR HH. pose proof nfacts as (Fr & FS & F16 & Ffirst & Fimg & Fdj & Fvp & Ftop & FB0 & FBh & FBc). pose proof MOK as (Mh & Ml & Mm).
  pose proof RAok as (Hr1 & Hr2).
  unfold PMSP.cfg. eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| |].
  { apply (PMK.ret_to RSEGS fx R M 0x38f98 W_37fb4 r F_37fb4 ltac:(reflexivity) D_37fb4 B1 Hr1 Hr2). }
  apply (KONT fx R M ptr).
  - apply PMK.preserved_by_index. intros i Hi. unfold PMK.cs_all in Hi.
    destruct Hi as [<-|Hi]; [rewrite B2; symmetry; exact Rsp0|]. apply CS. revert i Hi. apply sub_in. vm_compute. reflexivity.
  - rewrite L5K.rl10. exact B10.
  - exact Hptr.
  - intros i Hi. apply (DK (first + i)); [clear -Hi Ffirst; lia| | | apply DEFf; exact Hi].
    + left. exists (Bb, mb). split; [exact HBin|]. cbn. clear -Hi HB1 HB2; lia.
    + unfold in_errno. rewrite (ly_errno L LY). clear -Hi Fimg; lia.
  - exact ERR.
  - apply (PMK.hpres_of L LB S 18432 W M0 M EK); [| exact DK]. destruct STK as (_ & _ & _ & _ & D). exact D.
  - exact HH.
Qed.

(* [comment removed for export] *)
Lemma err_keep M M' (P : Z -> Prop) bx :
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> (forall a, P a -> (S - 18432 <= a < S) \/ (first <= a < first + 42)) ->
  PNST.berr_ok RSEGS AD AN M bx -> PNST.berr_ok RSEGS AD AN M' bx.
Proof.
  intros AG HP. pose proof nfacts as (Fr & FS & F16 & Ffirst & Fimg & Fdj & Fvp & Ftop & FB0 & FBh & FBc).
  apply (PNKP.berr_agree RSEGS AD AN PNRS.addrs_wf_B M M'). intros a Ha D. apply AG; [exact Ha|]. intros Pa.
  destruct (HP a Pa) as [X|X]; destruct D as [H|[H|(iv & Hin & H)]]; cbn in H; try (cbn in Hin; destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in H);
    clear -X H FS Fimg; lia.
Qed.

(* [comment removed for export] *)
Lemma mod8_256 S0 : S0 mod 16 = 0 -> (S0 - 256) mod 8 = 0.
Proof. intros H. pose proof (Z.div_mod S0 16 ltac:(clear; lia)) as E. rewrite H in E. replace (S0 - 256) with ((2 * (S0 / 16) - 32) * 8) by (clear -E; lia). apply Z_mod_mult. Qed.
(* [comment removed for export] *)
Lemma u8_of_u64_0 M a : L5.u64_at RSEGS M a 0 -> L5.u8_at RSEGS M a 0.
Proof.
  unfold L5.u64_at, L5.u8_at. intros H. rewrite (SeqExec.rdn_firstn RSEGS M 8%nat (Z_to_bv 64 a) _ 1%nat H) by lia. vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma MI_after_call Mc M2 scr' :
  L5C.hpres L LB (S - 256) scr' [(S - 256, 24)] Mc M2 -> L5C.stk (hl_sptop L) Mc (S - 256) scr' -> 0 <= scr' ->
  L5C.stk (hl_sptop L) M2 S 18432 -> L5.defined M2 first 42 -> PNSDD.MI R0 S first r Mc -> PNSDD.MI R0 S first r M2.
Proof.
  intros HP STKc Hscr STK2 DF (W1 & W2 & IC & SV). pose proof nfacts as (Fr & FS & F16 & Ffirst & Fimg & Fdj & Fvp & Ftop & FB0 & FBh & FBc).
  pose proof (callee_ag LB (S - 256) scr' [(S - 256, 24)] Mc M2 HP STKc Hscr) as AG.
  assert (NW : forall a, S - 216 <= a -> ~ PMK.inW [(S - 256, 24)] a).
  { intros a Ha (rg & [<-|[]] & Hr). unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear -Ha Hr. lia. }
  split. { apply (L5.writable_sub RSEGS M2 (S - 18432) 18432); [apply (L5C.stk_writable RSEGS _ M2 S 18432 STK2)| clear; lia| clear; lia]. }
  split. { apply (L5C.writable_of_defined RSEGS M2 first 42 DF); clear -Ffirst; lia. }
  split. { apply (PMKP.clear_agree Mc M2 65536 754672); [|exact IC]. intros i Hi. apply (L5C.hpres_kept L LB (S - 256) scr' _ Mc M2 i HP).
           apply (PMKP.kept_cstatic RSEGS L KL); [apply (PMKS.cstatic_S L LY); clear -Hi; lia|].
           apply PMFR.outside_of_not_inW. intros (rg & [<-|[]] & Hr). unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear -Hi Hr FS. lia. }
  destruct SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  repeat split; (eapply (L5C.u64_at_agree RSEGS Mc M2); [intros i Hi; apply AG; [clear -Hi FS; lia| apply NW; clear -Hi; lia]| clear -FS; lia| clear -FS; lia| eassumption]).
Qed.

(* [comment removed for export] *)
Lemma arm_done fxa Ra Ma (pca : Z) fxb Rb Mb ptr :
  hi_heap HI LB cr Ma (m_vmmaps model) -> PMK.ek L LB S 18432 W M0 Ma -> PMK.dk L LB S 18432 M0 Ma -> L5C.stk (hl_sptop L) Ma S 18432 ->
  PNST.berr_ok RSEGS AD AN Ma (PNST.bax_add_dec ax) ->
  msteps RSEGS (st fxa Ra pca Ma) (st fxb Rb 0x38f6c Mb) -> mem_grows Ma Mb -> PNSDD.agree_but (PNSDD.in_out first) Ma Mb ->
  PNSDD.stE R0 S ptr Rb -> first <= ptr <= first + 42 -> PNSDD.MI R0 S first r Mb ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fxa Ra pca Ma model) K.
Proof.
  intros HH EK DK STK ERR MS MG AG SE Hptr MIb. pose proof nfacts as (Fr & FS & F16 & Ffirst & Fimg & Fdj & Fvp & Ftop & FB0 & FBh & FBc). pose proof MOK as (Mh & Ml & Mm).
  destruct (PNSDOUT.epilogue R0 S first 0 0 r Fr ltac:(clear -FS; lia) F16 Ffirst ltac:(clear -Fdj; lia) fxb Rb Mb ptr SE MIb ltac:(clear -Hptr Ffirst; lia)) as (fxc & Rc & MSc & B1 & B2 & B10 & CS).
  unfold PMSP.cfg.
  apply (PMK.spiece RSEGS L HI KL HIok LB cr Ma model fxa fxc Ra pca Rc 0x38f98 Mb (PNSDD.in_out first) K HH Mh Ml ltac:(clear -Ftop FS Fvp; lia)
           ltac:(eapply msteps_trans; [exact MS| exact MSc]) MG AG).
  { intros a X. apply (PMK.cwr_block L LB Bb mb a HBin). unfold PNSDD.in_out in X. clear -X HB1 HB2; lia. }
  { intros a. unfold PNSDD.in_out. apply PMK.rng_dec. }
  intros HHb. apply (finish fxc Rc Mb ptr B1 B2 B10 CS Hptr).
  - apply (PMK.ek_trans L LB S 18432 W M0 Ma Mb EK). apply (PMK.ek_piece_in RSEGS L KL LB S 18432 W Ma Mb (PNSDD.in_out first) AG STK LBhi).
    intros a X. right. apply PMK.inW_here. unfold PNSDD.in_out in X. clear -X; lia.
  - apply (PMK.dk_trans L LB S 18432 M0 Ma Mb DK). apply PMK.dk_grows. exact MG.
  - apply (PMK.stk_grows L Ma Mb S 18432 MG STK).
  - apply (err_keep Ma Mb (PNSDD.in_out first) _ AG); [| exact ERR]. intros a X. right. exact X.
  - exact HHb.
Qed.

(* [comment removed for export] *)
Lemma output (sigma e : Z) (Fsig : 0 <= sigma <= 1) (Fe : 0 <= e <= 16383) (pc0 : Z) fx R M fx' R' M' (z sd d : Z) :
  hi_heap HI LB cr M (m_vmmaps model) -> PMK.ek L LB S 18432 W M0 M -> PMK.dk L LB S 18432 M0 M -> L5C.stk (hl_sptop L) M S 18432 ->
  PNST.berr_ok RSEGS AD AN M (PNST.bax_add_dec ax) ->
  msteps RSEGS (st fx R pc0 M) (st fx' R' 0x38cec M') -> mem_grows M M' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 256 <= a < S - 72) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  PNSDD.stP R0 S first sigma e z sd d R' -> PNSDD.MI R0 S first r M' -> L5.defined M' (S - 216) 144 ->
  0 <= z -> 1 <= sd -> z + sd <= 36 -> 0 <= d <= 9 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R pc0 M model) K.
Proof.
  intros HH EK DK STK ERR MS MG AG SP MI' DF Hz0 Hsd Hz Hd.
  pose proof nfacts as (Fr & FS & F16 & Ffirst & Fimg & Fdj & Fvp & Ftop & FB0 & FBh & FBc). pose proof MOK as (Mh & Ml & Mm).
  (* [comment removed for export] *)
  unfold PMSP.cfg.
  apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx' R pc0 R' 0x38cec M' (fun a => S - 256 <= a < S - 72) K HH Mh Ml ltac:(clear -Ftop FS Fvp; lia) MS MG AG).
  { intros a X. pose proof STK as (_ & _ & SCx & _ & _). apply (PMK.cwr_stack L LB M S 18432 a STK). clear -X SCx; lia. }
  { intros a. apply PMK.rng_dec. }
  intros HH'.
  assert (EK' : PMK.ek L LB S 18432 W M0 M').
  { apply (PMK.ek_trans L LB S 18432 W M0 M M' EK). apply (PMK.ek_piece_in RSEGS L KL LB S 18432 W M M' _ AG STK LBhi). intros a X. left. clear -X; lia. }
  assert (DK' : PMK.dk L LB S 18432 M0 M') by (apply (PMK.dk_trans L LB S 18432 M0 M M' DK); apply PMK.dk_grows; exact MG).
  assert (STK' : L5C.stk (hl_sptop L) M' S 18432) by (apply (PMK.stk_grows L M M' S 18432 MG STK)).
  assert (ERR' : PNST.berr_ok RSEGS AD AN M' (PNST.bax_add_dec ax)).
  { apply (err_keep M M' (fun a => S - 256 <= a < S - 72) _ AG); [| exact ERR]. intros a X. left. clear -X; lia. }
  clear HH EK DK STK ERR MS MG AG fx R M.
  (* [comment removed for export] *)
  destruct (PNSDOUT.fork R0 S first sigma e r Fr ltac:(clear -FS; lia) F16 Ffirst ltac:(clear -Fdj; lia) Fe Fsig z sd d fx' R' M' SP MI' Hz0 Hsd Hz Hd)
    as (fx1 & R1 & [(MS1 & RB1 & O10 & O11 & O12 & O13 & O14 & O15 & O19 & Hsci) | [(MS1 & SQ1 & He1 & Hsci) | (MS1 & SQ1 & G18 & He1)]]).
  - (* [comment removed for export] *)
    set (sci := e + sd - 6177) in *.
    assert (Hsci64 : - 2 ^ 62 <= sci < 2 ^ 62) by (subst sci; clear -Fe Hsd Hz Hz0; lia).
    pose proof (Z.mod_pos_bound sci (2 ^ 64) ltac:(clear; lia)) as Hsw.
    destruct (PNSDOUT.sci_front R0 S first sigma e r Fr ltac:(clear -FS; lia) F16 Ffirst ltac:(clear -Fdj; lia) Fe Fsig Fimg z sd d (sci mod 2 ^ 64) fx1 R1 M' RB1 O10 O11 O12 O13 O14 O15
                ltac:(rewrite PNSDOUT.to_bv_mod; exact O19) Hsw MI' DF Hz0 Hsd Hz Hd)
      as (fx2 & R2 & M2 & p & MS2 & MG2 & AG2 & RL2 & B21 & B19 & B9 & Hp & MI2).
    rewrite PNSDOUT.to_bv_mod in B19.
    destruct (PNSDOUT.sci_e R0 S first sigma e r Fr ltac:(clear -FS; lia) F16 Ffirst ltac:(clear -Fdj; lia) Fe Fsig Fimg sci p fx2 R2 M2 RL2 B21 B19 B9 Hsci64 Hp MI2)
      as (fx3 & R3 & M3 & MG3 & AG3 & MI3 & RL3 & C19 & C9 & C21 & Z240 & Z232 & Z224 & ARM).
    (* [comment removed for export] *)
    set (P3 := fun a => PNSDD.in_out first a \/ (S - 256 <= a < S - 216)).
    assert (AG23 : forall a, 0 <= a < 2 ^ 64 -> ~ P3 a -> M3 (Z_to_bv 64 a) = M' (Z_to_bv 64 a)).
    { intros a Ha N. unfold P3, PNSDD.in_out in N. rewrite (AG3 a Ha) by (clear -N Hp Fsig; lia). apply (AG2 a Ha). unfold PNSDD.in_out. clear -N; lia. }
    assert (MG23 : mem_grows M' M3) by (intros a Ha; apply MG3; apply MG2; exact Ha).
    assert (CW3 : forall a, P3 a -> PMK.cwr L LB a).
    { intros a [X|X]; [apply (PMK.cwr_block L LB Bb mb a HBin); unfold PNSDD.in_out in X; clear -X HB1 HB2; lia| pose proof STK' as (_ & _ & SCx & _ & _); apply (PMK.cwr_stack L LB M' S 18432 a STK'); clear -X SCx; lia]. }
    assert (DEC3 : forall a, {P3 a} + {~ P3 a}) by (intros a; unfold P3, PNSDD.in_out; apply PMK.or_dec; apply PMK.rng_dec).
    assert (EK3 : PMK.ek L LB S 18432 W M0 M3).
    { apply (PMK.ek_trans L LB S 18432 W M0 M' M3 EK'). apply (PMK.ek_piece_in RSEGS L KL LB S 18432 W M' M3 P3 AG23 STK' LBhi).
      intros a [X|X]; [right; apply PMK.inW_here; unfold PNSDD.in_out in X; clear -X; lia| left; clear -X; lia]. }
    assert (DK3 : PMK.dk L LB S 18432 M0 M3) by (apply (PMK.dk_trans L LB S 18432 M0 M' M3 DK'); apply PMK.dk_grows; exact MG23).
    assert (STK3 : L5C.stk (hl_sptop L) M3 S 18432) by (apply (PMK.stk_grows L M' M3 S 18432 MG23 STK')).
    assert (ERR3 : PNST.berr_ok RSEGS AD AN M3 (PNST.bax_add_dec ax)).
    { apply (err_keep M' M3 P3 _ AG23); [| exact ERR']. intros a [X|X]; [right; exact X| left; clear -X; lia]. }
    assert (DF3 : L5.defined M3 first 42).
    { intros i Hi. apply (DK3 (first + i)); [clear -Hi Ffirst; lia| | | apply DEFf; exact Hi].
      - left. exists (Bb, mb). split; [exact HBin|]. cbn. clear -Hi HB1 HB2; lia.
      - unfold in_errno. rewrite (ly_errno L LY). clear -Hi Fimg; lia. }
    assert (STKc3 : L5C.stk (hl_sptop L) M3 (S - 256) 16384) by (apply (PMK.stk_call L M3 S 18432 (S - 256) 16384 STK3); [clear; lia| clear; lia| clear; lia| clear -F16; clear -F16; pose proof (Z.div_mod S 16 ltac:(lia)) as E; rewrite F16 in E; replace (S - 256) with ((S / 16 - 16) * 16) by lia; apply Z_mod_mult]).
    assert (VS3 : PM.vstr_at RSEGS PMSP.T3 M3 (S - 256) (PM.VShort 0)).
    { split; [| split; [exact I| split; [clear; lia| apply u8_of_u64_0; exact Z240]]].
      destruct STK3 as (_ & _ & _ & _ & D). apply (L5.defined_sub M3 (S - 18432) 18432); [exact D| clear; lia| clear; lia]. }
    (* [comment removed for export] *)
    assert (AFTER : forall M4 M6 scr', L5C.hpres L LB (S - 256) scr' [(S - 256, 24)] M4 M6 -> 0 <= scr' -> scr' <= 16384 ->
              PMK.ek L LB S 18432 W M0 M4 -> PMK.dk L LB S 18432 M0 M4 -> L5C.stk (hl_sptop L) M4 S 18432 ->
              PNST.berr_ok RSEGS AD AN M4 (PNST.bax_add_dec ax) -> PNSDD.MI R0 S first r M4 ->
              PMK.ek L LB S 18432 W M0 M6 /\ PMK.dk L LB S 18432 M0 M6 /\ L5C.stk (hl_sptop L) M6 S 18432
              /\ PNST.berr_ok RSEGS AD AN M6 (PNST.bax_add_dec ax) /\ PNSDD.MI R0 S first r M6 /\ L5.defined M6 first 42).
    { intros M4 M6 scr' HP Hs0 Hs1 EK4 DK4 STK4 ERR4 MI4.
      assert (STKc4 : L5C.stk (hl_sptop L) M4 (S - 256) scr') by (apply (PMK.stk_call L M4 S 18432 (S - 256) scr' STK4); [clear; lia| clear -Hs1; lia| exact Hs0| clear -F16; pose proof (Z.div_mod S 16 ltac:(lia)) as E; rewrite F16 in E; replace (S - 256) with ((S / 16 - 16) * 16) by lia; apply Z_mod_mult]).
      assert (STK6 : L5C.stk (hl_sptop L) M6 S 18432) by (apply (PMK.stk_after RSEGS L KL LB M4 M6 S 18432 (S - 256) scr' _ STK4 HP); clear -Hs0 Hs1; lia).
      assert (EK46 : forall Wx, PMK.ek L LB S 18432 Wx M4 M6).
      { intros Wx. apply (PMK.ek_callee_in RSEGS L KL LB LB S 18432 (S - 256) scr' Wx [(S - 256, 24)] M4 M4 M6 HP (incl_refl _)); [clear -Hs1; lia| clear; lia| exact STK4| exact LBhi|].
        intros a (rg & [<-|[]] & Hr). left. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear -Hr; lia. }
      assert (DK6 : PMK.dk L LB S 18432 M0 M6).
      { apply (PMK.dk_trans L LB S 18432 M0 M4 M6 DK4). apply (PMK.dk_callee L LB LB S 18432 (S - 256) scr' _ M4 M6 HP (incl_refl _)); clear -Hs1; lia. }
      assert (DF6 : L5.defined M6 first 42).
      { intros i Hi. apply (DK6 (first + i)); [clear -Hi Ffirst; lia| | | apply DEFf; exact Hi].
        - left. exists (Bb, mb). split; [exact HBin|]. cbn. clear -Hi HB1 HB2; lia.
        - unfold in_errno. rewrite (ly_errno L LY). clear -Hi Fimg; lia. }
      split; [exact (PMK.ek_trans L LB S 18432 W M0 M4 M6 EK4 (EK46 W))|]. split; [exact DK6|]. split; [exact STK6|].
      split. { apply (PNKP.berr_ok_keep RSEGS AD AN L KL SF PNRS.addrs_wf_B SFN LB S 18432 [] M4 M6 _ (EK46 [])); [| exact ERR4]. intros a _ rg [] _. }
      split; [exact (MI_after_call M4 M6 scr' HP STKc4 Hs0 STK6 DF6 MI4)| exact DF6]. }
    (* [comment removed for export] *)
    assert (FROM : forall fx4 R4 M4 n0, hi_heap HI LB cr M4 (m_vmmaps model) -> PMK.ek L LB S 18432 W M0 M4 -> PMK.dk L LB S 18432 M0 M4 ->
              L5C.stk (hl_sptop L) M4 S 18432 -> PNST.berr_ok RSEGS AD AN M4 (PNST.bax_add_dec ax) -> PNSDD.MI R0 S first r M4 ->
              PNSDOUT.RL R0 S first sigma R4 -> getr R4 (reg 20) = Z_to_bv 64 (first + p) -> getr R4 (reg 19) = Z_to_bv 64 sci -> getr R4 (reg 18) = Z_to_bv 64 first ->
              PM.vstr_at RSEGS PMSP.T3 M4 (S - 256) (PM.VShort n0) -> 0 <= n0 <= 1 ->
              srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx4 R4 0x38ed8 M4 model) K).
    { intros fx4 R4 M4 n0 HH4 EK4 DK4 STK4 ERR4 MI4 RL4 D21 D19 D9 VS4 Hn0.
      destruct (PNSDOUT.sci_fi R0 S first sigma e r Fr ltac:(clear -FS; lia) F16 Ffirst ltac:(clear -Fdj; lia) Fe Fsig sci p fx4 R4 M4 RL4 D21 D19 D9 Hp MI4)
        as (fx5 & R5 & MS5 & RL5 & E19 & E9 & E21 & E1 & E10 & E11).
      unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx4 fx5 R4 0x38ed8 R5 0x39a24 M4 K Mh Ml MS5).
      assert (STKc4 : L5C.stk (hl_sptop L) M4 (S - 256) 16384) by (apply (PMK.stk_call L M4 S 18432 (S - 256) 16384 STK4); [clear; lia| clear; lia| clear; lia| clear -F16; pose proof (Z.div_mod S 16 ltac:(lia)) as E; rewrite F16 in E; replace (S - 256) with ((S / 16 - 16) * 16) by lia; apply Z_mod_mult]).
      destruct RL5 as (E2 & E3 & E4 & E8 & E18 & E24 & E25 & E26 & E27).
      pose proof FI as FI'. unfold PNRS.from_int_spec, PNR.from_int_spec in FI'. cbn [PNL.pn_from_int PnLayoutS_u.NADDR_S] in FI'.
      apply (FI' fx5 R5 M4 model K LB cr (S - 256) sci (S - 256) 0x38ee4 n0 HH4 MOK K0); clear FI'.
      { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact E1|]. split; [clear; unfold L5.ra_ok; lia|].
        split; [exact E2|]. split; [rewrite E3; exact Rgp0|]. split; [rewrite E4; exact Rtp0|]. exact STKc4. }
      { rewrite L5K.rl10. exact E10. } { subst sci; clear -Fe Hsd Hz Hz0; lia. } { rewrite L5K.rl11. exact E11. } { clear; lia. } { pose proof STK4 as (_ & _ & SC4 & _ & _); clear -SC4; lia. }
      { apply mod8_256. exact F16. }
      { exact VS4. } { clear -Hn0; lia. }
      intros fx6 R6 M6 n' RP6 VS6 Hn' HP6 HH6. change (PMSP.pm_scr 2) with 16384 in HP6.
      destruct (AFTER M4 M6 16384 HP6 ltac:(clear; lia) ltac:(clear; lia) EK4 DK4 STK4 ERR4 MI4) as (EK6 & DK6 & STK6 & ERR6 & MI6 & DF6).
      assert (R56 : forall i, In i PMK.cs_all -> getr R6 (reg i) = getr R5 (reg i)) by (intros i Hi; apply (PMK.cs_of_preserved R5 R6 i RP6 Hi)).
      assert (RL6 : PNSDOUT.RL R0 S first sigma R6).
      { unfold PNSDOUT.RL. rewrite (R56 2%nat), (R56 3%nat), (R56 4%nat), (R56 8%nat), (R56 9%nat), (R56 24%nat), (R56 25%nat), (R56 26%nat), (R56 27%nat) by PMK.inl.
        repeat split; assumption. }
      assert (U6 : L5.u8_at RSEGS M6 (S - 256) (2 * n')) by (destruct VS6 as (_ & _ & _ & U); exact U).
      destruct (PNSDOUT.sci_cp R0 S first sigma e r Fr ltac:(clear -FS; lia) F16 Ffirst ltac:(clear -Fdj; lia) Fe Fsig p n' fx6 R6 M6 RL6
                  ltac:(rewrite (R56 20%nat) by PMK.inl; exact E21) ltac:(rewrite (R56 18%nat) by PMK.inl; exact E9) Hp ltac:(clear -Hn' Hn0; lia) U6 MI6)
        as (fx7 & R7 & [(Hroom & MS7 & RL7 & G1 & G9 & G10 & G11 & G12 & G18 & G19 & G20 & G21) | (Hnoroom & MS7 & SE7)]).
      - (* [comment removed for export] *)
        pose proof MI6 as (WRf6 & WF6 & IC6 & SV6).
        assert (DS6 : L5.defined M6 (S - 255) n') by (destruct VS6 as (D & _); apply (L5.defined_sub M6 (S - 256) 24); [exact D| clear; lia| clear -Hn' Hn0; lia]).
        assert (WD6 : L5.writable RSEGS M6 (first + p + 1) n') by (apply (L5.writable_sub RSEGS M6 first 42 _ _ WF6); clear -Hp Hroom Fsig Hn' Hn0; lia).
        destruct (PMCP.copy_run RSEGS 0xab480 PMCPS.memcpy_copy1 fx7 R7 M6 (first + p + 1) (S - 255) n' 0x38f28 G10 G11 G12 G1 ltac:(split; [clear; lia| reflexivity])
                    ltac:(clear -Hn' Hn0; lia) ltac:(clear -Ffirst Hp Fsig; lia) ltac:(clear -Ffirst Hp Hroom Fsig Hn'; lia) ltac:(clear -FS; lia) ltac:(clear -FS Hn' Hn0; lia)
                    ltac:(left; clear -Fdj Hp Hroom Hn' Fsig; lia) WD6 DS6)
          as (R8 & M8 & MS8 & MG8 & AG8 & DF8 & CS8 & _).
        assert (RL8 : PNSDOUT.RL_ R0 S first R8).
        { destruct RL7 as (Q2 & Q3 & Q4 & Q8 & Q24 & Q25 & Q26 & Q27). unfold PNSDOUT.RL_.
          rewrite (CS8 2%nat), (CS8 3%nat), (CS8 4%nat), (CS8 8%nat), (CS8 24%nat), (CS8 25%nat), (CS8 26%nat), (CS8 27%nat) by PMK.inl. repeat split; assumption. }
        assert (MI8 : PNSDD.MI R0 S first r M8).
        { apply (PNSDOUT.MI_out R0 S first r ltac:(clear -FS; lia) ltac:(clear -Fdj; lia) Fimg M6 M8 MI6 MG8). intros a Ha N. apply (AG8 a Ha). unfold PNSDD.in_out in N. clear -N Hp Hroom Fsig Hn' Hn0; lia. }
        destruct (PNSDOUT.sci_tail R0 S first sigma e r Fr ltac:(clear -FS; lia) F16 Ffirst ltac:(clear -Fdj; lia) Fe Fsig p n' fx7 R8 M8 RL8
                    ltac:(rewrite (CS8 9%nat) by PMK.inl; exact G9) ltac:(rewrite (CS8 18%nat) by PMK.inl; exact G18) ltac:(rewrite (CS8 19%nat) by PMK.inl; exact G19)
                    ltac:(rewrite (CS8 20%nat) by PMK.inl; exact G20) ltac:(rewrite (CS8 21%nat) by PMK.inl; exact G21) Hp ltac:(clear -Hn' Hn0; lia) MI8)
          as (fx9 & R9 & MS9 & SE9).
        apply (arm_done fx6 R6 M6 0x38ee4 fx9 R9 M8 (first + p + 1 + n') HH6 EK6 DK6 STK6 ERR6); [| exact MG8| | exact SE9| clear -Hp Hroom Fsig Hn' Hn0; lia| exact MI8].
        + eapply msteps_trans; [exact MS7| eapply msteps_trans; [exact MS8| exact MS9]].
        + intros a Ha N. apply (AG8 a Ha). unfold PNSDD.in_out in N. clear -N Hp Hroom Fsig Hn' Hn0; lia.
      - (* [comment removed for export] *)
        apply (arm_done fx6 R6 M6 0x38ee4 fx7 R7 M6 (first + p + 1) HH6 EK6 DK6 STK6 ERR6 MS7); [intros a Ha; exact Ha| intros a _ _; reflexivity| exact SE7| clear -Hp Fsig; lia| exact MI6]. }
    destruct ARM as [(Hneg & MS3) | (Hpos & MS3 & Q1 & Q10 & Q11)].
    + (* [comment removed for export] *)
      apply (PMK.spiece RSEGS L HI KL HIok LB cr M' model fx' fx3 R' 0x38cec R3 0x38ed8 M3 P3 K HH' Mh Ml ltac:(clear -Ftop FS Fvp; lia)
               ltac:(eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MS2| exact MS3]]) MG23 AG23 CW3 DEC3).
      intros HH3. apply (FROM fx3 R3 M3 0 HH3 EK3 DK3 STK3 ERR3 MI3 RL3 C21 C19 C9 VS3). clear; lia.
    + (* [comment removed for export] *)
      apply (PMK.spiece RSEGS L HI KL HIok LB cr M' model fx' fx3 R' 0x38cec R3 0x58938 M3 P3 K HH' Mh Ml ltac:(clear -Ftop FS Fvp; lia)
               ltac:(eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MS2| exact MS3]]) MG23 AG23 CW3 DEC3).
      intros HH3.
      assert (STKc3' : L5C.stk (hl_sptop L) M3 (S - 256) 14336) by (apply (PMK.stk_call L M3 S 18432 (S - 256) 14336 STK3); [clear; lia| clear; lia| clear; lia| clear -F16; pose proof (Z.div_mod S 16 ltac:(lia)) as E; rewrite F16 in E; replace (S - 256) with ((S / 16 - 16) * 16) by lia; apply Z_mod_mult]).
      destruct RL3 as (E2 & E3 & E4 & E8 & E18 & E24 & E25 & E26 & E27).
      pose proof PBS as PB'. unfold PNRS.str_push_back_short_spec, PNR.str_push_back_short_spec in PB'. cbn [PNL.pn_str_push_back PnLayoutS_u.NADDR_S] in PB'.
      apply (PB' fx3 R3 M3 model K LB cr (S - 256) (S - 256) 0x38ed8 0 HH3 MOK K0); clear PB'.
      { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact Q1|]. split; [clear; unfold L5.ra_ok; lia|].
        split; [exact E2|]. split; [rewrite E3; exact Rgp0|]. split; [rewrite E4; exact Rtp0|]. exact STKc3'. }
      { rewrite L5K.rl10. exact Q10. } { clear; lia. } { pose proof STK3 as (_ & _ & SC3 & _ & _); clear -SC3; lia. } { apply mod8_256. exact F16. } { exact VS3. } { clear; lia. }
      intros fx4 R4 M4 RP4 VS4 HP4 HH4. change (PMSP.pm_scr 1) with 14336 in HP4.
      destruct (AFTER M3 M4 14336 HP4 ltac:(clear; lia) ltac:(clear; lia) EK3 DK3 STK3 ERR3 MI3) as (EK4 & DK4 & STK4 & ERR4 & MI4 & DF4).
      assert (R34 : forall i, In i PMK.cs_all -> getr R4 (reg i) = getr R3 (reg i)) by (intros i Hi; apply (PMK.cs_of_preserved R3 R4 i RP4 Hi)).
      apply (FROM fx4 R4 M4 1 HH4 EK4 DK4 STK4 ERR4 MI4); [| rewrite (R34 20%nat) by PMK.inl; exact C21| rewrite (R34 19%nat) by PMK.inl; exact C19| rewrite (R34 18%nat) by PMK.inl; exact C9| replace (0 + 1) with 1 in VS4 by reflexivity; exact VS4| clear; lia].
      unfold PNSDOUT.RL. rewrite (R34 2%nat), (R34 3%nat), (R34 4%nat), (R34 8%nat), (R34 9%nat), (R34 24%nat), (R34 25%nat), (R34 26%nat), (R34 27%nat) by PMK.inl.
      repeat split; assumption.
  - (* [comment removed for export] *)
    destruct (RDX sigma e fx1 R1 M' z sd Fsig ltac:(clear -Fe He1; lia) Fr FS F16 Ffirst Fimg Fdj SQ1 MI' DF Hz0 Hsd Hz ltac:(clear -Hsci; lia)) as (fxb & Rb & Mb & ptr & MSb & MGb & AGb & SEb & Hptr & MIb).
    apply (arm_done fx' R' M' 0x38cec fxb Rb Mb ptr HH' EK' DK' STK' ERR' ltac:(eapply msteps_trans; [exact MS1| exact MSb]) MGb AGb SEb Hptr MIb).
  - (* [comment removed for export] *)
    destruct (PNSDOUT.regular R0 S first sigma e r Fr ltac:(clear -FS; lia) F16 Ffirst ltac:(clear -Fdj; lia) Fe Fsig Fimg z sd fx1 R1 M' SQ1 G18 MI' DF Hz0 Hsd Hz)
      as (fxb & Rb & Mb & cnt & MSb & MGb & AGb & SEb & Hcnt & Hsc & MIb).
    apply (arm_done fx' R' M' 0x38cec fxb Rb Mb (first + sigma + cnt) HH' EK' DK' STK' ERR' ltac:(eapply msteps_trans; [exact MS1| exact MSb]) MGb AGb SEb ltac:(clear -Hcnt Hsc Fsig; lia) MIb).
Qed.

Theorem call (fx : FPState) : hi_heap HI LB cr M0 (m_vmmaps model) -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R0 0x38a78 M0 model) K.
Proof.
  intros HH0. pose proof nfacts as (Fr & FS & F16 & Ffirst & Fimg & Fdj & Fvp & Ftop & FB0 & FBh & FBc). pose proof MOK as (Mh & Ml & Mm).
  pose proof STK0 as (S16 & SB & SC & SD & SW).
  assert (WR0 : L5.writable RSEGS M0 (S - 336) 336).
  { apply (L5.writable_sub RSEGS M0 (S - 18432) 18432); [apply (L5C.stk_writable RSEGS _ M0 S 18432 STK0)| clear; lia| clear; lia]. }
  assert (WRF : L5.writable RSEGS M0 first 42) by (apply (L5C.writable_of_defined RSEGS M0 first 42 DEFf); clear -Ffirst; lia).
  destruct (PMTK.u64_of_defined RSEGS M0 vp ltac:(clear -Fvp; lia) ltac:(clear -Fvp; lia) ltac:(apply (L5.defined_sub M0 vp 16 vp 8 DEFv); clear; lia)) as (lo & Flo & VLO).
  destruct (PMTK.u64_of_defined RSEGS M0 (vp + 8) ltac:(clear -Fvp; lia) ltac:(clear -Fvp; lia) ltac:(apply (L5.defined_sub M0 vp 16 (vp + 8) 8 DEFv); clear; lia)) as (hi & Fhi & VHI).
  (* [comment removed for export] *)
  destruct (PNSDENT.entry R0 S first vp hi lo r ax A10 A11 A12 Rsp0 Rra0 Fr FS F16 Ffirst Fimg ltac:(clear -Fdj; lia) Fvp Hvp8 Hvp1 ltac:(clear -Fdj Hvp1; lia) Fhi Flo fx M0
              WR0 WRF (conj VLO VHI) BASE BERR)
    as (fx1 & R1 & M1 & sigma & MG1 & MS1 & SJ1 & CS1 & MI1 & (ZR1 & DF1) & VP1 & BASE1 & ERR1 & Fsig & Hsg & AG1).
  set (P1 := fun a => S - 336 <= a < S \/ (first <= a < first + 1) \/ (PNST.bax_dec ax = false /\ PMK.inW (PNST.dec_W AD AN) a)).
  change (PNSDD.agree_but P1 M0 M1) in AG1.
  assert (CW1 : forall a, P1 a -> PMK.cwr L LB a).
  { intros a [X|[X|(_ & X)]].
    - apply (PMK.cwr_stack L LB M0 S 18432 a STK0). clear -X SC; lia.
    - apply (PMK.cwr_block L LB Bb mb a HBin). clear -X HB1 HB2; lia.
    - apply cwr_dec. destruct X as (rg & Hin & Hr). cbn in Hin. destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear -Hr; lia. }
  assert (DEC1 : forall a, {P1 a} + {~ P1 a}).
  { intros a. unfold P1. apply PMK.or_dec; [apply PMK.rng_dec|]. apply PMK.or_dec; [apply PMK.rng_dec|].
    destruct (PNST.bax_dec ax); [right; intros (X & _); discriminate X|].
    assert (ID : forall lo n, {lo <= a < lo + n} + {~ (lo <= a < lo + n)}) by (intros; apply PMK.rng_dec).
    destruct (ID 820640 8) as [Y|N1]; [left; split; [reflexivity|]; exists (820640, 8); split; [cbn; auto| exact Y]|].
    destruct (ID 820672 8) as [Y|N2]; [left; split; [reflexivity|]; exists (820672, 8); split; [cbn; auto| exact Y]|].
    destruct (ID 820616 24) as [Y|N3]; [left; split; [reflexivity|]; exists (820616, 24); split; [cbn; auto 6| exact Y]|].
    destruct (ID 820648 24) as [Y|N4]; [left; split; [reflexivity|]; exists (820648, 24); split; [cbn; auto 6| exact Y]|].
    destruct (ID 958472 544) as [Y|N5]; [left; split; [reflexivity|]; exists (958472, 544); split; [cbn; auto 8| exact Y]|].
    right. intros (_ & rg & Hin & Hr). cbn in Hin. unfold L5.in_rng in Hr.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hr; [apply N1| apply N2| apply N3| apply N4| apply N5]; exact Hr. }
  unfold PMSP.cfg. apply (PMK.spiece RSEGS L HI KL HIok LB cr M0 model fx fx1 R0 0x38a78 R1 0x38afc M1 P1 K HH0 Mh Ml ltac:(clear -SD; lia) MS1 MG1 AG1 CW1 DEC1).
  intros HH1.
  assert (EK1 : PMK.ek L LB S 18432 W M0 M1).
  { apply (PMK.ek_piece_in RSEGS L KL LB S 18432 W M0 M1 P1 AG1 STK0 LBhi). intros a [X|[X|(E & X)]].
    - left. clear -X; lia.
    - right. apply PMK.inW_here. clear -X; lia.
    - right. unfold W. rewrite E. apply PMK.inW_next. exact X. }
  assert (DK1 : PMK.dk L LB S 18432 M0 M1) by (apply PMK.dk_grows; exact MG1).
  assert (STK1 : L5C.stk (hl_sptop L) M1 S 18432) by (apply (PMK.stk_grows L M0 M1 S 18432 MG1 STK0)).
  (* [comment removed for export] *)
  destruct (PNSDMID.middle R0 S first sigma r vp hi lo Fr ltac:(clear -FS; lia) F16 Ffirst ltac:(clear -Fdj; lia) Fsig Fvp Hvp8 ltac:(clear -Hvp1; lia)
              ltac:(clear -Fdj Hvp1; lia) Fhi Flo fx1 R1 M1 SJ1 MI1 ZR1 VP1)
    as [(fx2 & R2 & M2 & MG2 & AG2 & MI2 & MS2 & SX2 & HSP) | (fx2 & R2 & M2 & MG2 & AG2 & MI2 & e & z & sd & d & MS2 & SP2 & Fe & Hz0 & Hsd & Hzsd & Hd & SDG)].
  - (* [comment removed for export] *)
    apply (PMK.spiece RSEGS L HI KL HIok LB cr M1 model fx1 fx2 R1 0x38afc R2 0x39080 M2 (fun a => S - 232 <= a < S - 216) K HH1 Mh Ml ltac:(clear -Ftop FS Fvp; lia) MS2 MG2 AG2).
    { intros a X. apply (PMK.cwr_stack L LB M1 S 18432 a STK1). clear -X SC; lia. }
    { intros a. apply PMK.rng_dec. }
    intros HH2.
    assert (EK2 : PMK.ek L LB S 18432 W M0 M2).
    { apply (PMK.ek_trans L LB S 18432 W M0 M1 M2 EK1). apply (PMK.ek_piece_in RSEGS L KL LB S 18432 W M1 M2 _ AG2 STK1 LBhi). intros a X. left. clear -X; lia. }
    assert (DK2 : PMK.dk L LB S 18432 M0 M2) by (apply (PMK.dk_trans L LB S 18432 M0 M1 M2 DK1); apply PMK.dk_grows; exact MG2).
    assert (STK2 : L5C.stk (hl_sptop L) M2 S 18432) by (apply (PMK.stk_grows L M1 M2 S 18432 MG2 STK1)).
    assert (ERR2 : PNST.berr_ok RSEGS AD AN M2 (PNST.bax_add_dec ax)).
    { apply (err_keep M1 M2 (fun a => S - 232 <= a < S - 216) _ AG2); [| exact ERR1]. intros a X. left. clear -X; lia. }
    assert (DF2 : L5.defined M2 (S - 216) 144) by exact (L5.defined_grows M1 M2 _ _ MG2 DF1).
    assert (ZR2 : PNSDD.zers S M2 4).
    { intros i Hi. apply (PNSDD.cell_xfer S ltac:(clear -FS; lia) M1 M2 (fun a => S - 232 <= a < S - 216) i 0 AG2); [intros a Ha; clear -Ha Hi; lia| clear -Hi; lia| exact (ZR1 i Hi)]. }
    assert (DEC' : PNST.bdec_ok RSEGS AN M2 true).
    { destruct ERR2 as (_ & D & _). rewrite PNST.bax_dec_add in D. exact D. }
    destruct (PNSDSPC.special R0 S first sigma vp hi lo r ltac:(clear -FS; lia) F16 Ffirst Fimg ltac:(clear -Fdj; lia) Fsig Fhi Flo Fvp Fr RAok fx2 R2 M2 SX2 MI2 HSP DEC')
      as (fx3 & R3 & M3 & MG3 & [(MS3 & (ptr & SR3 & Hptr) & MI3 & _ & AG3) | [(MS3 & SN3 & CN3 & MI3 & _ & AG3) | (MS3 & SH3 & X10 & CN3 & MI3 & _ & AG3)]]).
    + (* [comment removed for export] *)
      set (P3 := fun a => PNSDD.in_frame S a \/ PNSDD.in_out first a). change (PNSDD.agree_but P3 M2 M3) in AG3.
      assert (CW3 : forall a, P3 a -> PMK.cwr L LB a).
      { intros a [X|X]; [apply (PMK.cwr_stack L LB M2 S 18432 a STK2); unfold PNSDD.in_frame in X; clear -X SC; lia| apply (PMK.cwr_block L LB Bb mb a HBin); unfold PNSDD.in_out in X; clear -X HB1 HB2; lia]. }
      assert (DEC3 : forall a, {P3 a} + {~ P3 a}) by (intros a; unfold P3, PNSDD.in_frame, PNSDD.in_out; apply PMK.or_dec; apply PMK.rng_dec).
      destruct SR3 as (B2 & B10 & CS3).
      eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| exact MS3|].
      pose proof (PMK.hi_heap_stretch RSEGS L HI KL HIok LB cr M2 M3 _ HH2 ltac:(clear -SD; lia) ltac:(intros a Ha; destruct (DEC3 a) as [Y|N]; [right; apply CW3; exact Y| left; apply AG3; assumption]) MG3) as HH3.
      change (srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 r M3 model) K).
      apply (KONT fx3 R3 M3 ptr).
      * apply PMK.preserved_by_index. intros i Hi. unfold PMK.cs_all in Hi.
        destruct Hi as [<-|Hi]; [rewrite B2; symmetry; exact Rsp0|]. apply CS3. revert i Hi. apply sub_in. vm_compute. reflexivity.
      * rewrite L5K.rl10. exact B10.
      * exact Hptr.
      * assert (DK3 : PMK.dk L LB S 18432 M0 M3) by (apply (PMK.dk_trans L LB S 18432 M0 M2 M3 DK2); apply PMK.dk_grows; exact MG3).
        intros i Hi. apply (DK3 (first + i)); [clear -Hi Ffirst; lia| | | apply DEFf; exact Hi].
        -- left. exists (Bb, mb). split; [exact HBin|]. cbn. clear -Hi HB1 HB2; lia.
        -- unfold in_errno. rewrite (ly_errno L LY). clear -Hi Fimg; lia.
      * apply (err_keep M2 M3 P3 _ AG3); [| exact ERR2]. intros a [X|X]; [left; unfold PNSDD.in_frame in X; clear -X; lia| right; exact X].
      * apply (PMK.hpres_of L LB S 18432 W M0 M3).
        -- apply (PMK.ek_trans L LB S 18432 W M0 M2 M3 EK2). apply (PMK.ek_piece_in RSEGS L KL LB S 18432 W M2 M3 P3 AG3 STK2 LBhi).
           intros a [X|X]; [left; unfold PNSDD.in_frame in X; clear -X; lia| right; apply PMK.inW_here; unfold PNSDD.in_out in X; clear -X; lia].
        -- pose proof (PMK.stk_grows L M2 M3 S 18432 MG3 STK2) as (_ & _ & _ & _ & D). exact D.
        -- apply (PMK.dk_trans L LB S 18432 M0 M2 M3 DK2). apply PMK.dk_grows. exact MG3.
      * exact HH3.
    + (* [comment removed for export] *)
      destruct (PNSDMID.from_nz R0 S first sigma r vp hi lo Fr ltac:(clear -FS; lia) F16 Ffirst ltac:(clear -Fdj; lia) Fsig Fhi Flo fx3 R3 M3 SN3 MI3)
        as (fx4 & R4 & M4 & MG4 & AG4 & MI4 & e' & z & sd & d & MS4 & SP4 & Fe' & Hz0 & Hsd & Hzsd & Hd & SDG).
      assert (MG14 : mem_grows M2 M4) by (intros a Ha; apply MG4; apply MG3; exact Ha).
      apply (output sigma e' Fsig Fe' 0x39080 fx2 R2 M2 fx4 R4 M4 z sd d HH2 EK2 DK2 STK2 ERR2 ltac:(eapply msteps_trans; [exact MS3| exact MS4]) MG14
               ltac:(intros a Ha Hn; rewrite (AG4 a Ha Hn); apply (AG3 a Ha); clear -Hn; lia) SP4 MI4 (L5.defined_grows M2 M4 _ _ MG14 DF2) Hz0 Hsd Hzsd Hd).
    + assert (ZR3 : PNSDD.zers S M3 4).
      { intros i Hi. apply (PNSDD.cell_xfer S ltac:(clear -FS; lia) M2 M3 (fun a => S - 232 <= a < S - 216) i 0 AG3); [intros a Ha; clear -Ha Hi; lia| clear -Hi; lia| exact (ZR2 i Hi)]. }
      destruct (PNSDMID.from_nh R0 S first sigma r hi lo Fr ltac:(clear -FS; lia) F16 Ffirst ltac:(clear -Fdj; lia) Fsig Fhi Flo fx3 R3 M3 SH3 X10 CN3 MI3 ZR3)
        as (fx4 & R4 & M4 & MG4 & AG4 & MI4 & e' & z & sd & d & MS4 & SP4 & Fe' & Hz0 & Hsd & Hzsd & Hd & SDG).
      assert (MG14 : mem_grows M2 M4) by (intros a Ha; apply MG4; apply MG3; exact Ha).
      apply (output sigma e' Fsig Fe' 0x39080 fx2 R2 M2 fx4 R4 M4 z sd d HH2 EK2 DK2 STK2 ERR2 ltac:(eapply msteps_trans; [exact MS3| exact MS4]) MG14
               ltac:(intros a Ha Hn; rewrite (AG4 a Ha Hn); apply (AG3 a Ha); clear -Hn; lia) SP4 MI4 (L5.defined_grows M2 M4 _ _ MG14 DF2) Hz0 Hsd Hzsd Hd).
  - (* [comment removed for export] *)
    apply (output sigma e Fsig Fe 0x38afc fx1 R1 M1 fx2 R2 M2 z sd d HH1 EK1 DK1 STK1 ERR1 MS2 MG2 AG2 SP2 MI2 (L5.defined_grows M1 M2 _ _ MG2 DF1) Hz0 Hsd Hzsd Hd).
Qed.
End Call.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma radix_ok R0 first S r : RADIX_stmt R0 first S r.
Proof.
  unfold RADIX_stmt. intros sigma e fx R M z sd Fsig He Fr FS F16 Ffirst Fimg Fdj SQ MIM DF Hz0 Hsd Hz Hse.
  exact (PNSDRDX.radix R0 S first sigma e r ltac:(clear -FS; lia) F16 Ffirst ltac:(clear -Fdj; lia) Fimg Fsig ltac:(clear -He; lia) Fr fx R M z sd SQ MIM DF Hz0 Hsd Hz
           ltac:(clear -He; lia) Hse).
Qed.

Theorem dec128_ok : PNRS.str_push_back_short_spec L HI -> PNRS.from_int_spec L HI -> PNRS.dec128_spec L HI.
Proof.
  intros PBS FI. unfold PNRS.dec128_spec, PNR.dec128_spec.
  intros fx R M model K LB cr first vp sp r ax HH MOK K0 ENT A10 A11 A12 HB DEFf Hvp1 Hvp2 DEFv Hvp8 BASE BERR KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl12 in A12.
  change (PMSP.pm_scr 3) with 18432 in STK, KONT.
  destruct HB as (Bb & mb & HBin & HB1 & HB2).
  assert (BRLB : PMFR.brange L LB) by (apply (PMFR.brange_of_heap L HI HIok _ LB cr M _ HH); intros y Hy; exact Hy).
  pose proof (PMCK.lb_hi L HI HIok LB cr M _ HH) as LBhi.
  cbn [PNL.pn_dec128 PnLayoutS_u.NADDR_S].
  exact (call R M model K LB cr first vp sp r ax Bb mb MOK K0 Rra RAok Rsp Rgp Rtp STK A10 A11 A12 HBin HB1 HB2 DEFf Hvp1 Hvp2 DEFv Hvp8 BASE BERR BRLB LBhi PBS FI KONT (radix_ok R first sp r) fx HH).
Qed.

(* [comment removed for export] *)
Theorem dec128_closed : PNRS.dec128_spec L HI.
Proof. exact (dec128_ok (PNSPBS.str_push_back_short_ok L HI LY HIok) (PNSFI.from_int_ok L HI LY HIok (PNSPBS.str_push_back_short_ok L HI LY HIok))). Qed.

End WithHeap.
End PNSDEC.
