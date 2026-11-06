(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep Image SFW1_lemmas.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlParser YajlFactsBuf YajlFactsLex YajlFactsParse YajlFactsLoop.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BY_ubkit B_iface BYajlRep BYajl_iface BY_rz BY_hand BY_parse_kit BY_parse_head.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA.LiaFastA.zify_fast_euclid3.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition J_BACK : Z := 0x8982c.   (* [comment removed for export] *)
Definition J_SETB : Z := 0x89094.
Definition J_LEXERR : Z := 0x89090.
Definition J_PERR : Z := 0x89238.

(* [comment removed for export] *)
(* [comment removed for export] *)
End RC__1.
Ltac pkill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia; rewrite ?signed_lit_small by lia; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac qlia0 := first [solve [clear; lia] | lia].
(* [comment removed for export] *)
Ltac keep_mod := repeat match goal with H : ?T |- _ =>
  lazymatch T with
  | _ /\ _ /\ _ mod _ = 0 => fail | _ <= alloc_ceiling <= _ => fail | @eq Z _ _ => fail
  | _ => clear H end end.
Ltac qliaH := first [solve [keep_mod; lia] | lia].
Ltac qliaS := qliaH.
(* [comment removed for export] *)
Ltac keep_sep := repeat match goal with H : ?T |- _ =>
  lazymatch T with
  | _ /\ _ /\ _ mod _ = 0 => fail | _ <= alloc_ceiling <= _ => fail | @eq Z _ _ => fail | _ \/ _ => fail | _ /\ (_ \/ _) => fail | _ -> _ \/ _ => fail
  | _ => clear H end end.
(* [comment removed for export] *)
Ltac qlia_sep := first [solve [unfold yhide in *; keep_sep; Z.div_mod_to_equations; lia] | unfold yhide in *; Z.div_mod_to_equations; lia].
(* [comment removed for export] *)
Ltac keep_bsg := repeat match goal with H : ?T |- _ =>
  lazymatch T with
  | _ /\ _ /\ _ mod _ = 0 => fail | _ <= alloc_ceiling <= _ => fail | @eq Z _ _ => fail
  | 0 <= zlength _ => fail | 0 < h_used _ => fail | _ <= h_used _ <= _ => fail | h_used _ <= _ => fail
  | _ = true => fail | _ = false => fail
  | _ => clear H end end.
Ltac qliaB := first [solve [keep_bsg; Z.div_mod_to_equations; lia] | Z.div_mod_to_equations; lia].
Ltac shH SHH SHHeq MU WM k w :=
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch type of SHH with u8arr _ ?m0 (2147450880 + ?H / 8) ?shb =>
      let R := fresh "SHR" in
      assert (R : ov_read_bytes bsegs mx (Z_to_bv 64 ((H + k) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 0]);
      [ replace ((H + k) / 8 + 2147450880) with (2147450880 + (H + k) / 8) by qlia0;
        apply (block_shadow_read0_u bsegs mx 2147450880 H 104 (H + k) w);
        [ qliaH | qlia0 | rewrite <- SHHeq; first [exact SHH | eapply (u8arr_transport bsegs); [exact SHH| exact MU| exact WM| rewrite SHHeq, (blk_shadow_length 104) by qlia0; cbn [disjoint_from fst snd]; qlia_sep]]
        | qlia0 | qlia0 | qlia0 | qliaH ]
      | zstepA; clear R; rewrite ?zxb_small, ?sxb_small by qlia0 ]
    end end.
(* [comment removed for export] *)
Ltac shH0 SHH SHHeq MU WM w :=
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch type of SHH with u8arr _ ?m0 (2147450880 + ?H / 8) ?shb =>
      let R := fresh "SHR" in
      assert (R : ov_read_bytes bsegs mx (Z_to_bv 64 (H / 8 + 2147450880)) 1 = Some [Z_to_bv 8 0]);
      [ replace (H / 8 + 2147450880) with (2147450880 + H / 8) by qlia0;
        apply (block_shadow_read0_u bsegs mx 2147450880 H 104 H w);
        [ qliaH | qlia0 | rewrite <- SHHeq; first [exact SHH | eapply (u8arr_transport bsegs); [exact SHH| exact MU| exact WM| rewrite SHHeq, (blk_shadow_length 104) by qlia0; cbn [disjoint_from fst snd]; qlia_sep]]
        | qlia0 | qlia0 | qlia0 | qliaH ]
      | zstepA; clear R; rewrite ?zxb_small, ?sxb_small by qlia0 ]
    end end.
(* [comment removed for export] *)
Ltac shS SHS SHSeq MU WM i size :=
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch type of SHS with u8arr _ ?m0 (2147450880 + ?B / 8) ?shb =>
      let R := fresh "SHR" in
      assert (R : ov_read_bytes bsegs mx (Z_to_bv 64 ((B + i) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 0]);
      [ replace ((B + i) / 8 + 2147450880) with (2147450880 + (B + i) / 8) by qlia0;
        apply (block_shadow_read0_u bsegs mx 2147450880 B size (B + i) 1);
        [ qliaS | qliaB | rewrite <- SHSeq; first [exact SHS | eapply (u8arr_transport bsegs); [exact SHS| exact MU| exact WM| rewrite SHSeq, (blk_shadow_length size) by qliaB; cbn [disjoint_from fst snd]; qlia_sep]]
        | qliaB | qlia0 | qliaB | first [solve [clear; Z.div_mod_to_equations; lia] | qliaB] ]
      | zstepA; try shadow_addr; zstepA; zstepA; clear R; rewrite ?zxb_small, ?sxb_small by qlia0 ]
    end end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lia1 := LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker.
Ltac solve_cond_base1 :=
  first [ reflexivity
        | apply Z.ltb_lt; lia1 | apply Z.ltb_ge; lia1
        | apply Z.leb_le; lia1 | apply Z.leb_gt; lia1
        | apply Z.eqb_eq; lia1 | apply Z.eqb_neq; lia1 ].
Ltac solve_cond_rec1 :=
  lazymatch goal with
  | |- negb _ = true => apply (proj2 (Bool.negb_true_iff _)); solve_cond_rec1
  | |- negb _ = false => apply (proj2 (Bool.negb_false_iff _)); solve_cond_rec1
  | _ => solve_cond_base1
  end.
Ltac solve_cond1 := unfold_cond; fold_lit_ux; solve_cond_rec1.
Ltac if_true1 := let c := goal_cond in replace c with true; [cbv iota| symmetry; solve_cond1].
Ltac if_false1 := let c := goal_cond in replace c with false; [cbv iota| symmetry; solve_cond1].
(* [comment removed for export] *)
Ltac if_litc1 := let c := goal_cond in let v := eval vm_compute in c in
  lazymatch v with true => change c with true | false => change c with false end; cbv iota.
(* [comment removed for export] *)
Lemma zext32_shl_shr : forall x, 0 <= x < 4294967296 ->
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl x 32))) 32) = Z_to_bv 64 x.
Proof.
  intros x Hx. f_equal. rewrite unsigned_lit_wrap. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite Z.mod_small by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac kill_bsg G := revert G; keep_bsg; intros G; try rewrite ZBridge.zb_lxor_ones in G by lia; first [kill G | gkill G | xkill G].
Ltac ugd_bs := zstepA; (let G := fresh "G" in if_cases G; zify_cond G; [ first [kill_bsg G | clear G] | first [kill_bsg G | clear G] ]).
Ltac ugd_bsN := ugd_bs.
Ltac bs_guards := ugd_bs; zstepA; zstepA; zstepA; ugd_bs; ugd_bs.
Ltac bs_guardsN := bs_guards.

(* [comment removed for export] *)
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section W.
Variable Y : ay_params.
Hypothesis KIPY : AHK_y_kip_stmt Y.
Hypothesis FRAMEY : AHK_y_frame_stmt Y.
Hypothesis BLKY : AHK_y_blocks_stmt Y.
Hypothesis BSHY : AHK_y_block_shadow_stmt Y.
Hypothesis LAYY : AHK_y_layout_stmt Y.
Hypothesis RRT : ayR_trans_stmt Y.
Hypothesis UFRAME : forall m m' SP ra s0, (forall a, SP <= a < 2^47 -> m' (wa a) = m (wa a)) -> y_uanchor Y m SP ra s0 -> y_uanchor Y m' SP ra s0.

(* [comment removed for export] *)
Definition pagain (E : apE Y) (h0 : yhandle) (cx0 : yctx) (LK : list ablock) : Prop :=
  forall (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : y_APS Y) (h' : yhandle) (mh' : mhand) (cx' : yctx)
         (rav' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s2v' s5v' t3' t4' t5' t6' : word),
    yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_again h' cx') ->
    phead_inv E fc' m' mo' s' LK h' mh' cx' ->
    realizes_cfg acfg bsegs (mkCfg (phead E F' fc' m' (h_used h') rav' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s2v' s5v' t3' t4' t5' t6') mo') (p_K E).

Lemma pok_again : forall (E : apE Y) h0 cx0 h cx,
  pok E h0 cx0 -> loop_pre (pLEN E) h cx -> 0 < h_used h -> h_stack_blk h <> None -> h_stack_size h mod 8 = 0 -> pok E h cx.
Proof. aceil.
  intros E h0 cx0 h cx OK LP1 U1 SB SZ. destruct OK as (K0 & _ & _ & _ & REST0). unfold pok.
  split; [exact K0|]. split; [exact LP1|]. split; [exact U1|]. split; [split; [exact SB| exact SZ]| exact REST0].
Qed.

(* [comment removed for export] *)
Lemma J_back : forall (E : apE Y) (F : bvmap 5 word) (fc : bv 32) m mo s LK h0 cx0 h mh cx obw olw cr
    (rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2v s5v t3 t4 t5 t6 : word),
  penvA E -> pok E h0 cx0 -> pmem E m mo s LK h mh cx obw olw cr -> pcr E h cr -> frm0 fc ->
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_again h cx) -> h_stack_size h mod 8 = 0 -> plk_ok LK h ->
  pagain E h0 cx0 LK ->
  realizes_cfg acfg bsegs (mkCfg (pstate E J_BACK F fc m rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2v (wz (p_ff E)) s5v t3 t4 t5 t6) mo) (p_K E).
Proof. aceil.
  intros until t6. intros PA OK PM HCR FRM YL SZM' PLK AG.
  popen OK PM.
  destruct (yparse_step_again_facts (p_txt E) (zlength (p_txt E)) h0 cx0 h cx eq_refl ltac:(openPA PA; clear -CEILB pa_len0; lia) LP YL) as (LP1 & U1 & _).
  assert (SZ : 0 < h_stack_size h) by (destruct (loop_pre_exit_facts _ _ _ LP1) as (_ & _ & X); exact X).
  pose proof (pok_again E h0 cx0 h cx OK LP1 U1 SB1 SZM') as OK1.
  openPA PA. clear pa_ffCX0 pa_ffH0 pa_CXH0 pa_Tsep0 pa_OT0 pa_j0. pose proof SAME as (EH & EL & ELB & EDB & ECX).
  assert (IN : forall b, In b (abl (yblocks mh h)) -> In b (abl (yblocks mh h) ++ LK ++ p_REST E)) by (intros b Hb; apply in_or_app; left; exact Hb).
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_hand mh h)) ltac:(cbn; unfold SIZEOF_HANDLE; lia))) as OSH_H. cbn [ab_addr ab_size] in OSH_H.
  unfold oshadow, A_SB, SIZEOF_HANDLE in OSH_H. destruct OSH_H as (_ & _ & SHH). rewrite EH in SHH.
  remember (blk_shadow 104) as shb eqn:SHHeq in SHH.
  unfold hand_cells, hand_head_cells, alloc_cells in HC. cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ayc app] in HC. unfold wz in HC. rewrite EH in HC.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold pstate, J_BACK, wz.
  arz_seg KIPY AHK.
  pose proof (mk_ppol BLKY LAYY BSHY E s LK h mh h0 cx0 m mo _ _ PA OK AHK SAME SB1 SZ LINK) as PP. openPP PP.
  unfold pol in pp_Hs0, pp_H0.
  shH SHH SHHeq MU WM 60 4.                                 (* [comment removed for export] *)
  zstepA. if_false.                                        (* [comment removed for export] *)
  zstepA. rewrite ?ysx32_small by (clear -CEILB BC3 BC2; lia).   (* [comment removed for export] *)
  zstepA. if_cases K1; zify_cond K1; [pkill K1|].          (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
  unfold pagain, phead, pstate in AG. eapply AG; [exact YL|].
  split; [| split; [exact OK1| split; [exact FRM| exact PLK]]].
  exists obw, olw, cr. split; [| exact HCR]. unfold pmem. split; [apply AYST_split; split; [exact AHK1| exact YS]|].
  split; [exact HR|]. split; [exact SAME|]. split; [exact CXR|]. split; [exact TXT|]. split; [exists k0, k224; exact FR|]. split; [exact SV|].
  split; [exact FF|]. split; [exact OCX|]. split; [exact STK|]. split; [exact GAP|]. split; [exact MI|]. split; [exact PRES|]. split; [exact UA|]. split; [split; [exact CRED| exact CR0]|].
  split; [split; [exact SO1| eapply RRT; [exact R1| exact R01]]|]. split; [exact SB1| lk_nil].
Qed.
(* [comment removed for export] *)
Lemma J_setb : forall (E : apE Y) (F : bvmap 5 word) (fc : bv 32) m mo s LK h0 cx0 h mh cx obw olw cr st rest s'
    (rav t0 t1 t2 a2 a3 a4 a5 a6 a7 s2v s5v t3 t4 t5 t6 : word),
  penvA E -> pok E h0 cx0 -> pmem E m mo s LK h mh cx obw olw cr -> frm0 fc -> h_stack h = st :: rest -> h_stack_size h mod 8 = 0 ->
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_again (h_set_stack h (s' :: rest)) cx) ->
  pcr E (h_set_stack h (s' :: rest)) cr -> (LK = [] \/ (length LK = 1%nat /\ lex_state s' = false)) ->
  pagain E h0 cx0 LK ->
  realizes_cfg acfg bsegs (mkCfg (pstate E J_SETB F fc m rav t0 t1 t2 (wz (mh_stack mh + (h_used h - 1))) (wz (state_code s')) a2 a3 a4 a5 a6 a7
                                 s2v (wz (p_ff E)) s5v t3 t4 t5 t6) mo) (p_K E).
Proof. aceil.
  intros until t6. intros PA OK PM FRM HST SZM' YL PHI PLK AG.
  assert (PLK' : plk_ok LK (h_set_stack h (s' :: rest))).
  { destruct PLK as [PLK|[PL1 PLK]]; [left; exact PLK| right]. split; [exact PL1|]. exists s', rest. split; [reflexivity| exact PLK]. }
  clear PLK.
  popen OK PM. yhide TB. yhide OTB. yhide LP. yhide FFR0.
  assert (U1 : 0 < h_used h) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  pose proof (proj2 BC3) as US. assert (SZ : 0 < h_stack_size h) by (clear -CEILB U1 US; lia).
  pose proof (mk_pblk BLKY LAYY BSHY E s LK h mh h0 cx0 m mo PA OK AHK SAME SB1 SZ) as PB. pose proof (pb_SB _ _ _ PB) as RSB. pose proof (pb_SBA PB) as RSBA.
  openPA PA. clear pa_ffCX0 pa_ffH0 pa_CXH0 pa_Tsep0 pa_OT0 pa_j0. pose proof SAME as (EH & EL & ELB & EDB & ECX).
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  pose proof (state_code_range s') as CR.
  pose proof BSR as BSR'. unfold RYajlRep.bs_rep in BSR'. destruct (h_stack_blk h) as [sbk|] eqn:HSB in BSR'; [| exfalso; exact (SB1 HSB)].
  destruct BSR' as (SBNZ & junk & SC).
  destruct (u8arr_of_CB2 _ _ _ _ _ _ _ SC) as (ARR & L1 & L2). clear SC.
  pose proof L1 as L1'. rewrite zbytes_length, stack_bytes_length, HST in L1'. cbn [length] in L1'.
  assert (LEN : length (zbytes (stack_bytes (h_stack h)) ++ junk) = Z.to_nat (h_stack_size h)) by (rewrite length_app; clear -CEILB L1 L2 US U1; lia).
  pose proof (munch_refl [(mh_stack mh + (h_used h - 1), mh_stack mh + (h_used h - 1) + 1)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (pb_HSB _ _ _ PB) as SEPHS. rewrite <- EH in SEPHS. pose proof (pb_SBCX _ _ _ PB) as SEPSC.
  clear TXT LXR DBR FF OCX GAP PRES UA CRED HS HR. yhide SV.
  unfold hand_cells, hand_head_cells, alloc_cells in HC. cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ayc app] in HC. unfold wz in HC.
  unfold pstate, J_SETB, wz.
  arz_seg KIPY AHK.
  pose proof (mk_ppol BLKY LAYY BSHY E s LK h mh h0 cx0 m mo _ _ PA OK AHK SAME SB1 SZ LINK) as PP. pose proof (pp_SB _ _ _ _ PP) as PSB. unfold pol in PSB.
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (u8arr_store_ok_at bsegs mx (mh_stack mh) _ (h_used h - 1) ARR ltac:(rewrite length_app; clear -CEILB L1 L2 US USED Z0; lia)) as SOK end.
  stepA.                                                   (* [comment removed for export] *)
  lazymatch type of ARR with u8arr _ ?mx _ _ =>
    pose proof (u8arr_write bsegs mx (mh_stack mh) _ (h_used h - 1) (Z_to_bv 8 (state_code s')) ARR ltac:(rewrite length_app; clear -CEILB L1 L2 US USED Z0; lia)) as ARR' end.
  rewrite le1_wz by (clear -CEILB CR; lia). clear ARR. store_done.
  zstepA.                                                  (* [comment removed for export] *)
  apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
  lazymatch goal with |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m2 end.
  pose proof (pmem_remodel E m mo mo1 s LK h mh cx obw olw cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
  pose proof (J_back E F fc m2 mo1 s LK h0 cx0 (h_set_stack h (s' :: rest)) mh cx obw olw cr) as JB. unfold pstate, J_BACK, wz in JB.
  eapply JB; [exact PA| exact OK| | exact PHI| exact FRM| exact YL| exact SZM'| exact PLK'| exact AG].
  yshow TB. yshow OTB. yshow LP. yshow FFR0.
  eapply (pmem_updA BLKY LAYY BSHY FRAMEY UFRAME E m m2 mo1 s LK h mh cx obw olw cr);
    [exact PA| exact OK| exact PM1| exact SZ| exact MU| exact WM| assumption| | reflexivity| reflexivity| reflexivity| reflexivity| exact I| |
    | eapply ctx_rep_agree; [eapply munch_agree; [exact MU| exact WM]| exact CXR| intros a Ha; cbn; clear -CEILB Ha SEPSC US U1; lia]
    | exists k0, k224; assumption| yshow SV; eapply (rw_cells_transport bsegs); [exact SV| exact MU| exact WM| unfold psaved; cbn; clear -CEILB pa_SQ0 pa_lo0 pa_ceil0 RSB US U1; lia] | assumption].
  - constructor; [| constructor]. unfold ownA. cbn [fst snd]. right; left. clear -CEILB US USED Z0. lia.
  - (* [comment removed for export] *)
    split; [| cbn [h_set_stack h_bytesConsumed h_stack_size h_stack_blk h_parseError]; rewrite HSB;
             replace (h_used (h_set_stack h (s' :: rest))) with (h_used h) by (unfold h_used; cbn [h_stack h_set_stack]; rewrite HST; reflexivity);
             split; [exact BC1| split; [exact BC2| split; [exact BC3| intros; split; intros; congruence]]]].
    exists pew, pad. split; [| exact PW].
    unfold hand_cells, hand_head_cells, alloc_cells. cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ayc app h_set_stack h_bytesConsumed h_stack_size].
    replace (h_used (h_set_stack h (s' :: rest))) with (h_used h) by (unfold h_used; cbn [h_stack h_set_stack]; rewrite HST; reflexivity).
    lazymatch goal with H0 : rw_cells bsegs m2 (mh_addr mh) _ |- _ => exact H0 end.
  - (* [comment removed for export] *)
    unfold RYajlRep.bs_rep. cbn [h_stack_blk h_set_stack h_stack h_stack_size]. rewrite HSB. split; [exact SBNZ|]. exists junk.
    replace (h_used (h_set_stack h (s' :: rest))) with (h_used h) by (unfold h_used; cbn [h_stack h_set_stack]; rewrite HST; reflexivity).
    apply CB2_of_u8arr; [| rewrite zbytes_length, stack_bytes_length; cbn [length]; clear -CEILB L1'; lia | exact L2].
    revert ARR'. rewrite HST, !stack_bytes_cons, !zbytes_app. cbn [zbytes map]. rewrite <- !app_assoc. cbn [app].
    rewrite (upd_app_len _ _ _ _ _) by (rewrite zbytes_length, stack_bytes_length; unfold zlength in USED; clear -CEILB USED; lia).
    intros ARR'. exact ARR'.
Qed.
(* [comment removed for export] *)
Lemma J_lexerr : forall (E : apE Y) (F : bvmap 5 word) (fc : bv 32) m mo s LK h0 cx0 h mh cx obw olw cr st rest
    (rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2v s5v t3 t4 t5 t6 : word),
  penvA E -> pok E h0 cx0 -> pmem E m mo s LK h mh cx obw olw cr -> frm0 fc -> h_stack h = st :: rest -> h_stack_size h mod 8 = 0 ->
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_again (h_set_stack h (ST_lexical_error :: rest)) cx) ->
  pcr E (h_set_stack h (ST_lexical_error :: rest)) cr -> (length LK <= 1)%nat ->
  pagain E h0 cx0 LK ->
  realizes_cfg acfg bsegs (mkCfg (pstate E J_LEXERR F fc m rav t0 t1 t2 (wz (mh_stack mh + (h_used h - 1))) a1 a2 a3 a4 a5 a6 a7
                                 s2v (wz (p_ff E)) s5v t3 t4 t5 t6) mo) (p_K E).
Proof. aceil.
  intros until t6. intros PA OK PM FRM HST SZM' YL PHI LKL AG.
  assert (PLK : LK = [] \/ (length LK = 1%nat /\ lex_state ST_lexical_error = false)).
  { destruct LK; [left; reflexivity| right]. split; [cbn [length] in LKL |- *; clear -CEILB LKL; lia| reflexivity]. }
  pose proof PM as (AY & _). apply AYST_split in AY. destruct AY as [AHK _].
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold pstate, J_LEXERR, wz. arz_seg KIPY AHK.
  zstepA.                                                  (* [comment removed for export] *)
  apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
  pose proof PM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [_ R1] & _).
  pose proof (pmem_remodel E m mo mo1 s LK h mh cx obw olw cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
  pose proof (J_setb E F fc m mo1 s LK h0 cx0 h mh cx obw olw cr st rest ST_lexical_error) as JS. unfold pstate, J_SETB, wz in JS. cbn [state_code] in JS.
  eapply JS; [exact PA| exact OK| exact PM1| exact FRM| exact HST| exact SZM'| exact YL| exact PHI| exact PLK| exact AG].
Qed.

(* [comment removed for export] *)
Lemma J_perr : forall (E : apE Y) (F : bvmap 5 word) (fc : bv 32) m mo s LK h0 cx0 h mh cx obw olw cr e
    (rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2v s5v t3 t4 t5 t6 : word),
  penvA E -> pok E h0 cx0 -> pmem E m mo s LK h mh cx obw olw cr -> frm0 fc -> h_stack_size h mod 8 = 0 -> 0 < h_used h ->
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_again (h_set_perr h e) cx) ->
  pcr E (h_set_perr h e) cr -> plk_ok LK h ->
  pagain E h0 cx0 LK ->
  realizes_cfg acfg bsegs (mkCfg (pstate E J_PERR F fc m rav t0 t1 t2 (wz (ay_perr e)) a1 a2 a3 a4 a5 a6 a7
                                 s2v (wz (p_ff E)) s5v t3 t4 t5 t6) mo) (p_K E).
Proof. aceil.
  intros until t6. intros PA OK PM FRM SZM' U1 YL PHI PLK AG.
  assert (PLK' : plk_ok LK (h_set_perr h e)) by exact PLK. clear PLK.
  popen OK PM. yhide TB. yhide OTB. yhide LP. yhide FFR0.
  pose proof (proj2 BC3) as US. assert (SZ : 0 < h_stack_size h) by (clear -CEILB U1 US; lia).
  pose proof (mk_pblk BLKY LAYY BSHY E s LK h mh h0 cx0 m mo PA OK AHK SAME SB1 SZ) as PB.
  pose proof (pb_HSB _ _ _ PB) as SEPHS. pose proof (pb_SB _ _ _ PB) as RSB. pose proof (pb_SBA PB) as RSBA.
  openPA PA. clear pa_ffCX0 pa_Tsep0 pa_OT0 pa_j0. pose proof SAME as (EH & EL & ELB & EDB & ECX).
  pose proof BSR as BSR'. unfold RYajlRep.bs_rep in BSR'. destruct (h_stack_blk h) as [sbk|] eqn:HSB in BSR'; [| exfalso; exact (SB1 HSB)].
  destruct BSR' as (SBNZ & junk & SC).
  clear TXT LXR DBR FF OCX GAP PRES UA CRED HS HR. yhide SV. yhide SC.
  unfold hand_cells, hand_head_cells, alloc_cells in HC. cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ayc app] in HC. unfold wz in HC. rewrite EH in HC.
  pose proof (munch_refl [(mh_addr (p_mh E) + 24, mh_addr (p_mh E) + 32)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold pstate, J_PERR, wz.
  arz_seg KIPY AHK.
  pose proof (mk_ppol BLKY LAYY BSHY E s LK h mh h0 cx0 m mo _ _ PA OK AHK SAME SB1 SZ LINK) as PP.
  pose proof (pp_H _ _ _ _ PP) as PH. pose proof (pp_stk _ _ _ _ PP) as PSTK. unfold pol in PH, PSTK.
  zstepA.                                                  (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
  lazymatch goal with |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m2 end.
  pose proof (pmem_remodel E m mo mo1 s LK h mh cx obw olw cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
  pose proof (J_back E F fc m2 mo1 s LK h0 cx0 (h_set_perr h e) mh cx obw olw cr) as JB. unfold pstate, J_BACK, wz in JB.
  eapply JB; [exact PA| exact OK| | exact PHI| exact FRM| exact YL| exact SZM'| exact PLK'| exact AG].
  yshow TB. yshow OTB. yshow LP. yshow FFR0. yshow SV. yshow SC.
  eapply (pmem_updA BLKY LAYY BSHY FRAMEY UFRAME E m m2 mo1 s LK h mh cx obw olw cr);
    [exact PA| exact OK| exact PM1| exact SZ| exact MU| exact WM| assumption| | reflexivity| reflexivity| reflexivity| reflexivity| exact I| |
    | eapply ctx_rep_agree; [eapply munch_agree; [exact MU| exact WM]| exact CXR| intros a Ha; cbn; clear -CEILB Ha pa_CXH0; lia]
    | exists k0, k224; assumption
    | eapply (rw_cells_transport bsegs); [exact SV| exact MU| exact WM| unfold psaved; cbn; clear -CEILB pa_SQ0 pa_lo0 pa_ceil0 pa_H0; lia] | assumption].
  - constructor; [| constructor]. unfold ownA. cbn [fst snd]. left. rewrite EH. clear. lia.
  - split; [| cbn [h_set_perr h_bytesConsumed h_stack_size h_stack_blk h_parseError]; rewrite HSB;
             split; [exact BC1| split; [exact BC2| split; [exact BC3| intros; split; intros; congruence]]]].
    exists (Z_to_bv 64 (ay_perr e)), pad. split; [| cbn [h_set_perr h_parseError perr_word]; reflexivity].
    unfold hand_cells, hand_head_cells, alloc_cells. cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w yc_perr ayc app h_set_perr h_bytesConsumed h_stack_size h_parseError]. unfold wz. rewrite EH.
    lazymatch goal with H0 : rw_cells bsegs m2 (mh_addr (p_mh E)) _ |- _ => exact H0 end.
  - eapply (rw_cells_transport bsegs) in SC; [| exact MU| exact WM| cbn; clear -CEILB SEPHS US U1; lia].
    unfold RYajlRep.bs_rep. cbn [h_stack_blk h_set_perr h_stack h_stack_size]. rewrite HSB. split; [exact SBNZ|]. exists junk. exact SC.
Qed.
End W.
End RC__2.
