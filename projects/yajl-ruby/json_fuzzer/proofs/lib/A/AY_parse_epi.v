(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AYajlRep AYajl_iface AY_rz AY_hand AY_parse_kit AY_parse_head.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
Definition AY_PEXIT_B : Z := 0x898b0.
Definition AFF_RETIRED : Z := 0x45e0360e.
Definition F5 : byte := Z_to_bv 8 245.
Definition pffsh_dead : list cell :=
  [C1 F5; C1 F5; C1 F5; C1 F5; C1 F5; C1 F5; C1 F5; C1 F5; C1 F5; C1 F5; C1 F5; C1 F5; C1 F5; C1 F5; C1 F5; C1 F5].

(* [comment removed for export] *)
Lemma epiA_seg : forall (P : acc -> Prop) (sp gp tp rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2v s4v s5v t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (H SQ ff T len : Z) (k0 k224 j1 : list byte),
  rw_cells asegs m SQ
     [CB 24 k0; C8 (Z_to_bv 64 3); C8 (Z_to_bv 64 7); C8 (Z_to_bv 64 9223372036854775809); C8 (Z_to_bv 64 ff);
      C8 (Z_to_bv 64 ((H + 32) / 8 + 2147450880)); C8 (Z_to_bv 64 0x21d00); C8 (Z_to_bv 64 ff); C8 (Z_to_bv 64 (H + 40));
      C8 (Z_to_bv 64 ((H + 8) / 8 + 2147450880)); C8 (Z_to_bv 64 (H + 8)); C8 (Z_to_bv 64 ((H + 24) / 8 + 2147450880)); C8 (Z_to_bv 64 (H + 24));
      C8 (Z_to_bv 64 AY_JT_PTOK); C8 (Z_to_bv 64 (H / 8 + 2147450880)); C8 (Z_to_bv 64 H); C8 (Z_to_bv 64 ((H + 56) / 8 + 2147450880));
      C8 (Z_to_bv 64 (H + 56)); C8 (Z_to_bv 64 ((H + 16) / 8 + 2147450880)); C8 (Z_to_bv 64 (H + 16)); C8 (Z_to_bv 64 T); C8 (Z_to_bv 64 len);
      C8 (Z_to_bv 64 (H + 32)); C8 (Z_to_bv 64 (ff + 32)); C8 (Z_to_bv 64 (ff + 64)); C8 (Z_to_bv 64 (H + 48)); CB 8 k224; C8 (Z_to_bv 64 ff)] ->
  rw_cells asegs m ff [C8 (Z_to_bv 64 AFF_MAGIC); C8 (Z_to_bv 64 AFF_DESCR); C8 (Z_to_bv 64 AY_DO_PARSE); CB 8 j1] ->
  rw_cells asegs m (ff / 8 + 2147450880) pffsh -> mem_inv asegs m ->
  (6303744 <= ff /\ (ff + 128 <= 2147446784 \/ 17594333495296 <= ff)) -> ff + 128 <= alloc_ceiling -> ff mod 128 = 0 ->
  alloc_ceiling <= SQ -> SQ + 240 <= 2^47 ->
  pol P SQ (SQ + 240) -> pol P ff (ff + 128) -> pol P (ff / 8 + 2147450880) (ff / 8 + 2147450880 + 16) ->
  evtA asegs P (fun ms' => exists (a0' : word) (m' : mem),
      ms' = MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) a0' (Z_to_bv 64 ff) a2 a3 a4 a5 a6 a7
                   s2v (Z_to_bv 64 11) s4v s5v (Z_to_bv 64 (H + 60)) (Z_to_bv 64 ((H + 60) / 8 + 2147450880)) (Z_to_bv 64 2147450880)
                   (Z_to_bv 64 ((H + 48) / 8 + 2147450880)) (Z_to_bv 64 AY_JT_PSTATE) (Z_to_bv 64 (ff / 8 + 2147450880)) t3 t4 t5 t6)
               F (Z_to_bv 64 AY_PEXIT_B) fc None m' (seg_rom asegs)
      /\ munch [(ff / 8 + 2147450880, ff / 8 + 2147450880 + 16); (ff, ff + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' ff [C8 (Z_to_bv 64 AFF_RETIRED); C8 (Z_to_bv 64 AFF_DESCR); C8 (Z_to_bv 64 AY_DO_PARSE); CB 8 j1]
      /\ rw_cells asegs m' (ff / 8 + 2147450880) pffsh_dead)
    (MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) a0 a1 a2 a3 a4 a5 a6 a7
             s2v (Z_to_bv 64 11) s4v s5v (Z_to_bv 64 (H + 60)) (Z_to_bv 64 ((H + 60) / 8 + 2147450880)) (Z_to_bv 64 2147450880)
             (Z_to_bv 64 ((H + 48) / 8 + 2147450880)) (Z_to_bv 64 AY_JT_PSTATE) (Z_to_bv 64 (ff / 8 + 2147450880)) t3 t4 t5 t6)
        F (Z_to_bv 64 AY_PEXIT) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until j1. intros FR FFA FSH MI FF1 FF2 FF3 SQ0 SQH PSTK PFF PFFS.
  unfold pol, AY_PEXIT, AY_PEXIT_B, AY_JT_PSTATE, AY_JT_PTOK, AFF_MAGIC, AFF_DESCR, AY_DO_PARSE, AFF_RETIRED in *.
  set (SHF := ff / 8 + 2147450880) in *.
  assert (SHFR : 2147450880 <= SHF /\ SHF + 16 <= 17594333495296) by (subst SHF; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(SHF, SHF + 16); (ff, ff + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold pffsh in FSH.
  zstepA. zstepA. zstepA.                                   (* [comment removed for export] *)
  zstepA. zstepA.                                          (* [comment removed for export] *)
  zstepA. zstepA.                                          (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0; [exfalso; revert K0; rewrite ?unsigned_lit by lia; lia|].   (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  do 16 zstepA.                                            (* [comment removed for export] *)
  apply evtA_done. cbv beta. eexists _, _. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

(* [comment removed for export] *)
Lemma epiB_seg : forall (P : acc -> Prop) (sp gp tp rav t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s4v s5v t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (H SQ ff AFL lo : Z) (j3 : list byte) (code : Z) (fl : byte) (fcs : list cell)
    (fs0e s11e s10e s9e s8e s7e s6e s5e s4e s3e s2e s1e s0e rae : word),
  rw_cells asegs m (ff + 68) [CB 52 j3; C8 (Z_to_bv 64 AFL)] ->
  rw_cells asegs m AFL [C1 fl] -> mem_inv asegs m ->
  rw_cells asegs m (bv_unsigned sp - 112) [C8 fs0e; C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 rae] ->
  stk asegs m lo SQ -> rw_cells asegs m SQ fcs -> cells_size fcs = 240%nat -> stk asegs m (SQ + 240) (bv_unsigned sp - 112) ->
  (6303744 <= ff /\ (ff + 128 <= 2147446784 \/ 17594333495296 <= ff)) -> ff + 128 <= alloc_ceiling ->
  (6303744 <= AFL /\ (AFL + 1 <= 2147446784 \/ 17594333495296 <= AFL)) -> AFL < alloc_ceiling -> (AFL + 1 <= ff \/ ff + 128 <= AFL) ->
  alloc_ceiling <= lo -> lo <= SQ -> SQ + 352 <= bv_unsigned sp -> bv_unsigned sp < 2^47 ->
  pol P lo (bv_unsigned sp) -> pol P ff (ff + 128) -> P (Z_to_bv 64 AFL, 1%nat) ->
  evtA asegs P (fun ms' => exists (m' : mem),
      ms' = MS (mkR rae sp gp tp t0 t1 t2 s0e s1e (Z_to_bv 64 code) (Z_to_bv 64 ff) a2 a3 a4 a5 a6 a7
                   s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
               (bvmap_set 8 fs0e F) (ret_pc rae) fc None m' (seg_rom asegs)
      /\ munch [(AFL, AFL + 1)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' AFL [C1 (Z_to_bv 8 0)]
      /\ stk asegs m' lo (bv_unsigned sp))
    (MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) a0 (Z_to_bv 64 ff) a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 code) (Z_to_bv 64 11) s4v s5v (Z_to_bv 64 (H + 60)) (Z_to_bv 64 ((H + 60) / 8 + 2147450880)) (Z_to_bv 64 2147450880)
             (Z_to_bv 64 ((H + 48) / 8 + 2147450880)) (Z_to_bv 64 AY_JT_PSTATE) (Z_to_bv 64 (ff / 8 + 2147450880)) t3 t4 t5 t6)
        F (Z_to_bv 64 AY_PEXIT_B) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until rae. intros FJ3 FLC MI SV ST FRX FRS GAP FF1 FF2 AF1 AF2 AF3 CEIL LOQ SQH SPH PSTK PFF PAFL.
  unfold pol, AY_PEXIT_B, AY_JT_PSTATE in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (munch_refl [(AFL, AFL + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstepA.                                                  (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA. zstepA.                                          (* [comment removed for export] *)
  zstepA. rewrite ?Z_to_bv_bv_unsigned.                    (* [comment removed for export] *)
  replace (bv_unsigned sp - 112) with (bv_unsigned sp + -112) in SV by lia.
  do 13 zstepA.                                            (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA. rewrite ?Z_to_bv_bv_unsigned.                    (* [comment removed for export] *)
  lazymatch goal with H0 : stk asegs ?mx lo SQ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H0 into ST9 end.
  lazymatch type of ST9 with stk _ ?my _ _ => assert (STX : stk asegs my lo (bv_unsigned sp)) end.
  { lazymatch type of ST9 with stk _ ?mx _ _ =>
      assert (STM : stk asegs mx SQ (bv_unsigned sp + -112))
        by (eapply stk_merge; [pose proof (stk_of_rw_cells asegs _ _ _ FRX) as X; rewrite FRS in X; change (Z.of_nat 240) with 240 in X; exact X
                              | replace (bv_unsigned sp + -112) with (bv_unsigned sp - 112) by lia; exact GAP | lia]) end.
    eapply stk_merge; [eapply stk_merge; [exact ST9| exact STM| lia]| | lia].
    pose proof (stk_of_rw_cells asegs _ _ _ SV) as X. cbn [cells_size csize Nat.add] in X.
    replace (bv_unsigned sp + -112 + Z.of_nat 112) with (bv_unsigned sp) in X by lia. exact X. }
  zstepA.                                                  (* [comment removed for export] *)
  apply evtA_done. cbv beta. eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

(* [comment removed for export] *)
Section W.
Variable Y : ay_params.
Hypothesis KIPY : AHK_y_kip_stmt Y.
Hypothesis FRAMEY : AHK_y_frame_stmt Y.
Hypothesis BLKY : AHK_y_blocks_stmt Y.
Hypothesis BSHY : AHK_y_block_shadow_stmt Y.
Hypothesis LAYY : AHK_y_layout_stmt Y.
Hypothesis RRT : ayR_trans_stmt Y.
Hypothesis NONNEG : yacct_nonneg_stmt Y.
Hypothesis YHM : yacct_hand_mono_stmt Y.
Hypothesis RELY : AHK_y_fake_release_stmt Y.
Hypothesis AFLSEP : AHK_y_aflsep_stmt Y.
(* [comment removed for export] *)
Hypothesis FLAGY : forall s LB LF m mo f, y_AHK Y s LB LF m mo -> In f LF ->
  (exists fl, rw_cells asegs m (y_aflag Y (fst f) (snd f)) [C1 fl])
  /\ (y_aflag Y (fst f) (snd f) + 1 <= snd f \/ snd f + ff_bytes (fst f) <= y_aflag Y (fst f) (snd f)).

(* [comment removed for export] *)
Lemma pass_exit : forall (E : apE Y) (F : bvmap 5 word) (fc : bv 32) m mo s LK h mh cx obw olw cr
    (rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4v s5v t3 t4 t5 t6 : word) (st : ystatus) (R : ystatus * yhandle * yctx -> Prop) h0 cx0,
  penvA E -> pok E h0 cx0 -> pmem E m mo s LK h mh cx obw olw cr -> y_phi_hand Y h 0 <= cr -> frm0 fc -> R (st, h, cx) -> (length LK <= 1)%nat ->
  (yb_data (lx_buf (h_lexer h)) <> None -> 0 < yb_len (lx_buf (h_lexer h))) ->
  (yb_data (h_decbuf h) <> None -> 0 < yb_len (h_decbuf h)) -> 0 < h_stack_size h ->
  pexit_cont E R ->
  realizes_cfg acfg asegs (mkCfg (pstate E AY_PEXIT F fc m rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz (status_code st)) s4v s5v t3 t4 t5 t6) mo) (p_K E).
Proof. aceil.
  intros until R. intros h0 cx0 PA OK PM HCR FRM HR0 LKL WL WD SZ EXIT.
  pose proof PM as (AY & HR & SAME & CXR & TXT & (k0 & k224 & FR) & SV & FF & OCX & STK & GAP & MI & PRES & UA & (CRED & CR0) & (SO1 & R1) & SB1 & LKZ).
  pose proof OK as (K0 & LP & U0 & SB0 & TB & OTB & (f & FIN & FCX & FCL) & LC0 & NBIG & RR0 & TP & FFP & FFR0).
  apply AYST_split in AY. destruct AY as [AHK YS].
  pose proof HR as (HS & LXR & DBR & BSR). pose proof HS as (_ & BC1 & BC2 & BC3 & BC4).
  pose proof (mk_pblk BLKY LAYY BSHY E s LK h mh h0 cx0 m mo PA OK AHK SAME SB1 SZ) as PB.
  openPA PA. openPB PB. yshow pa_ffP0. (* [comment removed for export] *) pose proof SAME as (EH & EL & ELB & EDB & ECX).
  destruct (BLKY _ _ _ _ _ AHK) as (RNG & _ & _). destruct (LAYY _ _ _ _ _ AHK) as (LAYF & LAYFB & LAYFF).
  pose proof FF as (FFA & FOB & FJ2 & FOL & FJ3 & FSH).
  pose proof (bv_unsigned_in_range 64 (p_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  destruct (FLAGY _ _ _ _ _ (1, p_ff E) AHK (or_introl eq_refl)) as [[fl FLC] AFF]. cbn [fst snd] in FLC, AFF.
  pose proof (LAYF (1, p_ff E) (or_introl eq_refl)) as (_ & _ & _ & _ & AFR). cbn [fst snd] in AFR. unfold oshw_hi, A_SB, amem in AFR; aceil.
  unfold ff_bytes in AFF. change (Z.shiftl 64 1) with 128 in AFF.
  set (AFL := y_aflag Y 1 (p_ff E)) in *.
  unfold pstate.
  arz_seg KIPY AHK.
  pose proof (mk_ppol BLKY LAYY BSHY E s LK h mh h0 cx0 m mo _ _ PA OK AHK SAME SB1 SZ LINK) as PP. openPP PP.
  assert (PAFL : acc_ok (m_vm_lazy mo) (y_aS Y s) (Z_to_bv 64 AFL, 1%nat)).
  { apply LINK. unfold ay_acc. cbn [fst snd]. rewrite unsigned_lit by (clear -CEILB AFR; lia). do 6 right. left. exists (1, p_ff E). split; [left; reflexivity|]. cbn [fst snd]. split; [reflexivity| reflexivity]. }
  (* [comment removed for export] *)
  eapply evtA_cut.
  { eapply (epiA_seg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (mh_addr (p_mh E)) (p_SQ E) (p_ff E) (p_T E) (zlength (p_txt E)) k0 k224 (p_fj1 E));
      [ exact FR | exact FFA | exact FSH | exact MI | exact (pa_ffA PA) | clear -CEILB pa_ff0 pa_ffP0; lia | clear -CEILB pa_ff0 pa_ffP0; lia
      | clear -CEILB pa_SQ0 pa_ceil0 pa_lo0; lia | clear -CEILB pa_SQ0 pa_sp0; lia
      | intros a k Ha Hk; apply pp_stk0; clear -CEILB Ha Hk pa_SQ0 pa_lo0; lia | exact pp_ff0 | intros a k Ha Hk; apply pp_ffs0; clear -CEILB Ha Hk; lia ]. }
  cbv beta. intros ms1 (a0x & m1 & -> & MU1 & WM1 & MI1 & FFA1 & FSH1).
  (* [comment removed for export] *)
  pose proof FJ3 as FJ3'. unfold pffZ in FJ3'. rewrite FFP in FJ3'. unfold wz in FJ3'. fold AFL in FJ3'.
  eapply evtA_cut.
  { eapply (epiB_seg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (mh_addr (p_mh E)) (p_SQ E) (p_ff E) AFL (p_lo E) (p_fj3 E) (status_code st) fl (pframe E k0 k224));
      [ eapply rw_cells_transport; [exact FJ3'| exact MU1| exact WM1| cbn; clear -CEILB pa_ff0 pa_ffP0; lia]
      | eapply rw_cells_transport; [exact FLC| exact MU1| exact WM1| cbn; clear -CEILB AFF AFR pa_ff0 pa_ffP0; lia]
      | exact MI1
      | eapply rw_cells_transport; [exact SV| exact MU1| exact WM1| cbn; clear -CEILB pa_ff0 pa_ffP0 pa_SQ0 pa_ceil0 pa_lo0; lia]
      | eapply stk_transport_disjoint; [exact STK| exact MU1| exact WM1| cbn; clear -CEILB pa_ff0 pa_ffP0 pa_SQ0 pa_ceil0 pa_lo0; lia]
      | eapply rw_cells_transport; [exact FR| exact MU1| exact WM1| cbn; clear -CEILB pa_ff0 pa_ffP0 pa_SQ0 pa_ceil0 pa_lo0; lia]
      | reflexivity
      | eapply stk_transport_disjoint; [exact GAP| exact MU1| exact WM1| cbn; clear -CEILB pa_ff0 pa_ffP0 pa_SQ0 pa_ceil0 pa_lo0; lia]
      | exact (pa_ffA PA) | clear -CEILB pa_ff0 pa_ffP0; lia | clear -CEILB AFR; lia | clear -CEILB AFR; lia | exact AFF
      | clear -CEILB pa_ceil0; lia | clear -CEILB pa_SQ0 pa_lo0 pa_ceil0; lia | clear -CEILB pa_SQ0; lia | clear -CEILB pa_sp0; lia
      | exact pp_stk0 | exact pp_ff0 | exact PAFL ]. }
  cbv beta. intros ms2 (m2 & -> & MU2 & WM2 & MI2 & FLC2 & ST2).
  apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
  (* [comment removed for export] *)
  assert (AHK2 : y_AHK Y s (abl (yblocks mh h) ++ LK ++ p_REST E) (pLF E) m1 mo1).
  { eapply FRAMEY; [exact AHK1| exact MU1| exact WM1|]. constructor; [| constructor; [| constructor]].
    - right; right; right; left. exists (1, p_ff E). split; [left; reflexivity|]. cbn [fst snd]. unfold oshw_lo, A_SB. change (Z.shiftl 8 1) with 16. clear -CEILB pa_ff0 pa_ffP0. lia.
    - right; right; left. exists (1, p_ff E). split; [left; reflexivity|]. cbn [fst snd]. unfold ff_bytes. change (Z.shiftl 64 1) with 128. clear -CEILB pa_ff0 pa_ffP0. lia. }
  assert (AHK3 : y_AHK Y s (abl (yblocks mh h) ++ LK ++ p_REST E) (p_LF E) m2 mo1).
  { pose proof (RELY _ _ _ _ _ _ 1 (p_ff E) AHK2 (or_introl eq_refl) MU2 WM2 FLC2) as X. unfold pLF in X. cbn [ff_remove fst snd] in X.
    rewrite Z.eqb_refl, Z.eqb_refl in X. cbn [andb] in X. exact X. }
  (* [comment removed for export] *)
  pose proof (munch_agree _ _ _ MU1 WM1) as AG1. pose proof (munch_agree _ _ _ MU2 WM2) as AG2.
  assert (AG : agree_on asegs (fun a => outside [(p_ff E / 8 + 2147450880, p_ff E / 8 + 2147450880 + 16); (p_ff E, p_ff E + 8)] a /\ outside [(AFL, AFL + 1)] a) m m2).
  { intros a Ha [O1 O2]. destruct (AG1 a Ha O1) as [E1 W1]. destruct (AG2 a Ha O2) as [E2 W2]. split; [congruence| auto]. }
  assert (OUTff : forall a, (a < p_ff E \/ p_ff E + 128 <= a) -> (a < 2147450880 \/ 17594333495296 <= a) -> (a < AFL \/ AFL + 1 <= a) ->   (* [comment removed for export] *)
            outside [(p_ff E / 8 + 2147450880, p_ff E / 8 + 2147450880 + 16); (p_ff E, p_ff E + 8)] a /\ outside [(AFL, AFL + 1)] a).
  { intros a H1 H2 H3. cbn. clear -CEILB H1 H2 H3 pa_ff0 pa_ffP0. repeat split; Z.div_mod_to_equations; lia. }
  (* [comment removed for export] *)
  assert (IN : forall b, In b (abl (yblocks mh h)) -> In b (abl (yblocks mh h) ++ LK ++ p_REST E)) by (intros b Hb; apply in_or_app; left; exact Hb).
  assert (OUTB : forall A n a, In (mkABlock A n) (abl (yblocks mh h) ++ LK ++ p_REST E) -> (6303744 <= A /\ (A + n <= 2147446784 \/ 17594333495296 <= A)) -> A <= a < A + n ->
            outside [(p_ff E / 8 + 2147450880, p_ff E / 8 + 2147450880 + 16); (p_ff E, p_ff E + 8)] a /\ outside [(AFL, AFL + 1)] a).
  { intros A n a Hb HA Ha. pose proof (LAYFB (1, p_ff E) _ (or_introl eq_refl) Hb) as [D1 D2]. cbn [ab_addr ab_size fst snd] in D1, D2.
    unfold ff_bytes in D1. change (Z.shiftl 64 1) with 128 in D1. fold AFL in D2.
    apply OUTff; clear -CEILB D1 D2 HA Ha; lia. }
  assert (RBLK : forall b, In b (abl (yblocks mh h) ++ LK ++ p_REST E) -> 0 < ab_size b -> (6303744 <= ab_addr b /\ (ab_addr b + ab_size b <= 2147446784 \/ 17594333495296 <= ab_addr b))).
  { intros b Hb Hn. pose proof (proj2 (BSHY _ _ _ _ _ _ AHK Hb Hn)) as X. revert X CEILB. clear. unfold oshw_hi, A_SB, amem. intros X CEILB. lia. }
  unfold pexit_cont in EXIT.
  eapply (EXIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fc m2 mo1 s st h cx mh LK HR0); [| | | | | | | | | | | | | | | | exact LKL | exact LKZ].
  - exact SO1.
  - eapply RRT; [exact R1| exact R01].
  - clear -CEILB CRED HCR. lia.
  - reflexivity.
  - exact MI2.
  - exact ST2.
  - exact FRM.
  - (* [comment removed for export] *)
    eapply ay_pres_trans; [exact PRES|]. intros a Ha Hc Hx.
    destruct (AG a Ha) as [Eq Wq]; [| split; [exact Eq| exact Wq]].
    cbn. destruct Hc as [Hc|[(b & Hb & Hr)|[(f' & Hf' & Hr)|Hc]]].
    + clear -CEILB Hc pa_ff0 pa_ffP0 pa_ceil0 pa_lo0 AFR. repeat split; Z.div_mod_to_equations; lia.
    + pose proof (LAYFB (1, p_ff E) b (or_introl eq_refl) ltac:(apply in_or_app; right; apply in_or_app; right; exact Hb)) as [D1 D2].
      cbn [fst snd] in D1, D2. unfold ff_bytes in D1. change (Z.shiftl 64 1) with 128 in D1. fold AFL in D2.
      destruct (Z.lt_ge_cases 0 (ab_size b)) as [Hn|Hn]; [| exfalso; clear -CEILB Hn Hr; lia].
      pose proof (RBLK _ ltac:(apply in_or_app; right; apply in_or_app; right; exact Hb) Hn) as Y0.
      clear -CEILB D1 D2 Y0 Hr pa_ff0 pa_ffP0. repeat split; Z.div_mod_to_equations; lia.
    + pose proof (FFR0 f' Hf') as D. pose proof (LAYF f' (or_intror Hf')) as (F1' & F2' & F3' & F4' & _).
      aceil.
      pose proof (AFLSEP _ _ _ _ _ (1, p_ff E) f' AHK (or_introl eq_refl) (or_intror Hf')) as D3. cbn [fst snd] in D3. fold AFL in D3.
      assert (NEQ : p_ff E <> snd f').
      { intros EQ. rewrite <- EQ in D. clear -CEILB D F4'. assert (E0 : fst f' = 0 \/ fst f' = 1) by lia.
        destruct E0 as [E0|E0]; rewrite E0 in D; [change (ff_bytes 0) with 64 in D| change (ff_bytes 1) with 128 in D]; lia. }
      specialize (D3 NEQ).
      revert Hr D F1' F2' F3' F4' D3 pa_ff0 pa_ffP0 AFR CEILB. clear. unfold oshw_lo, oshw_hi, A_SB, amem. intros Hr D F1' F2' F3' F4' D3 PFF PFFP AFR CEILB.
      change (2147450880 + 0 / 8 + (2 ^ 47 + 7) / 8) with 17594333495296 in *.
      assert (Q1 : p_ff E = 8 * (p_ff E / 8)) by (clear -CEILB PFF; Z.div_mod_to_equations; lia).
      assert (E0 : fst f' = 0 \/ fst f' = 1) by lia.
      assert (Q2 : snd f' = 8 * (snd f' / 8)).
      { clear -CEILB F3' E0. destruct E0 as [E0|E0]; rewrite E0 in F3'; [change (ff_bytes 0) with 64 in F3'| change (ff_bytes 1) with 128 in F3']; Z.div_mod_to_equations; lia. }
      set (q1 := p_ff E / 8) in *. set (q2 := snd f' / 8) in *. clearbody q1 q2.
      destruct E0 as [E0|E0]; rewrite E0 in Hr, F1', F2', D, D3;
        [change (Z.shiftl 8 0) with 8 in Hr; change (ff_bytes 0) with 64 in F1', Hr, F2', D, D3| change (Z.shiftl 8 1) with 16 in Hr; change (ff_bytes 1) with 128 in F1', Hr, F2', D, D3];
        (clear F3'; repeat split; lia).
    + unfold ay_static in Hc. clear -CEILB Hc pa_ff0 pa_ffP0 AFR. repeat split; Z.div_mod_to_equations; lia.
  - eapply hand_rep_agree; [exact AG| exact HR|]. intros a (b & Hb & Ha). destruct b as [bA bn].
    eapply (OUTB bA bn a); [apply IN; exact Hb| | exact Ha]. apply (RBLK _ (IN _ Hb)). cbn [ab_addr ab_size] in Ha |- *. clear -CEILB Ha. lia.
  - exact SAME.
  - eapply ctx_rep_agree; [exact AG| exact CXR|]. intros a Ha.
    pose proof (AFLSEP _ _ _ _ _ (1, p_ff E) f AHK (or_introl eq_refl) (or_intror FIN) ltac:(cbn [snd]; clear -CEILB pa_ffCX0 FCX; lia)) as D3. cbn [fst snd] in D3. fold AFL in D3.
    rewrite FCL in D3. change (ff_bytes 1) with 128 in D3.
    yshow pa_CXP0. apply OUTff; [clear -CEILB Ha pa_ffCX0; lia| clear -CEILB Ha pa_CX0 pa_CXP0; lia| clear -CEILB Ha D3 FCX; lia].
  - eapply text_at_agree; [exact AG| exact TXT|]. intros a Ha.
    destruct TB as [(bt & Hbt & B1 & B2)| Z0]; [| exfalso; clear -CEILB Ha Z0; lia]. destruct bt as [btA btn].
    eapply (OUTB btA btn a); [apply in_or_app; right; apply in_or_app; right; exact Hbt| | cbn [ab_addr ab_size] in B1, B2; clear -CEILB Ha B1 B2; lia].
    apply (RBLK _ ltac:(apply in_or_app; right; apply in_or_app; right; exact Hbt)). cbn [ab_addr ab_size] in B1, B2 |- *. clear -CEILB Ha B1 B2. lia.
  - intros HD. destruct (BSHY _ _ _ _ _ _ AHK3 (IN _ (yb_in_lexdata mh h HD)) ltac:(cbn; exact (WL HD))) as [X1 X2]. cbn [ab_addr ab_size] in X1, X2. split; [exact X1| exact X2].
  - intros HD. destruct (BSHY _ _ _ _ _ _ AHK3 (IN _ (yb_in_decdata mh h HD)) ltac:(cbn; exact (WD HD))) as [X1 X2]. cbn [ab_addr ab_size] in X1, X2. split; [exact X1| exact X2].
  - intros HSB. destruct (BSHY _ _ _ _ _ _ AHK3 (IN _ (yb_in_stack mh h HSB)) ltac:(cbn; exact SZ)) as [X1 X2]. cbn [ab_addr ab_size] in X1, X2. split; [exact X1| exact X2].
  - apply AYST_split. split; [exact AHK3|].
    eapply aystatics_munch; [eapply aystatics_munch; [exact YS| exact MU1| exact WM1|]| exact MU2| exact WM2|].
    + constructor; [cbn [fst snd]; clear -CEILB pa_ff0 pa_ffP0; right; Z.div_mod_to_equations; lia| constructor; [cbn [fst snd]; clear -CEILB pa_ff0 pa_ffP0; lia| constructor]].
    + constructor; [cbn [fst snd]; clear -CEILB AFR; lia| constructor].
Qed.
(* [comment removed for export] *)
Lemma pass_done : forall (E : apE Y) (F : bvmap 5 word) (fc : bv 32) m mo s LK h mh cx
    (rav t0 t1 a1 a2 a3 a4 a5 a6 a7 s4v s5v t3 t4 t5 t6 : word) st rest,
  penvA E -> phead_inv E fc m mo s LK h mh cx -> h_stack h = st :: rest -> lex_state st = false ->
  pexit_cont E (fun r => let '(st', h', cx') := r in yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h cx) (SR_done st' h' cx')) ->
  realizes_cfg acfg asegs (mkCfg (phead E F fc m (h_used h) rav t0 t1 a1 a2 a3 a4 a5 a6 a7 s4v s5v t3 t4 t5 t6) mo) (p_K E).
Proof. aceil.
  intros until rest. intros PA HI HST LS EXIT.
  destruct HI as ((obw & olw & cr & PM & [HCR _]) & OK & FRM & PLK). pose proof (plk_ok_len _ _ PLK) as LKL. clear PLK. popen OK PM.
  destruct (loop_pre_exit_facts _ _ _ LP) as (WL & WD & SZ).
  assert (SZ8 : h_stack_size h mod 8 = 0 /\ zlength rest + 1 <= h_stack_size h).
  { split; [exact SZM|]. assert (W : weak_inv (zlength (p_txt E)) h) by (destruct LP as [HI|[W _]]; [apply (hinv_weak _ _ _ HI)| exact W]).
    destruct W as (_ & US & _). unfold h_used in US. rewrite HST in US. unfold zlength in *. cbn [length] in US. clear -CEILB US. lia. }
  pose proof (mk_pblk BLKY LAYY BSHY E s LK h mh h cx m mo PA OK AHK SAME SB1 SZ) as PB.
  openPA PA. openPB PB. yshow pa_ffP0. (* [comment removed for export] *) pose proof SAME as (EH & EL & ELB & EDB & ECX).
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (IN : forall b, In b (abl (yblocks mh h)) -> In b (abl (yblocks mh h) ++ LK ++ p_REST E)) by (intros b Hb; apply in_or_app; left; exact Hb).
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_hand mh h)) ltac:(cbn; unfold SIZEOF_HANDLE; lia))) as OSH_H. cbn [ab_addr ab_size] in OSH_H.
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_stack mh h SB1)) ltac:(cbn; lia))) as OSH_S. cbn [ab_addr ab_size] in OSH_S.
  unfold oshadow, A_SB in OSH_H, OSH_S. destruct OSH_H as (_ & _ & SHH). destruct OSH_S as (_ & _ & SHS).
  assert (SCX : exists junk, rw_cells asegs m (mh_stack mh) [CB (Z.to_nat (h_used h)) (zbytes (stack_bytes (h_stack h))); CB (Z.to_nat (h_stack_size h - h_used h)) junk]).
  { clear -CEILB BSR SB1. unfold RYajlRep.bs_rep in BSR. destruct (h_stack_blk h); [| exfalso; apply SB1; reflexivity]. destruct BSR as (_ & junk & SC). exists junk. exact SC. }
  destruct SCX as [junk SC]. rewrite USED, HST in SC.
  unfold hand_cells, hand_head_cells, alloc_cells in HC. cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ayc app] in HC. unfold wz in HC. rewrite EH in HC.
  unfold phead, pstate.
  arz_seg KIPY AHK.
  pose proof (mk_ppol BLKY LAYY BSHY E s LK h mh h cx m mo _ _ PA OK AHK SAME SB1 SZ LINK) as PP. openPP PP.
  eapply evtA_cut.
  { rewrite USED. eapply (head_dispatch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (mh_addr (p_mh E)) (p_SQ E) (p_ff E) (mh_stack mh) st rest (h_stack_size h) junk);
      [ exact MI | exact HC | exact I | exact SC | exact (proj2 SZ8) | exact (proj1 SZ8) | clear -CEILB BC2; lia
      | clear -CEILB pa_H0; lia | clear -CEILB pa_H0; lia | clear -CEILB pa_H0; lia
      | exact (pb_SBA PB) | clear -CEILB pb_SB0; lia | clear -CEILB pb_SB0; lia
      | rewrite EH in SHH; exact SHH | reflexivity | exact SHS | reflexivity
      | exact pp_img0 | exact pp_Hs0 | exact pp_H0 | exact pp_SB0 | exact pp_SBs0 ]. }
  cbv beta. intros ms1 ->.
  assert (PMX : forall mo1, magree mo mo1 -> LI (y_aS Y s) (y_aN Y s) (y_aEB Y s) mo1 -> pmem E m mo1 s LK h mh cx obw olw cr).
  { intros mo1 Hag1 HLI1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
    unfold pmem. split; [apply AYST_split; split; [exact AHK1| exact YS]|].
    split; [exact HR|]. split; [exact SAME|]. split; [exact CXR|]. split; [exact TXT|]. split; [exists k0, k224; exact FR|]. split; [exact SV|].
    split; [exact FF|]. split; [exact OCX|]. split; [exact STK|]. split; [exact GAP|]. split; [exact MI|]. split; [exact PRES|]. split; [exact UA|]. split; [split; [exact CRED| exact CR0]|].
    split; [split; [exact SO1| eapply RRT; [exact R1| exact R01]]|]. split; [exact SB1| lk_nil]. }
  destruct st; try discriminate LS; cbn [state_targetA].
  - (* [comment removed for export] *)
    apply evtA_done. intros mo1 Hag1 HLI1 Hh1.
    pose proof (fun rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4v s5v t3 t4 t5 t6 st R => pass_exit E F fc m mo1 s LK h mh cx obw olw cr rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4v s5v t3 t4 t5 t6 st R h cx) as PX. unfold pstate in PX.
    eapply PX with (st := YS_ok); [exact PA| exact OK| apply PMX; assumption| exact HCR| exact FRM| | exact LKL| exact WL| exact WD| exact SZ| exact EXIT].
    cbv beta. unfold yparse_step. rewrite (ybs_current_eq _ _ _ HST). cbn [ybind]. apply yl_ret.
  - (* [comment removed for export] *)
    zstepA. zstepA. apply evtA_done. intros mo1 Hag1 HLI1 Hh1.
    pose proof (fun rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4v s5v t3 t4 t5 t6 st R => pass_exit E F fc m mo1 s LK h mh cx obw olw cr rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4v s5v t3 t4 t5 t6 st R h cx) as PX. unfold pstate in PX.
    eapply PX with (st := YS_error); [exact PA| exact OK| apply PMX; assumption| exact HCR| exact FRM| | exact LKL| exact WL| exact WD| exact SZ| exact EXIT].
    cbv beta. unfold yparse_step. rewrite (ybs_current_eq _ _ _ HST). cbn [ybind]. apply yl_ret.
  - (* [comment removed for export] *)
    zstepA. zstepA. apply evtA_done. intros mo1 Hag1 HLI1 Hh1.
    pose proof (fun rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4v s5v t3 t4 t5 t6 st R => pass_exit E F fc m mo1 s LK h mh cx obw olw cr rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4v s5v t3 t4 t5 t6 st R h cx) as PX. unfold pstate in PX.
    eapply PX with (st := YS_error); [exact PA| exact OK| apply PMX; assumption| exact HCR| exact FRM| | exact LKL| exact WL| exact WD| exact SZ| exact EXIT].
    cbv beta. unfold yparse_step. rewrite (ybs_current_eq _ _ _ HST). cbn [ybind]. apply yl_ret.
Qed.
End W.
End RC__1.
