(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr Ceiling RunWord SysStep.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac IcptA0 AllocA0 ATacAp.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import ShadowKit F_syscalls RF_mainA_A RDriverA_iface.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import HttpAllocA HApxF HttpRepA AWKit HObjA HCount HObjK HObjF H2KitA HPrepA H_freelist H_ListAddTail H_httpheader_free H_ListDestroy_seg H_ListDestroy
  H_httpmsg_destroy H_httpmsg_destroy_W H_parser_init H_presp H_phdr H_pent_kit H_pparse_stmt H_germ_GL H_germ PZDef H_pparse H_pappend_stmt H_pappend H_fuzz_room H_fuzz_q1 H_fuzz_pz H_fuzz_seg.
Import ListNotations.
Open Scope Z_scope.

Section W.
Context {HC : HasCeiling} {HG : HasGuard}.
Hypothesis IC : icpt_contracts.
Variable FI : fs_if.
Variable AI : am_if FI.
Variable J : a0_judg FI AI.
Variable AC : am_contracts FI AI J.
Hypothesis ASL : forall lo hi, am_static FI AI lo hi -> a0_static lo hi.
Hypothesis AMS : forall lo hi, a0_static lo hi -> am_static FI AI lo hi.
Hypothesis STACK_MALLOC_0 : stack_malloc_stmt FI 0.
Hypothesis STACK_MALLOC_1 : stack_malloc_stmt FI 1.
Hypothesis STACK_MALLOC_2 : stack_malloc_stmt FI 2.
Hypothesis STACK_MALLOC_3 : stack_malloc_stmt FI 3.
Hypothesis STACK_MALLOC_4 : stack_malloc_stmt FI 4.
Hypothesis SET_SHADOW_F5 : set_shadow_f5_stmt.
Local Notation K := (am_K FI AI).
Local Notation BLK := (block K).
Local Notation BL := (list (block K)).
Local Notation PS := (aps FI AI).
Local Notation FSIV W := ((FSB FI, FSB FI + A0_FS_SIZE) :: (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE) :: W)%Z.
Local Notation WER := [(A0_ERRNO, A0_ERRNO + 4)]%Z.
Local Notation httpmsg_destroy_stmtW_A := (H_httpmsg_destroy_W.httpmsg_destroy_stmtW_A FI AI J).

#[using="Type"] Lemma pkeep_of_apxF : forall s (LB : BL) q st m0 m m',
  RHEAP_A FI AI s LB m0 -> alloc_ceiling <= q -> apxF FI AI WER LB q st m m' -> pkeep FI AI LB q m m'.
Proof.
  intros s LB q st m0 m m' HR QC AP a Ha Hc.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  apply (AP a Ha).
  - destruct Hc as [X|[X|[X|X]]]; [left; exact X| right; left; destruct X as (lo & hi & S1 & S2 & _); exists lo, hi; split; assumption
                                  | right; right; left; exact X| right; right; right; left; exact X].
  - cbn [outside]. split; [| exact I]. unfold A0_ERRNO in *. destruct Hc as [X|[X|[X|X]]].
    + intros C. lia.
    + destruct X as (_ & _ & _ & _ & NE). exact NE.
    + intros C. destruct X as (b & Hb & R). destruct (am_block_range FI AI s LB m0 b HR Hb) as (_ & _ & _ & _ & R5 & _). lia.
    + intros C. destruct X as (b & Hb & R). destruct (am_block_range FI AI s LB m0 b HR Hb) as (R1 & _). unfold sh, SHADOW_OFF in R. Z.div_mod_to_equations. lia.
Qed.

#[using="AMS"] Lemma fuzz_close : forall s (LB : BL) q lo st m0 m m' (canary : word),
  RHEAP_A FI AI s LB m0 -> alloc_ceiling <= lo -> lo <= q -> q < 2^47 -> apxF FI AI WER LB q st m m' ->
  PZ m -> shz m (sh lo) (sh q) ->
  rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells asegs m ssp_guard [C8 canary] ->
  pkeep FI AI LB q m m' /\ PZ m' /\ shz m' (sh lo) (sh q)
  /\ rw_cells asegs m' got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells asegs m' ssp_guard [C8 canary].
Proof.
  intros s LB q lo st m0 m m' canary HR CLO LQ Q47 AP HPZ SHZ GS SG.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (pkeep_of_apxF s LB q st m0 m m' HR ltac:(lia) AP) as PK.
  split; [exact PK|].
  split.
  { apply (PZ_of_agree GL_germ (pclient FI AI LB q) m m' (pkeep_agree FI AI LB q m m' PK)); [| exact HPZ].
    intros a Ha. right; left. unfold pz_band in Ha. unfold A0_ERRNO.
    destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
    - exists 0x10000, 0xaca48. split; [apply AMS; unfold a0_static; split; [lia|]; left; lia| lia].
    - exists 0xaf320, 0xafa20. split; [apply AMS; unfold a0_static; split; [lia|]; right; left; lia| lia].
    - exists 0x5d6b80, 0x5e6be0. split; [apply AMS; unfold a0_static; split; [lia|]; do 2 right; left; lia| lia].
    - exists 0x5e6c00, 0x5e6ca0. split; [apply AMS; unfold a0_static; split; [lia|]; do 3 right; left; lia| lia].
    - exists 0x7fffa000, 0x800b9200. split; [apply AMS; unfold a0_static; split; [lia|]; do 11 right; left; lia| lia]. }
  split.
  { apply (shz_apxF FI AI AMS WER LB q st m m' _ _ SHZ AP).
    - unfold sh, SHADOW_OFF. clear - CLO. Z.div_mod_to_equations. lia.
    - unfold sh, SHADOW_OFF. clear - Q47. Z.div_mod_to_equations. lia.
    - intros a Ha. cbn [outside]. split; [| exact I]. intros C. unfold A0_ERRNO, sh, SHADOW_OFF in *. clear - Ha CLO ACR C. Z.div_mod_to_equations. lia. }
  split.
  - apply (apxF_rw_cells FI AI WER LB q st m m' _ _ AP GS).
    + apply (fclient_range_static FI AI LB q st _ _ 0x10000 0xaca48); [apply AMS; unfold a0_static; split; [lia|]; left; lia| unfold got_ssp; lia| unfold got_ssp; cbn; lia].
    + unfold got_ssp, A0_ERRNO. cbn. lia.
  - apply (apxF_rw_cells FI AI WER LB q st m m' _ _ AP SG).
    + apply (fclient_range_static FI AI LB q st _ _ 0x6075f0 0x6075f8); [apply AMS; unfold a0_static; split; [lia|]; do 5 right; left; lia| unfold ssp_guard; lia| unfold ssp_guard; cbn; lia].
    + unfold ssp_guard, A0_ERRNO. cbn. lia.
Qed.

#[using="ASL AMS STACK_MALLOC_4 SET_SHADOW_F5"] Lemma fuzz_n0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PS) (LB : BL) (st : fsstate FI) (D lo : Z) (errv canary : word),
  RHEAP_A FI AI s LB m -> RFAKE FI st m -> fs_call_ok FI st tp 6 -> asan_env asegs m ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - PARSER_STACK_A ->
  bv_unsigned sp mod 16 = 0 -> bv_unsigned sp + 16 < am_stack_top FI AI ->
  shz m (sh lo) (sh (bv_unsigned sp)) ->
  rw_cells asegs m RERRNOA [C4 errv] -> mem_inv asegs m -> PZ m ->
  rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells asegs m ssp_guard [C8 canary] ->
  AJ FI AI J (fuzz_one_postA FI AI PZ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s LB lo canary m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 fuzz_entryA) fc None m (seg_rom asegs))
    s LB.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB st D lo errv canary.
  intros HR RF FCO AE ST CLO LO QAL QTOP SHZ ERRC MI HPZ GS SG.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (am_stack_ok FI AI) as (TK1 & TK2 & TK3 & TK4).
  pose proof (bv_unsigned_in_range _ sp) as SPR. unfold bv_modulus in SPR.
  remember (bv_unsigned sp) as q eqn:Eq.
  assert (ESP : sp = Z_to_bv 64 q) by (subst q; symmetry; apply Z_to_bv_bv_unsigned).
  assert (AL16 : q = 16 * (q / 16)) by (clear - QAL; Z.div_mod_to_equations; lia).
  unfold PARSER_STACK_A in LO. assert (LOF : lo <= q - 65536) by lia.
  pose proof (fsb_ok FI) as (FB1 & FB2 & _ & FB4 & FB5).
  rewrite ESP. change fuzz_entryA with fuzz_entryF.
  eapply (aj_evt FI AI J).
  { eapply (frontF0 FI STACK_MALLOC_4 SET_SHADOW_F5 lo q (q / 16) st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m
              CLO LOF AL16 ltac:(lia) RF (fs_call_ok_le FI st tp 6 1 FCO ltac:(lia)) (am_fsenv FI AI s LB m HR) D); [exact ST| exact MI| exact AE]. }
  intros ms' PO. unfold postF0 in PO.
  destruct PO as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & m' & st' & -> & MU & WM & MI' & FK & LIVE' & RF' & ST' & AE').
  pose proof (apxF_of_munch_fkeep FI AI ASL s LB LB m m q lo st [] m m' HR (fun b H => H) RF CLO ltac:(lia) MU WM FK) as APF0.
  assert (APF : apxF FI AI WER LB q st m m').
  { eapply (apxF_weaken FI AI); [exact APF0| intros x Hx; exact I| lia| intros b Hb; exact Hb| intros g Hg; exact Hg]. }
  destruct (fuzz_close s LB q lo st m m m' canary HR CLO ltac:(lia) ltac:(lia) APF HPZ SHZ GS SG) as (PK & HPZ' & SHZ' & GS' & SG').
  apply (aj_ret FI AI J). unfold fuzz_one_postA.
  exists y0, y1, y2, b1, b2, b3, b4, b5, b6, b7, y3, y4, y5, y6, m', st'.
  split; [reflexivity|]. split; [exact MI'|]. split; [rewrite unsigned_lit by lia; exact ST'|]. split; [exact AE'|]. split; [exact RF'|].
  split; [rewrite unsigned_lit by lia; exact PK|]. split; [exact LIVE'|].
  split.
  { eapply (am_heap_frame FI AI s LB m m' _ HR MU WM).
    apply Forall_cons; [left; cbn [fst]; exact CLO|]. apply Forall_cons; [do 3 right; left; cbn [fst snd]; lia|].
    apply Forall_cons; [do 4 right; cbn [fst snd]; lia| apply Forall_nil]. }
  split; [intros b Hb; exact Hb|]. split; [intros b Hb; exact Hb|]. split; [unfold FZ_NSEC; lia|]. split; [exact HPZ'|].
  split.
  { exists errv. apply (rw_cells_transport asegs _ m m' _ _ ERRC MU WM). unfold RERRNOA.
    cbn [disjoint_from cells_size csize Nat.add]. change (Z.of_nat 4) with 4.
    split; [lia|]. split; [lia|]. split; [| exact I]. left. unfold sh, SHADOW_OFF. clear - FB1. Z.div_mod_to_equations. lia. }
  split; [rewrite unsigned_lit by lia; exact SHZ'|]. split; [exact GS'| exact SG'].
Qed.

#[using="Type"] Lemma apxF_narrow : forall W1 W2 (LB : BL) q st m m',
  apxF FI AI W1 LB q st m m' -> (forall a, fclient FI AI LB q st a -> outside W2 a -> outside W1 a) -> apxF FI AI W2 LB q st m m'.
Proof. intros W1 W2 LB q st m m' AP H a Ha Hc Ho. exact (AP a Ha Hc (H a Hc Ho)). Qed.

#[using="Type"] Lemma minvF_gagree : forall (Pk : Z -> Prop) lo q st (ra s0 s1 s2 s3 s4 s5 s6 s7 : word) q' m m' w,
  gagree_on Pk m m' -> minvF FI lo q st ra s0 s1 s2 s3 s4 s5 s6 s7 q' m w ->
  (forall a, q' <= a < q -> Pk a) ->
  (forall a, fuzzF FI st <= a < fuzzF FI st + 32 \/ fuzzF FI st + 536 <= a < fuzzF FI st + 1024
             \/ fuzzSF FI st <= a < fuzzSF FI st + 128 \/ a = fuzzFL FI st -> Pk a) ->
  stk asegs m' lo q' ->
  minvF FI lo q st ra s0 s1 s2 s3 s4 s5 s6 s7 q' m' w.
Proof.
  intros Pk lo q st ra s0 s1 s2 s3 s4 s5 s6 s7 q' m m' w AG INV HS HF ST'.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j0 & j8 & QC) & GAP & FRhi & FH & (jt & FT) & SHF & FLG).
  unfold minvF. split; [exists kq'; exact Hq32|]. split; [exact Hq|]. split; [exact ST'|].
  split. { exists j0, j8. eapply rw_cells_gagree; [exact AG| exact QC|]. cbn [cells_size csize Nat.add]. intros a Ha. apply HS. lia. }
  split. { eapply stk_gagree; [exact AG| exact GAP|]. intros a Ha. apply HS. lia. }
  split. { eapply rw_cells_gagree; [exact AG| exact FRhi|]. cbn [cells_size csize Nat.add]. intros a Ha. apply HS. lia. }
  split. { eapply rw_cells_gagree; [exact AG| exact FH|]. cbn [cells_size csize Nat.add]. intros a Ha. apply HF. lia. }
  split. { exists jt. eapply rw_cells_gagree; [exact AG| exact FT|]. cbn [cells_size csize Nat.add]. intros a Ha. apply HF. lia. }
  split. { eapply rw_cells_gagree; [exact AG| exact SHF|]. cbn [cells_size csize Nat.add]. intros a Ha. apply HF. lia. }
  eapply rw_cells_gagree; [exact AG| exact FLG|]. cbn [cells_size csize Nat.add]. intros a Ha. apply HF. lia.
Qed.

#[using="Type"] Lemma hs_count : forall m (hs : list (HObjA.hdr FI AI)), hdrs_mem FI AI m hs -> 2 * Z.of_nat (length hs) <= H_phdr.hsumA FI AI hs.
Proof.
  intros m hs. induction hs as [|h hs IH]; intros HM; [cbn; lia|].
  destruct HM as (_ & (V1 & _ & N1 & _) & HM'). specialize (IH HM'). unfold H_phdr.hsumA in *. cbn [fold_right length]. lia.
Qed.

#[using="Type"] Lemma noleak_incl : forall (l LB' : BL), NoDup (map blk_id l) -> (forall b, In b l -> In b LB') -> (length LB' <= length l)%nat ->
  forall b, In b LB' -> In b l.
Proof.
  intros l LB' ND SUB LEN.
  assert (ND' : List.NoDup l).
  { clear - ND. induction l as [|x l IH]; [constructor|]. cbn [map] in ND. apply list.NoDup_cons in ND. destruct ND as [NI ND]. constructor; [| exact (IH ND)].
    intros Hin. apply NI. apply list_elem_of_In. apply in_map. exact Hin. }
  exact (NoDup_length_incl ND' LEN SUB).
Qed.

Definition t_fresh (isreq meth pos : Z) : pstA FI AI :=
  mkPSA FI AI 0 0 0 0 None [] 0 [CB 216 (repeat (Z_to_bv 8 0) 216)] meth 0 0 0 0 None [] isreq 0 0 [] [] 0 (wz 0) (wz 0) 400 0 pos 1 0 0 0 0 [].

#[using="Type"] Lemma pinit_parser : forall m (LB : BL) P isreq meth pos,
  parser_init_cells_A m P isreq meth pos -> 0 <= isreq <= 1 -> 0 <= meth <= 11 -> 0 <= pos <= 1 ->
  p_parserA FI AI m LB P (t_fresh isreq meth pos) /\ rw_cells asegs m (P + 500) [C4 (wz 0)].
Proof.
  intros m LB P isreq meth pos (C0 & C8_ & C224 & C232 & C264 & C288 & C344 & C368 & C384 & C400 & C432) RI RM RP.
  unfold pinit_k5 in C432.
  split_chunk C432 1%nat CU R1. split_chunk R1 8%nat CCTL R2. split_chunk R2 3%nat CSC CPAD.
  replace (P + 432 + 8) with (P + 440) in CCTL by lia.
  split; [| exact CPAD].
  unfold p_parserA.
  cbn [pa_cur pa_A pa_len pa_cap pa_okm pa_bs pa_meth pa_uc pa_rm pa_sc pa_SA pa_slen pa_scap pa_sok pa_sbs pa_isreq pa_maj pa_min
       pa_ns pa_hs pa_X pa_ebw pa_elw pa_err pa_hack pa_pos pa_entp pa_clen pa_csz pa_esp pa_ub pa_UB t_fresh].
  split; [exact CSC|].
  split; [unfold p_msg; split; [exact C400|]; split; [cbn [mownA]; repeat split; reflexivity|]; split; [lia|]; split; [unfold LMAX_A; lia| reflexivity]|].
  split; [lia|].
  split; [split; [exact C0| lia]|].
  split; [split; [exact C8_| reflexivity]|].
  split; [split; [exact C224| lia]|].
  split; [unfold p_smsgWA; split; [exact C232|]; split; [cbn [mownA]; repeat split; reflexivity| lia]|].
  split; [split; [exists (wz 0); exact C264| lia]|].
  split; [unfold p_hlist; cbn [hd_addr last_addr zlength length Z.of_nat dlseg hdrs_mem map];
          split; [exact C288|]; split; [exact C344|]; split; [exact C368|]; split; [exact I|]; split; [exact I|]; split; [reflexivity|];
          split; [intros h []|]; split; [unfold zlength; cbn; lia| lia]|].
  split; [exact C384|].
  split; [split; [exact CCTL| lia]|].
  split; [split; [exact CU| lia]| reflexivity].
Qed.

#[using="Type"] Lemma pobj_join : forall m P (uc : list cell) (a0 a4 r0 r4 : word) (sb0 sb1 sb2 sb3 : word) (v0 v8 v12 v16 v20 : word)
    (l0 l1 l2 l3 l4 l5 l6 : word) (f0 f1 f2 f3 : word) (g0 g1 e0 e1 : word) (mb0 mb1 mb2 mb3 : word) (u0 : word)
    (c0 c1 c2 c3 c4 c5 c6 c7 : word) (s0 s1 s2 pad : word),
  rw_cells asegs m P [C4 a0; C4 a4] -> rw_cells asegs m (P + 8) uc -> cells_size uc = 216%nat ->
  rw_cells asegs m (P + 224) [C4 r0; C4 r4] -> rw_cells asegs m (P + 232) [C8 sb0; C8 sb1; C8 sb2; C8 sb3] ->
  rw_cells asegs m (P + 264) [C8 v0; C4 v8; C4 v12; C4 v16; C4 v20] ->
  rw_cells asegs m (P + 288) [C8 l0; C8 l1; C8 l2; C8 l3; C8 l4; C8 l5; C8 l6] -> rw_cells asegs m (P + 344) [C8 f0; C8 f1; C4 f2; C4 f3] ->
  rw_cells asegs m (P + 368) [C8 g0; C8 g1] -> rw_cells asegs m (P + 384) [C8 e0; C8 e1] ->
  rw_cells asegs m (P + 400) [C8 mb0; C8 mb1; C8 mb2; C8 mb3] -> rw_cells asegs m (P + 432) [C8 u0] ->
  rw_cells asegs m (P + 440) [C4 c0; C4 c1; C4 c2; C4 c3; C4 c4; C4 c5; C8 c6; C8 c7] ->
  rw_cells asegs m (P + 480) [C8 s0; C8 s1; C4 s2] -> rw_cells asegs m (P + 500) [C4 pad] ->
  exists jp, rw_cells asegs m P [CB 504 jp].
Proof.
  intros until pad. intros H0 HU SU H224 H232 H264 H288 H344 H368 H384 H400 H432 H440 H480 H500.
  destruct (rw_cells_forget asegs m (P + 8) uc HU) as [ju HU']. rewrite SU in HU'. clear HU.
  join_chunks H480 H500 J1. join_chunks H440 J1 J2. join_chunks H432 J2 J3. join_chunks H400 J3 J4. join_chunks H384 J4 J5.
  join_chunks H368 J5 J6. join_chunks H344 J6 J7. join_chunks H288 J7 J8. join_chunks H264 J8 J9. join_chunks H232 J9 J10.
  join_chunks H224 J10 J11. join_chunks HU' J11 J12. join_chunks H0 J12 J13.
  destruct (rw_cells_forget asegs m P _ J13) as [jp HJ]. exists jp. exact HJ.
Qed.

Section ARM1.
Hypothesis PA : pappend_stmt_A FI AI J.
Hypothesis DW : httpmsg_destroy_stmtW_A.
Hypothesis GERM : H_pent_kit.germ_stmt_A FI AI (H_pent_kit.gstA GL_germ).

#[using="IC ASL AMS STACK_MALLOC_4 SET_SHADOW_F5 PA DW GERM"] Lemma fuzz_n1 : forall (ra sp gp tp t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PS) (LB : BL) (st : fsstate FI) (D n lo : Z) (errv canary : word) (data : list byte) (kD : K),
  bytes_at asegs m D data -> Z.of_nat (length data) = n -> 1 <= n <= 2^26 -> In (kD, D, n) LB ->
  RHEAP_A FI AI s LB m -> RFAKE FI st m -> fs_call_ok FI st tp 6 -> asan_env asegs m ->
  Z.of_nat (length LB) <= 2 -> lb_bytes FI AI LB <= 2^27 -> am_nsec FI AI s + FZ_NSEC <= A0_NSEC_MAX ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 69632 ->
  bv_unsigned sp mod 16 = 0 -> bv_unsigned sp + 16 < am_stack_top FI AI ->
  shz m (sh lo) (sh (bv_unsigned sp)) -> shr m (sh lo - sh lo mod 8) (sh (bv_unsigned sp) + 8) ->
  rw_cells asegs m RERRNOA [C4 errv] -> mem_inv asegs m -> PZ m ->
  rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells asegs m ssp_guard [C8 canary] ->
  tp = Z_to_bv 64 A0_TP -> ra = Z_to_bv 64 0x863f8 ->
  AJ FI AI J (fuzz_one_postA FI AI PZ ra sp gp tp (Z_to_bv 64 n) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s LB lo canary m)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 n) s1 (Z_to_bv 64 D) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 fuzz_entryA) fc None m (seg_rom asegs))
    s LB.
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB st D n lo errv canary data kD.
  intros BD LEN NR DIN HR RF FCO AE LBL LBB NSEC ST CLO LO QAL QTOP SHZ SHR ERRC MI HPZ GS SG TPV RAV.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (am_stack_ok FI AI) as (TK1 & TK2 & TK3 & TK4).
  pose proof (bv_unsigned_in_range _ sp) as SPR. unfold bv_modulus in SPR.
  remember (bv_unsigned sp) as q eqn:Eq.
  assert (ESP : sp = Z_to_bv 64 q) by (subst q; symmetry; apply Z_to_bv_bv_unsigned).
  assert (AL16 : q = 16 * (q / 16)) by (clear - QAL; Z.div_mod_to_equations; lia).
  pose proof (fsb_ok FI) as (FB1 & FB2 & _ & FB4 & FB5).
  destruct (am_block_range FI AI s LB m _ HR DIN) as (DR1 & DR2 & DR3 & DR4 & DR5 & DR6 & DR7). cbn [blk_addr blk_size fst snd] in DR1, DR2, DR3, DR4, DR5, DR6, DR7.

  destruct data as [|b0 data']; [cbn in LEN; lia|].
  assert (BD0 : bytes_at asegs m D [b0]).
  { destruct BD as (B0 & B1 & BB). split; [exact B0|]. split; [cbn [length] in *; lia|]. intros i Hi. cbn [length] in Hi. assert (i = 0%nat) by lia. subst i. exact (BB 0%nat ltac:(cbn [length]; lia)). }
  assert (BDS : bytes_at asegs m (D + 1) data').
  { destruct BD as (B0 & B1 & BB). split; [lia|]. split; [cbn [length] in *; lia|]. intros i Hi.
    replace (D + 1 + Z.of_nat i) with (D + Z.of_nat (S i)) by lia. exact (BB (S i) ltac:(cbn [length]; lia)). }
  assert (LEN' : Z.of_nat (length data') = n - 1) by (cbn [length] in LEN; lia).
  pose proof (block_shw FI AI s LB m (kD, D, n) D n HR DIN ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)) as SHWD.
  rewrite ESP. change fuzz_entryA with fuzz_entryF.
  assert (LOF : lo <= q - 65536) by lia.
  eapply (aj_evt FI AI J).
  { eapply (frontF1 FI IC STACK_MALLOC_4 lo q (q / 16) st ra gp tp (Z_to_bv 64 n) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m
              CLO LOF AL16 ltac:(lia) RF (fs_call_ok_le FI st tp 6 1 FCO ltac:(lia)) (am_fsenv FI AI s LB m HR) D n b0);
      [exact ST| exact MI| exact AE| lia| exact SHWD| exact BD0| lia| lia| exact DR7]. }
  intros ms1 PO. unfold postF1 in PO.
  destruct PO as (q' & m1 & y0 & y1 & y2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & -> & INV1 & ICELLS & SHWP1 & MI1 & AE1 & RF1 & LIVE1 & MU1 & WM1 & FK1).

  pose proof (geomF FI st m RF) as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & FSB1 & FSB2 & FSB5).
  destruct (liveF FI st m RF _ LIVE1) as (LVF & LVS & LVL & LSUB).
  set (Fz := fuzzF FI st) in *. set (P := (Fz + 32)%Z).
  assert (HR1 : RHEAP_A FI AI s LB m1).
  { eapply (am_heap_frame FI AI s LB m m1 _ HR MU1 WM1).
    apply Forall_cons; [left; cbn [fst]; exact CLO|]. apply Forall_cons; [do 3 right; left; cbn [fst snd]; lia|].
    apply Forall_cons; [do 4 right; cbn [fst snd]; lia| apply Forall_nil]. }
  pose proof (apxF_of_munch_fkeep FI AI ASL s LB LB m m q lo st [] m m1 HR (fun b H => H) RF CLO ltac:(lia) MU1 WM1 FK1) as APF0.
  assert (APF01 : apxF FI AI WER LB q st m m1).
  { eapply (apxF_weaken FI AI); [exact APF0| intros x Hx; exact I| lia| intros b Hb; exact Hb| intros g Hg; exact Hg]. }
  clear APF0.
  destruct (fuzz_close s LB q lo st m m m1 canary HR CLO ltac:(lia) ltac:(lia) APF01 HPZ SHZ GS SG) as (_ & HPZ1 & SHZ1 & GS1 & SG1).
  assert (ERRC1 : rw_cells asegs m1 RERRNOA [C4 errv]).
  { apply (rw_cells_transport asegs _ m m1 _ _ ERRC MU1 WM1). unfold RERRNOA.
    cbn [disjoint_from cells_size csize Nat.add]. change (Z.of_nat 4) with 4.
    split; [lia|]. split; [lia|]. split; [| exact I]. left. unfold sh, SHADOW_OFF. clear - FB1. Z.div_mod_to_equations. lia. }
  assert (SHR1 : shr m1 (sh lo - sh lo mod 8) (sh q)).
  { apply (shr_apxF FI AI AMS WER LB q st m m1 _ _ (shr_sub m (sh lo - sh lo mod 8) (sh q + 8) (sh lo - sh lo mod 8) (sh q) SHR ltac:(lia) ltac:(lia)) APF01).
    - unfold sh, SHADOW_OFF. clear - CLO. Z.div_mod_to_equations. lia.
    - unfold sh, SHADOW_OFF. clear - SPR TK3 QTOP. Z.div_mod_to_equations. lia.
    - intros a Ha. cbn [outside]. split; [| exact I]. intros C. unfold A0_ERRNO, sh, SHADOW_OFF in *. clear - Ha CLO ACR C. Z.div_mod_to_equations. lia. }
  assert (BDS1 : bytes_at asegs m1 (D + 1) data').
  { apply (apxF_bytes_at FI AI WER LB q st m m1 _ _ APF01 BDS).
    - apply (fclient_range_block FI AI LB q st _ _ (kD, D, n) DIN); cbn [blk_addr blk_size fst snd]; lia.
    - cbn [disjoint_from]. split; [| exact I]. unfold A0_ERRNO. lia. }
  pose proof (block_shw FI AI s LB m1 (kD, D, n) (D + 1) (n - 1) HR1 DIN ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)) as SHWS1.

  assert (IVR : 0 <= fst (fst (initvF b0)) <= 1 /\ 0 <= snd (fst (initvF b0)) <= 11 /\ 0 <= snd (initvF b0) <= 1)
    by (unfold initvF; destruct (Z.land (bv_unsigned b0) 1 =? 0); cbn [fst snd]; lia).
  destruct IVR as (IVR1 & IVR2 & IVR3).
  destruct (pinit_parser m1 LB P _ _ _ ICELLS IVR1 IVR2 IVR3) as [PAR0 PAD0].
  set (t0p := t_fresh (fst (fst (initvF b0))) (snd (fst (initvF b0))) (snd (initvF b0))) in *.
  destruct (pp_stat_of_PZ GL_germ m1 canary errv HPZ1 ERRC1 GS1 SG1) as (ws & mws & cslack & WSL & WSOK & MTOK & GLOK & STAT1).
  destruct (fuzz_room FI AI s LB m1 t0p (n - 1) (2 * PZ_GMAX + 5) data' HR1 NSEC LBL LBB ltac:(lia) ltac:(unfold RKD; lia) eq_refl) as [BUD PBUD].
  pose proof INV1 as ((kq' & Hq32) & Hq & ST1 & _ & _ & FRhi1 & _).
  assert (CH1 : fpchain m1 (am_stack_top FI AI) q' (bv_unsigned (Z_to_bv 64 q)) [0x863f8]).
  { pose proof (proj1 (rw_cells_app asegs m1 (q + -72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 (Z_to_bv 64 n); C8 ra]) FRhi1) as [_ T2].
    replace (q + -72 + Z.of_nat (cells_size [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) with (q - 16) in T2 by (simpl_sizes; lia).
    pose proof (proj1 (rw_cells_app asegs m1 (q - 16) [C8 (Z_to_bv 64 n)] [C8 ra]) T2) as [T3 T4].
    replace (q - 16 + Z.of_nat (cells_size [C8 (Z_to_bv 64 n)])) with (q - 8) in T4 by (simpl_sizes; lia).
    pose proof (SysStep.rw_cells_bytes_at asegs _ _ _ T3) as B3. cbn [cells_bytes cbytes] in B3. rewrite app_nil_r in B3.
    pose proof (SysStep.rw_cells_bytes_at asegs _ _ _ T4) as B4. cbn [cells_bytes cbytes] in B4. rewrite app_nil_r in B4. rewrite RAV in B4.
    rewrite unsigned_lit by lia. cbn [fpchain]. unfold valid_frame, rd64.
    split; [split; [lia|]; split; [lia| clear - AL16; Z.div_mod_to_equations; lia]|]. split; [lia|].
    split; [split; [exact B4| lia]|]. split; [lia|].
    exists n. split; [split; [exact B3| lia]| intros (V1 & _); lia]. }
  subst tp.

  eapply (aj_bind FI AI J).
  { eapply PA with (lo := lo) (LBK := LB) (st := fs_next FI st 4) (P := P) (gmax := PZ_GMAX) (canary := canary) (ws := ws) (mws := mws)
                   (cslack := cslack) (GL := GL_germ) (t := t0p) (ras := [0x863f8]) (SRC := D + 1) (n := n - 1) (src := data').
    - exact HR1.
    - exact RF1.
    - exact (fs_call_ok_push FI st (fs_next FI st 4) (Z_to_bv 64 A0_TP) 5 _ FCO LIVE1).
    - exact AE1.
    - exact ST1.
    - exact CLO.
    - clear - LO Hq. lia.
    - clear - Hq32. Z.div_mod_to_equations. lia.
    - clear - Hq QTOP. lia.
    - exact MI1.
    - apply (lb_sub _ Fz 1024 _ _ LVF); unfold P; lia.
    - unfold P. clear - GF2 FSB2. lia.
    - unfold P. clear - EKF. Z.div_mod_to_equations. lia.
    - exact SHWP1.
    - exact PAR0.
    - unfold pp_sideA, t0p, t_fresh, pa_set_msg.
      cbn [pa_cur pa_A pa_len pa_cap pa_okm pa_bs pa_meth pa_uc pa_rm pa_sc pa_SA pa_slen pa_scap pa_sok pa_sbs pa_isreq pa_maj pa_min
           pa_ns pa_hs pa_X pa_ebw pa_elw pa_err pa_hack pa_pos pa_entp pa_clen pa_csz pa_esp pa_ub pa_UB].
      unfold POS_REQUEST_LINE_A, POS_RESPONSE_LINE_A, LMAX_A.
      split; [clear - IVR3; lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [lia|].
      split; [intros X; exfalso; exact (X eq_refl)|]. split; [clear - NR; lia|]. split; [clear - NR; lia|]. split; reflexivity.
    - unfold LMAX_A. cbn [pa_cap t0p t_fresh]. clear - NR. lia.
    - exact BUD.
    - intros sa LBa ta HPA. replace (pa_len FI AI t0p + (n - 1) - pa_cur FI AI t0p) with (n - 1) by (cbn [pa_len pa_cur t0p t_fresh]; lia).
      exact (PBUD sa LBa ta HPA).
    - intros b Hb. exact Hb.
    - exact (am_blocks_nodup FI AI s LB m1 HR1).
    - exact WSL.
    - exact WSOK.
    - exact MTOK.
    - lia.
    - exact GLOK.
    - exact GERM.
    - exact STAT1.
    - apply AMS. unfold a0_static. split; [lia|]. do 2 right; left. lia.
    - apply (shz_sub _ _ _ _ _ SHZ1); [lia|]. unfold sh, SHADOW_OFF. clear - Hq. Z.div_mod_to_equations. lia.
    - apply (shr_sub _ _ _ _ _ SHR1); [lia|]. unfold sh, SHADOW_OFF. clear - Hq. Z.div_mod_to_equations. lia.
    - exact CH1.
    - rewrite unsigned_lit by lia. unfold A0_TRACES. do 8 right; left; reflexivity.
    - rewrite unsigned_lit by lia. unfold A0_TRACES. do 9 right; left; reflexivity.
    - exact BDS1.
    - exact LEN'.
    - right. reflexivity.
    - lia.
    - left. right; left. exists (kD, D, n). split; [exact DIN|]. cbn [blk_addr blk_size fst snd]. lia.
    - exact SHWS1.
    - clear - DR4 ACR NR. lia.
    - unfold P. clear - DR7 GF1 GF2 NR. lia.
    - reflexivity.
    - reflexivity.
    - reflexivity. }

  intros s2_ LB2 ms2 PO2. destruct PO2 as (sa & LBa & ta & ma & HPA & APFa & PO2).
  destruct PO2 as (z0 & z1 & z2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & z3 & z4 & z5 & z6 & m2 & st2 & r & t2p & -> & MI2 & ST2 & AE2 & RF2 & LIVE2
                   & APF2 & HR2 & PAR2 & ISREQ2 & BSUB2 & ND2 & SCRIPT & TG6 & NOLEAK & STAT2 & SHWP2 & SHZ2 & SHR2 & RR).
  replace (ret_pc (Z_to_bv 64 550744)) with (Z_to_bv 64 550744) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  pose proof (apxF_trans FI AI _ LB q' (fs_next FI st 4) m1 ma m2 APFa APF2) as APF12.
  assert (LIVE2' : fs_live FI st2 = fs_newff FI st 4 :: fs_live FI st) by (rewrite LIVE2; exact LIVE1).

  assert (PIECES : forall a, Fz <= a < Fz + 32 \/ Fz + 536 <= a < Fz + 1024 \/ fuzzSF FI st <= a < fuzzSF FI st + 128 \/ a = fuzzFL FI st ->
             (exists g, In g (fs_live FI (fs_next FI st 4)) /\ in_pieces g a) /\ (a < P \/ P + 504 <= a) /\ 0x609000 <= a).
  { intros a Ha. split; [| clear - Ha EKF ESF EKB ESHB GF1 GF2 GF4 GF5 FSB1 FSB2 FSB5; unfold P; lia].
    destruct Ha as [Ha|[Ha|[Ha|Ha]]].
    - destruct LVF as (g & Hg & G1 & G2). exists g. split; [exact Hg|]. left. lia.
    - destruct LVF as (g & Hg & G1 & G2). exists g. split; [exact Hg|]. left. lia.
    - destruct LVS as (g & Hg & G1 & G2). exists g. split; [exact Hg|]. right; left. lia.
    - destruct LVL as (g & Hg & G1). exists g. split; [exact Hg|]. right; right. lia. }
  assert (INV2 : minvF FI lo q st ra (Z_to_bv 64 n) s1 s2 s3 s4 s5 s6 s7 q' m2 0).
  { apply (minvF_gagree (fun a => fclient FI AI LB q' (fs_next FI st 4) a /\ outside (pparse_WA P) a) lo q st ra _ _ _ _ _ _ _ _ q' m1 m2 0).
    - intros a Ha [Hc Ho]. exact (APF12 a Ha Hc Ho).
    - exact INV1.
    - intros a Ha. split; [left; lia|]. unfold pparse_WA. cbn [outside]. unfold P. clear - Ha Hq LO CLO GF2 FSB2 ACR. repeat split; lia.
    - intros a Ha. destruct (PIECES a Ha) as (X1 & X2 & X3). split; [do 4 right; exact X1|].
      unfold pparse_WA. cbn [outside]. clear - X2 X3. repeat split; lia.
    - exact ST2. }
  assert (PAD2 : rw_cells asegs m2 (P + 500) [C4 (wz 0)]).
  { apply (apxF_rw_cells FI AI _ LB q' (fs_next FI st 4) m1 m2 _ _ APF12 PAD0).
    - apply (fclient_range_lb FI AI). apply (lb_sub _ Fz 1024 _ _ LVF); unfold P; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
    - unfold pparse_WA. cbn [disjoint_from cells_size csize Nat.add]. change (Z.of_nat 4) with 4. unfold P. clear - GF1 FSB1. repeat split; lia. }

  destruct HPA as (A' & cap' & ok' & bs' & ETA & ALT & CAPR & _ & _).
  assert (TAF : pa_hs FI AI ta = [] /\ pa_len FI AI ta = n - 1 /\ pa_cur FI AI ta = 0
                /\ (length LBa = length LB + length (pa_blocks FI AI ta))%nat /\ am_nsec FI AI sa <= am_nsec FI AI s + 1).
  { rewrite ETA. unfold pa_set_msg, pa_blocks, t0p, t_fresh.
    cbn [pa_cur pa_A pa_len pa_cap pa_okm pa_bs pa_meth pa_uc pa_rm pa_sc pa_SA pa_slen pa_scap pa_sok pa_sbs pa_isreq pa_maj pa_min
         pa_ns pa_hs pa_X pa_ebw pa_elw pa_err pa_hack pa_pos pa_entp pa_clen pa_csz pa_esp pa_ub pa_UB hl_blocks map hdrs_blocks concat app okbA].
    split; [reflexivity|]. split; [lia|]. split; [reflexivity|].
    unfold t0p, t_fresh in ALT. cbn [pa_okm pa_A pa_cap pa_len] in ALT.
    destruct ALT as [(EOK & ELB & _ & _ & NS)|(k' & EOK & ELB & NS & _)]; subst ok' LBa.
    - cbn [okbA app length]. split; [lia| lia].
    - cbn [okbA app length lb_keepA]. split; [lia|]. rewrite NS. pose proof (HttpAllocA.nsec1_range (cap' + 1)). lia. }
  destruct TAF as (TA1 & TA2 & TA3 & TA4 & TA5).

  destruct PAR2 as (PSC & PMSG & CURR & PMETH & PURI & PRS & PSM & PVER & PHL & PENT & PCTL & PURL & UBO).
  destruct PMSG as (MBC & MOWN & _ & _ & _). destruct PSM as (SBC & SOWN & _ & _).
  destruct PMETH as (MC & MR). destruct PURI as (UCC & UCS). destruct PRS as (RSC & _). destruct PVER as ((vpad & VERC) & _).
  destruct PHL as (LC & FLC & FFC & DL & HS & ITEMS & _ & _ & _). destruct PCTL as (CTLC & _). destruct PURL as (UC & UR).
  assert (NSLEN : zlength (pa_ns FI AI t2p) < 2^40).
  { pose proof (hs_count m2 _ HS) as HC2. rewrite TA1, TA2, TA3 in TG6. unfold H_phdr.hsumA in TG6 at 2. cbn [fold_right] in TG6.
    apply (f_equal (@length _)) in ITEMS. rewrite !length_map in ITEMS. unfold zlength. rewrite ITEMS. clear - HC2 TG6 NR. lia. }

  eapply (aj_evt FI AI J).
  { eapply (midF FI q st gp (Z_to_bv 64 A0_TP) s8 s9 s10 s11 F fc q' m2). }
  intros ms3 ->.

  assert (LVP2 : lb (fs_live FI st2) P 440).
  { rewrite LIVE2. apply (lb_sub _ Fz 1024 _ _ LVF); unfold P; lia. }
  assert (BSUB2' := BSUB2). assert (ND2' := ND2).
  unfold pa_blocks, hl_blocks in BSUB2', ND2'. rewrite <- !app_assoc in BSUB2', ND2'.
  eapply (aj_bind FI AI J).
  { eapply DW with (lo := lo) (LBK := LB) (st := st2) (P := P) (ns := pa_ns FI AI t2p) (hs := pa_hs FI AI t2p)
                   (MBb := okbA FI AI (pa_okm FI AI t2p) (pa_A FI AI t2p) (pa_cap FI AI t2p))
                   (SBb := okbA FI AI (pa_sok FI AI t2p) (pa_SA FI AI t2p) (pa_scap FI AI t2p)) (UB := pa_UB FI AI t2p)
                   (meth := pa_meth FI AI t2p) (fcmp := httpmsg_compare_entryA) (U := pa_ub FI AI t2p)
                   (Am := pa_A FI AI t2p) (lm := pa_len FI AI t2p) (cm := pa_cap FI AI t2p)
                   (As := pa_SA FI AI t2p) (ls := pa_slen FI AI t2p) (cs := pa_scap FI AI t2p).
    - exact HR2.
    - exact RF2.
    - exact AE2.
    - exact ST2.
    - exact CLO.
    - unfold A0_RT_STACK. clear - LO Hq. lia.
    - clear - Hq32. Z.div_mod_to_equations. lia.
    - clear - Hq QTOP. lia.
    - exact MI2.
    - exact MC.
    - clear - MR. lia.
    - exact LC.
    - exact FLC.
    - replace (P + 288 + 80) with (P + 368) by lia. exact FFC.
    - exact DL.
    - exact HS.
    - exact ITEMS.
    - exact NSLEN.
    - unfold httpmsg_compare_entryA. lia.
    - exact MBC.
    - apply (okbA_mbo FI AI). intros E. rewrite E in MOWN. cbn [mownA] in MOWN. exact (proj1 MOWN).
    - exact SBC.
    - apply (okbA_mbo FI AI). intros E. rewrite E in SOWN. cbn [mownA] in SOWN. exact (proj1 SOWN).
    - exact UC.
    - exact UBO.
    - right. exact LVP2.
    - unfold P. clear - GF2 FSB2. lia.
    - unfold P. clear - EKF. Z.div_mod_to_equations. lia.
    - eapply shw_sub; [exact SHWP2| lia| lia| lia].
    - exact BSUB2'.
    - exact ND2'.
    - reflexivity. }
  intros s3_ LB3 ms3 PO3.
  destruct PO3 as (u0 & u1 & u2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & u3 & u4 & u5 & u6 & m3 & -> & MI3 & ST3 & AE3 & RF3 & APX3 & HR3 & KSUB3 & INCL3 & GONE3
                   & IC3 & LC3 & FLC3 & FF3 & MBC3 & SBC3 & UC3 & SHWP3 & NS3).
  replace (ret_pc (Z_to_bv 64 0x86760)) with (Z_to_bv 64 0x86760) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

  assert (INV3 : minvF FI lo q st ra (Z_to_bv 64 n) s1 s2 s3 s4 s5 s6 s7 q' m3 0).
  { apply (minvF_gagree (fun a => aclient FI AI LB q' a /\ outside [(P, P + 8); (P + 232, P + 264); (P + 288, P + 384); (P + 400, P + 432)]%Z a)
                        lo q st ra _ _ _ _ _ _ _ _ q' m2 m3 0).
    - intros a Ha [Hc Ho]. exact (APX3 a Ha Hc Ho).
    - exact INV2.
    - intros a Ha. split; [left; lia|]. cbn [outside]. unfold P. clear - Ha Hq LO CLO GF2 FSB2 ACR. repeat split; lia.
    - intros a Ha. destruct (PIECES a Ha) as (_ & X2 & X3). split.
      + do 3 right. clear - Ha EKF ESF EKB ESHB GF1 GF2 GF4 GF5 FSB1 FSB2 FSB5. fold Fz in Ha. lia.
      + cbn [outside]. clear - X2. repeat split; lia.
    - exact ST3. }
  assert (TP3 : forall X cs, rw_cells asegs m2 X cs -> P <= X -> X + Z.of_nat (cells_size cs) <= P + 504 ->
            disjoint_from [(P, P + 8); (P + 232, P + 264); (P + 288, P + 384); (P + 400, P + 432)]%Z X (Z.of_nat (cells_size cs)) -> rw_cells asegs m3 X cs).
  { intros X cs H H1 H2 H3. apply (apx_rw_cells FI AI _ LB q' m2 m3 X cs APX3 H); [| exact H3].
    apply (aclient_range_fs FI AI); unfold P in *; clear - H1 H2 GF1 GF2; lia. }
  assert (ERR3 : exists ev3, rw_cells asegs m3 RERRNOA [C4 ev3]).
  { destruct STAT2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (ev2 & E2) & _).
    exists ev2. apply (apx_rw_cells FI AI _ LB q' m2 m3 _ _ APX3 E2).
    - apply (aclient_range_static FI AI LB q' _ _ 0x5e7508 0x5e7510); [apply AMS; unfold a0_static; split; [lia|]; do 4 right; left; lia| unfold A0_ERRNO; lia| unfold A0_ERRNO; cbn; lia].
    - unfold A0_ERRNO, P. cbn [disjoint_from cells_size csize Nat.add]. change (Z.of_nat 4) with 4. clear - GF1 FSB1. repeat split; lia. }

  assert (PCH3 : exists jp, rw_cells asegs m3 P [CB 504 jp]).
  { unfold mbuf_cells, lhead_cells, fl_cells, p_ctl_cells in *.
    apply TP3 in UCC; [| lia| rewrite UCS; lia| rewrite UCS; cbn [disjoint_from]; change (Z.of_nat 216) with 216; repeat split; lia].
    apply TP3 in RSC; [| lia| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; repeat split; lia].
    apply TP3 in VERC; [| lia| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; repeat split; lia].
    apply TP3 in PENT; [| lia| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; repeat split; lia].
    apply TP3 in CTLC; [| lia| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; repeat split; lia].
    apply TP3 in PSC; [| lia| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; repeat split; lia].
    apply TP3 in PAD2; [| lia| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; repeat split; lia].
    replace (P + 288 + 80) with (P + 368) in FF3 by lia.
    eapply (pobj_join m3 P); [exact IC3| exact UCC| exact UCS| exact RSC| exact SBC3| exact VERC| exact LC3| exact FLC3| exact FF3| exact PENT| exact MBC3| exact UC3| exact CTLC| exact PSC| exact PAD2]. }
  destruct PCH3 as (jp3 & PCH3).

  eapply (aj_evt FI AI J).
  { eapply (exitF FI SET_SHADOW_F5 lo q (q / 16) st ra gp (Z_to_bv 64 A0_TP) (Z_to_bv 64 n) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m
              CLO LOF AL16 ltac:(lia) RF q' m3 0 jp3 st2); [exact INV3| exact PCH3| exact MI3| exact AE3| exact RF3| exact LIVE2']. }
  intros ms4 PO4. unfold postF in PO4.
  destruct PO4 as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & m4 & st4 & -> & MU4 & WM4 & MI4 & LIVE4 & RF4 & ST4 & AE4).

  assert (NFC : forall a, Fz <= a < Fz + 1024 -> ~ fclient FI AI LB q st a).
  { intros a Ha. apply (new_frame_not_fclient FI AI ASL s LB LB m q st 4 m Fz (fuzzSF FI st) (fuzzFL FI st) HR (fun b H => H) ltac:(lia) RF ltac:(lia) eq_refl eq_refl eq_refl a).
    left. cbn [FB_of]. exact Ha. }
  assert (APF12' : apxF FI AI WER LB q st m1 m2).
  { apply (apxF_narrow (pparse_WA P) WER LB q st m1 m2).
    - eapply (apxF_weaken FI AI); [exact APF12| intros x Hx; exact Hx| lia| intros b Hb; exact Hb| exact LSUB].
    - intros a Hc Ho. unfold pparse_WA. cbn [outside] in *. split; [intros C; apply (NFC a); [unfold P in C; lia| exact Hc]| exact Ho]. }
  assert (APF23 : apxF FI AI WER LB q st m2 m3).
  { apply (apxF_narrow [(P, P + 8); (P + 232, P + 264); (P + 288, P + 384); (P + 400, P + 432)]%Z WER LB q st m2 m3).
    - apply (apxF_of_apx FI AI _ LB LB q q' st st2 m2 m2 m3 APX3 RF2 ltac:(lia) (fun b H => H)). intros g Hg. rewrite LIVE2'. right. exact Hg.
    - intros a Hc Ho. cbn [outside] in *.
      assert (NP : ~ (P <= a < P + 504)) by (intros C; apply (NFC a); [unfold P in C; lia| exact Hc]).
      clear - NP. repeat split; lia. }
  pose proof (apxF_epilogue FI AI ASL s LB LB m m q lo st 4 Fz (fuzzSF FI st) (fuzzFL FI st) WER m3 m4 HR (fun b H => H) RF CLO ltac:(lia) ltac:(lia)
                eq_refl eq_refl eq_refl MU4 WM4) as APF34.
  pose proof (apxF_trans FI AI _ _ _ _ _ _ _ APF01 (apxF_trans FI AI _ _ _ _ _ _ _ APF12' (apxF_trans FI AI _ _ _ _ _ _ _ APF23 APF34))) as APF.
  destruct (fuzz_close s LB q lo st m m m4 canary HR CLO ltac:(lia) ltac:(lia) APF HPZ SHZ GS SG) as (PK & HPZ4 & SHZ4 & GS4 & SG4).

  assert (Q2b : forall b, In b LB3 -> In b LB).
  { intros b Hb. pose proof (INCL3 b Hb) as Hb2.
    assert (LEN2 : (length LB2 <= length (pa_blocks FI AI t2p ++ LB))%nat) by (rewrite length_app; clear - NOLEAK TA4; lia).
    pose proof (noleak_incl (pa_blocks FI AI t2p ++ LB) LB2 ND2 BSUB2 LEN2 b Hb2) as Hb3.
    apply in_app_or in Hb3. destruct Hb3 as [OWN|OK]; [| exact OK]. exfalso.
    apply (GONE3 b); [| exact Hb]. unfold pa_blocks, hl_blocks in OWN. rewrite <- !app_assoc in OWN. exact OWN. }
  assert (Q1 : am_nsec FI AI s3_ <= am_nsec FI AI s + FZ_NSEC).
  { destruct SCRIPT as (N1 & LB1' & N2 & LB2' & dd & kk & dd2 & _ & _ & _ & KR & _ & _ & _ & CNT).
    rewrite TA1 in CNT. rewrite TA1, TA2, TA3 in TG6. unfold H_phdr.hsumA in TG6 at 2. cbn [fold_right] in TG6.
    rewrite NS3. unfold FZ_NSEC.
    apply (fuzz_q1 FI AI m2 (pa_hs FI AI t2p) (am_nsec FI AI s) (am_nsec FI AI sa) (am_nsec FI AI s2_) kk (n - 1) HS TA5 KR ltac:(lia) ltac:(lia) CNT). }
  assert (ERR4 : exists ev4, rw_cells asegs m4 RERRNOA [C4 ev4]).
  { destruct ERR3 as (ev3 & E3). exists ev3. apply (rw_cells_transport asegs _ m3 m4 _ _ E3 MU4 WM4). unfold WEF, RERRNOA.
    cbn [disjoint_from cells_size csize Nat.add]. change (Z.of_nat 4) with 4. fold Fz.
    clear - CLO ACR EKF ESF EKB ESHB GF1 GF2 GF4 GF5 FSB1 FSB2 FSB5. repeat split; lia. }
  assert (HR4 : RHEAP_A FI AI s3_ LB3 m4).
  { eapply (am_heap_frame FI AI s3_ LB3 m3 m4 _ HR3 MU4 WM4). unfold WEF. fold Fz.
    apply Forall_cons; [left; cbn [fst]; exact CLO|].
    apply Forall_cons; [do 3 right; left; cbn [fst snd]; clear - GF1 GF2; lia|].
    apply Forall_cons; [do 4 right; cbn [fst snd]; clear - EKF ESF EKB ESHB GF1 GF2; lia|].
    apply Forall_cons; [do 3 right; left; cbn [fst snd]; clear - GF4 GF5; lia| apply Forall_nil]. }
  apply (aj_ret FI AI J). unfold fuzz_one_postA.
  exists w0, w1, w2, e1, e2, e3, e4, e5, e6, e7, w3, w4, w5, w6, m4, st4.
  split; [reflexivity|]. split; [exact MI4|]. split; [rewrite unsigned_lit by lia; exact ST4|]. split; [exact AE4|]. split; [exact RF4|].
  split; [rewrite unsigned_lit by lia; exact PK|]. split; [exact LIVE4|]. split; [exact HR4|].
  split; [exact KSUB3|]. split; [exact Q2b|]. split; [exact Q1|]. split; [exact HPZ4|]. split; [exact ERR4|].
  split; [rewrite unsigned_lit by lia; exact SHZ4|]. split; [exact GS4| exact SG4].
Qed.
End ARM1.

#[using="IC AC ASL AMS STACK_MALLOC_0 STACK_MALLOC_1 STACK_MALLOC_2 STACK_MALLOC_3 STACK_MALLOC_4 SET_SHADOW_F5"] Theorem fuzz_one_spec_sec : fuzz_one_stmtA FI AI J PZ.
Proof.
  unfold fuzz_one_stmtA.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB st D n lo errv canary data.
  intros BD LEN NR DSRC HR RF FCO AE LBL LBB NSEC ST CLO LO QAL QTOP SHZ SHR SHW1 SHW2 ERRC MI HPZ GS SG TPV -> -> -> RAV FRM.
  assert (ARM0 : n = 0 -> AJ FI AI J (fuzz_one_postA FI AI PZ ra sp gp tp (Z_to_bv 64 n) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s LB lo canary m)
            (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 n) s1 (Z_to_bv 64 D) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 fuzz_entryA) fc None m (seg_rom asegs)) s LB).
  { intros ->. exact (fuzz_n0 ra sp gp tp t0 t1 t2 (Z_to_bv 64 0) s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB st D lo errv canary
                      HR RF FCO AE ST CLO LO QAL QTOP SHZ ERRC MI HPZ GS SG). }
  destruct DSRC as [(N0 & _)|(kD & DIN)]; [exact (ARM0 N0)|].
  destruct (Z.eq_dec n 0) as [N0|N1]; [exact (ARM0 N0)|].
  unfold PARSER_STACK_A in LO.
  exact (fuzz_n1 (pappend_spec_A IC FI AI J AC ASL AMS (pparse_spec_A HC IC FI AI J AC ASL AMS STACK_MALLOC_0 STACK_MALLOC_1 STACK_MALLOC_2 STACK_MALLOC_3 SET_SHADOW_F5))
                 (httpmsg_destroy_specW_A IC FI AI J AC ASL AMS)
                 (germ_spec_A IC FI AI AMS STACK_MALLOC_2 STACK_MALLOC_3 SET_SHADOW_F5)
                 ra sp gp tp t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB st D n lo errv canary data kD
                 BD LEN ltac:(lia) DIN HR RF FCO AE LBL LBB NSEC ST CLO LO QAL QTOP SHZ SHR ERRC MI HPZ GS SG TPV RAV).
Qed.
End W.

Theorem fuzz_one_spec_A : forall {HC : HasCeiling} {HG : HasGuard} (IC : icpt_contracts) (FI : fs_if) (AI : am_if FI) (J : a0_judg FI AI)
    (AC : am_contracts FI AI J)
    (ASL : forall lo hi, am_static FI AI lo hi -> a0_static lo hi) (AMS : forall lo hi, a0_static lo hi -> am_static FI AI lo hi)
    (SM0 : stack_malloc_stmt FI 0) (SM1 : stack_malloc_stmt FI 1) (SM2 : stack_malloc_stmt FI 2) (SM3 : stack_malloc_stmt FI 3)
    (SM4 : stack_malloc_stmt FI 4) (F5 : set_shadow_f5_stmt),
  fuzz_one_stmtA FI AI J PZDef.PZ.
Proof. intros. eapply fuzz_one_spec_sec; eassumption. Qed.

