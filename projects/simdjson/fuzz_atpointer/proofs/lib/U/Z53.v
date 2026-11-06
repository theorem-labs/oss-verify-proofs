(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Image Z11w Z119 ITree Nodes Decode Arr FP MonadX Z10q.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Malloc Require Import Zei Zf6.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.MallocU Require Import Zhy Zhz Zi1.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim StrFun STree Malloc Monad Stdio Zpb Z3o Target Prog AtpImpl.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Zpp.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.U Require Import Layout Exit Zfr Zq5 Sj_kit Sj_new Zq6 Zpu Zpo Zpr Zpn Zpq Zpz Z9n Z9p.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpf Zpg Zph SjTape Zpk.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Zp8.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Zvw.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.U Require Import Zwn Zpw Z6n Z6o.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.U Require Import Z4d Z4j Z51.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.U Require Z5l Z6d.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition doc_cap (d : list Z) : Z := Z.max (zlength (atp_doc d)) 32.

Definition gate_post (sp0 : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra : word) (F : bvmap 5 word)
    (s : PState) (LB : list block) (lo B D : Z) (d : list Z) (m0 : mem) (bv : bptr) (A cap : Z) (jr : list byte)
    (psb ptp pim pix poc pia : bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7 xs2 xs3 t3 t4 t5 t6 F' fc' m' (errv' : word)
                    (IMPL IDX OC IA TAPE SBUF : Z) (r : word) (jg jl jo jn j105 j121 j161 jr20 j225 : list byte)
                    (vptr nsi nxt capv md bufv lenv docv : word) (b48 b49 : byte) (p12 p28 p50 : list byte),
    ms' = MS (mkR x1 (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7 xs2 xs3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (Z_to_bv 64 0x2733c) fc' None m' (seg_rom usegs)
    /\ frm0 fc'
    /\ mem_inv usegs m' /\ stk usegs m' lo sp0 /\ rw_cells usegs m' LX_ERRNO [C4 errv'] /\ rauxv_ok m' B
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ RHEAP s' ((pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, 4 * (roundup64 (doc_cap d) + 9)) :: (pim, IMPL, 96)
                 :: (ptp, TAPE, 8 * roundup64 (doc_cap d + 3)) :: (psb, SBUF, roundup64 (5 * (doc_cap d / 3) + 64)) :: (bv, A, 16 * cap) :: LB) m'
    /\ lx_pres LB (sp0 + 272) [LXW_SJ] m0 m' /\ sj_statics m' true /\ payload_ok m' LB D d
    /\ vrep m' (sp0 + 184) A (cap, Z.of_nat (atp_P d), Some bv) (atp_els D d) jr
    /\ rw_cells usegs m' (sp0 + 80) (res_cells (sp0 + 128) r jr20)
    /\ s2_okres TAPE SBUF (roundup64 (doc_cap d + 3)) (roundup64 (5 * (doc_cap d / 3) + 64)) r m'
    /\ rblock_range TAPE (8 * roundup64 (doc_cap d + 3)) /\ rblock_range SBUF (roundup64 (5 * (doc_cap d / 3) + 64))
    /\ rw_cells usegs m' (sp0 + 104) [C1 (Z_to_bv 8 0); CB 7 j105]
    /\ rw_cells usegs m' (sp0 + 112) [C8 (Z_to_bv 64 IMPL)]
    /\ rw_cells usegs m' (sp0 + 120) [C1 (Z_to_bv 8 0); CB 3 j121; C4 (Z_to_bv 64 12)]
    /\ rw_cells usegs m' (sp0 + 128) [C8 (Z_to_bv 64 TAPE); C8 (Z_to_bv 64 SBUF); C8 (Z_to_bv 64 (doc_cap d))]
    /\ rw_cells usegs m' (sp0 + 152) (p48_cells (Z_to_bv 8 0) j161 (Z_to_bv 64 0) (Z_to_bv 64 0))
    /\ rw_cells usegs m' IMPL (impl_cells16 vptr nsi p12 (Z_to_bv 64 IDX) nxt p28 capv md b48 b49 p50 (Z_to_bv 64 OC) (Z_to_bv 64 IA) bufv lenv docv)
    /\ vptr = Z_to_bv 64 SJ_DPI_VPTR
    /\ rw_cells usegs m' sp0 [CB 24 jg] /\ rw_cells usegs m' (sp0 + 24) [CB 16 jl] /\ rw_cells usegs m' (sp0 + 40) [CB 24 jo] /\ rw_cells usegs m' (sp0 + 64) [CB 16 jn]
    /\ rw_cells usegs m' (sp0 + 208) [C8 (Z_to_bv 64 (D + zlength d)); C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 7 j225]
    /\ rw_cells usegs m' (sp0 + 232) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma atp_els_shape : forall D d, exists P0 e1 rest,
  atp_els D d = (P0, zlength (atp_s0 d)) :: e1 :: rest /\ (P0 = 0 /\ atp_s0 d = [] \/ P0 = D + Z.of_nat 0) /\ atp_s0 d = firstn (length (atp_s0 d)) d.
Proof.
  intros D d. unfold atp_els, atp_P, atp_s0.
  pose proof (poffs_length d) as PL. pose proof (poffs_parts d) as PP.
  destruct (poffs d) as [|[o0 n0] tl] eqn:EP.
  - cbn in PP. rewrite <- PP. cbn. exists 0, (0, 0), []. split; [reflexivity|]. split; [left; split; reflexivity| reflexivity].
  - assert (O0 : o0 = 0%nat).
    { rewrite poffs_eq in EP. destruct d as [|c l]; [discriminate|]. rewrite poffs_of_unfold in EP. destruct (find_sep (c :: l)); congruence. }
    subst o0. rewrite <- PP. cbn [map nth fst snd skipn].
    assert (LN0 : (n0 <= length d)%nat) by (pose proof (poffs_bound d (0%nat, n0) ltac:(rewrite EP; left; reflexivity)) as B; cbn in B; lia).
    assert (ZL : zlength (firstn n0 d) = Z.of_nat n0) by (unfold zlength; rewrite firstn_length; lia).
    rewrite ZL. replace (length (firstn n0 d)) with n0 by (rewrite firstn_length; clear - LN0; lia).
    destruct tl as [|e1 tl'].
    + cbn [length Nat.max Nat.sub repeat map app pview fst snd]. do 3 eexists. split; [reflexivity|]. split; [right; reflexivity| reflexivity].
    + cbn [map app]. do 3 eexists. split; [reflexivity|]. split; [right; reflexivity| reflexivity].
Qed.

Ltac readdr H e := lazymatch type of H with rw_cells _ _ ?a _ => replace a with e in H by lia end.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.
  Hypothesis S2 : stage2t_stmt.

  Lemma lftoi_parse_cps : forall {R} (k : bptr -> bptr -> bptr -> bptr -> bptr -> bptr -> M PState R) (Q : R -> PState -> machine_state -> Prop)
      (x1 gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (s0 s1 s2 s3 ra : word)
      (F : bvmap 5 word) (fc : bv 32) (m0 m : mem) (s00 s : PState) (LB : list block) (sp0 lo B D : Z) (d : list Z) (init : bool) (errv : word)
      (A cap : Z) (bv : bptr) (jr : list byte) (jg jl jo jn c104 c112 c120 c128 c136 j144 jr0 jr8 jr16 jr20 j225 : list byte),

    RHEAP s00 LB m0 -> lx_statics m0 ->

    RHEAP s ((bv, A, 16 * cap) :: LB) m -> rauxv_ok m B -> sp0 + 272 <= B -> B < 2^63 ->
    stk usegs m lo sp0 -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= sp0 + 272 - LX_FUZZ_STACK ->
    rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m -> (sp0 + 272) mod 16 = 0 -> frm0 fc ->
    ps_fa s = ps_fa s00 -> ps_so s = ps_so s00 ->
    vrep m (sp0 + 184) A (cap, Z.of_nat (atp_P d), Some bv) (atp_els D d) jr -> cap < 2^26 ->
    lx_pres LB (sp0 + 272) [LXW_SJ] m0 m -> sj_statics m init -> payload_ok m LB D d ->
    rw_cells usegs m sp0 [CB 24 jg] -> rw_cells usegs m (sp0 + 24) [CB 16 jl] -> rw_cells usegs m (sp0 + 40) [CB 24 jo] -> rw_cells usegs m (sp0 + 64) [CB 16 jn] ->
    rw_cells usegs m (sp0 + 80) [CB 8 jr0; CB 8 jr8; CB 4 jr16; CB 4 jr20] ->
    rw_cells usegs m (sp0 + 104) [CB 8 c104; CB 8 c112; CB 8 c120; CB 8 c128; CB 8 c136; CB 40 j144] ->
    rw_cells usegs m (sp0 + 208) [C8 (Z_to_bv 64 (D + zlength d)); C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 7 j225] ->
    rw_cells usegs m (sp0 + 232) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    (forall psb ptp pim pix poc pia s' ms',
        gate_post sp0 gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra F s00 LB lo B D d m0 bv A cap jr psb ptp pim pix poc pia s' ms' ->
        implM usegs (k psb ptp pim pix poc pia) s' Q ms') ->
    implM usegs
      (mbind (if zlength (atp_s0 d) <=? 1048512 then mbind (newnt lops (zlength (atp_s0 d) + 64)) (fun p => mret (Some p)) else mret None) (fun cpo =>
       mbind (newnt lops (roundup64 (5 * (Z.max (zlength (atp_doc d)) 32 / 3) + 64))) (fun sb =>
       mbind (newnt lops (8 * roundup64 (Z.max (zlength (atp_doc d)) 32 + 3))) (fun tp =>
       mbind (newnt lops 96) (fun im =>
       mbind (newnt lops (4 * (roundup64 (Z.max (zlength (atp_doc d)) 32) + 9))) (fun ix =>
       mbind (newnt lops 8192) (fun oc =>
       mbind (newnt lops 1024) (fun ia =>
       mbind (parse_model (Zp8.strip_bom (atp_doc d))) (fun _ =>
       mbind (match cpo with Some p => del lops p | None => mret tt end) (fun _ => k sb tp im ix oc ia))))))))))
      s Q
      (MS (mkR x1 (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 16) s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x27258) fc None m (seg_rom usegs)).
  Proof.
    intros until j225.
    intros HEAP00 LXS0 HEAP AUX QB B63 ST CEIL GLO LO ERR MI AL16 FRM FA SO VR CAPB PRES SJS PL GSO LEAF OUT ROOT RES PARS XFD SAVE HK.
    unfold LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK, GLOBALS_TOP in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    assert (ELX : LX_ERRNO = 606604) by reflexivity. rewrite ELX in ERR.
    pose proof PL as (PB & PRNG & D0 & DN & DLEN & PIN).
    assert (ZD : zlength d = Z.of_nat (length d)) by reflexivity. pose proof DLEN as DLEN'. change (2^26) with 67108864 in DLEN'.
    assert (LBL : length (to_bytes d) = length d) by apply to_bytes_length.
    pose proof (atp_s0_len d) as S0L. pose proof (atp_doc_len d) as [DCL DCP]. unfold SJ_PADMAX in DCP.
    remember (zlength (atp_s0 d)) as len0 eqn:Elen0.
    assert (LEN0 : 0 <= len0) by (subst len0; unfold zlength; lia).

    pose proof (rw_cells_merge usegs m (sp0 + 104) [] _ [] ltac:(rewrite app_nil_r; exact PARS)) as PARS'. cbn [cells_size csize cells_bytes cbytes app Nat.add] in PARS'. clear PARS.
    apply (rw_cells_split_CB usegs _ _ [] 80 _ [] [1;7; 8; 1;3;4; 8;8;8; 8;1;7;8;8]%nat) in PARS'; [|reflexivity]. cbn [mk_CB_cells app] in PARS'.
    set (j105 := take 7 (drop 1 (c104 ++ c112 ++ c120 ++ c128 ++ c136 ++ j144 ++ []))) in PARS'.
    set (j121 := take 3 (drop 1 (drop 8 (drop 7 (drop 1 (c104 ++ c112 ++ c120 ++ c128 ++ c136 ++ j144 ++ [])))))) in PARS'.
    set (j161 := take 7 (drop 1 (drop 8 (drop 8 (drop 8 (drop 8 (drop 4 (drop 3 (drop 1 (drop 8 (drop 7 (drop 1 (c104 ++ c112 ++ c120 ++ c128 ++ c136 ++ j144 ++ []))))))))))))) in PARS'.

    destruct (atp_els_shape D d) as (P0 & e1 & rest & EE & HP0 & HS0). rewrite <- Elen0 in EE. rewrite EE in VR.
    destruct VR as (ELS & SZ & SV & BLK). pose proof BLK as BLK'. unfold vblk in BLK'. destruct BLK' as (BE & BJ & BR & C1).
    pose proof BR as (A0 & _ & _ & AC & AS). unfold OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec.Malloc.MCEIL in AC.
    destruct (rw_cells_split_at1 _ _ _ 2%nat BE) as [BE2 BER]. cbn [velts fst snd firstn skipn cells_size csize Nat.add] in BE2, BER. hide BER.
    assert (P0R : 0 <= P0 < 2^64) by (destruct HP0 as [[-> _] | ->]; lia).
    assert (BLB : forall a, in_block LB a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP ltac:(right; exact Hb)) as (_ & _ & _ & BC & _).
      unfold OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec.Malloc.MCEIL in BC. lia. }
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client LB (sp0 + 272) [LXW_SJ] a -> outside [(sp0, sp0 + 272)] a).
    { intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
    pose proof (munch_refl [(sp0, sp0 + 272)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof BR as (_ & A16 & _).
    hide BJ. hide BE.
    unfold implM. iprefix.

    step. hstep. hstep. hstep. hstep. step. zstep. hstep. hstep. hstep. hstep. hstep. hstep. hstep.

    step. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
    zstep. rewrite (Z5l.land7_mod8 A) by lia. step. if_false.
    step. step. zstep. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.

    destruct (rw_cells_split_at1 _ _ _ 2%nat PARS') as [PA0 Q1]. cbn [firstn skipn cells_size csize Nat.add] in PA0, Q1.
    destruct (rw_cells_split_at1 _ _ _ 1%nat Q1) as [PIMPL Q2]. cbn [firstn skipn cells_size csize Nat.add] in PIMPL, Q2.
    destruct (rw_cells_split_at1 _ _ _ 3%nat Q2) as [PA16 Q3]. cbn [firstn skipn cells_size csize Nat.add] in PA16, Q3.
    destruct (rw_cells_split_at1 _ _ _ 3%nat Q3) as [DOCC P48]. cbn [firstn skipn cells_size csize Nat.add] in DOCC, P48.
    clear PARS' Q1 Q2 Q3.
    readdr PIMPL (sp0 + 104 + 8). readdr PA16 (sp0 + 120). readdr DOCC (sp0 + 104 + 24). readdr P48 (sp0 + 104 + 48).

    pose proof (agree_on_of_munch _ _ _ MU WM) as AG1.
    assert (HEAP1 : RHEAP s ((bv, A, 16 * cap) :: LB) m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (PRES1 : lx_pres LB (sp0 + 272) [LXW_SJ] m0 m1).
    { eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]. }
    assert (SJS1 : sj_statics m1 init).
    { eapply sj_statics_agree; [exact AG1| | exact SJS]. intros a Ha. unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha. cbn [outside]; split; [lia| exact I]. }
    assert (PL1 : payload_ok m1 LB D d).
    { eapply payload_ok_agree; [exact AG1| exact PL|]. intros b a Hb Ha. pose proof (LH_block_range _ _ _ _ HEAP00 Hb) as (_ & _ & _ & BC & _).
      unfold OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec.Malloc.MCEIL in BC. cbn [outside]. split; [lia| exact I]. }
    assert (LXS1 : lx_statics m1).
    { eapply lx_statics_agree; [exact (agree_of_lx_pres _ _ _ _ _ PRES1)| | exact LXS0]. intros a Ha. apply lxs_addr_client; [exact Ha|].
      pose proof (lxs_addr_lt a Ha) as [R1 _]. unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, SJ_GOT_NOTHROW, SJ_IMPL_VT24, SJ_DPI_VPTR in Ha.
      unfold LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI. cbn [rin_ivs fst snd]. clear - Ha. lia. }
    pose proof LXS1 as (_ & _ & GOT1 & VT241 & VTD1).
    unhide BJ. unhide BER.
    apply (vblk_agree _ _ _ _ _ _ _ _ _ AG1) in BLK; [| intros a _ Ha; cbn [outside]; clear - Ha AC CEIL LO; lia| exact ELS| lia].
    clear BJ BER BE MU WM AG1.
    if_cases KB; zify_cond KB.
    -
      assert (EDOC : atp_doc d = []) by (unfold atp_doc; rewrite <- Elen0; replace (len0 <=? SJ_PADMAX) with false by (symmetry; apply Z.leb_gt; unfold SJ_PADMAX; lia); reflexivity).
      replace (len0 <=? 1048512) with false by (symmetry; apply Z.leb_gt; lia).
      assert (CAPD : doc_cap d = 32) by (unfold doc_cap; rewrite EDOC; reflexivity).
      rewrite EDOC. change (zlength (@nil Z)) with 0.

      step. step. step. step. step. step. step.
      replace (Z_to_bv 64 (sp0 + 128)) with (Z_to_bv 64 (sp0 + 104 + 24)) by (f_equal; lia).
      ihere. to_implM. apply implM_ret_bind.
      eapply (pid_front_cps HM) with (B := B) (lo := lo) (SRET := sp0 + 80) (PARSER := sp0 + 104) (init := init);
        [exact HEAP1| exact AUX1| lia| exact ST| exact CEIL'| unfold GLOBALS_TOP; lia| unfold SJ_OPNEW_STACK, RMALLOC_STACK; lia
        | rewrite ELX; eassumption| assumption| lia| lia| lia| lia
        | exact (conj GOT1 (conj VT241 VTD1))| exact SJS1| exact PIMPL| exact DOCC| exact P48|].
      intros psb ptp pim pix poc pia st2 ms2 MID.
      eapply pid_null_cps with (B := B) (lo := lo);
        [exact MID| exact HEAP1| exact FRM| lia| exact B63| exact CEIL'| unfold GLOBALS_TOP; lia| unfold SJ_S2_STACK, SJ_S2_FRAMES, RMALLOC_STACK; lia| lia
        | lia| lia| lia| clear - AL16; lia| exact RES|].
      intros st3 ms3 (IMPL & IDX & OC & IA & TAPE & SBUF & PO). unfold hpostF in PO.
      destruct PO as (u5 & u6 & u7 & u10 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & F' & fc' & m3
                      & -> & FRM3 & MI3 & ST3 & (errv3 & ERR3) & AUX3 & FA3 & SO3 & RR).
      unfold pidn_R in RR.
      destruct RR as (HEAP3 & PRES13 & SJRO3 & SJS3 & PIMPL3 & DOCC3 & P483 & (r & SRET3 & OKR) & (vptr & nsi & p12 & nxt & p28 & capv & md & b48 & b49 & p50 & bufv & lenv & docv & THIS3 & EVP) & BRTP & BRSB).
      replace (ret_pc (Z_to_bv 64 0x2733c)) with (Z_to_bv 64 0x2733c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      apply implM_ret_bind. apply HK.

      pose proof (agree_of_lx_pres _ _ _ _ _ PRES13) as AG13.
      assert (FRCL : forall a, sp0 <= a < sp0 + 272 -> ~ (sp0 + 80 <= a < sp0 + 104) -> ~ (sp0 + 112 <= a < sp0 + 120) -> ~ (sp0 + 128 <= a < sp0 + 152) ->
                lx_client ((bv, A, 16 * cap) :: LB) sp0 (pid_front_X (sp0 + 104) ++ pidn_X (sp0 + 80)) a).
      { intros a Ha N1 N2 N3. split; [| left; lia]. unfold pid_front_X, pidn_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI. cbn [app rin_ivs fst snd]. clear - Ha N1 N2 N3 GLO LO. lia. }
      apply (rw_cells_agree _ _ _ _ _ AG13) in PA0; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG13) in PA16; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG13) in GSO; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG13) in LEAF; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG13) in OUT; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG13) in XFD; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG13) in ROOT; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG13) in SAVE; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG13) in SV; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      assert (BKCL : forall a, A <= a < A + 16 * cap -> lx_client ((bv, A, 16 * cap) :: LB) sp0 (pid_front_X (sp0 + 104) ++ pidn_X (sp0 + 80)) a).
      { intros a Ha. split; [| right; left; exists (bv, A, 16 * cap); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]].
        unfold pid_front_X, pidn_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI. cbn [app rin_ivs fst snd]. clear - Ha AC AS A0 CEIL LO. lia. }
      apply (vblk_agree _ _ _ _ _ _ _ _ _ AG13) in BLK; [| intros a _ Ha; apply BKCL; exact Ha| exact ELS| lia].
      assert (PL3 : payload_ok m3 LB D d).
      { eapply payload_ok_agree; [exact AG13| exact PL1|]. intros b a Hb Ha. pose proof (LH_block_range _ _ _ _ HEAP00 Hb) as (_ & _ & _ & BC & BS).
        unfold OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec.Malloc.MCEIL in BC. split; [| right; left; exists b; split; [right; exact Hb| exact Ha]].
        unfold pid_front_X, pidn_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI. cbn [app rin_ivs fst snd]. clear - Ha BC BS CEIL LO. lia. }
      assert (PRES3 : lx_pres LB (sp0 + 272) [LXW_SJ] m0 m3).
      { eapply lx_pres_trans; [exact PRES1|]. eapply (lx_pres_sub LB (sp0 + 272) _ _ _ _ _ _ PRES13); [lia| intros b0 Hb0; right; exact Hb0|].
        intros a Ha NX. unfold pid_front_X, pidn_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI in Ha, NX. cbn [app rin_ivs fst snd] in Ha, NX.
        split; [clear - Ha NX LO GLO; lia|]. split; [intros IB; specialize (BLB a IB); clear - Ha NX BLB CEIL LO; lia| clear - Ha NX LO GLO; lia]. }
      rewrite <- CAPD in HEAP3, OKR, BRTP, BRSB, DOCC3. replace (sp0 + 104 + 24) with (sp0 + 128) in SRET3 by lia.
      readdr PIMPL3 (sp0 + 112). readdr DOCC3 (sp0 + 128). readdr P483 (sp0 + 152).
      unfold gate_post. do 22 eexists. exists m3, errv3, IMPL, IDX, OC, IA, TAPE, SBUF, r. do 9 eexists.
      exists vptr, nsi, nxt, capv, md, bufv, lenv, docv, b48, b49, p12, p28, p50.
      split; [cbv delta [mkR]; reflexivity|].
      split; [exact FRM3|]. split; [exact MI3|]. split; [exact ST3|]. split; [exact ERR3|]. split; [exact AUX3|]. split; [congruence|]. split; [congruence|].
      split; [exact HEAP3|]. split; [exact PRES3|]. split; [exact SJS3|]. split; [exact PL3|].
      split. { rewrite EE. split; [exact ELS|]. split; [exact SZ|]. split; [exact SV| exact BLK]. }
      split; [exact SRET3|]. split; [exact OKR|]. split; [exact BRTP|]. split; [exact BRSB|].
      split; [exact PA0|]. split; [exact PIMPL3|]. split; [exact PA16|]. split; [exact DOCC3|]. split; [exact P483|]. split; [exact THIS3|]. split; [exact EVP|].
      split; [exact GSO|]. split; [exact LEAF|]. split; [exact OUT|]. split; [exact ROOT|]. split; [exact XFD| exact SAVE].
    -
      assert (EDOC : atp_doc d = atp_s0 d) by (unfold atp_doc; rewrite <- Elen0; replace (len0 <=? SJ_PADMAX) with true by (symmetry; apply Z.leb_le; unfold SJ_PADMAX; lia); reflexivity).
      replace (len0 <=? 1048512) with true by (symmetry; apply Z.leb_le; lia).
      rewrite EDOC, <- Elen0.
      unfold SJ_GOT_NOTHROW, SJ_NOTHROW_TAG in GOT1. unfold Zf2.wz in GOT1.

      step. zstep. step. step. step.
      ihere. to_implM. apply implM_bind_assoc.
      eapply implM_bind.
      { eapply (opnew_arr_nt_proof HM) with (B := B) (lo := lo);
          [exact HEAP1| exact AUX1| lia| exact ST| exact CEIL'| unfold SJ_OPNEW_STACK, RMALLOC_STACK; lia| rewrite ELX; eassumption| assumption| lia| lia]. }
      cbv beta. intros pcp st2 ms2 PO. unfold opnew_postZ in PO.
      destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2 & errv2 & COPY & junk2
                      & -> & MI2 & ST2 & ERR2 & AUX2 & HP2 & FA2 & SO2 & BRC & HEAP2 & BLKC).
      replace (ret_pc (Z_to_bv 64 0x272c4)) with (Z_to_bv 64 0x272c4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      rewrite ELX in ERR2. apply implM_ret_bind.
      pose proof BRC as (C0 & _ & _ & CC & CS). unfold OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec.Malloc.MCEIL in CC.

      pose proof (agree_of_heap_pres _ _ _ _ HP2) as AG2.
      assert (FRH : forall a, sp0 <= a < sp0 + 272 -> rclient_addr ((bv, A, 16 * cap) :: LB) sp0 a) by (intros a Ha; left; lia).
      apply (rw_cells_agree _ _ _ _ _ AG2) in PA0; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in PIMPL; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in PA16; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in DOCC; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in P48; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in GSO; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in LEAF; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in OUT; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in RES; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in XFD; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in ROOT; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in SAVE; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in SV; [| intros a Ha; cbn in Ha; apply FRH; lia].
      apply (vblk_agree _ _ _ _ _ _ _ _ _ AG2) in BLK; [| intros a _ Ha; right; right; exists (bv, A, 16 * cap); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]| exact ELS| lia].
      assert (PRES2 : lx_pres LB (sp0 + 272) [LXW_SJ] m0 m2).
      { eapply lx_pres_trans; [exact PRES1|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP2| lia| intros b Hb; right; exact Hb]. }
      pose proof (statics_heap _ _ _ _ HP2 ltac:(unfold GLOBALS_TOP; lia)) as (LXSf & SJSf & _).
      pose proof (SJSf _ SJS1) as SJS2. pose proof (LXSf LXS1) as LXS2. clear LXSf SJSf.
      assert (PL2 : payload_ok m2 LB D d).
      { eapply payload_ok_agree; [exact AG2| exact PL1|]. intros b a Hb Ha. right; right. exists b. split; [right; exact Hb| exact Ha]. }
      pose proof LXS2 as (_ & _ & GOT2 & VT242 & VTD2).
      clear AG2 HP2 HEAP1 AUX1 PRES1 SJS1 PL1 LXS1 GOT1 VT241 VTD1.

      replace (Z.to_nat (len0 + 64)) with (Z.to_nat len0 + 64)%nat in BLKC by lia.
      apply rw_cells_CB_split2 in BLKC. destruct BLKC as [BDOC BPAD]. rewrite Z2Nat.id in BPAD by lia.
      pose proof (munch_refl [(sp0, sp0 + 272); (COPY, COPY + (len0 + 64))]%Z m2) as MU. pose proof (wmono_refl usegs m2) as WM.
      unfold implM. iprefix.

      step. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
      step. zstep. rewrite (Z6d.lxor_ones64 COPY) by lia. step. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K CC CS C0 LEN0; lia| clear K].
      zstep. step. step. step.
      eapply evt_cut.
      { eapply memset_callZ with (junk := drop (Z.to_nat len0) junk2); [exact BPAD| assumption| lia| lia| lia| lia]. }
      cbv beta. intros ms' PO. unfold memset_postZ in PO.
      destruct PO as (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m3 & -> & MU3 & WM3 & MI3 & PAD3).
      replace (ret_pc (Z_to_bv 64 0x272e4)) with (Z_to_bv 64 0x272e4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      change (0 mod 256) with 0 in PAD3.
      hide MU. hide WM. transport_after_call usegs m2 m3 MU3 WM3. unhide MU. unhide WM.

      pose proof (fun p' A' n' H => LH_head_sep _ _ _ _ _ _ p' A' n' HEAP2 H) as SEPC.
      assert (OUTC : forall a, 0x7e000 <= a < GLOBALS_TOP -> outside [(COPY + len0, COPY + len0 + 64)] a).
      { intros a Ha. unfold GLOBALS_TOP in Ha. cbn [outside]. clear - Ha CS C0 LEN0. lia. }
      pose proof (statics_munch _ _ _ rr_guard MU3 WM3 OUTC) as (LXSf & SJSf & _). pose proof (LXSf LXS2) as LXS3. pose proof (SJSf _ SJS2) as SJS3. clear LXSf SJSf.
      pose proof LXS3 as (_ & _ & GOT3 & VT243 & VTD3).
      pose proof (agree_on_of_munch _ _ _ MU3 WM3) as AG3.
      assert (PL3 : payload_ok m3 LB D d).
      { eapply payload_ok_agree; [exact AG3| exact PL2|]. intros [[bi ba] bn] a Hb Ha.
        pose proof (SEPC bi ba bn ltac:(right; exact Hb)) as SP. cbn [blk_addr blk_size blk_id fst snd outside] in *. clear - SP Ha LEN0. lia. }
      apply (vblk_agree _ _ _ _ _ _ _ _ _ AG3) in BLK; [| intros a _ Ha; pose proof (SEPC bv A (16 * cap) ltac:(left; reflexivity)) as SP; cbn [outside]; clear - SP Ha LEN0; lia| exact ELS| lia].
      assert (PRES3 : lx_pres LB (sp0 + 272) [LXW_SJ] m0 m3).
      { eapply lx_pres_trans; [exact PRES2|]. eapply lx_pres_of_munch; [exact MU3| exact WM3|].
        intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[([[bi ba] bn] & Hb & Hr)|HC]]; [clear - HC CC CEIL LO; lia| | clear - HC CS C0 LEN0; lia].
        pose proof (SEPC bi ba bn ltac:(right; exact Hb)) as SP. cbn [blk_addr blk_size blk_id fst snd] in *. clear - SP Hr LEN0. lia. }

      assert (MU3' : munch [(sp0, sp0 + 272); (COPY, COPY + (len0 + 64))]%Z m2 m3).
      { eapply munch_weaken; [| exact MU3]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
      pose proof (munch_trans _ _ _ _ MU MU3') as MU3''. pose proof (wmono_trans usegs _ _ _ WM WM3) as WM3''.
      clear MU WM MU3 MU3' AG3. rename MU3'' into MU. rename WM3'' into WM.

      assert (DOCB : len0 = 0 \/ (bytes_at usegs m3 P0 (to_bytes (atp_s0 d)) /\ P0 = D + 0 /\ exists b0, In b0 LB /\ blk_addr b0 <= P0 /\ P0 + len0 <= blk_addr b0 + blk_size b0)).
      { destruct (Z.eq_dec len0 0) as [Z0|NZ]; [left; exact Z0| right].
        destruct HP0 as [[EP ES]|EP]. { exfalso. apply NZ. subst len0. rewrite ES. reflexivity. }
        destruct PL3 as (PB3 & _ & _ & _ & _ & PIN3).
        split. { rewrite HS0, to_bytes_firstn. replace P0 with D by lia. apply bytes_at_firstn. exact PB3. }
        split; [lia|].
        destruct PIN3 as [E0|(b0 & Hb & Hb1 & Hb2)]. { exfalso. apply NZ. subst len0. rewrite E0. reflexivity. }
        exists b0. split; [exact Hb|]. subst len0. lia. }

      lazymatch goal with |- evt _ ?QQ _ =>
      assert (K214 : forall (m4 : mem) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
        munch [(COPY, COPY + len0)]%Z m3 m4 -> wmono usegs m3 m4 -> mem_inv usegs m4 ->
        rw_cells usegs m4 COPY [CB (Z.to_nat len0) (to_bytes (atp_s0 d))] ->
        evt usegs QQ (MS (mkR y1 (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) y5 y6 y7 (Z_to_bv 64 (sp0 + 128)) (Z_to_bv 64 len0) y10 y11 y12 y13 y14 y15 y16 y17
                               (Z_to_bv 64 COPY) (Z_to_bv 64 P0) s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                        F (Z_to_bv 64 0x272f8) fc None m4 (seg_rom usegs))) end.
      { intros m4 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 MU4 WM4 MI4 BDOC4.
        clear BDOC DOCB. hide MU. hide WM. transport_after_call usegs m3 m4 MU4 WM4. unhide MU. unhide WM.
        assert (OUTC4 : forall a, 0x7e000 <= a < GLOBALS_TOP -> outside [(COPY, COPY + len0)] a).
        { intros a Ha. unfold GLOBALS_TOP in Ha. cbn [outside]. clear - Ha CS C0 LEN0. lia. }
        pose proof (statics_munch _ _ _ rr_guard MU4 WM4 OUTC4) as (LXSf & SJSf & _). pose proof (LXSf LXS3) as LXS4. pose proof (SJSf _ SJS3) as SJS4. clear LXSf SJSf.
        pose proof LXS4 as (_ & _ & GOT4 & VT244 & VTD4).
        pose proof (agree_on_of_munch _ _ _ MU4 WM4) as AG4.
        assert (PL4 : payload_ok m4 LB D d).
        { eapply payload_ok_agree; [exact AG4| exact PL3|]. intros [[bi ba] bn] a Hb Ha.
          pose proof (SEPC bi ba bn ltac:(right; exact Hb)) as SP. cbn [blk_addr blk_size blk_id fst snd outside] in *. clear - SP Ha LEN0. lia. }
        apply (vblk_agree _ _ _ _ _ _ _ _ _ AG4) in BLK; [| intros a _ Ha; pose proof (SEPC bv A (16 * cap) ltac:(left; reflexivity)) as SP; cbn [outside]; clear - SP Ha LEN0; lia| exact ELS| lia].
        assert (PRES4 : lx_pres LB (sp0 + 272) [LXW_SJ] m0 m4).
        { eapply lx_pres_trans; [exact PRES3|]. eapply lx_pres_of_munch; [exact MU4| exact WM4|].
          intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[([[bi ba] bn] & Hb & Hr)|HC]]; [clear - HC CC CEIL LO LEN0; lia| | clear - HC CS C0 LEN0; lia].
          pose proof (SEPC bi ba bn ltac:(right; exact Hb)) as SP. cbn [blk_addr blk_size blk_id fst snd] in *. clear - SP Hr LEN0. lia. }
        assert (HEAP4 : RHEAP st2 ((pcp, COPY, len0 + 64) :: (bv, A, 16 * cap) :: LB) m4).
        { eapply LH_frame; [eapply LH_frame; [exact HEAP2| exact MU| exact WM|]| exact MU4| exact WM4|].
          - constructor; [apply W_ok_stack; cbn; lia|]. constructor; [| constructor]. eapply (W_ok_block _ (pcp, COPY, len0 + 64)); [left; reflexivity| cbn; lia| cbn; lia].
          - constructor; [| constructor]. eapply (W_ok_block _ (pcp, COPY, len0 + 64)); [left; reflexivity| cbn; lia| cbn; lia]. }
        assert (AUX4 : rauxv_ok m4 B).
        { eapply rauxv_ok_frame; [eapply rauxv_ok_frame; [exact AUX2| exact MU| exact WM|]| exact MU4| exact WM4|].
          - constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; clear - CC CS C0 CEIL LO LEN0 QB; lia| constructor].
          - constructor; [cbn; unfold RAUXV_CELL; clear - CC CS C0 CEIL LO LEN0 QB; lia| constructor]. }

        lazymatch goal with H : rw_cells usegs m4 (COPY + len0) _ |- _ => rename H into PAD4 end.
        assert (BUF4 : bytes_at usegs m4 COPY (padded_bytes (atp_s0 d))).
        { pose proof (rw_cells_join _ _ _ _ _ BDOC4 PAD4 ltac:(cbn [cells_size csize Nat.add]; lia)) as J. destruct J as [[_ HB] _].
          cbn [cells_bytes cbytes app] in HB. rewrite app_nil_r in HB. unfold padded_bytes, zbytes. exact HB. }
        clear MU WM MU4 WM4 AG4 PL3 PRES3 LXS3 SJS3 HEAP2 AUX2.
        pose proof (munch_refl ([] : list (Z * Z)) m4) as MU. pose proof (wmono_refl usegs m4) as WM.

        step. step. step. step. step. step. step.
        replace (Z_to_bv 64 (sp0 + 128)) with (Z_to_bv 64 (sp0 + 104 + 24)) by (f_equal; lia).
        unfold SJ_GOT_NOTHROW, SJ_NOTHROW_TAG, Zf2.wz in GOT4. unfold SJ_IMPL_VT24, SJ_CREATE_DPI, Zf2.wz in VT244. unfold Zf2.wz in VTD4.
        ihere. to_implM.
        eapply (pid_front_cps HM) with (B := B) (lo := lo) (SRET := sp0 + 80) (PARSER := sp0 + 104) (init := init);
          [exact HEAP4| exact AUX4| lia| eassumption| exact CEIL'| unfold GLOBALS_TOP; lia| unfold SJ_OPNEW_STACK, RMALLOC_STACK; lia
          | rewrite ELX; eassumption| assumption| lia| lia| lia| lia
          | split; [exact GOT4| split; [exact VT244| exact VTD4]]| exact SJS4| exact PIMPL| exact DOCC| exact P48|].
        intros psb ptp pim pix poc pia st5 ms5 MID. subst len0.
        eapply (pid_nocopy_cps S2) with (B := B) (lo := lo) (pcp := pcp) (d := atp_s0 d);
          [exact MID| lia| exact HEAP4| left; reflexivity| rewrite HS0; apply Forall_firstn'; exact PRNG| exact BUF4| exact FRM| lia| exact B63| exact CEIL'| unfold GLOBALS_TOP; lia
          | unfold SJ_S2_STACK, SJ_S2_FRAMES, RMALLOC_STACK; lia| lia| clear - AL16; replace sp0 with (sp0 + 272 + (-17) * 16) by lia; rewrite Z.mod_add by lia; exact AL16
          | lia| lia| lia| clear - AL16; lia| exact RES|].
        intros st6 ms6 (IMPL & IDX & OC & IA & TAPE & SBUF & PO). unfold hpostF in PO.
        destruct PO as (w5 & w6 & w7 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & F' & fc' & m6
                        & -> & FRM6 & MI6 & ST6 & (errv6 & ERR6) & AUX6 & FA6 & SO6 & RR).
        unfold pidn_R in RR.
        destruct RR as (HEAP6 & PRES46 & SJRO6 & SJS6 & PIMPL6 & DOCC6 & P486 & (r & SRET6 & OKR) & (vptr & nsi & p12 & nxt & p28 & capv & md & b48 & b49 & p50 & bufv & lenv & docv & THIS6 & EVP) & BRTP & BRSB).
        replace (ret_pc (Z_to_bv 64 0x27314)) with (Z_to_bv 64 0x27314) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        rewrite ELX in ERR6. remember (zlength (atp_s0 d)) as len0 eqn:Elen0.
        remember (Z.max len0 32) as capd eqn:Ecapd.
        pose proof BRTP as (TP0 & _ & _ & TPC & TPS). pose proof BRSB as (SB0 & _ & _ & SBC & SBS). unfold OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec.Malloc.MCEIL in TPC, SBC.
        pose proof (roundup64_ge (capd + 3)) as RC2. pose proof (roundup64_ge (5 * (capd / 3) + 64)) as RC3.
        assert (D3 : 0 <= capd / 3) by (apply Z.div_pos; lia).

        pose proof (agree_of_lx_pres _ _ _ _ _ PRES46) as AG46.
        assert (FRCL : forall a, sp0 <= a < sp0 + 272 -> ~ (sp0 + 80 <= a < sp0 + 104) -> ~ (sp0 + 112 <= a < sp0 + 120) -> ~ (sp0 + 128 <= a < sp0 + 152) ->
                  lx_client ((pcp, COPY, len0 + 64) :: (bv, A, 16 * cap) :: LB) sp0 (pid_front_X (sp0 + 104) ++ pidn_X (sp0 + 80)) a).
        { intros a Ha N1 N2 N3. split; [| left; lia]. unfold pid_front_X, pidn_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI. cbn [app rin_ivs fst snd]. clear - Ha N1 N2 N3 GLO LO. lia. }
        apply (rw_cells_agree _ _ _ _ _ AG46) in PA0; [| intros a Ha; cbn in Ha; apply FRCL; lia].
        apply (rw_cells_agree _ _ _ _ _ AG46) in PA16; [| intros a Ha; cbn in Ha; apply FRCL; lia].
        apply (rw_cells_agree _ _ _ _ _ AG46) in GSO; [| intros a Ha; cbn in Ha; apply FRCL; lia].
        apply (rw_cells_agree _ _ _ _ _ AG46) in LEAF; [| intros a Ha; cbn in Ha; apply FRCL; lia].
        apply (rw_cells_agree _ _ _ _ _ AG46) in OUT; [| intros a Ha; cbn in Ha; apply FRCL; lia].
        apply (rw_cells_agree _ _ _ _ _ AG46) in XFD; [| intros a Ha; cbn in Ha; apply FRCL; lia].
        apply (rw_cells_agree _ _ _ _ _ AG46) in ROOT; [| intros a Ha; cbn in Ha; apply FRCL; lia].
        apply (rw_cells_agree _ _ _ _ _ AG46) in SAVE; [| intros a Ha; cbn in Ha; apply FRCL; lia].
        apply (rw_cells_agree _ _ _ _ _ AG46) in SV; [| intros a Ha; cbn in Ha; apply FRCL; lia].
        assert (BKCL : forall a, A <= a < A + 16 * cap -> lx_client ((pcp, COPY, len0 + 64) :: (bv, A, 16 * cap) :: LB) sp0 (pid_front_X (sp0 + 104) ++ pidn_X (sp0 + 80)) a).
        { intros a Ha. split; [| right; left; exists (bv, A, 16 * cap); split; [right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]].
          unfold pid_front_X, pidn_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI. cbn [app rin_ivs fst snd]. clear - Ha AC AS A0 CEIL LO. lia. }
        apply (vblk_agree _ _ _ _ _ _ _ _ _ AG46) in BLK; [| intros a _ Ha; apply BKCL; exact Ha| exact ELS| lia].
        assert (PL6 : payload_ok m6 LB D d).
        { eapply payload_ok_agree; [exact AG46| exact PL4|]. intros b a Hb Ha. pose proof (LH_block_range _ _ _ _ HEAP00 Hb) as (_ & _ & _ & BC & BS).
          unfold OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec.Malloc.MCEIL in BC. split; [| right; left; exists b; split; [right; right; exact Hb| exact Ha]].
          unfold pid_front_X, pidn_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI. cbn [app rin_ivs fst snd]. clear - Ha BC BS CEIL LO. lia. }
        assert (PRES6 : lx_pres LB (sp0 + 272) [LXW_SJ] m0 m6).
        { eapply lx_pres_trans; [exact PRES4|]. eapply (lx_pres_sub LB (sp0 + 272) _ _ _ _ _ _ PRES46); [lia| intros b0 Hb0; right; right; exact Hb0|].
          intros a Ha NX. unfold pid_front_X, pidn_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI in Ha, NX. cbn [app rin_ivs fst snd] in Ha, NX.
          split; [clear - Ha NX LO GLO; lia|]. split; [intros IB; specialize (BLB a IB); clear - Ha NX BLB CEIL LO; lia| clear - Ha NX LO GLO; lia]. }
        clear AG46 PRES46 FRCL BKCL HEAP4 AUX4 PRES4 PL4 MU WM.

        pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl usegs m6) as WM.
        unfold implM. iprefix. step. step.
        pose proof (RHEAP_pull _ [(pia, IA, 1024); (poc, OC, 8192); (pix, IDX, 4 * (roundup64 capd + 9)); (pim, IMPL, 96); (ptp, TAPE, 8 * roundup64 (capd + 3)); (psb, SBUF, roundup64 (5 * (capd / 3) + 64))]
                      (pcp, COPY, len0 + 64) ((bv, A, 16 * cap) :: LB) _ HEAP6) as HEAP6'. cbn [app] in HEAP6'.
        assert (ND : List.NoDup (map blk_id ((pcp, COPY, len0 + 64) :: (pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, 4 * (roundup64 capd + 9)) :: (pim, IMPL, 96)
                                            :: (ptp, TAPE, 8 * roundup64 (capd + 3)) :: (psb, SBUF, roundup64 (5 * (capd / 3) + 64)) :: (bv, A, 16 * cap) :: LB))) by (eapply LH_nodup; exact HEAP6').
        ihere. to_implM. eapply implM_bind.
        { eapply (opdel_arr_proof HF) with (B := B) (lo := lo) (A := COPY) (n := len0 + 64);
            [exact HEAP6'| left; reflexivity| exact AUX6| lia| exact ST6| exact CEIL'| unfold RFREE_STACK; lia| exact ERR6| exact MI6| lia]. }
        cbv beta. intros [] st7 ms7 PO. unfold free_postZ in PO.
        destruct PO as (v5 & v6 & v7 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & m7
                        & -> & MI7 & ST7 & ERR7 & AUX7 & HP7 & FA7 & SO7 & HEAP7).
        rewrite (lb_remove_hd _ _ _ _ ND) in HP7, HEAP7.
        replace (ret_pc (Z_to_bv 64 0x2731c)) with (Z_to_bv 64 0x2731c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        pose proof (agree_of_heap_pres _ _ _ _ HP7) as AG7.
        pose proof (statics_heap _ _ _ _ HP7 ltac:(unfold GLOBALS_TOP; lia)) as (LXSf & SJSf & _). pose proof (SJSf _ SJS6) as SJS7. clear LXSf SJSf.
        assert (FRH7 : forall a, sp0 <= a < sp0 + 272 -> rclient_addr ((pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, 4 * (roundup64 capd + 9)) :: (pim, IMPL, 96)
                                            :: (ptp, TAPE, 8 * roundup64 (capd + 3)) :: (psb, SBUF, roundup64 (5 * (capd / 3) + 64)) :: (bv, A, 16 * cap) :: LB) sp0 a) by (intros a Ha; left; lia).
        apply (rw_cells_agree _ _ _ _ _ AG7) in PA0; [| intros a Ha; cbn in Ha; apply FRH7; lia].
        apply (rw_cells_agree _ _ _ _ _ AG7) in PA16; [| intros a Ha; cbn in Ha; apply FRH7; lia].
        apply (rw_cells_agree _ _ _ _ _ AG7) in GSO; [| intros a Ha; cbn in Ha; apply FRH7; lia].
        apply (rw_cells_agree _ _ _ _ _ AG7) in LEAF; [| intros a Ha; cbn in Ha; apply FRH7; lia].
        apply (rw_cells_agree _ _ _ _ _ AG7) in OUT; [| intros a Ha; cbn in Ha; apply FRH7; lia].
        apply (rw_cells_agree _ _ _ _ _ AG7) in XFD; [| intros a Ha; cbn in Ha; apply FRH7; lia].
        apply (rw_cells_agree _ _ _ _ _ AG7) in ROOT; [| intros a Ha; cbn in Ha; apply FRH7; lia].
        apply (rw_cells_agree _ _ _ _ _ AG7) in SAVE; [| intros a Ha; cbn in Ha; apply FRH7; lia].
        apply (rw_cells_agree _ _ _ _ _ AG7) in SV; [| intros a Ha; cbn in Ha; apply FRH7; lia].
        apply (rw_cells_agree _ _ _ _ _ AG7) in PIMPL6; [| intros a Ha; cbn in Ha; apply FRH7; lia].
        apply (rw_cells_agree _ _ _ _ _ AG7) in DOCC6; [| intros a Ha; cbn in Ha; apply FRH7; lia].
        apply (rw_cells_agree _ _ _ _ _ AG7) in P486; [| intros a Ha; cbn in Ha; apply FRH7; lia].
        apply (rw_cells_agree _ _ _ _ _ AG7) in SRET6; [| intros a Ha; unfold res_cells in Ha; destruct (bv_eqb r (Z_to_bv 64 0)); cbn in Ha; apply FRH7; lia].
        apply (rw_cells_agree _ _ _ _ _ AG7) in THIS6; [| intros a Ha; right; right; exists (pim, IMPL, 96); split; [do 3 right; left; reflexivity| unfold impl_cells16 in Ha; cbn in Ha; cbn [blk_addr blk_size fst snd]; lia]].
        apply (vblk_agree _ _ _ _ _ _ _ _ _ AG7) in BLK; [| intros a _ Ha; right; right; exists (bv, A, 16 * cap); split; [do 6 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]| exact ELS| lia].
        apply (s2_okres_agree _ _ _ _ _ _ _ _ AG7) in OKR;
          [| intros a Ha; right; right; exists (ptp, TAPE, 8 * roundup64 (capd + 3)); split; [do 4 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]
           | intros a Ha; right; right; exists (psb, SBUF, roundup64 (5 * (capd / 3) + 64)); split; [do 5 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]].
        assert (PL7 : payload_ok m7 LB D d).
        { eapply payload_ok_agree; [exact AG7| exact PL6|]. intros b a Hb Ha. right; right. exists b. split; [do 7 right; exact Hb| exact Ha]. }
        assert (PRES7 : lx_pres LB (sp0 + 272) [LXW_SJ] m0 m7).
        { eapply lx_pres_trans; [exact PRES6|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP7| lia| intros b Hb; do 7 right; exact Hb]. }
        clear AG7 HP7.

        unfold implM. iprefix. step.
        ihere. to_implM. apply HK.
        assert (CAPD : doc_cap d = capd) by (unfold doc_cap; rewrite EDOC, <- Elen0, Ecapd; reflexivity).
        rewrite <- CAPD in HEAP7, OKR, BRTP, BRSB, DOCC6. replace (sp0 + 104 + 24) with (sp0 + 128) in SRET6 by lia.
        readdr PIMPL6 (sp0 + 112). readdr DOCC6 (sp0 + 128). readdr P486 (sp0 + 152).
        unfold gate_post. do 22 eexists. exists m7, errv6, IMPL, IDX, OC, IA, TAPE, SBUF, r. do 9 eexists.
        exists vptr, nsi, nxt, capv, md, bufv, lenv, docv, b48, b49, p12, p28, p50.
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact FRM6|]. split; [exact MI7|]. split; [exact ST7|]. split; [exact ERR7|]. split; [exact AUX7|]. split; [congruence|]. split; [congruence|].
        split; [exact HEAP7|]. split; [exact PRES7|]. split; [exact SJS7|]. split; [exact PL7|].
        split. { rewrite EE. split; [exact ELS|]. split; [exact SZ|]. split; [exact SV| exact BLK]. }
        split; [exact SRET6|]. split; [exact OKR|]. split; [exact BRTP|]. split; [exact BRSB|].
        split; [exact PA0|]. split; [exact PIMPL6|]. split; [exact PA16|]. split; [exact DOCC6|]. split; [exact P486|]. split; [exact THIS6|]. split; [exact EVP|].
        split; [exact GSO|]. split; [exact LEAF|]. split; [exact OUT|]. split; [exact ROOT|]. split; [exact XFD| exact SAVE]. }

      step. if_cases KZ; zify_cond KZ.
      +
        eapply (K214 m3); [apply munch_refl| apply wmono_refl| assumption|].
        assert (ES0 : atp_s0 d = []) by (destruct (atp_s0 d) as [|c l] eqn:E0; [reflexivity| exfalso; rewrite Elen0 in KZ; unfold zlength in KZ; cbn in KZ; lia]).
        rewrite ES0. rewrite KZ in BDOC. cbn [Z.to_nat take to_bytes map] in BDOC. rewrite KZ. cbn [Z.to_nat]. exact BDOC.
      +
        destruct DOCB as [Z0|(SRCB & EP0 & (b0 & Hb0 & Hb01 & Hb02))]; [exfalso; lia|].
        destruct b0 as [[b0i b0a] b0n]. pose proof (SEPC b0i b0a b0n ltac:(right; exact Hb0)) as SP0. cbn [blk_addr blk_size blk_id fst snd] in Hb01, Hb02, SP0.
        step. step. step. step.
        eapply evt_cut.
        { eapply memcpy_callZ with (src := to_bytes (atp_s0 d)) (junk := take (Z.to_nat len0) junk2);
            [exact SRCB| rewrite to_bytes_length; rewrite Elen0; unfold zlength; lia| exact BDOC| clear - SP0 Hb01 Hb02 LEN0; lia| lia| lia| lia| assumption]. }
        cbv beta. intros ms' PO. unfold memcpy_postZ in PO.
        destruct PO as (z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m4 & -> & MU4 & WM4 & MI4 & DST4 & SRC4).
        replace (ret_pc (Z_to_bv 64 0x272f8)) with (Z_to_bv 64 0x272f8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        eapply (K214 m4); [exact MU4| exact WM4| exact MI4| exact DST4].
  Qed.
End Proofs.
End WithCeiling0.
