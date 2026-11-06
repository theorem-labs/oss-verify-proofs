(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge ZBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World U_Img ImgU U_Cov8m.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_VS58t.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_crc32.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_crc32.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_crc32.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_vegk2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.

Module U_VSdg2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb ImgU U_Leaves U_VSe1y U_VS58t.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutPU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutPU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac akit_plia := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker.
Ltac akit_avoids_false X :=
  lazymatch type of X with
  | _ \/ _ => destruct X as [X|X]; akit_avoids_false X
  | False => destruct X
  | _ => try (lazymatch type of X with (_ <> _) /\ _ => destruct X as [_ X] end);
         first [ match goal with D : _ \/ _ |- _ => solve [ destruct D; akit_plia ] end | akit_plia ]
  end.
Local Ltac avoids_solve ::=
  cbn [Cells.cells_size Cells.csize Nat.add length app];
  split; [ lia | intros ? ? X; unfold blk, nowhere in X; cbn beta in X; first [ solve [ akit_avoids_false X ] | lia ] ].
(* [comment removed for export] *)

Definition VSB_bcat_entry := 0x19418.
(* [comment removed for export] *)
Definition BCAT_STACK := 48 + EXT_STACK.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (m : mem) (md : Model) (A : AS) (S SRC : Z) (src : list byte) (v : vsb_rec) (lo : Z) (T : TSet).

  (* [comment removed for export] *)
  Hypothesis AINV : ainv A m md.
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis A0 : a0 = Z_to_bv 64 S.
  Hypothesis A1 : a1 = Z_to_bv 64 SRC.
  Hypothesis A2 : a2 = Z_to_bv 64 (Z.of_nat (length src)).
  Hypothesis VOBJ : vsb_obj LayoutPU A m S v false.
  Hypothesis BSRC : bytes_at rsegs m SRC src.
  Hypothesis LSRC : 1 <= Z.of_nat (length src) <= 9.
  Hypothesis SRCHI : bv_unsigned sp <= SRC.                 (* [comment removed for export] *)
  Hypothesis EM : vb_size v + 9 <= EXT_MAX.
  (* [comment removed for export] *)
  Hypothesis LBUD : a_livebytes A + vsb_extendsize (vb_size v + 9) <= LIVE_MAX.
  Hypothesis NBUD : a_nlive A + 1 <= NLIVE_MAX.
  Hypothesis TP : tp = al_tp LayoutPU.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + BCAT_STACK <= bv_unsigned sp.
  Hypothesis SPHI : bv_unsigned sp + 64 <= 2^47.
  Hypothesis SRC47 : SRC + 16 <= 2^47.

  (* [comment removed for export] *)
  Hypothesis K : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
                        (v' : vsb_rec),
      ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
      vsb_obj LayoutPU A' m' S v' false ->
      vb_len v <= vb_len v' <= vb_len v + Z.of_nat (length src) ->
      vb_size v <= vb_size v' <= Z.max (vb_size v) (vb_len v' + 4096) ->   (* [comment removed for export] *)
      (forall q, q <> vb_buf v -> q <> vb_buf v' -> a_live A' q = a_live A q) ->
      (vb_buf v' = vb_buf v \/ (a_live A (vb_buf v') = None /\ a_live A' (vb_buf v) = None)) ->
      a_livebytes A' = a_livebytes A + vb_size v' - vb_size v -> a_nlive A' = a_nlive A ->   (* [comment removed for export] *)
      stk rsegs m' lo (bv_unsigned sp) ->
      cframe LayoutPU (owned A) (owned A') (bv_unsigned sp) BCAT_STACK
               (fun a => blk (vb_buf v) (vb_size v) a \/ (S <= a < S + 40))
               (blk (vb_buf v') (vb_size v')) m m' ->
      realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T.

  Let W := [(bv_unsigned sp - 8352, bv_unsigned sp); (S, S + 40); (vb_buf v, vb_buf v + vb_size v)].

  (* [comment removed for export] *)
  #[using="K LO CEIL"] Lemma bcat_epilogue :
    forall (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (r : Z) (junk8 : list byte)
           (A' : AS) (m' : mem) (md' : Model) (v' : vsb_rec),
      m_halted md' = None -> m_vm_lazy md' = [] ->
      rw_cells rsegs m' (bv_unsigned sp + -48) [CB 8 junk8; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      stk rsegs m' lo (bv_unsigned sp + -48) ->
      ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
      vsb_obj LayoutPU A' m' S v' false ->
      vb_len v <= vb_len v' <= vb_len v + Z.of_nat (length src) ->
      vb_size v <= vb_size v' <= Z.max (vb_size v) (vb_len v' + 4096) ->   (* [comment removed for export] *)
      (forall q, q <> vb_buf v -> q <> vb_buf v' -> a_live A' q = a_live A q) ->
      (vb_buf v' = vb_buf v \/ (a_live A (vb_buf v') = None /\ a_live A' (vb_buf v) = None)) ->
      a_livebytes A' = a_livebytes A + vb_size v' - vb_size v -> a_nlive A' = a_nlive A ->   (* [comment removed for export] *)
      (mapped m' (bv_unsigned sp - BCAT_STACK) BCAT_STACK ->
       cframe LayoutPU (owned A) (owned A') (bv_unsigned sp) BCAT_STACK
               (fun a => blk (vb_buf v) (vb_size v) a \/ (S <= a < S + 40))
               (blk (vb_buf v') (vb_size v')) m m') ->
      evt rsegs (rz_at rsegs md' T)
          (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp xt0 xt1 xt2 (Z_to_bv 64 S) (Z_to_bv 64 (Z.of_nat (length src)))
                   xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 SRC) (Z_to_bv 64 r) s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
              bvmap_empty (Z_to_bv 64 0x19468) (Z_to_bv 32 0) None m' (seg_rom rsegs)).
  Proof.
    intros until v'. intros MDH' MDL' FR ST' AINV' MI' MDF VOBJ' LEN SZ LIVEq REL LBp NLp FRK.
    pose proof alloc_ceiling_val as CV. unfold BCAT_STACK, EXT_STACK, REALLOC_STACK in *.
    pose proof (rw_cells_bound _ _ _ _ FR) as FB.
    rename ST' into STq.
    zstep. do 5 zstep. zstep. zstep.
    try replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    release_frame FR STq (bv_unsigned sp).
    cps_done.
    eapply K; try eassumption.
    apply FRK. eapply (stk_mapped (L:=LayoutPU)); [exact STq | exact CEIL | lia | lia].
  Qed.

  (* [comment removed for export] *)
  #[using="K SRC47 LO CEIL SRCHI LSRC"] Lemma bcat_copy : forall (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 : word) (junk8 : list byte)
      (A' : AS) (md' : Model) (mb mt : mem) (v1 : vsb_rec) (bs1 : list byte),
    m_halted md' = None -> m_vm_lazy md' = [] ->
    ainv A' mb md' ->
    munch [(bv_unsigned sp - 8352, bv_unsigned sp); (S, S + 40); (vb_buf v1, vb_buf v1 + vb_size v1)] mb mt ->
    wmono rsegs mb mt ->
    client_fp LayoutPU A' [(bv_unsigned sp - 8352, bv_unsigned sp); (S, S + 40); (vb_buf v1, vb_buf v1 + vb_size v1)] ->
    mem_inv rsegs mt -> md_frame md md' ->
    stk rsegs mt lo (bv_unsigned sp + -48) ->
    rw_cells rsegs mt (bv_unsigned sp + -48) [CB 8 junk8; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells rsegs mt S (vsb_cells v1) -> vsb_inv v1 false -> vb_error v1 = 0 -> vb_len v1 = vb_len v ->
    vb_len v1 + Z.of_nat (length src) < vb_size v1 ->
    a_live A' S = Some 40 -> a_live A' (vb_buf v1) = Some (vb_size v1) -> S <> vb_buf v1 ->
    u8arr rsegs mt (vb_buf v1) bs1 -> Z.of_nat (length bs1) = vb_size v1 ->
    bytes_at rsegs mt SRC src ->
    vb_size v <= vb_size v1 <= Z.max (vb_size v) (vb_len v1 + Z.of_nat (length src) + 4096) ->   (* [comment removed for export] *)
    (forall q, q <> vb_buf v -> q <> vb_buf v1 -> a_live A' q = a_live A q) ->
    (vb_buf v1 = vb_buf v \/ (a_live A (vb_buf v1) = None /\ a_live A' (vb_buf v) = None)) ->
    a_livebytes A' = a_livebytes A + vb_size v1 - vb_size v -> a_nlive A' = a_nlive A ->   (* [comment removed for export] *)
    4096 <= S -> S + 40 <= alloc_ceiling -> (S + 40 <= vb_buf v1 \/ vb_buf v1 + vb_size v1 <= S) ->
    vb_buf v1 + vb_size v1 <= alloc_ceiling ->
    (forall m'', munch [(bv_unsigned sp - 8352, bv_unsigned sp); (S, S + 40); (vb_buf v1, vb_buf v1 + vb_size v1)] mb m'' ->
                 mapped m'' (bv_unsigned sp - BCAT_STACK) BCAT_STACK ->
                 cframe LayoutPU (owned A) (owned A') (bv_unsigned sp) BCAT_STACK
                        (fun a => blk (vb_buf v) (vb_size v) a \/ (S <= a < S + 40)) (blk (vb_buf v1) (vb_size v1)) m m'') ->
    evt rsegs (rz_at rsegs md' T)
        (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp xt0 xt1 xt2 (Z_to_bv 64 S) (Z_to_bv 64 (Z.of_nat (length src)))
                 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 SRC) xs3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
            bvmap_empty (Z_to_bv 64 0x194dc) (Z_to_bv 32 0) None mt (seg_rom rsegs)).
  Proof.
    intros until bs1. intros MDH' MDL' AINVb MU WM CFP MIt MDF STt FR VSBC VINV1 E1 EL ROOM VLS1 VLB1 VNE1 U81 LBS1 BSRC1
           SZ1 LIVEq REL LBp NLp Slo Shi DSB1 Bhi1 CFK.
    pose proof alloc_ceiling_val as CV.
    unfold BCAT_STACK, EXT_STACK, REALLOC_STACK in *.
    pose proof VINV1 as VINV0. (first [ dand8 VINV1 as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm | destruct VINV1 as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm) ]).
    unfold vsb_cells in VSBC. rewrite E1 in VSBC.
    pose proof (rw_cells_bound _ _ _ _ VSBC) as SB. cbn [cells_size csize Nat.add length] in SB.
    pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize Nat.add length] in FB.
    pose proof (bytes_at_bound _ _ _ _ BSRC1) as SRCB.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. if_cases KT; zify_cond KT. { exfalso. unsign KT. decide_ltb KT. congruence. } clear KT.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. if_cases KT; zify_cond KT. { unsign KT. decide_ltb KT. dead KT. } clear KT.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (vb_len v1 + vb_buf v1) with (vb_buf v1 + vb_len v1) by lia.
    (first [ pose proof ((u8arr_window rsegs _ _ _ (Z.to_nat (vb_len v1)) (length src) U81 ltac:(lia))) as dR_2; dand3 dR_2 as U8a U8b U8c | destruct (u8arr_window rsegs _ _ _ (Z.to_nat (vb_len v1)) (length src) U81 ltac:(lia)) as (U8a & U8b & U8c) ]).
    pose proof (rw_cells_of_u8arr rsegs _ _ _ U8b) as DST. clear U8b U81.
    rewrite Z2Nat.id in DST, U8c by lia.
    rewrite firstn_length_le in DST by (rewrite skipn_length; lia).
    assert (LA : length (take (Z.to_nat (vb_len v1)) bs1) = Z.to_nat (vb_len v1)) by (rewrite firstn_length_le; lia).
    assert (LC : length (drop (Z.to_nat (vb_len v1) + length src) bs1) = (length bs1 - (Z.to_nat (vb_len v1) + length src))%nat)
      by (rewrite skipn_length; lia).
    call memcpy_spec_z.
    1:{ reflexivity. }
    1:{ exact BSRC1. }
    1:{ exact DST. }
    1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ assumption. }
    match goal with H : rw_cells rsegs ?mx (vb_buf v1 + vb_len v1) [CB (length src) src] |- _ =>
      pose proof (u8arr_of_rw_cells rsegs _ _ _ _ H) as U8b; clear H end.
    match goal with Ha : u8arr rsegs ?mx (vb_buf v1) ?pre, Hc : u8arr rsegs ?mx (vb_buf v1 + vb_len v1 + _) ?post |- _ =>
      pose proof (u8arr_unwindow rsegs mx (vb_buf v1) pre src post Ha
                    ltac:(rewrite LA, Z2Nat.id by lia; exact U8b)
                    ltac:(rewrite LA, Z2Nat.id by lia; exact Hc)) as U8n; clear Ha Hc U8b end.
    assert (LBn : Z.of_nat (length (take (Z.to_nat (vb_len v1)) bs1 ++ src ++ drop (Z.to_nat (vb_len v1) + length src) bs1)) = vb_size v1)
      by (rewrite !app_length, LA, LC; lia).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. if_cases KT; zify_cond KT. { exfalso. unsign KT. decide_ltb KT. congruence. } clear KT.
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (ainv_munch LayoutPU A' mb mx md' _ AINVb MU WM CFP) as AINV9 end.
    eapply bcat_epilogue with (v' := vsb_set_len v1 (vb_len v1 + Z.of_nat (length src))) (A' := A') (md' := md');
      [ exact MDH' | exact MDL' | exact FR | assumption | exact AINV9 | assumption | exact MDF
      | split; [ unfold vsb_cells; cbn [vb_error vb_buf vb_size vb_len vb_flags vb_indent vsb_set_len]; rewrite E1; exact VSBC |];
        split; [ unfold vsb_inv in *; cbn [vb_error vb_buf vb_size vb_len vb_flags vb_indent vsb_set_len]; lia |];
        split; [ exact VLS1 |]; split; [ exact VLB1 |]; split; [ exact VNE1 |];
        eexists; split; [ exact U8n |]; split; [ cbn [vsb_set_len vb_size]; exact LBn | intros X; discriminate X ]
      | cbn [vsb_set_len vb_len]; lia | cbn [vsb_set_len vb_size vb_len]; lia
      | cbn [vsb_set_len vb_buf]; exact LIVEq | cbn [vsb_set_len vb_buf]; exact REL
      | cbn [vsb_set_len vb_size]; exact LBp | exact NLp | ].
    unfold BCAT_STACK, EXT_STACK, REALLOC_STACK. cbn [vsb_set_len vb_buf vb_size]. intros MAP.
    apply CFK; [exact MU | exact MAP].
  Qed.

  #[using="W K SRC47 SPHI LO CEIL ST SP16 TP EM LBUD NBUD SRCHI LSRC BSRC VOBJ A2 A1 A0 MI AINV lo v src SRC S A AI Clg"] Lemma VSB_bcat_cps :
    realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               bvmap_empty (Z_to_bv 64 VSB_bcat_entry) (Z_to_bv 32 0) None m (seg_rom rsegs)) md) T.
  Proof.
    rewrite A0, A1, A2.
    pose proof (as_lazy_nil A m md AINV) as [MDL MDH].
    (first [ pose proof ((vsb_obj_geom LayoutPU A m md S v false AINV VOBJ)) as dR_3; dand11 dR_3 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LayoutPU A m md S v false AINV VOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    pose proof alloc_ceiling_val as CV.
    pose proof VOBJ as VOBJ0. vsb_open VOBJ0. (first [ dex1 VBUF as bs0; dand3 VBUF as U8 LBS _ | dand4 VBUF as bs0 U8 LBS _ | destruct VBUF as (bs0 & U8 & LBS & _) ]). cbn [al_segs LayoutPU] in U8.
    pose proof VINV as VINV0. (first [ dand8 VINV as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm | destruct VINV as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm) ]).
    pose proof (rw_cells_bound _ _ _ _ VSBC) as SB. cbn [cells_size csize Nat.add length] in SB.
    pose proof (bytes_at_bound _ _ _ _ BSRC) as SRCB.
    unfold BCAT_STACK, EXT_STACK, REALLOC_STACK, EXT_MAX in *. unfold VSB_bcat_entry.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (S8 : S mod 8 = 0) by (apply mod8_of_mod16; exact S16).
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl rsegs m) as WM.
    assert (CFP : client_fp LayoutPU A W).
    { subst W. cbn. split; [left; lia|]. split; [right; left; exists S, 40; split; [exact VLS|lia]|].
      split; [right; left; exists (vb_buf v), (vb_size v); split; [exact VLB|lia]| exact I]. }
    subst W.
    apply rz_go; [exact MDH | exact MDL |].
    carve_frame 48%nat ST.
    do 6 zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. call assert_integrity_spec.
    1:{ reflexivity. } 1:{ exact VSBC. } 1:{ exact VINV0. } 1:{ exact Slo. } 1:{ exact S8. } 1:{ assumption. }
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    call (assert_state_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ S v false).
    1:{ reflexivity. } 1:{ reflexivity. } 1:{ exact VSBC. } 1:{ exact VINV0. } 1:{ exact Slo. } 1:{ exact S8. } 1:{ assumption. }
    (* [comment removed for export] *)
    zstep. if_cases K6; zify_cond K6. { dead K6. } clear K6.
    zstep. if_cases K7; zify_cond K7. { exfalso. klia K7. } clear K7.
    zstep. zstep. if_cases KT; zify_cond KT. { exfalso. rewrite (land7_of_mod8 S) in KT by lia. klia KT. } clear KT.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases KE; zify_cond KE.
    2:{ (* [comment removed for export] *)
        exfalso. rewrite Verr in KE. revert KE. vm_compute. congruence. }
    (* [comment removed for export] *)
    assert (E0 : vb_error v = 0) by exact Verr.
    clear KE Verr.
    (* [comment removed for export] *)
    zstep. if_cases KL; zify_cond KL. { dead KL. } clear KL.
    (* [comment removed for export] *)
    zstep. zstep.
    call_lit vsb_indent_spec by (idtac;
      lazymatch goal with
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
      | |- rw_cells _ _ _ _ => exact VSBC
      | |- vsb_inv _ _ => exact VINV0
      | |- mem_inv _ _ => assumption
      | |- @eq word _ _ => reflexivity
      | |- _ => rewrite ?unsigned_lit by lia; lia
      end).
    rename POST into ST.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases KT; zify_cond KT. { exfalso. unsign KT. klia KT. } clear KT.
    zstep. zstep. zstep. zstep. zstep. if_cases KT; zify_cond KT. { exfalso. unsign KT. decide_ltb KT. congruence. } clear KT.
    replace (vb_size v - (vb_len v + 1)) with (vb_size v - vb_len v - 1) by lia.
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR; unsign KR.
    - (* [comment removed for export] *)
      eapply (bcat_copy _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A md m _ v bs0);
        [ exact MDH | exact MDL | exact AINV | exact MU | exact WM | exact CFP | assumption | exact (md_frame_refl _ MDL MDH)
        | exact ST | exact FR | exact VSBC | exact VINV0 | exact E0 | reflexivity | lia
        | exact VLS | exact VLB | exact VNE | exact U8 | exact LBS | exact BSRC
        | lia | intros q _ _; reflexivity | left; reflexivity
        | lia | reflexivity
        | exact Slo | exact Shi | exact DSB | exact Bhi | ].
      intros m'' MU'' MP. unfold BCAT_STACK, EXT_STACK, REALLOC_STACK in MU'', MP |- *.
      eapply (cframe_noalloc LayoutPU); [exact MU'' | | exact MP | intros a X; left; exact X].
      intros a Ha NO. cbn [outside] in NO. unfold blk. lia.
    - (* [comment removed for export] *)
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. if_cases KT; zify_cond KT.
      { exfalso. unsign KT. destruct (Z.lt_ge_cases 0 (vb_size v - vb_len v - 1)); decide_ltb KT; congruence. }
      clear KT.
      (* [comment removed for export] *)
      zstep. zstep.
      apply rz_stop.
      pose proof (ainv_munch LayoutPU A m _ md _ AINV MU WM CFP) as AINV1.
      lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
        pose proof (crange_stack (L:=LayoutPU) A mx md (bv_unsigned sp - 48) 48 AINV1 ltac:(lia) ltac:(lia)
                      (rw_cells_mapped LayoutPU mx _ _ FR ltac:(off_image_solve LayoutPU))) as CF;
        pose proof (crange_stack (L:=LayoutPU) A mx md SRC (Z.of_nat (length src)) AINV1 ltac:(lia) ltac:(lia)
                      (bytes_at_mapped LayoutPU mx _ _ BSRC ltac:(off_image_solve LayoutPU))) as CSRC end.
      eapply VSB_extend_cps;
        [ exact AINV1 | assumption | reflexivity | reflexivity
        | split; [exact VSBC|]; split; [exact VINV0|]; split; [exact VLS|]; split; [exact VLB|]; split; [exact VNE|];
          exists bs0; split; [exact U8|]; split; [exact LBS| intros X; discriminate X]
        | lia | unfold EXT_MAX; lia
        | eapply Z.le_trans; [| exact LBUD]; apply Z.add_le_mono_l; apply vsb_extendsize_mono; lia | exact NBUD | exact TP
        | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
        | rewrite unsigned_lit by lia; reflexivity
        | rewrite unsigned_lit by lia; exact ST | exact CEIL | rewrite unsigned_lit by lia; unfold EXT_STACK, REALLOC_STACK; lia
        | rewrite unsigned_lit by lia; lia | ].
      clear VSBC U8.
      intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' r A' m' md' v' AINV' MI' MDF VOBJ' LIVEq ST' OUT.
      pose proof (as_lazy_nil A' m' md' AINV') as [MDL' MDH'].
      rewrite unsigned_lit in OUT, ST' by lia.
      (first [ pose proof ((vsb_obj_geom LayoutPU A' m' md' S v' false AINV' VOBJ')) as dR_6; dand11 dR_6 as _ _ _ _ B16' Blo' Bhi' Bimg' DSB' Smap' Bmap' | pose proof (vsb_obj_geom LayoutPU A' m' md' S v' false AINV' VOBJ') as (_ & _ & _ & _ & B16' & Blo' & Bhi' & Bimg' & DSB' & Smap' & Bmap') ]).
      clear Bimg'.
      pose proof VOBJ' as VOBJ1. vsb_open VOBJ1. (first [ dex1 VBUF as bs1; dand3 VBUF as U8n LBS1 _ | dand4 VBUF as bs1 U8n LBS1 _ | destruct VBUF as (bs1 & U8n & LBS1 & _) ]). cbn [al_segs LayoutPU] in U8n.
      pose proof VINV as VINV1. (first [ dand8 VINV as Vsz' Vlen' Verr' Vind' Vfl' Vb0' Vb47' Vbm' | destruct VINV as (Vsz' & Vlen' & Verr' & Vind' & Vfl' & Vb0' & Vb47' & Vbm') ]).
      (* [comment removed for export] *)
      destruct OUT as (nb & Er & Ev & COPY & REL & LBx & NLx & FRK); subst r; unfold EXT_STACK, REALLOC_STACK in FRK.
      + (* [comment removed for export] *)
        subst v'. cbn [vb_buf vb_size vb_len vb_error vb_flags vb_indent vsb_set_buf_size] in FRK, VSBC, VLS0, VLB0, VNE0, U8n, LBS1, VINV1,
          Vsz', Vlen', Verr', Vind', Vfl', Vb0', Vb47', Vbm', B16', Blo', Bhi', DSB', Smap', Bmap', REL, LIVEq |- *.
        (first [ pose proof ((vsb_extendsize_spec (vb_size v + (Z.of_nat (length src) - (vb_size v - vb_len v - 1))) ltac:(lia))) as dR_9; dand3 dR_9 as NS1 NS2 NS3 | pose proof (vsb_extendsize_spec (vb_size v + (Z.of_nat (length src) - (vb_size v - vb_len v - 1))) ltac:(lia)) as (NS1 & NS2 & NS3) ]).
        pose proof (vsb_extendsize_tight (vb_size v + (Z.of_nat (length src) - (vb_size v - vb_len v - 1)))) as NST.
        set (nsz := vsb_extendsize (vb_size v + (Z.of_nat (length src) - (vb_size v - vb_len v - 1)))) in *.
        clear ST. acall_xfer FRK. clear AINV1. rename ST' into ST.
        set (W2 := [(bv_unsigned sp - 8352, bv_unsigned sp); (S, S + 40); (nb, nb + nsz)]).
        pose proof (munch_refl W2 m') as MU2. pose proof (wmono_refl rsegs m') as WM2.
        assert (CFP2 : client_fp LayoutPU A' W2)
          by (subst W2; cbn; split; [left; lia|]; split; [right; left; exists S, 40; split; [exact VLS0|lia]|];
              split; [right; left; exists nb, nsz; split; [exact VLB0|lia]| exact I]).
        subst W2.
        rz_resume MDH' MDL'.
        zstep. if_cases KX; zify_cond KX. { dead KX. } clear KX.
        (* [comment removed for export] *)
        unfold vsb_cells in VSBC. rewrite E0 in VSBC.
        zstep. zstep. if_cases KY; zify_cond KY. { exfalso. dead KY. } clear KY.
        eapply (bcat_copy _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A' md' m' _ (vsb_set_buf_size v nb nsz) bs1);
          [ exact MDH' | exact MDL' | exact AINV' | exact MU2 | exact WM2 | exact CFP2 | assumption | exact MDF
          | exact ST | exact FR | unfold vsb_cells; cbn [vb_buf vb_size vb_len vb_error vb_flags vb_indent vsb_set_buf_size]; rewrite E0; exact VSBC
          | exact VINV1 | exact E0 | reflexivity | cbn [vb_size vb_len vsb_set_buf_size]; lia
          | exact VLS0 | exact VLB0 | exact VNE0 | exact U8n | exact LBS1 | assumption
          | cbn [vb_size vb_len vsb_set_buf_size]; lia | exact LIVEq | exact REL
          | cbn [vb_size vsb_set_buf_size]; first [exact LBx | subst nsz; lia] | exact NLx
          | exact Slo | exact Shi | exact DSB' | exact Bhi' | ].
        intros m'' MU'' MP. unfold BCAT_STACK, EXT_STACK, REALLOC_STACK in MU'', MP |- *.
        cbn [vb_size vb_len vb_buf vsb_set_buf_size] in MU'' |- *.
        eapply (cframe_extend LayoutPU _ _ _ _ _ _ _ _ _ _ m _ m' _ _ _);
          [ exact MU | | exact FRK | lia | lia | intros a X; exact X
          | intros a X; left; exact X
          | exact MU'' | | exact MP ].
        * intros a Ha NO. cbn [outside] in NO. unfold blk. lia.
        * intros a Ha NO. cbn [outside] in NO. unfold blk. lia.
  Qed.
End S.
End U_VSdg2.

Module U_verhp.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World U_Img ImgU U_Cov8m.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_VS58t.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_VS58t OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_ve2lq.U_VSdg2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutPU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutPU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac akit_plia := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker.
Ltac akit_avoids_false X :=
  lazymatch type of X with
  | _ \/ _ => destruct X as [X|X]; akit_avoids_false X
  | False => destruct X
  | _ => try (lazymatch type of X with (_ <> _) /\ _ => destruct X as [_ X] end);
         first [ match goal with D : _ \/ _ |- _ => solve [ destruct D; akit_plia ] end | akit_plia ]
  end.
Local Ltac avoids_solve ::=
  cbn [Cells.cells_size Cells.csize Nat.add length app];
  split; [ lia | intros ? ? X; unfold blk, nowhere in X; cbn beta in X; first [ solve [ akit_avoids_false X ] | lia ] ].
(* [comment removed for export] *)


(* [comment removed for export] *)
Lemma be64_redecode_pub : forall l, 0 <= l < 2^62 ->
  Z.lor (Z.shiftl (Z.lor (Z.lor (Z.shiftr (Z.shiftl (l / 281474976710656) 56 mod 18446744073709551616) 40)
                                (Z.shiftl (l / 72057594037927936) 24 mod 18446744073709551616))
                         (Z.lor (Z.shiftr (Z.shiftl (l / 1099511627776) 56 mod 18446744073709551616) 48)
                                (Z.land (l / 4294967296) 255))) 32 mod 18446744073709551616)
        (l mod 4294967296) = l.
Proof.
  intros l Hl.
  rewrite !Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  set (A := l / 281474976710656 * 2 ^ 56 mod 18446744073709551616 / 2 ^ 40).
  set (B := l / 72057594037927936 * 2 ^ 24 mod 18446744073709551616).
  set (C := l / 1099511627776 * 2 ^ 56 mod 18446744073709551616 / 2 ^ 48).
  set (D := (l / 4294967296) mod 2 ^ 8).
  assert (EA : A = ((l / 281474976710656) mod 2^8) * 2^16) by (subst A; lia).
  assert (EB : B = (l / 72057594037927936) * 2^24 /\ 0 <= l / 72057594037927936 < 2^6) by (subst B; lia).
  assert (EC : C = ((l / 1099511627776) mod 2^8) * 2^8) by (subst C; lia).
  assert (ED : 0 <= D < 2^8) by (subst D; lia).
  rewrite (lor_add' A B 24) by lia.
  rewrite (lor_add C D 8) by lia.
  rewrite (lor_add (A + B) (C + D) 16) by lia.
  rewrite (Z.mod_small ((A + B + (C + D)) * 2^32)) by lia.
  rewrite (lor_add ((A + B + (C + D)) * 2^32) (l mod 4294967296) 32) by lia.
  subst D. lia.
Qed.

(* [comment removed for export] *)
Definition emit_seg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (VEP l : Z) (raw : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a3 a4 a5 a6 a7 : word) (m' : mem) (j15 w9 code : list byte),
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 VEP) a1
                 (Z_to_bv 64 (Z.of_nat (length code))) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x1c428) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' (bv_unsigned sp + -32) [CB 15 j15; CB 9 w9; C8 raw]
    /\ bytes_at rsegs m' (bv_unsigned sp + -17) code /\ 1 <= Z.of_nat (length code) <= 9 /\ Z.of_nat (length code) <= 2 + l.

Local Ltac sb1 := zstep; rewrite le1_byte, unsigned_lit by lia; mem_after_store_opt.

(* [comment removed for export] *)
Local Ltac seg_finish spv FR MU WM w9 code :=
  let WF := fresh "WF" in
  pose proof FR as [[WF _] _]; cbn [cells_wf cell_wf] in WF;
  lazymatch type of FR with rw_cells _ ?mx ?A (CB 15 ?x :: ?rest) =>
    lazymatch rest with context [C8 ?rw] =>
    apply (rw_cells_recast rsegs mx A _ [CB 15 x; CB 9 w9; C8 rw]) in FR;
      [ | cbn [cells_wf cell_wf length]; cbn [length] in WF; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia
        | cbn [cells_bytes cbytes app]; reflexivity ];
    let B := fresh "B" in
    pose proof (rw_cells_bytes_at_cell rsegs mx A _ 15 (CB 9 w9) FR eq_refl) as B;
    cbn [cbytes] in B;
    replace (A + Z.of_nat 15) with (bv_unsigned spv + -17) in B by lia;
    apply (bytes_at_prefix rsegs mx _ code) in B;
    apply evt_done; unfold emit_seg_post;
    do 9 eexists; eexists mx, x, w9, code;
    split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [assumption|];
    split; [exact FR|]; split; [exact B| cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia]
  end end.

(* [comment removed for export] *)
Local Ltac ubguard K :=
  exfalso;
  lazymatch goal with S1 : (bv_unsigned ?x + 64 <= _)%Z, S0 : (64 <= bv_unsigned ?x)%Z |- _ =>
    revert K S1 S0; clear; intros K S1 S0; first [rewrite Z.mod_small in K by lia | idtac]; lia end.

Lemma emit_code_seg :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (VEP l c8 c16 c64 : Z) (j24 : list byte) (raw : word),
    1 <= l < 2^62 -> 0 <= c8 < 256 -> 0 <= c16 < 256 -> 0 <= c64 < 256 ->
    64 <= bv_unsigned sp -> bv_unsigned sp + 64 <= 2^47 -> 0 <= VEP < 2^64 -> VEP mod 8 = 0 ->
    rw_cells rsegs m (bv_unsigned sp + -32) [CB 24 j24; C8 raw] -> mem_inv rsegs m ->
    evt rsegs (emit_seg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc VEP l raw m)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 VEP) (Z_to_bv 64 l)
               (Z_to_bv 64 c8) (Z_to_bv 64 c16) (Z_to_bv 64 c64) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1c2fc) fc None m (seg_rom rsegs)).
Proof.
  intros until raw. intros HL HC8 HC16 HC64 SPLO SPHI VR V8 FR MI.
  pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (L7 : Z.land VEP 7 = 0) by (apply land7_of_mod8; lia).
  (* [comment removed for export] *)
  zstep. zstep. if_cases K1; zify_cond K1.
  - (* [comment removed for export] *)
    zstep. rewrite !Z.shiftr_div_pow2 by lia. zstep. if_cases K2; zify_cond K2.
    + (* [comment removed for export] *)
      (* [comment removed for export] *)
      zstep. zstep. sb1. zstep. if_cases G; zify_cond G. { ubguard G. } clear G.
      (* [comment removed for export] *)
      zstep. zstep. rewrite !Z.shiftr_div_pow2 by lia. sb1. zstep. if_cases G; zify_cond G. { ubguard G. } clear G.
      (* [comment removed for export] *)
      zstep. rewrite !Z.shiftr_div_pow2 by lia. zstep. sb1. zstep. if_cases G; zify_cond G. { ubguard G. } clear G.
      (* [comment removed for export] *)
      zstep. rewrite !Z.shiftr_div_pow2 by lia. zstep. sb1. zstep. if_cases G; zify_cond G. { ubguard G. } clear G.
      (* [comment removed for export] *)
      zstep. rewrite !Z.shiftr_div_pow2 by lia. sb1. zstep. if_cases G; zify_cond G. { ubguard G. } clear G.
      (* [comment removed for export] *)
      zstep. zstep. rewrite !Z.shiftr_div_pow2 by lia. zstep. sb1. zstep. if_cases G; zify_cond G. { ubguard G. } clear G.
      (* [comment removed for export] *)
      zstep. sb1. zstep. if_cases G; zify_cond G. { ubguard G. } clear G.
      (* [comment removed for export] *)
      zstep. rewrite !Z.shiftr_div_pow2 by lia. zstep. sb1. zstep. if_cases G; zify_cond G. { ubguard G. } clear G.
      (* [comment removed for export] *)
      do 13 zstep. sb1.
      zstep. if_cases KT; zify_cond KT.
      { exfalso. apply KT. apply be64_redecode_pub. clear - HL; lia. }
      clear KT.
      (* [comment removed for export] *)
      zstep. rewrite L7. zstep. if_cases G; zify_cond G. { exfalso. apply G. reflexivity. } clear G.
      zstep.
      lazymatch type of FR with rw_cells _ _ _ [_; C1 ?b0; C1 ?b1; C1 ?b2; C1 ?b3; C1 ?b4; C1 ?b5; C1 ?b6; C1 ?b7; C1 ?b8; _] =>
        seg_finish sp FR MU WM [b0; b1; b2; b3; b4; b5; b6; b7; b8] [b0; b1; b2; b3; b4; b5; b6; b7; b8] end.
    + (* [comment removed for export] *)
      zstep. zstep. sb1. zstep. if_cases G; zify_cond G. { ubguard G. } clear G.
      zstep. zstep. rewrite !Z.shiftr_div_pow2 by lia. sb1. zstep. if_cases G; zify_cond G. { ubguard G. } clear G.
      zstep. rewrite L7. sb1. zstep. if_cases G; zify_cond G. { exfalso. apply G. reflexivity. } clear G.
      zstep. zstep.
      lazymatch type of FR with rw_cells _ _ _ [_; C1 ?b0; C1 ?b1; C1 ?b2; CB 6 ?r; _] =>
        seg_finish sp FR MU WM (b0 :: b1 :: b2 :: r) [b0; b1; b2] end.
  - (* [comment removed for export] *)
    zstep. zstep. sb1. zstep. if_cases G; zify_cond G. { ubguard G. } clear G.
    zstep. rewrite L7. sb1. zstep. if_cases G; zify_cond G. { exfalso. apply G. reflexivity. } clear G.
    zstep. zstep.
    lazymatch type of FR with rw_cells _ _ _ [_; C1 ?b0; C1 ?b1; CB 7 ?r; _] =>
      seg_finish sp FR MU WM (b0 :: b1 :: r) [b0; b1] end.
Qed. (* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.

  Lemma vep_emit_len_ok : vep_emit_len_stmt.
  Proof.
    unfold vep_emit_len_stmt.
    intros VEP v tag q vv l c8 c16 c64 lo. intros until T.
    intros AINV MI A0 A1 A2 A3 A4 HL HC8 HC16 HC64 VOBJ SOBJ NES NEB EM LBUD NBUD TP SP16 RA2 ST CEIL LO SPHI K.
    rewrite A0, A1, A2, A3, A4.
    pose proof (as_lazy_nil A m md AINV) as [MDL MDH].
    pose proof (as_layout_order (L:=LayoutPU)) as LAY. cbn [al_image_lo al_rw_lo al_image_hi LayoutPU] in LAY.
    pose proof alloc_ceiling_val as ACV.
    unfold EMITLEN_STACK, REALLOC_STACK in *. unfold vep_emit_len_entry.
    (* [comment removed for export] *)
    (first [ dand4 VOBJ as VLV VEPC TAG PADS | destruct VOBJ as (VLV & VEPC & TAG & PADS) ]). cbn [al_segs LayoutPU] in VEPC.
    (first [ pose proof ((as_live_ok A m md VEP _ AINV VLV)) as dR_2; dand7 dR_2 as _ V16 Vlo Vhi Vimg Vmap Vown | pose proof (as_live_ok A m md VEP _ AINV VLV) as (_ & V16 & Vlo & Vhi & Vimg & Vmap & Vown) ]). clear Vimg.
    (first [ pose proof (PADS) as dR_3; dand7 dR_3 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]).
    unfold vep_cells in VEPC.
    (* [comment removed for export] *)
    (first [ pose proof ((vsb_obj_geom LayoutPU A m md (v Fvsb) vv false AINV SOBJ)) as dR_4; dand11 dR_4 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LayoutPU A m md (v Fvsb) vv false AINV SOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    pose proof SOBJ as SOBJ0. vsb_open SOBJ0. (first [ dex1 VBUF as bs0; dand3 VBUF as U8 LBS _ | dand4 VBUF as bs0 U8 LBS _ | destruct VBUF as (bs0 & U8 & LBS & _) ]). cbn [al_segs LayoutPU] in U8.
    unfold vsb_cells in VSBC.
    pose proof (as_live_disjoint A m md VEP 312 (v Fvsb) 40 AINV VLV VLS NES) as DVS.
    pose proof (as_live_disjoint A m md VEP 312 (vb_buf vv) (vb_size vv) AINV VLV VLB NEB) as DVB.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 8384, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (CFP : client_fp LayoutPU A [(bv_unsigned sp - 8384, bv_unsigned sp)]).
    { cbn. split; [left; lia| exact I]. }
    apply rz_go; [exact MDH | exact MDL |].
    carve_frame 32%nat ST.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases KA; zify_cond KA. { exfalso. klia KA. } try clear KA.
    (* [comment removed for export] *)
    eapply evt_cut; [eapply emit_code_seg; [exact HL | exact HC8 | exact HC16 | exact HC64 | lia | lia | lia | clear - V16; lia | exact FR | assumption] |].
    cbv beta. intros ms' POST.
    (first [ dex13 POST as xt0 xt1 xt2 xa1 xa3 xa4 xa5 xa6 xa7 m' j15 w9 code; dand8 POST as -> MUs WMs MI' FR' BSRC LSRC LCODE | dand21 POST as xt0 xt1 xt2 xa1 xa3 xa4 xa5 xa6 xa7 m' j15 w9 code -> MUs WMs MI' FR' BSRC LSRC LCODE | destruct POST as (xt0 & xt1 & xt2 & xa1 & xa3 & xa4 & xa5 & xa6 & xa7 & m' & j15 & w9 & code & -> & MUs & WMs & MI' & FR' & BSRC & LSRC & LCODE) ]).
    lazymatch type of MUs with munch _ ?mq _ => transport_after_call rsegs mq m' MUs WMs; clear MUs WMs; try clear mq end.
    rename FR' into FR.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    apply rz_stop.
    pose proof (ainv_munch LayoutPU A m _ md _ AINV MU WM CFP) as AINV1.
    lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => pose_cranges LayoutPU A mx AINV1 end.
    eapply (VSB_bcat_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ md A (v Fvsb) (bv_unsigned sp + -17) code vv lo);
      [ exact AINV1 | assumption | reflexivity | reflexivity | reflexivity | vsb_close | exact BSRC | exact LSRC
      | rewrite unsigned_lit by lia; lia | exact EM | exact LBUD | exact NBUD | exact TP
      | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
      | rewrite unsigned_lit by lia; exact ST | exact CEIL
      | rewrite unsigned_lit by lia; unfold BCAT_STACK, EXT_STACK, REALLOC_STACK; lia
      | rewrite unsigned_lit by lia; lia | lia | ].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A' m2 md' vv' AINV' MI2 MDF SOBJ' LEN SZ LIVEq REL LBp NLp ST' FRK.
    pose proof (as_lazy_nil A' m2 md' AINV') as [MDL' MDH'].
    rewrite unsigned_lit in ST', FRK by lia. unfold BCAT_STACK, EXT_STACK, REALLOC_STACK in FRK.
    (* [comment removed for export] *)
    (first [ pose proof ((vsb_obj_geom LayoutPU A' m2 md' (v Fvsb) vv' false AINV' SOBJ')) as dR_7; dand7 dR_7 as _ _ _ _ _ Blo' _ | pose proof (vsb_obj_geom LayoutPU A' m2 md' (v Fvsb) vv' false AINV' SOBJ') as (_ & _ & _ & _ & _ & Blo' & _) ]).
    pose proof (proj1 (proj2 SOBJ')) as VINV'. pose proof (proj1 VINV') as Vsz'.
    assert (NEB2 : VEP <> vb_buf vv').
    { intros E. eapply (blk_avoids_crange LayoutPU A A' m' m2 _ _ _ (vb_buf vv') (vb_size vv') VEP 312 FRK CR1); try lia.
      intros x Hx [X|X]; unfold blk in X; lia. }
    clear ST. try clear VSBC. try clear BSRC. try clear U8. acall_xfer FRK. rename ST' into ST.
    rz_resume MDH' MDL'.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    try replace (bv_unsigned sp + -32 + 32) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    release_frame FR ST (bv_unsigned sp).
    cps_done.
    eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A' m2 md' vv');
      [ exact AINV' | exact MI2 | exact MDF | exact ST
      | split; [rewrite (LIVEq VEP NEB NEB2); exact VLV|]; split; [exact VEPC|]; split; [exact TAG| exact PADS]
      | exact SOBJ' | lia | lia | exact REL | exact LIVEq | exact LBp | exact NLp | ].
    eapply (cframe_extend LayoutPU _ _ _ _ _ _ _ _ _ _ m _ _ m2 _ []);
      [ exact MU | | exact FRK | lia | lia | intros a X; exact X | intros a X; left; exact X
      | apply munch_refl | intros a _ X; exfalso; apply X; exact I
      | eapply (stk_mapped (L:=LayoutPU)); [exact ST | exact CEIL | lia | lia] ].
    intros a Ha NO. cbn [outside] in NO. lia.
  Qed.
End S.
End U_verhp.

Module U_veyab.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World U_Img ImgU U_Cov8m.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_VS58t.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_crc32.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_crc32.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_VS58t OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_crc32.U_cromo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_crc32 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_ve2lq.U_verhp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutPU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutPU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac call_consts_in H ::= unfold CRC_FRAME_U in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@LO; @CEIL; @ACV; @TAG; @P36; @P124; @P140; @P196; @P236; @P268; @P308; @SPHI; @Vlo; @Blo; @Slo; @HTOT; @HT0; @HL0; @LBS; @NES; @VNE; @DVS; @Vhi; @NEB; @L1; @Vsz'; @SP16; @V16; @S16; @B16; @DSB; @DVB; @Hx; @X1; @NEB1; @H; @NO; @KZ; @H0; @KB; @Blo'; @E; @Bhi; @Shi; @KS; @KO; @KA; @KT; @KD])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac akit_plia := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker.
Ltac akit_avoids_false X :=
  lazymatch type of X with
  | _ \/ _ => destruct X as [X|X]; akit_avoids_false X
  | False => destruct X
  | _ => try (lazymatch type of X with (_ <> _) /\ _ => destruct X as [_ X] end);
         first [ match goal with D : _ \/ _ |- _ => solve [ destruct D; akit_plia ] end | akit_plia ]
  end.
Local Ltac avoids_solve ::=
  cbn [Cells.cells_size Cells.csize Nat.add length app];
  split; [ lia | intros ? ? X; unfold blk, nowhere in X; cbn beta in X; first [ solve [ akit_avoids_false X ] | lia ] ].
(* [comment removed for export] *)

(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.
  Variables (VEP : Z) (v : vep) (tag : list byte) (q : vep_pads) (vv : vsb_rec) (l mark : Z) (lo : Z).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (m : mem) (md : Model) (A : AS) (T : TSet).
  Hypothesis AINV : ainv A m md.
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis A0 : a0 = Z_to_bv 64 VEP.
  Hypothesis A1 : a1 = Z_to_bv 64 l.
  Hypothesis A2 : a2 = Z_to_bv 64 mark.
  Hypothesis HL0 : 0 <= l.
  Hypothesis HTOT : v Fo_total + l < 2^62.
  Hypothesis HT0 : 0 <= v Fo_total.
  Hypothesis HMK : bool01 mark.
  Hypothesis VOBJ : vep_obj LayoutPU A m VEP v tag q.
  Hypothesis DZ : v Fdogzip = 0.
  Hypothesis SOBJ : vsb_obj LayoutPU A m (v Fvsb) vv false.
  Hypothesis NES : VEP <> v Fvsb.
  Hypothesis NEB : VEP <> vb_buf vv.
  Hypothesis EM : vb_size vv + 9 <= EXT_MAX.
  (* [comment removed for export] *)
  Hypothesis LBUD : a_livebytes A + vsb_extendsize (vb_size vv + 9) <= LIVE_MAX.
  Hypothesis NBUD : a_nlive A + 1 <= NLIVE_MAX.
  Hypothesis TP : tp = al_tp LayoutPU.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + EMITC_STACK <= bv_unsigned sp.
  Hypothesis SPHI : bv_unsigned sp + 64 <= 2^47.
  Hypothesis K : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
              (v' : vep) (vv' : vsb_rec),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          stk rsegs m' lo (bv_unsigned sp) ->
          vep_obj LayoutPU A' m' VEP v' tag q ->
          (   (l = 0 /\ v' = v /\ vv' = vv)
           \/ (1 <= l /\ exists c, v' = fupd (fupd (fupd v Fcrc c) Fo_crc 0) Fo_total (v Fo_total + l))) ->
          vsb_obj LayoutPU A' m' (v Fvsb) vv' false ->
          vb_len vv <= vb_len vv' <= vb_len vv + Z.min 9 (2 + l) ->
          vb_size vv <= vb_size vv' <= Z.max (vb_size vv) (vb_len vv' + 4096) ->
          (vb_buf vv' = vb_buf vv \/ (a_live A (vb_buf vv') = None /\ a_live A' (vb_buf vv) = None)) ->
          (forall p, p <> vb_buf vv -> p <> vb_buf vv' -> a_live A' p = a_live A p) ->
          a_livebytes A' = a_livebytes A + vb_size vv' - vb_size vv -> a_nlive A' = a_nlive A ->   (* [comment removed for export] *)
          cframe LayoutPU (owned A) (owned A') (bv_unsigned sp) EMITC_STACK
                 (fun a => blk VEP 312 a \/ blk (vb_buf vv) (vb_size vv) a \/ (v Fvsb <= a < v Fvsb + 40))
                 (blk (vb_buf vv') (vb_size vv')) m m' ->
          realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T.

  (* [comment removed for export] *)
  #[using="K SPHI LO CEIL SP16 NES VOBJ HT0 HTOT HL0"] Lemma ec_tail :
    forall (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (j16 : list byte)
           (Ax : AS) (mq mc : mem) (mdx : Model) (vv1 : vsb_rec),
      m_halted mdx = None -> m_vm_lazy mdx = [] ->
      ainv Ax mc mdx -> mem_inv rsegs mc -> md_frame md mdx ->
      stk rsegs mc lo (bv_unsigned sp + -48) ->
      rw_cells rsegs mc (bv_unsigned sp + -48) [CB 16 j16; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells rsegs mc VEP (vep_cells v tag q) -> a_live Ax VEP = Some 312 ->
      vsb_obj LayoutPU Ax mc (v Fvsb) vv1 false ->
      vb_len vv <= vb_len vv1 <= vb_len vv + Z.min 9 (2 + l) ->
      vb_size vv <= vb_size vv1 <= Z.max (vb_size vv) (vb_len vv1 + 4096) ->
      (vb_buf vv1 = vb_buf vv \/ (a_live A (vb_buf vv1) = None /\ a_live Ax (vb_buf vv) = None)) ->
      (forall p, p <> vb_buf vv -> p <> vb_buf vv1 -> a_live Ax p = a_live A p) ->
      a_livebytes Ax = a_livebytes A + vb_size vv1 - vb_size vv -> a_nlive Ax = a_nlive A ->
      1 <= l -> VEP <> vb_buf vv1 ->
      munch [(bv_unsigned sp - EMITC_STACK, bv_unsigned sp)] m mq ->
      cframe LayoutPU (owned A) (owned Ax) (bv_unsigned sp + -48) EMITLEN_STACK
             (fun a => blk (vb_buf vv) (vb_size vv) a \/ (v Fvsb <= a < v Fvsb + 40)) (blk (vb_buf vv1) (vb_size vv1)) mq mc ->
      evt rsegs (rz_at rsegs mdx T)
          (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp xt0 xt1 xt2 (Z_to_bv 64 VEP) (Z_to_bv 64 l)
                   xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 1) s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
              bvmap_empty (Z_to_bv 64 0x1c1f8) (Z_to_bv 32 0) None mc (seg_rom rsegs)).
  Proof.
    intros until vv1. intros MDH1 MDL1 AINV1 MI1 MDF1 ST1 FR VEPC VLV1 SOBJ1 LEN SZ REL LIVEq LBp NLp L1 NEB1 MU0 FRK.
    pose proof alloc_ceiling_val as ACV. unfold EMITC_STACK, EMITLEN_STACK, REALLOC_STACK in *.
    destruct VOBJ as (VLV & _ & TAG & PADS).
    (first [ pose proof ((as_live_ok Ax mc mdx VEP _ AINV1 VLV1)) as dR_1; dand7 dR_1 as _ V16 Vlo Vhi Vimg Vmap Vown | pose proof (as_live_ok Ax mc mdx VEP _ AINV1 VLV1) as (_ & V16 & Vlo & Vhi & Vimg & Vmap & Vown) ]). clear Vimg.
    (first [ pose proof (PADS) as dR_2; dand7 dR_2 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]).
    unfold vep_cells in VEPC.
    pose proof SOBJ1 as SOBJ2. vsb_open SOBJ2. (first [ dex1 VBUF as bs1; dand3 VBUF as U8 LBS _ | dand4 VBUF as bs1 U8 LBS _ | destruct VBUF as (bs1 & U8 & LBS & _) ]). cbn [al_segs LayoutPU] in U8.
    (first [ pose proof ((vsb_obj_geom LayoutPU Ax mc mdx (v Fvsb) vv1 false AINV1 SOBJ1)) as dR_4; dand11 dR_4 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LayoutPU Ax mc mdx (v Fvsb) vv1 false AINV1 SOBJ1) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    pose proof (as_live_disjoint Ax mc mdx VEP 312 (v Fvsb) 40 AINV1 VLV1 VLS NES) as DVS.
    pose proof (as_live_disjoint Ax mc mdx VEP 312 (vb_buf vv1) (vb_size vv1) AINV1 VLV1 VLB NEB1) as DVB.
    pose proof (munch_refl [(bv_unsigned sp - 8432, bv_unsigned sp); (VEP, VEP + 312)] mc) as MU.
    pose proof (wmono_refl rsegs mc) as WM.
    assert (CFP : client_fp LayoutPU Ax [(bv_unsigned sp - 8432, bv_unsigned sp); (VEP, VEP + 312)]).
    { cbn. split; [left; lia|]. split; [right; left; exists VEP, 312; split; [exact VLV1|lia]| exact I]. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    call_fr crc32_null_spec by (first [assumption | rewrite unsigned_lit by lia; first [exact ST1 | reflexivity | assumption | lia]]).
    (* [comment removed for export] *)
    zstep. if_cases KS; zify_cond KS. { exfalso. clear - KS. lia. } clear KS.
    zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. if_cases KO; zify_cond KO.
    { exfalso. revert KO HL0 HTOT HT0. clear. intros KO HL0 HTOT HT0.
      unsign KO.
      destruct (Z.ltb_spec (l + 9223372036854775808) 9223372036854775808);
      destruct (Z.ltb_spec (v Fo_total + l + 9223372036854775808) (v Fo_total + 9223372036854775808)); cbn in KO; lia. }
    clear KO.
    zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    try replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    lazymatch goal with S : stk _ _ lo _ |- _ => release_frame FR S (bv_unsigned sp) end.
    cps_done.
    lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
      lazymatch type of MU with munch ?W _ _ =>
        pose proof (ainv_munch LayoutPU Ax mc mx mdx W AINV1 MU WM CFP) as AINV9 end end.
    lazymatch type of VEPC with context [C4 ?cw :: CB 4 (p124 q) :: _] =>
    eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ax _ mdx (fupd (fupd (fupd v Fcrc (bv_unsigned cw)) Fo_crc 0) Fo_total (v Fo_total + l)) vv1);
      [ exact AINV9 | assumption | exact MDF1 | assumption
      | split; [exact VLV1|]; split; [unfold vep_cells; cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; rewrite Z_to_bv_bv_unsigned; exact VEPC|];
        split; [exact TAG| exact PADS]
      | right; split; [exact L1| eexists; reflexivity]
      | vsb_close | exact LEN | exact SZ | exact REL | exact LIVEq | exact LBp | exact NLp | ] end.
    lazymatch goal with |- cframe _ _ _ _ _ _ _ _ ?mx =>
    eapply (cframe_extend LayoutPU _ _ _ _ _ _ _ _ _ _ m _ mc mx _ _);
      [ exact MU0 | | exact FRK | lia | lia | intros a X; right; exact X | intros a X; left; exact X
      | exact MU | | eapply (stk_mapped (L:=LayoutPU)); [eassumption | exact CEIL | lia | lia] ] end.
    - intros a Ha NO. cbn [outside] in NO. lia.
    - intros a Ha NO. cbn [outside] in NO. unfold blk. lia.
  Qed. (* [comment removed for export] *)

  Local Ltac call_emit_len c8 c16 c64 :=
    lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
      lazymatch goal with MUx : munch ?W m mx, WMx : wmono _ m mx, CFPx : client_fp _ A ?W |- _ =>
      pose proof (ainv_munch LayoutPU A m mx md W AINV MUx WMx CFPx) as AINV1;
      pose_cranges LayoutPU A mx AINV1;
      eapply (vep_emit_len_ok VEP v tag q vv l c8 c16 c64 lo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx md A T);
      [ exact AINV1 | assumption | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | lia | lia | lia | lia
      | split; [| split; [eassumption| split; assumption]]; assumption
      | vsb_close | exact NES | exact NEB | exact EM | exact LBUD | exact NBUD | exact TP
      | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
      | rewrite unsigned_lit by lia; reflexivity
      | rewrite unsigned_lit by lia; eassumption | exact CEIL
      | rewrite unsigned_lit by lia; unfold EMITLEN_STACK, REALLOC_STACK; lia
      | rewrite unsigned_lit by lia; lia | ]
      end end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac after_emit_len :=
    lazymatch goal with FRK : cframe _ _ _ _ _ _ (blk (vb_buf ?vv') (vb_size ?vv')) ?mx ?m', AINV' : ainv ?A' ?m' ?md',
                        SOBJ' : vsb_obj _ ?A' ?m' _ ?vv' false, C : crange A ?mx VEP _,
                        LEN : (vb_len vv <= vb_len ?vv' <= _)%Z, SZ : (vb_size vv <= vb_size ?vv' <= _)%Z,
                        REL : (vb_buf ?vv' = vb_buf vv \/ _) |- _ =>
      let X := fresh "MDL'" in let Y := fresh "MDH'" in
      pose proof (as_lazy_nil A' m' md' AINV') as [X Y];
      rewrite unsigned_lit in * by lia; unfold EMITLEN_STACK, REALLOC_STACK in *;
      (first [ pose proof ((vsb_obj_geom LayoutPU A' m' md' (v Fvsb) vv' false AINV' SOBJ')) as dR_5; dand7 dR_5 as _ _ _ _ _ Blo' _ | pose proof (vsb_obj_geom LayoutPU A' m' md' (v Fvsb) vv' false AINV' SOBJ') as (_ & _ & _ & _ & _ & Blo' & _) ]);
      pose proof (proj1 (proj1 (proj2 SOBJ'))) as Vsz';
      try clear HMK;
      assert (NEB2 : VEP <> vb_buf vv')
        by (clear LEN SZ REL HTOT; intros E;
            eapply (blk_avoids_crange LayoutPU A A' mx m' _ _ _ (vb_buf vv') (vb_size vv') VEP 312 FRK C); try lia;
            intros x Hx [X1|X1]; unfold blk in X1; lia);
      match goal with STo : stk _ mx lo _ |- _ => clear STo end;
      revert LEN SZ REL;
      acall_xfer FRK;
      intros LEN SZ REL;
      rz_resume Y X
    end.

  Local Ltac tail_emit :=
    lazymatch goal with FRK : cframe _ _ (owned ?A') _ _ _ (blk (vb_buf ?vv') (vb_size ?vv')) ?mx ?m',
                        VOBJ' : vep_obj _ ?A' ?m' VEP v tag q, MUx : munch _ m ?mx |- _ =>
      eapply (ec_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A' mx m' _ vv');
      [ eassumption | eassumption | eassumption | assumption | eassumption | eassumption | eassumption
      | exact (proj1 (proj2 VOBJ')) | exact (proj1 VOBJ') | eassumption
      | assumption | assumption | assumption | assumption | assumption | assumption | assumption | assumption
      | exact MUx | exact FRK ]
    end.

  #[using="K SPHI LO CEIL ST SP16 TP EM LBUD NBUD NEB NES SOBJ DZ VOBJ HMK HT0 HTOT HL0 A2 A1 A0 MI AINV A lo mark l vv q tag v VEP AI Clg"] Lemma ec_main :
    realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               bvmap_empty (Z_to_bv 64 vep_emit_common_entry) (Z_to_bv 32 0) None m (seg_rom rsegs)) md) T.
  Proof.
    rewrite A0, A1, A2.
    pose proof (as_lazy_nil A m md AINV) as [MDL MDH].
    pose proof (as_layout_order (L:=LayoutPU)) as LAY. cbn [al_image_lo al_rw_lo al_image_hi LayoutPU] in LAY.
    pose proof alloc_ceiling_val as ACV.
    unfold EMITC_STACK, EMITLEN_STACK, REALLOC_STACK in *. unfold vep_emit_common_entry.
    pose proof VOBJ as (VLV & VEPC & TAG & PADS). cbn [al_segs LayoutPU] in VEPC.
    (first [ pose proof ((as_live_ok A m md VEP _ AINV VLV)) as dR_6; dand7 dR_6 as _ V16 Vlo Vhi Vimg Vmap Vown | pose proof (as_live_ok A m md VEP _ AINV VLV) as (_ & V16 & Vlo & Vhi & Vimg & Vmap & Vown) ]). clear Vimg.
    (first [ pose proof (PADS) as dR_7; dand7 dR_7 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]).
    unfold vep_cells in VEPC.
    (first [ pose proof ((vsb_obj_geom LayoutPU A m md (v Fvsb) vv false AINV SOBJ)) as dR_8; dand11 dR_8 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LayoutPU A m md (v Fvsb) vv false AINV SOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    pose proof SOBJ as SOBJ0. vsb_open SOBJ0. (first [ dex1 VBUF as bs0; dand3 VBUF as U8 LBS _ | dand4 VBUF as bs0 U8 LBS _ | destruct VBUF as (bs0 & U8 & LBS & _) ]). cbn [al_segs LayoutPU] in U8.
    unfold vsb_cells in VSBC.
    pose proof (as_live_disjoint A m md VEP 312 (v Fvsb) 40 AINV VLV VLS NES) as DVS.
    pose proof (as_live_disjoint A m md VEP 312 (vb_buf vv) (vb_size vv) AINV VLV VLB NEB) as DVB.
    pose proof (munch_refl [(bv_unsigned sp - 8432, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (CFP : client_fp LayoutPU A [(bv_unsigned sp - 8432, bv_unsigned sp)]).
    { cbn. split; [left; lia| exact I]. }
    assert (L7 : Z.land VEP 7 = 0) by (apply land7_of_mod8; [lia| apply mod8_of_mod16; exact V16]).
    apply rz_go; [exact MDH | exact MDL |].
    carve_frame 48%nat ST.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    zstep. if_cases KA; zify_cond KA. { exfalso. klia KA. } try clear KA.
    zstep. zstep. if_cases KZ; zify_cond KZ.
    { (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep.
      try replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
      release_frame FR ST (bv_unsigned sp).
      cps_done.
      lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
        pose proof (ainv_munch LayoutPU A m mx md _ AINV MU WM CFP) as AINV9 end.
      eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A _ md v vv);
        [ exact AINV9 | assumption | exact (md_frame_refl _ MDL MDH) | exact ST
        | split; [exact VLV|]; split; [exact VEPC|]; split; [exact TAG| exact PADS]
        | left; split; [klia KZ|]; split; reflexivity
        | vsb_close | lia | lia | left; reflexivity | intros p _ _; reflexivity | lia | reflexivity | ].
      eapply (cframe_noalloc LayoutPU); [exact MU | | eapply (stk_mapped (L:=LayoutPU)); [exact ST | exact CEIL | lia | lia]
        | intros a X; right; left; exact X ].
      intros a Ha NO. cbn [outside] in NO. lia. }
    (* [comment removed for export] *)
    assert (L1 : 1 <= l) by klia KZ. clear KZ.
    zstep. zstep. if_cases KB; zify_cond KB. { exfalso. destruct HMK as [-> | ->]; klia KB. } clear KB.
    zstep. zstep. rewrite L7.
    zstep. if_cases KM; zify_cond KM.
    - (* [comment removed for export] *)
      zstep. if_cases KT; zify_cond KT. { exfalso. klia KT. } clear KT.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      apply rz_stop. call_emit_len 65 66 72.
      intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A' m' md' vv' AINV' MI' MDF ST' VOBJ' SOBJ' LEN SZ REL LIVEq LBp NLp FRK.
      clear KM. try clear VSBC. try clear U8. after_emit_len.
      (* [comment removed for export] *)
      (first [ pose proof (VOBJ') as dR_10; dand3 dR_10 as _ VEPC' _ | pose proof VOBJ' as (_ & VEPC' & _) ]). cbn [al_segs LayoutPU] in VEPC'. unfold vep_cells in VEPC'. rewrite DZ in VEPC'.
      zstep. rewrite sx32_zero. zstep. if_cases KD; zify_cond KD; [| exfalso; klia KD]. clear KD VEPC'.
      zstep.
      tail_emit.
    - (* [comment removed for export] *)
      zstep. change (Z.b2z (0 <? 1)) with 1. zstep. zstep. zstep. zstep. zstep. zstep.
      apply rz_stop. call_emit_len 97 98 104.
      intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A' m' md' vv' AINV' MI' MDF ST' VOBJ' SOBJ' LEN SZ REL LIVEq LBp NLp FRK.
      clear KM. try clear VSBC. try clear U8. after_emit_len.
      zstep.
      tail_emit.
  Qed.
End S.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma vep_emit_common_ok {AI : AllocSpec LayoutPU} : vep_emit_common_stmt.
Proof. unfold vep_emit_common_stmt. intros. eapply ec_main; eassumption. Qed.

End CEIL.
End U_veyab.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_VS58t OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_crc32.U_cromo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_crc32 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_crc32.U_cr6ux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_vegk2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_ve2lq.U_veyab.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutPU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutPU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.

Module U_vermr.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World U_Img ImgU U_Cov8m.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutPU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutPU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma vep_error_ok : vep_error_stmt.
Proof.
  unfold vep_error_stmt.
  intros VEP v tag q H lo. intros until m.
  intros A0 VEPC TAG PADS EVC HENV HG IMG VLO V8 VHI ST LO CEIL SPH MI.
  rewrite A0. unfold vep_error_entry. unfold VEPERR_STACK in *.
  pose proof alloc_ceiling_val as ACV.
  (first [ dand3 HG as G16 GCE GHI | destruct HG as (G16 & GCE & GHI) ]). unfold HFRAME in GHI.
  assert (Evc : h_vc H = h_sp H + 1304) by reflexivity.
  assert (Ewrk : h_wrk H = h_sp H + 1120) by reflexivity.
  assert (Evsc : h_vsc H = h_sp H + 2240) by reflexivity.
  assert (Ecp : h_cp H = h_sp H + 1488) by reflexivity.
  destruct HENV as [GLOB HOBJ].
  (first [ pose proof (GLOB) as dR_2; dand4 dR_2 as EBSS BSS CP [cnt CNT] | pose proof GLOB as (EBSS & BSS & CP & [cnt CNT]) ]). rewrite EBSS in BSS. cbn [vi_bss VIU al_segs LayoutPU] in BSS.
  cbn [al_segs LayoutPU] in CP, CNT.
  (first [ pose proof (HOBJ) as dR_3; dand3 dR_3 as VC WK _ | pose proof HOBJ as (VC & WK & _) ]). (first [ dex2 VC as vcpad vcrest; dand3 VC as LP1 LR1 VC | dand5 VC as vcpad vcrest LP1 LR1 VC | destruct VC as (vcpad & vcrest & LP1 & LR1 & VC) ]). (first [ dex2 WK as wkpad wkrest; dand3 WK as LP2 LR2 WK | dand5 WK as wkpad wkrest LP2 LR2 WK | destruct WK as (wkpad & wkrest & LP2 & LR2 & WK) ]).
  cbn [al_segs LayoutPU] in VC, WK. unfold vc_cells in VC. unfold wrk_cells in WK.
  (first [ dand4 IMG as _ _ GVSC _ | destruct IMG as (_ & _ & GVSC & _) ]). unfold GOT_vsc in GVSC.
  pose proof (rw_cells_bound _ _ _ _ VEPC) as VEPB. rewrite (vep_cells_size v tag q TAG PADS) in VEPB.
  (first [ pose proof (PADS) as dR_7; dand7 dR_7 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]).
  unfold vep_cells in VEPC. rewrite EVC in VEPC.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (h_vsc H + 1304, h_vsc H + 1320)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.
  zstep. if_cases K1; zify_cond K1. { exfalso. clear - K1 Evsc GCE ACV. lia. } clear K1.
  zstep. zstep. if_cases K2; zify_cond K2. { exfalso. apply K2. apply land7_of_mod8; clear - Evsc G16 GCE ACV; lia. } clear K2.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.
  zstep. if_cases K3; zify_cond K3. { exfalso. apply K3. apply land7_of_mod8; clear - V8 VLO; lia. } clear K3.
  (* [comment removed for export] *)
  zstep. zstep. if_cases K4; zify_cond K4. { exfalso. clear - K4 Evc GCE ACV. lia. } clear K4.
  zstep. zstep. if_cases K5; zify_cond K5. { exfalso. apply K5. apply land7_of_mod8; clear - Evc G16 GCE ACV; lia. } clear K5.
  (* [comment removed for export] *)
  zstep. zstep. if_cases K6; zify_cond K6. { exfalso. clear - K6 Ewrk GCE ACV. lia. } clear K6.
  zstep. zstep. if_cases K7; zify_cond K7. { exfalso. apply K7. apply land7_of_mod8; clear - Ewrk G16 GCE ACV; lia. } clear K7.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep.
  carve_frame 48%nat ST.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  try replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
  release_frame FR ST (bv_unsigned sp).
  destruct (rw_cells_forget _ _ _ _ CNT) as [cnt' CNT']. cbn [cells_size csize Nat.add] in CNT'. clear CNT.
  apply evt_done. unfold vep_error_post.
  do 16 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [|exact ST].
  split.
  - eapply (glob_ok_intro LayoutPU); [exact EBSS| rewrite EBSS; cbn [vi_bss VIU al_segs LayoutPU]; exact BSS | exact CP | exact CNT'].
  - eapply (hobj_ok_munch LayoutPU); [exact HOBJ| exact MU| exact WM|].
    intros a Ha. unfold h_req, h_resp, h_hd in Ha. cbn [outside]. lia.
Qed.

End CEIL.
End U_vermr.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac call_consts_in H ::= unfold CRC_FRAME_U, C64_FRAME in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma swrap32_small : forall z, 0 <= z < 2^31 -> bv_swrap 32 (z + 0) = z.
Proof.
  intros z Hz. rewrite Z.add_0_r. apply bv_swrap_small.
  unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 `div` 2) with 2147483648. lia.
Qed.

Lemma sx32_small : forall z, 0 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia. rewrite bv_swrap_small; [reflexivity|].
  unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 `div` 2) with 2147483648. lia.
Qed.

Lemma vkeep_refl : forall (v : vep) ch, vkeep v v ch.
Proof. intros v ch f _. reflexivity. Qed.

(* [comment removed for export] *)
Lemma vkeep_fupd : forall (v v' : vep) ch f x, vkeep v v' ch -> In f ch -> vkeep v (fupd v' f x) ch.
Proof.
  intros v v' ch f x VK IN g NG. unfold fupd. destruct (vf_beq g f) eqn:E; [| apply VK, NG].
  apply vf_beq_eq in E. subst g. contradiction.
Qed.
(* [comment removed for export] *)
Ltac in_tac := cbn; repeat first [ left; reflexivity | right ]; reflexivity.
Ltac notin_tac := cbn; let X := fresh "X" in intros X; repeat (destruct X as [X|X]; [discriminate X|]); first [discriminate X | destruct X].
Ltac vkeep_tac VK := repeat (apply vkeep_fupd; [| in_tac]); exact VK.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.
  Variables (VEP : Z) (v : vep) (tag : list byte) (q : vep_pads) (vv : vsb_rec) (H : henv) (p mark n : Z) (seg : list byte) (lo : Z).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (m : mem) (md : Model) (A : AS) (T : TSet).
  Hypothesis AINV : ainv A m md.
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis A0 : a0 = Z_to_bv 64 VEP.
  Hypothesis A1 : a1 = Z_to_bv 64 p.
  Hypothesis A2 : a2 = Z_to_bv 64 mark.
  Hypothesis HMK : bool01 mark.
  Hypothesis VOBJ : vep_obj LayoutPU A m VEP v tag q.
  Hypothesis VBASE : vep_base H VEP v.
  Hypothesis HENV : henv_ok LayoutPU VIU H m.
  Hypothesis HG : henv_geom H.
  Hypothesis IMG : img_okU m.
  Hypothesis HLM : bool01 (v Flast_mark).
  Hypothesis CNT : vep_cnt v n.
  Hypothesis N0 : 0 <= n.
  Hypothesis NMX : n + (p - v Fver_p) < NMAX.
  Hypothesis SOBJ : vsb_obj LayoutPU A m (v Fvsb) vv false.
  Hypothesis NES : VEP <> v Fvsb.
  Hypothesis NEB : VEP <> vb_buf vv.
  Hypothesis EM : vb_size vv + 9 <= EXT_MAX.
  (* [comment removed for export] *)
  Hypothesis LBUD : a_livebytes A + vsb_extendsize (vb_size vv + 9) <= LIVE_MAX.
  Hypothesis NBUD : a_nlive A + 1 <= NLIVE_MAX.
  Hypothesis BSEG : bytes_at rsegs m (v Fver_p) seg.
  Hypothesis LSEG : Z.of_nat (length seg) = p - v Fver_p.
  Hypothesis VPLO : 4096 <= v Fver_p.
  Hypothesis PHI : p <= alloc_ceiling.
  Hypothesis SEGH : (v Fver_p = vi_empty VIU /\ seg = []) \/
                    (exists d k, a_live A d = Some k /\ 0 < k /\ d <= v Fver_p /\ p <= d + k /\ d <> VEP /\ d <> v Fvsb /\ d <> vb_buf vv).
  Hypothesis TP : tp = al_tp LayoutPU.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + MARK_STACK <= bv_unsigned sp.
  Hypothesis SPH : bv_unsigned sp <= h_sp H.
  Hypothesis K : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
              (v' : vep) (vv' : vsb_rec),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          stk rsegs m' lo (bv_unsigned sp) ->
          vep_obj LayoutPU A' m' VEP v' tag q -> vkeep v v' MARK_FIELDS ->
          v' Fver_p = p -> v' Flast_mark = mark -> v' Fo_pending = 0 -> vep_cnt v' (n + (p - v Fver_p)) ->
          0 <= v' Fcrc < 2^64 -> 0 <= v' Fcrcp < 2^64 ->
          vsb_obj LayoutPU A' m' (v Fvsb) vv' false ->
          vb_len vv <= vb_len vv' <= vb_len vv + 3 * (v' Fo_last - v Fo_last) ->
          vb_size vv <= vb_size vv' <= Z.max (vb_size vv) (vb_len vv' + 4096) ->
          (vb_buf vv' = vb_buf vv \/ (a_live A (vb_buf vv') = None /\ a_live A' (vb_buf vv) = None)) ->
          (forall r, r <> vb_buf vv -> r <> vb_buf vv' -> a_live A' r = a_live A r) ->
          a_livebytes A' = a_livebytes A + vb_size vv' - vb_size vv -> a_nlive A' = a_nlive A ->   (* [comment removed for export] *)
          henv_ok LayoutPU VIU H m' -> bytes_at rsegs m' (v Fver_p) seg ->
          cframe LayoutPU (owned A) (owned A') (bv_unsigned sp) MARK_STACK
                 (fun a => blk VEP 312 a \/ blk (vb_buf vv) (vb_size vv) a \/ (v Fvsb <= a < v Fvsb + 40))
                 (blk (vb_buf vv') (vb_size vv')) m m' ->
          realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T.

  Let Vmc : Z -> Prop := fun a => blk VEP 312 a \/ blk (vb_buf vv) (vb_size vv) a \/ (v Fvsb <= a < v Fvsb + 40).
  Let l : Z := p - v Fver_p.

  (* [comment removed for export] *)
  #[using="l HG sp ra seg p v"] Lemma henv_ok_ccall0 : forall (Ax A' : AS) (mx : mem) (mdx : Model) (m' : mem) (xsp win : Z) (Vc N : Z -> Prop),
    ainv Ax mx mdx -> cframe LayoutPU (owned Ax) (owned A') xsp win Vc N mx m' ->
    henv_ok LayoutPU VIU H mx -> xsp <= h_sp H -> alloc_ceiling <= xsp - win ->
    (forall a, Vc a -> (a + 1 <= al_image_lo LayoutPU \/ al_image_hi LayoutPU <= a) /\ a < alloc_ceiling) ->
    henv_ok LayoutPU VIU H m'.
  Proof.
    intros Ax A' mx mdx m' xsp win Vc N AI0 CF [GL HO] SPX CE HV.
    pose proof (as_layout_order (L:=LayoutPU)) as LAY. cbn [al_image_lo al_rw_lo al_image_hi LayoutPU] in LAY.
    pose proof (proj1 GL) as EB. cbn [vi_bss VIU] in EB.
    pose proof HG as (G1 & G2 & G3). pose proof alloc_ceiling_val as ACV. unfold HFRAME in G3.
    split.
    - eapply (glob_ok_ccall LayoutPU VIU H Ax A' mx mdx m'); [exact AI0| exact CF| exact HG| exact GL| exact SPX| exact CE
        | rewrite EB; cbn; lia| rewrite EB; cbn; lia
        | intros i Hi; rewrite EB; cbn; unfold pu_static; lia
        | rewrite EB; change (al_errno LayoutPU) with 0x42454; lia|].
      intros a Ha X. apply HV in X. unfold h_cp, h_vsc in Ha. rewrite EB in Ha. cbn [al_image_lo al_image_hi LayoutPU] in X. lia.
    - eapply (hobj_ok_ccall LayoutPU VIU H Ax A' mx mdx m'); [exact AI0| exact CF| exact HG| exact HO| exact SPX|].
      intros a Ha X. apply HV in X. unfold h_vc, h_wrk, h_req, h_resp, h_hd in Ha. cbn [al_image_lo al_image_hi LayoutPU] in X. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="l SPH LO CEIL SP16 HG ra lo seg p v AI"] Lemma henv_ok_munch0 : forall (mx m' : mem),
    henv_ok LayoutPU VIU H mx -> munch [(bv_unsigned sp - MARK_STACK, bv_unsigned sp); (VEP, VEP + 312)] mx m' ->
    wmono rsegs mx m' -> VEP + 312 <= alloc_ceiling -> off_image LayoutPU VEP 312 ->
    henv_ok LayoutPU VIU H m'.
  Proof.
    intros mx m' HE MU WM VHI VIM. unfold off_image in VIM.
    pose proof (as_layout_order (L:=LayoutPU)) as LAY. cbn [al_image_lo al_rw_lo al_image_hi LayoutPU] in LAY, VIM.
    pose proof (proj1 (proj1 HE)) as EB. cbn [vi_bss VIU] in EB.
    pose proof HG as (G1 & G2 & G3). pose proof alloc_ceiling_val as ACV. unfold HFRAME in G3.
    eapply (henv_ok_munch LayoutPU); [exact HE| exact MU| exact WM|].
    intros a Ha. unfold h_hd, h_wrk, h_req, h_vsc in Ha. rewrite EB in Ha. cbn [outside]. unfold MARK_STACK, EMITC_STACK, EMITLEN_STACK, REALLOC_STACK in *.
    split; [lia|]. split; [lia| exact I].
  Qed.

  (* [comment removed for export] *)
  #[using="l SEGH LSEG NEB NES SOBJ VOBJ AINV A md m sp ra p q tag AI Clg"] Lemma seg_ranges :
       (v Fver_p + Z.of_nat (length seg) <= VEP \/ VEP + 312 <= v Fver_p)
    /\ (v Fver_p + Z.of_nat (length seg) <= v Fvsb \/ v Fvsb + 40 <= v Fver_p)
    /\ (v Fver_p + Z.of_nat (length seg) <= vb_buf vv \/ vb_buf vv + vb_size vv <= v Fver_p).
  Proof.
    pose proof (as_layout_order (L:=LayoutPU)) as LAY. cbn [al_image_lo al_rw_lo al_image_hi LayoutPU] in LAY.
    destruct VOBJ as (VLV & _ & _ & _).
    (first [ pose proof ((as_live_ok A m md VEP _ AINV VLV)) as dR_1; dand7 dR_1 as _ _ _ _ Vimg _ _ | pose proof (as_live_ok A m md VEP _ AINV VLV) as (_ & _ & _ & _ & Vimg & _ & _) ]).
    (first [ pose proof ((vsb_obj_geom LayoutPU A m md (v Fvsb) vv false AINV SOBJ)) as dR_2; dand11 dR_2 as _ _ _ Simg _ _ _ Bimg _ _ _ | pose proof (vsb_obj_geom LayoutPU A m md (v Fvsb) vv false AINV SOBJ) as (_ & _ & _ & Simg & _ & _ & _ & Bimg & _ & _ & _) ]).
    unfold off_image in Vimg, Simg, Bimg. cbn [al_image_lo al_image_hi LayoutPU] in Vimg, Simg, Bimg.
    destruct SOBJ as (_ & _ & VLS & VLB & _ & _).
    destruct SEGH as [[EV ES] | (d & k & LD & K0 & D0 & D1 & N1 & N2 & N3)].
    - rewrite ES. rewrite EV. cbn [vi_empty VIU length Z.of_nat]. lia.
    - pose proof (as_live_disjoint A m md d k VEP 312 AINV LD VLV N1).
      pose proof (as_live_disjoint A m md d k (v Fvsb) 40 AINV LD VLS N2).
      pose proof (as_live_disjoint A m md d k (vb_buf vv) (vb_size vv) AINV LD VLB N3).
      lia.
  Qed.

  (* [comment removed for export] *)
  Local Ltac touch_all :=
    pose proof (conj AINV (conj MI (conj A0 (conj A1 (conj A2 (conj HMK (conj VOBJ (conj VBASE (conj HENV (conj HG (conj IMG
      (conj HLM (conj CNT (conj N0 (conj NMX (conj SOBJ (conj NES (conj NEB (conj EM (conj LBUD (conj NBUD (conj BSEG (conj LSEG (conj VPLO (conj PHI
      (conj SEGH (conj TP (conj SP16 (conj RA2 (conj ST (conj CEIL (conj LO (conj SPH K))))))))))))))))))))))))))))))))) as ALL_HYPS; clear ALL_HYPS.

  (* [comment removed for export] *)
  Local Ltac prelims :=
    pose proof (as_layout_order (L:=LayoutPU)) as LAY; cbn [al_image_lo al_rw_lo al_image_hi LayoutPU] in LAY;
    pose proof alloc_ceiling_val as ACV;
    pose proof HG as (G1 & G2 & G3); unfold HFRAME in G3;
    pose proof VBASE as (EVC & ECB & EPRIV & EDZ & EURL); cbn [vi_cb vi_url VIU] in ECB, EURL;
    pose proof CNT as (CN1 & CN2 & CN3 & CN4 & CN5 & CN6 & CN7);
    unfold MARK_STACK, EMITC_STACK, EMITLEN_STACK, REALLOC_STACK, NMAX in *.

  (* [comment removed for export] *)
  Local Ltac leaf_side :=
    lazymatch goal with
    | |- mem_inv _ _ => assumption
    | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
    | |- @eq (bv _) _ _ => first [reflexivity | rewrite ?unsigned_lit by lia; reflexivity]
    | |- rw_cells _ _ _ _ => eassumption
    | |- bytes_at _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
    | |- length _ = _ => assumption
    | |- vep_pads_wf _ => assumption
    | |- (_ mod 8 = 0)%Z => first [apply mod8_of_mod16; assumption | unfold h_vc; apply align_mod8_of16; [match goal with G : (h_sp H mod 16 = 0)%Z |- _ => exact G | G : kept (h_sp H mod 16 = 0)%Z |- _ => exact G end| reflexivity]]
    | |- _ => rewrite ?unsigned_lit by lia;
            repeat match goal with H : (_ <= _ \/ _ <= _)%Z |- _ => clear H end;
            first [ lia | rewrite Z.mod_small by lia; lia | cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; lia ]
    end.

  (* [comment removed for export] *)
  Local Ltac ovf64 KO :=
    lazymatch type of KO with context [Z.b2z ?c] => idtac end;
    repeat match goal with H : _ |- _ => lazymatch type of H with
      | vep_cnt _ _ => fail | (0 <= n)%Z => fail | (n + _ < _)%Z => fail | (_ = p - v Fver_p)%Z => fail
      | _ => lazymatch H with KO => fail | _ => clear H end end end;
    unfold vep_cnt in *; unsign KO;
    repeat match type of KO with context [?a <? ?b] => destruct (Z.ltb_spec a b); cbn in KO end; lia.
  (* [comment removed for export] *)
  #[using="l K SPH LO CEIL ST RA2 SP16 TP SEGH PHI VPLO LSEG BSEG EM LBUD NBUD NEB NES SOBJ NMX N0 CNT HLM IMG HG HENV VBASE VOBJ HMK A2 A1 A0 MI AINV a2 a1 a0"] Lemma mc_step4 :
    forall (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 : word) (j8 : list byte)
           (Ax : AS) (mx : mem) (mdx : Model) (vx : vep) (vvx : vsb_rec),
      m_halted mdx = None -> m_vm_lazy mdx = [] ->
      ainv Ax mx mdx -> mem_inv rsegs mx -> md_frame md mdx ->
      stk rsegs mx lo (bv_unsigned sp + -48) ->
      rw_cells rsegs mx (bv_unsigned sp + -48) [CB 8 j8; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells rsegs mx VEP (vep_cells vx tag q) -> a_live Ax VEP = Some 312 ->
      vkeep v vx MARK_FIELDS -> vx Fver_p = v Fver_p -> vx Fo_pending = 0 -> vep_cnt vx n ->
      vsb_obj LayoutPU Ax mx (v Fvsb) vvx false ->
      vb_len vv <= vb_len vvx <= vb_len vv + 3 * (vx Fo_last - v Fo_last) ->
      vb_size vv <= vb_size vvx <= Z.max (vb_size vv) (vb_len vvx + 4096) -> VEP <> vb_buf vvx ->
      (vb_buf vvx = vb_buf vv \/ (a_live A (vb_buf vvx) = None /\ a_live Ax (vb_buf vv) = None)) ->
      (forall r, r <> vb_buf vv -> r <> vb_buf vvx -> a_live Ax r = a_live A r) ->
      a_livebytes Ax = a_livebytes A + vb_size vvx - vb_size vv -> a_nlive Ax = a_nlive A ->   (* [comment removed for export] *)
      henv_ok LayoutPU VIU H mx -> bytes_at rsegs mx (v Fver_p) seg ->
      (v Fver_p + Z.of_nat (length seg) <= VEP \/ VEP + 312 <= v Fver_p) ->
      cframe LayoutPU (owned A) (owned Ax) (bv_unsigned sp) MARK_STACK Vmc (blk (vb_buf vvx) (vb_size vvx)) m mx ->
      evt rsegs (rz_at rsegs mdx T)
          (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp xt0 xt1 xt2 (Z_to_bv 64 mark) (Z_to_bv 64 VEP)
                   xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 p) xs3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
              bvmap_empty (Z_to_bv 64 0x1b244) (Z_to_bv 32 0) None mx (seg_rom rsegs)).
  Proof.
    touch_all.
    intros until vvx. intros MDHx MDLx AINVx MIx MDFx STx FR VEPC VLVx VK EVP EPEND CNTx SOBJx LENx SZx NEBx RELx LIVEx LBx NLx HENVx BSEGx SEGV CFx.
    prelims. hide HMK. hide HLM.
    (first [ pose proof (CNTx) as dR_3; dand7 dR_3 as D1 D2 D3 D4 D5 D6 D7 | pose proof CNTx as (D1 & D2 & D3 & D4 & D5 & D6 & D7) ]).
    (first [ pose proof ((as_live_ok Ax mx mdx VEP _ AINVx VLVx)) as dR_4; dand7 dR_4 as _ V16 Vlo Vhi Vimg Vmap Vown | pose proof (as_live_ok Ax mx mdx VEP _ AINVx VLVx) as (_ & V16 & Vlo & Vhi & Vimg & Vmap & Vown) ]).
    pose proof VOBJ as (_ & _ & TAG & PADS). (first [ pose proof (PADS) as dR_5; dand7 dR_5 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]).
    pose proof (bytes_at_bound _ _ _ _ BSEGx) as SEGBD.
    assert (EVCx : vx Fvc = h_vc H) by (rewrite (VK Fvc ltac:(notin_tac)); exact EVC).
    assert (ECBx : vx Fcb = 114388) by (rewrite (VK Fcb ltac:(notin_tac)); exact ECB).
    assert (EPRx : vx Fcb_priv = VEP + 56) by (rewrite (VK Fcb_priv ltac:(notin_tac)); exact EPRIV).
    assert (Ehvc : h_vc H = h_sp H + 1304) by reflexivity.
    unfold vep_cells in VEPC. rewrite EVP in VEPC.
    (first [ pose proof ((vsb_obj_geom LayoutPU Ax mx mdx (v Fvsb) vvx false AINVx SOBJx)) as dR_6; dand11 dR_6 as S16 Slo Shi Simg B16 Blo Bhi Bimg _ Smap Bmap | pose proof (vsb_obj_geom LayoutPU Ax mx mdx (v Fvsb) vvx false AINVx SOBJx) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & _ & Smap & Bmap) ]).
    pose proof (proj1 (proj2 SOBJx)) as VINVx. (first [ pose proof (VINVx) as dR_7; dand3 dR_7 as Vsz Vlen _ | pose proof VINVx as (Vsz & Vlen & _) ]).
    pose proof (proj1 (proj2 (proj2 (proj2 SOBJx)))) as VLBx.
    pose proof (as_live_disjoint Ax mx mdx VEP 312 (v Fvsb) 40 AINVx VLVx (proj1 (proj2 (proj2 SOBJx))) NES) as DVS.
    pose proof (as_live_disjoint Ax mx mdx VEP 312 (vb_buf vvx) (vb_size vvx) AINVx VLVx VLBx NEBx) as DVB.
    (* [comment removed for export] *)
    pose proof BSEGx as BSEG0. hide BSEG0. hide DVS. hide DVB. hide SEGV. hide_slow.
    pose proof (munch_refl [(bv_unsigned sp - 8480, bv_unsigned sp); (VEP, VEP + 312)] mx) as MU.
    pose proof (wmono_refl rsegs mx) as WM.
    assert (CFP : client_fp LayoutPU Ax [(bv_unsigned sp - 8480, bv_unsigned sp); (VEP, VEP + 312)]).
    { cbn. split; [left; lia|]. split; [right; left; exists VEP, 312; split; [exact VLVx|lia]| exact I]. }
    (* [comment removed for export] *)
    zstep. zstep. if_cases KT; zify_cond KT. { exfalso. klia KT. } clear KT.
    zstep. zstep. if_cases KT; zify_cond KT. { exfalso. unsign KT. klia KT. } clear KT.
    (* [comment removed for export] *)
    zstep. zstep. rewrite (swrap32_small (p - v Fver_p)) by lia. zstep.
    call_fr (crc32_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bvmap_empty (Z_to_bv 32 0) _ lo seg) by (idtac; leaf_side).
    try clear BSEGx.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    zstep. if_cases KO; zify_cond KO. { exfalso. ovf64 KO. } clear KO.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    zstep. if_cases KO; zify_cond KO. { exfalso. ovf64 KO. } clear KO.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    try replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    lazymatch goal with S : stk _ _ lo _ |- _ => release_frame FR S (bv_unsigned sp) end.
    rewrite EVCx, ECBx, EPRx. zstep.
    (* [comment removed for export] *)
    lazymatch type of VEPC with context [C8 (Z_to_bv 64 (vx Fo_total)) :: C4 ?cw :: _] =>
    set (v4 := fupd (fupd (fupd (fupd (fupd (fupd vx Fo_wait (vx Fo_wait + (p - v Fver_p))) Fcrc (bv_unsigned cw))
                 Fo_crc (vx Fo_crc + (p - v Fver_p))) Fver_p p) Flast_mark mark) Fcrcp ((vx Fcrcp) mod 2^64)) end.
    (first [ pose proof ((proj1 (proj2 HENVx))) as dR_8; dex2 dR_8 as vcpad vcrest; dand3 dR_8 as LP1 LR1 VCX | pose proof ((proj1 (proj2 HENVx))) as dR_8; dand5 dR_8 as vcpad vcrest LP1 LR1 VCX | pose proof (proj1 (proj2 HENVx)) as (vcpad & vcrest & LP1 & LR1 & VCX) ]). cbn [al_segs LayoutPU] in VCX.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => lazymatch type of MU with munch ?W _ _ =>
      assert (VEPC4 : rw_cells rsegs mq VEP (vep_cells v4 tag q))
        by (unfold vep_cells, v4; cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; rewrite Z_to_bv_mod64, Z_to_bv_bv_unsigned; exact VEPC);
      apply (rw_cells_transport rsegs W mx mq _ _) in VCX; [| exact MU | exact WM | cbn [disjoint_from cells_size csize vc_cells Nat.add length]; lia ]
    end end.
    clear VEPC.
    call_fr (vep_default_cb_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bvmap_empty (Z_to_bv 32 0) _
               (h_vc H) VEP v4 tag q (p - v Fver_p) vcpad (h_resp H) (h_wrk H) vcrest) by (idtac; unfold v4; leaf_side).
    cps_done.
    (* [comment removed for export] *)
    unhide_slow. unhide BSEG0. unhide SEGV.
    lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ => lazymatch type of MU with munch ?W _ _ =>
      pose proof (ainv_munch LayoutPU Ax mx mf mdx _ AINVx MU WM CFP) as AINV9;
      apply (bytes_at_transport rsegs W mx mf _ seg) in BSEG0; [| exact MU | clear - SEGV LSEG PHI CEIL LO ACV SEGBD; cbn [disjoint_from]; lia ];
      hide SEGV; unhide DVS;
      assert (D40 : disjoint_from W (v Fvsb) 40) by (clear - DVS Shi CEIL LO ACV; cbn [disjoint_from]; lia);
      hide DVS; unhide DVB;
      assert (SOBJ9 : vsb_obj LayoutPU Ax mf (v Fvsb) vvx false)
        by (eapply (vsb_obj_munch LayoutPU); [exact SOBJx | exact MU | exact WM | exact D40 | clear - DVB Bhi CEIL LO ACV; cbn [disjoint_from]; lia]);
      hide DVB
    end end.
    lazymatch goal with PCB : rw_cells _ _ VEP (vep_cells ?v5 tag q) |- _ =>
    eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ax _ mdx v5 vvx);
      [ exact AINV9 | assumption | exact MDFx | assumption
      | split; [exact VLVx|]; split; [exact PCB|]; split; [exact TAG| exact PADS]
      | unfold v4; vkeep_tac VK
      | reflexivity | reflexivity
      | unfold v4, fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; exact EPEND
      | unfold vep_cnt, v4, fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; lia
      | unfold v4, fupd; cbn [vf_beq vf_index N.eqb Pos.eqb];
        match goal with |- 0 <= bv_unsigned ?w < _ => pose proof (bv_unsigned_in_range _ w) as UR; unfold bv_modulus in UR; cbn in UR; lia end
      | unfold v4, fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; apply Z.mod_pos_bound; lia
      | exact SOBJ9
      | unfold v4, fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; exact LENx
      | exact SZx
      | exact RELx | exact LIVEx | exact LBx | exact NLx
      | eapply henv_ok_munch0; [exact HENVx | exact MU | exact WM | exact Vhi | exact Vimg]
      | exact BSEG0 | ] end.
    lazymatch goal with |- cframe _ _ _ _ _ _ _ _ ?mf =>
      assert (MP : mapped mf (bv_unsigned sp - 8480) 8480) by (eapply (stk_mapped (L:=LayoutPU)); [eassumption | exact CEIL | lia | lia]);
      assert (CF2 : cframe LayoutPU (owned Ax) (owned Ax) (bv_unsigned sp) 8480 Vmc nowhere mx mf)
        by (eapply (cframe_noalloc LayoutPU); [exact MU | | exact MP | intros a X; destruct X];
            intros a Ha NO; cbn [outside] in NO; clear - Ha NO Vlo; unfold Vmc, blk; lia);
      eapply (cframe_seq LayoutPU _ _ _ _ _ _ _ _ _ _ _ _ _ m mx mf CFx CF2);
      [ lia | lia | exact MP | intros a X; exact X | intros a X; right; exact X | intros a X; left; exact X ] end.
  Qed.

End S.
