(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep InitMem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import MM_syscalls.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import SysStepF ITreeA Shadow.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import STree AsanCtrl AsanCtrlProps AsanEmbed.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AsanW Require Import AImg RtCells AProto ABase AKit AKit2 ABytes AModelFacts FsKit F_memset F_apoison F_m2s
     F_annot APoisonR_iface F_apoison_remap.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition annot_grow_postF (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (A cap lo : Z) (m : amem) (st : astate) (RNG : footprint) (r : astate) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => r = st /\ fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - ANNOT_STACK, bv_unsigned sp); (shad A, shad A + shlen (rup8 cap))] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (shad A) [CB (Z.to_nat (cap / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (cap / 8)))]
    /\ (cap mod 8 <> 0 -> rw_cells asegs m' (shad A + cap / 8) [C1 (Z_to_bv 8 (cap mod 8))]).

(* [comment removed for export] *)
Lemma aannotate_grow_tree : forall st p ch cap,
  (a_live st) !! p = Some ch -> 0 < cap <= 2^40 ->
  aannotate st p cap 0 cap =
    match ch with
    | CPrim _ _ => aret st
    | CSec _ _ _ => if 0 <? rdn cap 8 then poison0 (chunk_user_beg ch + 0) (rdn cap 8 - 0) (aret st) else aret st
    end.
Proof.
  intros st p ch cap L HC. unfold aannotate. rewrite L.
  replace ((0 <=? 0) && (0 <=? cap) && (0 <=? cap) && (cap <=? cap))%bool with true
    by (symmetry; rewrite !Bool.andb_true_iff, !Z.leb_le; lia).
  cbn [negb]. replace (2 ^ 40 <? cap) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (0 =? cap) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (rdn cap 8 <? Z.min 0 cap) with false by (symmetry; apply Z.ltb_ge; unfold rdn; Z.div_mod_to_equations; lia).
  rewrite Bool.andb_false_r. replace (0 <? cap) with true by (symmetry; apply Z.ltb_lt; lia).
  change (rdn 0 8) with 0. destruct ch; reflexivity.
Qed.

Lemma is_primary_small : forall n, is_primary n = true -> n <= 65536.
Proof.
  intros n H. unfold is_primary, needed0, rounded_size, rz_size, K_MAX_SIZE, rup in H. apply Z.leb_le in H.
  assert (0 <= Z.shiftl 16 (rz_log n)) by (apply Z.shiftl_nonneg; lia).
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
End CANSEC1.
Local Ltac grow_detour Kal M8E M8 M7 CAP AL SBC RSH SHF SHL R8 beg cap sb :=
  zstep; rewrite land_align8, M8E by lia;
  zstep; zstep;
  let Ki := fresh "Ki" in if_cases Ki; zify_cond Ki; [exfalso; clear - Ki CAP; lia|];
  zstep;
  zstep; let Kj := fresh "Kj" in if_cases Kj; zify_cond Kj; [exfalso; clear - Kj Kal M8; lia|];
  do 5 zstep;
  let HR := fresh "HR" in let ACC := fresh "ACC" in let SBR := fresh "SBR" in let Kk := fresh "Kk" in
  let SB1 := fresh "SB1" in let SB2 := fresh "SB2" in
  lazymatch goal with |- evtF _ ?RNG _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (end_byte_read mm beg cap sb AL ltac:(lia) SBC) as HR;
    assert (ACC : rng RNG (2147450880 + Z.shiftr (beg + cap) 3) 1)
      by (eapply rng_sub'; [exact RSH|]; rewrite SHF, SHL, R8, Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - AL CAP M7 M8 Kal; Z.div_mod_to_equations; lia)
  end;
  zstep; clear HR ACC; rewrite sxb_sval;
  pose proof (sval_range sb) as SBR;
  lazymatch goal with EOK : end_byte_ok cap sb |- _ => destruct EOK as [SB1 SB2] end;
  zstep; if_cases Kk; zify_cond Kk; [ exfalso; clear - Kk SB1 SBR; rewrite ?unsigned_sval in Kk; apply SB1; Z.div_mod_to_equations; lia |];
  zstep; unfold bv_lts; rewrite !signed_lit_small64 by lia;
  replace (cap mod 8 <? sval sb) with false by (symmetry; apply Z.ltb_ge; lia); cbn [negb];
  clear Ki Kj Kk SB1 SB2 SBR.

Section CANSEC2. Context {rc : runConstT}.
(* [comment removed for export] *)
Lemma ablk_rup8 : forall A cap, ablk A (A + cap) -> A mod 8 = 0 -> 0 <= cap -> ablk A (A + rup8 cap).
Proof. intros A cap H A8 C. pose proof ATOP_al16. unfold ablk, KLS, rup8, rdn8, AIMG_HI in *. Z.div_mod_to_equations. lia. Qed.
Theorem annot_grow_full : forall (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (lo : Z)
    (st : astate) (p : AsanCtrl.aptr) (ch : achunk) (A cap : Z) (junk : list byte) (sb : byte),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - ANNOT_STACK ->
  poison_cells m -> annot_cells m -> artcells m ->
  premap_cells m -> (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 (A + cap) -> a2 = Z_to_bv 64 A -> a3 = Z_to_bv 64 (A + cap) ->
  ablock_range A cap -> 0 < cap <= AREQMAX ->
  (a_live st) !! p = Some ch -> chunk_size ch = cap -> (is_primary cap = false -> A = chunk_user_beg ch) ->
  match ch with CPrim _ _ => is_primary cap = true | CSec _ _ _ => is_primary cap = false end ->
  rw_cells asegs m (shad A) [CB (Z.to_nat (cap / 8)) junk] ->
  (cap mod 8 <> 0 -> rw_cells asegs m (shad A + cap / 8) [C1 sb] /\ end_byte_ok cap sb) ->
  (exists RLO RHI, RLO mod 4096 = 0 /\ RHI mod 4096 = 0 /\ RLO + 64 <= A /\ A + cap + 64 <= RHI
       /\ rng RNG (shad RLO) (shlen (RHI - RLO)) /\ wr_at asegs m (shad RLO) (shlen (RHI - RLO))) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad A) (shlen (rup8 cap)) ->
  implS asegs RNG (aembed ATOP (aannotate st p cap 0 cap))
        (epostF (annot_grow_postF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc A cap lo m st RNG))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            FR (Z_to_bv 64 AANNOT) fc None m (seg_rom asegs)).
Proof.
  intros until sb. intros MI ST CEIL LO PC AC ART PRC RR Ea0 Ea1 Ea2 Ea3 BR CAP LIVE CSZ UBEG KIND BODY SB ARENA RIMG RSTK RSH.
  pose proof BR as (BR1 & BR2 & BR3 & BR4). unfold AREQMAX in CAP. pose proof (ablk_lin _ _ BR1) as (BL1 & BL2 & BL3 & BL4). unfold AIMG_HI in BL1.   (* [comment removed for export] *)
  assert (A8 : A mod 8 = 0) by (clear -BR4; Z.div_mod_to_equations; lia). pose proof (ablk_rup8 _ _ BR1 A8 ltac:(lia)) as BRU.   (* [comment removed for export] *)
  rewrite (aannotate_grow_tree st p ch cap LIVE ltac:(lia)).
  destruct (Z_lt_le_dec (cap / 8) 65536) as [SMALL|BIG].
  - (* [comment removed for export] *)
    assert (T : match ch with
                | CPrim _ _ => aret st
                | CSec _ _ _ => if 0 <? rdn cap 8 then poison0 (chunk_user_beg ch + 0) (rdn cap 8 - 0) (aret st) else aret st
                end = aret st).
    { destruct ch as [|mb ms n]; [reflexivity|]. cbn [chunk_user_beg]. cbn in KIND. specialize (UBEG KIND). cbn in UBEG. rewrite <- UBEG.
      rewrite poison0_small by (first [clear -A8; Z.div_mod_to_equations; lia | unfold rdn; clear -SMALL CAP; Z.div_mod_to_equations; lia]).
      destruct (0 <? rdn cap 8); reflexivity. }
    rewrite T. apply implS_ret.
    eapply evtF_mono.
    + subst a0 a1 a2 a3. eapply (annot_grow_spec RNG) with (lo := lo) (junk := junk) (sb := sb); try eassumption; try reflexivity; try lia.
      all: first [ unfold ANNOT_STACK; clear -LO; lia | unfold rup8, rdn8; clear -BR3 CAP; Z.div_mod_to_equations; lia ].
    + intros ms' PO. unfold annot_grow_postF. split; [reflexivity|]. split; [intros b j H; exact H|].
      unfold annot_grow_post in PO. destruct_exs PO. destruct PO as (-> & MU & REST). do 16 eexists. split; [reflexivity|]. split; [| exact REST].
      eapply munch_weaken; [| exact MU]. unfold ANNOT_STACK, sub_fp; cbn [outside]; clear; intros x Hx; lia.
  - (* [comment removed for export] *)
    destruct ch as [q n|mb ms n].
    { exfalso. cbn in KIND. pose proof (is_primary_small _ KIND). clear -H BIG CAP. Z.div_mod_to_equations. lia. }
    cbn in KIND. specialize (UBEG KIND). cbn in UBEG. cbn [chunk_user_beg]. rewrite <- UBEG.
    replace (0 <? rdn cap 8) with true by (symmetry; apply Z.ltb_lt; unfold rdn; clear -BIG CAP; Z.div_mod_to_equations; lia).
    replace (A + 0) with A by lia. replace (rdn cap 8 - 0) with (rdn8 cap) by (unfold rdn, rdn8; clear -CAP; Z.div_mod_to_equations; lia).
    clear T0 || idtac.
    subst a0 a1 a2 a3. unfold AANNOT, ANNOT_STACK in *.
    pose proof PC as PC'. destruct PC' as (GOT & GOTMS & REAL & SHB & LAY & CANP & THR). destruct AC as (DCO & GVB & VERB).
    pose proof PRC as PRC'. destruct PRC' as (GPG & PGSZ & MLIM & F216 & F240 & CAN & LPG).
    pose proof (munch_refl [(bv_unsigned sp - 2720, bv_unsigned sp); (shad A, shad A + shlen (rup8 cap))] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (R8 : rup8 cap = cap + 7 - (cap + 7) mod 8 /\ 0 <= (cap + 7) mod 8 < 8 /\ 0 <= cap mod 8 < 8) by (unfold rup8, rdn8; repeat split; try lia; apply Z.mod_pos_bound; lia).
    destruct R8 as (R8 & M7 & M8).
    assert (HE : A + rup8 cap <= 2^47) by (clear -BR3 CAP R8 M7; lia).
    assert (BIG8 : 8 * 65536 <= cap) by (clear -BIG CAP; Z.div_mod_to_equations; lia).
    assert (SHF : shad A = 2147450880 + A / 8 /\ shlen (rup8 cap) = rup8 cap / 8 /\ 8 * (cap / 8) = cap - cap mod 8 /\ shlen (rdn8 cap) = cap / 8).
    { unfold shad, shlen, rdn8, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. repeat split; try reflexivity; clear - CAP; Z.div_mod_to_equations; lia. }
    destruct SHF as (SHF & SHL & DIV8 & SHL2).
    assert (M8E : (A + cap) mod 8 = cap mod 8) by (clear - A8 CAP; Z.div_mod_to_equations; lia).
    assert (SAB : 0x800d0c00 <= shad A /\ shad A + shlen (rup8 cap) <= 0x10007fff8000 /\ 65536 <= cap / 8 <= 2^26 /\ cap / 8 <= shlen (rup8 cap) <= cap / 8 + 1).   (* [comment removed for export] *)
    { rewrite SHF, SHL, R8. clear -BL1 BL3 HE BR3 CAP BIG M7 M8. Z.div_mod_to_equations. lia. }
    pose proof poison_remap as PR. unfold poison_remap_stmt in PR.
    iprefix.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 2720, bv_unsigned sp)]%Z m) as MUF.
    (* [comment removed for export] *)
    carve_frame 56%nat ST;
         (destruct (stk_split asegs _ lo (bv_unsigned sp + -2128) (bv_unsigned sp + -56) ST ltac:(lia)) as [ST' STP]; clear ST; rename ST' into ST).
    do 9 zstep.                 (* [comment removed for export] *)
    zstep.                      (* [comment removed for export] *)
    zstep.                      (* [comment removed for export] *)
    zstep; zstep.               (* [comment removed for export] *)
    zstep; rewrite zxb_lit by lia.   (* [comment removed for export] *)
    zstep; let K := fresh "Ka" in if_cases K; zify_cond K; [exfalso; clear - K; lia|].   (* [comment removed for export] *)
    do 3 zstep.                 (* [comment removed for export] *)
    zstep; zstep; zstep; lits.  (* [comment removed for export] *)
    zstep; zstep; let K := fresh "Kb" in if_cases K; zify_cond K; [exfalso; clear - K; lia|].   (* [comment removed for export] *)
    zstep; let K := fresh "Kc" in if_cases K; zify_cond K; [| exfalso; clear - K CAP; lia].   (* [comment removed for export] *)
    zstep; let K := fresh "Kd" in if_cases K; zify_cond K; [exfalso; clear - K CAP; lia|].   (* [comment removed for export] *)
    zstep; let K := fresh "Ke" in if_cases K; zify_cond K; [exfalso; clear - K CAP; lia|].   (* [comment removed for export] *)
    zstep; let K := fresh "Kf" in if_cases K; zify_cond K; [exfalso; clear - K CAP; lia|].   (* [comment removed for export] *)
    do 4 zstep.                 (* [comment removed for export] *)
    zstep; let K := fresh "Kg" in if_cases K; zify_cond K; [exfalso; clear - K CAP; lia|].   (* [comment removed for export] *)
    zstep; let K := fresh "Kh" in if_cases K; zify_cond K; [exfalso; clear - K CAP; lia|].   (* [comment removed for export] *)
    zstep.                      (* [comment removed for export] *)
    replace (Z.land (A + cap) 7) with (cap mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; clear - A8 CAP; Z.div_mod_to_equations; lia).
    zstep; if_cases Kal; zify_cond Kal.   (* [comment removed for export] *)
    all: swap 1 2.                       (* [comment removed for export] *)
    1: assert (ALI : cap mod 8 = 0) by (clear - Kal M8; lia).
    2: assert (NAL : cap mod 8 <> 0) by (clear - Kal M8; lia).
    2: destruct (SB NAL) as [SBC0 EOK];
       pose proof (rw_cells_transport asegs _ _ _ _ _ SBC0 MUF WM ltac:(cbn [disjoint_from cells_size csize]; lia)) as SBC; clear SBC0.
    all: clear SB MUF Kal.
    2: grow_detour NAL M8E M8 M7 CAP A8 SBC RSH SHF SHL R8 A cap sb.
    (* [comment removed for export] *)
    all: do 3 zstep.                 (* [comment removed for export] *)
    all: zstep.                      (* [comment removed for export] *)
    all: replace (Z.land A 7) with 0 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; clear - A8; lia).
    all: zstep; if_lit.              (* [comment removed for export] *)
    all: zstep; zstep.               (* [comment removed for export] *)
    all: zstep; let K := fresh "Kt" in if_cases K; zify_cond K; [| exfalso; clear - K CAP; lia].   (* [comment removed for export] *)
    all: zstep; rewrite land_align8 by lia.     (* [comment removed for export] *)
    all: replace (A - A mod 8) with A by (clear - A8; lia).
    all: zstep; let K := fresh "Kt" in if_cases K; zify_cond K; [exfalso; clear - K CAP; lia|].   (* [comment removed for export] *)
    all: zstep.                      (* [comment removed for export] *)
    all: zstep; rewrite land_align8, M8E by lia.        (* [comment removed for export] *)
    all: zstep; zstep; rewrite land_align8 by lia.      (* [comment removed for export] *)
    all: replace (A + cap + 7 - (A + cap + 7) mod 8) with (A + rup8 cap) by (unfold rup8, rdn8; clear - A8 CAP; Z.div_mod_to_equations; lia).
    all: zstep; let K := fresh "Kge" in if_cases K; zify_cond K; first [ exfalso; clear - K BIG8 CAP M8; Z.div_mod_to_equations; lia | idtac ].   (* [comment removed for export] *)
    all: zstep; zstep; zstep.                            (* [comment removed for export] *)
    all: replace (A + cap - cap mod 8 - A) with (rdn8 cap) by (unfold rdn8; lia).
    all: zstep.                                          (* [comment removed for export] *)
    (* [comment removed for export] *)
    all: apply evtF_done; name_sp sp (-2128); eapply PR with (lo := lo);
         first [ (lazymatch goal with |- stk _ _ _ _ => idtac end; rewrite Hsp; eassumption)
               | (lazymatch goal with |- ATOP <= _ => idtac end; atop_facts; exact CEIL)
               | (lazymatch goal with |- _ <= bv_unsigned _ - PZR_STACK => idtac end; unfold PZR_STACK; rewrite Hsp; clear -LO; lia)
               | (lazymatch goal with |- mem_inv _ _ => idtac end; eassumption)
               | (lazymatch goal with |- poison_cells _ => idtac end; unfold poison_cells; repeat (split; [eassumption|]); eassumption)
               | (lazymatch goal with |- premap_cells _ => idtac end; unfold premap_cells; repeat (split; [first [eassumption | apply premap_canary_any]|]); eassumption)
               | (lazymatch goal with |- forall i, _ -> _ = None => idtac end;
                  eapply arelro0_munch; [exact RR | exact MU | repeat (apply Forall_cons; [cbn; unfold ARELRO_LO, ARELRO_HI; clear -CEIL LO SAB; lia|]); apply Forall_nil])
               | (lazymatch goal with |- @eq word _ _ => idtac end; reflexivity)
               | (lazymatch goal with |- ?x mod 8 = 0 => is_var x; idtac end; exact A8)
               | (lazymatch goal with |- rdn8 _ mod 8 = 0 => idtac end; unfold rdn8; clear -M8 CAP; Z.div_mod_to_equations; lia)
               | (lazymatch goal with |- 0 < rdn8 _ => idtac end; unfold rdn8; clear -M8 BIG8; lia)
               | (lazymatch goal with |- ablk _ _ => idtac end; eapply ablk_sub; [exact BR1| clear; lia| unfold rdn8; clear -M8 CAP; Z.div_mod_to_equations; lia])   (* [comment removed for export] *)
               | (lazymatch goal with |- _ + rdn8 _ <= _ => idtac end; unfold rdn8; clear -M8 BR3 CAP; lia)
               | (lazymatch goal with |- 65536 <= shlen _ => idtac end; rewrite SHL2; exact BIG)
               | (lazymatch goal with |- rw_cells _ _ _ _ => idtac end; rewrite SHL2; eassumption)
               | (lazymatch goal with |- rng _ 65536 _ => idtac end; exact RIMG)
               | (lazymatch goal with |- rng _ _ (bv_unsigned _ - _) => idtac end; rewrite Hsp; eapply rng_sub'; [exact RSTK| clear -LO LO0; lia])
               | (lazymatch goal with |- rng _ (shad _) _ => idtac end; eapply rng_sub'; [exact RSH| rewrite SHL2; clear -SAB; lia])
               | idtac ].
    all: intros RNG' m9 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' PP;
         destruct PP as (FPLE & MU2 & WM2 & MI2 & ST2 & ZSH & RSH2 & PC2 & PRC2);   (* [comment removed for export] *) unname_sp; unfold PZR_STACK in MU2; rewrite SHL2 in MU2.
    all: apply (rng_fp_le _ _ _ _ FPLE) in RSH; apply (rng_fp_le _ _ _ _ FPLE) in RSTK; apply (rng_fp_le _ _ _ _ FPLE) in RIMG.
    all: lazymatch type of MU2 with munch _ ?ma ?mb => transport_after_call asegs ma mb MU2 WM2 end; clear MU2 WM2.
    all: rewrite SHL2 in ZSH; unfold zeros in ZSH.
    all: apply implS_ret;
         replace (ret_pc (Z_to_bv 64 539608)) with (Z_to_bv 64 539608 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    (* [comment removed for export] *)
    all: zstep; let K := fresh "Keq" in if_cases K; zify_cond K;
         first [ exfalso; clear - K ALI R8 M7 M8 CAP; Z.div_mod_to_equations; lia
               | exfalso; clear - K NAL R8 M7 M8 CAP; Z.div_mod_to_equations; lia | clear K ].   (* [comment removed for export] *)
    2: zstep; replace (A + rup8 cap - (A + cap - cap mod 8)) with 8 by (clear - NAL R8 M7 M8 CAP; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
    2: zstep; zstep; if_lit.                          (* [comment removed for export] *)
    2: zstep; replace (Z.land (A + cap) 7) with (cap mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; clear - A8 CAP; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
    2: zstep; zstep.                                  (* [comment removed for export] *)
    2: call m2s_spec; first [ eassumption | (rewrite ?unsigned_lit by (clear - BL1 BL2 HE R8 M7 M8 CAP NAL; Z.div_mod_to_equations; lia); pose proof BR1 as BRB; unfold ablk, AIMG_HI, KLS in BRB; pose proof atop_range as ATR; unfold KLOW, KHIGH, KEND; clear - BRB ATR HE R8 M7 M8 CAP NAL; Z.div_mod_to_equations; lia) | idtac ].   (* [comment removed for export] *)
    2: rewrite ?unsigned_lit by (clear - BL1 BL2 HE R8 M7 M8 CAP NAL; Z.div_mod_to_equations; lia).
    2: replace (shad (A + cap - cap mod 8)) with (shad A + cap / 8) by (unfold shad, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - A8 CAP M8; Z.div_mod_to_equations; lia).
    2: assert (RUPD : shlen (rup8 cap) = cap / 8 + 1) by (rewrite SHL, R8; clear -NAL M7 M8 CAP; Z.div_mod_to_equations; lia).
    2: assert (RB1 : rng RNG' (shad A + cap / 8) 1) by (eapply rng_sub'; [exact RSH|]; clear -RUPD SAB; lia).
    2: set (SBA := shad A + cap / 8) in *; zstep; rewrite le1_sym; mem_after_store; subst SBA; clear RB1.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    all: do 10 zstep.
    all: match goal with P : stk asegs ?mm ?a _, H : stk asegs ?mm _ ?a |- _ => (pose proof (stk_merge asegs _ _ _ _ H P ltac:(lia)) as ST9'; clear H P); release_frame FR0 ST9' (bv_unsigned sp) end.
    all: apply evtF_done; unfold annot_grow_postF; split; [reflexivity|]; split; [exact FPLE|];
         do 16 eexists; split; [reflexivity|].
    all: repeat match goal with |- _ /\ _ => split end; try assumption.
    all: try (intros NE; exfalso; apply NE; exact ALI).
    all: try (intros _; assumption).
  Unshelve. all: try (apply ref_ro_addr_false; right; lia).
Qed.
End CANSEC2.
