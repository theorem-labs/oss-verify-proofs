(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import HttpRepA AWKit AWAuto FakeKit HObjK H_memptr_cmp AWUb.
Import ListNotations.
Open Scope Z_scope.

Definition map_str_to_int_entryA : Z := 0x8e7f8.

Section W.
Context {HC : HasCeiling}.
Hypothesis IC : icpt_contracts.
Variable FI : fs_if.
Hypothesis STACK_MALLOC_0 : stack_malloc_stmt FI 0.

Local Notation FSIV W := ((FSB FI, FSB FI + A0_FS_SIZE) :: (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE) :: W)%Z.

Definition table_strings_A (m : mem) (ws : list word) (ne : Z) : Prop :=
  forall i, 0 <= i < ne -> exists S str slack,
    nth_error ws (Z.to_nat (2 * i)) = Some (wz S)
    /\ (forall m', mem_inv asegs m' -> bytes_at asegs m' S (str ++ Z_to_bv 8 0 :: slack)) /\ ~ In (Z_to_bv 8 0) str
    /\ (- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack)
    /\ 0x10000 <= S /\ S + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= 0x609000
    /\ shw m S (Z.of_nat (length str) + 1).

Definition map_str_to_int_post_A (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32)
    (st : fsstate FI) (lo ne : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (r : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (st' : fsstate FI),
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F_ (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch ((lo, q) :: FSIV []) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ fkeep FI [] st m m' /\ fs_live FI st' = fs_live FI st /\ RFAKE FI st' m'
    /\ stk asegs m' lo q /\ asan_env asegs m'
    /\ (r = -1 \/ 0 <= r < ne).

Definition map_str_to_int_stmt_A : Prop :=
  forall (T n TAB ne cs lo : Z) (tok : list byte) (ws : list word) (st : fsstate FI)
         (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F_ : bvmap 5 word) (fc : bv 32) (m : mem),
  bytes_at asegs m T tok -> Z.of_nat (length tok) >= n -> 1 <= n <= 2^43 ->
  0x609000 <= T -> T + Z.of_nat (length tok) <= alloc_ceiling -> shw m T n ->
  (T + Z.of_nat (length tok) <= FSB FI \/ FSB FI + A0_FS_SIZE <= T) ->
  (T + Z.of_nat (length tok) <= 0x7fff7000 \/ 0x10007fff8000 <= T) ->
  u64arr asegs m TAB ws -> Z.of_nat (length ws) = 2 * ne -> 1 <= ne <= 33 ->
  0x10000 <= TAB -> TAB + 16 * ne <= 0x609000 -> TAB mod 8 = 0 -> shw m TAB (16 * ne) ->
  table_strings_A m ws ne ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 128 - 16 - 32 - A0_RT_STACK -> q mod 16 = 0 -> q < 2^64 ->
  mem_inv asegs m -> asan_env asegs m -> RFAKE FI st m -> fs_call_ok FI st tp 1 -> FSENV FI m -> 0 <= cs < 2^64 ->
  a0 = wz T -> a1 = wz n -> a2 = wz TAB -> a3 = wz ne -> a4 = wz cs ->
  evt asegs (map_str_to_int_post_A ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc st lo ne m)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz map_str_to_int_entryA) fc None m (seg_rom asegs)).

Section WALK.
  Variables (T n TAB ne lo : Z) (tok : list byte) (ws : list word) (st : fsstate FI).
  Variables (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32) (m0 : mem).
  Hypothesis TL : Z.of_nat (length tok) >= n.
  Hypothesis N1 : 1 <= n <= 2^43.
  Hypothesis TLO : 0x609000 <= T.
  Hypothesis THI : T + Z.of_nat (length tok) <= alloc_ceiling.
  Hypothesis SHWT : shw m0 T n.
  Hypothesis TFS : T + Z.of_nat (length tok) <= FSB FI \/ FSB FI + A0_FS_SIZE <= T.
  Hypothesis TBAND : T + Z.of_nat (length tok) <= 0x7fff7000 \/ 0x10007fff8000 <= T.
  Hypothesis LEN : Z.of_nat (length ws) = 2 * ne.
  Hypothesis NE : 1 <= ne <= 33.
  Hypothesis TABLO : 0x10000 <= TAB.
  Hypothesis TABHI : TAB + 16 * ne <= 0x609000.
  Hypothesis TABAL : TAB mod 8 = 0.
  Hypothesis SHWTAB : shw m0 TAB (16 * ne).
  Hypothesis TS : table_strings_A m0 ws ne.
  Hypothesis CLO : alloc_ceiling <= lo.
  Hypothesis LO : lo <= q - 128 - 16 - 32 - 4096.
  Hypothesis AL16 : q mod 16 = 0.
  Hypothesis QHI : q < 2^64.
  Hypothesis RF0 : RFAKE FI st m0.
  Hypothesis FCO : fs_call_ok FI st tp 1.
  Hypothesis FE0 : FSENV FI m0.

  Let F := fs_F FI st 0.  Let FL := fs_FL FI st 0.  Let st1 := fs_next FI st 0.  Let SF := sh F.
  Notation POST := (map_str_to_int_post_A ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc st lo ne m0).
  Notation W0 := ((lo, q) :: FSIV [])%Z.

  Definition minvM (q' : Z) (m : mem) : Prop :=
    (q' = q + -128 \/ q' = q + -128 - 16)
    /\ stk asegs m lo q'
    /\ (exists jq, rw_cells asegs m q' [CB 16 jq; C8 (wz F)])
    /\ stk asegs m (q' + 24) (q + -104)
    /\ rw_cells asegs m (q + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m F [C8 (wz 0x41b58ab3); C8 (wz 0x1808d); C8 (wz 0x8e7f8); C8 (wz q')]
    /\ rw_cells asegs m (F + 32) (memptr_cells T n)
    /\ (exists j8, rw_cells asegs m (F + 48) [CB 8 j8; C8 (wz FL)])
    /\ rw_cells asegs m SF [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241)]
    /\ rw_cells asegs m (SF + 4) (shadow_zero_cells 2)
    /\ rw_cells asegs m (SF + 6) [C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)]
    /\ rw_cells asegs m FL [C1 (Z_to_bv 8 1)]
    /\ bytes_at asegs m T tok /\ u64arr asegs m TAB ws /\ mem_inv asegs m
    /\ munch W0 m0 m /\ wmono asegs m0 m
    /\ fkeep FI [] st m0 m /\ RFAKE FI st1 m /\ asan_env asegs m
    /\ fs_live FI st1 = fs_newff FI st 0 :: fs_live FI st.

  #[using="STACK_MALLOC_0 TL N1 THI TFS TBAND LEN NE TABLO TABHI CLO LO AL16 QHI RF0 FCO FE0"] Lemma prologueM : forall (cs : Z) t0 t1 t2 a5 a6 a7 t3 t4 t5 t6,
    bytes_at asegs m0 T tok -> u64arr asegs m0 TAB ws ->
    stk asegs m0 lo q -> mem_inv asegs m0 -> asan_env asegs m0 -> 0 <= cs < 2^64 ->
    forall (Q : machine_state -> Prop),
    (forall q' m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31, minvM q' m ->
       evt asegs Q (MS (mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') x10 x11 x12 x13 x14 x15 x16 x17
                            (wz F) (wz TAB) (wz (-1)) (wz n) (wz cs) (wz T) (wz SF) (wz 0x7fff8000) (wz F) (wz (ne + -1)) x28 x29 x30 x31)
                        F_ (wz 0x8e91c) fc None m (seg_rom asegs))) ->
    evt asegs Q
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz T) (wz n) (wz TAB) (wz ne) (wz cs) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz map_str_to_int_entryA) fc None m0 (seg_rom asegs)).
  Proof.
    intros cs t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 TOK ARR ST MI AG CS Q K. unfold map_str_to_int_entryA.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof AG as AE. apply asan_env_globals in AG. ag_split AG.
    pose proof (fsb_ok FI) as (FSB1 & FSB2 & FSB3 & FSB4). unfold app_mem in FSB3.
    assert (ESHB : sh (FSB FI) = FSB FI / 8 + 2147450880) by reflexivity.
    assert (ESF : SF = F / 8 + 2147450880) by reflexivity.
    destruct (new_frame_facts FI st 0 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & FLO & FHI & FAL & FLLO & FLHI & APART).
    cbn [FB_of SB_of] in FHI, APART.
    pose proof (new_frame_fk FI st 0 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
    pose proof (munch_refl W0 m0) as MU. pose proof (wmono_refl asegs m0) as WM.
    pose proof (munch_refl [(lo, q)]%Z m0) as MU0. pose proof (wmono_refl asegs m0) as WM0.
    pose proof (fkeep_refl FI [] st m0) as FK. assert (LSUB : forall g, In g (fs_live FI st) -> In g (fs_live FI st)) by (intros g Hg; exact Hg).
    pose proof RF0 as RF.
    carve_frame 128%nat ST.
    step. do 14 (step; fix_lit_store).
    step.
    step.
    rewrite (unsigned_lit (q + -128)) by lia. rewrite land_align32 by lia.
    remember (q + -128 - (q + -128) mod 32)%Z as q' eqn:Eq0.
    assert (Hq : q' = q + -128 \/ q' = q + -128 - 16) by (subst q'; apply align32_cases; clear - AL16; Z.div_mod_to_equations; lia).
    clear Eq0.
    lazymatch goal with FRx : rw_cells asegs ?mm (q + -128) (?c0 :: ?c1 :: ?rest) |- _ =>
      destruct (align_frame_gen mm lo (q + -128) q' [c0; c1] rest 24%nat ST ltac:(lia) FRx eq_refl ltac:(lia) Hq) as (STq & (jq & QC) & GAP & FRhi);
      clear FRx end.
    clear ST. rename STq into ST. change (Z.of_nat 24) with 24 in GAP, FRhi. replace (q + -128 + 24) with (q + -104) in GAP, FRhi by lia.
    do 5 step.
    step. step. step. step.
    step. step.
    step.
    step.   lit_branch.
    step.
    step.
    env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
    call (STACK_MALLOC_0 st lo q' 64 F SF FL 64 24%nat 8%nat).
    all: side (try (first [ assumption | reflexivity | (unfold A0_RT_STACK in *; lia) ])).

    match goal with A : asan_env asegs _ |- _ => try clear AE; rename A into AE end.
    match goal with R : RFAKE FI (fs_next FI st 0) _ |- _ => rename R into RF end.
    match goal with E : fs_live FI _ = _ :: _ |- _ => rename E into LIVE1 end. fold st1 in LIVE1, RF.
    match goal with K0 : fkeep FI [] st _ _ |- _ => rename K0 into FKc end.
    match goal with P : rw_cells asegs _ F _ |- _ => rename P into FRF end.
    match goal with P : rw_cells asegs _ SF _ |- _ => rename P into SHF; shadow_cells_lit SHF end.
    match goal with P : rw_cells asegs _ FL _ |- _ => rename P into FLG end.
    fs_after_call FI FK FKc LSUB LIVE1 [(lo, q); (F, F + 64); (SF, SF + 8)]%Z.
    pose proof (lb_new _ _ _ LIVE1) as LVF. pose proof (ls_new _ _ _ LIVE1) as LVS. pose proof (lf_new _ _ _ LIVE1) as LVL.
    unfold ff_size, ff_shsize in LVF, LVS. rewrite FCLS in LVF, LVS. cbn [FB_of SB_of] in LVF, LVS.
    change (ff_addr (fs_newff FI st 0)) with F in LVF, LVS. change (ff_flag (fs_newff FI st 0)) with FL in LVL. change (sh F) with SF in LVS.
    step. step.
    step.   if_cases K0; zify_cond K0. 2:{ exfalso. lia. } clear K0.
    step; fix_lit_store.

    do 7 step.
    step; fix_lit_store. step; fix_lit_store. step; fix_lit_store.
    step. step.
    replace (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 F)) 3 + 2147450880)) with (Z_to_bv 64 SF)
      by (f_equal; rewrite unsigned_lit by lia; rewrite shiftr3_div; lia).
    do 4 sstep.
    step.
    do 4 sstep.
    zstep. rewrite swrap32_id by lia.
    step; fix_lit_store. step; fix_lit_store.
    step. ubr_by ltac:(rewrite ?signed_lit in KU by lia; lia).
    step.

    env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
    split_chunk FRF 4%nat FH R1. split_chunk R1 2%nat MPC FT.
    split_chunk SHF 4%nat SH1 R2. split_chunk R2 2%nat SH2 SH3.
    replace (F + 32 + 16) with (F + 48) in FT by lia. replace (SF + 4 + 2) with (SF + 6) in SH3 by lia.
    apply K. unfold minvM, memptr_cells, shadow_zero_cells, shadow_cells. cbn [map repeat].
    split; [exact Hq|].
    repeat (split; [first [eassumption | (eexists; eassumption)] |]). assumption.
  Qed.

End WALK.
End W.
