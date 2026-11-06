(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.P0 Require H_scanner_get_token H_presp_B.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpRepA AWKit AWAuto AWAuto2 FakeKit HObjK HObjF FsEnvKit H_scanner_get_token H_vfm_A H_vfm_G H_vfm_X H_vfm_GX H_match_shell H_match_A H_match_X H_UpnpPrintf.
Import ListNotations.
Open Scope Z_scope.

Definition parse_entity_entryA : Z := 0x89a20.
Notation PE_LOOP := 0x89c00%Z.
Notation PE_DISP := 0x89c08%Z.
Notation PE_EXIT := 0x8a1f4%Z.
Notation PENT_DEPTH_A := 49152%Z.
Notation PE_JT_A := 0x213c0%Z.

Section W.
Context {HC : HasCeiling}.
Variable FI : fs_if.
Hypothesis IC : icpt_contracts.
Hypothesis STACK_MALLOC_0 : stack_malloc_stmt FI 0.
Hypothesis STACK_MALLOC_1 : stack_malloc_stmt FI 1.
Hypothesis STACK_MALLOC_2 : stack_malloc_stmt FI 2.
Local Notation FSIV W := ((FSB FI, FSB FI + A0_FS_SIZE) :: (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE) :: W)%Z.

Definition pe_okA (q lo P : Z) (st : fsstate FI) : Prop :=
  alloc_ceiling <= lo /\ lo <= q - PENT_DEPTH_A /\ q mod 16 = 0 /\ q + 64 <= 2^47
  /\ 0x609000 <= P /\ P + 504 <= alloc_ceiling /\ P mod 8 = 0 /\ lb (fs_live FI st) P 504.
Ltac pokA V := destruct V as (CLO & LO & AL16 & QHI & PLO & PHI & PAL & PLB).

Section DEFS.
  Variables (q lo P : Z) (st : fsstate FI).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32).

  Definition eF := fs_F FI st 1.  Definition eFL := fs_FL FI st 1.  Definition est1 := fs_next FI st 1.  Definition eSF := sh eF.
  Notation F := eF. Notation FL := eFL. Notation st1 := est1. Notation SF := eSF.
  Definition eSH (X : Z) : Z := Z.shiftr X 3 + 2147450880.

  Definition eshadow : list cell :=
    [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
     C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
     C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].

  Definition eshadowU : list cell :=
    [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
     C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].

  Definition pscr (q' : Z) (m : mem) : Prop :=
    exists j0 j160,
      rw_cells asegs m q' [CB 24 j0; C8 (wz (Z.land (P + 452) 7 + 3)); C8 (wz (P + 440)); C8 (wz (P + 472)); C8 (wz (eSH (P + 472)));
                           C8 (wz F); C8 (wz F); C8 (wz (P + 264)); C8 (wz 4294967295); C8 (wz FMT_CHUNK_A); C8 (wz (F + 32)); C8 (wz P);
                           C8 (wz (F + 64)); C8 (wz (P + 400)); C8 (wz (P + 392)); C8 (wz (P + 480)); C8 (wz (P + 408)); C8 (wz 2147450880);
                           CB 16 j160; C8 (wz F)].

  Definition prestS (shd : list cell) (q' : Z) (m : mem) : Prop :=
    (q' = q + -288 \/ q' = q + -288 - 16)
    /\ stk asegs m (q' + 184) (q + -104)
    /\ rw_cells asegs m (q + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ (exists w0, rw_cells asegs m F [C8 w0; C8 (wz 0x159f5); C8 (wz 0x89a20); C8 (wz q')])
    /\ (exists j, rw_cells asegs m (F + 32) [CB 88 j])
    /\ rw_cells asegs m (F + 120) [C8 (wz FL)]
    /\ rw_cells asegs m SF shd
    /\ rw_cells asegs m FL [C1 (Z_to_bv 8 1)]
    /\ (exists stc, RFAKE FI stc m /\ fs_live FI stc = fs_newff FI st 1 :: fs_live FI st).

  Definition pinvS (shd : list cell) (q' : Z) (m : mem) : Prop :=
    stk asegs m lo q' /\ pscr q' m /\ mem_inv asegs m /\ asan_env asegs m
    /\ (q + -304 <= q' <= q + -288 /\ q' mod 16 = 0)
    /\ prestS shd q' m.

  Definition pregs (q' : Z) (x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 x30 x31 : word) : bvmap 5 word :=
    mkR x1 (wz q') gp tp x5 x6 (wz 2147450880) (wz q) (wz q') x10 x11 x12 x13 x14 x15 x16 x17
        (wz (eSH (P + 452))) (wz PE_JT_A) (wz (P + 392)) (wz (P + 464)) (wz (P + 488)) (wz (eSH (P + 464))) (wz (eSH (P + 488)))
        (wz (P + 452)) x26 (wz SF) x28 x29 x30 x31.
  Definition dispstA (q' : Z) x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 x30 x31 (m : mem) : machine_state :=
    MS (pregs q' x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 x30 x31) F_ (wz PE_DISP) fc None m (seg_rom asegs).
  Definition loopstA (q' r : Z) x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 (m : mem) : machine_state :=
    MS (pregs q' x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 (wz r) x28 x29 x30 x31) F_ (wz PE_LOOP) fc None m (seg_rom asegs).
End DEFS.

Section PE.
  Variables (q lo P : Z) (st : fsstate FI).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32) (m0 : mem).
  Hypothesis POK : pe_okA q lo P st.
  Hypothesis RF0 : RFAKE FI st m0.
  Hypothesis FCO : fs_call_ok FI st tp 4.
  Hypothesis FE0 : FSENV FI m0.

  Notation F := (eF st). Notation FL := (eFL st). Notation st1 := (est1 st). Notation SF := (eSF st).
  Notation prestS := (prestS q st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Notation pscr := (pscr P st).
  Notation pinvS := (pinvS q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Notation pinv := (pinvS eshadow).
  Notation dispstA := (dispstA q P st gp tp F_ fc). Notation loopstA := (loopstA q P st gp tp F_ fc).

  Ltac hide_mem_except2 k1 k2 :=
    repeat match goal with
    | H : rw_cells _ _ _ _ |- _ => tryif (first [constr_eq H k1 | constr_eq H k2]) then fail else hide H
    | H : stk _ _ _ _ |- _ => hide H
    | H : munch _ _ _ |- _ => hide H
    | H : wmono _ _ _ |- _ => hide H
    end.

  #[using="STACK_MALLOC_1 POK RF0 FCO FE0"] Lemma prologueE : forall t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (Q : machine_state -> Prop),
    stk asegs m0 lo q -> mem_inv asegs m0 -> asan_env asegs m0 ->
    (forall q' m x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 x30 x31, pinv q' m ->
       munch ((lo, q) :: FSIV []) m0 m -> wmono asegs m0 m -> fkeep FI [] st m0 m ->
       evt asegs Q (dispstA q' x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 x30 x31 m)) ->
    evt asegs Q
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz parse_entity_entryA) fc None m0 (seg_rom asegs)).
  Proof.
    intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Q ST MI AG K.
    pose proof POK as POK'. pokA POK'. unfold parse_entity_entryA.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof AG as AE. apply asan_env_globals in AG. ag_split AG.
    pose proof (fsb_ok FI) as (FSB1 & FSB2 & _ & FSB4 & FSB5).
    assert (ESHB : sh (FSB FI) = FSB FI / 8 + 2147450880) by reflexivity.
    assert (ESF : SF = F / 8 + 2147450880) by reflexivity.
    destruct (new_frame_facts FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & FLO & FHI & FAL & FLLO & FLHI & APART).
    cbn [FB_of SB_of] in FHI. clear APART PLB.
    assert (SFB : 8 * (SF - 2147450880) = F) by (rewrite ESF; clear - FAL; Z.div_mod_to_equations; lia).
    assert (SHB8 : 8 * (sh (FSB FI) - 2147450880) = FSB FI) by (rewrite ESHB; clear - FSB4; Z.div_mod_to_equations; lia).
    hide FAL. hide FSB4. hide ESF. hide ESHB. hide PAL.
    pose proof (new_frame_fk FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
    pose proof (munch_refl ((lo, q) :: FSIV [])%Z m0) as MUF.
    pose proof (munch_refl [(lo, q)]%Z m0) as MU0. pose proof (wmono_refl asegs m0) as WM0. pose proof (wmono_refl asegs m0) as WM.
    pose proof (fkeep_refl FI [] st m0) as FK. assert (LSUB : forall g, In g (fs_live FI st) -> In g (fs_live FI st)) by (intros g Hg; exact Hg).
    pose proof RF0 as RF.
    carve_frame 288%nat ST.
    step. do 14 (step; fix_lit_store).
    step.
    step.
    rewrite (unsigned_lit (q + -288)) by lia. rewrite land_align32 by lia.
    remember (q + -288 - (q + -288) mod 32)%Z as q' eqn:Eq0.
    assert (Hq : q' = q + -288 \/ q' = q + -288 - 16) by (subst q'; apply align32_cases; clear - AL16; Z.div_mod_to_equations; lia).
    assert (QAL : q' mod 16 = 0) by (subst q'; clear - AL16; Z.div_mod_to_equations; lia).
    hide AL16. hide QAL. clear Eq0.
    lazymatch goal with FRx : rw_cells asegs ?mm (q + -288) (?c0 :: ?c1 :: ?rest) |- _ =>
      destruct (align_frame_gen mm lo (q + -288) q' [c0; c1] rest 184%nat ST ltac:(lia) FRx eq_refl ltac:(lia) Hq) as (STq & (jq & QC) & GAP & FRhi);
      clear FRx end.
    clear ST. rename STq into ST. assert (QB : q + -304 <= q' <= q + -288) by lia. hide Hq. change (Z.of_nat 184) with 184 in GAP, FRhi. replace (q + -288 + 184) with (q + -104) in GAP, FRhi by lia.
    step.
    step. step. step. step.
    step. step.
    step.
    sstep.
    step.   lit_branch.
    step.
    step.
    env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
    pose proof (fs_call_ok_le FI _ _ _ 1%nat FCO ltac:(lia)) as FCO1.
    call (STACK_MALLOC_1 st lo q' 96 F SF FL 128 88%nat 16%nat).
    all: side (try (first [ assumption | reflexivity | (unfold A0_RT_STACK in *; lia) ])).
    match goal with A : asan_env asegs _ |- _ => try clear AE; rename A into AE end.
    match goal with R : RFAKE FI (fs_next FI st 1) _ |- _ => rename R into RF end.
    match goal with E : fs_live FI _ = _ :: _ |- _ => rename E into LIVE1 end. fold st1 in LIVE1, RF.
    match goal with K0 : fkeep FI [] st _ _ |- _ => rename K0 into FKc end.
    match goal with P0 : rw_cells asegs _ F _ |- _ => rename P0 into FRF end.
    match goal with P0 : rw_cells asegs _ SF _ |- _ => rename P0 into SHF; shadow_cells_lit SHF end.
    match goal with P0 : rw_cells asegs _ FL _ |- _ => rename P0 into FLG end.
    fs_after_call FI FK FKc LSUB LIVE1 [(lo, q); (F, F + 128); (SF, SF + 16)]%Z.
    pose proof (lb_new _ _ _ LIVE1) as LVF. pose proof (ls_new _ _ _ LIVE1) as LVS. pose proof (lf_new _ _ _ LIVE1) as LVL.
    unfold ff_size, ff_shsize in LVF, LVS. rewrite FCLS in LVF, LVS. cbn [FB_of SB_of] in LVF, LVS.
    change (ff_addr (fs_newff FI st 1)) with F in LVF, LVS. change (ff_flag (fs_newff FI st 1)) with FL in LVL. change (sh F) with SF in LVS.
    zstep. zstep.
    step.   if_cases K0; zify_cond K0. 2:{ exfalso. lia. } clear K0.
    assert (SFLO : SF + 16 <= lo /\ 2147450880 <= SF) by (clear - SFB FLO FHI FSB1 FSB2 CLO ACR; lia).

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(q', q' + 184); (F, F + 128)]%Z mm) as MUs; pose proof (wmono_refl asegs mm) as WMs end.
    hide_mem_except2 QC FRF. unhide MUs. unhide WMs.
    sstep. zstep. sstep. zstep. sstep. zstep. sstep.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    sstep. zstep. sstep. zstep. zstep. zstep. sstep. zstep. zstep. sstep. zstep. sstep. zstep. sstep.
    zstep. zstep. zstep. zstep. sstep. zstep. sstep. zstep. zstep. sstep. zstep. sstep. sstep. zstep. zstep.
    unhide_transport MUs WMs. clear MUs WMs.

    replace (Z_to_bv 64 (Z.shiftr F 3 + 2147450880)) with (Z_to_bv 64 SF) by (f_equal; rewrite shiftr3_div; unhide ESF; rewrite ESF; reflexivity).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(q', q' + 184); (SF, SF + 16)]%Z mm) as MUs; pose proof (wmono_refl asegs mm) as WMs end.
    hide_mem_except2 QC SHF. unhide MUs. unhide WMs.
    sstep. sstep. sstep. sstep. zstep. zstep. sstep.
    sstep. sstep. sstep. sstep. zstep. sstep. sstep. sstep. sstep.
    sstep. zstep. zstep. zstep. sstep. zstep. zstep. zstep. sstep. sstep.
    unhide_transport MUs WMs. clear MUs WMs.
    step.

    env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
    match goal with P0 : stk asegs _ lo q' |- _ => rename P0 into ST end.
    split_chunk FRF 4%nat FH FT. split_chunk FT 1%nat FT1 FT2. replace (F + 32 + 88) with (F + 120) in FT2 by lia.
    unhide Hq. unhide QAL.
    eapply (K q' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [| exact MUF| exact WM| exact FK].
    split; [exact ST|]. split; [do 2 eexists; exact QC|]. split; [exact MI0|]. split; [exact AE|].
    split; [split; [exact QB| exact QAL]|].
    split; [exact Hq|]. split; [exact GAP|]. split; [exact FRhi|]. split; [eexists; exact FH|]. split; [eexists; exact FT1|]. split; [exact FT2|].
    split; [exact SHF|]. split; [exact FLG|]. exists st1. split; [exact RF| exact LIVE1].
  Qed.

  Definition epostA (X : mem -> Z -> Prop) : machine_state -> Prop :=
    fun ms' => exists (r : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (st' : fsstate FI),
      ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ mem_inv asegs m' /\ fs_live FI st' = fs_live FI st /\ RFAKE FI st' m'
      /\ stk asegs m' lo q /\ asan_env asegs m' /\ X m' r.
  Definition pWE : list ivl := [(lo, q); (F, F + 128); (SF, SF + 16); (FL, FL + 1)]%Z.
  Definition rframeE (R : mem -> Prop) : Prop := forall m m', R m -> munch pWE m m' -> wmono asegs m m' -> R m'.

  #[using="m0 POK RF0"] Lemma exitF : forall (q' r : Z) (R : mem -> Prop)
      x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 m,
    pinv q' m -> R m -> rframeE R ->
    evt asegs (epostA (fun m' r' => R m' /\ r' = r))
      (MS (mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') x10 (wz F) x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 (wz r) (wz SF) x28 x29 x30 x31)
          F_ (wz 0x8a20c) fc None m (seg_rom asegs)).
  Proof.
    intros q' r R x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 m INV HR RFR.
    destruct INV as (ST & (j0 & j160 & QC) & MI & AE & (QB & QAL) & VR).
    destruct VR as (Hq & GAP & FRhi & (w0 & FH) & (jf & FT1) & FT2 & SHF & FLG & (stc & RF & LIVE1)).
    pose proof POK as POK'. pokA POK'.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR. unfold eshadow, eSH in *.
    pose proof (fsb_ok FI) as (FSB1 & FSB2 & _ & FSB4 & FSB5).
    destruct (new_frame_facts FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & FLO & FHI & FAL & FLLO & FLHI & APART).
    cbn [FB_of SB_of] in FHI. clear APART PLB.
    assert (SFB : 8 * (SF - 2147450880) = F) by (unfold eSF, sh, SHADOW_OFF; clear - FAL; Z.div_mod_to_equations; lia).
    assert (SHB8 : 8 * (sh (FSB FI) - 2147450880) = FSB FI) by (unfold sh, SHADOW_OFF; clear - FSB4; Z.div_mod_to_equations; lia).
    hide FAL. hide FSB4. hide Hq. hide PAL. hide QAL. hide AL16.
    pose proof (new_frame_fk FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
    assert (LSUB : forall g, In g (fs_live FI st) -> In g (fs_live FI stc)) by (intros g Hg; rewrite LIVE1; right; exact Hg).
    pose proof (lb_new _ _ _ LIVE1) as LVF. pose proof (ls_new _ _ _ LIVE1) as LVS. pose proof (lf_new _ _ _ LIVE1) as LVL.
    unfold ff_size, ff_shsize in LVF, LVS. rewrite FCLS in LVF, LVS. cbn [FB_of SB_of] in LVF, LVS.
    change (ff_addr (fs_newff FI st 1)) with F in LVF, LVS. change (ff_flag (fs_newff FI st 1)) with FL in LVL. change (sh F) with SF in LVS.
    pose proof (fkeep_refl FI [] st m) as FK.
    pose proof (munch_refl pWE m) as MUE. pose proof (wmono_refl asegs m) as WME. unfold pWE in MUE.
    pose proof (munch_refl [(lo, q); (F, F + 128); (SF, SF + 16)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(SF, SF + 16)]%Z mm) as MUs; pose proof (wmono_refl asegs mm) as WMs end.
    hide_mem_except SHF. unhide MUs. unhide WMs.
    do 16 sstep.
    unhide_transport MUs WMs. clear MUs WMs.
    zstep.

    env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(FL, FL + 1)]%Z mm) as MU0; pose proof (wmono_refl asegs mm) as WM0 end.
    sstep.
    env_sync AE MU0 WM0. fk_sync FI RF MU0 FK LSUB.
    join_chunks FT1 FT2 FRt. join_chunks FH FRt FRF.
    lazymatch type of RF with RFAKE _ ?st2 ?mb =>
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (SHF' : rw_cells asegs mc (sh (ff_addr (fs_newff FI st 1))) (shadow_cells (repeat 245 (Z.to_nat (ff_shsize (fs_newff FI st 1))))))
        by (change (ff_addr (fs_newff FI st 1)) with F; change (sh F) with SF; unfold ff_shsize; rewrite FCLS; exact SHF);
      destruct (release FI st2 (fs_newff FI st 1) (fs_live FI st) mb mc _ RF LIVE1 MU0 WM0 FLG SHF' FRF
                  ltac:(unfold ff_size; rewrite FCLS; reflexivity)) as [RF3 LIVE3]
    end end.
    clear RF MU0 WM0 SHF'.
    zstep.   zstep.
    do 13 step.
    step.   step.
    release_frame QC ST (q' + 184)%Z.
    pose proof (stk_merge asegs _ _ _ _ ST GAP ltac:(lia)) as STm. clear ST GAP.
    release_frame FRhi STm q.
    apply evt_done. unfold epostA. exists r. do 14 eexists. lazymatch goal with |- exists _ _, MS _ _ _ _ _ ?mm _ = _ /\ _ => exists mm, (fs_after_release FI stc) end.
    split; [reflexivity|]. split; [exact MI|]. split; [exact LIVE3|]. split; [exact RF3|]. split; [exact STm|]. split; [exact AE|].
    split; [exact (RFR m _ HR MUE WME)| reflexivity].
  Qed.

  Definition pjt_A : list byte := map (Z_to_bv 8) [48; 136; 6; 0; 0; 141; 6; 0; 120; 136; 6; 0; 100; 139; 6; 0; 88; 137; 6; 0; 44; 140; 6; 0]%Z.
  #[using="Type"] Lemma pjt_bytes_A : forall m, mem_inv asegs m -> bytes_at asegs m PE_JT_A pjt_A.
  Proof.
    intros m MI. pose proof (ro_cells_image asegs m PE_JT_A pjt_A MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO.
    destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
  Qed.

  Definition pjt_tgt (k : Z) : Z :=
    if k =? 1 then 0x89bf0 else if k =? 2 then 0x8a0c0 else if k =? 3 then 0x89c38 else if k =? 4 then 0x89f24 else if k =? 5 then 0x89d18 else 0x89fec.
  #[using="Type"] Lemma pjt_read_A : forall m k, mem_inv asegs m -> 1 <= k <= 6 ->
    ov_read_bytes asegs m (wa (PE_JT_A + 4 * (k - 1))) 4 = Some (le4 (Z_to_bv 64 (pjt_tgt k - PE_JT_A))).
  Proof.
    intros m k MI Hk. pose proof (pjt_bytes_A m MI) as B.
    assert (CASES : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6) by lia.
    destruct CASES as [-> |[-> |[-> |[-> |[-> | ->]]]]];
      (rewrite (bytes_at_read asegs m PE_JT_A pjt_A _ 4 B) by (cbn; lia)); f_equal; apply P0.H_scanner_get_token.bytes_eqb_eq; vm_compute; reflexivity.
  Qed.

  Definition blkstA (q' pc : Z) x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 (m : mem) : machine_state :=
    MS (pregs q P st gp tp q' x1 x5 x6 (wz pc) (wz 5) x12 x13 x14 x15 x16 x17 (wz 3) x28 x29 x30 x31) F_ (wz pc) fc None m (seg_rom asegs).

  #[using="lo POK"] Lemma dispE : forall (q' entp : Z) x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    pscr q' m -> mem_inv asegs m -> rw_cells asegs m (P + 452) [C4 (wz entp)] -> acc m (P + 452 + 4 - 1) -> 1 <= entp <= 6 ->
    (forall y1 y5 y6 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       evt asegs Q (blkstA q' (pjt_tgt entp) y1 y5 y6 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m)) ->
    evt asegs Q (dispstA q' x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 x30 x31 m).
  Proof.
    intros q' entp x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 x30 x31 m Q (j0 & j160 & QC) MI EC HACC ER K.
    pose proof POK as POK'. pokA POK'. clear PLB.
    unfold dispstA, pregs, eSH in *.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let a := reg_val 18 in
      destruct (AWAuto2.acc_loadw mm (P + 452) 4 a ltac:(lia) ltac:(clear - PAL; Z.div_mod_to_equations; lia) ltac:(lia) HACC ltac:(shadow_addr_tac)) as (k & SHR & Hk) end.
    destruct Hk as [-> | [K1 K2]]; [| exfalso; clear - PAL K1 K2; Z.div_mod_to_equations; lia].
    step. step. lit_branch. clear SHR HACC.
    zstep. rewrite (sx32_lit entp) by lia.
    pose proof (pjt_read_A m entp MI ER) as TR.
    assert (CASES : entp = 1 \/ entp = 2 \/ entp = 3 \/ entp = 4 \/ entp = 5 \/ entp = 6) by lia.
    unfold blkstA, pregs, eSH in K.
    destruct CASES as [-> |[-> |[-> |[-> |[-> | ->]]]]]; cbn [pjt_tgt Z.eqb Pos.eqb] in *;
      (zstep; zstep; zstep; step; lit_branch; zstep; zstep; zstep; rewrite ?sx32_lit by lia; zstep; zstep; rewrite ?ret_pc_even by lia; apply K).
  Qed.

  Definition exitstA (q' r : Z) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 (m : mem) : machine_state :=
    MS (mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') x10 x11 x12 x13 x14 x15 x16 x17
            x18 x19 x20 x21 x22 x23 x24 x25 (wz r) (wz SF) x28 x29 x30 x31)
       F_ (wz PE_EXIT) fc None m (seg_rom asegs).

  #[using="Type"] Lemma loopE : forall (q' r : Z) x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    0 <= r <= 6 ->
    (r = 6 -> forall y10, evt asegs Q (dispstA q' x1 x5 x6 y10 x11 x12 x13 x14 x15 x16 x17 (wz 6) x28 x29 x30 x31 m)) ->
    (r <> 6 -> forall y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y28 y29 y30 y31,
       evt asegs Q (exitstA q' r y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y28 y29 y30 y31 m)) ->
    evt asegs Q (loopstA q' r x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m).
  Proof.
    intros q' r x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m Q RR KD KX.
    unfold loopstA, dispstA, exitstA, pregs in *.
    zstep. step. if_cases KB; zify_cond KB.
    - apply KX. lia.
    - assert (r = 6) by lia. subst r. apply KD. reflexivity.
  Qed.

  Definition retire_pc (pc : Z) : Prop := pc = 0x8a1f4 \/ pc = 0x89fd0 \/ pc = 0x8a0a4 \/ pc = 0x8a14c \/ pc = 0x8a350 \/ pc = 0x8a1bc.
  #[using="m0 POK RF0"] Lemma retireE : forall (pc q' r : Z) (R : mem -> Prop)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 m,
    retire_pc pc -> pinv q' m -> R m -> rframeE R ->
    evt asegs (epostA (fun m' r' => R m' /\ r' = r))
      (MS (mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 (wz r) (wz SF) x28 x29 x30 x31)
          F_ (wz pc) fc None m (seg_rom asegs)).
  Proof.
    intros pc q' r R x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 m HPC INV HR RFR.
    destruct INV as (ST & (j0 & j160 & QC) & MI & AE & (QB & QAL) & VR).
    destruct VR as (Hq & GAP & FRhi & (w0 & FH) & (jf & FT1) & FT2 & SHF & FLG & (stc & RF & LIVE1)).
    pose proof POK as POK'. pokA POK'. clear PLB.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (FSB1 & FSB2 & _ & FSB4 & FSB5).
    destruct (new_frame_facts FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (_ & FLO & FHI & FAL & FLLO & FLHI & _).
    cbn [FB_of] in FHI.
    assert (SFB : 8 * (SF - 2147450880) = F) by (unfold eSF, sh, SHADOW_OFF; clear - FAL; Z.div_mod_to_equations; lia).
    assert (FSF : F + 128 <= SF \/ SF + 16 <= F) by (clear - SFB FLO FHI FSB1 FSB2 FSB5 ACR; lia).
    clear FSB5 FSB4 FAL. hide FSF. hide Hq. hide PAL. hide AL16. hide QAL.
    assert (RFm : forall m', munch [(F, F + 8)]%Z m m' -> wmono asegs m m' -> R m').
    { intros m' MU WM. apply (RFR m m' HR); [| exact WM]. eapply munch_weaken; [| exact MU]. unfold pWE. intros xx OO. cbn [outside] in *. clear - OO. lia. }
    assert (AEm : forall m', munch [(F, F + 8)]%Z m m' -> wmono asegs m m' -> asan_env asegs m' /\ RFAKE FI stc m').
    { intros m' MU WM. split.
      - apply (asan_env_frame asegs m m' [(F, F + 8)]%Z AE MU WM). unfold env_safe. constructor; [left; cbn [fst snd]; clear - FLO FSB1; lia| constructor].
      - apply (rfake_frame FI stc m m' [(F, F + 8)]%Z RF MU WM). constructor; [| constructor]. right; left. cbn [fst snd].
        pose proof (lb_new _ _ _ LIVE1) as LVF. unfold ff_size in LVF.
        destruct (new_frame_facts FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & _). rewrite FCLS in LVF. cbn [FB_of] in LVF.
        change (ff_addr (fs_newff FI st 1)) with F in LVF. apply (Contracts.lb_sub _ _ _ _ _ LVF); lia. }
    clear HR AE RF. hide SHF. unfold eSH in QC.
    pose proof (munch_refl [(F, F + 8)]%Z m) as MU1. pose proof (wmono_refl asegs m) as WM1.
    destruct HPC as [-> |[-> |[-> |[-> |[-> | ->]]]]];
      (zstep; zstep; zstep; sstep; zstep; step; if_cases K0; zify_cond K0; try (exfalso; lia); clear K0;
       lazymatch type of MU1 with munch _ _ ?m1 =>
         assert (SHF1 : rw_cells asegs m1 SF (eshadow)) by (unhide SHF; unfold eshadow in *; eapply rw_cells_transport; [exact SHF| exact MU1| exact WM1| cbn [disjoint_from]; simpl_sizes; split; [| exact I]; unhide FSF; clear - FSF; lia]) end;
       unhide Hq; unhide QAL;
       eapply (exitF q' r R); [| exact (RFm _ MU1 WM1)| exact RFR];
       split; [eassumption|]; split; [do 2 eexists; unfold eSH; eassumption|]; split; [eassumption|]; split; [exact (proj1 (AEm _ MU1 WM1))|]; split; [exact (conj QB QAL)|];
       split; [exact Hq|]; split; [eassumption|]; split; [eassumption|]; split; [eexists; eassumption|]; split; [eexists; eassumption|]; split; [eassumption|];
       split; [exact SHF1|]; split; [eassumption|]; exists stc; split; [exact (proj2 (AEm _ MU1 WM1))| exact LIVE1]).
  Qed.

  Definition inP (iv : ivl) : Prop := P <= fst iv /\ fst iv <= snd iv /\ snd iv <= P + 504.
  #[using="Type"] Lemma dj_inP : forall (W : list ivl) X n, Forall inP W -> (X + n <= P \/ P + 504 <= X) -> disjoint_from W X n.
  Proof.
    induction W as [|[a b] W IH]; intros X n HW HX; cbn [disjoint_from]; [exact I|].
    inversion HW as [|? ? (H1 & H2 & H3) HW']; subst. cbn [fst snd] in *. split; [lia| exact (IH X n HW' HX)].
  Qed.
  #[using="m0 POK RF0"] Lemma pinv_stepP : forall shd, Z.of_nat (cells_size shd) = 16 -> forall q' m m' (W : list ivl),
    pinvS shd q' m -> munch W m m' -> wmono asegs m m' -> mem_inv asegs m' -> Forall inP W -> pinvS shd q' m'.
  Proof.
    intros shd HSZ q' m m' W (ST & (j0 & j160 & QC) & MI & AE & (QB & QAL) & VR) MU WM MI' HW.
    destruct VR as (Hq & GAP & FRhi & (w0 & FH) & (jf & FT1) & FT2 & SHF & FLG & (stc & RF & LIVE1)).
    pose proof POK as POK'. pokA POK'.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (FSB1 & FSB2 & _).
    destruct (new_frame_facts FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (_ & FLO & FHI & _ & FLLO & FLHI & APART).
    cbn [FB_of SB_of] in FHI, APART.
    assert (SH1 : sh (FSB FI) <= SF /\ SF + 16 <= sh (FSB FI) + A0_FS_SHSIZE).
    { pose proof (fsb_ok FI) as (_ & _ & _ & B4 & _). unfold eSF, sh, SHADOW_OFF. clear - FLO FHI B4. Z.div_mod_to_equations. lia. }
    pose proof (lb_apart_frame _ _ _ F 128 _ _ PLB APART) as PF.
    pose proof (lb_apart_shadow FI st m0 _ _ SF 16 RF0 PLB ltac:(lia) ltac:(lia)) as PS.
    pose proof (lb_apart_flag FI st m0 _ _ FL RF0 PLB FLLO FLHI) as PL.
    assert (LSUB : forall g, In g (fs_live FI st) -> In g (fs_live FI stc)) by (intros g Hg; rewrite LIVE1; right; exact Hg).
    assert (DJ : forall X n, (X + n <= P \/ P + 504 <= X) -> disjoint_from W X n) by (intros X n HX; exact (dj_inP W X n HW HX)).
    split; [eapply stk_transport_disjoint; [exact ST| exact MU| exact WM| apply DJ; right; lia]|].
    split; [exists j0, j160; eapply rw_cells_transport; [exact QC| exact MU| exact WM| apply DJ; right; simpl_sizes; lia]|].
    split; [exact MI'|].
    split. { apply (asan_env_frame asegs m m' W AE MU WM). unfold env_safe. eapply Forall_impl; [| exact HW]. intros [a b] (H1 & H2 & H3). cbn [fst snd] in *. left. lia. }
    split; [exact (conj QB QAL)|].
    split; [exact Hq|].
    split; [eapply stk_transport_disjoint; [exact GAP| exact MU| exact WM| apply DJ; right; lia]|].
    split; [eapply rw_cells_transport; [exact FRhi| exact MU| exact WM| apply DJ; right; simpl_sizes; lia]|].
    split; [exists w0; eapply rw_cells_transport; [exact FH| exact MU| exact WM| apply DJ; simpl_sizes; clear - PF; lia]|].
    split; [exists jf; eapply rw_cells_transport; [exact FT1| exact MU| exact WM| apply DJ; simpl_sizes; clear - PF; lia]|].
    split; [eapply rw_cells_transport; [exact FT2| exact MU| exact WM| apply DJ; simpl_sizes; clear - PF; lia]|].
    split; [eapply rw_cells_transport; [exact SHF| exact MU| exact WM| apply DJ; rewrite HSZ; clear - PS; lia]|].
    split; [eapply rw_cells_transport; [exact FLG| exact MU| exact WM| apply DJ; simpl_sizes; clear - PL; lia]|].
    exists stc. split; [| exact LIVE1].
    apply (rfake_frame FI stc m m' W RF MU WM). eapply Forall_impl; [| exact HW]. intros [a b] (H1 & H2 & H3). cbn [fst snd] in *.
    right; left. apply (lb_mono (fs_live FI st)); [apply (Contracts.lb_sub _ _ _ _ _ PLB); lia| exact LSUB].
  Qed.

  #[using="m0 POK RF0"] Lemma pobj_rframe : forall X cs, P <= X -> X + Z.of_nat (cells_size cs) <= P + 504 -> rframeE (fun mm => rw_cells asegs mm X cs).
  Proof.
    intros X cs H1 H2 m m' H MU WM. pose proof POK as POK'. pokA POK'.
    pose proof (fsb_ok FI) as (FSB1 & FSB2 & _).
    destruct (new_frame_facts FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (_ & FLO & FHI & _ & FLLO & FLHI & APART).
    cbn [FB_of SB_of] in FHI, APART.
    assert (SH1 : sh (FSB FI) <= SF /\ SF + 16 <= sh (FSB FI) + A0_FS_SHSIZE).
    { pose proof (fsb_ok FI) as (_ & _ & _ & B4 & _). unfold eSF, sh, SHADOW_OFF. clear - FLO FHI B4. Z.div_mod_to_equations. lia. }
    pose proof (lb_apart_frame _ _ _ F 128 _ _ PLB APART) as PF.
    pose proof (lb_apart_shadow FI st m0 _ _ SF 16 RF0 PLB ltac:(lia) ltac:(lia)) as PS.
    pose proof (lb_apart_flag FI st m0 _ _ FL RF0 PLB FLLO FLHI) as PL.
    eapply rw_cells_transport; [exact H| exact MU| exact WM|]. unfold pWE. cbn [disjoint_from].
    clear - H1 H2 PHI CLO PF PS PL. repeat split; try exact I; lia.
  Qed.

  Definition blk4W : list ivl := [(P + 384, P + 400); (P + 488, P + 496)]%Z.
  #[using="m0 POK RF0"] Lemma blk4E : forall (q' disc buf mlen esp : Z) (w384 w392 wcur : word) x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m,
    pinv q' m -> shw m P 504 -> 0 <= mlen < 2^64 -> 0 <= esp < 2^64 ->
    rw_cells asegs m (P + 264) [C8 (wz disc)] ->
    rw_cells asegs m (P + 384) [C8 w384; C8 w392; C8 (wz buf); C8 (wz mlen)] ->
    rw_cells asegs m (P + 472) [C8 (wz esp)] -> rw_cells asegs m (P + 488) [C8 wcur] ->
    evt asegs (epostA (fun m' r' =>
                 (munch (blk4W ++ pWE) m m' /\ wmono asegs m m'
                  /\ rw_cells asegs m' (P + 264) [C8 (wz disc)]
                  /\ rw_cells asegs m' (P + 384) [C8 (wz (buf + esp)); C8 (wz (mlen - esp + disc)); C8 (wz buf); C8 (wz mlen)]
                  /\ rw_cells asegs m' (P + 472) [C8 (wz esp)] /\ rw_cells asegs m' (P + 488) [C8 (wz mlen)]) /\ r' = 2))
      (blkstA q' 0x89f24 x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m).
  Proof.
    intros q' disc buf mlen esp w384 w392 wcur x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m INV SHP MLR ESR C264 C384 C472 C488.
    pose proof INV as INV0. destruct INV as (_ & (j0 & j160 & QC) & MI & _ & (QB & _) & _).
    pose proof POK as POK'. pokA POK'. clear PLB.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    unfold blkstA, pregs, eSH in *.
    pose proof (munch_refl blk4W m) as MU. pose proof (wmono_refl asegs m) as WM. unfold blk4W in MU.
    walk_lia_to 0x89fd0.
    rewrite ?Z.mod_small in C384 by lia.
    assert (HW : Forall inP blk4W) by (unfold blk4W, inP; repeat constructor; cbn [fst snd]; lia).
    pose proof (pinv_stepP eshadow eq_refl q' m _ blk4W INV0 MU WM MI HW) as INV1.
    eapply evt_mono.
    - eapply (retireE 0x89fd0 q' 2 (fun mm => munch (blk4W ++ pWE) m mm /\ wmono asegs m mm
                  /\ rw_cells asegs mm (P + 264) [C8 (wz disc)]
                  /\ rw_cells asegs mm (P + 384) [C8 (wz (buf + esp)); C8 (wz (mlen - esp + disc)); C8 (wz buf); C8 (wz mlen)]
                  /\ rw_cells asegs mm (P + 472) [C8 (wz esp)] /\ rw_cells asegs mm (P + 488) [C8 (wz mlen)]));
        [right; left; reflexivity| exact INV1| |].
      + split; [eapply munch_weaken; [| exact MU]; intros xx OO; unfold blk4W, pWE in *; cbn [app outside] in *; clear - OO; tauto|].
        split; [exact WM|]. split; [exact C264|]. split; [exact C384|]. split; [exact C472| exact C488].
      + intros mA mB (H1 & H2 & H3 & H4 & H5 & H6) MUx WMx.
        split; [eapply munch_trans; [exact H1|]; eapply munch_weaken; [| exact MUx]; intros xx OO; unfold blk4W, pWE in *; cbn [app outside] in *; clear - OO; tauto|].
        split; [exact (wmono_trans _ _ _ _ H2 WMx)|].
        split; [apply (fun A B => pobj_rframe (P + 264) _ A B mA mB H3 MUx WMx); [lia| simpl_sizes; lia]|].
        split; [apply (fun A B => pobj_rframe (P + 384) _ A B mA mB H4 MUx WMx); [lia| simpl_sizes; lia]|].
        split; [apply (fun A B => pobj_rframe (P + 472) _ A B mA mB H5 MUx WMx); [lia| simpl_sizes; lia]|].
        apply (fun A B => pobj_rframe (P + 488) _ A B mA mB H6 MUx WMx); [lia| simpl_sizes; lia].
    - intros ms V. exact V.
  Qed.

  #[using="m0 POK RF0"] Lemma pinv_stepSh : forall shd shd' q' m m', pinvS shd q' m -> munch [(SF, SF + 16)]%Z m m' -> wmono asegs m m' -> mem_inv asegs m' ->
    rw_cells asegs m' SF shd' -> pinvS shd' q' m'.
  Proof.
    intros shd shd' q' m m' (ST & (j0 & j160 & QC) & MI & AE & (QB & QAL) & VR) MU WM MI' SHF'.
    destruct VR as (Hq & GAP & FRhi & (w0 & FH) & (jf & FT1) & FT2 & SHF & FLG & (stc & RF & LIVE1)).
    pose proof POK as POK'. pokA POK'. clear PLB.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (FSB1 & FSB2 & _ & FSB4 & FSB5).
    destruct (new_frame_facts FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & FLO & FHI & FAL & FLLO & FLHI & _).
    cbn [FB_of] in FHI.
    assert (SFB : 8 * (SF - 2147450880) = F) by (unfold eSF, sh, SHADOW_OFF; clear - FAL; Z.div_mod_to_equations; lia).
    assert (AP : SF + 16 <= lo /\ 0x609000 <= SF /\ (F + 128 <= SF \/ SF + 16 <= F) /\ (FL + 1 <= SF \/ SF + 16 <= FL))
      by (clear - SFB FLO FHI FLLO FLHI FSB1 FSB2 FSB5 ACR CLO; lia).
    destruct AP as (A1 & A2 & A3 & A4).
    assert (DJ : forall X n, (X + n <= SF \/ SF + 16 <= X) -> disjoint_from [(SF, SF + 16)]%Z X n) by (intros X n HX; cbn [disjoint_from]; split; [lia| exact I]).
    split; [eapply stk_transport_disjoint; [exact ST| exact MU| exact WM| apply DJ; right; lia]|].
    split; [exists j0, j160; eapply rw_cells_transport; [exact QC| exact MU| exact WM| apply DJ; right; simpl_sizes; lia]|].
    split; [exact MI'|].
    split. { apply (asan_env_frame asegs m m' _ AE MU WM). unfold env_safe. constructor; [left; cbn [fst snd]; lia| constructor]. }
    split; [exact (conj QB QAL)|].
    split; [exact Hq|].
    split; [eapply stk_transport_disjoint; [exact GAP| exact MU| exact WM| apply DJ; right; lia]|].
    split; [eapply rw_cells_transport; [exact FRhi| exact MU| exact WM| apply DJ; right; simpl_sizes; lia]|].
    split; [exists w0; eapply rw_cells_transport; [exact FH| exact MU| exact WM| apply DJ; simpl_sizes; clear - A3; lia]|].
    split; [exists jf; eapply rw_cells_transport; [exact FT1| exact MU| exact WM| apply DJ; simpl_sizes; clear - A3; lia]|].
    split; [eapply rw_cells_transport; [exact FT2| exact MU| exact WM| apply DJ; simpl_sizes; clear - A3; lia]|].
    split; [exact SHF'|].
    split; [eapply rw_cells_transport; [exact FLG| exact MU| exact WM| apply DJ; simpl_sizes; clear - A4; lia]|].
    exists stc. split; [| exact LIVE1].
    apply (rfake_frame FI stc m m' _ RF MU WM). constructor; [| constructor]. right; right. cbn [fst snd].
    pose proof (ls_new _ _ _ LIVE1) as LVS. unfold ff_shsize in LVS. rewrite FCLS in LVS. cbn [SB_of] in LVS.
    change (ff_addr (fs_newff FI st 1)) with F in LVS. change (sh F) with SF in LVS. apply (Contracts.ls_sub _ _ _ _ _ LVS); lia.
  Qed.

  #[using="m0 POK RF0"] Lemma repoisonE : forall (q' r : Z) x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    pinvS eshadowU q' m ->
    (forall y10 m', pinv q' m' -> munch [(SF, SF + 16)]%Z m m' -> wmono asegs m m' ->
       evt asegs Q (loopstA q' r x1 x5 x6 y10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m')) ->
    evt asegs Q (MS (pregs q P st gp tp q' x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 (wz r) x28 x29 x30 x31) F_ (wz 0x89ecc) fc None m (seg_rom asegs)).
  Proof.
    intros q' r x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m Q INV K.
    pose proof INV as INV0. destruct INV as (_ & _ & MI & _ & _ & VR). destruct VR as (_ & _ & _ & _ & _ & _ & SHF & _).
    unfold pregs, loopstA, eshadowU in *.
    pose proof (munch_refl [(SF, SF + 16)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. sstep. sstep. sstep. step.
    eapply K; [| exact MU| exact WM].
    eapply (pinv_stepSh _ _ q' m _ INV0 MU WM); [eassumption| exact SHF].
  Qed.

  #[using="m0 POK RF0"] Lemma unpoisonE : forall (q' : Z) x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    pinv q' m ->
    (forall m', pinvS eshadowU q' m' -> munch [(SF, SF + 16)]%Z m m' -> wmono asegs m m' ->
       evt asegs Q (MS (pregs q P st gp tp q' x1 x5 x6 (wz 4) (wz 5) x12 x13 x14 x15 x16 x17 (wz 3) x28 x29 x30 x31) F_ (wz 0x89c48) fc None m' (seg_rom asegs))) ->
    evt asegs Q (blkstA q' 0x89c38 x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m).
  Proof.
    intros q' x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m Q INV K.
    pose proof INV as INV0. destruct INV as (_ & _ & MI & _ & _ & VR). destruct VR as (_ & _ & _ & _ & _ & _ & SHF & _).
    unfold blkstA, pregs, eshadow in *.
    pose proof (munch_refl [(SF, SF + 16)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    sstep. sstep. zstep. sstep.
    eapply K; [| exact MU| exact WM].
    eapply (pinv_stepSh _ _ q' m _ INV0 MU WM); [eassumption| exact SHF].
  Qed.

  Definition outX (iv : ivl) : Prop :=
    fst iv <= snd iv /\ 0x609000 <= fst iv /\ snd iv <= alloc_ceiling
    /\ (snd iv <= FSB FI \/ FSB FI + A0_FS_SIZE <= fst iv) /\ (snd iv <= 0x7fff7000 \/ 0x10007fff8000 <= fst iv).
  Definition clsX (X n : Z) : Prop :=
    alloc_ceiling <= X \/ (FSB FI <= X /\ X + n <= FSB FI + A0_FS_SIZE) \/ (0x7fff7000 <= X /\ X + n <= 0x10007fff8000).
  #[using="Type"] Lemma dj_inPX : forall (W : list ivl) X n, Forall (fun iv => inP iv \/ outX iv) W -> (X + n <= P \/ P + 504 <= X) -> clsX X n ->
    disjoint_from W X n.
  Proof.
    induction W as [|[a b] W IH]; intros X n HW HX HC'; cbn [disjoint_from]; [exact I|].
    inversion HW as [|? ? HH HW']; subst. split; [| exact (IH X n HW' HX HC')].
    destruct HH as [(H1 & H2 & H3)|(H1 & H2 & H3 & H4 & H5)]; cbn [fst snd] in *; [lia|].
    unfold clsX in HC'. lia.
  Qed.
  #[using="m0 POK RF0"] Lemma pinv_stepX : forall shd, Z.of_nat (cells_size shd) = 16 -> forall q' m m' (W : list ivl),
    pinvS shd q' m -> munch W m m' -> wmono asegs m m' -> mem_inv asegs m' -> Forall (fun iv => inP iv \/ outX iv) W -> pinvS shd q' m'.
  Proof.
    intros shd HSZ q' m m' W (ST & (j0 & j160 & QC) & MI & AE & (QB & QAL) & VR) MU WM MI' HW.
    destruct VR as (Hq & GAP & FRhi & (w0 & FH) & (jf & FT1) & FT2 & SHF & FLG & (stc & RF & LIVE1)).
    pose proof POK as POK'. pokA POK'.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (FSB1 & FSB2 & _ & FSB4 & FSB5).
    destruct (new_frame_facts FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (_ & FLO & FHI & _ & FLLO & FLHI & APART).
    cbn [FB_of SB_of] in FHI, APART.
    assert (SH1 : sh (FSB FI) <= SF /\ SF + 16 <= sh (FSB FI) + A0_FS_SHSIZE).
    { unfold eSF, sh, SHADOW_OFF. clear - FLO FHI FSB4. Z.div_mod_to_equations. lia. }
    assert (SH2 : 0x7fff8000 <= sh (FSB FI) /\ sh (FSB FI) + A0_FS_SHSIZE <= 0x10007fff8000).
    { unfold sh, SHADOW_OFF. clear - FSB1 FSB2 ACR. Z.div_mod_to_equations. lia. }
    pose proof (lb_apart_frame _ _ _ F 128 _ _ PLB APART) as PF.
    pose proof (lb_apart_shadow FI st m0 _ _ SF 16 RF0 PLB ltac:(lia) ltac:(lia)) as PS.
    pose proof (lb_apart_flag FI st m0 _ _ FL RF0 PLB FLLO FLHI) as PL.
    assert (LSUB : forall g, In g (fs_live FI st) -> In g (fs_live FI stc)) by (intros g Hg; rewrite LIVE1; right; exact Hg).
    assert (DJ : forall X n, (X + n <= P \/ P + 504 <= X) -> clsX X n -> disjoint_from W X n) by (intros X n HX HC'; exact (dj_inPX W X n HW HX HC')).
    split; [eapply stk_transport_disjoint; [exact ST| exact MU| exact WM| apply DJ; [right; lia| left; lia]]|].
    split; [exists j0, j160; eapply rw_cells_transport; [exact QC| exact MU| exact WM| apply DJ; [right; simpl_sizes; lia| left; lia]]|].
    split; [exact MI'|].
    split. { apply (asan_env_frame asegs m m' W AE MU WM). unfold env_safe. eapply Forall_impl; [| exact HW].
             intros [a b] [(H1 & H2 & H3)|(H1 & H2 & _)]; cbn [fst snd] in *; left; lia. }
    split; [exact (conj QB QAL)|].
    split; [exact Hq|].
    split; [eapply stk_transport_disjoint; [exact GAP| exact MU| exact WM| apply DJ; [right; lia| left; lia]]|].
    split; [eapply rw_cells_transport; [exact FRhi| exact MU| exact WM| apply DJ; [right; simpl_sizes; lia| left; lia]]|].
    split; [exists w0; eapply rw_cells_transport; [exact FH| exact MU| exact WM| apply DJ; [simpl_sizes; clear - PF; lia| right; left; simpl_sizes; clear - FLO FHI FSB1; lia]]|].
    split; [exists jf; eapply rw_cells_transport; [exact FT1| exact MU| exact WM| apply DJ; [simpl_sizes; clear - PF; lia| right; left; simpl_sizes; clear - FLO FHI FSB1; lia]]|].
    split; [eapply rw_cells_transport; [exact FT2| exact MU| exact WM| apply DJ; [simpl_sizes; clear - PF; lia| right; left; simpl_sizes; clear - FLO FHI FSB1; lia]]|].
    split; [eapply rw_cells_transport; [exact SHF| exact MU| exact WM| apply DJ; [rewrite HSZ; clear - PS; lia| right; right; rewrite HSZ; clear - SH1 SH2; lia]]|].
    split; [eapply rw_cells_transport; [exact FLG| exact MU| exact WM| apply DJ; [simpl_sizes; clear - PL; lia| right; left; simpl_sizes; clear - FLLO FLHI FSB1; lia]]|].
    exists stc. split; [| exact LIVE1].
    apply (rfake_frame FI stc m m' W RF MU WM). eapply Forall_impl; [| exact HW].
    intros [a b] [(H1 & H2 & H3)|(H1 & H2 & H3 & H4 & H5)]; cbn [fst snd] in *.
    - right; left. apply (lb_mono (fs_live FI st)); [apply (Contracts.lb_sub _ _ _ _ _ PLB); lia| exact LSUB].
    - left. split; [exact H4|]. clear - H5 SH2. lia.
  Qed.

  #[using="ra"] Lemma cb_split1E : forall m X (n : nat) (xs : list byte) (k : nat),
    rw_cells asegs m X [CB n xs] -> (k < n)%nat -> 0 <= X ->
    rw_cells asegs m X [CB k (firstn k xs)] /\ rw_cells asegs m (X + Z.of_nat k) [CB 1 (firstn 1 (skipn k xs)); CB (n - k - 1) (skipn (k + 1) xs)].
  Proof.
    intros m X n xs k BLK LT X0.
    assert (LXS : length xs = n) by (destruct BLK as [[W _] _]; cbn in W; LiaTuning.ctauto).
    apply (rw_cells_split_CB asegs m X [] n xs [] [k; 1%nat; (n - k - 1)%nat]) in BLK; [| cbn; lia].
    cbn [app mk_CB_cells] in BLK.
    lazymatch type of BLK with rw_cells _ _ _ [?c1; ?c2; ?c3] =>
      destruct (proj1 (rw_cells_app asegs m X [c1] [c2; c3]) BLK) as [BLK1 BLK23] end.
    cbn [cells_size csize] in BLK23. rewrite Nat.add_0_r in BLK23.
    replace (firstn (n - k - 1) (skipn 1 (skipn k xs))) with (skipn (k + 1) xs) in BLK23.
    2:{ rewrite skipn_skipn. replace (1 + k)%nat with (k + 1)%nat by lia. symmetry. apply firstn_all2. rewrite length_skipn. lia. }
    split; [exact BLK1| exact BLK23].
  Qed.
  Notation set_byte := P0.H_presp_B.set_byte.
  #[using="Type"] Lemma cb_join1E : forall m X (n : nat) (xs : list byte) (k : nat) (b : byte),
    rw_cells asegs m X [CB k (firstn k xs)] -> rw_cells asegs m (X + Z.of_nat k) [CB 1 [b]; CB (n - k - 1) (skipn (k + 1) xs)] ->
    (k < n)%nat -> length xs = n ->
    rw_cells asegs m X [CB n (set_byte xs k b)].
  Proof.
    intros m X n xs k b BLK1 BLK23 LT LXS.
    pose proof (proj2 (rw_cells_app asegs m X [CB k (firstn k xs)] [CB 1 [b]; CB (n - k - 1) (skipn (k + 1) xs)])) as J.
    cbn [cells_size csize Nat.add] in J. rewrite Nat.add_0_r in J. specialize (J (conj BLK1 BLK23)). cbn [app] in J.
    pose proof (rw_cells_merge asegs m X [] [CB k (firstn k xs); CB 1 [b]; CB (n - k - 1) (skipn (k + 1) xs)] []) as M.
    rewrite !app_nil_r in M. cbn [app cells_size csize cells_bytes cbytes Nat.add] in M.
    replace (k + Datatypes.S (n - k - 1 + 0))%nat with n in M by lia.
    pose proof (M J) as MJ. rewrite app_nil_r in MJ. exact MJ.
  Qed.

  #[using="Type"] Lemma epostA_mono : forall (X Y : mem -> Z -> Prop), (forall m' r, X m' r -> Y m' r) -> forall ms, epostA X ms -> epostA Y ms.
  Proof.
    intros X Y HXY ms (r & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & st' & E & H1 & H2 & H3 & H4 & H5 & HX).
    exists r, t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', st'.
    split; [exact E|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. exact (HXY _ _ HX).
  Qed.
  #[using="Type"] Lemma zx32_litE : forall x, 0 <= x < 2^32 -> zx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
  Proof. intros x H. unfold zx32. f_equal. rewrite unsigned_lit by lia. apply Z.mod_small. lia. Qed.

  #[using="P m0 POK RF0"] Lemma xobj_rframe : forall X cs n, Z.of_nat (cells_size cs) = n -> outX (X, X + n) -> rframeE (fun mm => rw_cells asegs mm X cs).
  Proof.
    intros X cs n Hn (H1 & H2 & H3 & H4 & H5) m m' H MU WM. cbn [fst snd] in *. pose proof POK as POK'. pokA POK'.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (FSB1 & FSB2 & _ & FSB4 & FSB5).
    destruct (new_frame_facts FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (_ & FLO & FHI & _ & FLLO & FLHI & _).
    cbn [FB_of SB_of] in FHI.
    assert (SH1 : sh (FSB FI) <= SF /\ SF + 16 <= sh (FSB FI) + A0_FS_SHSIZE).
    { unfold eSF, sh, SHADOW_OFF. clear - FLO FHI FSB4. Z.div_mod_to_equations. lia. }
    assert (SH2 : 0x7fff8000 <= sh (FSB FI) /\ sh (FSB FI) + A0_FS_SHSIZE <= 0x10007fff8000).
    { unfold sh, SHADOW_OFF. clear - FSB1 FSB2 ACR. Z.div_mod_to_equations. lia. }
    eapply rw_cells_transport; [exact H| exact MU| exact WM|]. unfold pWE. cbn [disjoint_from]. rewrite Hn.
    clear - H1 H2 H3 H4 H5 CLO FLO FHI SH1 SH2 FLLO FLHI. repeat split; try exact I; lia.
  Qed.

  Definition blk2W : list ivl := [(P + 384, P + 400); (P + 448, P + 452)]%Z.
  Definition blk2post (buf mlen cap esp clen : Z) (w384 wpos : word) (bs : list byte) (m m' : mem) (r : Z) : Prop :=
    wmono asegs m m'
    /\ rw_cells asegs m' (P + 264) [C8 (wz 0)] /\ rw_cells asegs m' (P + 456) [C4 (wz clen)] /\ rw_cells asegs m' (P + 472) [C8 (wz esp)]
    /\ ( (r = 1 /\ mlen - esp < clen /\ munch (blk2W ++ pWE) m m'
          /\ rw_cells asegs m' (P + 384) [C8 w384; C8 (wz (mlen - esp)); C8 (wz buf); C8 (wz mlen)] /\ rw_cells asegs m' (P + 448) [C4 wpos])
       \/ (r = 0 /\ clen <= mlen - esp
           /\ rw_cells asegs m' (P + 384) [C8 (wz (buf + esp)); C8 (wz clen); C8 (wz buf); C8 (wz mlen)] /\ rw_cells asegs m' (P + 448) [C4 (wz 4)]
           /\ ( (clen = mlen - esp /\ munch (blk2W ++ pWE) m m')
              \/ (clen < mlen - esp /\ munch ((buf + (esp + clen), buf + (esp + clen) + 1) :: blk2W ++ pWE) m m'
                  /\ rw_cells asegs m' buf [CB (Z.to_nat (cap + 1)) (set_byte bs (Z.to_nat (esp + clen)) (Z_to_bv 8 0))]))) ).
  #[using="m0 POK RF0"] Lemma blk2E : forall (q' buf mlen cap esp clen : Z) (w384 w392 wpos : word) (bs : list byte) x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m,
    pinv q' m -> shw m P 504 -> 0 <= esp <= mlen -> mlen <= cap -> cap + 1 <= 2^32 -> 0 <= clen < 2^32 -> 0 <= buf < 2^63 ->
    rw_cells asegs m (P + 264) [C8 (wz 0)] ->
    rw_cells asegs m (P + 384) [C8 w384; C8 w392; C8 (wz buf); C8 (wz mlen)] ->
    rw_cells asegs m (P + 448) [C4 wpos] -> rw_cells asegs m (P + 456) [C4 (wz clen)] ->
    rw_cells asegs m (P + 472) [C8 (wz esp)] ->
    (clen < mlen - esp -> outX (buf, buf + (cap + 1)) /\ shw m buf (cap + 1) /\ rw_cells asegs m buf [CB (Z.to_nat (cap + 1)) bs]) ->
    evt asegs (epostA (blk2post buf mlen cap esp clen w384 wpos bs m))
      (blkstA q' 0x8a0c0 x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m).
  Proof.
    intros q' buf mlen cap esp clen w384 w392 wpos bs x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m INV SHP ESR MLC CAPR CLR BUFR C264 C384 C448 C456 C472 TXT.
    pose proof INV as INV0. destruct INV as (_ & (j0 & j160 & QC) & MI & _ & (QB & _) & _).
    pose proof POK as POK'. pokA POK'. clear PLB.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    unfold blkstA, pregs, eSH in *.
    destruct (Z.lt_ge_cases (mlen - esp) clen) as [LT|GE].
    {
      pose proof (munch_refl blk2W m) as MU. pose proof (wmono_refl asegs m) as WM. unfold blk2W in MU. clear TXT.
      walk_lia_to 0x8a14c. rewrite (zx32_litE clen) by lia. if_cases K1; zify_cond K1; [exfalso; lia|].
      walk_lia_to 0x8a14c.
      rewrite ?Z.mod_small in C384 by lia.
      assert (HW : Forall inP blk2W) by (unfold blk2W, inP; repeat constructor; cbn [fst snd]; lia).
      pose proof (pinv_stepP eshadow eq_refl q' m _ blk2W INV0 MU WM MI HW) as INV1.
      eapply evt_mono.
      - eapply (retireE 0x8a14c q' 1 (fun mm => munch (blk2W ++ pWE) m mm /\ wmono asegs m mm
                  /\ rw_cells asegs mm (P + 264) [C8 (wz 0)]
                  /\ rw_cells asegs mm (P + 384) [C8 w384; C8 (wz (mlen - esp)); C8 (wz buf); C8 (wz mlen)]
                  /\ rw_cells asegs mm (P + 448) [C4 wpos] /\ rw_cells asegs mm (P + 456) [C4 (wz clen)]
                  /\ rw_cells asegs mm (P + 472) [C8 (wz esp)]));
          [right; right; right; left; reflexivity| exact INV1| |].
        + split; [eapply munch_weaken; [| exact MU]; intros xx OO; unfold blk2W, pWE in *; cbn [app outside] in *; clear - OO; tauto|].
          split; [exact WM|]. split; [exact C264|]. split; [exact C384|]. split; [exact C448|]. split; [exact C456| exact C472].
        + intros mA mB (H1 & H2 & H3 & H4 & H5 & H6 & H7) MUx WMx.
          split; [eapply munch_trans; [exact H1|]; eapply munch_weaken; [| exact MUx]; intros xx OO; unfold blk2W, pWE in *; cbn [app outside] in *; clear - OO; tauto|].
          split; [exact (wmono_trans _ _ _ _ H2 WMx)|].
          split; [apply (fun A B => pobj_rframe (P + 264) _ A B mA mB H3 MUx WMx); [lia| simpl_sizes; lia]|].
          split; [apply (fun A B => pobj_rframe (P + 384) _ A B mA mB H4 MUx WMx); [lia| simpl_sizes; lia]|].
          split; [apply (fun A B => pobj_rframe (P + 448) _ A B mA mB H5 MUx WMx); [lia| simpl_sizes; lia]|].
          split; [apply (fun A B => pobj_rframe (P + 456) _ A B mA mB H6 MUx WMx); [lia| simpl_sizes; lia]|].
          apply (fun A B => pobj_rframe (P + 472) _ A B mA mB H7 MUx WMx); [lia| simpl_sizes; lia].
      - apply epostA_mono. intros m' r' ((H1 & H2 & H3 & H4 & H5 & H6 & H7) & ->).
        split; [exact H2|]. split; [exact H3|]. split; [exact H6|]. split; [exact H7|].
        left. split; [reflexivity|]. split; [exact LT|]. split; [exact H1|]. split; [exact H4| exact H5]. }
    destruct (Z.eq_dec clen (mlen - esp)) as [EQ|NE].
    {
      pose proof (munch_refl blk2W m) as MU. pose proof (wmono_refl asegs m) as WM. unfold blk2W in MU. clear TXT.
      walk_lia_to 0x8a350. rewrite (zx32_litE clen) by lia. if_cases K1; zify_cond K1; [| exfalso; lia].
      walk_lia_to 0x8a350.
      rewrite (zx32_litE clen) in C384 by lia.
      assert (HW : Forall inP blk2W) by (unfold blk2W, inP; repeat constructor; cbn [fst snd]; lia).
      pose proof (pinv_stepP eshadow eq_refl q' m _ blk2W INV0 MU WM MI HW) as INV1.
      eapply evt_mono.
      - eapply (retireE 0x8a350 q' 0 (fun mm => munch (blk2W ++ pWE) m mm /\ wmono asegs m mm
                  /\ rw_cells asegs mm (P + 264) [C8 (wz 0)]
                  /\ rw_cells asegs mm (P + 384) [C8 (wz (buf + esp)); C8 (wz clen); C8 (wz buf); C8 (wz mlen)]
                  /\ rw_cells asegs mm (P + 448) [C4 (wz 4)] /\ rw_cells asegs mm (P + 456) [C4 (wz clen)]
                  /\ rw_cells asegs mm (P + 472) [C8 (wz esp)]));
          [right; right; right; right; left; reflexivity| exact INV1| |].
        + split; [eapply munch_weaken; [| exact MU]; intros xx OO; unfold blk2W, pWE in *; cbn [app outside] in *; clear - OO; tauto|].
          split; [exact WM|]. split; [exact C264|]. split; [exact C384|]. split; [exact C448|]. split; [exact C456| exact C472].
        + intros mA mB (H1 & H2 & H3 & H4 & H5 & H6 & H7) MUx WMx.
          split; [eapply munch_trans; [exact H1|]; eapply munch_weaken; [| exact MUx]; intros xx OO; unfold blk2W, pWE in *; cbn [app outside] in *; clear - OO; tauto|].
          split; [exact (wmono_trans _ _ _ _ H2 WMx)|].
          split; [apply (fun A B => pobj_rframe (P + 264) _ A B mA mB H3 MUx WMx); [lia| simpl_sizes; lia]|].
          split; [apply (fun A B => pobj_rframe (P + 384) _ A B mA mB H4 MUx WMx); [lia| simpl_sizes; lia]|].
          split; [apply (fun A B => pobj_rframe (P + 448) _ A B mA mB H5 MUx WMx); [lia| simpl_sizes; lia]|].
          split; [apply (fun A B => pobj_rframe (P + 456) _ A B mA mB H6 MUx WMx); [lia| simpl_sizes; lia]|].
          apply (fun A B => pobj_rframe (P + 472) _ A B mA mB H7 MUx WMx); [lia| simpl_sizes; lia].
      - apply epostA_mono. intros m' r' ((H1 & H2 & H3 & H4 & H5 & H6 & H7) & ->).
        split; [exact H2|]. split; [exact H3|]. split; [exact H6|]. split; [exact H7|].
        right. split; [reflexivity|]. split; [exact GE|]. split; [exact H4|]. split; [exact H5|].
        left. split; [exact EQ| exact H1]. }
    assert (LT : clen < mlen - esp) by lia. clear GE NE.
    destruct (TXT LT) as (OX & SHA & BLK). clear TXT.
    pose proof OX as OX'. destruct OX' as (_ & BLO & BHI & TFS & TBAND). cbn [fst snd] in BLO, BHI, TFS, TBAND.

    assert (PFS : FSB FI + 36864 <= P /\ P + 504 <= FSB FI + A0_FS_SIZE).
    { destruct POK as (_ & _ & _ & _ & _ & _ & _ & (g & Hg & G1 & G2)). pose proof (live_num FI st m0 RF0) as LN. rewrite Forall_forall in LN.
      destruct (LN g Hg) as (L1 & L2 & _). clear - G1 G2 L1 L2. lia. }
    set (k := esp + clen). assert (Hk0 : k = esp + clen) by reflexivity. clearbody k.
    assert (HWX : Forall (fun iv => inP iv \/ outX iv) ((buf + k, buf + k + 1) :: blk2W)).
    { unfold blk2W, inP, outX. constructor; [right; cbn [fst snd]; clear - BLO BHI TFS TBAND LT ESR CLR Hk0 MLC; lia|].
      constructor; [left; cbn [fst snd]; lia|]. constructor; [left; cbn [fst snd]; lia| constructor]. }
    assert (PT : buf + (cap + 1) <= P \/ P + 504 <= buf) by (clear - TFS PFS; lia).
    clear TFS TBAND PFS.
    assert (LBS : length bs = Z.to_nat (cap + 1)) by (destruct BLK as [[W _] _]; cbn in W; LiaTuning.ctauto).
    assert (AIV : app_iv (buf, buf + (cap + 1))) by (eapply (app_iv_of_win_ok buf (cap + 1) _ _ (proj2 (proj2 SHA))); lia). hide SHA.
    destruct (cb_split1E m buf (Z.to_nat (cap + 1)) bs (Z.to_nat k) BLK ltac:(lia) ltac:(lia)) as [TX1 TX23]. clear BLK.
    rewrite Z2Nat.id in TX23 by lia.
    remember (Z.to_nat (cap + 1) - Z.to_nat k - 1)%nat as nr eqn:Enr.
    pose proof (munch_refl ((buf + k, buf + k + 1) :: blk2W) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold blk2W in MU.
    walk_lia_to 0x8a350. rewrite (zx32_litE clen) by lia. if_cases K1; zify_cond K1; [| exfalso; lia].
    walk_lia_to 0x8a350.
    unhide SHA. shw_now SHA MU. pose proof (proj1 SHA (buf + k) ltac:(lia)) as HACC. clear SHA.
    replace (buf + (esp - 0) + clen) with (buf + k) by lia.
    gen2 CONT 0x8a2d0 14%nat 15%nat.
    { intros yi yj.
      remember (buf + k) as V eqn:EV.
      sstep.
      walk_lia_to 0x8a350.
      subst V.
      change ((fix add (n m : nat) {struct n} : nat := match n with | 0%nat => m | S p => S (add p m) end) (Z.to_nat k) 1%nat) with (Z.to_nat k + 1)%nat in TX23.
      apply (rw_cells_reshape asegs _ _ _ [CB 1 [Z_to_bv 8 0]; CB nr (skipn (Z.to_nat k + 1) bs)]) in TX23;
        [| destruct TX23 as [[W23 _] _]; cbn in W23 |- *; LiaTuning.ctauto | reflexivity | reflexivity].
      subst nr.
      pose proof (cb_join1E _ buf (Z.to_nat (cap + 1)) bs (Z.to_nat k) (Z_to_bv 8 0) TX1 ltac:(rewrite Z2Nat.id by lia; exact TX23) ltac:(lia) ltac:(lia)) as TXT'.
      clear TX1 TX23.
      rewrite (zx32_litE clen) in C384 by lia.
      pose proof (pinv_stepX eshadow eq_refl q' m _ _ INV0 MU WM MI HWX) as INV1.
      eapply evt_mono.
      - eapply (retireE 0x8a350 q' 0 (fun mm => munch (((buf + k, buf + k + 1) :: blk2W) ++ pWE) m mm /\ wmono asegs m mm
                  /\ rw_cells asegs mm (P + 264) [C8 (wz 0)]
                  /\ rw_cells asegs mm (P + 384) [C8 (wz (buf + esp)); C8 (wz clen); C8 (wz buf); C8 (wz mlen)]
                  /\ rw_cells asegs mm (P + 448) [C4 (wz 4)] /\ rw_cells asegs mm (P + 456) [C4 (wz clen)]
                  /\ rw_cells asegs mm (P + 472) [C8 (wz esp)]
                  /\ rw_cells asegs mm buf [CB (Z.to_nat (cap + 1)) (set_byte bs (Z.to_nat k) (Z_to_bv 8 0))]));
          [right; right; right; right; left; reflexivity| exact INV1| |].
        + split; [eapply munch_weaken; [| exact MU]; intros xx OO; unfold blk2W, pWE in *; cbn [app outside] in *; clear - OO; tauto|].
          split; [exact WM|]. split; [exact C264|]. split; [exact C384|]. split; [exact C448|]. split; [exact C456|]. split; [exact C472| exact TXT'].
        + intros mA mB (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) MUx WMx.
          split; [eapply munch_trans; [exact H1|]; eapply munch_weaken; [| exact MUx]; intros xx OO; unfold blk2W, pWE in *; cbn [app outside] in *; clear - OO; tauto|].
          split; [exact (wmono_trans _ _ _ _ H2 WMx)|].
          split; [apply (fun A B => pobj_rframe (P + 264) _ A B mA mB H3 MUx WMx); [lia| simpl_sizes; lia]|].
          split; [apply (fun A B => pobj_rframe (P + 384) _ A B mA mB H4 MUx WMx); [lia| simpl_sizes; lia]|].
          split; [apply (fun A B => pobj_rframe (P + 448) _ A B mA mB H5 MUx WMx); [lia| simpl_sizes; lia]|].
          split; [apply (fun A B => pobj_rframe (P + 456) _ A B mA mB H6 MUx WMx); [lia| simpl_sizes; lia]|].
          split; [apply (fun A B => pobj_rframe (P + 472) _ A B mA mB H7 MUx WMx); [lia| simpl_sizes; lia]|].
          apply (fun A B => xobj_rframe buf _ (cap + 1) A B mA mB H8 MUx WMx); [cbn [cells_size csize]; lia| exact OX].
      - apply epostA_mono. intros m' r' ((H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) & ->).
        split; [exact H2|]. split; [exact H3|]. split; [exact H6|]. split; [exact H7|].
        right. split; [reflexivity|]. split; [lia|]. split; [exact H4|]. split; [exact H5|].
        right. split; [exact LT|]. rewrite <- Hk0. split; [exact H1| exact H8]. }
    acc_chk 14 (buf + k) HACC kk SHRk Hk. clear HACC.
    destruct Hk as [-> | [G1 G2]].
    - step. step. lit_branch. apply CONT.
    - step. rewrite (sxb_small kk) by lia.
      step. if_cases G3; zify_cond G3; [| exfalso; lia].
      zstep.
      step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
      apply CONT.
  Qed.

  #[using="q lo m0 POK RF0"] Lemma eframe_facts :
    FSB FI + A0_FS_FRAMES <= F /\ F + 128 <= FSB FI + A0_FS_SIZE /\ F mod 64 = 0
    /\ FSB FI + 4096 <= FL /\ FL + 1 <= FSB FI + A0_FS_FRAMES
    /\ 8 * (SF - 2147450880) = F
    /\ sh (FSB FI) <= SF /\ SF + 16 <= sh (FSB FI) + A0_FS_SHSIZE
    /\ (P + 504 <= F \/ F + 128 <= P) /\ (P + 504 <= FL \/ FL + 1 <= P)
    /\ FSB FI + A0_FS_FRAMES <= P /\ P + 504 <= FSB FI + A0_FS_SIZE.
  Proof.
    pose proof POK as POK'. pokA POK'.
    destruct (new_frame_facts FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & FLO & FHI & FAL & FLLO & FLHI & APART).
    cbn [FB_of SB_of] in FHI, APART.
    pose proof (fsb_ok FI) as (B1 & B2 & B3 & B4 & B5).
    pose proof (lb_apart_frame _ _ _ F 128 _ _ PLB APART) as P1.
    pose proof (lb_apart_flag FI st m0 _ _ FL RF0 PLB FLLO FLHI) as P3.
    split; [exact FLO|]. split; [exact FHI|]. split; [exact FAL|]. split; [exact FLLO|]. split; [exact FLHI|].
    split; [unfold eSF, sh, SHADOW_OFF; clear - FAL; Z.div_mod_to_equations; lia|].
    split; [unfold eSF, sh, SHADOW_OFF; clear - FLO B4; Z.div_mod_to_equations; lia|].
    split; [unfold eSF, sh, SHADOW_OFF in *; clear - FHI FLO B4; Z.div_mod_to_equations; lia|].
    split; [exact P1|]. split; [exact P3|].
    destruct PLB as (g & Hg & G1 & G2). pose proof (live_num FI st m0 RF0) as LN. rewrite Forall_forall in LN.
    destruct (LN g Hg) as (L1 & L2 & _). clear - G1 G2 L1 L2. lia.
  Qed.

  Definition elive (stc : fsstate FI) : Prop :=
    lb (fs_live FI stc) F 128 /\ ls (fs_live FI stc) SF 16 /\ lf (fs_live FI stc) FL /\ lb (fs_live FI stc) P 504
    /\ (forall g, In g (fs_live FI st) -> In g (fs_live FI stc)).
  #[using="q lo m0 POK RF0"] Lemma elive_of : forall stc, fs_live FI stc = fs_newff FI st 1 :: fs_live FI st -> elive stc.
  Proof.
    intros stc LIVE1. pose proof POK as POK'. pokA POK'.
    destruct (new_frame_facts FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & _).
    assert (LSUB : forall g, In g (fs_live FI st) -> In g (fs_live FI stc)) by (intros g Hg; rewrite LIVE1; right; exact Hg).
    pose proof (lb_new _ _ _ LIVE1) as LVF. pose proof (ls_new _ _ _ LIVE1) as LVS. pose proof (lf_new _ _ _ LIVE1) as LVL.
    unfold ff_size, ff_shsize in LVF, LVS. rewrite FCLS in LVF, LVS. cbn [FB_of SB_of] in LVF, LVS.
    change (ff_addr (fs_newff FI st 1)) with F in LVF, LVS. change (ff_flag (fs_newff FI st 1)) with FL in LVL. change (sh F) with SF in LVS.
    split; [exact LVF|]. split; [exact LVS|]. split; [exact LVL|]. split; [exact (lb_mono _ _ _ _ PLB LSUB)| exact LSUB].
  Qed.
  #[using="Type"] Lemma pinv_rf : forall shd q' m, pinvS shd q' m -> exists stc, RFAKE FI stc m /\ fs_live FI stc = fs_newff FI st 1 :: fs_live FI st.
  Proof. intros shd q' m (_ & _ & _ & _ & _ & VR). destruct VR as (_ & _ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.

  Definition inFJ (iv : ivl) : Prop := F + 32 <= fst iv /\ fst iv <= snd iv /\ snd iv <= F + 120.
  Definition inER (iv : ivl) : Prop := 0x5e68c8 <= fst iv /\ fst iv <= snd iv /\ snd iv <= 0x5e68d0.

  Definition inW3 (iv : ivl) : Prop := inP iv \/ inFJ iv \/ inER iv \/ outX iv.
  #[using="Type"] Lemma dj_W3 : forall (W : list ivl) X n, Forall inW3 W ->
    (X + n <= P \/ P + 504 <= X) -> (X + n <= F + 32 \/ F + 120 <= X) -> (X + n <= 0x5e68c8 \/ 0x5e68d0 <= X) -> clsX X n -> disjoint_from W X n.
  Proof.
    induction W as [|[a b] W IH]; intros X n HW H1 H2 H3 H4; cbn [disjoint_from]; [exact I|].
    inversion HW as [|? ? HO HW']; subst. split; [| exact (IH X n HW' H1 H2 H3 H4)].
    unfold inW3, inP, inFJ, inER, outX, clsX in *. cbn [fst snd] in HO.
    destruct HO as [HO|[HO|[HO|HO]]]; [clear - HO H1| clear - HO H2| clear - HO H3| clear - HO H4]; lia.
  Qed.
  #[using="q lo m0 POK RF0"] Lemma app_W3 : forall (W : list ivl), Forall inW3 W -> app_ivs W.
  Proof.
    intros W HW. pose proof (fsb_ok FI) as (B1 & B2 & _ & _ & B5).
    destruct eframe_facts as (FLO & FHI & _ & _ & _ & _ & _ & _ & _ & _ & PF1 & PF2).
    eapply Forall_impl; [| exact HW]. intros [x y] HO. unfold inW3, inP, inFJ, inER, outX in HO. cbn [fst snd] in HO.
    unfold app_iv, SH_HI. cbn [fst snd].
    destruct HO as [HO|[HO|[HO|HO]]]; [clear - HO B1 B2 B5 PF1 PF2| clear - HO B1 B2 B5 FLO FHI| clear - HO| clear - HO]; lia.
  Qed.
  #[using="q m0 POK RF0"] Lemma fsw_W3 : forall (W : list ivl) q', Forall inW3 W -> Forall (fsw_iv FI) ((lo, q') :: FSIV W).
  Proof.
    intros W q' HW. pose proof POK as POK'. pokA POK'.
    apply fsw_cons_app; [apply app_iv_stack; exact CLO|]. apply fsw_FSIV. exact (app_W3 W HW).
  Qed.
  #[using="q lo m0 POK RF0"] Lemma out_W3 : forall (W : list ivl), Forall inW3 W -> forall a, sh (FSB FI) <= a < sh (FSB FI) + A0_FS_SHSIZE -> outside W a.
  Proof.
    intros W HW a Ha. pose proof (fsb_ok FI) as (B1 & B2 & _). pose proof (fs_shadow_apart FI) as AP.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct eframe_facts as (FLO & FHI & _ & _ & _ & _ & _ & _ & _ & _ & PF1 & PF2).
    assert (SH2 : 0x7fff8000 <= sh (FSB FI) /\ sh (FSB FI) + A0_FS_SHSIZE <= 0x10007fff8000).
    { unfold sh, SHADOW_OFF. clear - B1 B2 ACR. Z.div_mod_to_equations. lia. }
    induction W as [|[x y] W IH]; cbn [outside]; [exact I|]. inversion HW as [|? ? HO HW']; subst. split; [| exact (IH HW')].
    unfold inW3, inP, inFJ, inER, outX in HO. cbn [fst snd] in HO.
    destruct HO as [HO|[HO|[HO|HO]]]; [clear - HO Ha AP PF1 PF2| clear - HO Ha AP FLO FHI| clear - HO Ha SH2| clear - HO Ha SH2]; lia.
  Qed.

  #[using="m0 POK RF0"] Lemma pinv_stepF : forall shd, Z.of_nat (cells_size shd) = 16 -> forall (W : list ivl) q' m m' stc st',
    pinvS shd q' m -> fs_live FI stc = fs_newff FI st 1 :: fs_live FI st ->
    munch ((lo, q') :: FSIV W) m m' -> wmono asegs m m' -> fkeep FI W stc m m' ->
    fs_live FI st' = fs_live FI stc -> RFAKE FI st' m' ->
    stk asegs m' lo q' -> mem_inv asegs m' -> asan_env asegs m' ->
    Forall inW3 W ->
    (exists j, rw_cells asegs m' (F + 32) [CB 88 j]) ->
    pinvS shd q' m'.
  Proof.
    intros shd HSZ W q' m m' stc st' (ST & (j0 & j160 & QC) & MI & AE & (QB & QAL) & VR) LIVE1 MUF WMF FKc LIVE' RF' ST' MI' AE' HW FT1'.
    destruct VR as (Hq & GAP & FRhi & (w0 & FH) & _ & FT2 & SHF & FLG & _).
    pose proof POK as POK'. pokA POK'.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (B1 & B2 & _ & B4 & B5). pose proof (fs_shadow_apart FI) as FSAP.
    destruct eframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & PAF & PAFL & PF1 & PF2).
    destruct (elive_of stc LIVE1) as (LVF & LVS & LVL & LVP & LSUB).
    assert (SH2 : 0x7fff8000 <= sh (FSB FI) /\ sh (FSB FI) + A0_FS_SHSIZE <= 0x10007fff8000).
    { unfold sh, SHADOW_OFF. clear - B1 B2 ACR. Z.div_mod_to_equations. lia. }
    assert (PSH : P + 504 <= SF \/ SF + 16 <= P) by (pose proof (lb_apart_shadow FI st m0 _ _ SF 16 RF0 PLB ltac:(lia) ltac:(lia)); lia).

    assert (DJS : forall a n, q' <= a -> 0 <= n -> disjoint_from ((lo, q') :: FSIV W) a n).
    { intros a n Ha Hn. cbn [disjoint_from]. split; [right; exact Ha|]. split; [right; clear - Ha QB LO CLO B2; lia|].
      split; [right; clear - Ha QB LO CLO SH2 ACR; lia|].
      apply dj_W3; [exact HW| right; clear - Ha QB LO CLO PHI; lia| right; clear - Ha QB LO CLO FHI B2; lia| right; clear - Ha QB LO CLO ACR; lia| left; clear - Ha QB LO CLO; lia]. }

    assert (DJF : forall a n, 0 <= n -> (F <= a /\ a + n <= F + 32) \/ (F + 120 <= a /\ a + n <= F + 128) \/ (SF <= a /\ a + n <= SF + 16) \/ (a = FL /\ n = 1) ->
                  disjoint_from W a n).
    { intros a n Hn HP. apply dj_W3; [exact HW| | | |].
      - clear - HP PAF PSH PAFL. lia.
      - clear - HP FLO FHI SHF1 SHF2 FSAP FLLO FLHI Hn. lia.
      - clear - HP FLO FLLO SHF1 SH2 B1 Hn. lia.
      - unfold clsX. clear - HP FLO FHI FLLO FLHI SHF1 SHF2 SH2 Hn. lia. }
    unfold pinvS, prestS.
    split; [exact ST'|].
    split; [exists j0, j160; eapply rw_cells_transport; [exact QC| exact MUF| exact WMF| apply DJS; [lia| simpl_sizes; lia]]|].
    split; [exact MI'|]. split; [exact AE'|]. split; [exact (conj QB QAL)|].
    split; [exact Hq|].
    split; [eapply stk_transport_disjoint; [exact GAP| exact MUF| exact WMF| apply DJS; clear - QB; lia]|].
    split; [eapply rw_cells_transport; [exact FRhi| exact MUF| exact WMF| apply DJS; [clear - QB; lia| simpl_sizes; lia]]|].
    split; [exists w0; eapply (rw_cells_fkeep FI W stc); [exact FH| exact FKc| exact WMF| left; apply (Contracts.lb_sub _ _ _ _ _ LVF); simpl_sizes; lia| apply DJF; [simpl_sizes; lia| left; simpl_sizes; lia]]|].
    split; [exact FT1'|].
    split; [eapply (rw_cells_fkeep FI W stc); [exact FT2| exact FKc| exact WMF| left; apply (Contracts.lb_sub _ _ _ _ _ LVF); simpl_sizes; lia| apply DJF; [simpl_sizes; lia| right; left; simpl_sizes; lia]]|].
    split; [eapply (rw_cells_fkeep FI W stc); [exact SHF| exact FKc| exact WMF| right; left; apply (Contracts.ls_sub _ _ _ _ _ LVS); rewrite ?HSZ; lia| apply DJF; [rewrite ?HSZ; lia| right; right; left; rewrite ?HSZ; lia]]|].
    split; [eapply (rw_cells_fkeep FI W stc); [exact FLG| exact FKc| exact WMF| right; right; split; [exact LVL| simpl_sizes; lia]| apply DJF; [simpl_sizes; lia| right; right; right; simpl_sizes; lia]]|].
    exists st'. split; [exact RF'| rewrite LIVE'; exact LIVE1].
  Qed.

  #[using="Type"] Lemma fj_split : forall m j, rw_cells asegs m (F + 32) [CB 88 j] ->
    exists pa pb j1 pv j2, rw_cells asegs m (F + 32) [C8 pa; C8 pb] /\ rw_cells asegs m (F + 48) [CB 16 j1]
                           /\ rw_cells asegs m (F + 64) [C4 pv] /\ rw_cells asegs m (F + 68) [CB 52 j2].
  Proof.
    intros m j FR.
    splitcb FR 0%nat [8; 8; 16; 4; 52]%nat. recell FR 0%nat. recell FR 1%nat. recell FR 3%nat. name_junk FR.
    split_chunk FR 2%nat H1 H2. split_chunk H2 1%nat H3 H4. split_chunk H4 1%nat H5 H6.
    do 5 eexists. split; [exact H1|]. split; [exact H3|]. split; [exact H5| exact H6].
  Qed.
  #[using="Type"] Lemma fj_join : forall m pa pb j1 pv j2, rw_cells asegs m (F + 32) [C8 pa; C8 pb] -> rw_cells asegs m (F + 48) [CB 16 j1] ->
    rw_cells asegs m (F + 64) [C4 pv] -> rw_cells asegs m (F + 68) [CB 52 j2] -> exists j, rw_cells asegs m (F + 32) [CB 88 j].
  Proof.
    intros m pa pb j1 pv j2 H1 H2 H3 H4.
    join_chunks H3 H4 H34. join_chunks H2 H34 H234. join_chunks H1 H234 HA.
    pose proof (rw_cells_merge asegs m (F + 32) [] [C8 pa; C8 pb; CB 16 j1; C4 pv; CB 52 j2] [] HA) as M.
    eexists. exact M.
  Qed.

  #[using="q lo P m0 POK RF0"] Lemma eouts_shw : forall m, rw_cells asegs m SF eshadowU -> shw m (F + 32) 16 /\ shw m (F + 64) 4.
  Proof.
    intros m SHF. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct eframe_facts as (FLO & FHI & FAL & _). pose proof (fsb_ok FI) as (B1 & B2 & _ & _ & B5).
    assert (F8 : F mod 8 = 0) by (clear - FAL; Z.div_mod_to_equations; lia).
    unfold eshadowU in SHF.
    change [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
            C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
            C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243);
            C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
      with (shadow_cells [241; 241; 241; 241; 0; 0; 242; 242; 4; 243; 243; 243; 0; 0; 0; 0]) in SHF.
    split.
    - split; [| split].
      + eapply (accessible_of_chunk m F _ (F + 32) 16 SHF F8); [lia| cbn [length]; lia|].
        intros i Hi H1 H2. cbn [length] in Hi. assert (Ei : i = 4%nat \/ i = 5%nat) by lia. destruct Ei as [-> | ->]; reflexivity.
      + eapply (sh_readable_of_chunk m F _ (F + 32) 16 SHF); cbn [length]; unfold sh, SHADOW_OFF; clear - FAL; Z.div_mod_to_equations; lia.
      + unfold win_ok. split; [lia|]. clear - FLO FHI B1 B2 B5 ACR. change (2^47) with 140737488355328. lia.
    - split; [| split].
      + intros a Ha. assert (E : (a - F) / 8 = 8) by (clear - Ha; Z.div_mod_to_equations; lia).
        eapply (acc_of_chunk m F _ a SHF F8); [lia| rewrite E; change (Z.to_nat 8) with 8%nat; cbn [length]; lia|].
        rewrite E. change (Z.to_nat 8) with 8%nat. cbn [nth]. right. split; [lia|]. clear - Ha F8. Z.div_mod_to_equations. lia.
      + eapply (sh_readable_of_chunk m F _ (F + 64) 4 SHF); cbn [length]; unfold sh, SHADOW_OFF; clear - FAL; Z.div_mod_to_equations; lia.
      + unfold win_ok. split; [lia|]. clear - FLO FHI B1 B2 B5 ACR. change (2^47) with 140737488355328. lia.
  Qed.

  Definition txt_okA (A len cap : Z) : Prop :=
    0x609000 <= A /\ A + (cap + 1) + 16 <= alloc_ceiling /\ 0 <= len <= cap /\ A mod 16 = 0
    /\ (A + (cap + 1) <= FSB FI \/ FSB FI + A0_FS_SIZE <= A)
    /\ (A + (cap + 1) + 16 <= 0x7fff7000 \/ 0x10007fff8000 <= A)
    /\ cap + 1 <= 2^40.
  Ltac tokA V := destruct V as (ALO & AHI & LENC & AAL & TFS & TBAND & CAPB).

  Variable canary : word.
  Definition pctx (A len cap cur : Z) (bs : list byte) (m : mem) : Prop :=
    rw_cells asegs m (P + 480) [C8 (wz (P + 400)); C8 (wz cur); C4 (wz 0)]
    /\ rw_cells asegs m (P + 400) (mbuf_cells A len cap)
    /\ rw_cells asegs m A [CB (Z.to_nat (cap + 1)) bs]
    /\ shw m P 504 /\ shw m A (cap + 1) /\ shw m SEPTAB_A 20 /\ shw m FMT_CHUNK_A 7 /\ shw m FMT_CRLF_A 3
    /\ shz m (sh lo) (sh q) /\ shr m (sh lo - sh lo mod 8) (sh q + 8)
    /\ (exists ev, clow canary ev m) /\ shw m ERRNO_A 4.

  #[using="Type"] Lemma dj_low : forall (W : list ivl) X n, Forall (fun iv => 0x609000 <= fst iv) W -> X + n <= 0x609000 -> disjoint_from W X n.
  Proof.
    induction W as [|[a b] W IH]; intros X n HW HX; cbn [disjoint_from]; [exact I|].
    inversion HW as [|? ? HO HW']; subst. cbn [fst snd] in HO. split; [left; lia| exact (IH X n HW' HX)].
  Qed.
  #[using="Type"] Lemma clow_stepW : forall (W : list ivl) ev m m', clow canary ev m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv => 0x609000 <= fst iv) W -> clow canary ev m'.
  Proof.
    intros W ev m m' (C1' & C2' & C3') MU WM HW. unfold clow, A0_got_ssp, A0_ssp_guard in *.
    split; [| split]; (eapply rw_cells_transport; [eassumption| exact MU| exact WM| apply dj_low; [exact HW| simpl_sizes; lia]]).
  Qed.
  #[using="q st POK"] Lemma low_fsW : forall (W : list ivl) q', Forall inP W -> Forall (fun iv : ivl => 0x609000 <= fst iv) ((lo, q') :: FSIV W).
  Proof.
    intros W q' HW. pose proof POK as POK'. pokA POK'. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (B1 & B2 & _).
    constructor; [cbn [fst]; clear - CLO ACR; lia|]. constructor; [cbn [fst]; exact B1|].
    constructor; [cbn [fst]; unfold sh, SHADOW_OFF; clear - B1; Z.div_mod_to_equations; lia|].
    eapply Forall_impl; [| exact HW]. intros [x y] (H1 & _). cbn [fst] in *. clear - H1 PLO. lia.
  Qed.

  #[using="Type"] Lemma text_bytesE : forall m A cap bs, rw_cells asegs m A [CB (Z.to_nat (cap + 1)) bs] -> 0 <= cap ->
    bytes_at asegs m A bs /\ Z.of_nat (length bs) = cap + 1.
  Proof.
    intros m A cap bs TXT HC'. pose proof TXT as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
    destruct TXT as [[W _] _]. cbn in W. destruct W as [W _]. split; [exact B| lia].
  Qed.

  #[using="m0 POK RF0"] Lemma pctx_stepF : forall (W : list ivl) q' A len cap cur cur' bs m m' stc,
    pctx A len cap cur bs m -> txt_okA A len cap -> q + -304 <= q' <= q + -288 ->
    RFAKE FI stc m -> fs_live FI stc = fs_newff FI st 1 :: fs_live FI st ->
    munch ((lo, q') :: FSIV W) m m' -> wmono asegs m m' -> fkeep FI W stc m m' ->
    Forall inW3 W -> disjoint_from W (P + 400) 32 -> disjoint_from W A (cap + 1) ->
    rw_cells asegs m' (P + 480) [C8 (wz (P + 400)); C8 (wz cur'); C4 (wz 0)] ->
    (exists ev', clow canary ev' m') ->
    pctx A len cap cur' bs m'.
  Proof.
    intros W q' A len cap cur cur' bs m m' stc (SC & MBC & TXT & SHP & SHA & SHSEP & SHF1 & SHF2 & SHZ & SHR & _ & SHE) TOK QB RF LIVE1 MUF WMF FKc HW DJM DJT SC' CLOW'.
    tokA TOK. pose proof POK as POK'. pokA POK'.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (B1 & B2 & _ & B4 & B5).
    destruct eframe_facts as (FLO & FHI & _ & _ & _ & _ & _ & _ & _ & _ & PF1 & PF2).
    destruct (elive_of stc LIVE1) as (LVF & LVS & LVL & LVP & LSUB).
    pose proof (fsw_W3 W q' HW) as FW.
    assert (SH2 : 0x7fff8000 <= sh (FSB FI) /\ sh (FSB FI) + A0_FS_SHSIZE <= 0x10007fff8000).
    { unfold sh, SHADOW_OFF. clear - B1 B2 ACR. Z.div_mod_to_equations. lia. }
    unfold pctx.
    split; [exact SC'|].
    split; [eapply (rw_cells_fkeep FI W stc); [exact MBC| exact FKc| exact WMF| left; apply (Contracts.lb_sub _ _ _ _ _ LVP); unfold mbuf_cells; simpl_sizes; lia| unfold mbuf_cells; simpl_sizes; exact DJM]|].
    split.
    { eapply rw_cells_transport; [exact TXT| exact MUF| exact WMF|]. cbn [disjoint_from cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia.
      split; [left; clear - AHI CLO; lia|]. split; [clear - TFS; lia|]. split; [clear - TBAND SH2; lia|]. exact DJT. }
    split; [exact (shw_fkeep FI W stc m m' P 504 SHP FKc RF LVP (out_W3 W HW))|].
    split; [exact (shw_frame_fs FI _ m m' A (cap + 1) SHA MUF FW TFS)|].
    split; [apply (shw_frame_fs FI _ m m' SEPTAB_A 20 SHSEP MUF FW); left; unfold SEPTAB_A; clear - B1; lia|].
    split; [apply (shw_frame_fs FI _ m m' FMT_CHUNK_A 7 SHF1 MUF FW); left; clear - B1; lia|].
    split; [apply (shw_frame_fs FI _ m m' FMT_CRLF_A 3 SHF2 MUF FW); left; clear - B1; lia|].
    split; [exact (shz_stack_fs FI _ m m' lo _ _ SHZ CLO (stack_lo_ok lo) (sh_hi_ok q ltac:(clear - QHI; lia)) MUF FW)|].
    split; [exact (shr_stack_fs FI _ m m' lo _ _ SHR CLO ltac:(lia) (sh_hi_ok8 q ltac:(clear - QHI; lia)) MUF FW)|].
    split; [exact CLOW'|]. apply (shw_frame_fs FI _ m m' ERRNO_A 4 SHE MUF FW); left; clear - B1; lia.
  Qed.

  #[using="st m0 POK RF0"] Lemma pctx_stepP : forall (W : list ivl) A len cap cur cur' bs m m',
    pctx A len cap cur bs m -> txt_okA A len cap -> munch W m m' -> wmono asegs m m' -> Forall inP W ->
    disjoint_from W (P + 400) 32 ->
    rw_cells asegs m' (P + 480) [C8 (wz (P + 400)); C8 (wz cur'); C4 (wz 0)] ->
    pctx A len cap cur' bs m'.
  Proof.
    intros W A len cap cur cur' bs m m' (_ & MBC & TXT & SHP & SHA & SHSEP & SHF1 & SHF2 & SHZ & SHR & (ev & CLOW) & SHE) TOK MU WM HW DJM SC'.
    tokA TOK. pose proof POK as POK'. pokA POK'.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (B1 & B2 & _ & B4 & B5).
    destruct eframe_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PF1 & PF2).
    assert (AW : app_ivs W).
    { eapply Forall_impl; [| exact HW]. intros [x y] (H1 & H2 & H3). cbn [fst snd] in *. unfold app_iv, SH_HI. cbn [fst snd]. clear - H1 H2 H3 PF1 PF2 B1 B2 B5. lia. }
    unfold pctx.
    split; [exact SC'|].
    split; [eapply rw_cells_transport; [exact MBC| exact MU| exact WM| unfold mbuf_cells; simpl_sizes; exact DJM]|].
    split; [eapply rw_cells_transport; [exact TXT| exact MU| exact WM| apply dj_inP; [exact HW| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; clear - TFS PF1 PF2; lia]]|].
    split; [exact (shw_frame _ _ _ _ _ SHP MU AW)|]. split; [exact (shw_frame _ _ _ _ _ SHA MU AW)|].
    split; [exact (shw_frame _ _ _ _ _ SHSEP MU AW)|]. split; [exact (shw_frame _ _ _ _ _ SHF1 MU AW)|]. split; [exact (shw_frame _ _ _ _ _ SHF2 MU AW)|].
    assert (FW : Forall (fsw_iv FI) W) by (eapply Forall_impl; [| exact AW]; intros iv H; left; exact H).
    split; [exact (shz_stack_fs FI _ m m' lo _ _ SHZ CLO (stack_lo_ok lo) (sh_hi_ok q ltac:(clear - QHI; lia)) MU FW)|].
    split; [exact (shr_stack_fs FI _ m m' lo _ _ SHR CLO ltac:(lia) (sh_hi_ok8 q ltac:(clear - QHI; lia)) MU FW)|].
    split; [exists ev; apply (clow_stepW W ev m m' CLOW MU WM); eapply Forall_impl; [| exact HW]; intros [x y] (H1 & _); cbn [fst] in *; clear - H1 PLO; lia|].
    exact (shw_frame _ _ _ _ _ SHE MU AW).
  Qed.

  #[using="Type"] Lemma dj_FJER : forall (Wx : list ivl) X n, Forall (fun iv => inFJ iv \/ inER iv) Wx ->
    (X + n <= F + 32 \/ F + 120 <= X) -> (X + n <= 0x5e68c8 \/ 0x5e68d0 <= X) -> disjoint_from Wx X n.
  Proof.
    induction Wx as [|[a b] Wx IH]; intros X n HW H2 H3; cbn [disjoint_from]; [exact I|].
    inversion HW as [|? ? HO HW']; subst. split; [| exact (IH X n HW' H2 H3)].
    unfold inFJ, inER in HO. cbn [fst snd] in HO. clear - HO H2 H3. lia.
  Qed.
  #[using="m0 POK RF0"] Lemma evf_ok : forall q' A len cap cur (bs : list byte) stc (Wx : list ivl),
    elive stc -> q + -304 <= q' <= q + -288 -> q' mod 16 = 0 -> txt_okA A len cap -> Z.of_nat (length bs) = cap + 1 -> 0 <= cur <= len ->
    Forall (fun iv => inFJ iv \/ inER iv) Wx ->
    vf_okA FI q' lo (P + 480) (P + 400) A len cap cur bs stc Wx.
  Proof.
    intros q' A len cap cur bs stc Wx (LVF & LVS & LVL & LVP & LSUB) QB QAL TOK BL CR HWx.
    tokA TOK. pose proof POK as POK'. pokA POK'. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (B1 & B2 & _).
    destruct eframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & PAF & PAFL & PF1 & PF2).
    unfold vf_okA. rewrite BL.
    split; [exact CLO|]. split; [clear - LO QB; lia|]. split; [exact QAL|]. split; [change (2^47) with 140737488355328 in *; clear - QB QHI; lia|].
    split; [clear - PLO; lia|]. split; [clear; lia|]. split; [clear - PHI; lia|]. split; [clear - PAL; Z.div_mod_to_equations; lia|]. split; [clear - PAL; Z.div_mod_to_equations; lia|].
    split; [apply (Contracts.lb_sub _ _ _ _ _ LVP); clear; lia|].
    split; [clear - ALO; lia|]. split; [clear - AHI; lia|]. split; [clear - LENC; lia|]. split; [clear - LENC; lia|].
    split; [change (2^63) with 9223372036854775808; clear - AHI ACR; lia|].
    split; [exact CR|].
    split; [clear - TFS PF1 PF2; lia|]. split; [exact TFS|]. split; [clear - TBAND; lia|].
    split.
    { eapply Forall_impl; [| exact HWx]. intros [x y] [(H1 & H2 & H3)|(H1 & H2 & H3)]; cbn [fst snd] in *.
      - split; [exact H2|]. left. apply (Contracts.lb_sub _ _ _ _ _ LVF); clear - H1 H2 H3; lia.
      - split; [exact H2|]. right. clear - H1 H3. lia. }
    split; [apply dj_FJER; [exact HWx| clear - TFS FLO FHI; lia| right; clear - ALO; lia]|].
    apply dj_FJER; [exact HWx| clear - PAF; lia| right; clear - PLO; lia].
  Qed.

  Definition pregsG (q' : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x26 x28 x29 x30 x31 : word) : bvmap 5 word :=
    mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') x10 x11 x12 x13 x14 x15 x16 x17
        x18 x19 x20 (wz (P + 464)) (wz (P + 488)) (wz (eSH (P + 464))) (wz (eSH (P + 488)))
        (wz (P + 452)) x26 (wz SF) x28 x29 x30 x31.
  Definition ajcallstE (pc ra' q' : Z) (a0 a1 a2 : word) x5 x6 x7 x13 x14 x15 x16 x17 x18 x19 x20 x26 x28 x29 x30 x31 (m : mem) : machine_state :=
    MS (pregsG q' (wz ra') x5 x6 x7 a0 a1 a2 x13 x14 x15 x16 x17 x18 x19 x20 x26 x28 x29 x30 x31) F_ (wz pc) fc None m (seg_rom asegs).
  Definition ajretstE (pc q' : Z) (a0 : word) x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x26 x28 x29 x30 x31 (m : mem) : machine_state :=
    MS (pregsG q' (wz pc) x5 x6 x7 a0 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x26 x28 x29 x30 x31) F_ (wz pc) fc None m (seg_rom asegs).
  Notation S2V := (wz (eSH (P + 452))).  Notation S3V := (wz PE_JT_A).

  Notation GMAX_GOT_A := 0xaad50%Z.
  Notation GMAX_A := 0xaea60%Z.
  Definition pstatE (gmax : Z) (m : mem) : Prop :=
    rw_cells asegs m GMAX_GOT_A [C8 (wz GMAX_A)] /\ rw_cells asegs m GMAX_A [C8 (wz gmax)] /\ shw m GMAX_A 8
    /\ rw_cells asegs m INITWASCALLED_A [C1 (Z_to_bv 8 0)].
  Definition hiER (iv : ivl) : Prop := 0x609000 <= fst iv \/ inER iv.
  #[using="Type"] Lemma dj_hiER : forall (W : list ivl) X n, Forall hiER W -> X + n <= 0x5e68c8 -> disjoint_from W X n.
  Proof.
    induction W as [|[a b] W IH]; intros X n HW HX; cbn [disjoint_from]; [exact I|].
    inversion HW as [|? ? HO HW']; subst. unfold hiER, inER in HO. cbn [fst snd] in HO. split; [left; clear - HO HX; lia| exact (IH X n HW' HX)].
  Qed.
  #[using="Type"] Lemma pstat_stepW : forall (W : list ivl) gmax m m', pstatE gmax m -> munch W m m' -> wmono asegs m m' -> Forall hiER W -> app_ivs W ->
    pstatE gmax m'.
  Proof.
    intros W gmax m m' (G1 & G2 & G3 & G4) MU WM HW AW. unfold pstatE.
    split; [eapply rw_cells_transport; [exact G1| exact MU| exact WM| apply dj_hiER; [exact HW| simpl_sizes; lia]]|].
    split; [eapply rw_cells_transport; [exact G2| exact MU| exact WM| apply dj_hiER; [exact HW| simpl_sizes; lia]]|].
    split; [exact (shw_frame _ _ _ _ _ G3 MU AW)|].
    eapply rw_cells_transport; [exact G4| exact MU| exact WM| apply dj_hiER; [exact HW| simpl_sizes; lia]].
  Qed.
  #[using="q m0 POK RF0"] Lemma hiER_fsW3 : forall (W : list ivl) q', Forall inW3 W -> Forall hiER ((lo, q') :: FSIV W).
  Proof.
    intros W q' HW. pose proof POK as POK'. pokA POK'. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (B1 & B2 & _).
    destruct eframe_facts as (FLO & _).
    constructor; [left; cbn [fst]; clear - CLO ACR; lia|]. constructor; [left; cbn [fst]; exact B1|].
    constructor; [left; cbn [fst]; unfold sh, SHADOW_OFF; clear - B1; Z.div_mod_to_equations; lia|].
    eapply Forall_impl; [| exact HW]. intros [x y] HO. unfold inW3, inP, inFJ, outX in HO. unfold hiER. cbn [fst snd] in *.
    destruct HO as [HO|[HO|[HO|HO]]]; [left; clear - HO PLO; lia| left; clear - HO FLO B1; lia| right; exact HO| left; clear - HO; lia].
  Qed.

  #[using="Type"] Lemma blk1aE : forall (q' : Z) x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    pscr q' m -> mem_inv asegs m ->
    evt asegs Q (ajcallstE 0x89068 0x89bf8 q' (wz P) (wz 5) x12 x5 x6 (wz 2147450880) x13 x14 x15 x16 x17 S2V S3V (wz (P + 392)) (wz 3) x28 x29 x30 x31 m) ->
    evt asegs Q (blkstA q' 0x89bf0 x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m).
  Proof.
    intros q' x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m Q (j0 & j160 & QC) MI K.
    unfold blkstA, pregs, ajcallstE, pregsG, eSH in *.
    step. step. exact K.
  Qed.
  #[using="Type"] Lemma blk1bE : forall (q' r : Z) x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    pscr q' m -> mem_inv asegs m ->
    evt asegs Q (loopstA q' r (wz 0x89bf8) x5 x6 (wz r) x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m) ->
    evt asegs Q (ajretstE 0x89bf8 q' (wz r) x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 S2V S3V (wz (P + 392)) x26 x28 x29 x30 x31 m).
  Proof.
    intros q' r x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 x30 x31 m Q (j0 & j160 & QC) MI K.
    unfold ajretstE, pregsG, loopstA, pregs, eSH in *.
    step. zstep. exact K.
  Qed.

  #[using="lo POK"] Lemma blk6aE : forall (q' cur : Z) x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    pscr q' m -> mem_inv asegs m -> shw m P 504 ->
    rw_cells asegs m (P + 480) [C8 (wz (P + 400)); C8 (wz cur); C4 (wz 0)] ->
    evt asegs Q (ajcallstE 0x88134 0x8a000 q' (wz P) (wz 5) x12 x5 x6 (wz 2147450880) x13 x14 x15 x16 x17 S2V S3V (wz cur) (wz 3) x28 x29 x30 x31 m) ->
    evt asegs Q (blkstA q' 0x89fec x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m).
  Proof.
    intros q' cur x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m Q (j0 & j160 & QC) MI SHP SC K.
    pose proof POK as POK'. pokA POK'. clear PLB.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    unfold blkstA, pregs, ajcallstE, pregsG, eSH in *.
    walk_lia_to 0x89ffc. step. exact K.
  Qed.

  #[using="lo POK"] Lemma blk6bE : forall (q' r cur0 cur' : Z) (wpos : word) x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    pscr q' m -> q + -304 <= q' <= q + -288 -> mem_inv asegs m -> shw m P 504 -> 0 <= r <= 5 -> 0 <= cur0 <= cur' -> cur' < 2^64 ->
    rw_cells asegs m (P + 448) [C4 wpos] ->
    rw_cells asegs m (P + 480) [C8 (wz (P + 400)); C8 (wz cur'); C4 (wz 0)] ->
    (r <> 4 -> forall y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y28 y29 y30 y31,
       evt asegs Q (exitstA q' r y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y28 y29 y30 y31 m)) ->
    (r = 4 -> forall m' y5 y6 y7 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       munch [(P + 448, P + 452)]%Z m m' -> wmono asegs m m' -> mem_inv asegs m' -> rw_cells asegs m' (P + 448) [C4 (wz 4)] ->
       evt asegs Q (ajcallstE 0x8c704 0x8a050 q' (wz (P + 400)) (wz cur0) (wz (cur' - cur0)) y5 y6 y7 y13 y14 y15 y16 y17
                              (wz P) (wz (P + 400)) (wz cur0) (wz 4) y28 y29 y30 y31 m')) ->
    evt asegs Q (ajretstE 0x8a000 q' (wz r) x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 S2V S3V (wz cur0) x26 x28 x29 x30 x31 m).
  Proof.
    intros q' r cur0 cur' wpos x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 x30 x31 m Q (j0 & j160 & QC) QB MI SHP RR CC CH C448 SC KX KD.
    pose proof POK as POK'. pokA POK'. clear PLB.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    unfold ajretstE, ajcallstE, pregsG, exitstA, eSH in *.
    pose proof (munch_refl [(P + 448, P + 452)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. zstep. step. step. if_cases KB; zify_cond KB.
    { apply KX. lia. }
    assert (r = 4) by lia. subst r.
    walk_lia_to 0x8a04c. step.
    eapply (KD eq_refl); try eassumption.
  Qed.

  Definition blk6cW : list ivl := [(P + 384, P + 392); (P + 488, P + 496)]%Z.
  #[using="m0 POK RF0"] Lemma blk6cE : forall (q' A len cap cur0 cur' esp : Z) (w384 : word) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m,
    pinv q' m -> shw m P 504 -> 0 <= esp < 2^64 -> 0 <= A < 2^63 -> 0 <= cur0 < 2^64 ->
    rw_cells asegs m (P + 384) [C8 w384] -> rw_cells asegs m (P + 400) (mbuf_cells A len cap) ->
    rw_cells asegs m (P + 472) [C8 (wz esp)] ->
    rw_cells asegs m (P + 480) [C8 (wz (P + 400)); C8 (wz cur'); C4 (wz 0)] ->
    evt asegs (epostA (fun m' r' =>
                 (munch (blk6cW ++ pWE) m m' /\ wmono asegs m m'
                  /\ rw_cells asegs m' (P + 384) [C8 (wz (A + esp))] /\ rw_cells asegs m' (P + 400) (mbuf_cells A len cap)
                  /\ rw_cells asegs m' (P + 472) [C8 (wz esp)]
                  /\ rw_cells asegs m' (P + 480) [C8 (wz (P + 400)); C8 (wz cur0); C4 (wz 0)]) /\ r' = 0))
      (ajretstE 0x8a050 q' x10 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 (wz P) (wz (P + 400)) (wz cur0) (wz 4) x28 x29 x30 x31 m).
  Proof.
    intros q' A len cap cur0 cur' esp w384 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m INV SHP ESR AR C0R C384 MBC C472 SC.
    pose proof INV as INV0. destruct INV as (_ & (j0 & j160 & QC) & MI & _ & (QB & _) & _).
    pose proof POK as POK'. pokA POK'. clear PLB.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    unfold ajretstE, pregsG, eSH, mbuf_cells, MEMBUF_DEF_SIZE_INC in *.
    pose proof (munch_refl blk6cW m) as MU. pose proof (wmono_refl asegs m) as WM. unfold blk6cW in MU.
    walk_lia_to 0x8a0a4.
    rewrite ?Z.mod_small in C384 by lia.
    assert (HW : Forall inP blk6cW) by (unfold blk6cW, inP; repeat constructor; cbn [fst snd]; lia).
    pose proof (pinv_stepP eshadow eq_refl q' m _ blk6cW INV0 MU WM MI HW) as INV1.
    eapply evt_mono.
    - eapply (retireE 0x8a0a4 q' 0 (fun mm => munch (blk6cW ++ pWE) m mm /\ wmono asegs m mm
                  /\ rw_cells asegs mm (P + 384) [C8 (wz (A + esp))] /\ rw_cells asegs mm (P + 400) (mbuf_cells A len cap)
                  /\ rw_cells asegs mm (P + 472) [C8 (wz esp)]
                  /\ rw_cells asegs mm (P + 480) [C8 (wz (P + 400)); C8 (wz cur0); C4 (wz 0)]));
        [right; right; left; reflexivity| exact INV1| |].
      + split; [eapply munch_weaken; [| exact MU]; intros xx OO; unfold blk6cW, pWE in *; cbn [app outside] in *; clear - OO; tauto|].
        split; [exact WM|]. split; [exact C384|]. split; [exact MBC|]. split; [exact C472| exact SC].
      + intros mA mB (H1 & H2 & H3 & H4 & H5 & H6) MUx WMx.
        split; [eapply munch_trans; [exact H1|]; eapply munch_weaken; [| exact MUx]; intros xx OO; unfold blk6cW, pWE in *; cbn [app outside] in *; clear - OO; tauto|].
        split; [exact (wmono_trans _ _ _ _ H2 WMx)|].
        split; [apply (fun A B => pobj_rframe (P + 384) _ A B mA mB H3 MUx WMx); [lia| simpl_sizes; lia]|].
        split; [apply (fun A B => pobj_rframe (P + 400) _ A B mA mB H4 MUx WMx); [lia| unfold mbuf_cells; simpl_sizes; lia]|].
        split; [apply (fun A B => pobj_rframe (P + 472) _ A B mA mB H5 MUx WMx); [lia| simpl_sizes; lia]|].
        apply (fun A B => pobj_rframe (P + 480) _ A B mA mB H6 MUx WMx); [lia| simpl_sizes; lia].
    - intros ms V. exact V.
  Qed.

  Definition blk3cW : list ivl := [(P + 392, P + 400); (P + 440, P + 444); (P + 452, P + 456); (P + 488, P + 496)]%Z.
  #[using="m0 POK RF0"] Lemma blk3cE : forall (q' A len cap cur0 cur' v esp err entp gmax : Z) (w392 : word) (bs : list byte)
      x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    pinvS eshadowU q' m -> pctx A len cap cur' bs m -> txt_okA A len cap -> pstatE gmax m -> 0 < gmax < 2^32 ->
    0 <= v < 2^31 -> 0 <= esp < 2^64 -> 0 <= cur0 < 2^64 ->
    rw_cells asegs m (P + 264) [C8 (wz 0)] -> rw_cells asegs m (P + 392) [C8 w392] ->
    rw_cells asegs m (P + 440) [C4 (wz err)] -> rw_cells asegs m (P + 452) [C4 (wz entp)] ->
    rw_cells asegs m (P + 464) [C8 (wz v)] -> rw_cells asegs m (P + 472) [C8 (wz esp)] ->
    (forall m' (r err' entp' : Z) (w392' : word) y1 y5 y6 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       pinvS eshadowU q' m' -> pctx A len cap cur0 bs m' -> pstatE gmax m' ->
       rw_cells asegs m' (P + 264) [C8 (wz 0)] -> rw_cells asegs m' (P + 392) [C8 w392'] ->
       rw_cells asegs m' (P + 440) [C4 (wz err')] -> rw_cells asegs m' (P + 452) [C4 (wz entp')] ->
       rw_cells asegs m' (P + 464) [C8 (wz v)] -> rw_cells asegs m' (P + 472) [C8 (wz esp)] ->
       munch blk3cW m m' -> wmono asegs m m' ->
       ( (v = 0 /\ r = 6 /\ entp' = 6 /\ w392' = wz (cur0 - esp) /\ err' = err)
         \/ (v <> 0 /\ gmax < v /\ r = 3 /\ entp' = entp /\ w392' = w392 /\ err' = 413)
         \/ (v <> 0 /\ v <= gmax /\ r = 6 /\ entp' = 5 /\ w392' = w392 /\ err' = err) ) ->
       evt asegs Q (MS (pregs q P st gp tp q' y1 y5 y6 y10 y11 y12 y13 y14 y15 y16 y17 (wz r) y28 y29 y30 y31) F_ (wz 0x89ecc) fc None m' (seg_rom asegs))) ->
    evt asegs Q (ajretstE 0x89ca4 q' x10 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 S2V S3V (wz cur0) (wz 4) x28 x29 x30 x31 m).
  Proof.
    intros q' A len cap cur0 cur' v esp err entp gmax w392 bs x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m Q
      INV CTX TOK PST GMX VR ESR C0R C264 C392 C440 C452 C464 C472 K.
    pose proof INV as INV0. destruct INV as (_ & (j0 & j160 & QC) & MI & _ & (QB & _) & _).
    pose proof CTX as CTX0. destruct CTX as (SC & _ & _ & SHP & _).
    pose proof PST as PST0. destruct PST as (G1 & G2 & G3 & _).
    pose proof POK as POK'. pokA POK'. clear PLB.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    unfold ajretstE, pregsG, pregs, eSH in *.
    pose proof (munch_refl blk3cW m) as MU. pose proof (wmono_refl asegs m) as WM. unfold blk3cW in MU.
    assert (HW : Forall inP blk3cW) by (unfold blk3cW, inP; repeat constructor; cbn [fst snd]; lia).
    assert (DJM : disjoint_from blk3cW (P + 400) 32) by (unfold blk3cW; cbn [disjoint_from]; repeat split; try exact I; lia).
    assert (FIN : forall m' (r err' entp' : Z) (w392' : word) y1 y5 y6 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       munch blk3cW m m' -> wmono asegs m m' -> mem_inv asegs m' ->
       rw_cells asegs m' (P + 480) [C8 (wz (P + 400)); C8 (wz cur0); C4 (wz 0)] ->
       rw_cells asegs m' (P + 264) [C8 (wz 0)] -> rw_cells asegs m' (P + 392) [C8 w392'] ->
       rw_cells asegs m' (P + 440) [C4 (wz err')] -> rw_cells asegs m' (P + 452) [C4 (wz entp')] ->
       rw_cells asegs m' (P + 464) [C8 (wz v)] -> rw_cells asegs m' (P + 472) [C8 (wz esp)] ->
       ( (v = 0 /\ r = 6 /\ entp' = 6 /\ w392' = wz (cur0 - esp) /\ err' = err)
         \/ (v <> 0 /\ gmax < v /\ r = 3 /\ entp' = entp /\ w392' = w392 /\ err' = 413)
         \/ (v <> 0 /\ v <= gmax /\ r = 6 /\ entp' = 5 /\ w392' = w392 /\ err' = err) ) ->
       evt asegs Q (MS (pregs q P st gp tp q' y1 y5 y6 y10 y11 y12 y13 y14 y15 y16 y17 (wz r) y28 y29 y30 y31) F_ (wz 0x89ecc) fc None m' (seg_rom asegs))).
    { intros m' r err' entp' w392' y1 y5 y6 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 MU' WM' MI' SC' D264 D392 D440 D452 D464 D472 CASES.
      apply (K m' r err' entp' w392'); try assumption.
      - exact (pinv_stepP eshadowU eq_refl q' m m' blk3cW INV0 MU' WM' MI' HW).
      - exact (pctx_stepP blk3cW A len cap cur' cur0 bs m m' CTX0 TOK MU' WM' HW DJM SC').
      - apply (pstat_stepW blk3cW gmax m m' PST0 MU' WM').
        + eapply Forall_impl; [| exact HW]. intros [x y] (H1 & _). left. cbn [fst] in *. lia.
        + pose proof (fsb_ok FI) as (B1 & B2 & _ & _ & B5). destruct eframe_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PF1 & PF2).
          eapply Forall_impl; [| exact HW]. intros [x y] (H1 & H2 & H3). cbn [fst snd] in *. unfold app_iv, SH_HI. cbn [fst snd]. clear - H1 H2 H3 PF1 PF2 B1 B2 B5. lia. }
    clear K INV0 CTX0 PST0.
    destruct (Z.eq_dec v 0) as [V0|V0].
    { subst v. walk_lia_to 0x89ecc. rewrite ?Z.mod_small in * by lia.
      unfold pregs, eSH in FIN. eapply (FIN _ 6 err 6 _); try eassumption. left. repeat split; reflexivity. }
    destruct (Z_lt_le_dec gmax v) as [GV|GV].
    { walk_lia_to 0x89ecc. chk0_auto 12 0xaea60. step. clear_shr. walk_lia_to 0x89ecc.
      replace (Z.land gmax 4294967295) with gmax by (change 4294967295 with (Z.ones 32); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity).
      if_cases KG; zify_cond KG; [exfalso; lia|].
      walk_lia_to 0x89ecc. rewrite ?Z.mod_small in * by lia.
      unfold pregs, eSH in FIN. eapply (FIN _ 3 413 entp w392); try eassumption. right; left. repeat split; try reflexivity; lia. }
    walk_lia_to 0x89ecc. chk0_auto 12 0xaea60. step. clear_shr. walk_lia_to 0x89ecc.
    replace (Z.land gmax 4294967295) with gmax by (change 4294967295 with (Z.ones 32); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity).
    if_cases KG; zify_cond KG; [| exfalso; lia].
    walk_lia_to 0x89ecc. rewrite ?Z.mod_small in * by lia.
    unfold pregs, eSH in FIN. eapply (FIN _ 6 err 5 w392); try eassumption. right; right. repeat split; try reflexivity; lia.
  Qed.

  Definition blk3W : list ivl := [(P + 464, P + 472); (P + 480 + 8, P + 480 + 16); (F + 64, F + 64 + 4); (F + 32, F + 32 + 16); (ERRNO_A, ERRNO_A + 4)]%Z.
  #[using="Type"] Lemma blk3W_ok : Forall inW3 blk3W.
  Proof.
    unfold blk3W, inW3, inP, inFJ, inER.
    constructor; [left; cbn [fst snd]; lia|]. constructor; [left; cbn [fst snd]; lia|].
    constructor; [right; left; cbn [fst snd]; lia|]. constructor; [right; left; cbn [fst snd]; lia|].
    constructor; [right; right; left; cbn [fst snd]; lia| constructor].
  Qed.

  #[using="q lo m0 POK RF0"] Lemma blk3W_fcls : Forall (fsenv_cls (FSB FI)) blk3W.
  Proof.
    destruct eframe_facts as (FLO & FHI & _ & _ & _ & _ & _ & _ & _ & _ & PF1 & PF2). unfold blk3W.
    constructor; [apply fcls_in_fs; lia|]. constructor; [apply fcls_in_fs; lia|]. constructor; [apply fcls_in_fs; lia|]. constructor; [apply fcls_in_fs; lia|].
    constructor; [apply fcls_errno; lia| constructor].
  Qed.

  #[using="IC STACK_MALLOC_0 STACK_MALLOC_1 STACK_MALLOC_2 m0 POK RF0 FCO"] Lemma blk3bE : forall (q' A len cap cur gmax : Z) (bs : list byte) (wcsz : word)
      x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    pinvS eshadowU q' m -> pctx A len cap cur bs m -> txt_okA A len cap -> pstatE gmax m -> 0 <= cur <= len ->
    nth_error bs (Z.to_nat len) = Some (Z_to_bv 8 0) -> bv_unsigned tp = 0x5e6970 ->
    rw_cells asegs m (P + 464) [C8 wcsz] ->
    FSENV FI m ->
    (forall m' r y1 y5 y6 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       0 <= r <= 5 -> r <> 4 ->
       pinvS eshadowU q' m' -> pctx A len cap cur bs m' -> pstatE gmax m' -> rw_cells asegs m' (P + 464) [C8 wcsz] ->
       munch ((lo, q) :: FSIV blk3W) m m' -> wmono asegs m m' -> fkeep FI blk3W st m m' ->
       evt asegs Q (MS (pregs q P st gp tp q' y1 y5 y6 y10 y11 y12 y13 y14 y15 y16 y17 (wz r) y28 y29 y30 y31) F_ (wz 0x89ecc) fc None m' (seg_rom asegs))) ->
    (forall m' v cur' y5 y6 y7 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       0 <= v < 2^31 -> cur + 1 <= cur' -> cur' <= len ->
       pinvS eshadowU q' m' -> pctx A len cap cur' bs m' -> pstatE gmax m' -> rw_cells asegs m' (P + 464) [C8 (wz v)] ->
       munch ((lo, q) :: FSIV blk3W) m m' -> wmono asegs m m' -> fkeep FI blk3W st m m' ->
       evt asegs Q (ajcallstE 0x8c704 0x89ca4 q' (wz (P + 400)) (wz cur) (wz (cur' - cur)) y5 y6 y7 y13 y14 y15 y16 y17 S2V S3V (wz cur) (wz 4) y28 y29 y30 y31 m')) ->
    evt asegs Q (MS (pregs q P st gp tp q' x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 (wz 3) x28 x29 x30 x31) F_ (wz 0x89c48) fc None m (seg_rom asegs)).
  Proof.
    intros q' A len cap cur gmax bs wcsz x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m Q INV CTX TOK PST CR NULT TPV C464 FE KF KO.
    pose proof INV as INV0. destruct INV as (ST & (j0 & j160 & QC) & MI & AE & (QB & QAL) & VR).
    destruct VR as (_ & _ & _ & _ & (jf & FT1) & _ & SHF & _ & (stc & RF & LIVE1)).
    pose proof CTX as CTX0. destruct CTX as (SC & MBC & TXT & SHP & SHA & SHSEP & SHFC & SHFL & SHZ & SHR & (ev & CLOW) & SHE).
    pose proof POK as POK'. pokA POK'. pose proof TOK as TOK'. tokA TOK'.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct (text_bytesE m A cap bs TXT ltac:(lia)) as [BUF BL].
    destruct (eouts_shw m SHF) as [SHO2 SHO1].
    destruct (fj_split m jf FT1) as (pa & pb & j1 & pv & j2 & O2 & J1 & O1 & J2).
    pose proof (elive_of stc LIVE1) as EL. pose proof EL as (LVF & LVS & LVL & LVP & LSUB).
    destruct eframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & PAF & PAFL & PF1 & PF2).
    pose proof (fsb_ok FI) as (B1 & B2 & _).
    assert (NUM : alloc_ceiling <= lo /\ lo <= q' /\ 0x609000 <= FSB FI /\ FSB FI + A0_FS_FRAMES <= F /\ F + 128 <= FSB FI + A0_FS_SIZE
                  /\ FSB FI + A0_FS_FRAMES <= P /\ P + 504 <= FSB FI + A0_FS_SIZE /\ FSB FI + A0_FS_SIZE <= alloc_ceiling
                  /\ (P + 504 <= F \/ F + 128 <= P)) by (clear - CLO LO QB B1 B2 FLO FHI PF1 PF2 PAF; lia).
    hide QAL. hide AL16. hide PAL. hide AAL. hide FAL. hide TFS. hide TBAND. hide PAF. hide PAFL.
    unfold pregs, eSH in *.
    walk_lia_to 0x89c64. step.
    eapply evt_cut.
    { eapply (match_chunkA IC FI STACK_MALLOC_0 STACK_MALLOC_1) with (S := P + 480) (MB := P + 400) (A := A) (len := len) (cap := cap) (cur0 := cur)
                           (P := F + 64) (P2 := F + 32) (lo := lo) (q := q') (bs := bs) (st := stc) (pv := pv) (pw1 := pa) (pw2 := pb) (ev := ev) (canary := canary);
        [ unhide QAL; apply (evf_ok q' A len cap cur bs stc _ EL QB QAL TOK BL CR);
          constructor; [left; unfold inFJ; cbn [fst snd]; lia|]; constructor; [left; unfold inFJ; cbn [fst snd]; lia|]; constructor; [right; unfold inER; cbn [fst snd]; lia| constructor]
        | clear - LO QB; lia | change (2^47) with 140737488355328 in *; clear - QHI QB; lia | exact RF
        | exact (fs_call_ok_le FI _ _ _ 2%nat (fs_call_ok_push FI st stc tp 3%nat _ FCO LIVE1) ltac:(lia)) | exact FE
        | exact ST | exact MI | exact AE | exact SC | exact MBC | exact BUF
        | apply (shw_sub _ P 504); [exact SHP| lia| lia| lia]
        | apply (shw_sub _ P 504); [exact SHP| lia| lia| lia]
        | apply (shw_sub _ A (cap + 1)); [exact SHA| lia| lia| lia]
        | exact SHSEP | exact SHFC
        | apply (shz_sub _ _ _ _ _ SHZ); [lia| apply sh_mono; clear - QB; lia]
        | intros a Ha; apply SHR; pose proof (sh_mono q' q ltac:(clear - QB; lia)); lia
        | exact O1 | exact SHO1 | unhide FAL; clear - FAL; Z.div_mod_to_equations; lia | clear - NUM; lia
        | exact O2 | exact SHO2 | unhide FAL; clear - FAL; Z.div_mod_to_equations; lia | right; clear; lia
        | exact TPV | exact CLOW | exact SHE | exact ALO | exact NULT | clear - LENC CAPB; lia ]. }
    intros ms' POST. unfold match_postXA in POST.
    destruct POST as (r & cur' & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & st' & -> & MUF & WMF & MI' & FKc & LIVE' & RF' & ST' & AE' & SC' & RR & CR' & ROK & RNOK & XF).
    destruct XF as (pv' & pa' & pb' & ev' & O1' & O2' & CLOW' & XOK).
    replace (ret_pc (Z_to_bv 64 0x89c68)) with (Z_to_bv 64 0x89c68) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (HW3 : Forall inW3 [(P + 480 + 8, P + 480 + 16); (F + 64, F + 64 + 4); (F + 32, F + 32 + 16); (ERRNO_A, ERRNO_A + 4)]%Z).
    { unfold inW3, inP, inFJ, inER. constructor; [left; cbn [fst snd]; lia|]. constructor; [right; left; cbn [fst snd]; lia|].
      constructor; [right; left; cbn [fst snd]; lia|]. constructor; [right; right; left; cbn [fst snd]; lia| constructor]. }
    assert (J1' : rw_cells asegs m' (F + 48) [CB 16 j1]).
    { eapply (rw_cells_fkeep FI _ stc); [exact J1| exact FKc| exact WMF| left; apply (Contracts.lb_sub _ _ _ _ _ LVF); simpl_sizes; lia|].
      cbn [disjoint_from]; simpl_sizes; repeat split; try exact I; clear - NUM; lia. }
    assert (J2' : rw_cells asegs m' (F + 68) [CB 52 j2]).
    { eapply (rw_cells_fkeep FI _ stc); [exact J2| exact FKc| exact WMF| left; apply (Contracts.lb_sub _ _ _ _ _ LVF); simpl_sizes; lia|].
      cbn [disjoint_from]; simpl_sizes; repeat split; try exact I; clear - NUM; lia. }
    assert (C464' : rw_cells asegs m' (P + 464) [C8 wcsz]).
    { eapply (rw_cells_fkeep FI _ stc); [exact C464| exact FKc| exact WMF| left; apply (Contracts.lb_sub _ _ _ _ _ LVP); simpl_sizes; lia|].
      cbn [disjoint_from]; simpl_sizes; repeat split; try exact I; clear - NUM; lia. }
    pose proof (fj_join m' pa' pb' j1 pv' j2 O2' J1' O1' J2') as FT1'.
    pose proof (pinv_stepF eshadowU eq_refl _ q' m m' stc st' INV0 LIVE1 MUF WMF FKc LIVE' RF' ST' MI' AE' HW3 FT1') as INV1.
    assert (DJM : disjoint_from [(P + 480 + 8, P + 480 + 16); (F + 64, F + 64 + 4); (F + 32, F + 32 + 16); (ERRNO_A, ERRNO_A + 4)]%Z (P + 400) 32)
      by (cbn [disjoint_from]; repeat split; try exact I; clear - NUM; lia).
    assert (DJT : disjoint_from [(P + 480 + 8, P + 480 + 16); (F + 64, F + 64 + 4); (F + 32, F + 32 + 16); (ERRNO_A, ERRNO_A + 4)]%Z A (cap + 1))
      by (cbn [disjoint_from]; repeat split; try exact I; unhide TFS; clear - NUM TFS ALO; lia).
    pose proof (pctx_stepF _ q' A len cap cur cur' bs m m' stc CTX0 TOK QB RF LIVE1 MUF WMF FKc HW3 DJM DJT SC' (ex_intro _ ev' CLOW')) as CTX1.
    assert (PST1 : pstatE gmax m').
    { destruct PST as (G1 & G2 & G3 & G4). pose proof (fsw_W3 _ q' HW3) as FW. pose proof (hiER_fsW3 _ q' HW3) as HE.
      unfold pstatE.
      split; [eapply rw_cells_transport; [exact G1| exact MUF| exact WMF| apply dj_hiER; [exact HE| simpl_sizes; lia]]|].
      split; [eapply rw_cells_transport; [exact G2| exact MUF| exact WMF| apply dj_hiER; [exact HE| simpl_sizes; lia]]|].
      split; [apply (shw_frame_fs FI _ m m' _ 8 G3 MUF FW); left; clear - B1; lia|].
      eapply rw_cells_transport; [exact G4| exact MUF| exact WMF| apply dj_hiER; [exact HE| simpl_sizes; lia]]. }
    assert (MUa : munch ((lo, q) :: FSIV blk3W) m m').
    { clear - MUF QB. eapply munch_weaken; [| exact MUF]. unfold blk3W. sub_fp_solve. }
    assert (FKa : fkeep FI blk3W st m m').
    { eapply (fkeep_weaken FI _ blk3W stc st m m' FKc); [unfold blk3W; sub_fp_solve| exact LSUB]. }
    pose proof WMF as WMa.
    pose proof (fsenv_FSIV FI blk3W lo q m m' FE MUa CLO blk3W_fcls) as FEa.
    clear ST QC MI AE SC MBC TXT BUF SHP SHA SHSEP SHFC SHFL SHZ SHR CLOW SHE SHF FT1 O1 O2 J1 J2 SHO1 SHO2 C464 RF INV0 CTX0 PST MUF WMF FKc.
    pose proof INV1 as (ST1 & (j0' & j160' & QC1) & MI1 & AE1 & _ & VR1).
    destruct VR1 as (_ & _ & _ & _ & _ & _ & _ & _ & (stc1 & RF1 & LIVE1')).
    pose proof CTX1 as (SC1 & _ & _ & SHP1 & _).
    unfold eSH in QC1.
    zstep. zstep. step. if_cases KB; zify_cond KB.
    {
      assert (cur' = cur) by (apply RNOK; exact KB). subst cur'.
      pose proof (munch_refl [(P + 488, P + 496)]%Z m') as MU2. pose proof (wmono_refl asegs m') as WM2.
      walk_lia_to 0x89e40. step.
      assert (HWc : Forall inP [(P + 488, P + 496)]%Z) by (unfold inP; repeat constructor; cbn [fst snd]; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (pinv_stepP eshadowU eq_refl q' m' mm _ INV1 MU2 WM2 MI1 HWc) as INV2 end.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (FE2 : FSENV FI mm) by (refine (fsenv_munch FI _ m' mm FEa MU2 _); constructor; [apply fcls_in_fs; clear - NUM; lia| constructor]) end.
      pose proof INV2 as (ST2 & _ & _ & AE2 & _ & VR2). destruct VR2 as (_ & _ & _ & _ & (jf2 & FT2) & _ & _ & _ & (stc2 & RF2 & LIVE2)).
      assert (AWc : app_ivs [(P + 488, P + 496)]%Z).
      { constructor; [| constructor]. unfold app_iv, SH_HI. cbn [fst snd]. pose proof (fsb_ok FI) as (_ & _ & _ & _ & B5). clear - NUM B5. lia. }
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (PST2 : pstatE gmax mm) by (apply (pstat_stepW [(P + 488, P + 496)]%Z gmax m' mm PST1 MU2 WM2); [constructor; [left; cbn [fst]; clear - NUM; lia| constructor]| exact AWc]) end.
      pose proof PST2 as (_ & _ & _ & IW2).
      eapply evt_cut.
      { eapply (UpnpPrintf_spec_A FI STACK_MALLOC_2) with (lo := lo) (st := stc2);
          [exact IW2| exact ST2| exact CLO| unfold A0_RT_STACK; clear - LO QB; lia| unhide QAL; exact QAL| clear - QB QHI; lia| exact MI1| exact AE2| exact RF2
          | exact (fs_call_ok_le FI _ _ _ 1%nat (fs_call_ok_push FI st stc2 tp 3%nat _ FCO LIVE2) ltac:(lia)) | exact FE2]. }
      intros ms' POST. unfold UpnpPrintf_post_A in POST.
      destruct POST as (z5 & z6 & z7 & z10 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m3 & st3 & -> & MU3 & WM3 & MI3 & FK3 & LIVE3 & RF3 & ST3 & AE3 & IW3).
      replace (ret_pc (Z_to_bv 64 0x89e44)) with (Z_to_bv 64 0x89e44) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (elive_of stc2 LIVE2) as (LVF2 & LVS2 & LVL2 & LVP2 & LSUB2).
      assert (FT3 : exists j, rw_cells asegs m3 (F + 32) [CB 88 j]).
      { exists jf2. eapply (rw_cells_fkeep FI [] stc2); [exact FT2| exact FK3| exact WM3| left; apply (Contracts.lb_sub _ _ _ _ _ LVF2); simpl_sizes; lia| exact I]. }
      pose proof (pinv_stepF eshadowU eq_refl [] q' _ m3 stc2 st3 INV2 LIVE2 MU3 WM3 FK3 LIVE3 RF3 ST3 MI3 AE3 (Forall_nil _) FT3) as INV3.
      assert (DJM2 : disjoint_from [(P + 488, P + 496)]%Z (P + 400) 32) by (cbn [disjoint_from]; split; [clear; lia| exact I]).
      pose proof (pctx_stepP _ A len cap cur cur bs m' _ CTX1 TOK MU2 WM2 HWc DJM2 SC1) as CTX2.
      assert (SC3 : rw_cells asegs m3 (P + 480) [C8 (wz (P + 400)); C8 (wz cur); C4 (wz 0)]).
      { eapply (rw_cells_fkeep FI [] stc2); [exact SC1| exact FK3| exact WM3| left; apply (Contracts.lb_sub _ _ _ _ _ LVP2); simpl_sizes; lia| exact I]. }
      assert (CLOW3 : exists ev3, clow canary ev3 m3).
      { destruct CTX2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (ev2 & CL2) & _). exists ev2.
        exact (clow_stepW _ ev2 _ m3 CL2 MU3 WM3 (low_fsW [] q' (Forall_nil _))). }
      pose proof (pctx_stepF [] q' A len cap cur cur bs _ m3 stc2 CTX2 TOK QB RF2 LIVE2 MU3 WM3 FK3 (Forall_nil _) I I SC3 CLOW3) as CTX3.
      assert (PST3 : pstatE gmax m3).
      { destruct PST2 as (G1 & G2 & G3 & G4). pose proof (fsw_W3 [] q' (Forall_nil _)) as FW. pose proof (hiER_fsW3 [] q' (Forall_nil _)) as HE.
        unfold pstatE.
        split; [eapply rw_cells_transport; [exact G1| exact MU3| exact WM3| apply dj_hiER; [exact HE| simpl_sizes; lia]]|].
        split; [eapply rw_cells_transport; [exact G2| exact MU3| exact WM3| apply dj_hiER; [exact HE| simpl_sizes; lia]]|].
        split; [apply (shw_frame_fs FI _ _ m3 _ 8 G3 MU3 FW); left; clear - B1; lia|].
        exact IW3. }
      assert (C464c : rw_cells asegs m3 (P + 464) [C8 wcsz]).
      { eapply (rw_cells_fkeep FI [] stc2); [exact C464'| exact FK3| exact WM3| left; apply (Contracts.lb_sub _ _ _ _ _ LVP2); simpl_sizes; lia| exact I]. }
      assert (MUb : munch ((lo, q) :: FSIV blk3W) m m3).
      { eapply munch_trans; [exact MUa|]. clear - MU3 QB. eapply munch_weaken; [| exact MU3]. unfold blk3W. sub_fp_solve. }
      pose proof (wmono_trans _ _ _ _ WMa WM3) as WMb.
      assert (FKb : fkeep FI blk3W st m m3).
      { eapply fkeep_trans; [exact FKa|]. eapply fkeep_trans.
        - eapply (fkeep_of_munch FI blk3W _ st stc1 m' m' _ RF1); [intros g Hg; rewrite LIVE1'; right; exact Hg| exact MU2|].
          unfold blk3W. constructor; [| constructor]. left. cbn [fst snd inside]. clear. lia.
        - eapply (fkeep_weaken FI [] blk3W stc2 st _ m3 FK3); [unfold blk3W; sub_fp_solve| exact LSUB2]. }
      clear QC1 ST1 ST2 AE1 AE2 RF1 RF2 SC1 MI1 INV1 INV2 CTX1 CTX2 PST1 PST2 C464' MU2 WM2 MU3 WM3 FK3 FKa MUa WMa IW2 IW3 FT2 SHP1.
      pose proof INV3 as (_ & (j0'' & j160'' & QC3) & _). unfold eSH in QC3.
      step. step. step.
      eapply (KF m3 r); try eassumption.
    }
    assert (r = 4) by lia. subst r.
    destruct (XOK eq_refl) as (v & -> & VR & CUR1).
    pose proof (munch_refl [(P + 464, P + 472)]%Z m') as MU2. pose proof (wmono_refl asegs m') as WM2.
    walk_lia_to 0x89ca0. step.
    assert (HWc : Forall inP [(P + 464, P + 472)]%Z) by (unfold inP; repeat constructor; cbn [fst snd]; lia).
    assert (DJM2 : disjoint_from [(P + 464, P + 472)]%Z (P + 400) 32) by (cbn [disjoint_from]; split; [clear; lia| exact I]).
    assert (AWc : app_ivs [(P + 464, P + 472)]%Z).
    { constructor; [| constructor]. unfold app_iv, SH_HI. cbn [fst snd]. pose proof (fsb_ok FI) as (_ & _ & _ & _ & B5). clear - NUM B5. lia. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (pinv_stepP eshadowU eq_refl q' m' mm _ INV1 MU2 WM2 MI1 HWc) as INV2;
      pose proof (pctx_stepP _ A len cap cur' cur' bs m' mm CTX1 TOK MU2 WM2 HWc DJM2 SC1) as CTX2;
      assert (PST2 : pstatE gmax mm) by (apply (pstat_stepW [(P + 464, P + 472)]%Z gmax m' mm PST1 MU2 WM2); [constructor; [left; cbn [fst]; clear - NUM; lia| constructor]| exact AWc]);
      assert (FKb : fkeep FI blk3W st m mm) by
        (eapply fkeep_trans; [exact FKa|]; eapply (fkeep_of_munch FI blk3W _ st stc1 m' m' _ RF1); [intros g Hg; rewrite LIVE1'; right; exact Hg| exact MU2|];
         unfold blk3W; constructor; [| constructor]; left; cbn [fst snd inside]; clear; lia)
    end.
    eapply (KO _ v cur'); try eassumption; lia.
  Qed.

  Definition retstA (pc q' r : Z) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 (m : mem) : machine_state :=
    MS (mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') x10 x11 x12 x13 x14 x15 x16 x17
            x18 x19 x20 x21 x22 x23 x24 x25 (wz r) (wz SF) x28 x29 x30 x31)
       F_ (wz pc) fc None m (seg_rom asegs).

  Definition blk5W : list ivl := [(P + 480 + 8, P + 480 + 16)]%Z.
  #[using="Type"] Lemma blk5W_ok : Forall inW3 blk5W.
  Proof. unfold blk5W, inW3, inP. constructor; [left; cbn [fst snd]; lia| constructor]. Qed.

  #[using="IC STACK_MALLOC_0 STACK_MALLOC_1 m0 POK RF0 FCO"] Lemma blk5aE : forall (q' A len cap cur csz gmax : Z) (bs : list byte)
      x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    pinv q' m -> pctx A len cap cur bs m -> txt_okA A len cap -> pstatE gmax m -> 0 <= cur <= len -> 0 <= csz < 2^63 ->
    rw_cells asegs m (P + 464) [C8 (wz csz)] ->
    FSENV FI m ->
    (len - cur < csz -> forall y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y28 y29 y30 y31,
       evt asegs Q (retstA 0x8a14c q' 1 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y28 y29 y30 y31 m)) ->
    (forall m' r y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y28 y29 y30 y31,
       0 <= r <= 5 -> r <> 4 -> csz <= len - cur ->
       pinv q' m' -> pctx A len cap cur bs m' -> pstatE gmax m' -> rw_cells asegs m' (P + 464) [C8 (wz csz)] ->
       munch ((lo, q) :: FSIV blk5W) m m' -> wmono asegs m m' -> fkeep FI blk5W st m m' ->
       evt asegs Q (retstA 0x8a1bc q' r y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y28 y29 y30 y31 m')) ->
    (forall m' cur' y5 y6 y7 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       csz <= len - cur -> cur + csz + 1 <= cur' -> cur' <= len ->
       pinv q' m' -> pctx A len cap cur' bs m' -> pstatE gmax m' -> rw_cells asegs m' (P + 464) [C8 (wz csz)] ->
       munch ((lo, q) :: FSIV blk5W) m m' -> wmono asegs m m' -> fkeep FI blk5W st m m' ->
       evt asegs Q (ajcallstE 0x8c704 0x89d98 q' (wz (P + 400)) (wz (cur + csz)) (wz (cur' - (cur + csz))) y5 y6 y7 y13 y14 y15 y16 y17 S2V S3V (wz (cur + csz)) (wz 3) y28 y29 y30 y31 m')) ->
    evt asegs Q (blkstA q' 0x89d18 x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m).
  Proof.
    intros q' A len cap cur csz gmax bs x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m Q INV CTX TOK PST CR CSR C464 FE KI KF KO.
    pose proof INV as INV0. destruct INV as (ST & (j0 & j160 & QC) & MI & AE & (QB & QAL) & VR).
    destruct VR as (_ & _ & _ & _ & (jf & FT1) & _ & _ & _ & (stc & RF & LIVE1)).
    pose proof CTX as CTX0. destruct CTX as (SC & MBC & TXT & SHP & SHA & SHSEP & SHFC & SHFL & SHZ & SHR & (ev & CLOW) & SHE).
    pose proof POK as POK'. pokA POK'. pose proof TOK as TOK'. tokA TOK'.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct (text_bytesE m A cap bs TXT ltac:(lia)) as [BUF BL].
    pose proof (elive_of stc LIVE1) as EL. pose proof EL as (LVF & LVS & LVL & LVP & LSUB).
    destruct eframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & PAF & PAFL & PF1 & PF2).
    pose proof (fsb_ok FI) as (B1 & B2 & _).
    assert (NUM : alloc_ceiling <= lo /\ lo <= q' /\ 0x609000 <= FSB FI /\ FSB FI + A0_FS_FRAMES <= F /\ F + 128 <= FSB FI + A0_FS_SIZE
                  /\ FSB FI + A0_FS_FRAMES <= P /\ P + 504 <= FSB FI + A0_FS_SIZE /\ FSB FI + A0_FS_SIZE <= alloc_ceiling
                  /\ (P + 504 <= F \/ F + 128 <= P)) by (clear - CLO LO QB B1 B2 FLO FHI PF1 PF2 PAF; lia).
    hide QAL. hide AL16. hide PAL. hide AAL. hide FAL. hide TFS. hide TBAND. hide PAF. hide PAFL.
    unfold blkstA, pregs, eSH, mbuf_cells, MEMBUF_DEF_SIZE_INC in *.
    pose proof (munch_refl [(P + 488, P + 496)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
    walk_lia_to 0x89d70.
    if_cases KI0; zify_cond KI0.
    { zstep. unfold retstA in KI. apply KI. lia. }
    assert (CSZ : csz <= len - cur) by lia. clear KI KI0.
    walk_lia_to 0x89d70. step.
    replace (csz + cur) with (cur + csz) in * by lia.
    assert (HWc : Forall inP [(P + 488, P + 496)]%Z) by (unfold inP; repeat constructor; cbn [fst snd]; lia).
    assert (DJMc : disjoint_from [(P + 488, P + 496)]%Z (P + 400) 32) by (cbn [disjoint_from]; split; [clear; lia| exact I]).
    assert (AWc : app_ivs [(P + 488, P + 496)]%Z).
    { constructor; [| constructor]. unfold app_iv, SH_HI. cbn [fst snd]. pose proof (fsb_ok FI) as (_ & _ & _ & _ & B5). clear - NUM B5. lia. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (pinv_stepP eshadow eq_refl q' m mm _ INV0 MU0 WM0 MI HWc) as INV1;
      pose proof (pctx_stepP _ A len cap cur (cur + csz) bs m mm CTX0 TOK MU0 WM0 HWc DJMc SC) as CTX1;
      assert (PST1 : pstatE gmax mm) by (apply (pstat_stepW [(P + 488, P + 496)]%Z gmax m mm PST MU0 WM0); [constructor; [left; cbn [fst]; clear - NUM; lia| constructor]| exact AWc]);
      assert (FK1 : fkeep FI blk5W st m mm) by
        (eapply (fkeep_of_munch FI blk5W _ st stc m m _ RF); [exact LSUB| exact MU0|];
         unfold blk5W; constructor; [| constructor]; left; cbn [fst snd inside]; clear; lia);
      assert (FE1 : FSENV FI mm) by (refine (fsenv_munch FI _ m mm FE MU0 _); constructor; [apply fcls_in_fs; clear - NUM; lia| constructor])
    end.
    clear ST AE RF MBC SHP SHA SHSEP SHFC SHFL SHZ SHR CLOW SHE FT1 INV0 CTX0 PST SC LIVE1 EL LVF LVS LVL LVP LSUB. try clear TXT. try clear BUF.
    pose proof INV1 as (ST1 & _ & _ & AE1 & _ & VR1). destruct VR1 as (_ & _ & _ & _ & (jf1 & FT1) & _ & _ & _ & (stc1 & RF1 & LIVE1)).
    pose proof CTX1 as (SC1 & MBC1 & TXT1 & SHP1 & SHA1 & SHSEP1 & _ & SHFL1 & SHZ1 & SHR1 & (ev1 & CLOW1) & _).
    destruct (text_bytesE _ A cap bs TXT1 ltac:(lia)) as [BUF1 _].
    pose proof (elive_of stc1 LIVE1) as EL. pose proof EL as (LVF & LVS & LVL & LVP & LSUB).
    eapply evt_cut.
    { eapply (match_crlfA IC FI STACK_MALLOC_0 STACK_MALLOC_1) with (S := P + 480) (MB := P + 400) (A := A) (len := len) (cap := cap) (cur0 := cur + csz)
                           (lo := lo) (q := q') (bs := bs) (st := stc1);
        [ unhide QAL; apply (evf_ok q' A len cap (cur + csz) bs stc1 _ EL QB QAL TOK BL); [clear - CR CSR CSZ; lia| constructor]
        | clear - LO QB; lia | change (2^47) with 140737488355328 in *; clear - QHI QB; lia | exact RF1
        | exact (fs_call_ok_le FI _ _ _ 2%nat (fs_call_ok_push FI st stc1 tp 3%nat _ FCO LIVE1) ltac:(lia)) | exact FE1
        | exact ST1 | exact MI | exact AE1 | exact SC1 | exact MBC1 | exact BUF1
        | apply (shw_sub _ P 504); [exact SHP1| lia| lia| lia]
        | apply (shw_sub _ P 504); [exact SHP1| lia| lia| lia]
        | intros _; apply (shw_sub _ A (cap + 1)); [exact SHA1| lia| lia| lia]
        | exact SHSEP1 | exact SHFL1
        | apply (shz_sub _ _ _ _ _ SHZ1); [lia| apply sh_mono; clear - QB; lia]
        | intros a Ha; apply SHR1; pose proof (sh_mono q' q ltac:(clear - QB; lia)); lia ]. }
    intros ms' POST. unfold match_postXA in POST.
    destruct POST as (r & cur' & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & st' & -> & MUF & WMF & MI' & FKc & LIVE' & RF' & ST' & AE' & SC' & RR & CR' & ROK & RNOK & XF).
    destruct XF as (_ & XOK).
    replace (ret_pc (Z_to_bv 64 0x89d74)) with (Z_to_bv 64 0x89d74) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (FT1' : exists j, rw_cells asegs m' (F + 32) [CB 88 j]).
    { exists jf1. eapply (rw_cells_fkeep FI _ stc1); [exact FT1| exact FKc| exact WMF| left; apply (Contracts.lb_sub _ _ _ _ _ LVF); simpl_sizes; lia|].
      cbn [disjoint_from]; simpl_sizes; repeat split; try exact I; clear - NUM; lia. }
    pose proof (pinv_stepF eshadow eq_refl _ q' _ m' stc1 st' INV1 LIVE1 MUF WMF FKc LIVE' RF' ST' MI' AE' blk5W_ok FT1') as INV2.
    assert (DJM : disjoint_from blk5W (P + 400) 32) by (unfold blk5W; cbn [disjoint_from]; split; [clear; lia| exact I]).
    assert (DJT : disjoint_from blk5W A (cap + 1)) by (unfold blk5W; cbn [disjoint_from]; split; [unhide TFS; clear - NUM TFS; lia| exact I]).
    assert (CLOW' : exists ev', clow canary ev' m').
    { exists ev1. apply (clow_stepW _ ev1 _ m' CLOW1 MUF WMF). apply (low_fsW blk5W q'). unfold blk5W, inP. constructor; [cbn [fst snd]; clear; lia| constructor]. }
    pose proof (pctx_stepF _ q' A len cap (cur + csz) cur' bs _ m' stc1 CTX1 TOK QB RF1 LIVE1 MUF WMF FKc blk5W_ok DJM DJT SC' CLOW') as CTX2.
    assert (C464' : rw_cells asegs m' (P + 464) [C8 (wz csz)]).
    { eapply (rw_cells_fkeep FI _ stc1); [exact C464| exact FKc| exact WMF| left; apply (Contracts.lb_sub _ _ _ _ _ LVP); simpl_sizes; lia|].
      cbn [disjoint_from]; simpl_sizes; repeat split; try exact I; clear; lia. }
    assert (PST2 : pstatE gmax m').
    { destruct PST1 as (G1 & G2 & G3 & G4). pose proof (fsw_W3 _ q' blk5W_ok) as FW. pose proof (hiER_fsW3 _ q' blk5W_ok) as HE.
      unfold pstatE.
      split; [eapply rw_cells_transport; [exact G1| exact MUF| exact WMF| apply dj_hiER; [exact HE| simpl_sizes; lia]]|].
      split; [eapply rw_cells_transport; [exact G2| exact MUF| exact WMF| apply dj_hiER; [exact HE| simpl_sizes; lia]]|].
      split; [apply (shw_frame_fs FI _ _ m' _ 8 G3 MUF FW); left; clear - B1; lia|].
      eapply rw_cells_transport; [exact G4| exact MUF| exact WMF| apply dj_hiER; [exact HE| simpl_sizes; lia]]. }
    assert (MUa : munch ((lo, q) :: FSIV blk5W) m m').
    { eapply munch_trans.
      - clear - MU0. eapply munch_weaken; [| exact MU0]. unfold blk5W. sub_fp_solve.
      - clear - MUF QB. eapply munch_weaken; [| exact MUF]. unfold blk5W. sub_fp_solve. }
    pose proof (wmono_trans _ _ _ _ WM0 WMF) as WMa.
    assert (FKa : fkeep FI blk5W st m m').
    { eapply fkeep_trans; [exact FK1|]. eapply (fkeep_weaken FI _ blk5W stc1 st _ m' FKc); [unfold blk5W; sub_fp_solve| exact LSUB]. }
    clear ST1 AE1 RF1 SC1 MBC1 TXT1 BUF1 SHP1 SHA1 SHSEP1 SHFL1 SHZ1 SHR1 CLOW1 FT1 INV1 CTX1 PST1 C464 MU0 WM0 FK1 MUF WMF FKc QC MI.
    pose proof INV2 as (_ & (j0' & j160' & QC2) & MI2 & _ & _ & VR2). destruct VR2 as (_ & _ & _ & _ & _ & _ & _ & _ & (stc2 & RF2 & LIVE2)).
    pose proof CTX2 as (SC2 & _ & _ & SHP2 & _).
    unfold eSH in QC2.
    zstep. step. if_cases KB; zify_cond KB.
    {
      assert (cur' = cur + csz) by (apply RNOK; exact KB). subst cur'.
      pose proof (munch_refl [(P + 488, P + 496)]%Z m') as MU3. pose proof (wmono_refl asegs m') as WM3.
      walk_lia_to 0x8a1bc.
      replace (cur + csz - csz) with cur in * by lia.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (pinv_stepP eshadow eq_refl q' m' mm _ INV2 MU3 WM3 MI2 HWc) as INV3;
        pose proof (pctx_stepP _ A len cap (cur + csz) cur bs m' mm CTX2 TOK MU3 WM3 HWc DJMc SC2) as CTX3;
        assert (PST3 : pstatE gmax mm) by (apply (pstat_stepW [(P + 488, P + 496)]%Z gmax m' mm PST2 MU3 WM3); [constructor; [left; cbn [fst]; clear - NUM; lia| constructor]| exact AWc]);
        assert (FKb : fkeep FI blk5W st m mm) by
          (eapply fkeep_trans; [exact FKa|]; eapply (fkeep_of_munch FI blk5W _ st stc2 m' m' _ RF2); [intros g Hg; rewrite LIVE2; right; exact Hg| exact MU3|];
           unfold blk5W; constructor; [| constructor]; left; cbn [fst snd inside]; clear; lia)
      end.
      unfold retstA in KF. eapply (KF _ r); try eassumption. }
    assert (r = 4) by lia. subst r.
    pose proof (XOK eq_refl) as CUR1.
    walk_lia_to 0x89d94. step.
    eapply (KO m' cur'); try eassumption; lia.
  Qed.

  Definition blk5cW : list ivl := [(P + 392, P + 400); (P + 440, P + 444); (P + 452, P + 456); (P + 488, P + 496)]%Z.
  #[using="m0 POK RF0"] Lemma blk5cE : forall (q' A len cap sv cur' csz elen err entp gmax : Z) (bs : list byte)
      x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    pinv q' m -> pctx A len cap cur' bs m -> txt_okA A len cap -> pstatE gmax m -> 0 < gmax < 2^32 ->
    0 <= csz < 2^63 -> 0 <= elen < 2^63 -> 0 <= sv < 2^64 ->
    rw_cells asegs m (P + 392) [C8 (wz elen)] ->
    rw_cells asegs m (P + 440) [C4 (wz err)] -> rw_cells asegs m (P + 452) [C4 (wz entp)] ->
    rw_cells asegs m (P + 464) [C8 (wz csz)] ->
    (gmax < elen + csz -> forall m' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y28 y29 y30 y31,
       pinv q' m' -> pctx A len cap sv bs m' -> pstatE gmax m' ->
       rw_cells asegs m' (P + 392) [C8 (wz (elen + csz))] -> rw_cells asegs m' (P + 440) [C4 (wz 413)] -> rw_cells asegs m' (P + 452) [C4 (wz entp)] ->
       rw_cells asegs m' (P + 464) [C8 (wz csz)] -> munch blk5cW m m' -> wmono asegs m m' ->
       evt asegs Q (retstA 0x8a1f4 q' 3 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y28 y29 y30 y31 m')) ->
    (elen + csz <= gmax -> forall m' y1 y5 y6 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       pinv q' m' -> pctx A len cap sv bs m' -> pstatE gmax m' ->
       rw_cells asegs m' (P + 392) [C8 (wz (elen + csz))] -> rw_cells asegs m' (P + 440) [C4 (wz err)] -> rw_cells asegs m' (P + 452) [C4 (wz 3)] ->
       rw_cells asegs m' (P + 464) [C8 (wz csz)] -> munch blk5cW m m' -> wmono asegs m m' ->
       evt asegs Q (loopstA q' 6 y1 y5 y6 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m')) ->
    evt asegs Q (ajretstE 0x89d98 q' x10 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 S2V S3V (wz sv) (wz 3) x28 x29 x30 x31 m).
  Proof.
    intros q' A len cap sv cur' csz elen err entp gmax bs x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m Q
      INV CTX TOK PST GMX CSR ELR SVR C392 C440 C452 C464 KX KL.
    pose proof INV as INV0. destruct INV as (_ & (j0 & j160 & QC) & MI & _ & (QB & _) & _).
    pose proof CTX as CTX0. destruct CTX as (SC & _ & _ & SHP & _).
    pose proof PST as PST0. destruct PST as (G1 & G2 & G3 & _).
    pose proof POK as POK'. pokA POK'. clear PLB.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    unfold ajretstE, pregsG, loopstA, retstA, pregs, eSH in *.
    pose proof (munch_refl blk5cW m) as MU. pose proof (wmono_refl asegs m) as WM. unfold blk5cW in MU.
    assert (HW : Forall inP blk5cW) by (unfold blk5cW, inP; repeat constructor; cbn [fst snd]; lia).
    assert (DJM : disjoint_from blk5cW (P + 400) 32) by (unfold blk5cW; cbn [disjoint_from]; repeat split; try exact I; lia).
    assert (FIN : forall m', munch blk5cW m m' -> wmono asegs m m' -> mem_inv asegs m' ->
       rw_cells asegs m' (P + 480) [C8 (wz (P + 400)); C8 (wz sv); C4 (wz 0)] ->
       pinv q' m' /\ pctx A len cap sv bs m' /\ pstatE gmax m').
    { intros m' MU' WM' MI' SC'.
      split; [exact (pinv_stepP eshadow eq_refl q' m m' blk5cW INV0 MU' WM' MI' HW)|].
      split; [exact (pctx_stepP blk5cW A len cap cur' sv bs m m' CTX0 TOK MU' WM' HW DJM SC')|].
      apply (pstat_stepW blk5cW gmax m m' PST0 MU' WM').
      - eapply Forall_impl; [| exact HW]. intros [x y] (H1 & _). left. cbn [fst] in *. lia.
      - pose proof (fsb_ok FI) as (B1 & B2 & _ & _ & B5). destruct eframe_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PF1 & PF2).
        eapply Forall_impl; [| exact HW]. intros [x y] (H1 & H2 & H3). cbn [fst snd] in *. unfold app_iv, SH_HI. cbn [fst snd]. clear - H1 H2 H3 PF1 PF2 B1 B2 B5. lia. }
    clear INV0 CTX0 PST0.
    walk_lia_to 0x89c00. chk0_auto 12 0xaea60. step. clear_shr. walk_lia_to 0x89c00.
    replace (Z.land gmax 4294967295) with gmax by (change 4294967295 with (Z.ones 32); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity).
    if_cases KG; zify_cond KG.
    {
      walk_lia_to 0x8a1f4. rewrite ?Z.mod_small in * by lia.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => destruct (FIN mm MU WM MI SC) as (I1 & I2 & I3) end.
      eapply (KX ltac:(lia)); eassumption. }
    walk_lia_to 0x89c00. rewrite ?Z.mod_small in * by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => destruct (FIN mm MU WM MI SC) as (I1 & I2 & I3) end.
    eapply (KL ltac:(lia)); eassumption.
  Qed.

End PE.
End W.
