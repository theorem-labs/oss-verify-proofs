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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpRepA AWKit AWAuto AWAuto2 FakeKit HObjK HObjF FsEnvKit H_scanner_get_token H_vfm_A H_vfm_G H_vfm_X H_vfm_GX H_match_shell H_match_A H_match_X H_map_str_to_int H_puri.
Import ListNotations.
Open Scope Z_scope.

Definition parser_parse_entryA : Z := 0x8a904.
Notation PQ_LOOP := 0x8aadc%Z.
Notation PQ_REQL := 0x8ab34%Z.
Notation PQ_REJOIN := 0x8aca4%Z.
Notation PQ_EXIT := 0x8b158%Z.
Notation PPARSE_DEPTH_A := 65536%Z.
Notation METHOD_TAB_A := 0xae960%Z.
Notation FMT_REQ09_A := 0x21a80%Z.
Notation FMT_REQ_A := 0x21aa0%Z.

Section W.
Context {HC : HasCeiling}.
Variable FI : fs_if.
Hypothesis IC : icpt_contracts.
Hypothesis STACK_MALLOC_1 : stack_malloc_stmt FI 1.
Local Notation FSIV W := ((FSB FI, FSB FI + A0_FS_SIZE) :: (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE) :: W)%Z.

Definition pq_okA (q lo P : Z) (st : fsstate FI) : Prop :=
  alloc_ceiling <= lo /\ lo <= q - PPARSE_DEPTH_A /\ q mod 16 = 0 /\ q + 64 <= 2^47
  /\ 0x609000 <= P /\ P + 504 <= alloc_ceiling /\ P mod 8 = 0 /\ lb (fs_live FI st) P 504.
Ltac pqokA V := destruct V as (CLO & LO & AL16 & QHI & PLO & PHI & PAL & PLB).

Section DEFS.
  Variables (q lo P : Z) (st : fsstate FI).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32).

  Definition qF := fs_F FI st 1.  Definition qFL := fs_FL FI st 1.  Definition qst1 := fs_next FI st 1.  Definition qSF := sh qF.
  Notation F := qF. Notation FL := qFL. Notation st1 := qst1. Notation SF := qSF.
  Definition qSH (X : Z) : Z := Z.shiftr X 3 + 2147450880.

  Definition qshadow : list cell :=
    [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
     C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
     C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
     C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)].

  Definition qshadowU : list cell :=
    [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)].

  Definition pscrQ (q' : Z) (m : mem) : Prop :=
    exists j0 j160 j192,
      rw_cells asegs m q' [CB 32 j0; C8 (wz (Z.land (P + 448) 7 + 3)); C8 (wz (P + 280)); C8 (wz (P + 276)); C8 (wz (P + 8));
                           C8 (wz F); C8 (wz F); C8 (wz (P + 4)); C8 (wz (P + 432)); C8 (wz METHOD_TAB_A); C8 (wz (F + 64)); C8 (wz (P + 440));
                           C8 (wz 2147450880); C8 (wz (qSH (P + 488))); C8 (wz FMT_REQ09_A); C8 (wz (P + 488)); C8 (wz (F + 32));
                           CB 24 j160; C8 (wz F); CB 24 j192].

  Definition prestQ (shd : list cell) (q' : Z) (m : mem) : Prop :=
    (q' = q + -320 \/ q' = q + -320 - 16)
    /\ stk asegs m (q' + 216) (q + -104)
    /\ rw_cells asegs m (q + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ (exists w0, rw_cells asegs m F [C8 w0; C8 (wz 0x1801b); C8 (wz 0x8a904); C8 (wz q')])
    /\ (exists j, rw_cells asegs m (F + 32) [CB 88 j])
    /\ rw_cells asegs m (F + 120) [C8 (wz FL)]
    /\ rw_cells asegs m SF shd
    /\ rw_cells asegs m FL [C1 (Z_to_bv 8 1)]
    /\ (exists stc, RFAKE FI stc m /\ fs_live FI stc = fs_newff FI st 1 :: fs_live FI st).

  Definition pinvQS (shd : list cell) (q' : Z) (m : mem) : Prop :=
    stk asegs m lo q' /\ pscrQ q' m /\ mem_inv asegs m /\ asan_env asegs m
    /\ (q + -336 <= q' <= q + -320 /\ q' mod 16 = 0)
    /\ prestQ shd q' m.

  Definition pregsQ (q' : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 : word) : bvmap 5 word :=
    mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') x10 x11 x12 x13 x14 x15 x16 x17
        (wz SF) (wz P) (wz 2) (wz 4) (wz (F + 96)) (wz (P + 448)) (wz (qSH (P + 448))) x25 (Z_to_bv 64 (-8)) (wz (P + 480)) x28 x29 x30 x31.
  Definition loopstQ (q' : Z) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 (m : mem) : machine_state :=
    MS (pregsQ q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31) F_ (wz PQ_LOOP) fc None m (seg_rom asegs).
  Definition exitstQ (q' r : Z) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 (m : mem) : machine_state :=
    MS (pregsQ q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (wz r) x28 x29 x30 x31) F_ (wz PQ_EXIT) fc None m (seg_rom asegs).
End DEFS.

Section PQ.
  Variables (q lo P : Z) (st : fsstate FI).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32) (m0 : mem).
  Hypothesis POK : pq_okA q lo P st.
  Hypothesis RF0 : RFAKE FI st m0.
  Hypothesis FCO : fs_call_ok FI st tp 5.
  Hypothesis FE0 : FSENV FI m0.

  Notation F := (qF st). Notation FL := (qFL st). Notation st1 := (qst1 st). Notation SF := (qSF st).
  Notation prestQ := (prestQ q st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Notation pscrQ := (pscrQ P st).
  Notation pinvQS := (pinvQS q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Notation pinvQ := (pinvQS qshadow).
  Notation loopstQ := (loopstQ q P st gp tp F_ fc). Notation exitstQ := (exitstQ q P st gp tp F_ fc).

  Ltac hide_mem_except2 k1 k2 :=
    repeat match goal with
    | H : rw_cells _ _ _ _ |- _ => tryif (first [constr_eq H k1 | constr_eq H k2]) then fail else hide H
    | H : stk _ _ _ _ |- _ => hide H
    | H : munch _ _ _ |- _ => hide H
    | H : wmono _ _ _ |- _ => hide H
    end.

  #[using="STACK_MALLOC_1 POK RF0 FCO FE0"] Lemma prologueQ : forall t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (Q : machine_state -> Prop),
    stk asegs m0 lo q -> mem_inv asegs m0 -> asan_env asegs m0 ->
    (forall q' m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31, pinvQ q' m ->
       munch ((lo, q) :: FSIV []) m0 m -> wmono asegs m0 m -> fkeep FI [] st m0 m ->
       evt asegs Q (loopstQ q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 m)) ->
    evt asegs Q
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz parser_parse_entryA) fc None m0 (seg_rom asegs)).
  Proof.
    intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Q ST MI AG K.
    pose proof POK as POK'. pqokA POK'. unfold parser_parse_entryA.
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
    carve_frame 320%nat ST.
    step. do 14 (step; fix_lit_store).
    step.
    step.
    rewrite (unsigned_lit (q + -320)) by lia. rewrite land_align32 by lia.
    remember (q + -320 - (q + -320) mod 32)%Z as q' eqn:Eq0.
    assert (Hq : q' = q + -320 \/ q' = q + -320 - 16) by (subst q'; apply align32_cases; clear - AL16; Z.div_mod_to_equations; lia).
    assert (QAL : q' mod 16 = 0) by (subst q'; clear - AL16; Z.div_mod_to_equations; lia).
    hide AL16. hide QAL. clear Eq0.
    lazymatch goal with FRx : rw_cells asegs ?mm (q + -320) (?c0 :: ?c1 :: ?rest) |- _ =>
      destruct (align_frame_gen mm lo (q + -320) q' [c0; c1] rest 216%nat ST ltac:(lia) FRx eq_refl ltac:(lia) Hq) as (STq & (jq & QC) & GAP & FRhi);
      clear FRx end.
    clear ST. rename STq into ST. assert (QB : q + -336 <= q' <= q + -320) by lia. hide Hq. change (Z.of_nat 216) with 216 in GAP, FRhi. replace (q + -320 + 216) with (q + -104) in GAP, FRhi by lia.
    step.
    step. step. step. step.
    step. step.
    step.
    step.   lit_branch.
    step.
    step.
    env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
    pose proof (fs_call_ok_le FI _ _ _ 1%nat FCO ltac:(lia)) as FCO1.
    call (STACK_MALLOC_1 st lo q' 128 F SF FL 128 88%nat 16%nat).
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
    zstep.
    step.   if_cases K0; zify_cond K0. 2:{ exfalso. lia. } clear K0.
    assert (SFLO : SF + 16 <= lo /\ 2147450880 <= SF) by (clear - SFB FLO FHI FSB1 FSB2 CLO ACR; lia).

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(q', q' + 216); (F, F + 128)]%Z mm) as MUs; pose proof (wmono_refl asegs mm) as WMs end.
    hide_mem_except2 QC FRF. unhide MUs. unhide WMs.
    sstep. sstep. zstep. sstep. zstep. sstep.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    sstep. zstep. sstep. zstep. sstep. zstep. sstep. zstep. sstep. zstep. sstep.
    zstep. zstep. zstep. zstep. zstep. zstep.
    sstep. zstep. sstep. sstep. sstep. zstep.
    unhide_transport MUs WMs. clear MUs WMs.

    replace (Z_to_bv 64 (Z.shiftr F 3 + 2147450880)) with (Z_to_bv 64 SF) by (f_equal; rewrite shiftr3_div; unhide ESF; rewrite ESF; reflexivity).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(q', q' + 216); (SF, SF + 16)]%Z mm) as MUs; pose proof (wmono_refl asegs mm) as WMs end.
    hide_mem_except2 QC SHF. unhide MUs. unhide WMs.
    sstep. sstep. sstep. sstep. zstep.
    sstep. sstep. sstep. sstep. zstep.
    sstep. sstep. sstep. sstep. sstep. sstep. sstep. sstep.
    sstep. zstep. zstep. sstep. zstep. sstep. zstep. zstep. sstep. sstep. zstep. sstep.
    unhide_transport MUs WMs. clear MUs WMs.
    step.

    env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
    match goal with P0 : stk asegs _ lo q' |- _ => rename P0 into ST end.
    split_chunk FRF 4%nat FH FT. split_chunk FT 1%nat FT1 FT2. replace (F + 32 + 88) with (F + 120) in FT2 by lia.
    unhide Hq. unhide QAL.
    eapply (K q' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [| exact MUF| exact WM| exact FK].
    split; [exact ST|]. split; [do 3 eexists; exact QC|]. split; [exact MI0|]. split; [exact AE|].
    split; [split; [exact QB| exact QAL]|].
    split; [exact Hq|]. split; [exact GAP|]. split; [exact FRhi|]. split; [eexists; exact FH|]. split; [eexists; exact FT1|]. split; [exact FT2|].
    split; [exact SHF|]. split; [exact FLG|]. exists st1. split; [exact RF| exact LIVE1].
  Qed.

  Definition ajcallstQ (callee ret q' : Z) x5 x6 x7 (a1 : word) x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 (m : mem) : machine_state :=
    MS (pregsQ q P st gp tp q' (wz ret) x5 x6 x7 (wz P) a1 x12 x13 x14 x15 x16 x17 (wz 3) x28 x29 x30 x31) F_ (wz callee) fc None m (seg_rom asegs).
  Definition retstQ (ret q' r : Z) x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 (m : mem) : machine_state :=
    MS (pregsQ q P st gp tp q' (wz ret) x5 x6 x7 (wz r) x11 x12 x13 x14 x15 x16 x17 (wz 3) x28 x29 x30 x31) F_ (wz ret) fc None m (seg_rom asegs).
  Definition reqlstQ (q' : Z) x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 (m : mem) : machine_state :=
    MS (pregsQ q P st gp tp q' x1 x5 x6 x7 (wz 0) (wz 1) x12 x13 x14 x15 x16 x17 (wz 3) x28 x29 x30 x31) F_ (wz PQ_REQL) fc None m (seg_rom asegs).

  #[using="lo POK"] Lemma loopQ : forall (q' pos : Z) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    mem_inv asegs m -> rw_cells asegs m (P + 448) [C4 (wz pos)] -> acc m (P + 448 + 8 - 1) -> 0 <= pos <= 4 ->
    (pos = 0 -> evt asegs Q (reqlstQ q' x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m)) ->
    (pos = 1 -> evt asegs Q (ajcallstQ 0x879d0 0x8ab08 q' x5 x6 x7 (wz 1) x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m)) ->
    (pos = 2 -> evt asegs Q (ajcallstQ 0x88134 0x8aad4 q' x5 x6 x7 (wz 1) x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m)) ->
    (pos = 3 -> evt asegs Q (ajcallstQ 0x89a20 0x8ab28 q' x5 x6 x7 (wz 3) x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m)) ->
    (pos = 4 -> evt asegs Q (exitstQ q' 3 x1 x5 x6 x7 (wz 4) (wz 3) x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m)) ->
    evt asegs Q (loopstQ q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 m).
  Proof.
    intros q' pos x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 m Q MI PC HACC PR K0 K1 K2 K3 K4.
    pose proof POK as POK'. pqokA POK'. clear PLB.
    unfold loopstQ, reqlstQ, ajcallstQ, exitstQ, pregsQ, qSH in *.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let a := reg_val 24 in
      destruct (AWAuto2.acc_loadw mm (P + 448) 8 a ltac:(lia) ltac:(clear - PAL; Z.div_mod_to_equations; lia) ltac:(lia) HACC ltac:(shadow_addr_tac)) as (k & SHR & Hk) end.
    destruct Hk as [-> | [K1' K2']]; [| exfalso; clear - PAL K1' K2'; Z.div_mod_to_equations; lia].
    step. step. lit_branch. clear SHR HACC.
    zstep. rewrite (sx32_lit pos) by lia.
    assert (CASES : pos = 0 \/ pos = 1 \/ pos = 2 \/ pos = 3 \/ pos = 4) by lia.
    destruct CASES as [-> |[-> |[-> |[-> | ->]]]].
    - zstep. zstep. step. lit_branch. step. lit_branch. apply K0. reflexivity.
    - zstep. zstep. step. lit_branch. step. lit_branch. zstep. step. lit_branch. zstep. step. apply K1. reflexivity.
    - zstep. zstep. step. lit_branch. step. lit_branch. zstep. step. apply K2. reflexivity.
    - zstep. zstep. step. lit_branch. step. lit_branch. zstep. step. lit_branch. zstep. step. apply K3. reflexivity.
    - zstep. zstep. step. lit_branch. step. lit_branch. zstep. step. lit_branch. apply K4. reflexivity.
  Qed.

  #[using="Type"] Lemma retQ : forall (ret q' r : Z) x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    ret = 0x8ab08 \/ ret = 0x8aad4 \/ ret = 0x8ab28 -> 0 <= r <= 6 ->
    (r = 4 -> evt asegs Q (loopstQ q' (wz ret) x5 x6 x7 (wz 4) x11 x12 x13 x14 x15 x16 x17 (wz 4) x28 x29 x30 x31 m)) ->
    (r <> 4 -> evt asegs Q (exitstQ q' r (wz ret) x5 x6 x7 (wz r) x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m)) ->
    evt asegs Q (retstQ ret q' r x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m).
  Proof.
    intros ret q' r x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m Q HRET RR KL KX.
    unfold retstQ, loopstQ, exitstQ, pregsQ in *.
    destruct HRET as [-> |[-> | ->]].
    - zstep. step. if_cases KB; zify_cond KB; [assert (r = 4) by lia; subst r; apply KL; reflexivity| zstep; apply KX; lia].
    - zstep. step. if_cases KB; zify_cond KB; [apply KX; lia| assert (r = 4) by lia; subst r; apply KL; reflexivity].
    - zstep. step. if_cases KB; zify_cond KB; [assert (r = 4) by lia; subst r; apply KL; reflexivity| zstep; apply KX; lia].
  Qed.

  Definition epostQ (X : mem -> Z -> Prop) : machine_state -> Prop :=
    fun ms' => exists (r : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (st' : fsstate FI),
      ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ mem_inv asegs m' /\ fs_live FI st' = fs_live FI st /\ RFAKE FI st' m'
      /\ stk asegs m' lo q /\ asan_env asegs m' /\ X m' r.
  Definition pWQ : list ivl := [(lo, q); (F, F + 128); (SF, SF + 16); (FL, FL + 1)]%Z.
  Definition rframeQ (R : mem -> Prop) : Prop := forall m m', R m -> munch pWQ m m' -> wmono asegs m m' -> R m'.

  #[using="m0 POK RF0"] Lemma exitFQ : forall (q' r : Z) (R : mem -> Prop)
      x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m,
    pinvQ q' m -> R m -> rframeQ R ->
    evt asegs (epostQ (fun m' r' => R m' /\ r' = r))
      (MS (pregsQ q P st gp tp q' x1 x5 x6 x7 x10 (wz F) x12 x13 x14 x15 x16 x17 (wz r) x28 x29 x30 x31) F_ (wz 0x8b170) fc None m (seg_rom asegs)).
  Proof.
    intros q' r R x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m INV HR RFR. unfold pregsQ.
    destruct INV as (ST & (j0 & j160 & j192 & QC) & MI & AE & (QB & QAL) & VR).
    destruct VR as (Hq & GAP & FRhi & (w0 & FH) & (jf & FT1) & FT2 & SHF & FLG & (stc & RF & LIVE1)).
    pose proof POK as POK'. pqokA POK'.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR. unfold qshadow, qSH in *.
    pose proof (fsb_ok FI) as (FSB1 & FSB2 & _ & FSB4 & FSB5).
    destruct (new_frame_facts FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & FLO & FHI & FAL & FLLO & FLHI & APART).
    cbn [FB_of SB_of] in FHI. clear APART PLB.
    assert (SFB : 8 * (SF - 2147450880) = F) by (unfold qSF, sh, SHADOW_OFF; clear - FAL; Z.div_mod_to_equations; lia).
    assert (SHB8 : 8 * (sh (FSB FI) - 2147450880) = FSB FI) by (unfold sh, SHADOW_OFF; clear - FSB4; Z.div_mod_to_equations; lia).
    hide FAL. hide FSB4. hide Hq. hide PAL. hide QAL. hide AL16.
    pose proof (new_frame_fk FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
    assert (LSUB : forall g, In g (fs_live FI st) -> In g (fs_live FI stc)) by (intros g Hg; rewrite LIVE1; right; exact Hg).
    pose proof (lb_new _ _ _ LIVE1) as LVF. pose proof (ls_new _ _ _ LIVE1) as LVS. pose proof (lf_new _ _ _ LIVE1) as LVL.
    unfold ff_size, ff_shsize in LVF, LVS. rewrite FCLS in LVF, LVS. cbn [FB_of SB_of] in LVF, LVS.
    change (ff_addr (fs_newff FI st 1)) with F in LVF, LVS. change (ff_flag (fs_newff FI st 1)) with FL in LVL. change (sh F) with SF in LVS.
    pose proof (fkeep_refl FI [] st m) as FK.
    pose proof (munch_refl pWQ m) as MUE. pose proof (wmono_refl asegs m) as WME. unfold pWQ in MUE.
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
    step.   zstep.   zstep.
    do 13 step.
    step.   step.
    release_frame QC ST (q' + 216)%Z.
    pose proof (stk_merge asegs _ _ _ _ ST GAP ltac:(lia)) as STm. clear ST GAP.
    release_frame FRhi STm q.
    apply evt_done. unfold epostQ. exists r. do 14 eexists. lazymatch goal with |- exists _ _, MS _ _ _ _ _ ?mm _ = _ /\ _ => exists mm, (fs_after_release FI stc) end.
    split; [reflexivity|]. split; [exact MI|]. split; [exact LIVE3|]. split; [exact RF3|]. split; [exact STm|]. split; [exact AE|].
    split; [exact (RFR m _ HR MUE WME)| reflexivity].
  Qed.

  #[using="m0 POK RF0"] Lemma exitQ : forall (q' r : Z) (R : mem -> Prop)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m,
    pinvQ q' m -> R m -> rframeQ R ->
    evt asegs (epostQ (fun m' r' => R m' /\ r' = r))
      (exitstQ q' r x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m).
  Proof.
    intros q' r R x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m INV HR RFR. unfold exitstQ, pregsQ.
    destruct INV as (ST & (j0 & j160 & j192 & QC) & MI & AE & (QB & QAL) & VR).
    destruct VR as (Hq & GAP & FRhi & (w0 & FH) & (jf & FT1) & FT2 & SHF & FLG & (stc & RF & LIVE1)).
    pose proof POK as POK'. pqokA POK'. clear PLB.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (FSB1 & FSB2 & _ & FSB4 & FSB5).
    destruct (new_frame_facts FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (_ & FLO & FHI & FAL & FLLO & FLHI & _).
    cbn [FB_of] in FHI.
    assert (SFB : 8 * (SF - 2147450880) = F) by (unfold qSF, sh, SHADOW_OFF; clear - FAL; Z.div_mod_to_equations; lia).
    assert (FSF : F + 128 <= SF \/ SF + 16 <= F) by (clear - SFB FLO FHI FSB1 FSB2 FSB5 ACR; lia).
    clear FSB5 FSB4 FAL. hide FSF. hide Hq. hide PAL. hide AL16. hide QAL.
    assert (RFm : forall m', munch [(F, F + 8)]%Z m m' -> wmono asegs m m' -> R m').
    { intros m' MU WM. apply (RFR m m' HR); [| exact WM]. eapply munch_weaken; [| exact MU]. unfold pWQ. intros xx OO. cbn [outside] in *. clear - OO. lia. }
    assert (AEm : forall m', munch [(F, F + 8)]%Z m m' -> wmono asegs m m' -> asan_env asegs m' /\ RFAKE FI stc m').
    { intros m' MU WM. split.
      - apply (asan_env_frame asegs m m' [(F, F + 8)]%Z AE MU WM). unfold env_safe. constructor; [left; cbn [fst snd]; clear - FLO FSB1; lia| constructor].
      - apply (rfake_frame FI stc m m' [(F, F + 8)]%Z RF MU WM). constructor; [| constructor]. right; left. cbn [fst snd].
        pose proof (lb_new _ _ _ LIVE1) as LVF. unfold ff_size in LVF.
        destruct (new_frame_facts FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & _). rewrite FCLS in LVF. cbn [FB_of] in LVF.
        change (ff_addr (fs_newff FI st 1)) with F in LVF. apply (Contracts.lb_sub _ _ _ _ _ LVF); lia. }
    clear HR AE RF. hide SHF. unfold qSH in QC.
    pose proof (munch_refl [(F, F + 8)]%Z m) as MU1. pose proof (wmono_refl asegs m) as WM1.
    (zstep; zstep; zstep; sstep; zstep; step; if_cases K0; zify_cond K0; try (exfalso; lia); clear K0;
       lazymatch type of MU1 with munch _ _ ?m1 =>
         assert (SHF1 : rw_cells asegs m1 SF (qshadow)) by (unhide SHF; unfold qshadow in *; eapply rw_cells_transport; [exact SHF| exact MU1| exact WM1| cbn [disjoint_from]; simpl_sizes; split; [| exact I]; unhide FSF; clear - FSF; lia]) end;
       unhide Hq; unhide QAL;
       eapply (exitFQ q' r R); [| exact (RFm _ MU1 WM1)| exact RFR];
       split; [eassumption|]; split; [do 3 eexists; unfold qSH; eassumption|]; split; [eassumption|]; split; [exact (proj1 (AEm _ MU1 WM1))|]; split; [exact (conj QB QAL)|];
       split; [exact Hq|]; split; [eassumption|]; split; [eassumption|]; split; [eexists; eassumption|]; split; [eexists; eassumption|]; split; [eassumption|];
       split; [exact SHF1|]; split; [eassumption|]; exists stc; split; [exact (proj2 (AEm _ MU1 WM1))| exact LIVE1]).
  Qed.

  #[using="m0 POK RF0"] Lemma pinvQ_stepSh : forall shd shd' q' m m', pinvQS shd q' m -> munch [(SF, SF + 16)]%Z m m' -> wmono asegs m m' -> mem_inv asegs m' ->
    rw_cells asegs m' SF shd' -> pinvQS shd' q' m'.
  Proof.
    intros shd shd' q' m m' (ST & (j0 & j160 & j192 & QC) & MI & AE & (QB & QAL) & VR) MU WM MI' SHF'.
    destruct VR as (Hq & GAP & FRhi & (w0 & FH) & (jf & FT1) & FT2 & SHF & FLG & (stc & RF & LIVE1)).
    pose proof POK as POK'. pqokA POK'. clear PLB.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (FSB1 & FSB2 & _ & FSB4 & FSB5).
    destruct (new_frame_facts FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & FLO & FHI & FAL & FLLO & FLHI & _).
    cbn [FB_of] in FHI.
    assert (SFB : 8 * (SF - 2147450880) = F) by (unfold qSF, sh, SHADOW_OFF; clear - FAL; Z.div_mod_to_equations; lia).
    assert (AP : SF + 16 <= lo /\ 0x609000 <= SF /\ (F + 128 <= SF \/ SF + 16 <= F) /\ (FL + 1 <= SF \/ SF + 16 <= FL))
      by (clear - SFB FLO FHI FLLO FLHI FSB1 FSB2 FSB5 ACR CLO; lia).
    destruct AP as (A1 & A2 & A3 & A4).
    assert (DJ : forall X n, (X + n <= SF \/ SF + 16 <= X) -> disjoint_from [(SF, SF + 16)]%Z X n) by (intros X n HX; cbn [disjoint_from]; split; [lia| exact I]).
    split; [eapply stk_transport_disjoint; [exact ST| exact MU| exact WM| apply DJ; right; lia]|].
    split; [exists j0, j160, j192; eapply rw_cells_transport; [exact QC| exact MU| exact WM| apply DJ; right; simpl_sizes; lia]|].
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

  #[using="m0 POK RF0"] Lemma unpoisonQ : forall (q' : Z) x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    pinvQ q' m ->
    (forall m', pinvQS qshadowU q' m' -> munch [(SF, SF + 16)]%Z m m' -> wmono asegs m m' ->
       evt asegs Q (MS (pregsQ q P st gp tp q' x1 x5 x6 x7 (wz 0) (wz 1) x12 x13 x14 x15 x16 x17 (wz 3) x28 x29 x30 x31) F_ (wz 0x8ab4c) fc None m' (seg_rom asegs))) ->
    evt asegs Q (reqlstQ q' x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m).
  Proof.
    intros q' x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m Q INV K.
    pose proof INV as INV0. destruct INV as (_ & _ & MI & _ & _ & VR). destruct VR as (_ & _ & _ & _ & _ & _ & SHF & _).
    unfold reqlstQ, pregsQ, qshadow in *.
    pose proof (munch_refl [(SF, SF + 16)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    sstep. sstep. sstep. sstep. sstep. sstep.
    eapply K; [| exact MU| exact WM].
    eapply (pinvQ_stepSh _ _ q' m _ INV0 MU WM); [eassumption| exact SHF].
  Qed.

  #[using="m0 POK RF0"] Lemma rejoinQ : forall (q' r : Z) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    pinvQS qshadowU q' m -> 0 <= r <= 5 ->
    (forall m', r = 4 -> pinvQ q' m' -> munch [(SF, SF + 16)]%Z m m' -> wmono asegs m m' ->
       evt asegs Q (loopstQ q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (wz 4) x28 x29 x30 x31 m')) ->
    (forall m', r <> 4 -> pinvQ q' m' -> munch [(SF, SF + 16)]%Z m m' -> wmono asegs m m' ->
       evt asegs Q (exitstQ q' r x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m')) ->
    evt asegs Q (MS (pregsQ q P st gp tp q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (wz r) x28 x29 x30 x31) F_ (wz PQ_REJOIN) fc None m (seg_rom asegs)).
  Proof.
    intros q' r x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m Q INV RR KL KX.
    pose proof INV as INV0. destruct INV as (_ & _ & MI & _ & _ & VR). destruct VR as (_ & _ & _ & _ & _ & _ & SHF & _).
    unfold pregsQ, loopstQ, exitstQ, qshadowU in *.
    pose proof (munch_refl [(SF, SF + 16)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    sstep. sstep. sstep. sstep. sstep. sstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (INV' : pinvQ q' mm) by (eapply (pinvQ_stepSh _ _ q' m _ INV0 MU WM); [eassumption| exact SHF]) end.
    step. if_cases KB; zify_cond KB.
    - assert (r = 4) by lia. subst r. eapply KL; [reflexivity| exact INV'| exact MU| exact WM].
    - step. eapply KX; [lia| exact INV'| exact MU| exact WM].
  Qed.

  Definition inP (iv : ivl) : Prop := P <= fst iv /\ fst iv <= snd iv /\ snd iv <= P + 504.
  #[using="Type"] Lemma dj_inP : forall (W : list ivl) X n, Forall inP W -> (X + n <= P \/ P + 504 <= X) -> disjoint_from W X n.
  Proof.
    induction W as [|[a b] W IH]; intros X n HW HX; cbn [disjoint_from]; [exact I|].
    inversion HW as [|? ? (H1 & H2 & H3) HW']; subst. cbn [fst snd] in *. split; [lia| exact (IH X n HW' HX)].
  Qed.
  #[using="m0 POK RF0"] Lemma pinv_stepP : forall shd, Z.of_nat (cells_size shd) = 16 -> forall q' m m' (W : list ivl),
    pinvQS shd q' m -> munch W m m' -> wmono asegs m m' -> mem_inv asegs m' -> Forall inP W -> pinvQS shd q' m'.
  Proof.
    intros shd HSZ q' m m' W (ST & (j0 & j160 & j192 & QC) & MI & AE & (QB & QAL) & VR) MU WM MI' HW.
    destruct VR as (Hq & GAP & FRhi & (w0 & FH) & (jf & FT1) & FT2 & SHF & FLG & (stc & RF & LIVE1)).
    pose proof POK as POK'. pqokA POK'.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (FSB1 & FSB2 & _).
    destruct (new_frame_facts FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (_ & FLO & FHI & _ & FLLO & FLHI & APART).
    cbn [FB_of SB_of] in FHI, APART.
    assert (SH1 : sh (FSB FI) <= SF /\ SF + 16 <= sh (FSB FI) + A0_FS_SHSIZE).
    { pose proof (fsb_ok FI) as (_ & _ & _ & B4 & _). unfold qSF, sh, SHADOW_OFF. clear - FLO FHI B4. Z.div_mod_to_equations. lia. }
    pose proof (lb_apart_frame _ _ _ F 128 _ _ PLB APART) as PF.
    pose proof (lb_apart_shadow FI st m0 _ _ SF 16 RF0 PLB ltac:(lia) ltac:(lia)) as PS.
    pose proof (lb_apart_flag FI st m0 _ _ FL RF0 PLB FLLO FLHI) as PL.
    assert (LSUB : forall g, In g (fs_live FI st) -> In g (fs_live FI stc)) by (intros g Hg; rewrite LIVE1; right; exact Hg).
    assert (DJ : forall X n, (X + n <= P \/ P + 504 <= X) -> disjoint_from W X n) by (intros X n HX; exact (dj_inP W X n HW HX)).
    split; [eapply stk_transport_disjoint; [exact ST| exact MU| exact WM| apply DJ; right; lia]|].
    split; [exists j0, j160, j192; eapply rw_cells_transport; [exact QC| exact MU| exact WM| apply DJ; right; simpl_sizes; lia]|].
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
    pinvQS shd q' m -> munch W m m' -> wmono asegs m m' -> mem_inv asegs m' -> Forall (fun iv => inP iv \/ outX iv) W -> pinvQS shd q' m'.
  Proof.
    intros shd HSZ q' m m' W (ST & (j0 & j160 & j192 & QC) & MI & AE & (QB & QAL) & VR) MU WM MI' HW.
    destruct VR as (Hq & GAP & FRhi & (w0 & FH) & (jf & FT1) & FT2 & SHF & FLG & (stc & RF & LIVE1)).
    pose proof POK as POK'. pqokA POK'.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (FSB1 & FSB2 & _ & FSB4 & FSB5).
    destruct (new_frame_facts FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (_ & FLO & FHI & _ & FLLO & FLHI & APART).
    cbn [FB_of SB_of] in FHI, APART.
    assert (SH1 : sh (FSB FI) <= SF /\ SF + 16 <= sh (FSB FI) + A0_FS_SHSIZE).
    { unfold qSF, sh, SHADOW_OFF. clear - FLO FHI FSB4. Z.div_mod_to_equations. lia. }
    assert (SH2 : 0x7fff8000 <= sh (FSB FI) /\ sh (FSB FI) + A0_FS_SHSIZE <= 0x10007fff8000).
    { unfold sh, SHADOW_OFF. clear - FSB1 FSB2 ACR. Z.div_mod_to_equations. lia. }
    pose proof (lb_apart_frame _ _ _ F 128 _ _ PLB APART) as PF.
    pose proof (lb_apart_shadow FI st m0 _ _ SF 16 RF0 PLB ltac:(lia) ltac:(lia)) as PS.
    pose proof (lb_apart_flag FI st m0 _ _ FL RF0 PLB FLLO FLHI) as PL.
    assert (LSUB : forall g, In g (fs_live FI st) -> In g (fs_live FI stc)) by (intros g Hg; rewrite LIVE1; right; exact Hg).
    assert (DJ : forall X n, (X + n <= P \/ P + 504 <= X) -> clsX X n -> disjoint_from W X n) by (intros X n HX HC'; exact (dj_inPX W X n HW HX HC')).
    split; [eapply stk_transport_disjoint; [exact ST| exact MU| exact WM| apply DJ; [right; lia| left; lia]]|].
    split; [exists j0, j160, j192; eapply rw_cells_transport; [exact QC| exact MU| exact WM| apply DJ; [right; simpl_sizes; lia| left; lia]]|].
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

  #[using="Type"] Lemma epostQ_mono : forall (X Y : mem -> Z -> Prop), (forall m' r, X m' r -> Y m' r) -> forall ms, epostQ X ms -> epostQ Y ms.
  Proof.
    intros X Y HXY ms (r & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & st' & E & H1 & H2 & H3 & H4 & H5 & HX).
    exists r, t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', st'.
    split; [exact E|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. exact (HXY _ _ HX).
  Qed.
  #[using="Type"] Lemma zx32_litE : forall x, 0 <= x < 2^32 -> zx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
  Proof. intros x H. unfold zx32. f_equal. rewrite unsigned_lit by lia. apply Z.mod_small. lia. Qed.

  #[using="P m0 POK RF0"] Lemma xobj_rframe : forall X cs n, Z.of_nat (cells_size cs) = n -> outX (X, X + n) -> rframeQ (fun mm => rw_cells asegs mm X cs).
  Proof.
    intros X cs n Hn (H1 & H2 & H3 & H4 & H5) m m' H MU WM. cbn [fst snd] in *. pose proof POK as POK'. pqokA POK'.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (FSB1 & FSB2 & _ & FSB4 & FSB5).
    destruct (new_frame_facts FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (_ & FLO & FHI & _ & FLLO & FLHI & _).
    cbn [FB_of SB_of] in FHI.
    assert (SH1 : sh (FSB FI) <= SF /\ SF + 16 <= sh (FSB FI) + A0_FS_SHSIZE).
    { unfold qSF, sh, SHADOW_OFF. clear - FLO FHI FSB4. Z.div_mod_to_equations. lia. }
    assert (SH2 : 0x7fff8000 <= sh (FSB FI) /\ sh (FSB FI) + A0_FS_SHSIZE <= 0x10007fff8000).
    { unfold sh, SHADOW_OFF. clear - FSB1 FSB2 ACR. Z.div_mod_to_equations. lia. }
    eapply rw_cells_transport; [exact H| exact MU| exact WM|]. unfold pWQ. cbn [disjoint_from]. rewrite Hn.
    clear - H1 H2 H3 H4 H5 CLO FLO FHI SH1 SH2 FLLO FLHI. repeat split; try exact I; lia.
  Qed.

  #[using="q lo m0 POK RF0"] Lemma eframe_facts :
    FSB FI + A0_FS_FRAMES <= F /\ F + 128 <= FSB FI + A0_FS_SIZE /\ F mod 64 = 0
    /\ FSB FI + 4096 <= FL /\ FL + 1 <= FSB FI + A0_FS_FRAMES
    /\ 8 * (SF - 2147450880) = F
    /\ sh (FSB FI) <= SF /\ SF + 16 <= sh (FSB FI) + A0_FS_SHSIZE
    /\ (P + 504 <= F \/ F + 128 <= P) /\ (P + 504 <= FL \/ FL + 1 <= P)
    /\ FSB FI + A0_FS_FRAMES <= P /\ P + 504 <= FSB FI + A0_FS_SIZE.
  Proof.
    pose proof POK as POK'. pqokA POK'.
    destruct (new_frame_facts FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & FLO & FHI & FAL & FLLO & FLHI & APART).
    cbn [FB_of SB_of] in FHI, APART.
    pose proof (fsb_ok FI) as (B1 & B2 & B3 & B4 & B5).
    pose proof (lb_apart_frame _ _ _ F 128 _ _ PLB APART) as P1.
    pose proof (lb_apart_flag FI st m0 _ _ FL RF0 PLB FLLO FLHI) as P3.
    split; [exact FLO|]. split; [exact FHI|]. split; [exact FAL|]. split; [exact FLLO|]. split; [exact FLHI|].
    split; [unfold qSF, sh, SHADOW_OFF; clear - FAL; Z.div_mod_to_equations; lia|].
    split; [unfold qSF, sh, SHADOW_OFF; clear - FLO B4; Z.div_mod_to_equations; lia|].
    split; [unfold qSF, sh, SHADOW_OFF in *; clear - FHI FLO B4; Z.div_mod_to_equations; lia|].
    split; [exact P1|]. split; [exact P3|].
    destruct PLB as (g & Hg & G1 & G2). pose proof (live_num FI st m0 RF0) as LN. rewrite Forall_forall in LN.
    destruct (LN g Hg) as (L1 & L2 & _). clear - G1 G2 L1 L2. lia.
  Qed.

  Definition elive (stc : fsstate FI) : Prop :=
    lb (fs_live FI stc) F 128 /\ ls (fs_live FI stc) SF 16 /\ lf (fs_live FI stc) FL /\ lb (fs_live FI stc) P 504
    /\ (forall g, In g (fs_live FI st) -> In g (fs_live FI stc)).
  #[using="q lo m0 POK RF0"] Lemma elive_of : forall stc, fs_live FI stc = fs_newff FI st 1 :: fs_live FI st -> elive stc.
  Proof.
    intros stc LIVE1. pose proof POK as POK'. pqokA POK'.
    destruct (new_frame_facts FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & _).
    assert (LSUB : forall g, In g (fs_live FI st) -> In g (fs_live FI stc)) by (intros g Hg; rewrite LIVE1; right; exact Hg).
    pose proof (lb_new _ _ _ LIVE1) as LVF. pose proof (ls_new _ _ _ LIVE1) as LVS. pose proof (lf_new _ _ _ LIVE1) as LVL.
    unfold ff_size, ff_shsize in LVF, LVS. rewrite FCLS in LVF, LVS. cbn [FB_of SB_of] in LVF, LVS.
    change (ff_addr (fs_newff FI st 1)) with F in LVF, LVS. change (ff_flag (fs_newff FI st 1)) with FL in LVL. change (sh F) with SF in LVS.
    split; [exact LVF|]. split; [exact LVS|]. split; [exact LVL|]. split; [exact (lb_mono _ _ _ _ PLB LSUB)| exact LSUB].
  Qed.
  #[using="Type"] Lemma pinv_rf : forall shd q' m, pinvQS shd q' m -> exists stc, RFAKE FI stc m /\ fs_live FI stc = fs_newff FI st 1 :: fs_live FI st.
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
    intros W q' HW. pose proof POK as POK'. pqokA POK'.
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
    pinvQS shd q' m -> fs_live FI stc = fs_newff FI st 1 :: fs_live FI st ->
    munch ((lo, q') :: FSIV W) m m' -> wmono asegs m m' -> fkeep FI W stc m m' ->
    fs_live FI st' = fs_live FI stc -> RFAKE FI st' m' ->
    stk asegs m' lo q' -> mem_inv asegs m' -> asan_env asegs m' ->
    Forall inW3 W ->
    (exists j, rw_cells asegs m' (F + 32) [CB 88 j]) ->
    pinvQS shd q' m'.
  Proof.
    intros shd HSZ W q' m m' stc st' (ST & (j0 & j160 & j192 & QC) & MI & AE & (QB & QAL) & VR) LIVE1 MUF WMF FKc LIVE' RF' ST' MI' AE' HW FT1'.
    destruct VR as (Hq & GAP & FRhi & (w0 & FH) & _ & FT2 & SHF & FLG & _).
    pose proof POK as POK'. pqokA POK'.
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
    unfold pinvQS, prestQ.
    split; [exact ST'|].
    split; [exists j0, j160, j192; eapply rw_cells_transport; [exact QC| exact MUF| exact WMF| apply DJS; [lia| simpl_sizes; lia]]|].
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
    /\ shw m P 504 /\ shw m A (cap + 1) /\ shw m SEPTAB_A 20 /\ shw m FMT_REQ09_A 10 /\ shw m FMT_REQ_A 22
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
    intros W q' HW. pose proof POK as POK'. pqokA POK'. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
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
    pctx A len cap cur bs m -> txt_okA A len cap -> q + -336 <= q' <= q + -320 ->
    RFAKE FI stc m -> fs_live FI stc = fs_newff FI st 1 :: fs_live FI st ->
    munch ((lo, q') :: FSIV W) m m' -> wmono asegs m m' -> fkeep FI W stc m m' ->
    Forall inW3 W -> disjoint_from W (P + 400) 32 -> disjoint_from W A (cap + 1) ->
    rw_cells asegs m' (P + 480) [C8 (wz (P + 400)); C8 (wz cur'); C4 (wz 0)] ->
    (exists ev', clow canary ev' m') ->
    pctx A len cap cur' bs m'.
  Proof.
    intros W q' A len cap cur cur' bs m m' stc (SC & MBC & TXT & SHP & SHA & SHSEP & SHF1 & SHF2 & SHZ & SHR & _ & SHE) TOK QB RF LIVE1 MUF WMF FKc HW DJM DJT SC' CLOW'.
    tokA TOK. pose proof POK as POK'. pqokA POK'.
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
    split; [apply (shw_frame_fs FI _ m m' FMT_REQ09_A 10 SHF1 MUF FW); left; clear - B1; lia|].
    split; [apply (shw_frame_fs FI _ m m' FMT_REQ_A 22 SHF2 MUF FW); left; clear - B1; lia|].
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
    tokA TOK. pose proof POK as POK'. pqokA POK'.
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
    elive stc -> q + -336 <= q' <= q + -320 -> q' mod 16 = 0 -> txt_okA A len cap -> Z.of_nat (length bs) = cap + 1 -> 0 <= cur <= len ->
    Forall (fun iv => inFJ iv \/ inER iv) Wx ->
    vf_okA FI q' lo (P + 480) (P + 400) A len cap cur bs stc Wx.
  Proof.
    intros q' A len cap cur bs stc Wx (LVF & LVS & LVL & LVP & LSUB) QB QAL TOK BL CR HWx.
    tokA TOK. pose proof POK as POK'. pqokA POK'. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
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
End PQ.
End W.
