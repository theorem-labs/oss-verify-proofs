(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac STRW_merge Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ALayout APrim APrimLem ATacA ACells LJ LJU PEnv ATacFix F_gct F_alloc_B AFsEnv AFake AFakeRep AFakeInst F_fs_tls.
Import ListNotations.
Open Scope Z_scope.

Ltac pc_is P :=
  lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) => let a := eval cbv in p in let b := eval cbv in P in constr_eq a b end.

Ltac zto P := repeat (tryif pc_is P then fail else zstep).

Ltac ret_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.

Ltac fold_frame Fv tac :=
  match goal with
  | |- context [Z_to_bv 64 ?E] =>
      lazymatch E with context [Z.shiftl _ _] => idtac end;
      lazymatch E with Z.shiftl _ _ => fail | _ => idtac end;
      replace E with Fv by tac
  end.

Ltac xstep := first [ zstep; lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => fail | _ => idtac end | sstep ].
Ltac xto P := repeat (tryif pc_is P then fail else xstep).

Lemma land_mask_mod : forall h e, 0 <= e <= 64 -> Z.land (h mod 18446744073709551616) (Z.ones e) = h mod 2^e.
Proof.
  intros h e He. rewrite Z.land_ones by lia. symmetry. apply Znumtheory.Zmod_div_mod; [lia| lia|].
  exists (2^(64 - e)). change 18446744073709551616 with (2^64). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Section LOOP0.
  Context {HC : HasCeiling}.
  Variable fsb : Z.
  Hypothesis FSB_OK : 0x609000 <= fsb /\ fsb + A0_FS_SIZE <= alloc_ceiling /\ app_mem fsb A0_FS_SIZE /\ fsb mod 4096 = 0
                      /\ (fsb + A0_FS_SIZE <= 0x7fff7000 \/ 0x10007fff8000 <= fsb).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (st : fstate) (m : mem).
  Hypothesis RF : RFAKE_B fsb st m.

  Definition loop0_post (h' : Z) : machine_state -> Prop :=
    fun ms' => exists a0', ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (wz (fsb + 4096)) (wz h') (wz 16383) a4 (wz (fsb + 4096 + h' mod 16384)) (wz (h' mod 16384)) (wz 0)
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F_ (wz 0x3ece4) fc None m (seg_rom asegs).

  #[using="HC FSB_OK RF"] Lemma loop0 : forall (n : nat) (h c : Z) (a5 a6 a7 : word),
    0 <= h -> Z.of_nat n < c <= 16384 -> ~ In (fprobe (lpos st 0) 16384 h n mod 16384) (lpos st 0) ->
    evt asegs (loop0_post (fprobe (lpos st 0) 16384 h n))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz c) (wz (fsb + 4096)) (wz h) (wz 16383) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x3ec6c) fc None m (seg_rom asegs)).
  Proof.
    assert (STEP : forall h, 0 <= h ->
              rw_cells asegs m (fsb + 4096 + h mod 16384) [C1 (if existsb (Z.eqb (h mod 16384)) (lpos st 0) then Z_to_bv 8 1 else Z_to_bv 8 0)]).
    { intros h H0. pose proof (flag_cell fsb FSB_OK st m 0 (h mod 16384) RF ltac:(lia) ltac:(cbn [fk_N]; apply Z.mod_pos_bound; lia)) as FC.
      unfold fk_flag in FC. cbn [fk_flags_off] in FC. rewrite Z.add_0_r in FC. exact FC. }
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR. pose proof FSB_OK as (B1 & B2 & _).
    assert (EXIT : forall h c (a5 a6 a7 : word), 0 <= h -> existsb (Z.eqb (h mod 16384)) (lpos st 0) = false ->
              evt asegs (loop0_post h)
                (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz c) (wz (fsb + 4096)) (wz h) (wz 16383) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F_ (wz 0x3ec6c) fc None m (seg_rom asegs))).
    { intros h c a5 a6 a7 H0 EX. pose proof (STEP h H0) as FC. rewrite EX in FC.
      zstep. zstep.
      change 16383 with (Z.ones 14). rewrite (land_mask_mod h 14) by lia. change (2^14) with 16384. change (Z.ones 14) with 16383.
      assert (PR : 0 <= h mod 16384 < 16384) by (apply Z.mod_pos_bound; lia).
      set (p := h mod 16384) in *. assert (Hp : p = h mod 16384) by reflexivity. clearbody p.
      set (fa := fsb + 4096 + p) in *. assert (Hfa : fa = fsb + 4096 + p) by reflexivity. clearbody fa.
      zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0.
      zstep. if_true.
      apply evt_done. unfold loop0_post. subst fa p. eexists. reflexivity. }
    induction n as [|n IH]; intros h c a5 a6 a7 H0 HCN NL.
    - cbn [fprobe] in *. apply EXIT; [exact H0|].
      destruct (existsb (Z.eqb (h mod 16384)) (lpos st 0)) eqn:EX; [apply existsb_eqb_in in EX; contradiction| reflexivity].
    - cbn [fprobe] in *. destruct (existsb (Z.eqb (h mod 16384)) (lpos st 0)) eqn:EX; [| apply EXIT; assumption].
      pose proof (STEP h H0) as FC. rewrite EX in FC.
      zstep. zstep.
      change 16383 with (Z.ones 14). rewrite (land_mask_mod h 14) by lia. change (2^14) with 16384. change (Z.ones 14) with 16383.
      assert (PR : 0 <= h mod 16384 < 16384) by (apply Z.mod_pos_bound; lia).
      set (p := h mod 16384) in *. assert (Hp : p = h mod 16384) by reflexivity. clearbody p.
      set (fa := fsb + 4096 + p) in *. assert (Hfa : fa = fsb + 4096 + p) by reflexivity. clearbody fa.
      zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 1)) with 1.
      zstep. if_false.
      zstep. zstep.
      rewrite (swrap32_small (c + -1)) by (clear - HCN; lia).
      zstep. if_cases KC; zify_cond KC. 2: { exfalso. clear - KC HCN. lia. } clear KC.
      apply (IH (h + 1) (c + -1)); [clear - H0; lia| clear - HCN; lia| exact NL].
  Qed.
End LOOP0.

Section SM0.
  Context {HC : HasCeiling}.
  Variable fsb : Z.
  Hypothesis FSB_OK : 0x609000 <= fsb /\ fsb + A0_FS_SIZE <= alloc_ceiling /\ app_mem fsb A0_FS_SIZE /\ fsb mod 4096 = 0
                      /\ (fsb + A0_FS_SIZE <= 0x7fff7000 \/ 0x10007fff8000 <= fsb).
  Variable TL : athread.
  Variable BLK : Z.

  Definition sm0_post (st : fstate) (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32)
      (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (junk1 junk2 : list byte),
      let g := snd (fst_malloc fsb st 0) in
      ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz (ff_addr g)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(fsb + 8 * 0, fsb + 8 * 0 + 8); (ff_flag g, ff_flag g + 1); (ff_addr g, ff_addr g + FB_of 0);
                (sh (ff_addr g), sh (ff_addr g) + SB_of 0); (lo, q)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ RFAKE_B fsb (fst (fst_malloc fsb st 0)) m'
      /\ rw_cells asegs m' (ff_addr g) [CB 24%nat junk1; C8 (wz q); CB 24%nat junk2; C8 (wz (ff_flag g))]
      /\ rw_cells asegs m' (sh (ff_addr g)) (shadow_zero_cells 8)
      /\ rw_cells asegs m' (ff_flag g) [C1 (Z_to_bv 8 1)]
      /\ stk asegs m' lo q.

  #[using="FSB_OK"] Lemma sm0_core : forall (st : fstate) (lo q : Z)
         (ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F_ : bvmap 5 word) (fc : bv 32) (m : mem),
    RFAKE_B fsb st m -> (length (ft_live st) < 15)%nat ->
    thread_env TL m -> thread_layout_ok TL -> fs_tls_env (at_thr TL) A0_DTV A0_TLSB BLK fsb m ->
    asan_env asegs m ->
    stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 208 -> q < 2^64 -> mem_inv asegs m ->
    evt asegs (sm0_post st ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc lo m)
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x3ebe8) fc None m (seg_rom asegs)).
  Proof.
    intros st lo q ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m
      RF LEN TE TLO FTE AE ST CLO LOQ QH MI.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_num fsb FSB_OK) as (F0 & FM & FSA). pose proof (fsb_num2 fsb FSB_OK) as (B2 & B2s & B3 & B4).
    pose proof RF as (WF & _).

    destruct (fst_probe_ok st 0 WF ltac:(lia)) as [NI PR]. cbv zeta in NI, PR. cbn [fk_N] in PR.
    assert (Eg : snd (fst_malloc fsb st 0) = ff_of fsb (0, fst_probe st 0 mod 16384)) by reflexivity.
    set (h1 := fst_probe st 0) in *. set (pos := h1 mod 16384) in *.
    destruct (slot_num fsb FSB_OK 0 pos ltac:(lia) PR) as (S1 & S2 & S3 & S4 & _). cbn [FB_of SB_of] in S2, S4.
    assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; pose proof ST as (S0 & _); lia).
    pose proof FTE as (RTG & DESC & DTVC & DTV1 & FSTLS & _). change (A0_TLSB - 2048) with 6187376 in FSTLS.
    hideB RTG. hideB DESC. hideB DTVC. hideB DTV1. hideB FSTLS.
    pose proof (munch_refl [(q - 208, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    rewrite <- EQ in ST. carve_frame 32%nat ST. rewrite !EQ in *.
    zstep. do 4 sstep. zstep. zstep. zstep. zstep. zstep.
    assert (STK : Forall (fun iv : Z * Z => alloc_ceiling <= fst iv) [(q - 208, q)]) by (repeat constructor; cbn [fst]; clear - CLO LOQ; lia).
    assert (THB : at_thr TL + 64 <= alloc_ceiling) by (pose proof TLO as (_ & _ & _ & TT2 & _); clear - TT2; lia).
    pose proof (thread_env_stack TL _ m m1 TE TLO MU WM STK) as TE1.
    pose proof (fs_tls_env_stack _ _ _ _ _ _ m m1 FTE THB MU WM STK) as FTE1.
    assert (AE1 : asan_env asegs m1).
    { eapply (asan_env_frame asegs); [exact AE| exact MU| exact WM|]. unfold env_safe. repeat (apply Forall_cons || apply Forall_nil). cbn [fst snd]. left. clear - CLO LOQ ACR. lia. }
    pose proof AE1 as (_ & _ & (_ & _ & EI1 & _ & _ & ECF1 & _)).
    eapply evt_cut.
    { eapply (tga_spec TL) with (lo := lo) (DTV := A0_DTV) (TLSB := A0_TLSB) (BLK := BLK) (FSB0 := fsb);
        [ exact CLO | clear - QH; lia | clear - LOQ; lia | exact ST | eassumption | exact EI1 | exact ECF1 | exact TE1 | exact TLO | exact FTE1 ]. }
    cbv beta. intros msT PT. unfold tga_post in PT. destruct PT as (v1 & v2 & v3 & v4 & v5 & v6 & v7 & m2 & -> & MU2 & WM2 & MI2 & ST2).
    eapply (rw_cells_transport asegs _ m1 m2) in FR; [| exact MU2| exact WM2| cbn [disjoint_from cells_size csize Nat.add]; clear; lia].
    apply (munch_trans _ m m1 m2) in MU; [| eapply (munch_weaken [(q + -32 - 176, q + -32)] _ m1 m2); [unfold sub_fp; intros xo_ Hxo_; cbn [outside] in *; clear - Hxo_; lia| exact MU2]].
    apply (wmono_trans asegs m m1 m2) in WM; [| exact WM2].
    clear TE1 FTE1 AE1 EI1 ECF1 MU2 WM2 ST.
    assert (RF2 : RFAKE_B fsb st m2).
    { eapply (rfake_B_frame fsb FSB_OK st m m2); [exact RF| exact MU| exact WM|]. apply Forall_cons; [| apply Forall_nil]. unfold rf_cls. left. cbn [fst snd]. clear - CLO LOQ B2 B2s. lia. }
    assert (AE2 : asan_env asegs m2).
    { eapply (asan_env_frame asegs); [exact AE| exact MU| exact WM|]. unfold env_safe. repeat (apply Forall_cons || apply Forall_nil). cbn [fst snd]. left. clear - CLO LOQ ACR. lia. }
    unhideB FSTLS. eapply (rw_cells_transport asegs _ m m2) in FSTLS; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; clear - CLO LOQ ACR; lia].
    replace (ret_pc (Z_to_bv 64 257036)) with (Z_to_bv 64 257036) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    change (6320424 - 2048) with 6318376.
    zstep.
    zstep. if_cases KZ; zify_cond KZ. { exfalso. clear - KZ FSB_OK ACR. lia. } clear KZ.
    pose proof RF2 as (_ & HCc & FLc & FREE). unfold hint_cells in HCc. hideB FLc.
    zstep. zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0.
    zstep. if_true.
    zstep. zstep. zstep. zstep.
    zstep. if_false.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    assert (H1E : fprobe (lpos st 0) 16384 (ft_hint st 0) (S (length (lpos st 0))) = h1) by reflexivity.
    assert (HH0 : 0 <= ft_hint st 0 < 2^64) by (destruct WF as (_ & _ & _ & HR); apply HR; lia).
    assert (LPL : (length (lpos st 0) < 16)%nat) by (pose proof (lpos_len st 0); destruct WF as (_ & _ & LL & _); lia).
    eapply evt_cut.
    { eapply (loop0 fsb FSB_OK) with (st := st) (n := S (length (lpos st 0))) (h := ft_hint st 0) (c := 16384);
        [ exact RF2 | clear - HH0; lia | clear - LPL; lia | rewrite H1E; intros HI; apply NI; apply lpos_in; exact HI ]. }
    cbv beta. intros msL PL. unfold loop0_post in PL. rewrite H1E in PL. destruct PL as (c' & ->). fold pos.
    pose proof (flag_cell fsb FSB_OK st m2 0 pos RF2 ltac:(lia) PR) as FLG.
    replace (existsb (Z.eqb pos) (lpos st 0)) with false in FLG
      by (symmetry; destruct (existsb (Z.eqb pos) (lpos st 0)) eqn:EX; [apply existsb_eqb_in, lpos_in in EX; contradiction| reflexivity]).
    destruct (FREE 0 pos ltac:(lia) PR NI) as ((jf & FRM) & (js & SHM)). cbn [FB_of SB_of] in FRM, SHM.
    change (Z.to_nat 64) with 64%nat in FRM. change (Z.to_nat 8) with 8%nat in SHM.
    assert (EFL : fk_flag fsb 0 pos = fsb + 4096 + pos) by (unfold fk_flag; cbn [fk_flags_off]; lia).
    assert (EFR : fk_frame fsb 0 pos = fsb + 36864 + pos * 64) by (unfold fk_frame; cbn [FB_of]; lia).
    rewrite EFL in FLG.
    set (fa := fsb + 4096 + pos) in *. assert (Hfa : fa = fsb + 4096 + pos) by reflexivity. clearbody fa.
    set (Fv := fk_frame fsb 0 pos) in *. assert (HFv : Fv = fsb + 36864 + pos * 64) by exact EFR. clearbody Fv.
    set (SFv := sh Fv) in *. assert (HSF : SFv = sh Fv) by reflexivity. clearbody SFv.
    apply (munch_weaken _ [(fsb, fsb + 8); (fa, fa + 1); (Fv, Fv + 64); (SFv, SFv + 8); (q - 208, q)]) in MU;
      [| unfold sub_fp; intros xo_ Hxo_; cbn [outside] in *; clear - Hxo_; tauto].
    clear FREE RF2.
    zstep. zstep. zstep. zstep.
    sstep. sstep.
    zstep. zstep. zstep.
    replace (fsb + 36864 + Z.shiftl pos 6) with Fv by (rewrite Z.shiftl_mul_pow2 by (clear; lia); change (2^6) with 64; clear - HFv; lia).
    sstep. sstep.
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mc end.
    assert (SAFE : env_safe [(fsb, fsb + 8); (fa, fa + 1); (Fv, Fv + 64); (SFv, SFv + 8); (q - 208, q)]).
    { unfold env_safe. repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; left; clear - FSB_OK Hfa PR S1 HSF B3 S3 CLO LOQ ACR; lia. }
    assert (AEc : asan_env asegs mc) by (eapply (asan_env_frame asegs); [exact AE| exact MU| exact WM| exact SAFE]).
    pose proof AEc as (_ & _ & (ESH & ELY & _)).
    eapply evt_cut.
    { eapply (m2s_spec) with (A := Fv); [exact ESH| exact ELY|]. pose proof FSB_OK as (_ & _ & AM & _). unfold app_mem in AM. clear - AM S1 S2. lia. }
    cbv beta. intros msM PM. unfold m2s_post in PM. destruct PM as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & ->).
    replace (ret_pc (Z_to_bv 64 257304)) with (Z_to_bv 64 257304) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    rewrite <- HSF.
    zstep. zstep. zstep.
    clear AEc ESH ELY.
    sstep.
    zstep. zstep. zstep. zstep. zstep.
    replace (q + -32 + 32) with q by (clear; lia).
    zstep.
    release_frame FR ST2 q.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mZ end.
    assert (EF1 : fk_frame fsb 0 pos = Fv) by (unfold fk_frame; cbn [FB_of]; clear - HFv; lia).
    assert (EF2 : fk_flag fsb 0 pos = fa) by (unfold fk_flag; cbn [fk_flags_off]; clear - Hfa; lia).
    assert (MUZ : munch [(fsb + 8 * 0, fsb + 8 * 0 + 8); (fa, fa + 1); (Fv, Fv + FB_of 0); (SFv, SFv + SB_of 0); (lo, q)] m mZ).
    { eapply munch_weaken; [| exact MU]. unfold sub_fp. intros xo_ Hxo_. cbn [outside FB_of SB_of] in *. clear - Hxo_ LOQ. lia. }
    apply evt_done. unfold sm0_post. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, mZ, _, _. cbv zeta.
    rewrite Eg. unfold ff_of. cbn [ff_addr ff_flag ff_class fst snd]. change (fst_probe st 0 mod 16384) with pos. rewrite EF1, EF2, <- HSF.
    split; [reflexivity|]. split; [exact MUZ|]. split; [exact WM|]. split; [assumption|].
    split.
    { pose proof (rfake_B_malloc fsb FSB_OK st 0 m mZ lo q RF ltac:(lia) LEN) as RM. cbv zeta in RM. rewrite Eg in RM.
      unfold ff_of in RM. cbn [ff_addr ff_flag ff_class fst snd] in RM. change (fst_probe st 0 mod 16384) with pos in RM. rewrite EF1, EF2, <- HSF in RM.
      apply RM; [exact MUZ| exact WM| exact CLO| | exact FLG].
      unfold hint_cells, fst_malloc. cbv zeta. cbn [fst ft_hint Z.eqb]. fold h1.
      rewrite (Z_to_bv_eqm ((h1 + 1) mod 2^64) (h1 + 1)) by (apply Zmod_mod). exact HCc. }
    split; [exact FRM|].
    split; [eapply rw_cells_rebytes; [exact SHM| cbn; tauto| reflexivity| reflexivity]|].
    split; [exact FLG| exact ST2].
  Qed.
End SM0.

Section LOOP1.
  Context {HC : HasCeiling}.
  Variable fsb : Z.
  Hypothesis FSB_OK : 0x609000 <= fsb /\ fsb + A0_FS_SIZE <= alloc_ceiling /\ app_mem fsb A0_FS_SIZE /\ fsb mod 4096 = 0
                      /\ (fsb + A0_FS_SIZE <= 0x7fff7000 \/ 0x10007fff8000 <= fsb).
  Variables (ra sp gp tp t1 t2 s0 s1 a1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (st : fstate) (m : mem).
  Hypothesis RF : RFAKE_B fsb st m.

  Definition loop1_post (h' : Z) : machine_state -> Prop :=
    fun ms' => exists a0', ms' = MS (mkR ra sp gp tp (wz 0) t1 t2 s0 s1 a0' a1 (wz h') (wz (fsb + 20480)) (wz 8191) (wz (fsb + 20480 + h' mod 8192)) a6 (wz (h' mod 8192))
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F_ (wz 0x3ee68) fc None m (seg_rom asegs).

  #[using="HC FSB_OK RF"] Lemma loop1 : forall (n : nat) (h c : Z) (t0 a5 a7 : word),
    0 <= h -> Z.of_nat n < c <= 8192 -> ~ In (fprobe (lpos st 1) 8192 h n mod 8192) (lpos st 1) ->
    evt asegs (loop1_post (fprobe (lpos st 1) 8192 h n))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz c) a1 (wz h) (wz (fsb + 20480)) (wz 8191) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x3edf0) fc None m (seg_rom asegs)).
  Proof.
    assert (STEP : forall h, 0 <= h ->
              rw_cells asegs m (fsb + 20480 + h mod 8192) [C1 (if existsb (Z.eqb (h mod 8192)) (lpos st 1) then Z_to_bv 8 1 else Z_to_bv 8 0)]).
    { intros h H0. pose proof (flag_cell fsb FSB_OK st m 1 (h mod 8192) RF ltac:(lia) ltac:(cbn [fk_N]; apply Z.mod_pos_bound; lia)) as FC.
      unfold fk_flag in FC. cbn [fk_flags_off] in FC. replace (fsb + 4096 + 16384 + h mod 8192) with (fsb + 20480 + h mod 8192) in FC by lia. exact FC. }
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR. pose proof FSB_OK as (B1 & B2 & _).
    assert (EXIT : forall h c (t0 a5 a7 : word), 0 <= h -> existsb (Z.eqb (h mod 8192)) (lpos st 1) = false ->
              evt asegs (loop1_post h)
                (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz c) a1 (wz h) (wz (fsb + 20480)) (wz 8191) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F_ (wz 0x3edf0) fc None m (seg_rom asegs))).
    { intros h c t0 a5 a7 H0 EX. pose proof (STEP h H0) as FC. rewrite EX in FC.
      zstep. zstep.
      change 8191 with (Z.ones 13). rewrite (land_mask_mod h 13) by lia. change (2^13) with 8192. change (Z.ones 13) with 8191.
      assert (PR : 0 <= h mod 8192 < 8192) by (apply Z.mod_pos_bound; lia).
      set (p := h mod 8192) in *. assert (Hp : p = h mod 8192) by reflexivity. clearbody p.
      set (fa := fsb + 20480 + p) in *. assert (Hfa : fa = fsb + 20480 + p) by reflexivity. clearbody fa.
      zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0.
      zstep. if_true.
      apply evt_done. unfold loop1_post. subst fa p. eexists. reflexivity. }
    induction n as [|n IH]; intros h c t0 a5 a7 H0 HCN NL.
    - cbn [fprobe] in *. apply EXIT; [exact H0|].
      destruct (existsb (Z.eqb (h mod 8192)) (lpos st 1)) eqn:EX; [apply existsb_eqb_in in EX; contradiction| reflexivity].
    - cbn [fprobe] in *. destruct (existsb (Z.eqb (h mod 8192)) (lpos st 1)) eqn:EX; [| apply EXIT; assumption].
      pose proof (STEP h H0) as FC. rewrite EX in FC.
      zstep. zstep.
      change 8191 with (Z.ones 13). rewrite (land_mask_mod h 13) by lia. change (2^13) with 8192. change (Z.ones 13) with 8191.
      assert (PR : 0 <= h mod 8192 < 8192) by (apply Z.mod_pos_bound; lia).
      set (p := h mod 8192) in *. assert (Hp : p = h mod 8192) by reflexivity. clearbody p.
      set (fa := fsb + 20480 + p) in *. assert (Hfa : fa = fsb + 20480 + p) by reflexivity. clearbody fa.
      zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 1)) with 1.
      zstep. if_false.
      zstep. zstep.
      rewrite (swrap32_small (c + -1)) by (clear - HCN; lia).
      zstep. if_cases KC; zify_cond KC. 2: { exfalso. clear - KC HCN. lia. } clear KC.
      apply (IH (h + 1) (c + -1)); [clear - H0; lia| clear - HCN; lia| exact NL].
  Qed.
End LOOP1.

Section SM1.
  Context {HC : HasCeiling}.
  Variable fsb : Z.
  Hypothesis FSB_OK : 0x609000 <= fsb /\ fsb + A0_FS_SIZE <= alloc_ceiling /\ app_mem fsb A0_FS_SIZE /\ fsb mod 4096 = 0
                      /\ (fsb + A0_FS_SIZE <= 0x7fff7000 \/ 0x10007fff8000 <= fsb).
  Variable TL : athread.
  Variable BLK : Z.

  Definition sm1_post (st : fstate) (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32)
      (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (junk1 junk2 : list byte),
      let g := snd (fst_malloc fsb st 1) in
      ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz (ff_addr g)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(fsb + 8 * 1, fsb + 8 * 1 + 8); (ff_flag g, ff_flag g + 1); (ff_addr g, ff_addr g + FB_of 1);
                (sh (ff_addr g), sh (ff_addr g) + SB_of 1); (lo, q)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ RFAKE_B fsb (fst (fst_malloc fsb st 1)) m'
      /\ rw_cells asegs m' (ff_addr g) [CB 24%nat junk1; C8 (wz q); CB 88%nat junk2; C8 (wz (ff_flag g))]
      /\ rw_cells asegs m' (sh (ff_addr g)) (shadow_zero_cells 16)
      /\ rw_cells asegs m' (ff_flag g) [C1 (Z_to_bv 8 1)]
      /\ stk asegs m' lo q.

  #[using="FSB_OK"] Lemma sm1_core : forall (st : fstate) (lo q : Z)
         (ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F_ : bvmap 5 word) (fc : bv 32) (m : mem),
    RFAKE_B fsb st m -> (length (ft_live st) < 15)%nat ->
    thread_env TL m -> thread_layout_ok TL -> fs_tls_env (at_thr TL) A0_DTV A0_TLSB BLK fsb m ->
    asan_env asegs m ->
    stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 208 -> q < 2^64 -> mem_inv asegs m ->
    evt asegs (sm1_post st ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc lo m)
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x3ed5c) fc None m (seg_rom asegs)).
  Proof.
    intros st lo q ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m
      RF LEN TE TLO FTE AE ST CLO LOQ QH MI.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_num fsb FSB_OK) as (F0 & FM & FSA). pose proof (fsb_num2 fsb FSB_OK) as (B2 & B2s & B3 & B4).
    pose proof RF as (WF & _).
    destruct (fst_probe_ok st 1 WF ltac:(lia)) as [NI PR]. cbv zeta in NI, PR. cbn [fk_N] in PR.
    assert (Eg : snd (fst_malloc fsb st 1) = ff_of fsb (1, fst_probe st 1 mod 8192)) by reflexivity.
    set (h1 := fst_probe st 1) in *. set (pos := h1 mod 8192) in *.
    destruct (slot_num fsb FSB_OK 1 pos ltac:(lia) PR) as (S1 & S2 & S3 & S4 & _). cbn [FB_of SB_of] in S2, S4.
    assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; pose proof ST as (S0 & _); lia).
    pose proof FTE as (RTG & DESC & DTVC & DTV1 & FSTLS & _). change (A0_TLSB - 2048) with 6187376 in FSTLS.
    hideB RTG. hideB DESC. hideB DTVC. hideB DTV1. hideB FSTLS.
    pose proof (munch_refl [(q - 208, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    rewrite <- EQ in ST. carve_frame 32%nat ST. rewrite !EQ in *.
    zstep. do 4 sstep. zto 0x4aeac.
    assert (STK : Forall (fun iv : Z * Z => alloc_ceiling <= fst iv) [(q - 208, q)]) by (repeat constructor; cbn [fst]; clear - CLO LOQ; lia).
    assert (THB : at_thr TL + 64 <= alloc_ceiling) by (pose proof TLO as (_ & _ & _ & TT2 & _); clear - TT2; lia).
    pose proof (thread_env_stack TL _ m m1 TE TLO MU WM STK) as TE1.
    pose proof (fs_tls_env_stack _ _ _ _ _ _ m m1 FTE THB MU WM STK) as FTE1.
    assert (AE1 : asan_env asegs m1).
    { eapply (asan_env_frame asegs); [exact AE| exact MU| exact WM|]. unfold env_safe. repeat (apply Forall_cons || apply Forall_nil). cbn [fst snd]. left. clear - CLO LOQ ACR. lia. }
    pose proof AE1 as (_ & _ & (_ & _ & EI1 & _ & _ & ECF1 & _)).
    eapply evt_cut.
    { eapply (tga_spec TL) with (lo := lo) (DTV := A0_DTV) (TLSB := A0_TLSB) (BLK := BLK) (FSB0 := fsb);
        [ exact CLO | clear - QH; lia | clear - LOQ; lia | exact ST | eassumption | exact EI1 | exact ECF1 | exact TE1 | exact TLO | exact FTE1 ]. }
    cbv beta. intros msT PT. unfold tga_post in PT. destruct PT as (v1 & v2 & v3 & v4 & v5 & v6 & v7 & m2 & -> & MU2 & WM2 & MI2 & ST2).
    eapply (rw_cells_transport asegs _ m1 m2) in FR; [| exact MU2| exact WM2| cbn [disjoint_from cells_size csize Nat.add]; clear; lia].
    apply (munch_trans _ m m1 m2) in MU; [| eapply (munch_weaken [(q + -32 - 176, q + -32)] _ m1 m2); [unfold sub_fp; intros xo_ Hxo_; cbn [outside] in *; clear - Hxo_; lia| exact MU2]].
    apply (wmono_trans asegs m m1 m2) in WM; [| exact WM2].
    clear TE1 FTE1 AE1 EI1 ECF1 MU2 WM2 ST.
    assert (RF2 : RFAKE_B fsb st m2).
    { eapply (rfake_B_frame fsb FSB_OK st m m2); [exact RF| exact MU| exact WM|]. apply Forall_cons; [| apply Forall_nil]. unfold rf_cls. left. cbn [fst snd]. clear - CLO LOQ B2 B2s. lia. }
    unhideB FSTLS. eapply (rw_cells_transport asegs _ m m2) in FSTLS; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; clear - CLO LOQ ACR; lia].
    ret_lit. change (6320424 - 2048) with 6318376.
    zstep.
    zstep. if_cases KZ; zify_cond KZ. { exfalso. clear - KZ FSB_OK ACR. lia. } clear KZ.
    pose proof RF2 as (_ & HCc & FLc & FREE). unfold hint_cells in HCc. hideB FLc.
    zstep. zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0.
    zstep. if_true.
    zstep. zstep. zstep. zstep.
    zstep. if_false.
    zto 0x3edf0.
    assert (H1E : fprobe (lpos st 1) 8192 (ft_hint st 1) (S (length (lpos st 1))) = h1) by reflexivity.
    assert (HH0 : 0 <= ft_hint st 1 < 2^64) by (destruct WF as (_ & _ & _ & HR); apply HR; lia).
    assert (LPL : (length (lpos st 1) < 16)%nat) by (pose proof (lpos_len st 1); destruct WF as (_ & _ & LL & _); lia).
    eapply evt_cut.
    { eapply (loop1 fsb FSB_OK) with (st := st) (n := S (length (lpos st 1))) (h := ft_hint st 1) (c := 8192);
        [ exact RF2 | clear - HH0; lia | clear - LPL; lia | rewrite H1E; intros HI; apply NI; apply lpos_in; exact HI ]. }
    cbv beta. intros msL PL. unfold loop1_post in PL. rewrite H1E in PL. destruct PL as (c' & ->). fold pos.
    pose proof (flag_cell fsb FSB_OK st m2 1 pos RF2 ltac:(lia) PR) as FLG.
    replace (existsb (Z.eqb pos) (lpos st 1)) with false in FLG
      by (symmetry; destruct (existsb (Z.eqb pos) (lpos st 1)) eqn:EX; [apply existsb_eqb_in, lpos_in in EX; contradiction| reflexivity]).
    destruct (FREE 1 pos ltac:(lia) PR NI) as ((jf & FRM) & (js & SHM)). cbn [FB_of SB_of] in FRM, SHM.
    change (Z.to_nat 128) with 128%nat in FRM. change (Z.to_nat 16) with 16%nat in SHM.
    assert (EFL : fk_flag fsb 1 pos = fsb + 20480 + pos) by (unfold fk_flag; cbn [fk_flags_off]; lia).
    assert (EFR : fk_frame fsb 1 pos = fsb + 1085440 + pos * 128) by (unfold fk_frame; cbn [FB_of]; lia).
    rewrite EFL in FLG.
    set (fa := fsb + 20480 + pos) in *. assert (Hfa : fa = fsb + 20480 + pos) by reflexivity. clearbody fa.
    set (Fv := fk_frame fsb 1 pos) in *. assert (HFv : Fv = fsb + 1085440 + pos * 128) by exact EFR. clearbody Fv.
    set (SFv := sh Fv) in *. assert (HSF : SFv = sh Fv) by reflexivity. clearbody SFv.
    apply (munch_weaken _ [(fsb + 8, fsb + 8 + 8); (fa, fa + 1); (Fv, Fv + 128); (SFv, SFv + 16); (q - 208, q)]) in MU;
      [| unfold sub_fp; intros xo_ Hxo_; cbn [outside] in *; clear - Hxo_; tauto].
    clear FREE RF2.
    xto 0x3ee94.
    fold_frame Fv ltac:(rewrite ?Z.shiftl_mul_pow2 by (clear; lia); change (2^7) with 128; clear - HFv; lia).
    xto 0x3f400.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mc end.
    assert (SAFE : env_safe [(fsb + 8, fsb + 8 + 8); (fa, fa + 1); (Fv, Fv + 128); (SFv, SFv + 16); (q - 208, q)]).
    { unfold env_safe. repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; left; clear - FSB_OK Hfa PR S1 HSF B3 S3 CLO LOQ ACR; lia. }
    assert (AEc : asan_env asegs mc) by (eapply (asan_env_frame asegs); [exact AE| exact MU| exact WM| exact SAFE]).
    pose proof AEc as (_ & _ & (ESH & ELY & _)).
    eapply evt_cut.
    { eapply (m2s_spec) with (A := Fv); [exact ESH| exact ELY|]. pose proof FSB_OK as (_ & _ & AM & _). unfold app_mem in AM. clear - AM S1 S2. lia. }
    cbv beta. intros msM PM. unfold m2s_post in PM. destruct PM as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & ->).
    ret_lit. rewrite <- HSF.
    zstep. zstep. zstep.
    clear AEc ESH ELY.
    sstep. sstep.
    zstep. zstep. zstep. zstep. zstep.
    replace (q + -32 + 32) with q by (clear; lia).
    zstep.
    release_frame FR ST2 q.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mZ end.
    assert (EF1 : fk_frame fsb 1 pos = Fv) by (unfold fk_frame; cbn [FB_of]; clear - HFv; lia).
    assert (EF2 : fk_flag fsb 1 pos = fa) by (unfold fk_flag; cbn [fk_flags_off]; clear - Hfa; lia).
    assert (MUZ : munch [(fsb + 8 * 1, fsb + 8 * 1 + 8); (fa, fa + 1); (Fv, Fv + FB_of 1); (SFv, SFv + SB_of 1); (lo, q)] m mZ).
    { eapply munch_weaken; [| exact MU]. unfold sub_fp. intros xo_ Hxo_. cbn [outside FB_of SB_of] in *. clear - Hxo_ LOQ. lia. }
    apply evt_done. unfold sm1_post. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, mZ, _, _. cbv zeta.
    rewrite Eg. unfold ff_of. cbn [ff_addr ff_flag ff_class fst snd]. change (fst_probe st 1 mod 8192) with pos. rewrite EF1, EF2, <- HSF.
    split; [reflexivity|]. split; [exact MUZ|]. split; [exact WM|]. split; [assumption|].
    split.
    { pose proof (rfake_B_malloc fsb FSB_OK st 1 m mZ lo q RF ltac:(lia) LEN) as RM. cbv zeta in RM. rewrite Eg in RM.
      unfold ff_of in RM. cbn [ff_addr ff_flag ff_class fst snd] in RM. change (fst_probe st 1 mod 8192) with pos in RM. rewrite EF1, EF2, <- HSF in RM.
      apply RM; [exact MUZ| exact WM| exact CLO| | exact FLG].
      unfold hint_cells, fst_malloc. cbv zeta. cbn [fst ft_hint Z.eqb Pos.eqb]. fold h1.
      rewrite (Z_to_bv_eqm ((h1 + 1) mod 2^64) (h1 + 1)) by (apply Zmod_mod). exact HCc. }
    split; [exact FRM|].
    split; [eapply rw_cells_rebytes; [exact SHM| cbn; tauto| reflexivity| reflexivity]|].
    split; [exact FLG| exact ST2].
  Qed.
End SM1.

Section LOOP2.
  Context {HC : HasCeiling}.
  Variable fsb : Z.
  Hypothesis FSB_OK : 0x609000 <= fsb /\ fsb + A0_FS_SIZE <= alloc_ceiling /\ app_mem fsb A0_FS_SIZE /\ fsb mod 4096 = 0
                      /\ (fsb + A0_FS_SIZE <= 0x7fff7000 \/ 0x10007fff8000 <= fsb).
  Variables (ra sp gp tp t1 t2 s0 s1 a1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (st : fstate) (m : mem).
  Hypothesis RF : RFAKE_B fsb st m.

  Definition loop2_post (h' : Z) : machine_state -> Prop :=
    fun ms' => exists a0', ms' = MS (mkR ra sp gp tp (wz 0) t1 t2 s0 s1 a0' a1 (wz h') (wz (fsb + 28672)) (wz 4095) (wz (fsb + 28672 + h' mod 4096)) a6 (wz (h' mod 4096))
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F_ (wz 0x3eff8) fc None m (seg_rom asegs).

  #[using="HC FSB_OK RF"] Lemma loop2 : forall (n : nat) (h c : Z) (t0 a5 a7 : word),
    0 <= h -> Z.of_nat n < c <= 4096 -> ~ In (fprobe (lpos st 2) 4096 h n mod 4096) (lpos st 2) ->
    evt asegs (loop2_post (fprobe (lpos st 2) 4096 h n))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz c) a1 (wz h) (wz (fsb + 28672)) (wz 4095) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x3ef80) fc None m (seg_rom asegs)).
  Proof.
    assert (STEP : forall h, 0 <= h ->
              rw_cells asegs m (fsb + 28672 + h mod 4096) [C1 (if existsb (Z.eqb (h mod 4096)) (lpos st 2) then Z_to_bv 8 1 else Z_to_bv 8 0)]).
    { intros h H0. pose proof (flag_cell fsb FSB_OK st m 2 (h mod 4096) RF ltac:(lia) ltac:(cbn [fk_N]; apply Z.mod_pos_bound; lia)) as FC.
      unfold fk_flag in FC. cbn [fk_flags_off] in FC. replace (fsb + 4096 + 24576 + h mod 4096) with (fsb + 28672 + h mod 4096) in FC by lia. exact FC. }
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR. pose proof FSB_OK as (B1 & B2 & _).
    assert (EXIT : forall h c (t0 a5 a7 : word), 0 <= h -> existsb (Z.eqb (h mod 4096)) (lpos st 2) = false ->
              evt asegs (loop2_post h)
                (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz c) a1 (wz h) (wz (fsb + 28672)) (wz 4095) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F_ (wz 0x3ef80) fc None m (seg_rom asegs))).
    { intros h c t0 a5 a7 H0 EX. pose proof (STEP h H0) as FC. rewrite EX in FC.
      zstep. zstep.
      change 4095 with (Z.ones 12). rewrite (land_mask_mod h 12) by lia. change (2^12) with 4096. change (Z.ones 12) with 4095.
      assert (PR : 0 <= h mod 4096 < 4096) by (apply Z.mod_pos_bound; lia).
      set (p := h mod 4096) in *. assert (Hp : p = h mod 4096) by reflexivity. clearbody p.
      set (fa := fsb + 28672 + p) in *. assert (Hfa : fa = fsb + 28672 + p) by reflexivity. clearbody fa.
      zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0.
      zstep. if_true.
      apply evt_done. unfold loop2_post. subst fa p. eexists. reflexivity. }
    induction n as [|n IH]; intros h c t0 a5 a7 H0 HCN NL.
    - cbn [fprobe] in *. apply EXIT; [exact H0|].
      destruct (existsb (Z.eqb (h mod 4096)) (lpos st 2)) eqn:EX; [apply existsb_eqb_in in EX; contradiction| reflexivity].
    - cbn [fprobe] in *. destruct (existsb (Z.eqb (h mod 4096)) (lpos st 2)) eqn:EX; [| apply EXIT; assumption].
      pose proof (STEP h H0) as FC. rewrite EX in FC.
      zstep. zstep.
      change 4095 with (Z.ones 12). rewrite (land_mask_mod h 12) by lia. change (2^12) with 4096. change (Z.ones 12) with 4095.
      assert (PR : 0 <= h mod 4096 < 4096) by (apply Z.mod_pos_bound; lia).
      set (p := h mod 4096) in *. assert (Hp : p = h mod 4096) by reflexivity. clearbody p.
      set (fa := fsb + 28672 + p) in *. assert (Hfa : fa = fsb + 28672 + p) by reflexivity. clearbody fa.
      zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 1)) with 1.
      zstep. if_false.
      zstep. zstep.
      rewrite (swrap32_small (c + -1)) by (clear - HCN; lia).
      zstep. if_cases KC; zify_cond KC. 2: { exfalso. clear - KC HCN. lia. } clear KC.
      apply (IH (h + 1) (c + -1)); [clear - H0; lia| clear - HCN; lia| exact NL].
  Qed.
End LOOP2.

Section SM2.
  Context {HC : HasCeiling}.
  Variable fsb : Z.
  Hypothesis FSB_OK : 0x609000 <= fsb /\ fsb + A0_FS_SIZE <= alloc_ceiling /\ app_mem fsb A0_FS_SIZE /\ fsb mod 4096 = 0
                      /\ (fsb + A0_FS_SIZE <= 0x7fff7000 \/ 0x10007fff8000 <= fsb).
  Variable TL : athread.
  Variable BLK : Z.

  Definition sm2_post (st : fstate) (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32)
      (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (junk1 junk2 : list byte),
      let g := snd (fst_malloc fsb st 2) in
      ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz (ff_addr g)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(fsb + 8 * 2, fsb + 8 * 2 + 8); (ff_flag g, ff_flag g + 1); (ff_addr g, ff_addr g + FB_of 2);
                (sh (ff_addr g), sh (ff_addr g) + SB_of 2); (lo, q)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ RFAKE_B fsb (fst (fst_malloc fsb st 2)) m'
      /\ rw_cells asegs m' (ff_addr g) [CB 24%nat junk1; C8 (wz q); CB 216%nat junk2; C8 (wz (ff_flag g))]
      /\ rw_cells asegs m' (sh (ff_addr g)) (shadow_zero_cells 32)
      /\ rw_cells asegs m' (ff_flag g) [C1 (Z_to_bv 8 1)]
      /\ stk asegs m' lo q.

  #[using="FSB_OK"] Lemma sm2_core : forall (st : fstate) (lo q : Z)
         (ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F_ : bvmap 5 word) (fc : bv 32) (m : mem),
    RFAKE_B fsb st m -> (length (ft_live st) < 15)%nat ->
    thread_env TL m -> thread_layout_ok TL -> fs_tls_env (at_thr TL) A0_DTV A0_TLSB BLK fsb m ->
    asan_env asegs m ->
    stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 208 -> q < 2^64 -> mem_inv asegs m ->
    evt asegs (sm2_post st ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc lo m)
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x3eeec) fc None m (seg_rom asegs)).
  Proof.
    intros st lo q ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m
      RF LEN TE TLO FTE AE ST CLO LOQ QH MI.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_num fsb FSB_OK) as (F0 & FM & FSA). pose proof (fsb_num2 fsb FSB_OK) as (B2 & B2s & B3 & B4).
    pose proof RF as (WF & _).
    destruct (fst_probe_ok st 2 WF ltac:(lia)) as [NI PR]. cbv zeta in NI, PR. cbn [fk_N] in PR.
    assert (Eg : snd (fst_malloc fsb st 2) = ff_of fsb (2, fst_probe st 2 mod 4096)) by reflexivity.
    set (h1 := fst_probe st 2) in *. set (pos := h1 mod 4096) in *.
    destruct (slot_num fsb FSB_OK 2 pos ltac:(lia) PR) as (S1 & S2 & S3 & S4 & _). cbn [FB_of SB_of] in S2, S4.
    assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; pose proof ST as (S0 & _); lia).
    pose proof FTE as (RTG & DESC & DTVC & DTV1 & FSTLS & _). change (A0_TLSB - 2048) with 6187376 in FSTLS.
    hideB RTG. hideB DESC. hideB DTVC. hideB DTV1. hideB FSTLS.
    pose proof (munch_refl [(q - 208, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    rewrite <- EQ in ST. carve_frame 32%nat ST. rewrite !EQ in *.
    zstep. do 4 sstep. zto 0x4aeac.
    assert (STK : Forall (fun iv : Z * Z => alloc_ceiling <= fst iv) [(q - 208, q)]) by (repeat constructor; cbn [fst]; clear - CLO LOQ; lia).
    assert (THB : at_thr TL + 64 <= alloc_ceiling) by (pose proof TLO as (_ & _ & _ & TT2 & _); clear - TT2; lia).
    pose proof (thread_env_stack TL _ m m1 TE TLO MU WM STK) as TE1.
    pose proof (fs_tls_env_stack _ _ _ _ _ _ m m1 FTE THB MU WM STK) as FTE1.
    assert (AE1 : asan_env asegs m1).
    { eapply (asan_env_frame asegs); [exact AE| exact MU| exact WM|]. unfold env_safe. repeat (apply Forall_cons || apply Forall_nil). cbn [fst snd]. left. clear - CLO LOQ ACR. lia. }
    pose proof AE1 as (_ & _ & (_ & _ & EI1 & _ & _ & ECF1 & _)).
    eapply evt_cut.
    { eapply (tga_spec TL) with (lo := lo) (DTV := A0_DTV) (TLSB := A0_TLSB) (BLK := BLK) (FSB0 := fsb);
        [ exact CLO | clear - QH; lia | clear - LOQ; lia | exact ST | eassumption | exact EI1 | exact ECF1 | exact TE1 | exact TLO | exact FTE1 ]. }
    cbv beta. intros msT PT. unfold tga_post in PT. destruct PT as (v1 & v2 & v3 & v4 & v5 & v6 & v7 & m2 & -> & MU2 & WM2 & MI2 & ST2).
    eapply (rw_cells_transport asegs _ m1 m2) in FR; [| exact MU2| exact WM2| cbn [disjoint_from cells_size csize Nat.add]; clear; lia].
    apply (munch_trans _ m m1 m2) in MU; [| eapply (munch_weaken [(q + -32 - 176, q + -32)] _ m1 m2); [unfold sub_fp; intros xo_ Hxo_; cbn [outside] in *; clear - Hxo_; lia| exact MU2]].
    apply (wmono_trans asegs m m1 m2) in WM; [| exact WM2].
    clear TE1 FTE1 AE1 EI1 ECF1 MU2 WM2 ST.
    assert (RF2 : RFAKE_B fsb st m2).
    { eapply (rfake_B_frame fsb FSB_OK st m m2); [exact RF| exact MU| exact WM|]. apply Forall_cons; [| apply Forall_nil]. unfold rf_cls. left. cbn [fst snd]. clear - CLO LOQ B2 B2s. lia. }
    unhideB FSTLS. eapply (rw_cells_transport asegs _ m m2) in FSTLS; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; clear - CLO LOQ ACR; lia].
    ret_lit. change (6320424 - 2048) with 6318376.
    zstep.
    zstep. if_cases KZ; zify_cond KZ. { exfalso. clear - KZ FSB_OK ACR. lia. } clear KZ.
    pose proof RF2 as (_ & HCc & FLc & FREE). unfold hint_cells in HCc. hideB FLc.
    zstep. zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0.
    zstep. if_true.
    zstep. zstep. zstep. zstep.
    zstep. if_false.
    zto 0x3ef80.
    assert (H1E : fprobe (lpos st 2) 4096 (ft_hint st 2) (S (length (lpos st 2))) = h1) by reflexivity.
    assert (HH0 : 0 <= ft_hint st 2 < 2^64) by (destruct WF as (_ & _ & _ & HR); apply HR; lia).
    assert (LPL : (length (lpos st 2) < 16)%nat) by (pose proof (lpos_len st 2); destruct WF as (_ & _ & LL & _); lia).
    eapply evt_cut.
    { eapply (loop2 fsb FSB_OK) with (st := st) (n := S (length (lpos st 2))) (h := ft_hint st 2) (c := 4096);
        [ exact RF2 | clear - HH0; lia | clear - LPL; lia | rewrite H1E; intros HI; apply NI; apply lpos_in; exact HI ]. }
    cbv beta. intros msL PL. unfold loop2_post in PL. rewrite H1E in PL. destruct PL as (c' & ->). fold pos.
    pose proof (flag_cell fsb FSB_OK st m2 2 pos RF2 ltac:(lia) PR) as FLG.
    replace (existsb (Z.eqb pos) (lpos st 2)) with false in FLG
      by (symmetry; destruct (existsb (Z.eqb pos) (lpos st 2)) eqn:EX; [apply existsb_eqb_in, lpos_in in EX; contradiction| reflexivity]).
    destruct (FREE 2 pos ltac:(lia) PR NI) as ((jf & FRM) & (js & SHM)). cbn [FB_of SB_of] in FRM, SHM.
    change (Z.to_nat 256) with 256%nat in FRM. change (Z.to_nat 32) with 32%nat in SHM.
    assert (EFL : fk_flag fsb 2 pos = fsb + 28672 + pos) by (unfold fk_flag; cbn [fk_flags_off]; lia).
    assert (EFR : fk_frame fsb 2 pos = fsb + 2134016 + pos * 256) by (unfold fk_frame; cbn [FB_of]; lia).
    rewrite EFL in FLG.
    set (fa := fsb + 28672 + pos) in *. assert (Hfa : fa = fsb + 28672 + pos) by reflexivity. clearbody fa.
    set (Fv := fk_frame fsb 2 pos) in *. assert (HFv : Fv = fsb + 2134016 + pos * 256) by exact EFR. clearbody Fv.
    set (SFv := sh Fv) in *. assert (HSF : SFv = sh Fv) by reflexivity. clearbody SFv.
    apply (munch_weaken _ [(fsb + 16, fsb + 16 + 8); (fa, fa + 1); (Fv, Fv + 256); (SFv, SFv + 32); (q - 208, q)]) in MU;
      [| unfold sub_fp; intros xo_ Hxo_; cbn [outside] in *; clear - Hxo_; tauto].
    clear FREE RF2.
    xto 0x3f028.
    fold_frame Fv ltac:(rewrite ?Z.shiftl_mul_pow2 by (clear; lia); change (2^8) with 256; clear - HFv; lia).
    xto 0x3f400.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mc end.
    assert (SAFE : env_safe [(fsb + 16, fsb + 16 + 8); (fa, fa + 1); (Fv, Fv + 256); (SFv, SFv + 32); (q - 208, q)]).
    { unfold env_safe. repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; left; clear - FSB_OK Hfa PR S1 HSF B3 S3 CLO LOQ ACR; lia. }
    assert (AEc : asan_env asegs mc) by (eapply (asan_env_frame asegs); [exact AE| exact MU| exact WM| exact SAFE]).
    pose proof AEc as (_ & _ & (ESH & ELY & _)).
    eapply evt_cut.
    { eapply (m2s_spec) with (A := Fv); [exact ESH| exact ELY|]. pose proof FSB_OK as (_ & _ & AM & _). unfold app_mem in AM. clear - AM S1 S2. lia. }
    cbv beta. intros msM PM. unfold m2s_post in PM. destruct PM as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & ->).
    ret_lit. rewrite <- HSF.
    zstep. zstep. zstep.
    clear AEc ESH ELY.
    sstep. sstep. sstep. sstep.
    zstep. zstep. zstep. zstep. zstep.
    replace (q + -32 + 32) with q by (clear; lia).
    zstep.
    release_frame FR ST2 q.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mZ end.
    assert (EF1 : fk_frame fsb 2 pos = Fv) by (unfold fk_frame; cbn [FB_of]; clear - HFv; lia).
    assert (EF2 : fk_flag fsb 2 pos = fa) by (unfold fk_flag; cbn [fk_flags_off]; clear - Hfa; lia).
    assert (MUZ : munch [(fsb + 8 * 2, fsb + 8 * 2 + 8); (fa, fa + 1); (Fv, Fv + FB_of 2); (SFv, SFv + SB_of 2); (lo, q)] m mZ).
    { eapply munch_weaken; [| exact MU]. unfold sub_fp. intros xo_ Hxo_. cbn [outside FB_of SB_of] in *. clear - Hxo_ LOQ. lia. }
    apply evt_done. unfold sm2_post. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, mZ, _, _. cbv zeta.
    rewrite Eg. unfold ff_of. cbn [ff_addr ff_flag ff_class fst snd]. change (fst_probe st 2 mod 4096) with pos. rewrite EF1, EF2, <- HSF.
    split; [reflexivity|]. split; [exact MUZ|]. split; [exact WM|]. split; [assumption|].
    split.
    { pose proof (rfake_B_malloc fsb FSB_OK st 2 m mZ lo q RF ltac:(lia) LEN) as RM. cbv zeta in RM. rewrite Eg in RM.
      unfold ff_of in RM. cbn [ff_addr ff_flag ff_class fst snd] in RM. change (fst_probe st 2 mod 4096) with pos in RM. rewrite EF1, EF2, <- HSF in RM.
      apply RM; [exact MUZ| exact WM| exact CLO| | exact FLG].
      unfold hint_cells, fst_malloc. cbv zeta. cbn [fst ft_hint Z.eqb Pos.eqb]. fold h1.
      rewrite (Z_to_bv_eqm ((h1 + 1) mod 2^64) (h1 + 1)) by (apply Zmod_mod). exact HCc. }
    split; [exact FRM|].
    split; [eapply rw_cells_rebytes; [exact SHM| cbn; tauto| reflexivity| reflexivity]|].
    split; [exact FLG| exact ST2].
  Qed.
End SM2.

Section LOOP3.
  Context {HC : HasCeiling}.
  Variable fsb : Z.
  Hypothesis FSB_OK : 0x609000 <= fsb /\ fsb + A0_FS_SIZE <= alloc_ceiling /\ app_mem fsb A0_FS_SIZE /\ fsb mod 4096 = 0
                      /\ (fsb + A0_FS_SIZE <= 0x7fff7000 \/ 0x10007fff8000 <= fsb).
  Variables (ra sp gp tp t1 t2 s0 s1 a1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (st : fstate) (m : mem).
  Hypothesis RF : RFAKE_B fsb st m.

  Definition loop3_post (h' : Z) : machine_state -> Prop :=
    fun ms' => exists a0', ms' = MS (mkR ra sp gp tp (wz 0) t1 t2 s0 s1 a0' a1 (wz h') (wz (fsb + 32768)) (wz 2047) (wz (fsb + 32768 + h' mod 2048)) a6 (wz (h' mod 2048))
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F_ (wz 0x3f194) fc None m (seg_rom asegs).

  #[using="HC FSB_OK RF"] Lemma loop3 : forall (n : nat) (h c : Z) (t0 a5 a7 : word),
    0 <= h -> Z.of_nat n < c <= 2048 -> ~ In (fprobe (lpos st 3) 2048 h n mod 2048) (lpos st 3) ->
    evt asegs (loop3_post (fprobe (lpos st 3) 2048 h n))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz c) a1 (wz h) (wz (fsb + 32768)) (wz 2047) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x3f11c) fc None m (seg_rom asegs)).
  Proof.
    assert (STEP : forall h, 0 <= h ->
              rw_cells asegs m (fsb + 32768 + h mod 2048) [C1 (if existsb (Z.eqb (h mod 2048)) (lpos st 3) then Z_to_bv 8 1 else Z_to_bv 8 0)]).
    { intros h H0. pose proof (flag_cell fsb FSB_OK st m 3 (h mod 2048) RF ltac:(lia) ltac:(cbn [fk_N]; apply Z.mod_pos_bound; lia)) as FC.
      unfold fk_flag in FC. cbn [fk_flags_off] in FC. replace (fsb + 4096 + 28672 + h mod 2048) with (fsb + 32768 + h mod 2048) in FC by lia. exact FC. }
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR. pose proof FSB_OK as (B1 & B2 & _).
    assert (EXIT : forall h c (t0 a5 a7 : word), 0 <= h -> existsb (Z.eqb (h mod 2048)) (lpos st 3) = false ->
              evt asegs (loop3_post h)
                (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz c) a1 (wz h) (wz (fsb + 32768)) (wz 2047) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F_ (wz 0x3f11c) fc None m (seg_rom asegs))).
    { intros h c t0 a5 a7 H0 EX. pose proof (STEP h H0) as FC. rewrite EX in FC.
      zstep. zstep.
      change 2047 with (Z.ones 11). rewrite (land_mask_mod h 11) by lia. change (2^11) with 2048. change (Z.ones 11) with 2047.
      assert (PR : 0 <= h mod 2048 < 2048) by (apply Z.mod_pos_bound; lia).
      set (p := h mod 2048) in *. assert (Hp : p = h mod 2048) by reflexivity. clearbody p.
      set (fa := fsb + 32768 + p) in *. assert (Hfa : fa = fsb + 32768 + p) by reflexivity. clearbody fa.
      zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0.
      zstep. if_true.
      apply evt_done. unfold loop3_post. subst fa p. eexists. reflexivity. }
    induction n as [|n IH]; intros h c t0 a5 a7 H0 HCN NL.
    - cbn [fprobe] in *. apply EXIT; [exact H0|].
      destruct (existsb (Z.eqb (h mod 2048)) (lpos st 3)) eqn:EX; [apply existsb_eqb_in in EX; contradiction| reflexivity].
    - cbn [fprobe] in *. destruct (existsb (Z.eqb (h mod 2048)) (lpos st 3)) eqn:EX; [| apply EXIT; assumption].
      pose proof (STEP h H0) as FC. rewrite EX in FC.
      zstep. zstep.
      change 2047 with (Z.ones 11). rewrite (land_mask_mod h 11) by lia. change (2^11) with 2048. change (Z.ones 11) with 2047.
      assert (PR : 0 <= h mod 2048 < 2048) by (apply Z.mod_pos_bound; lia).
      set (p := h mod 2048) in *. assert (Hp : p = h mod 2048) by reflexivity. clearbody p.
      set (fa := fsb + 32768 + p) in *. assert (Hfa : fa = fsb + 32768 + p) by reflexivity. clearbody fa.
      zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 1)) with 1.
      zstep. if_false.
      zstep. zstep.
      rewrite (swrap32_small (c + -1)) by (clear - HCN; lia).
      zstep. if_cases KC; zify_cond KC. 2: { exfalso. clear - KC HCN. lia. } clear KC.
      apply (IH (h + 1) (c + -1)); [clear - H0; lia| clear - HCN; lia| exact NL].
  Qed.
End LOOP3.

Section SM3.
  Context {HC : HasCeiling}.
  Variable fsb : Z.
  Hypothesis FSB_OK : 0x609000 <= fsb /\ fsb + A0_FS_SIZE <= alloc_ceiling /\ app_mem fsb A0_FS_SIZE /\ fsb mod 4096 = 0
                      /\ (fsb + A0_FS_SIZE <= 0x7fff7000 \/ 0x10007fff8000 <= fsb).
  Variable TL : athread.
  Variable BLK : Z.

  Definition sm3_post (st : fstate) (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32)
      (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (junk1 junk2 : list byte),
      let g := snd (fst_malloc fsb st 3) in
      ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz (ff_addr g)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(fsb + 8 * 3, fsb + 8 * 3 + 8); (ff_flag g, ff_flag g + 1); (ff_addr g, ff_addr g + FB_of 3);
                (sh (ff_addr g), sh (ff_addr g) + SB_of 3); (lo, q)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ RFAKE_B fsb (fst (fst_malloc fsb st 3)) m'
      /\ rw_cells asegs m' (ff_addr g) [CB 24%nat junk1; C8 (wz q); CB 472%nat junk2; C8 (wz (ff_flag g))]
      /\ rw_cells asegs m' (sh (ff_addr g)) (shadow_zero_cells 64)
      /\ rw_cells asegs m' (ff_flag g) [C1 (Z_to_bv 8 1)]
      /\ stk asegs m' lo q.

  #[using="FSB_OK"] Lemma sm3_core : forall (st : fstate) (lo q : Z)
         (ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F_ : bvmap 5 word) (fc : bv 32) (m : mem),
    RFAKE_B fsb st m -> (length (ft_live st) < 15)%nat ->
    thread_env TL m -> thread_layout_ok TL -> fs_tls_env (at_thr TL) A0_DTV A0_TLSB BLK fsb m ->
    asan_env asegs m ->
    stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 208 -> q < 2^64 -> mem_inv asegs m ->
    evt asegs (sm3_post st ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc lo m)
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x3f088) fc None m (seg_rom asegs)).
  Proof.
    intros st lo q ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m
      RF LEN TE TLO FTE AE ST CLO LOQ QH MI.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_num fsb FSB_OK) as (F0 & FM & FSA). pose proof (fsb_num2 fsb FSB_OK) as (B2 & B2s & B3 & B4).
    pose proof RF as (WF & _).
    destruct (fst_probe_ok st 3 WF ltac:(lia)) as [NI PR]. cbv zeta in NI, PR. cbn [fk_N] in PR.
    assert (Eg : snd (fst_malloc fsb st 3) = ff_of fsb (3, fst_probe st 3 mod 2048)) by reflexivity.
    set (h1 := fst_probe st 3) in *. set (pos := h1 mod 2048) in *.
    destruct (slot_num fsb FSB_OK 3 pos ltac:(lia) PR) as (S1 & S2 & S3 & S4 & _). cbn [FB_of SB_of] in S2, S4.
    assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; pose proof ST as (S0 & _); lia).
    pose proof FTE as (RTG & DESC & DTVC & DTV1 & FSTLS & _). change (A0_TLSB - 2048) with 6187376 in FSTLS.
    hideB RTG. hideB DESC. hideB DTVC. hideB DTV1. hideB FSTLS.
    pose proof (munch_refl [(q - 208, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    rewrite <- EQ in ST. carve_frame 32%nat ST. rewrite !EQ in *.
    zstep. do 4 sstep. zto 0x4aeac.
    assert (STK : Forall (fun iv : Z * Z => alloc_ceiling <= fst iv) [(q - 208, q)]) by (repeat constructor; cbn [fst]; clear - CLO LOQ; lia).
    assert (THB : at_thr TL + 64 <= alloc_ceiling) by (pose proof TLO as (_ & _ & _ & TT2 & _); clear - TT2; lia).
    pose proof (thread_env_stack TL _ m m1 TE TLO MU WM STK) as TE1.
    pose proof (fs_tls_env_stack _ _ _ _ _ _ m m1 FTE THB MU WM STK) as FTE1.
    assert (AE1 : asan_env asegs m1).
    { eapply (asan_env_frame asegs); [exact AE| exact MU| exact WM|]. unfold env_safe. repeat (apply Forall_cons || apply Forall_nil). cbn [fst snd]. left. clear - CLO LOQ ACR. lia. }
    pose proof AE1 as (_ & _ & (_ & _ & EI1 & _ & _ & ECF1 & _)).
    eapply evt_cut.
    { eapply (tga_spec TL) with (lo := lo) (DTV := A0_DTV) (TLSB := A0_TLSB) (BLK := BLK) (FSB0 := fsb);
        [ exact CLO | clear - QH; lia | clear - LOQ; lia | exact ST | eassumption | exact EI1 | exact ECF1 | exact TE1 | exact TLO | exact FTE1 ]. }
    cbv beta. intros msT PT. unfold tga_post in PT. destruct PT as (v1 & v2 & v3 & v4 & v5 & v6 & v7 & m2 & -> & MU2 & WM2 & MI2 & ST2).
    eapply (rw_cells_transport asegs _ m1 m2) in FR; [| exact MU2| exact WM2| cbn [disjoint_from cells_size csize Nat.add]; clear; lia].
    apply (munch_trans _ m m1 m2) in MU; [| eapply (munch_weaken [(q + -32 - 176, q + -32)] _ m1 m2); [unfold sub_fp; intros xo_ Hxo_; cbn [outside] in *; clear - Hxo_; lia| exact MU2]].
    apply (wmono_trans asegs m m1 m2) in WM; [| exact WM2].
    clear TE1 FTE1 AE1 EI1 ECF1 MU2 WM2 ST.
    assert (RF2 : RFAKE_B fsb st m2).
    { eapply (rfake_B_frame fsb FSB_OK st m m2); [exact RF| exact MU| exact WM|]. apply Forall_cons; [| apply Forall_nil]. unfold rf_cls. left. cbn [fst snd]. clear - CLO LOQ B2 B2s. lia. }
    unhideB FSTLS. eapply (rw_cells_transport asegs _ m m2) in FSTLS; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; clear - CLO LOQ ACR; lia].
    ret_lit. change (6320424 - 2048) with 6318376.
    zstep.
    zstep. if_cases KZ; zify_cond KZ. { exfalso. clear - KZ FSB_OK ACR. lia. } clear KZ.
    pose proof RF2 as (_ & HCc & FLc & FREE). unfold hint_cells in HCc. hideB FLc.
    zstep. zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0.
    zstep. if_true.
    zstep. zstep. zstep. zstep.
    zstep. if_false.
    zto 0x3f11c.
    assert (H1E : fprobe (lpos st 3) 2048 (ft_hint st 3) (S (length (lpos st 3))) = h1) by reflexivity.
    assert (HH0 : 0 <= ft_hint st 3 < 2^64) by (destruct WF as (_ & _ & _ & HR); apply HR; lia).
    assert (LPL : (length (lpos st 3) < 16)%nat) by (pose proof (lpos_len st 3); destruct WF as (_ & _ & LL & _); lia).
    eapply evt_cut.
    { eapply (loop3 fsb FSB_OK) with (st := st) (n := S (length (lpos st 3))) (h := ft_hint st 3) (c := 2048);
        [ exact RF2 | clear - HH0; lia | clear - LPL; lia | rewrite H1E; intros HI; apply NI; apply lpos_in; exact HI ]. }
    cbv beta. intros msL PL. unfold loop3_post in PL. rewrite H1E in PL. destruct PL as (c' & ->). fold pos.
    pose proof (flag_cell fsb FSB_OK st m2 3 pos RF2 ltac:(lia) PR) as FLG.
    replace (existsb (Z.eqb pos) (lpos st 3)) with false in FLG
      by (symmetry; destruct (existsb (Z.eqb pos) (lpos st 3)) eqn:EX; [apply existsb_eqb_in, lpos_in in EX; contradiction| reflexivity]).
    destruct (FREE 3 pos ltac:(lia) PR NI) as ((jf & FRM) & (js & SHM)). cbn [FB_of SB_of] in FRM, SHM.
    change (Z.to_nat 512) with 512%nat in FRM. change (Z.to_nat 64) with 64%nat in SHM.
    assert (EFL : fk_flag fsb 3 pos = fsb + 32768 + pos) by (unfold fk_flag; cbn [fk_flags_off]; lia).
    assert (EFR : fk_frame fsb 3 pos = fsb + 3182592 + pos * 512) by (unfold fk_frame; cbn [FB_of]; lia).
    rewrite EFL in FLG.
    set (fa := fsb + 32768 + pos) in *. assert (Hfa : fa = fsb + 32768 + pos) by reflexivity. clearbody fa.
    set (Fv := fk_frame fsb 3 pos) in *. assert (HFv : Fv = fsb + 3182592 + pos * 512) by exact EFR. clearbody Fv.
    set (SFv := sh Fv) in *. assert (HSF : SFv = sh Fv) by reflexivity. clearbody SFv.
    apply (munch_weaken _ [(fsb + 24, fsb + 24 + 8); (fa, fa + 1); (Fv, Fv + 512); (SFv, SFv + 64); (q - 208, q)]) in MU;
      [| unfold sub_fp; intros xo_ Hxo_; cbn [outside] in *; clear - Hxo_; tauto].
    clear FREE RF2.
    xto 0x3f1c4.
    fold_frame Fv ltac:(rewrite ?Z.shiftl_mul_pow2 by (clear; lia); change (2^9) with 512; clear - HFv; lia).
    xto 0x3f400.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mc end.
    assert (SAFE : env_safe [(fsb + 24, fsb + 24 + 8); (fa, fa + 1); (Fv, Fv + 512); (SFv, SFv + 64); (q - 208, q)]).
    { unfold env_safe. repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; left; clear - FSB_OK Hfa PR S1 HSF B3 S3 CLO LOQ ACR; lia. }
    assert (AEc : asan_env asegs mc) by (eapply (asan_env_frame asegs); [exact AE| exact MU| exact WM| exact SAFE]).
    pose proof AEc as (_ & _ & (ESH & ELY & _)).
    eapply evt_cut.
    { eapply (m2s_spec) with (A := Fv); [exact ESH| exact ELY|]. pose proof FSB_OK as (_ & _ & AM & _). unfold app_mem in AM. clear - AM S1 S2. lia. }
    cbv beta. intros msM PM. unfold m2s_post in PM. destruct PM as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & ->).
    ret_lit. rewrite <- HSF.
    zstep. zstep. zstep.
    clear AEc ESH ELY.
    sstep. sstep. sstep. sstep. sstep. sstep. sstep. sstep.
    zstep. zstep. zstep. zstep. zstep.
    replace (q + -32 + 32) with q by (clear; lia).
    zstep.
    release_frame FR ST2 q.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mZ end.
    assert (EF1 : fk_frame fsb 3 pos = Fv) by (unfold fk_frame; cbn [FB_of]; clear - HFv; lia).
    assert (EF2 : fk_flag fsb 3 pos = fa) by (unfold fk_flag; cbn [fk_flags_off]; clear - Hfa; lia).
    assert (MUZ : munch [(fsb + 8 * 3, fsb + 8 * 3 + 8); (fa, fa + 1); (Fv, Fv + FB_of 3); (SFv, SFv + SB_of 3); (lo, q)] m mZ).
    { eapply munch_weaken; [| exact MU]. unfold sub_fp. intros xo_ Hxo_. cbn [outside FB_of SB_of] in *. clear - Hxo_ LOQ. lia. }
    apply evt_done. unfold sm3_post. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, mZ, _, _. cbv zeta.
    rewrite Eg. unfold ff_of. cbn [ff_addr ff_flag ff_class fst snd]. change (fst_probe st 3 mod 2048) with pos. rewrite EF1, EF2, <- HSF.
    split; [reflexivity|]. split; [exact MUZ|]. split; [exact WM|]. split; [assumption|].
    split.
    { pose proof (rfake_B_malloc fsb FSB_OK st 3 m mZ lo q RF ltac:(lia) LEN) as RM. cbv zeta in RM. rewrite Eg in RM.
      unfold ff_of in RM. cbn [ff_addr ff_flag ff_class fst snd] in RM. change (fst_probe st 3 mod 2048) with pos in RM. rewrite EF1, EF2, <- HSF in RM.
      apply RM; [exact MUZ| exact WM| exact CLO| | exact FLG].
      unfold hint_cells, fst_malloc. cbv zeta. cbn [fst ft_hint Z.eqb Pos.eqb]. fold h1.
      rewrite (Z_to_bv_eqm ((h1 + 1) mod 2^64) (h1 + 1)) by (apply Zmod_mod). exact HCc. }
    split; [exact FRM|].
    split; [eapply rw_cells_rebytes; [exact SHM| cbn; tauto| reflexivity| reflexivity]|].
    split; [exact FLG| exact ST2].
  Qed.
End SM3.

Section LOOP4.
  Context {HC : HasCeiling}.
  Variable fsb : Z.
  Hypothesis FSB_OK : 0x609000 <= fsb /\ fsb + A0_FS_SIZE <= alloc_ceiling /\ app_mem fsb A0_FS_SIZE /\ fsb mod 4096 = 0
                      /\ (fsb + A0_FS_SIZE <= 0x7fff7000 \/ 0x10007fff8000 <= fsb).
  Variables (ra sp gp tp t1 t2 s0 s1 a1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (st : fstate) (m : mem).
  Hypothesis RF : RFAKE_B fsb st m.

  Definition loop4_post (h' : Z) : machine_state -> Prop :=
    fun ms' => exists a0', ms' = MS (mkR ra sp gp tp (wz 0) t1 t2 s0 s1 a0' a1 (wz h') (wz (fsb + 34816)) (wz 1023) (wz (fsb + 34816 + h' mod 1024)) a6 (wz (h' mod 1024))
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F_ (wz 0x3f340) fc None m (seg_rom asegs).

  #[using="HC FSB_OK RF"] Lemma loop4 : forall (n : nat) (h c : Z) (t0 a5 a7 : word),
    0 <= h -> Z.of_nat n < c <= 1024 -> ~ In (fprobe (lpos st 4) 1024 h n mod 1024) (lpos st 4) ->
    evt asegs (loop4_post (fprobe (lpos st 4) 1024 h n))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz c) a1 (wz h) (wz (fsb + 34816)) (wz 1023) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x3f2c8) fc None m (seg_rom asegs)).
  Proof.
    assert (STEP : forall h, 0 <= h ->
              rw_cells asegs m (fsb + 34816 + h mod 1024) [C1 (if existsb (Z.eqb (h mod 1024)) (lpos st 4) then Z_to_bv 8 1 else Z_to_bv 8 0)]).
    { intros h H0. pose proof (flag_cell fsb FSB_OK st m 4 (h mod 1024) RF ltac:(lia) ltac:(cbn [fk_N]; apply Z.mod_pos_bound; lia)) as FC.
      unfold fk_flag in FC. cbn [fk_flags_off] in FC. replace (fsb + 4096 + 30720 + h mod 1024) with (fsb + 34816 + h mod 1024) in FC by lia. exact FC. }
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR. pose proof FSB_OK as (B1 & B2 & _).
    assert (EXIT : forall h c (t0 a5 a7 : word), 0 <= h -> existsb (Z.eqb (h mod 1024)) (lpos st 4) = false ->
              evt asegs (loop4_post h)
                (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz c) a1 (wz h) (wz (fsb + 34816)) (wz 1023) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F_ (wz 0x3f2c8) fc None m (seg_rom asegs))).
    { intros h c t0 a5 a7 H0 EX. pose proof (STEP h H0) as FC. rewrite EX in FC.
      zstep. zstep.
      change 1023 with (Z.ones 10). rewrite (land_mask_mod h 10) by lia. change (2^10) with 1024. change (Z.ones 10) with 1023.
      assert (PR : 0 <= h mod 1024 < 1024) by (apply Z.mod_pos_bound; lia).
      set (p := h mod 1024) in *. assert (Hp : p = h mod 1024) by reflexivity. clearbody p.
      set (fa := fsb + 34816 + p) in *. assert (Hfa : fa = fsb + 34816 + p) by reflexivity. clearbody fa.
      zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0.
      zstep. if_true.
      apply evt_done. unfold loop4_post. subst fa p. eexists. reflexivity. }
    induction n as [|n IH]; intros h c t0 a5 a7 H0 HCN NL.
    - cbn [fprobe] in *. apply EXIT; [exact H0|].
      destruct (existsb (Z.eqb (h mod 1024)) (lpos st 4)) eqn:EX; [apply existsb_eqb_in in EX; contradiction| reflexivity].
    - cbn [fprobe] in *. destruct (existsb (Z.eqb (h mod 1024)) (lpos st 4)) eqn:EX; [| apply EXIT; assumption].
      pose proof (STEP h H0) as FC. rewrite EX in FC.
      zstep. zstep.
      change 1023 with (Z.ones 10). rewrite (land_mask_mod h 10) by lia. change (2^10) with 1024. change (Z.ones 10) with 1023.
      assert (PR : 0 <= h mod 1024 < 1024) by (apply Z.mod_pos_bound; lia).
      set (p := h mod 1024) in *. assert (Hp : p = h mod 1024) by reflexivity. clearbody p.
      set (fa := fsb + 34816 + p) in *. assert (Hfa : fa = fsb + 34816 + p) by reflexivity. clearbody fa.
      zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 1)) with 1.
      zstep. if_false.
      zstep. zstep.
      rewrite (swrap32_small (c + -1)) by (clear - HCN; lia).
      zstep. if_cases KC; zify_cond KC. 2: { exfalso. clear - KC HCN. lia. } clear KC.
      apply (IH (h + 1) (c + -1)); [clear - H0; lia| clear - HCN; lia| exact NL].
  Qed.
End LOOP4.

Section SM4.
  Context {HC : HasCeiling}.
  Variable fsb : Z.
  Hypothesis FSB_OK : 0x609000 <= fsb /\ fsb + A0_FS_SIZE <= alloc_ceiling /\ app_mem fsb A0_FS_SIZE /\ fsb mod 4096 = 0
                      /\ (fsb + A0_FS_SIZE <= 0x7fff7000 \/ 0x10007fff8000 <= fsb).
  Variable TL : athread.
  Variable BLK : Z.

  Definition sm4_post (st : fstate) (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32)
      (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (junk1 junk2 : list byte),
      let g := snd (fst_malloc fsb st 4) in
      ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz (ff_addr g)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(fsb + 8 * 4, fsb + 8 * 4 + 8); (ff_flag g, ff_flag g + 1); (ff_addr g, ff_addr g + FB_of 4);
                (sh (ff_addr g), sh (ff_addr g) + SB_of 4); (lo, q)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ RFAKE_B fsb (fst (fst_malloc fsb st 4)) m'
      /\ rw_cells asegs m' (ff_addr g) [CB 24%nat junk1; C8 (wz q); CB 984%nat junk2; C8 (wz (ff_flag g))]
      /\ rw_cells asegs m' (sh (ff_addr g)) (shadow_zero_cells 128)
      /\ rw_cells asegs m' (ff_flag g) [C1 (Z_to_bv 8 1)]
      /\ stk asegs m' lo q.

  #[using="FSB_OK"] Lemma sm4_core : forall (st : fstate) (lo q : Z)
         (ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F_ : bvmap 5 word) (fc : bv 32) (m : mem),
    RFAKE_B fsb st m -> (length (ft_live st) < 15)%nat ->
    thread_env TL m -> thread_layout_ok TL -> fs_tls_env (at_thr TL) A0_DTV A0_TLSB BLK fsb m ->
    asan_env asegs m ->
    stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 208 -> q < 2^64 -> mem_inv asegs m ->
    evt asegs (sm4_post st ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc lo m)
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x3f234) fc None m (seg_rom asegs)).
  Proof.
    intros st lo q ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m
      RF LEN TE TLO FTE AE ST CLO LOQ QH MI.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_num fsb FSB_OK) as (F0 & FM & FSA). pose proof (fsb_num2 fsb FSB_OK) as (B2 & B2s & B3 & B4).
    pose proof RF as (WF & _).
    destruct (fst_probe_ok st 4 WF ltac:(lia)) as [NI PR]. cbv zeta in NI, PR. cbn [fk_N] in PR.
    assert (Eg : snd (fst_malloc fsb st 4) = ff_of fsb (4, fst_probe st 4 mod 1024)) by reflexivity.
    set (h1 := fst_probe st 4) in *. set (pos := h1 mod 1024) in *.
    destruct (slot_num fsb FSB_OK 4 pos ltac:(lia) PR) as (S1 & S2 & S3 & S4 & _). cbn [FB_of SB_of] in S2, S4.
    assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; pose proof ST as (S0 & _); lia).
    pose proof FTE as (RTG & DESC & DTVC & DTV1 & FSTLS & _). change (A0_TLSB - 2048) with 6187376 in FSTLS.
    hideB RTG. hideB DESC. hideB DTVC. hideB DTV1. hideB FSTLS.
    pose proof (munch_refl [(q - 208, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    rewrite <- EQ in ST. carve_frame 32%nat ST. rewrite !EQ in *.
    zstep. do 4 sstep. zto 0x4aeac.
    assert (STK : Forall (fun iv : Z * Z => alloc_ceiling <= fst iv) [(q - 208, q)]) by (repeat constructor; cbn [fst]; clear - CLO LOQ; lia).
    assert (THB : at_thr TL + 64 <= alloc_ceiling) by (pose proof TLO as (_ & _ & _ & TT2 & _); clear - TT2; lia).
    pose proof (thread_env_stack TL _ m m1 TE TLO MU WM STK) as TE1.
    pose proof (fs_tls_env_stack _ _ _ _ _ _ m m1 FTE THB MU WM STK) as FTE1.
    assert (AE1 : asan_env asegs m1).
    { eapply (asan_env_frame asegs); [exact AE| exact MU| exact WM|]. unfold env_safe. repeat (apply Forall_cons || apply Forall_nil). cbn [fst snd]. left. clear - CLO LOQ ACR. lia. }
    pose proof AE1 as (_ & _ & (_ & _ & EI1 & _ & _ & ECF1 & _)).
    eapply evt_cut.
    { eapply (tga_spec TL) with (lo := lo) (DTV := A0_DTV) (TLSB := A0_TLSB) (BLK := BLK) (FSB0 := fsb);
        [ exact CLO | clear - QH; lia | clear - LOQ; lia | exact ST | eassumption | exact EI1 | exact ECF1 | exact TE1 | exact TLO | exact FTE1 ]. }
    cbv beta. intros msT PT. unfold tga_post in PT. destruct PT as (v1 & v2 & v3 & v4 & v5 & v6 & v7 & m2 & -> & MU2 & WM2 & MI2 & ST2).
    eapply (rw_cells_transport asegs _ m1 m2) in FR; [| exact MU2| exact WM2| cbn [disjoint_from cells_size csize Nat.add]; clear; lia].
    apply (munch_trans _ m m1 m2) in MU; [| eapply (munch_weaken [(q + -32 - 176, q + -32)] _ m1 m2); [unfold sub_fp; intros xo_ Hxo_; cbn [outside] in *; clear - Hxo_; lia| exact MU2]].
    apply (wmono_trans asegs m m1 m2) in WM; [| exact WM2].
    clear TE1 FTE1 AE1 EI1 ECF1 MU2 WM2 ST.
    assert (RF2 : RFAKE_B fsb st m2).
    { eapply (rfake_B_frame fsb FSB_OK st m m2); [exact RF| exact MU| exact WM|]. apply Forall_cons; [| apply Forall_nil]. unfold rf_cls. left. cbn [fst snd]. clear - CLO LOQ B2 B2s. lia. }
    unhideB FSTLS. eapply (rw_cells_transport asegs _ m m2) in FSTLS; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; clear - CLO LOQ ACR; lia].
    ret_lit. change (6320424 - 2048) with 6318376.
    zstep.
    zstep. if_cases KZ; zify_cond KZ. { exfalso. clear - KZ FSB_OK ACR. lia. } clear KZ.
    pose proof RF2 as (_ & HCc & FLc & FREE). unfold hint_cells in HCc. hideB FLc.
    zstep. zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0.
    zstep. if_true.
    zstep. zstep. zstep. zstep.
    zstep. if_false.
    zto 0x3f2c8.
    assert (H1E : fprobe (lpos st 4) 1024 (ft_hint st 4) (S (length (lpos st 4))) = h1) by reflexivity.
    assert (HH0 : 0 <= ft_hint st 4 < 2^64) by (destruct WF as (_ & _ & _ & HR); apply HR; lia).
    assert (LPL : (length (lpos st 4) < 16)%nat) by (pose proof (lpos_len st 4); destruct WF as (_ & _ & LL & _); lia).
    eapply evt_cut.
    { eapply (loop4 fsb FSB_OK) with (st := st) (n := S (length (lpos st 4))) (h := ft_hint st 4) (c := 1024);
        [ exact RF2 | clear - HH0; lia | clear - LPL; lia | rewrite H1E; intros HI; apply NI; apply lpos_in; exact HI ]. }
    cbv beta. intros msL PL. unfold loop4_post in PL. rewrite H1E in PL. destruct PL as (c' & ->). fold pos.
    pose proof (flag_cell fsb FSB_OK st m2 4 pos RF2 ltac:(lia) PR) as FLG.
    replace (existsb (Z.eqb pos) (lpos st 4)) with false in FLG
      by (symmetry; destruct (existsb (Z.eqb pos) (lpos st 4)) eqn:EX; [apply existsb_eqb_in, lpos_in in EX; contradiction| reflexivity]).
    destruct (FREE 4 pos ltac:(lia) PR NI) as ((jf & FRM) & (js & SHM)). cbn [FB_of SB_of] in FRM, SHM.
    change (Z.to_nat 1024) with 1024%nat in FRM. change (Z.to_nat 128) with 128%nat in SHM.
    assert (EFL : fk_flag fsb 4 pos = fsb + 34816 + pos) by (unfold fk_flag; cbn [fk_flags_off]; lia).
    assert (EFR : fk_frame fsb 4 pos = fsb + 4231168 + pos * 1024) by (unfold fk_frame; cbn [FB_of]; lia).
    rewrite EFL in FLG.
    set (fa := fsb + 34816 + pos) in *. assert (Hfa : fa = fsb + 34816 + pos) by reflexivity. clearbody fa.
    set (Fv := fk_frame fsb 4 pos) in *. assert (HFv : Fv = fsb + 4231168 + pos * 1024) by exact EFR. clearbody Fv.
    set (SFv := sh Fv) in *. assert (HSF : SFv = sh Fv) by reflexivity. clearbody SFv.
    apply (munch_weaken _ [(fsb + 32, fsb + 32 + 8); (fa, fa + 1); (Fv, Fv + 1024); (SFv, SFv + 128); (q - 208, q)]) in MU;
      [| unfold sub_fp; intros xo_ Hxo_; cbn [outside] in *; clear - Hxo_; tauto].
    clear FREE RF2.
    xto 0x3f370.
    fold_frame Fv ltac:(rewrite ?Z.shiftl_mul_pow2 by (clear; lia); change (2^10) with 1024; clear - HFv; lia).
    xto 0x3f400.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mc end.
    assert (SAFE : env_safe [(fsb + 32, fsb + 32 + 8); (fa, fa + 1); (Fv, Fv + 1024); (SFv, SFv + 128); (q - 208, q)]).
    { unfold env_safe. repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; left; clear - FSB_OK Hfa PR S1 HSF B3 S3 CLO LOQ ACR; lia. }
    assert (AEc : asan_env asegs mc) by (eapply (asan_env_frame asegs); [exact AE| exact MU| exact WM| exact SAFE]).
    pose proof AEc as (_ & _ & (ESH & ELY & _)).
    eapply evt_cut.
    { eapply (m2s_spec) with (A := Fv); [exact ESH| exact ELY|]. pose proof FSB_OK as (_ & _ & AM & _). unfold app_mem in AM. clear - AM S1 S2. lia. }
    cbv beta. intros msM PM. unfold m2s_post in PM. destruct PM as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & ->).
    ret_lit. rewrite <- HSF.
    zstep. zstep. zstep.
    clear AEc ESH ELY.
    sstep. sstep. sstep. sstep. sstep. sstep. sstep. sstep. sstep. sstep. sstep. sstep. sstep. sstep. sstep. sstep.
    zstep. zstep. zstep. zstep. zstep.
    replace (q + -32 + 32) with q by (clear; lia).
    zstep.
    release_frame FR ST2 q.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mZ end.
    assert (EF1 : fk_frame fsb 4 pos = Fv) by (unfold fk_frame; cbn [FB_of]; clear - HFv; lia).
    assert (EF2 : fk_flag fsb 4 pos = fa) by (unfold fk_flag; cbn [fk_flags_off]; clear - Hfa; lia).
    assert (MUZ : munch [(fsb + 8 * 4, fsb + 8 * 4 + 8); (fa, fa + 1); (Fv, Fv + FB_of 4); (SFv, SFv + SB_of 4); (lo, q)] m mZ).
    { eapply munch_weaken; [| exact MU]. unfold sub_fp. intros xo_ Hxo_. cbn [outside FB_of SB_of] in *. clear - Hxo_ LOQ. lia. }
    apply evt_done. unfold sm4_post. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, mZ, _, _. cbv zeta.
    rewrite Eg. unfold ff_of. cbn [ff_addr ff_flag ff_class fst snd]. change (fst_probe st 4 mod 1024) with pos. rewrite EF1, EF2, <- HSF.
    split; [reflexivity|]. split; [exact MUZ|]. split; [exact WM|]. split; [assumption|].
    split.
    { pose proof (rfake_B_malloc fsb FSB_OK st 4 m mZ lo q RF ltac:(lia) LEN) as RM. cbv zeta in RM. rewrite Eg in RM.
      unfold ff_of in RM. cbn [ff_addr ff_flag ff_class fst snd] in RM. change (fst_probe st 4 mod 1024) with pos in RM. rewrite EF1, EF2, <- HSF in RM.
      apply RM; [exact MUZ| exact WM| exact CLO| | exact FLG].
      unfold hint_cells, fst_malloc. cbv zeta. cbn [fst ft_hint Z.eqb Pos.eqb]. fold h1.
      rewrite (Z_to_bv_eqm ((h1 + 1) mod 2^64) (h1 + 1)) by (apply Zmod_mod). exact HCc. }
    split; [exact FRM|].
    split; [eapply rw_cells_rebytes; [exact SHM| cbn; tauto| reflexivity| reflexivity]|].
    split; [exact FLG| exact ST2].
  Qed.
End SM4.

Section WRAP.
  Context {HC : HasCeiling}.
  Variable L : alayout.
  Hypothesis AO : alayout_ok L.
  Variable k : Z.
  Hypothesis Hk : 0 <= k <= 4.
  Variables (FBm SBn : nat).
  Hypothesis HFBm : Z.of_nat FBm = FB_of k - 40.
  Hypothesis HSBn : Z.of_nat SBn = SB_of k.

  Definition smk_post (st : fstate) (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32)
      (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (junk1 junk2 : list byte),
      let g := snd (fst_malloc (al_fsb L) st k) in
      ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz (ff_addr g)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(al_fsb L + 8 * k, al_fsb L + 8 * k + 8); (ff_flag g, ff_flag g + 1); (ff_addr g, ff_addr g + FB_of k);
                (sh (ff_addr g), sh (ff_addr g) + SB_of k); (lo, q)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ RFAKE_B (al_fsb L) (fst (fst_malloc (al_fsb L) st k)) m'
      /\ rw_cells asegs m' (ff_addr g) [CB 24%nat junk1; C8 (wz q); CB FBm junk2; C8 (wz (ff_flag g))]
      /\ rw_cells asegs m' (sh (ff_addr g)) (shadow_zero_cells SBn)
      /\ rw_cells asegs m' (ff_flag g) [C1 (Z_to_bv 8 1)]
      /\ stk asegs m' lo q.

  Hypothesis CORE : forall (st : fstate) (lo q : Z)
         (ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F_ : bvmap 5 word) (fc : bv 32) (m : mem),
    RFAKE_B (al_fsb L) st m -> (length (ft_live st) < 15)%nat ->
    thread_env (al_thread L) m -> thread_layout_ok (al_thread L) -> fs_tls_env (at_thr (al_thread L)) A0_DTV A0_TLSB (al_dtls L) (al_fsb L) m ->
    asan_env asegs m ->
    stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 208 -> q < 2^64 -> mem_inv asegs m ->
    evt asegs (smk_post st ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc lo m)
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz (A0_stack_malloc k)) fc None m (seg_rom asegs)).

  #[using="Hk FBm SBn HFBm HSBn CORE"] Lemma stack_malloc_wrap : forall (st : fstate) (lo q size F SF FL FB : Z) (FBm' SBn' : nat)
         (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F_ : bvmap 5 word) (fc : bv 32) (m : mem),
    F = fs_F (FI_B L AO) st k -> SF = sh F -> FL = fs_FL (FI_B L AO) st k -> FB = FB_of k -> Z.of_nat FBm' = FB - 40 -> Z.of_nat SBn' = SB_of k ->
    RFAKE (FI_B L AO) st m -> fs_call_ok (FI_B L AO) st tp 1 -> fsenv_B L (al_dtls L) m -> asan_env asegs m ->
    0 < size <= FB ->
    stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - A0_RT_STACK -> q < 2^64 ->
    mem_inv asegs m -> a0 = wz size ->
    evt asegs (stack_malloc_post (FI_B L AO) k st F SF FL FB FBm' SBn' ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc lo m)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz (A0_stack_malloc k)) fc None m (seg_rom asegs)).
  Proof.
    intros st lo q size F SF FL FB FBm' SBn' ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m
      EF ESF EFL EFB EFBm ESBn RF FCO (TE & FTE) AE SZ ST CLO LOQ QH MI EA0.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct FCO as [TP LEN]. assert (ETP : tp = wz A0_TP) by (rewrite <- (Z_to_bv_bv_unsigned tp), TP; reflexivity). subst tp.
    assert (FBm' = FBm) by (subst FB; lia). assert (SBn' = SBn) by lia. subst FBm' SBn'.
    pose proof AO as (_ & _ & _ & TLO & _).
    assert (LEN' : (length (ft_live st) < 15)%nat).
    { change (fs_live (FI_B L AO) st) with (fst_live (al_fsb L) st) in LEN. unfold fst_live in LEN. rewrite length_map in LEN. unfold A0_FS_DEPTH in LEN. lia. }
    destruct (new_frame_facts (FI_B L AO) st k m F SF FL RF ltac:(lia) EF ESF EFL) as (_ & N1 & N2 & N3 & N4 & N5 & _).
    pose proof (SB_FB k ltac:(lia)) as (SBF & _).
    pose proof (fsb_ok (FI_B L AO)) as (B1 & B2 & B3 & B4 & B5). change (FSB (FI_B L AO)) with (al_fsb L) in *.
    assert (NSH : sh (al_fsb L) <= SF /\ SF + SB_of k <= sh (al_fsb L) + A0_FS_SHSIZE /\ 0x7fff8000 <= SF).
    { subst SF. unfold sh, SHADOW_OFF. unfold app_mem in B3. clear - N1 N2 N3 SBF B4 B3. Z.div_mod_to_equations. lia. }
    pose proof (fs_shadow_apart (FI_B L AO)) as FSA. change (FSB (FI_B L AO)) with (al_fsb L) in FSA.
    eapply evt_cut.
    { eapply (CORE st lo q); [exact RF| exact LEN'| exact TE| exact TLO| exact FTE| exact AE| exact ST| exact CLO| unfold A0_RT_STACK in LOQ; clear - LOQ; lia| exact QH| exact MI]. }
    cbv beta. intros ms' P. unfold smk_post in P.
    destruct P as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m' & j1 & j2 & P). cbv zeta in P.
    change (snd (fst_malloc (al_fsb L) st k)) with (fs_newff (FI_B L AO) st k) in P.
    change (ff_addr (fs_newff (FI_B L AO) st k)) with (fs_F (FI_B L AO) st k) in P.
    change (ff_flag (fs_newff (FI_B L AO) st k)) with (fs_FL (FI_B L AO) st k) in P.
    rewrite <- EF, <- EFL in P. rewrite <- ESF in P.
    destruct P as (-> & MU & WM & MI' & RF' & FRM & SHM & FLG & ST').
    assert (AE' : asan_env asegs m').
    { eapply (asan_env_frame asegs); [exact AE| exact MU| exact WM|]. unfold env_safe.
      apply Forall_cons; [cbn [fst snd]; left; clear - B1 Hk; lia|].
      apply Forall_cons; [cbn [fst snd]; left; clear - B1 N4; lia|].
      apply Forall_cons; [cbn [fst snd]; left; clear - B1 N1; lia|].
      apply Forall_cons; [cbn [fst snd]; left; clear - NSH; lia|].
      apply Forall_cons; [cbn [fst snd]; left; clear - CLO ACR; lia|]. apply Forall_nil. }
    apply evt_done. unfold stack_malloc_post. exists y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, m', j1, j2.
    split; [reflexivity|].
    split. { eapply munch_weaken; [| exact MU]. unfold sub_fp. intros xo_ Hxo_. change (FSB (FI_B L AO)) with (al_fsb L) in Hxo_. cbn [outside] in *.
             clear - Hxo_ N1 N2 N4 N5 NSH Hk. lia. }
    split; [exact WM|]. split; [exact MI'|].
    split.
    { eapply (fkeep_of_munch (FI_B L AO) [] _ st st m m m'); [exact RF| intros g Hg; exact Hg| exact MU|].
      apply Forall_cons.
      {
        unfold fk_ok. right; right. cbn [fst snd]. eapply Forall_impl; [| exact (live_num (FI_B L AO) st m RF)]. cbv beta.
        change (FSB (FI_B L AO)) with (al_fsb L). intros g (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). clear - G1 G4 G8 G9 FSA Hk. lia. }
      apply Forall_cons; [replace (FL + 1) with (FL + 1) by reflexivity; apply (new_frame_fk (FI_B L AO) st k m F SF FL RF ltac:(lia) EF ESF EFL [] FL 1); right; right; split; reflexivity|].
      apply Forall_cons; [apply (new_frame_fk (FI_B L AO) st k m F SF FL RF ltac:(lia) EF ESF EFL [] F (FB_of k)); left; lia|].
      apply Forall_cons; [apply (new_frame_fk (FI_B L AO) st k m F SF FL RF ltac:(lia) EF ESF EFL [] SF (SB_of k)); right; left; lia|].
      apply Forall_cons; [| apply Forall_nil].
      unfold fk_ok. right; left. cbn [fst snd]. change (FSB (FI_B L AO)) with (al_fsb L). clear - CLO B2 NSH ACR N2. unfold sh, SHADOW_OFF in *. lia. }
    split; [reflexivity|]. split; [exact RF'|].
    split; [subst FB; exact FRM|]. split; [exact SHM|]. split; [exact FLG|]. split; [exact ST'| exact AE'].
  Qed.
End WRAP.

Section INSTK.
  Context {HC : HasCeiling}.
  Variable L : alayout.
  Hypothesis AO : alayout_ok L.

  Definition stack_malloc_stmt_B (k : Z) : Prop :=
    forall (st : fstate) (lo q size F SF FL FB : Z) (FBm SBn : nat)
         (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F_ : bvmap 5 word) (fc : bv 32) (m : mem),
    F = fs_F (FI_B L AO) st k -> SF = sh F -> FL = fs_FL (FI_B L AO) st k -> FB = FB_of k -> Z.of_nat FBm = FB - 40 -> Z.of_nat SBn = SB_of k ->
    RFAKE (FI_B L AO) st m -> fs_call_ok (FI_B L AO) st tp 1 -> fsenv_B L (al_dtls L) m -> asan_env asegs m ->
    0 < size <= FB ->
    stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - A0_RT_STACK -> q < 2^64 ->
    mem_inv asegs m -> a0 = wz size ->
    evt asegs (stack_malloc_post (FI_B L AO) k st F SF FL FB FBm SBn ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc lo m)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz (A0_stack_malloc k)) fc None m (seg_rom asegs)).

  #[using="Type"] Theorem stack_malloc0_B : stack_malloc_stmt_B 0.
  Proof.
    unfold stack_malloc_stmt_B. apply (stack_malloc_wrap L AO 0 ltac:(lia) 24%nat 8%nat eq_refl eq_refl).
    intros. eapply (sm0_core (al_fsb L) (fsb_ok_B L AO) (al_thread L) (al_dtls L)); eassumption.
  Qed.
  #[using="Type"] Theorem stack_malloc1_B : stack_malloc_stmt_B 1.
  Proof.
    unfold stack_malloc_stmt_B. apply (stack_malloc_wrap L AO 1 ltac:(lia) 88%nat 16%nat eq_refl eq_refl).
    intros. eapply (sm1_core (al_fsb L) (fsb_ok_B L AO) (al_thread L) (al_dtls L)); eassumption.
  Qed.
  #[using="Type"] Theorem stack_malloc2_B : stack_malloc_stmt_B 2.
  Proof.
    unfold stack_malloc_stmt_B. apply (stack_malloc_wrap L AO 2 ltac:(lia) 216%nat 32%nat eq_refl eq_refl).
    intros. eapply (sm2_core (al_fsb L) (fsb_ok_B L AO) (al_thread L) (al_dtls L)); eassumption.
  Qed.
  #[using="Type"] Theorem stack_malloc3_B : stack_malloc_stmt_B 3.
  Proof.
    unfold stack_malloc_stmt_B. apply (stack_malloc_wrap L AO 3 ltac:(lia) 472%nat 64%nat eq_refl eq_refl).
    intros. eapply (sm3_core (al_fsb L) (fsb_ok_B L AO) (al_thread L) (al_dtls L)); eassumption.
  Qed.
  #[using="Type"] Theorem stack_malloc4_B : stack_malloc_stmt_B 4.
  Proof.
    unfold stack_malloc_stmt_B. apply (stack_malloc_wrap L AO 4 ltac:(lia) 984%nat 128%nat eq_refl eq_refl).
    intros. eapply (sm4_core (al_fsb L) (fsb_ok_B L AO) (al_thread L) (al_dtls L)); eassumption.
  Qed.

  #[using="Type"] Theorem stack_malloc_ok0 : stack_malloc_stmt (FI_B L AO) 0. Proof. exact stack_malloc0_B. Qed.
  #[using="Type"] Theorem stack_malloc_ok1 : stack_malloc_stmt (FI_B L AO) 1. Proof. exact stack_malloc1_B. Qed.
  #[using="Type"] Theorem stack_malloc_ok2 : stack_malloc_stmt (FI_B L AO) 2. Proof. exact stack_malloc2_B. Qed.
  #[using="Type"] Theorem stack_malloc_ok3 : stack_malloc_stmt (FI_B L AO) 3. Proof. exact stack_malloc3_B. Qed.
  #[using="Type"] Theorem stack_malloc_ok4 : stack_malloc_stmt (FI_B L AO) 4. Proof. exact stack_malloc4_B. Qed.
End INSTK.
