(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac STRW_merge Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells LJ PEnv APrimSpec APrimLem AFrame F_prim_L0 F_prim_gfa.
Import ListNotations.
Open Scope Z_scope.

Definition rta_entry : Z := 0x361ec.

Section RTA.
  Context {HC : HasCeiling}.
  Variable AL : alayout.
  Hypothesis AO : alayout_ok AL.
  Notation SPACE := (al_space AL).
  Notation THR := (at_thr (al_thread AL)).
  Variables (ra gp tp : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q c n CH STAT MM : Z) (m0 : mem).
  Hypothesis Hc : 1 <= c <= 31.
  Notation RI := (RIB AL + 128 * c).
  Notation FA := (fa_base AL c).

  Definition rtaA_post (lo : Z) (t0 t1 t2 t3 t4 t5 t6 : word) (k : pclass) (j8 j64 j88 j96 j104 j112 : word) (jpad : list byte)
      (frame : list cell) : machine_state -> Prop :=
    fun ms' => exists m', ms' =
        MS (mkR ra (wz (q - 128)) gp tp t0 t1 t2 (wz RI) (wz 16140901064495857663) (wz 0) (wz (-1)) (wz (region AL c)) (wz 0) (wz 0) (wz KWL) (wz 0) (wz 1500)
                (wz c) (wz MM) (wz INSTANCE) (wz n) (wz CH) (wz 1099511627776) (wz 2305843009213693952) (wz FA) (wz 1152921504607895551) (wz KWL)
                t3 t4 t5 t6)
           F_ (wz 0x36338) fc None m' (seg_rom asegs)
        /\ munch [(q - 128, q); (RI, RI + 8)] m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' RI (ri_cells KWL k j8 j64 j88 j96 j104 j112 jpad)
        /\ rw_cells asegs m' (q - 128) frame
        /\ stk asegs m' lo (q - 128) /\ prim_env AL m'.

  #[using="AO Hc"] Lemma rta_A : forall lo (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a6 a7 : word) (k : pclass) j8 j64 j88 j96 j104 j112 jpad,
    stk asegs m0 lo q -> alloc_ceiling <= lo -> lo <= q - 128 -> q mod 16 = 0 -> q <= 2^47 ->
    prim_env AL m0 ->
    rw_cells asegs m0 RI (ri_cells 0 k j8 j64 j88 j96 j104 j112 jpad) ->
    mem_inv asegs m0 ->
    exists junk, evt asegs (rtaA_post lo t0 t1 t2 t3 t4 t5 t6 k j8 j64 j88 j96 j104 j112 jpad
                  [CB 16 junk; C8 (wz (RI + 8)); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz INSTANCE) (wz MM) (wz STAT) (wz c) (wz CH) (wz n) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz rta_entry) fc None m0 (seg_rom asegs)).
  Proof.
    intros lo s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a6 a7 k j8 j64 j88 j96 j104 j112 jpad ST CLO LO AL16 QH PE RIC MI.
    unfold ri_cells in RIC.
    unfold rta_entry. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    layout_facts AO 0%nat SPF. layout_facts AO 3%nat THF.
    unfold prim_env in PE. unfold RIB in *.
    pose proof (munch_refl [(q - 128, q); (SPACE + K_SPACE + 128 * c, SPACE + K_SPACE + 128 * c + 8)] m0) as MU. pose proof (wmono_refl asegs m0) as WM.
    assert (E : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    rewrite <- E in ST. carve_frame 128%nat ST. rewrite !E in *.
    eexists.
    do 14 sstep.
    do 22 zstep.
    rewrite !Z.shiftl_mul_pow2 by lia. change (2^7) with 128. change (2^32) with 4294967296.
    replace (SPACE + 137438953472 + c * 128) with (SPACE + 137438953472 + 128 * c) by lia.
    replace (SPACE + c * 4294967296 + 3758096384) with FA by (unfold fa_base, region; lia).
    set (ria := SPACE + 137438953472 + 128 * c) in *. assert (Hria : ria = SPACE + 137438953472 + 128 * c) by reflexivity. clearbody ria.
    set (faa := FA) in *. assert (Hfaa : faa = FA) by reflexivity. clearbody faa. unfold fa_base, region in Hfaa.
    zstep.
    zstep. zstep.
    do 4 zstep.
    zstep. zstep. if_cases K0; zify_cond K0. { exfalso. revert K0. clear. intros K0. cbn in K0. lia. }
    zstep. zstep.
    destruct AO as (RF & AP & SPAL & TLO & DLO & SW).
    assert (AMO : amo_aligned AD (Z_to_bv 64 ria) = true) by (apply amo_aligned_intro_d; [lia| rewrite Hria; Z.div_mod_to_equations; lia]).
    amo_step_h AMO.
    zstep. if_cases K1; zify_cond K1. { exfalso. revert K1. clear. intros K1. cbn in K1. lia. }
    amo_step_h AMO.   fix_lit_store.
    zstep. if_cases K2; zify_cond K2. { exfalso. revert K2. clear. intros K2. cbn in K2. lia. }
    zstep. if_cases K3; zify_cond K3. 2:{ exfalso. revert K3. clear. intros K3. cbn in K3. lia. }
    subst ria faa.
    apply evt_done. unfold rtaA_post, prim_env, ri_cells, RIB, fa_base, region. eexists. split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; eassumption.
  Qed.

  Definition rc_list (ws : list word) (base : Z) (i : nat) (vals : list Z) : list word :=
    firstn (Z.to_nat base) ws ++ map wz (firstn i vals) ++ skipn (Z.to_nat base + i) ws.

  #[using="Type"] Lemma rc_list_length : forall ws base i vals, (i <= length vals)%nat -> (Z.to_nat base + i <= length ws)%nat ->
    length (rc_list ws base i vals) = length ws.
  Proof. intros. unfold rc_list. rewrite !length_app, length_map, !length_firstn, length_skipn. lia. Qed.

  #[using="Type"] Lemma rc_list_0 : forall ws base vals, rc_list ws base 0 vals = ws.
  Proof. intros. unfold rc_list. cbn [firstn map app]. rewrite Nat.add_0_r. apply firstn_skipn. Qed.

  #[using="Type"] Lemma rc_list_step : forall ws base i vals, (i < length vals)%nat -> (Z.to_nat base + i < length ws)%nat ->
    upd (rc_list ws base i vals) (Z.to_nat base + i) (wz (nth i vals 0)) = rc_list ws base (S i) vals.
  Proof.
    intros ws base i vals Hi Hw. unfold rc_list.
    set (pre := firstn (Z.to_nat base) ws ++ map wz (firstn i vals)).
    assert (LP : length pre = (Z.to_nat base + i)%nat) by (unfold pre; rewrite length_app, length_map, !length_firstn; lia).
    assert (SK : skipn (Z.to_nat base + i) ws = nth (Z.to_nat base + i) ws (wz 0) :: skipn (Z.to_nat base + S i) ws).
    { replace (Z.to_nat base + S i)%nat with (S (Z.to_nat base + i)) by lia.
      rewrite <- (firstn_skipn (Z.to_nat base + i) ws) at 1 3.
      generalize (Z.to_nat base + i)%nat Hw. clear. intros j Hj. revert ws Hj. induction j as [|j IH]; intros [|x ws] Hj; cbn in Hj |- *; try lia; [reflexivity|].
      cbn [firstn skipn app nth]. specialize (IH ws ltac:(lia)). rewrite !firstn_skipn in *. exact IH. }
    rewrite app_assoc. fold pre. rewrite SK.
    rewrite (upd_firstn_skipn (pre ++ _ :: _) (Z.to_nat base + i)) by (rewrite length_app; cbn [length]; lia).
    rewrite firstn_app, LP, Nat.sub_diag, firstn_all2 by lia. cbn [firstn]. rewrite app_nil_r.
    rewrite skipn_app, LP. replace (S (Z.to_nat base + i) - (Z.to_nat base + i))%nat with 1%nat by lia.
    rewrite skipn_all2 by lia. cbn [skipn app].
    rewrite (firstn_S_nth_gen vals i 0 Hi), map_app. cbn [map]. unfold pre. rewrite <- !app_assoc. reflexivity.
  Qed.

  #[using="Type"] Lemma rta_copy : forall (K : nat) (i : nat) (ms mm : mem) (ws cs : list word) (vals : list Z) (base c0 CHB : Z)
        (r1 r2 r5 r6 r7 r8 r9 a1 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r26 r27 r28 r29 r30 r31 : word),
    (Z.to_nat n - i)%nat = K -> (i < Z.to_nat n)%nat -> 0 <= base -> (Z.to_nat (base + n) <= length ws)%nat ->
    0 <= c0 -> length vals = Z.to_nat n -> 1 <= n <= 16 ->
    (forall j, (j < Z.to_nat n)%nat -> nth_error cs (Z.to_nat c0 + j) = Some (wz (nth j vals 0))) -> Forall (fun v => 0 <= v < 2^31) vals ->
    u32arr asegs mm FA (rc_list ws base i vals) -> u32arr asegs mm CHB cs ->
    FA + 4 * Z.of_nat (length ws) <= CHB \/ CHB + 4 * Z.of_nat (length cs) <= FA ->
    munch [(FA + 4 * base, FA + 4 * (base + n))] ms mm -> wmono asegs ms mm -> mem_inv asegs mm ->
    evt asegs (fun ms' => exists a1' m', ms' =
          MS (mkR r1 r2 gp tp r5 r6 r7 r8 r9 (wz (CHB + 4 * (c0 + n))) a1' r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 (wz (CHB + 4 * (c0 + n))) r23 r24 (wz (FA + 4 * (base + n))) r26 r27
                  r28 r29 r30 r31) F_ (wz 0x3637c) fc None m' (seg_rom asegs)
          /\ munch [(FA + 4 * base, FA + 4 * (base + n))] ms m' /\ wmono asegs ms m' /\ mem_inv asegs m'
          /\ u32arr asegs m' FA (rc_list ws base (Z.to_nat n) vals) /\ u32arr asegs m' CHB cs)
      (MS (mkR r1 r2 gp tp r5 r6 r7 r8 r9 (wz (CHB + 4 * (c0 + n))) a1 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 (wz (CHB + 4 * (c0 + Z.of_nat i))) r23 r24 (wz (FA + 4 * (base + Z.of_nat i))) r26 r27
               r28 r29 r30 r31) F_ (wz 0x36368) fc None mm (seg_rom asegs)).
  Proof.
    induction K as [|K IH]; intros i ms mm ws cs vals base c0 CHB r1 r2 r5 r6 r7 r8 r9 a1 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r23 r24 r26 r27 r28 r29 r30 r31
      HK Hi B0 BF C0 LV NB RD SM FAA CHA SEP MU WM MI; [lia|].
    pose proof (u32arr_bound asegs _ _ _ FAA) as B1. pose proof (u32arr_bound asegs _ _ _ CHA) as B2.
    rewrite rc_list_length in B1 by lia.
    assert (VR : 0 <= nth i vals 0 < 2^31). { apply (Forall_nth (fun v => 0 <= v < 2^31) vals); [exact SM| lia]. }
    pose proof (u32arr_read asegs mm CHB cs (c0 + Z.of_nat i) _ (wa (CHB + 4 * (c0 + Z.of_nat i))) CHA
                  ltac:(replace (Z.to_nat (c0 + Z.of_nat i)) with (Z.to_nat c0 + i)%nat by lia; exact (RD i Hi)) ltac:(lia) eq_refl) as HR.
    set (faa := FA) in *. assert (Hfaa : faa = FA) by reflexivity. clearbody faa. unfold fa_base, region in Hfaa.
    zstep.   rewrite (sx32_lit (nth i vals 0)) by lia.
    zstep.
    pose proof (u32arr_store_ok asegs mm faa _ (base + Z.of_nat i) (wa (faa + 4 * (base + Z.of_nat i))) FAA ltac:(rewrite rc_list_length; lia) eq_refl) as SOK.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mx _ _) _) =>
      pose proof (u32arr_write asegs mx faa _ (base + Z.of_nat i) (wz (nth i vals 0)) FAA ltac:(rewrite rc_list_length; lia)) as FAA2 end.
    replace (Z.to_nat (base + Z.of_nat i)) with (Z.to_nat base + i)%nat in FAA2 by lia.
    rewrite rc_list_step in FAA2 by lia.
    clear FAA. store_done. rename FAA2 into FAA.
    zstep.
    zstep. if_cases KB; zify_cond KB.
    - replace (CHB + 4 * (c0 + Z.of_nat i) + 4) with (CHB + 4 * (c0 + Z.of_nat (S i))) by lia.
      replace (faa + 4 * (base + Z.of_nat i) + 4) with (faa + 4 * (base + Z.of_nat (S i))) by lia.
      subst faa. eapply (IH (S i)); try eassumption; try lia.
    - apply evt_done. replace (CHB + 4 * (c0 + Z.of_nat i) + 4) with (CHB + 4 * (c0 + n)) by lia.
      replace (faa + 4 * (base + Z.of_nat i) + 4) with (faa + 4 * (base + n)) by lia. replace (S i) with (Z.to_nat n) in FAA by lia.
      subst faa. eexists _, _. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.
End RTA.

Definition mrto_entry : Z := 0x36694.

Section MRTO.
  Context {HC : HasCeiling}.
  Variable AL : alayout.
  Hypothesis AO : alayout_ok AL.
  Variables (ra gp tp : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q c MM : Z) (m0 : mem).
  Hypothesis Hc : 1 <= c <= 31.
  Notation RI := (RIB AL + 128 * c).

  Ltac mrto_exit FR ST :=
    do 9 zstep; zstep; replace (q + -80 + 80) with q by lia; zstep;
    release_frame FR ST q;
    apply evt_done; eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _; split; [reflexivity|];
    repeat match goal with |- _ /\ _ => split end; eassumption.

  Ltac mrto_tail FR ST :=
    let KP := fresh "KP" in let KQ := fresh "KQ" in
    do 2 zstep; zstep; zstep;
    set (ria := al_space AL + 137438953472 + 128 * c) in *;
    zstep; if_false_z;
    zstep; zstep;
    zstep; if_cases KP; zify_cond KP;
    [ zstep; zstep; zstep; zstep;
      zstep; if_cases KQ; zify_cond KQ;
      [ mrto_exit FR ST
      | zstep; if_false_z; zstep;
        replace (sx32 (Z_to_bv 64 4294967295)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity);
        zstep; if_true_z; mrto_exit FR ST ]
    | zstep; mrto_exit FR ST ].

  #[using="AO Hc"] Lemma rta_mrto : forall lo (mtx : Z) (k : pclass) j8 j64 j88 j96 j104 j112 jpad
        (t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    stk asegs m0 lo q -> alloc_ceiling <= lo -> lo <= q - 80 -> q mod 16 = 0 -> q <= 2^47 ->
    prim_env AL m0 ->
    rw_cells asegs m0 GOT_PAGE [C8 (wz PAGE_CELL)] -> rw_cells asegs m0 PAGE_CELL [C8 (wz 4096)] ->
    rw_cells asegs m0 RI (ri_cells mtx k j8 j64 j88 j96 j104 j112 jpad) ->
    0 <= p_nf k < 2^40 ->
    mem_inv asegs m0 ->
    evt asegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
        ms' = MS (mkR ra (wz q) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F_ (ret_pc ra) fc None m' (seg_rom asegs)
        /\ munch [(q - 80, q)] m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m' /\ stk asegs m' lo q)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz INSTANCE) (wz MM) (wz c) (wz 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz mrto_entry) fc None m0 (seg_rom asegs)).
  Proof.
    intros lo mtx k j8 j64 j88 j96 j104 j112 jpad t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           ST CLO LO AL16 QH PE GP PG RIC NFR MI.
    unfold ri_cells in RIC. unfold mrto_entry.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    layout_facts AO 0%nat SPF.
    unfold prim_env in PE. unfold RIB in *.
    pose proof (munch_refl [(q - 80, q)] m0) as MU. pose proof (wmono_refl asegs m0) as WM.
    assert (E : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    rewrite <- E in ST. carve_frame 80%nat ST. rewrite !E in *.
    do 10 sstep.
    do 4 zstep.
    zstep.
    do 2 zstep.
    replace (Z.shiftl c 7) with (128 * c) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep. if_cases K31; zify_cond K31.
    -   zstep. zstep. mrto_tail FR ST.
    - zstep. zstep. if_cases K16; zify_cond K16.
      +   do 9 zstep. mrto_tail FR ST.
      +   zstep. zstep. mrto_tail FR ST.
  Qed.
End MRTO.

Section RTB.
  Context {HC : HasCeiling}.
  Variable AL : alayout.
  Hypothesis AO : alayout_ok AL.
  Notation SPACE := (al_space AL).
  Variables (ra gp tp : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q c n MM : Z) (m0 : mem).
  Hypothesis Hc : 1 <= c <= 31.
  Notation RI := (RIB AL + 128 * c).

  Definition rtaB_post (lo : Z) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (k : pclass) (total : Z) (j8 j64 j88 j96 j104 j112 : word) (jpad : list byte)
      : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m', ms' =
        MS (mkR ra (wz q) gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
           F_ (ret_pc ra) fc None m' (seg_rom asegs)
        /\ munch [(q - 208, q); (RI, RI + 8); (RI + 16, RI + 24); (RI + 80, RI + 88)] m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' RI (ri_cells 0 (mkPCL total (p_mfa k) (p_au k) (p_mu k) (p_nalloc k) (p_nfreed k + n) (p_fa k) (p_cnt k) (p_chunks k)) j8 j64 j88 j96 j104 j112 jpad)
        /\ stk asegs m' lo q.

  #[using="AO Hc"] Lemma rta_B : forall lo (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (k : pclass) (total : Z) j8 j64 j88 j96 j104 j112 jpad (junk : list byte)
        (xra x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x22 x25 x26 x27 x28 x29 x30 x31 : word),
    0 <= total < 2^40 -> 1 <= n <= 16 ->
    rw_cells asegs m0 RI (ri_cells KWL k j8 j64 j88 j96 j104 j112 jpad) ->
    rw_cells asegs m0 (q - 128) [CB 16 junk; C8 (wz (RI + 8)); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs m0 lo (q - 128) -> alloc_ceiling <= lo -> lo <= q - 208 -> q mod 16 = 0 -> q <= 2^47 ->
    prim_env AL m0 -> rw_cells asegs m0 GOT_PAGE [C8 (wz PAGE_CELL)] -> rw_cells asegs m0 PAGE_CELL [C8 (wz 4096)] ->
    mem_inv asegs m0 ->
    evt asegs (rtaB_post lo s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 k total j8 j64 j88 j96 j104 j112 jpad)
      (MS (mkR xra (wz (q - 128)) gp tp x5 x6 x7 (wz RI) x9 x10 x11 x12 x13 x14 x15 x16 x17
               (wz c) (wz MM) (wz INSTANCE) (wz n) x22 (wz total) (wz 2305843009213693952) x25 x26 x27 x28 x29 x30 x31)
          F_ (wz 0x3637c) fc None m0 (seg_rom asegs)).
  Proof.
    intros lo s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 k total j8 j64 j88 j96 j104 j112 jpad junk
           xra x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x22 x25 x26 x27 x28 x29 x30 x31
           TB NB RIC FR ST CLO LO AL16 QH PE GP PG MI.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    layout_facts AO 0%nat SPF. unfold ri_cells in RIC. unfold prim_env in PE. unfold RIB in *.
    pose proof (munch_refl [(q - 208, q); (SPACE + K_SPACE + 128 * c, SPACE + K_SPACE + 128 * c + 8); (SPACE + K_SPACE + 128 * c + 16, SPACE + K_SPACE + 128 * c + 24);
                            (SPACE + K_SPACE + 128 * c + 80, SPACE + K_SPACE + 128 * c + 88)] m0) as MU. pose proof (wmono_refl asegs m0) as WM.
    set (ria := SPACE + K_SPACE + 128 * c) in *. assert (Hria : ria = SPACE + K_SPACE + 128 * c) by reflexivity. clearbody ria.
    zstep.
    zstep.
    zstep. zstep.
    do 4 zstep.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      call (rta_mrto AL AO _ gp tp F_ fc (q - 128) c MM mx Hc lo KWL
              (mkPCL total (p_mfa k) (p_au k) (p_mu k) (p_nalloc k) (p_nfreed k + n) (p_fa k) (p_cnt k) (p_chunks k)) j8 j64 j88 j96 j104 j112 jpad) end.
    1: assumption.
    1: exact CLO.
    1: clear - LO; lia.
    1: clear - AL16; Z.div_mod_to_equations; lia.
    1: clear - QH; lia.
    1: unfold prim_env, RIB; assumption.
    1: assumption.
    1: assumption.
    1: unfold ri_cells, RIB; cbn [p_nf p_mfa p_au p_mu p_nalloc p_nfreed]; rewrite <- Hria; exact RIC.
    1: cbn [p_nf]; exact TB.
    1: assumption.
    zstep.
    do 13 zstep.
    zstep.
    zstep. zstep. zstep. lit_branch.
    zstep. zstep. lit_branch.
    do 7 zstep. zstep. lit_branch.
    assert (AMO : amo_aligned AD (Z_to_bv 64 ria) = true) by (apply amo_aligned_intro_d; [lia| rewrite Hria; destruct AO as (RF & _); Z.div_mod_to_equations; lia]).
    amo_step_h AMO.
    zstep. lit_branch.
    amo_step_h AMO.   fix_lit_store.
    zstep. lit_branch.
    zstep. lit_branch.
    zstep. lit_branch.
    do 13 zstep. zstep. replace (q - 128 + 128) with q by lia. zstep.
    release_frame FR POST q.
    subst ria.
    apply evt_done. unfold rtaB_post, ri_cells, RIB. cbn [p_nf p_mfa p_au p_mu p_nalloc p_nfreed].
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _. split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; eassumption.
  Qed.
End RTB.
