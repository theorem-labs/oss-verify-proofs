(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac STRW_merge Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells.
Import ListNotations.
Open Scope Z_scope.

Definition gfa_entry := 0x38548%Z.

Lemma firstn_S_nth_gen : forall {A} (l : list A) i (d : A), (i < length l)%nat -> firstn (S i) l = firstn i l ++ [nth i l d].
Proof.
  induction l as [|x l IHl]; intros i d Hi; cbn in Hi; [lia|]. destruct i; [reflexivity|].
  change (x :: firstn (S i) l = x :: (firstn i l ++ [nth i l d])). f_equal. apply IHl. lia.
Qed.

Section GFA.
  Context {HC : HasCeiling}.
  Variable AL : alayout.
  Hypothesis AO : alayout_ok AL.
  Notation SPACE := (al_space AL).
  Notation THR := (at_thr (al_thread AL)).
  Variables (ra gp tp : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q c n CH STAT : Z) (m0 : mem).
  Hypothesis Hc : 1 <= c <= 31.
  Notation RI := (RIB AL + 128 * c).
  Notation FA := (fa_base AL c).

  Definition gfaA_post (lo : Z) (s2 s10 s11 t3 t4 t5 t6 : word) (k : pclass) (j8 j64 j88 j96 j104 j112 : word) (jpad : list byte)
      (frame : list cell) : machine_state -> Prop :=
    fun ms' => exists m', ms' =
        MS (mkR ra (wz (q - 128)) gp tp (wz 0) (wz KWL) (wz 0) (wz RI) (wz INSTANCE) (wz (RI + 8)) (wz STAT) (wz c) (wz CH) (wz n) (wz 0) (wz (-1)) (wz 0)
                s2 (wz 2305843009213693952) (wz FA) (wz 1099511627776) (wz 1152921504607895551) (wz KWL) (wz 1500) (wz 16140901064495857663) s10 s11
                t3 t4 t5 t6)
           F_ (wz 0x38698) fc None m' (seg_rom asegs)
        /\ munch [(q - 128, q); (RI, RI + 8)] m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' RI (ri_cells KWL k j8 j64 j88 j96 j104 j112 jpad)
        /\ rw_cells asegs m' (q - 128) frame
        /\ stk asegs m' lo (q - 128) /\ prim_env AL m'.

  #[using="AO Hc"] Lemma gfa_A : forall lo (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a5 a6 a7 : word) (k : pclass) j8 j64 j88 j96 j104 j112 jpad,
    stk asegs m0 lo q -> alloc_ceiling <= lo -> lo <= q - 128 -> q mod 16 = 0 -> q <= 2^47 ->
    prim_env AL m0 ->
    rw_cells asegs m0 RI (ri_cells 0 k j8 j64 j88 j96 j104 j112 jpad) ->
    mem_inv asegs m0 ->
    exists junk, evt asegs (gfaA_post lo s2 s10 s11 t3 t4 t5 t6 k j8 j64 j88 j96 j104 j112 jpad
                  [CB 24 junk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz INSTANCE) (wz STAT) (wz c) (wz CH) (wz n) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz gfa_entry) fc None m0 (seg_rom asegs)).
  Proof.
    intros lo s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a5 a6 a7 k j8 j64 j88 j96 j104 j112 jpad ST CLO LO AL16 QH PE RIC MI.
    unfold ri_cells in RIC.
    unfold gfa_entry. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    layout_facts AO 0%nat SPF. layout_facts AO 3%nat THF.
    unfold prim_env in PE. unfold RIB in *.
    pose proof (munch_refl [(q - 128, q); (SPACE + K_SPACE + 128 * c, SPACE + K_SPACE + 128 * c + 8)] m0) as MU. pose proof (wmono_refl asegs m0) as WM.
    assert (E : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    rewrite <- E in ST. carve_frame 128%nat ST. rewrite !E in *.
    eexists.
    do 14 sstep.
    do 17 zstep.
    rewrite !Z.shiftl_mul_pow2 by lia. change (2^7) with 128. change (2^32) with 4294967296.
    replace (SPACE + 137438953472 + c * 128) with (SPACE + 137438953472 + 128 * c) by lia.
    replace (SPACE + (c * 4294967296 + 3758096384)) with FA by (unfold fa_base, region; lia).
    set (ria := SPACE + 137438953472 + 128 * c) in *. assert (Hria : ria = SPACE + 137438953472 + 128 * c) by reflexivity. clearbody ria.
    set (faa := FA) in *. assert (Hfaa : faa = FA) by reflexivity. clearbody faa. unfold fa_base, region in Hfaa.
    zstep.
    zstep.
    do 6 zstep.
    zstep. if_cases K0; zify_cond K0. { exfalso. revert K0. clear. intros K0. cbn in K0. lia. }
    zstep. zstep.
    destruct AO as (RF & AP & SPAL & TLO & DLO & SW).
    assert (AMO : amo_aligned AD (Z_to_bv 64 ria) = true) by (apply amo_aligned_intro_d; [lia| rewrite Hria; Z.div_mod_to_equations; lia]).
    amo_step_h AMO.
    zstep. if_cases K1; zify_cond K1. { exfalso. revert K1. clear. intros K1. cbn in K1. lia. }
    amo_step_h AMO.   fix_lit_store.
    zstep. if_cases K2; zify_cond K2. { exfalso. revert K2. clear. intros K2. cbn in K2. lia. }
    zstep. if_cases K3; zify_cond K3. 2:{ exfalso. revert K3. clear. intros K3. cbn in K3. lia. }
    subst ria faa.
    apply evt_done. unfold gfaA_post, prim_env, ri_cells, RIB, fa_base, region. eexists. split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; eassumption.
  Qed.

  Definition cp_list (fa : list Z) (base : Z) (i : nat) (cs0 : list word) : list word :=
    map wz (firstn i (skipn (Z.to_nat base) fa)) ++ skipn i cs0.

  #[using="Type"] Lemma cp_list_length : forall fa base i cs0, (i <= length cs0)%nat -> (Z.to_nat base + i <= length fa)%nat ->
    length (cp_list fa base i cs0) = length cs0.
  Proof. intros. unfold cp_list. rewrite length_app, length_map, firstn_length_le by (rewrite length_skipn; lia). rewrite length_skipn. lia. Qed.

  #[using="Type"] Lemma app_split_eq : forall {A} (la lb lc ld : list A), length la = length lc -> la ++ lb = lc ++ ld -> la = lc /\ lb = ld.
  Proof.
    induction la as [|x la IH]; intros lb lc ld L E; destruct lc as [|y lc]; cbn in L; try lia.
    - split; [reflexivity| exact E].
    - cbn in E. injection E as E1 E2. destruct (IH lb lc ld ltac:(lia) E2) as [-> ->]. subst. split; reflexivity.
  Qed.

  #[using="Type"] Lemma cp_list_step : forall fa base i cs0, (i < length cs0)%nat -> (Z.to_nat base + i < length fa)%nat ->
    upd (cp_list fa base i cs0) i (wz (nth (Z.to_nat base + i) fa 0)) = cp_list fa base (S i) cs0.
  Proof.
    intros fa base i cs0 Hi Hf. unfold cp_list.
    assert (L1 : length (map wz (firstn i (skipn (Z.to_nat base) fa))) = i).
    { rewrite length_map, firstn_length_le by (rewrite length_skipn; lia). reflexivity. }
    destruct (upd_app_split (map wz (firstn i (skipn (Z.to_nat base) fa)) ++ skipn i cs0) i (wz (nth (Z.to_nat base + i) fa 0))
                ltac:(rewrite length_app, L1, length_skipn; lia)) as (pre & y & post & E & Hlen & Hupd).
    rewrite Hupd.
    destruct (app_split_eq _ _ _ _ ltac:(rewrite L1, Hlen; reflexivity) E) as [PRE POST].
    rewrite <- PRE. replace post with (skipn (S i) cs0).
    2:{ replace (S i) with (1 + i)%nat by lia. rewrite <- skipn_skipn, POST. reflexivity. }
    rewrite (firstn_S_nth_gen (skipn (Z.to_nat base) fa) i 0) by (rewrite length_skipn; lia).
    rewrite map_app, nth_skipn. cbn [map]. rewrite <- app_assoc. reflexivity.
  Qed.

  #[using="Type"] Lemma gfa_copy : forall (K : nat) (i : nat) (ms mm : mem) (ws cs0 : list word) (fa : list Z) (base : Z) xra x5 x6 x7 x12 s0v a0v s1v s2 xs5 xs6 s10 s11 t3 t4 t5 t6 a5 a6 a7,
    (Z.to_nat n - i)%nat = K -> (i < Z.to_nat n)%nat -> 0 <= base -> (Z.to_nat (base + n) <= length fa)%nat -> (length fa <= length ws)%nat ->
    (Z.to_nat n <= length cs0)%nat -> 1 <= n <= 16 ->
    firstn (length fa) ws = map wz fa -> Forall (fun v => 0 <= v < 2^31) fa ->
    u32arr asegs mm FA ws -> u32arr asegs mm CH (cp_list fa base i cs0) ->
    FA + 4 * Z.of_nat (length ws) <= CH \/ CH + 4 * Z.of_nat (length cs0) <= FA ->
    munch [(CH, CH + 4 * n)] ms mm -> wmono asegs ms mm -> mem_inv asegs mm ->
    evt asegs (fun ms' => exists x12' m', ms' =
          MS (mkR xra (wz (q - 128)) gp tp x5 x6 x7 s0v s1v a0v (wz (CH + 4 * n)) x12' (wz (CH + 4 * n)) (wz n) a5 a6 a7
                  s2 (wz 2305843009213693952) (wz (FA + 4 * (base + n))) xs5 xs6 (wz KWL) (wz 1500) (wz 16140901064495857663) s10 s11
                  t3 t4 t5 t6) F_ (wz 0x386d0) fc None m' (seg_rom asegs)
          /\ munch [(CH, CH + 4 * n)] ms m' /\ wmono asegs ms m' /\ mem_inv asegs m'
          /\ u32arr asegs m' FA ws /\ u32arr asegs m' CH (cp_list fa base (Z.to_nat n) cs0))
      (MS (mkR xra (wz (q - 128)) gp tp x5 x6 x7 s0v s1v a0v (wz (CH + 4 * n)) x12 (wz (CH + 4 * Z.of_nat i)) (wz n) a5 a6 a7
               s2 (wz 2305843009213693952) (wz (FA + 4 * (base + Z.of_nat i))) xs5 xs6 (wz KWL) (wz 1500) (wz 16140901064495857663) s10 s11
               t3 t4 t5 t6) F_ (wz 0x386bc) fc None mm (seg_rom asegs)).
  Proof.
    induction K as [|K IH]; intros i ms mm ws cs0 fa base xra x5 x6 x7 x12 s0v a0v s1v s2 xs5 xs6 s10 s11 t3 t4 t5 t6 a5 a6 a7 HK Hi B0 BF LF BC NB FWS SM FAA CHA SEP MU WM MI; [lia|].
    pose proof (u32arr_bound asegs _ _ _ FAA) as B1. pose proof (u32arr_bound asegs _ _ _ CHA) as B2.
    rewrite cp_list_length in B2 by lia.
    assert (NW : nth_error ws (Z.to_nat base + i)%nat = Some (wz (nth (Z.to_nat base + i) fa 0))).
    { rewrite <- (firstn_skipn (length fa) ws), FWS. rewrite nth_error_app1 by (rewrite length_map; lia).
      rewrite nth_error_map, (nth_error_nth' fa 0) by lia. reflexivity. }
    assert (VR : 0 <= nth (Z.to_nat base + i) fa 0 < 2^31). { apply (Forall_nth (fun v => 0 <= v < 2^31) fa); [exact SM| lia]. }
    pose proof (u32arr_read asegs mm FA ws (base + Z.of_nat i) _ (wa (FA + 4 * (base + Z.of_nat i))) FAA ltac:(replace (Z.to_nat (base + Z.of_nat i)) with (Z.to_nat base + i)%nat by lia; exact NW) ltac:(lia) eq_refl) as HR.
    set (faa := FA) in *. assert (Hfaa : faa = FA) by reflexivity. clearbody faa. unfold fa_base, region in Hfaa.
    zstep.   rewrite (sx32_lit (nth (Z.to_nat base + i) fa 0)) by lia.
    pose proof (u32arr_store_ok asegs mm CH _ (Z.of_nat i) (wa (CH + 4 * Z.of_nat i)) CHA ltac:(rewrite cp_list_length; lia) eq_refl) as SOK.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mx _ _) _) =>
      pose proof (u32arr_write asegs mx CH _ (Z.of_nat i) (wz (nth (Z.to_nat base + i) fa 0)) CHA ltac:(rewrite cp_list_length; lia)) as CHA2 end.
    rewrite Nat2Z.id, cp_list_step in CHA2 by lia.
    clear CHA. store_done. rename CHA2 into CHA.
    zstep. zstep.
    zstep. if_cases KB; zify_cond KB.
    - replace (CH + 4 * Z.of_nat i + 4) with (CH + 4 * Z.of_nat (S i)) by lia.
      replace (faa + 4 * (base + Z.of_nat i) + 4) with (faa + 4 * (base + Z.of_nat (S i))) by lia.
      subst faa. eapply (IH (S i)); try eassumption; try lia.
    - apply evt_done. replace (CH + 4 * Z.of_nat i + 4) with (CH + 4 * n) by lia.
      replace (faa + 4 * (base + Z.of_nat i) + 4) with (faa + 4 * (base + n)) by lia. replace (S i) with (Z.to_nat n) in CHA by lia.
      subst faa. eexists _, _. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.

  Definition gfaB_post (lo : Z) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (k : pclass) (j8 j64 j88 j96 j104 j112 : word) (jpad : list byte)
      (ws cs0 : list word) (fa : list Z) (base : Z) (ms : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 m', ms' =
        MS (mkR ra (wz q) gp tp x5 x6 x7 s0 s1 (wz 1) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
           F_ (ret_pc ra) fc None m' (seg_rom asegs)
        /\ munch [(q - 128, q); (RI, RI + 8); (RI + 72, RI + 80); (CH, CH + 4 * n)] ms m' /\ wmono asegs ms m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' RI (ri_cells 0 (mkPCL base (p_mfa k) (p_au k) (p_mu k) (p_nalloc k + n) (p_nfreed k) (p_fa k) (p_cnt k) (p_chunks k)) j8 j64 j88 j96 j104 j112 jpad)
        /\ u32arr asegs m' FA ws /\ u32arr asegs m' CH (cp_list fa base (Z.to_nat n) cs0)
        /\ stk asegs m' lo q.

  #[using="AO Hc"] Lemma gfa_B : forall lo (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 xra x5 x6 x7 x10 x11 x12 x16 x17 s1v xs2 xs5 xs6 : word) (k : pclass) j8 j64 j88 j96 j104 j112 jpad
                 (ws cs0 : list word) (fa : list Z) (base : Z) (junk : list byte) (ms : mem),
    p_nf k = base -> 0 <= base -> (Z.to_nat (base + n) <= length fa)%nat -> (length fa <= length ws)%nat ->
    length cs0 = 16%nat -> 1 <= n <= 16 ->
    firstn (length fa) ws = map wz fa -> Forall (fun v => 0 <= v < 2^31) fa ->
    u32arr asegs ms FA ws -> u32arr asegs ms CH cs0 -> 4 * Z.of_nat (length ws) <= K_FA_SIZE ->
    0 < CH -> CH + 64 <= alloc_ceiling -> (CH + 64 <= SPACE \/ SPACE + K_SPACE + 4096 <= CH) ->
    rw_cells asegs ms RI (ri_cells KWL k j8 j64 j88 j96 j104 j112 jpad) ->
    rw_cells asegs ms (q - 128) [CB 24 junk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs ms lo (q - 128) -> alloc_ceiling <= lo -> lo <= q - 128 -> q mod 16 = 0 -> q <= 2^47 ->
    mem_inv asegs ms ->
    evt asegs (gfaB_post lo s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 k j8 j64 j88 j96 j104 j112 jpad ws cs0 fa base ms)
      (MS (mkR xra (wz (q - 128)) gp tp x5 x6 x7 (wz RI) s1v x10 x11 x12 (wz CH) (wz n) (wz base) x16 x17
               xs2 (wz 2305843009213693952) (wz FA) xs5 xs6 (wz KWL) (wz 1500) (wz 16140901064495857663) s10 s11
               t3 t4 t5 t6) F_ (wz 0x386ac) fc None ms (seg_rom asegs)).
  Proof.
    intros lo s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 xra x5 x6 x7 x10 x11 x12 x16 x17 s1v xs2 xs5 xs6 k j8 j64 j88 j96 j104 j112 jpad ws cs0 fa base junk ms.
    intros NF B0 BF LF LC NB FWS SM FAA CHA WSB CHL CHH CHS RIC FR ST CLO LO AL16 QH MI.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    layout_facts AO 0%nat SPF. unfold ri_cells in RIC. unfold RIB in *.
    pose proof (u32arr_bound asegs _ _ _ FAA) as B1. pose proof (u32arr_bound asegs _ _ _ CHA) as B2. rewrite LC in B2.
    pose proof (munch_refl [(q - 128, q); (RI, RI + 8); (RI + 72, RI + 80); (CH, CH + 4 * n)] ms) as MU. pose proof (wmono_refl asegs ms) as WM.
    unfold RIB in MU.
    set (ria := SPACE + K_SPACE + 128 * c) in *. assert (Hria : ria = SPACE + K_SPACE + 128 * c) by reflexivity. clearbody ria.
    set (faa := FA) in *. assert (Hfaa : faa = FA) by reflexivity. clearbody faa. unfold fa_base, region in Hfaa.
    do 4 zstep.
    rewrite !Z.shiftl_mul_pow2 by lia. change (2^2) with 4.
    replace (CH + n * 4) with (CH + 4 * n) by lia. replace (faa + base * 4) with (faa + 4 * (base + Z.of_nat 0)) by lia.
    replace (Z_to_bv 64 CH) with (Z_to_bv 64 (CH + 4 * Z.of_nat 0)) by (f_equal; lia).
    subst faa. eapply evt_cut.
    { eapply (gfa_copy (Z.to_nat n - 0) 0 ms ms ws cs0 fa base); try eassumption; try lia; try reflexivity.
      - unfold fa_base, region. lia.
      - apply munch_refl. }
    cbv beta. intros ms1 (x12' & m1 & -> & MU1 & WM1 & MI1 & FAA1 & CHA1).
    remember (cp_list fa base (Z.to_nat n) cs0) as cs1 eqn:Hcs1.
    assert (LC1 : length cs1 = 16%nat) by (rewrite Hcs1, cp_list_length; lia).
    rewrite NF in RIC.
    clear MU WM.
    pose proof (rw_cells_transport asegs _ ms m1 _ _ RIC MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as RIC1.
    pose proof (rw_cells_transport asegs _ ms m1 _ _ FR MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as FR1.
    pose proof (stk_transport_disjoint asegs _ ms m1 _ _ ST MU1 WM1 ltac:(cbn [disjoint_from]; lia)) as ST1.
    apply (munch_weaken _ [(q - 128, q); (ria, ria + 8); (ria + 72, ria + 80); (CH, CH + 4 * n)]) in MU1; [| unfold sub_fp; cbn [outside]; intros; lia].
    clear RIC FR ST FAA CHA MI. rename MU1 into MU. rename WM1 into WM.
    set (faa := FA) in *. assert (Hfaa : faa = FA) by reflexivity. clearbody faa. unfold fa_base, region in Hfaa.
    zstep. zstep. sstep.
    zstep.
    do 14 zstep.
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
    zstep.
    do 13 zstep. zstep. replace (q - 128 + 128) with q by lia. zstep.
    match goal with H : stk asegs _ lo _ |- _ => release_frame FR1 H q end.
    subst ria faa.
    apply evt_done. unfold gfaB_post, ri_cells, RIB, fa_base, region. cbn [p_nf p_mfa p_au p_mu p_nalloc p_nfreed].
    eexists _, _, _, _, _, _, _, _, _, _, _, _. split; [reflexivity|].
    subst cs1. repeat match goal with |- _ /\ _ => split end; eassumption.
  Qed.
End GFA.
