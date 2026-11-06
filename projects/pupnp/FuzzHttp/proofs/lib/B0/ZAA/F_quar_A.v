(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac STRW_merge Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells LJ LJU PEnv APrimSpec APrimSpec2 APrimLem AFrame APrimPop APrimPopR APrimQ APrimFrame AFrameM
                        APrimDealloc ASec AQuar AQuarM F_poison F_prim_L0 F_prim_cdealloc F_sec_A ATacFix.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition arec_entry : Z := 0x35898.
Definition AREC_STACK : Z := CDEALLOC_STACK.

Lemma arec_size : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a4 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32)
    (m : mem) (c : Z),
  1 <= c <= 31 ->
  evt asegs (fun ms' => exists a6' a7',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (wz c) (wz c) a4 (wz (class_size c)) a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (wz 0x35948) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (wz c) (wz c) a4 (wz 31) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (wz 0x358ec) fc None m (seg_rom asegs)).
Proof.
  intros until c. intros Hc.
  zstep. if_cases K31; zify_cond K31.
  {   subst c. zstep. zstep. apply evt_done. eexists _, _. reflexivity. }
  zstep. zstep. if_cases K17; zify_cond K17.
  2: {   zstep. if_cases K0; zify_cond K0. { exfalso. lia. }
       zstep. zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2^5) with 32.
       replace (c * 32) with (class_size c) by (unfold class_size; replace (c =? 31) with false by (symmetry; apply Z.eqb_neq; lia); replace (c <=? 16) with true by (symmetry; apply Z.leb_le; lia); lia).
       apply evt_done. eexists _, _. reflexivity. }

  assert (CC : c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30) by lia.
  clear Hc K31 K17.
  repeat (destruct CC as [CC|CC]); subst c; (do 9 zstep; apply evt_done; eexists _, _; reflexivity).
Qed.

Section AREC.
  Context {HC : HasCeiling}.
  Variables (AL : alayout) (E : penv).
  Notation L := (al_thread AL).
  Notation THR := (at_thr (al_thread AL)).
  Notation CACHE := (at_thr (al_thread AL) + CACHE_OFF).

  #[using="Type"] Lemma cb_join : forall (mm : mem) (A : Z) (n1 n2 : nat) (j1 j2 : list byte),
    rw_cells asegs mm A [CB n1 j1] -> rw_cells asegs mm (A + Z.of_nat n1) [CB n2 j2] -> rw_cells asegs mm A [CB (n1 + n2) (j1 ++ j2)].
  Proof.
    intros mm A n1 n2 j1 j2 C1 C2.
    assert (C2' : rw_cells asegs mm (A + Z.of_nat (cells_size [CB n1 j1])) [CB n2 j2]) by (cbn [cells_size csize]; rewrite Nat.add_0_r; exact C2).
    pose proof (proj2 (rw_cells_app asegs mm A [CB n1 j1] [CB n2 j2]) (conj C1 C2')) as C.
    pose proof (rw_cells_merge asegs mm A [] [CB n1 j1; CB n2 j2] [] C) as C'. cbn [app cells_size cells_bytes csize cbytes] in C'.
    rewrite Nat.add_0_r, app_nil_r in C'. exact C'.
  Qed.

  #[using="Type"] Lemma hdr_word_facts : forall bu, 0 <= bu < 256 ->
    Z.lor 3 (Z.shiftl bu 8) = 3 + 256 * bu /\ Z.land (3 + 256 * bu) 255 = 3 /\ Z.lxor (3 + 256 * bu) 3 = 256 * bu /\ Z.lor 0 (Z.shiftl bu 8) = 256 * bu.
  Proof.
    intros bu Hb.
    pose proof (range_check (fun b => (Z.lor 3 (Z.shiftl b 8) =? 3 + 256 * b) && (Z.land (3 + 256 * b) 255 =? 3) && (Z.lxor (3 + 256 * b) 3 =? 256 * b) && (Z.lor 0 (Z.shiftl b 8) =? 256 * b))
                  0 256 ltac:(vm_compute; reflexivity) bu ltac:(lia)) as X.
    cbn beta in X. apply andb_true_iff in X as [X X4]. apply andb_true_iff in X as [X X3]. apply andb_true_iff in X as [X1 X2].
    apply Z.eqb_eq in X1, X2, X3, X4. tauto.
  Qed.

  Definition arec_W (lo q c v : Z) (P : prim) : list (Z * Z) :=
    prim_W AL lo q c (get_cls P c) (get_cls (cache_dealloc P c v) c)
    ++ [(region AL c + 16 * v, region AL c + 16 * v + class_size c); (sh (region AL c + 16 * v), sh (region AL c + 16 * v) + class_size c / 8)].

  Definition arec_prim_post (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (q lo c v : Z) (P : prim) (H : word -> bool) (m : mem) : unit -> (word -> bool) -> machine_state -> Prop :=
    fun _ H' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ H' = H_cdealloc AL P c H
      /\ munch (arec_W lo q c v P) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo q /\ poison_env E m' /\ thread_env L m' /\ shvis H' m'
      /\ RPRIM AL (cache_dealloc P c v) m' /\ prim_ok (cache_dealloc P c v).

  #[using="Type"] Lemma arec_prim_tail : forall (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32)
         (m mK : mem) (H : word -> bool) (q lo c v rz n CBA : Z) (P : prim) (stackw : word) (bits : byte) (actx : word)
         (xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    alayout_ok AL -> shvis H m -> poison_env E m -> thread_env L m ->
    0x10007fff8000 <= lo -> alloc_ceiling <= lo -> lo <= q - AREC_STACK -> q <= 2^47 -> q mod 16 = 0 ->
    RPRIM AL P m -> prim_ok P -> qchunk_wf (mkQC (QPrim c v) rz n) -> qchunk_rep AL m (mkQC (QPrim c v) rz n) -> held1 P (c, v) ->
    q <= CBA -> CBA + 16 <= 2^47 ->
    munch [(q - 48, q); (region AL c + 16 * v, region AL c + 16 * v + 8)] m mK -> wmono asegs m mK -> mem_inv asegs mK ->
    stk asegs mK lo (q - 48) -> rw_cells asegs mK (q - 48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs mK CBA [C8 (wz CACHE); C8 stackw] ->
    (16 < rz -> rw_cells asegs mK (region AL c + 16 * v) [C8 (wz 0); C8 (wz (region AL c + 16 * v + rz - 16))]) ->
    rw_cells asegs mK (region AL c + 16 * v + rz - 16) [CB 4 [Z_to_bv 8 3; bits; Z_to_bv 8 0; Z_to_bv 8 0]; C4 (wz n); C8 actx] ->
    evt asegs (lzk H (t_cdealloc AL c (get_cls P c)) (arec_prim_post ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc q lo c v P H m))
      (MS (mkR xra (wz (q - 48)) gp (wz A0_TP) x5 x6 x7 (wz CBA) (wz (region AL c + 16 * v + rz - 16)) x10 x11 x12 x13 x14 x15 x16 x17
               (wz (region AL c + 16 * v)) (wz INSTANCE) (wz 137438953472) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F_ (wz 0x359a8) fc None mK (seg_rom asegs)).
  Proof.
    intros until x31. intros AO SV PE TE LOH CLO LO QH Q16 RP POK CHW CHR HELD CBQ CB47 MUK WMK MIK STK FRK CBK LCK HDRK.
    unfold AREC_STACK, CDEALLOC_STACK, MF_STACK in *.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & _).
    layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
    layout_apart_fact AO 0%nat 3%nat LP03.
    destruct HELD as (Hc & V0 & VAU & VAL & VNI). cbn [fst snd] in *.
    destruct CHW as (RZ16 & RZM & NR & RZN & (_ & _ & _)). cbn [qc_rz qc_n qc_kind qc_bsize] in *.
    pose proof (class_size_pos c Hc) as CS. pose proof (class_size_mod16 c Hc) as CS16.
    pose proof (region_range AL c Hc) as [R1 R2].
    set (k := get_cls P c) in *.
    pose proof RP as (LEN & PENV & CLS & STAT & (ts & TS)).
    destruct (CLS c Hc) as (WF & _). fold k in WF.
    pose proof WF as (_ & _ & _ & _ & _ & _ & AU & MUF & _).
    destruct CHR as (_ & LCH & (jr & REST) & SHL & SHU & SHR & _).
    unfold qc_hdr, qc_blk in LCH, REST, SHL, SHU, SHR. cbn [qc_kind qc_rz qc_n qc_bsize] in LCH, REST, SHL, SHU, SHR.
    set (B := region AL c + 16 * v) in *. set (M := B + rz - 16) in *.
    assert (BR : al_space AL + K_REGION <= B /\ B + class_size c <= al_space AL + K_SPACE /\ id (B mod 16 = 0)).
    { unfold B, id. split; [clear - R1 V0; lia|]. split; [clear - R2 VAU AU MUF; lia|]. unfold region. clear - SPM. Z.div_mod_to_equations. lia. }
    assert (MR : B + 0 <= M /\ M + 16 + rup8 n <= B + class_size c /\ id (M mod 16 = 0)).
    { unfold M. split; [clear - RZ16; lia|]. split; [clear - RZN; lia|]. destruct BR as (_ & _ & B16). unfold id in *. clear - B16 RZM. Z.div_mod_to_equations. lia. }
    assert (EM : M = B + rz - 16) by reflexivity. assert (EB : B = region AL c + 16 * v) by reflexivity.
    assert (N8 : n <= rup8 n < n + 8 /\ id (rup8 n mod 8 = 0)) by (unfold rup8, id; clear; Z.div_mod_to_equations; lia).
    clearbody M B.
    hide T1. hide T5. hide T6. hide T7. hide SPM. hide Q16. hide RZM. hide CS16. hide VAL. hide EM. hide EB.

    unhide EM.
    assert (SHG : sh (M + 16) = sh B + rz / 8 /\ sh (M + 16 + rup8 n) = sh B + rz / 8 + rup8 n / 8
                  /\ sh B + class_size c / 8 = sh (M + 16 + rup8 n) + (class_size c - rz - rup8 n) / 8
                  /\ 2147450880 <= sh B /\ sh B + class_size c / 8 <= 17594333495296).
    { unhide RZM. unhide CS16. unfold sh, SHADOW_OFF. clear - EM RZM CS16 BR N8 RZ16 RZN SP1 SP5. destruct BR as (B1 & B2 & B16). destruct N8 as (N1 & N2). unfold id in *. Z.div_mod_to_equations. lia. }
    destruct SHG as (SG1 & SG2 & SG3 & SG4 & SG5).
    assert (DJK : forall A n0, (A + n0 <= B \/ B + 8 <= A) -> A + n0 <= lo -> disjoint_from [(q - 48, q); (B, B + 8)] A n0)
      by (intros A n0 D1 D2; cbn [disjoint_from]; clear - D1 D2 LO; lia).
    eapply (rw_cells_transport asegs _ m mK) in REST; [| exact MUK| exact WMK| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear - RZN N8 NR; lia); apply DJK; clear - EM MR BR SP2 CLO RZN N8 NR; lia]. rename REST into RESTK.
    eapply (rw_cells_transport asegs _ m mK) in SHL; [| exact MUK| exact WMK| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (apply Z.div_pos; clear - RZ16; lia); apply DJK; clear - SG1 SG2 SG3 SG4 SG5 BR SP1 LOH RZ16 N8 NR RZN; lia]. rename SHL into SHLK.
    eapply (rw_cells_transport asegs _ m mK) in SHU; [| exact MUK| exact WMK| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (apply Z.div_pos; clear - N8 NR; lia); apply DJK; clear - SG1 SG2 SG3 SG4 SG5 BR SP1 LOH RZ16 N8 NR RZN; lia]. rename SHU into SHUK.
    eapply (rw_cells_transport asegs _ m mK) in SHR; [| exact MUK| exact WMK| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (apply Z.div_pos; clear - RZN; lia); apply DJK; clear - SG1 SG2 SG3 SG4 SG5 BR SP1 LOH RZ16 N8 NR RZN; lia]. rename SHR into SHRK.
    eapply (rw_cells_transport asegs _ m mK) in TS; [| exact MUK| exact WMK| cbn [cells_size csize Nat.add]; apply DJK; clear - BR CS SP1 SP2 LP03 T3 T4 CLO; lia]. rename TS into TSK.
    assert (LCJK : 16 < rz -> exists j, rw_cells asegs mK (B + 16) [CB (Z.to_nat (rz - 32)) j]).
    { intros RZ. destruct (LCH RZ) as (_ & j & LJ). exists j. eapply rw_cells_transport; [exact LJ| exact MUK| exact WMK|].
      unhide RZM. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (clear - RZ RZM; Z.div_mod_to_equations; lia). apply DJK; clear - EM RZ RZM MR BR CS SP2 CLO RZN N8 NR; Z.div_mod_to_equations; lia. }
    clear LCH.
    assert (PEK : poison_env E mK) by (eapply poison_env_frame; [exact PE| exact MUK| exact WMK|]; clear - BR CS SP1 LO CLO ACR; env_clear).
    assert (TEK : thread_env L mK).
    { eapply thread_env_frame; [exact TE| exact MUK| exact WMK|]. unhide T1. unhide T5. layout_apart_fact AO 0%nat 2%nat AP02.
      clear - T1 T2 T3 T4 T5 LP03 AP02 BR CS SP1 SP2 LO CLO ACR. env_clear. }
    assert (SVK : shvis H mK) by (eapply shvis_wmono; [exact SV| exact WMK]).

    hide MUK. hide WMK. hide RESTK. hide SHLK. hide SHRK. hide LCK. hide SHUK. hide TSK. hide FRK. hide CBK.
    pose proof (munch_refl [(M, M + 4)] mK) as MUc. pose proof (wmono_refl asegs mK) as WMc.

    set (bu := bv_unsigned bits). assert (BU : 0 <= bu < 256) by (unfold bu; apply byte_lt256).
    destruct (hdr_word_facts bu BU) as (HW1 & HW2 & HW3 & HW4).
    assert (HW : rw_cells asegs mK M [C4 (wz (3 + 256 * bu)); C4 (wz n); C8 actx]).
    { pose proof (rw_cells_CB_C4 asegs mK M [] _ _ HDRK) as X. cbn [app] in X.
      replace (le_bytes_to_word [Z_to_bv 8 3; bits; Z_to_bv 8 0; Z_to_bv 8 0]) with (wz (3 + 256 * bu)) in X; [exact X|].
      unfold le_bytes_to_word. cbn [bytes_le_to_Z]. fold bu. f_equal. change (bv_unsigned (Z_to_bv 8 3)) with 3. change (bv_unsigned (Z_to_bv 8 0)) with 0.
      change (Z.shiftl 0 8) with 0. change (Z.lor 0 0) with 0. change (Z.shiftl 0 8) with 0. rewrite Z.lor_0_r. symmetry. exact HW1. }
    clear HDRK.
    do 4 zstep.
    assert (SHB : 2147450880 <= sh (M + 16) /\ sh (M + 16) + rup8 n / 8 <= 17594333495296) by (clear - SG1 SG2 SG3 SG4 SG5 RZ16 RZN N8 NR; pose proof (Z.div_pos rz 8); pose proof (Z.div_pos (class_size c - rz - rup8 n) 8); lia).
    hide SG1. hide SG2. hide SG3.
    assert (LA4 : Z.land M 18446744073709551612 = M).
    { assert (EU : exists u, M = Z.shiftl u 2 /\ 0 <= u < 2^62).
      { exists (M / 4). rewrite Z.shiftl_mul_pow2 by lia. change (2^2) with 4. clear - MR BR SP1 SP5 CS N8 NR. destruct MR as (M0 & M1 & M16). unfold id in M16. change (2^62) with 4611686018427387904. Z.div_mod_to_equations. lia. }
      destruct EU as (u & -> & Hu). change 18446744073709551612 with (Z.shiftl (Z.ones 62) 2).
      rewrite <- Z.shiftl_land, Z.land_ones by lia. rewrite Z.mod_small by exact Hu. reflexivity. }
    rewrite LA4. clear LA4.
    assert (EMT : exists mt, M = 16 * mt) by (exists (M / 16); destruct MR as (_ & _ & M16); unfold id in M16; clear - M16; Z.div_mod_to_equations; lia).
    destruct EMT as (mt & EMT).
    assert (SH0 : (128 * mt) mod 32 = 0) by (clear; Z.div_mod_to_equations; lia).
    replace (Z.shiftl M 3) with (128 * mt) by (rewrite EMT, Z.shiftl_mul_pow2 by lia; change (2^3) with 8; lia).
    zstep.
    rewrite SH0. change (Z.shiftl 255 0) with 255. change (bv_swrap 32 255) with 255.
    zstep.
    rewrite SH0. change (Z.shiftl 3 0) with 3. change (bv_swrap 32 3) with 3.
    assert (AMOM : amo_aligned AW (Z_to_bv 64 M) = true) by (apply amo_aligned_intro_w; [clear - MR BR SP1 SP5 CS N8 NR; lia| rewrite EMT; clear; Z.div_mod_to_equations; lia]).
    amo_step_h AMOM.
    rewrite (sx32_lit (3 + 256 * bu)) by (clear - BU; lia).
    zstep.
    rewrite HW2.
    zstep. lit_branch.
    zstep.
    zstep.
    zstep.
    rewrite Z.lxor_0_r, HW2, HW3.
    amo_step_h AMOM.
    zstep. lit_branch.
    hide EMT. hide SH0. clear AMOM HW1 HW2 HW3.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mS end.
    unhide SHUK. unhide TSK. unhide FRK. unhide CBK.
    assert (DJC : forall A n0, (A + n0 <= M \/ M + 4 <= A) -> disjoint_from [(M, M + 4)] A n0) by (intros A n0 D1; cbn [disjoint_from]; clear - D1; lia).
    eapply (rw_cells_transport asegs _ mK mS) in FRK; [| exact MUc| exact WMc| cbn [cells_size csize Nat.add]; apply DJC; clear - MR BR CS SP2 CLO LO N8 NR; lia].
    eapply (rw_cells_transport asegs _ mK mS) in CBK; [| exact MUc| exact WMc| cbn [cells_size csize Nat.add]; apply DJC; clear - CBQ MR BR CS SP2 CLO LO N8 NR; lia].
    eapply (rw_cells_transport asegs _ mK mS) in TSK; [| exact MUc| exact WMc| cbn [cells_size csize Nat.add]; apply DJC; clear - MR BR CS SP1 SP2 LP03 T3 T4 N8 NR; lia].
    eapply (rw_cells_transport asegs _ mK mS) in SHUK; [| exact MUc| exact WMc| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (apply Z.div_pos; clear - N8 NR; lia); apply DJC; clear - SHB MR BR SP1; lia].
    assert (MUT : munch [(lo, q); (M, M + 4); (sh (M + 16), sh (M + 16) + rup8 n / 8); (THR + 2800, THR + 3168)] mK mS).
    { eapply munch_weaken; [| exact MUc]. unfold sub_fp; cbn [outside]. intros xo (_ & O2 & _). split; [exact O2| exact I]. }
    pose proof WMc as WMT. clear MUc WMc.

    assert (HS : rw_cells asegs mS M [CB 2 [Z_to_bv 8 0; bits]; C2 (wz 0); C4 (wz n); C8 actx]).
    { eapply rw_cells_rebytes; [exact HW| cbn; tauto| | reflexivity]. cbn [cells_bytes cbytes app]. f_equal.
      assert (EW : wz (256 * bu) = le_bytes_to_word [Z_to_bv 8 0; bits; Z_to_bv 8 0; Z_to_bv 8 0]).
      { unfold le_bytes_to_word. cbn [bytes_le_to_Z]. fold bu. f_equal. change (bv_unsigned (Z_to_bv 8 0)) with 0.
        change (Z.shiftl 0 8) with 0. change (Z.lor 0 0) with 0. change (Z.shiftl 0 8) with 0. rewrite Z.lor_0_r. symmetry. exact HW4. }
      rewrite EW, le4_of_bytes by reflexivity. reflexivity. }
    clear HW.
    zstep.
    zstep.
    change (zx16 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
    replace (zx32 (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (unfold zx32; rewrite unsigned_lit by (clear - NR; lia); rewrite Z.mod_small by (clear - NR; lia); reflexivity).
    do 3 zstep.
    rewrite Z.lor_0_l.
    zstep.
    zstep.
    replace (Z.land (n + 7) 18446744073709551608) with (rup8 n).
    2: { rewrite land_m8 by (clear - NR; lia). unfold rup8. clear. Z.div_mod_to_equations. lia. }
    zstep.
    zstep.
    unhide SG1. unhide SG2. unhide SG3.
    assert (AIT : above_img [(lo, q); (M, M + 4); (sh (M + 16), sh (M + 16) + rup8 n / 8); (THR + 2800, THR + 3168)]).
    { clear - LOH LO MR BR CS SP1 SG1 SG2 SG3 SG4 SG5 T3 T4 RZ16 N8 NR. env_clear. }
    assert (PES : poison_env E mS) by (eapply poison_env_frame; [exact PEK| exact MUT| exact WMT| exact AIT]).

    eapply evt_cut.
    { eapply (poison_shadow_spec_all E _ gp (wz A0_TP) _ _ _ _ _ _ _ _ s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F_ fc (q - 48) lo (M + 16) (rup8 n) 250 mS).
      - assumption.
      - clear - LOH LO QH; lia.
      - split; [unhide EMT; rewrite EMT; clear; Z.div_mod_to_equations; lia|]. split; [exact (proj2 N8)|]. split; [clear - N8 NR; lia|].
        split; [right; clear - MR BR CS SP1 SP5 N8 NR; lia| lia].
      - exact PES.
      - exact STK.
      - exact SHUK. }
    cbv beta. unfold poison_post. intros msP (p5 & p6 & p7 & p10 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p28 & p29 & p30 & p31 & mP & -> & MUp & WMp & MIP & STP & PEP & SHUP).
    hide SG1. hide SG2. hide SG3.
    assert (DJP : forall A n0, (A + n0 <= q - 48 - 64 \/ q - 48 <= A) -> (A + n0 <= 2147450880 \/ 17594333495296 <= A) ->
                    disjoint_from [(q - 48 - 64, q - 48); (sh (M + 16), sh (M + 16) + rup8 n / 8)] A n0)
      by (intros A n0 D1 D2; cbn [disjoint_from]; clear - D1 D2 SHB; lia).
    eapply (rw_cells_transport asegs _ mS mP) in HS; [| exact MUp| exact WMp| cbn [cells_size csize Nat.add]; apply DJP; clear - MR BR CS SP1 SP2 CLO LO N8 NR; lia].
    eapply (rw_cells_transport asegs _ mS mP) in FRK; [| exact MUp| exact WMp| cbn [cells_size csize Nat.add]; apply DJP; clear - LOH LO; lia].
    eapply (rw_cells_transport asegs _ mS mP) in CBK; [| exact MUp| exact WMp| cbn [cells_size csize Nat.add]; apply DJP; clear - CBQ LOH LO; lia].
    eapply (rw_cells_transport asegs _ mS mP) in TSK; [| exact MUp| exact WMp| cbn [cells_size csize Nat.add]; apply DJP; clear - T3 T4 CLO LO; lia].
    assert (MUT' : munch [(lo, q); (M, M + 4); (sh (M + 16), sh (M + 16) + rup8 n / 8); (THR + 2800, THR + 3168)] mK mP).
    { eapply munch_trans; [exact MUT|]. eapply munch_weaken; [| exact MUp]. unfold sub_fp; cbn [outside]. intros xo (O1 & _ & O3 & _).
      split; [intros R; apply O1; clear - R LO; lia|]. split; [exact O3| exact I]. }
    pose proof (wmono_trans asegs _ _ _ WMT WMp) as WMT'.
    clear MUT WMT MUp WMp STK SHUK PES. rename MUT' into MUT, WMT' into WMT.
    replace (ret_pc (Z_to_bv 64 219652)) with (Z_to_bv 64 219652) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    zstep.
    assert (TCT : thread_clear L [(lo, q); (M, M + 4); (sh (M + 16), sh (M + 16) + rup8 n / 8); (THR + 2800, THR + 3168)]).
    { unhide T1. unhide T5. layout_apart_fact AO 0%nat 2%nat AP02. clear - T1 T2 T3 T4 T5 LP03 AP02 LOH LO CLO ACR MR BR CS SP1 SP2 SHB N8 NR. env_clear. }
    assert (TEP : thread_env L mP) by (eapply thread_env_frame; [exact TEK| exact MUT| exact WMT| exact TCT]).
    unhide Q16.
    eapply evt_cut.
    { eapply (gcts_spec L _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F_ fc (q - 48) mP lo).
      - exact STP.
      - exact CLO.
      - clear - LO; lia.
      - clear - Q16; Z.div_mod_to_equations; lia.
      - clear - QH; lia.
      - exact TEP.
      - exact TLO.
      - exact MIP. }
    hide Q16.
    cbv beta. unfold gcts_post. intros msG (g1 & mG & -> & MUg & WMg & MIG & STG & TEG).
    assert (DJG : forall A n0, (A + n0 <= q - 48 - 32 \/ q - 48 <= A) -> disjoint_from [(q - 48 - 32, q - 48)] A n0)
      by (intros A n0 D1; cbn [disjoint_from]; clear - D1; lia).
    eapply (rw_cells_transport asegs _ mP mG) in HS; [| exact MUg| exact WMg| cbn [cells_size csize Nat.add]; apply DJG; clear - MR BR CS SP1 SP2 CLO LO N8 NR; lia].
    eapply (rw_cells_transport asegs _ mP mG) in FRK; [| exact MUg| exact WMg| cbn [cells_size csize Nat.add]; apply DJG; clear; lia].
    eapply (rw_cells_transport asegs _ mP mG) in CBK; [| exact MUg| exact WMg| cbn [cells_size csize Nat.add]; apply DJG; clear - CBQ; lia].
    eapply (rw_cells_transport asegs _ mP mG) in TSK; [| exact MUg| exact WMg| cbn [cells_size csize Nat.add]; apply DJG; clear - T4 CLO LO; lia].
    eapply (rw_cells_transport asegs _ mP mG) in SHUP; [| exact MUg| exact WMg| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (apply Z.div_pos; clear - N8 NR; lia); apply DJG; clear - SHB LOH LO; lia].
    assert (MUT' : munch [(lo, q); (M, M + 4); (sh (M + 16), sh (M + 16) + rup8 n / 8); (THR + 2800, THR + 3168)] mK mG).
    { eapply munch_trans; [exact MUT|]. eapply munch_weaken; [| exact MUg]. unfold sub_fp; cbn [outside]. intros xo (O1 & _).
      split; [intros R; apply O1; clear - R LO; lia| exact I]. }
    pose proof (wmono_trans asegs _ _ _ WMT WMg) as WMT'.
    clear MUT WMT MUg WMg STP TEP MIP. rename MUT' into MUT, WMT' into WMT.
    replace (ret_pc (Z_to_bv 64 219656)) with (Z_to_bv 64 219656) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

    pose proof (rw_cells_split_CB asegs mG (THR + 2800) [] _ ts [] [40%nat; 8%nat; 8%nat; 312%nat] TSK ltac:(reflexivity)) as TSS.
    cbn [mk_CB_cells app] in TSS. clear TSK.
    remember (firstn 40 ts) as tsa eqn:Etsa. remember (skipn 40 ts) as ts1 eqn:Ets1. clear Etsa Ets1.
    remember (firstn 8 ts1) as tb1 eqn:E1. remember (skipn 8 ts1) as ts2 eqn:E2. clear E1 E2.
    remember (firstn 8 ts2) as tb2 eqn:E1. remember (skipn 8 ts2) as ts3 eqn:E2. clear E1 E2.
    remember (firstn 312 ts3) as tsb eqn:E1. clear E1.
    apply (rw_cells_CB_C8 asegs mG (THR + 2800) [CB 40 tsa] tb1) in TSS. cbn [app] in TSS.
    apply (rw_cells_CB_C8 asegs mG (THR + 2800) [CB 40 tsa; C8 (le_bytes_to_word tb1)] tb2) in TSS. cbn [app] in TSS.
    zstep.
    zstep.
    change (zx16 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
    replace (zx32 (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (unfold zx32; rewrite unsigned_lit by (clear - NR; lia); rewrite Z.mod_small by (clear - NR; lia); reflexivity).
    zstep.
    zstep.
    do 4 zstep.

    hide HS. hide FRK. hide CBK. hide SHUP. hide MUT. hide WMT.
    pose proof (munch_refl [(THR + 2800, THR + 3168)] mG) as MUs. pose proof (wmono_refl asegs mG) as WMs.
    zstep.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mT end.
    unhide HS. unhide FRK. unhide CBK. unhide SHUP. unhide MUT. unhide WMT.
    assert (DJS : forall A n0, (A + n0 <= THR + 2800 \/ THR + 3168 <= A) -> disjoint_from [(THR + 2800, THR + 3168)] A n0)
      by (intros A n0 D1; cbn [disjoint_from]; clear - D1; lia).
    eapply (rw_cells_transport asegs _ mG mT) in HS; [| exact MUs| exact WMs| cbn [cells_size csize Nat.add]; apply DJS; clear - MR BR CS SP1 SP2 LP03 T3 T4 N8 NR; lia].
    eapply (rw_cells_transport asegs _ mG mT) in FRK; [| exact MUs| exact WMs| cbn [cells_size csize Nat.add]; apply DJS; clear - T4 CLO LO; lia].
    eapply (rw_cells_transport asegs _ mG mT) in CBK; [| exact MUs| exact WMs| cbn [cells_size csize Nat.add]; apply DJS; clear - CBQ T4 CLO LO; lia].
    eapply (rw_cells_transport asegs _ mG mT) in SHUP; [| exact MUs| exact WMs| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (apply Z.div_pos; clear - N8 NR; lia); apply DJS; clear - SHB T3 T4; lia].
    assert (MUT' : munch [(lo, q); (M, M + 4); (sh (M + 16), sh (M + 16) + rup8 n / 8); (THR + 2800, THR + 3168)] mK mT).
    { eapply munch_trans; [exact MUT|]. eapply munch_weaken; [| exact MUs]. unfold sub_fp; cbn [outside]. intros xo (_ & _ & _ & O4 & _). split; [exact O4| exact I]. }
    pose proof (wmono_trans asegs _ _ _ WMT WMs) as WMT'.
    clear MUT WMT MUs WMs. rename MUT' into MUT, WMT' into WMT.
    zstep. if_cases KP; zify_cond KP. { exfalso. clear - KP BR SP1. lia. } clear KP.

    unhide MUK. unhide WMK.
    assert (PENVT : prim_env AL mT).
    { eapply prim_env_frame; [| exact MUT| exact WMT| exact AIT]. eapply prim_env_frame; [exact PENV| exact MUK| exact WMK|]. clear - BR CS SP1 LO CLO ACR. env_clear. }
    pose proof PENVT as PENVC. unfold prim_env in PENVC.
    zstep.
    zstep. if_cases K5; zify_cond K5. { exfalso. clear - K5 BR. lia. } clear K5.
    zstep.
    zstep. if_cases K6; zify_cond K6. { exfalso. clear - K6 BR CS. lia. } clear K6.
    zstep.
    do 3 zstep.
    assert (ECL : Z.shiftr ((Z.shiftl (B - al_space AL) 27) mod 18446744073709551616) 59 = c).
    { unhide EB. rewrite EB. unfold region. replace (al_space AL + c * 4294967296 + 16 * v - al_space AL) with (c * 4294967296 + 16 * v) by lia.
      rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
      assert (V32 : 0 <= 16 * v < 4294967296) by (clear - V0 VAU AU MUF CS; lia).
      rewrite Z.mod_small by (change (2^27) with 134217728; clear - Hc V32; lia).
      replace ((c * 4294967296 + 16 * v) * 2 ^ 27) with (c * 2^59 + 16 * v * 2^27) by (change (2^59) with (4294967296 * 2^27); lia).
      rewrite Z.div_add_l by lia. rewrite Z.div_small by (change (2^27) with 134217728; change (2^59) with 576460752303423488; clear - V32; lia). lia. }
    rewrite ECL. clear ECL.
    do 3 zstep.
    do 6 zstep.
    zstep. replace (q - 48 + 48) with q by lia.
    zstep.
    release_frame FRK STG q.
    lazymatch goal with H0 : stk asegs mT lo q |- _ => rename H0 into STT end.

    unhide SG1. unhide SG2. unhide SG3. unhide EB.
    assert (MUA : munch ([(q - 48, q); (B, B + 8)] ++ [(lo, q); (M, M + 4); (sh (M + 16), sh (M + 16) + rup8 n / 8); (THR + 2800, THR + 3168)]) m mT).
    { eapply munch_trans; [eapply munch_weaken; [| exact MUK]| eapply munch_weaken; [| exact MUT]]; unfold sub_fp; intros xo O; apply outside_app in O as [O1 O2]; assumption. }
    pose proof (wmono_trans asegs _ _ _ WMK WMT) as WMA.
    assert (RPT : RPRIM AL P mT).
    { apply (RPRIM_frame_ts AL AO P _ m mT RP MUA).
      - unfold prim_clear_ts. cbn [app].
        assert (SHS : sh (al_space AL + K_SPACE + 4096) <= 17594333495296) by (unfold sh, SHADOW_OFF; clear - SP5; Z.div_mod_to_equations; lia).
        assert (HELD : held1 P (c, v)) by (unhide VAL; unfold held1, cls_free; cbn [fst snd]; fold k; split; [exact Hc|]; split; [exact V0|]; split; [exact VAU|]; split; [exact VAL| exact VNI]).
        assert (PO : forall a b, lo <= a -> prim_out AL (a, b)) by (intros a b Ha; unfold prim_out; cbn [fst snd]; clear - Ha LOH CLO ACR T3 T4 SP2 SHS; repeat split; lia).
        repeat (apply Forall_cons || apply Forall_nil).
        + left. apply PO. clear - LO. lia.
        + right. left. exists c, v. split; [exact HELD|]. left. unfold chunk_iv. cbn [fst snd]. rewrite <- EB. clear - CS. lia.
        + left. apply PO. lia.
        + right. left. exists c, v. split; [exact HELD|]. left. unfold chunk_iv. cbn [fst snd]. rewrite <- EB. clear - MR N8 NR. lia.
        + right. left. exists c, v. split; [exact HELD|]. right. unfold chunk_sh_iv. cbn [fst snd]. rewrite <- EB.
          clear - SG1 SG2 SG3 RZ16 RZN N8 NR. pose proof (Z.div_pos rz 8). pose proof (Z.div_pos (class_size c - rz - rup8 n) 8). lia.
        + right. right. cbn [fst snd]. lia.
      - destruct (rw_cells_forget asegs mT _ _ TSS) as (tsj & TSJ). cbn [cells_size csize Nat.add] in TSJ. exists tsj. exact TSJ. }
    assert (PET : poison_env E mT) by (eapply poison_env_frame; [exact PEK| exact MUT| exact WMT| exact AIT]).
    assert (TET : thread_env L mT) by (eapply thread_env_frame; [exact TEK| exact MUT| exact WMT| exact TCT]).
    assert (SVT : shvis H mT) by (eapply shvis_wmono; [exact SVK| exact WMT]).

    unhide RESTK. unhide SHLK. unhide SHRK. unhide LCK.
    assert (DJT : forall A n0, A + n0 <= lo -> (A + n0 <= M \/ M + 4 <= A) -> (A + n0 <= sh (M + 16) \/ sh (M + 16) + rup8 n / 8 <= A) -> (A + n0 <= THR + 2800 \/ THR + 3168 <= A) ->
                    disjoint_from [(lo, q); (M, M + 4); (sh (M + 16), sh (M + 16) + rup8 n / 8); (THR + 2800, THR + 3168)] A n0)
      by (intros A n0 D1 D2 D3 D4; cbn [disjoint_from]; clear - D1 D2 D3 D4; lia).
    assert (GEO : al_space AL + K_REGION <= B /\ B + class_size c <= al_space AL + K_SPACE /\ B + class_size c <= lo
                  /\ (B + class_size c <= THR + 2800 \/ THR + 3168 <= B) /\ 17594333495296 <= B) by (clear - BR CS SP1 SP2 LP03 T3 T4 CLO; lia).
    eapply (rw_cells_transport asegs _ mK mT) in RESTK; [| exact MUT| exact WMT| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear - RZN N8 NR; lia); apply DJT; clear - GEO EM MR SHB RZ16 RZN N8 NR; lia].
    eapply (rw_cells_transport asegs _ mK mT) in SHLK; [| exact MUT| exact WMT| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (apply Z.div_pos; clear - RZ16; lia); apply DJT; clear - GEO MR SG1 SG4 SG5 SHB LOH T3 T4 RZ16 N8 NR; pose proof (Z.div_pos rz 8); pose proof (Z.div_pos (rup8 n) 8); lia].
    eapply (rw_cells_transport asegs _ mK mT) in SHRK; [| exact MUT| exact WMT| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (apply Z.div_pos; clear - RZN; lia); apply DJT; clear - GEO MR SG1 SG2 SG3 SG4 SG5 SHB LOH T3 T4 RZ16 RZN N8 NR; pose proof (Z.div_pos rz 8); pose proof (Z.div_pos (rup8 n) 8); pose proof (Z.div_pos (class_size c - rz - rup8 n) 8); lia].
    assert (FCB : exists j, rw_cells asegs mT B [CB (Z.to_nat (class_size c)) j]).
    { destruct (rw_cells_forget asegs mT _ _ HS) as (jh & HJ). cbn [cells_size csize Nat.add] in HJ.
      destruct (Z_lt_le_dec 16 rz) as [RZB|RZS].
      -
        unhide RZM. assert (RZ32 : 32 <= rz) by (clear - RZB RZM; Z.div_mod_to_equations; lia).
        destruct (LCJK RZB) as (j1 & LJ). pose proof (LCK RZB) as LK.
        eapply (rw_cells_transport asegs _ mK mT) in LJ; [| exact MUT| exact WMT| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear - RZ32; lia); apply DJT; clear - GEO EM MR SHB RZ32 N8 NR; lia].
        eapply (rw_cells_transport asegs _ mK mT) in LK; [| exact MUT| exact WMT| cbn [cells_size csize Nat.add]; apply DJT; clear - GEO EM MR SHB RZ32 N8 NR; lia].
        destruct (rw_cells_forget asegs mT _ _ LK) as (j0 & LK0). cbn [cells_size csize Nat.add] in LK0.
        pose proof (cb_join mT B 16 _ _ _ LK0 ltac:(replace (B + Z.of_nat 16) with (B + 16) by lia; exact LJ)) as J1.
        pose proof (cb_join mT B _ 16 _ _ J1 ltac:(replace (B + Z.of_nat (16 + Z.to_nat (rz - 32))) with M by (rewrite Nat2Z.inj_add, Z2Nat.id by (clear - RZ32; lia); clear - EM; lia); exact HJ)) as J2.
        pose proof (cb_join mT B _ _ _ _ J2 ltac:(replace (B + Z.of_nat (16 + Z.to_nat (rz - 32) + 16)) with (M + 16) by (rewrite !Nat2Z.inj_add, Z2Nat.id by (clear - RZ32; lia); clear - EM; lia); exact RESTK)) as J3.
        replace (16 + Z.to_nat (rz - 32) + 16 + Z.to_nat (class_size c - rz))%nat with (Z.to_nat (class_size c)) in J3 by (clear - RZ32 RZN N8 NR; lia).
        eexists. exact J3.
      - assert (RZE : rz = 16) by (clear - RZS RZ16; lia).
        pose proof (cb_join mT B 16 _ _ _ ltac:(replace B with M by (clear - EM RZE; lia); exact HJ) ltac:(replace (B + Z.of_nat 16) with (M + 16) by (clear - EM RZE; lia); exact RESTK)) as J1.
        replace (16 + Z.to_nat (class_size c - rz))%nat with (Z.to_nat (class_size c)) in J1 by (clear - RZE CS; lia).
        eexists. exact J1. }
    assert (FCS : rw_cells asegs mT (sh B) [CB (Z.to_nat (class_size c / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat (class_size c / 8)))]).
    { unfold fa_bytes in SHLK, SHRK.
      assert (D0 : 0 <= rz / 8 /\ 0 <= rup8 n / 8 /\ 0 <= (class_size c - rz - rup8 n) / 8 /\ rz / 8 + rup8 n / 8 + (class_size c - rz - rup8 n) / 8 = class_size c / 8).
      { split; [apply Z.div_pos; clear - RZ16; lia|]. split; [apply Z.div_pos; clear - N8 NR; lia|]. split; [apply Z.div_pos; clear - RZN; lia|]. clear - SG2 SG3. lia. }
      destruct D0 as (D1 & D2 & D3 & D4).
      pose proof (rw_cells_CB3 mT (sh B) _ _ _ (Z_to_bv 8 250) SHLK
                    ltac:(rewrite Z2Nat.id by exact D1; rewrite <- SG1; exact SHUP)
                    ltac:(rewrite !Z2Nat.id by assumption; rewrite <- SG2; exact SHRK)) as J.
      replace (Z.to_nat (rz / 8) + Z.to_nat (rup8 n / 8) + Z.to_nat ((class_size c - rz - rup8 n) / 8))%nat with (Z.to_nat (class_size c / 8)) in J by (rewrite <- D4; clear - D1 D2 D3; lia).
      exact J. }
    assert (FCT : free_chunk AL mT c v).
    { unfold free_chunk. rewrite <- EB. split; [exact FCB| exact FCS]. }
    clear FCB FCS RESTK SHLK SHRK SHUP HS.

    unhide Q16. unhide VAL.
    rewrite EB.
    lz_here.
    eapply implA_mono.
    { eapply (cdealloc_spec AL E ra gp _ _ _ s0 s1 _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F_ fc mT H q lo c v P AO).
      - assumption.
      - assumption.
      - exact SVT.
      - exact PET.
      - exact TET.
      - exact STT.
      - exact LOH.
      - exact CLO.
      - unfold CDEALLOC_STACK, MF_STACK. exact LO.
      - exact QH.
      - exact Q16.
      - exact Hc.
      - exact RPT.
      - exact POK.
      - exact V0.
      - exact VAU.
      - exact VAL.
      - exact VNI.
      - exact FCT. }
    intros a H' ms' PO. unfold cache_dealloc_post in PO. cbv zeta in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & -> & MUd & WMd & MId & STd & PEd & TEd & SVd & RPd & POKd).
    unfold arec_prim_post. exists u0, u1, u2, b0, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m'.
    split; [reflexivity|]. split; [reflexivity|].
    split.
    { unfold arec_W. rewrite <- EB.
      eapply munch_trans; [eapply munch_weaken; [| exact MUA]| eapply munch_weaken; [| exact MUd]].
      - unfold sub_fp, prim_W. cbn [app outside]. intros xo (O1 & _ & _ & _ & _ & _ & _ & O8 & O9 & O10 & _).
        split; [intros R; apply O1; clear - R LO; lia|]. split; [intros R; apply O9; clear - R CS; lia|].
        split; [exact O1|]. split; [intros R; apply O9; clear - R MR N8 NR; lia|].
        split; [intros R; apply O10; clear - R SG1 SG2 SG3 RZ16 RZN N8 NR; pose proof (Z.div_pos rz 8); pose proof (Z.div_pos (class_size c - rz - rup8 n) 8); lia|].
        split; [intros R; apply O8; clear - R; lia| exact I].
      - unfold sub_fp. intros xo O. apply outside_app in O as [O1 _]. exact O1. }
    split; [exact (wmono_trans asegs _ _ _ WMA WMd)|].
    split; [exact MId|]. split; [exact STd|]. split; [exact PEd|]. split; [exact TEd|]. split; [exact SVd|]. split; [exact RPd| exact POKd].
  Qed.

  #[using="Type"] Theorem arec_prim : forall (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32)
         (m : mem) (H : word -> bool) (q lo c v rz n CBA : Z) (P : prim) (stackw : word),
    alayout_ok AL -> mem_inv asegs m -> mclean H m -> shvis H m -> poison_env E m -> thread_env L m ->
    stk asegs m lo q -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo -> lo <= q - AREC_STACK -> q <= 2^47 -> q mod 16 = 0 ->
    RPRIM AL P m -> prim_ok P -> qchunk_wf (mkQC (QPrim c v) rz n) -> qchunk_rep AL m (mkQC (QPrim c v) rz n) -> held1 P (c, v) ->
    rw_cells asegs m CBA [C8 (wz CACHE); C8 stackw] -> q <= CBA -> CBA + 16 <= 2^47 ->
    implA H (t_cdealloc AL c (get_cls P c))
          (arec_prim_post ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc q lo c v P H m)
          (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz CBA) (wz (qc_hdr AL (mkQC (QPrim c v) rz n))) a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F_ (wz arec_entry) fc None m (seg_rom asegs)).
  Proof.
    intros ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m H q lo c v rz n CBA P stackw
           AO MI MC SV PE TE ST LOH CLO LO QH Q16 RP POK CHW CHR HELD CBC CBQ CB47.
    unfold arec_entry, AREC_STACK, CDEALLOC_STACK, MF_STACK in *.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & _).
    layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
    layout_apart_fact AO 0%nat 3%nat LP03.
    pose proof HELD as HELD0. pose proof CHW as CHW0. pose proof CHR as CHR0.
    destruct HELD as (Hc & V0 & VAU & VAL & VNI). cbn [fst snd] in Hc, V0, VAU, VAL, VNI.
    destruct CHW as (RZ16 & RZM & NR & RZN & (_ & _ & _)). cbn [qc_rz qc_n qc_kind qc_bsize] in RZ16, RZM, NR, RZN.
    pose proof (class_size_pos c Hc) as CS. pose proof (class_size_mod16 c Hc) as CS16.
    pose proof (region_range AL c Hc) as [R1 R2].
    set (k := get_cls P c) in *.
    pose proof RP as (LEN & PENV & CLS & STAT & (ts & TS)).
    destruct (CLS c Hc) as (WF & RIc & _). fold k in WF, RIc.
    pose proof WF as (_ & _ & _ & _ & _ & _ & AU & MUF & _).
    unfold qc_hdr, qc_blk. cbn [qc_kind qc_rz].
    set (B := region AL c + 16 * v) in *. set (M := B + rz - 16) in *.
    assert (BR : al_space AL + K_REGION <= B /\ B + class_size c <= al_space AL + K_SPACE /\ B mod 16 = 0).
    { unfold B. split; [clear - R1 V0; lia|]. split; [clear - R2 VAU AU MUF; lia|]. unfold region. clear - SPM. Z.div_mod_to_equations. lia. }
    assert (MR : B + 0 <= M /\ M + 16 + rup8 n <= B + class_size c /\ M mod 16 = 0).
    { unfold M. split; [clear - RZ16; lia|]. split; [clear - RZN; lia|]. destruct BR as (_ & _ & B16). clear - B16 RZM. Z.div_mod_to_equations. lia. }
    assert (EM : M = B + rz - 16) by reflexivity. assert (EB : B = region AL c + 16 * v) by reflexivity.
    assert (N8 : n <= rup8 n < n + 8 /\ rup8 n mod 8 = 0) by (unfold rup8; clear; Z.div_mod_to_equations; lia).
    clearbody M B.
    hide T1. hide T5. hide T6. hide T7. hide SPM. hide Q16. hide RZM. hide CS16. hide VAL. hide EM. hide EB.
    pose proof (munch_refl [(q - 48, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    lz_go.
    zstep. carve_frame 48%nat ST.
    do 6 zstep.
    do 4 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.

    replace (q + -48) with (q - 48) in * by lia.
    unfold prim_env in PENV.
    pose proof (rw_cells_transport asegs _ m mA _ _ PENV MU WM ltac:(cbn [disjoint_from cells_size csize Nat.add]; clear - LO CLO ACR; lia)) as PENVA.
    zstep.
    do 2 zstep.
    zstep. if_cases K1; zify_cond K1. { exfalso. clear - K1 BR MR SP1 SP5. lia. } clear K1.
    zstep.
    zstep. if_cases K2; zify_cond K2. { exfalso. clear - K2 BR MR N8 NR SP1 SP5. lia. } clear K2.
    do 3 zstep.

    set (off := M - region AL c) in *.
    assert (OFF : 16 * v <= off /\ off + 16 + rup8 n <= 16 * v + class_size c /\ off = 16 * v + (rz - 16)) by (unfold off; unhide EM; unhide EB; clear - EM EB MR; lia).
    assert (EMS : M - al_space AL = c * 4294967296 + off) by (unfold off, region; clear; lia).
    assert (OFR : 0 <= off < 4294967296) by (clear - OFF V0 VAU AU MUF N8 NR; lia).
    assert (EC : Z.shiftr (M - al_space AL) 32 = c).
    { rewrite EMS, Z.shiftr_div_pow2 by lia. change (2^32) with 4294967296. rewrite Z.div_add_l by lia. rewrite (Z.div_small off) by exact OFR. lia. }
    rewrite EC.
    assert (EL : Z.land c 31 = c) by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; apply Z.mod_small; change (2^5) with 32; clear - Hc; lia).
    rewrite EL.
    zstep.
    eapply evt_cut; [eapply (arec_size _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F_ fc mA c Hc)|].
    cbv beta. intros ms1 (a6' & a7' & ->).
    zstep.
    set (sz := class_size c) in *. set (idx := 16 * v / sz) in *.
    assert (EIDX : 16 * v = sz * idx /\ 0 <= idx /\ off / sz = idx).
    { unhide VAL. pose proof (Z_div_exact_full_2 (16 * v) sz ltac:(clear - CS; lia) VAL) as X. fold idx in X.
      split; [exact X|]. split; [unfold idx; apply Z.div_pos; clear - V0 CS; lia|].
      destruct OFF as (_ & O2 & O3). rewrite O3, X, Z.mul_comm, Z.div_add_l by (clear - CS; lia).
      rewrite (Z.div_small (rz - 16)) by (clear - RZ16 O2 O3 N8 NR; lia). lia. }
    destruct EIDX as (EIDX & IDX0 & EDV).
    assert (IDXB : idx < 2^27) by (clear - EIDX OFR OFF CS IDX0; nia).
    assert (EDIV : v_divuw (Z_to_bv 64 (M - al_space AL)) (Z_to_bv 64 sz) = Z_to_bv 64 idx).
    { unfold v_divuw. rewrite !unsigned_lit by (clear - EMS OFR Hc CS; lia). unfold bv_wrap. change (bv_modulus 32) with 4294967296.
      rewrite (Z.mod_small sz) by (clear - CS; lia). replace (sz =? 0) with false by (symmetry; apply Z.eqb_neq; clear - CS; lia).
      rewrite EMS, Z.add_comm, Z_mod_plus_full, (Z.mod_small off) by exact OFR. rewrite EDV.
      f_equal. apply STRW_merge.swrap32_small. clear - IDX0 IDXB. lia. }
    rewrite EDIV. clear EDIV.
    zstep.
    zstep.
    do 4 zstep.
    destruct RIc as (j8 & j64 & j88 & j96 & j104 & j112 & jpad & RIC).
    pose proof (rw_cells_transport asegs _ m mA _ _ RIC MU WM ltac:(unfold ri_addr, RIB, ri_cells; cbn [disjoint_from cells_size csize Nat.add]; clear - LO CLO SP2 Hc; lia)) as RICA.
    unfold ri_addr, RIB, ri_cells in RICA.
    rewrite !Z.shiftl_mul_pow2 by lia. change (2^7) with 128. change (2^32) with 4294967296.
    unfold RIB. replace (al_space AL + 137438953472 + c * 128) with (al_space AL + 137438953472 + 128 * c) by lia.
    zstep.
    zstep.
    replace (Z.shiftr (idx * 4294967296) 32) with idx by (rewrite Z.shiftr_div_pow2 by lia; change (2^32) with 4294967296; rewrite Z.div_mul by lia; reflexivity).
    zstep.
    rewrite <- EIDX. hide EIDX. hide EDV. clear IDXB.
    zstep.
    zstep.
    replace (p_mu k <? 16 * v + sz) with false by (symmetry; apply Z.ltb_ge; clear - VAU AU; unfold sz; lia). cbn [Z.b2z].
    zstep.
    zstep.
    zstep.
    replace (Z.land 18446744073709551615 (c * 4294967296 + al_space AL + 16 * v)) with B.
    2: { unhide EB. rewrite EB. unfold region. rewrite Z.land_comm. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
         rewrite Z.mod_small by (clear - SP1 SP5 Hc V0 VAU AU MUF CS; change (2^64) with 18446744073709551616; lia). lia. }
    zstep. if_cases K3; zify_cond K3. { exfalso. clear - K3 BR SP1. lia. } clear K3.
    zstep. if_cases K4; zify_cond K4. { exfalso. clear - K4 BR CS SP1. lia. } clear K4.
    zstep.
    clear PENVA RICA.
    destruct CHR as ((bits & actx & HDR) & LCH & _). unfold qc_hdr, qc_blk in HDR, LCH. cbn [qc_kind qc_rz qc_n qc_bsize] in HDR, LCH.
    unhide EM. unhide EB.
    replace (region AL c + 16 * v + rz - 16) with M in HDR, LCH by (rewrite EM, EB; clear; lia). rewrite <- EB in LCH.
    pose proof (rw_cells_transport asegs _ m mA _ _ HDR MU WM ltac:(cbn [disjoint_from cells_size csize Nat.add]; clear - MR BR CS SP2 CLO LO N8 NR; lia)) as HDRA.
    if_cases KE; zify_cond KE.
    -
      assert (RZE : rz = 16) by (clear - KE EM; lia).
      rewrite EM, EB in HDRA |- *.
      eapply (arec_prim_tail ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m mA H q lo c v rz n CBA P stackw bits actx
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AO SV PE TE LOH CLO).
      + unfold AREC_STACK, CDEALLOC_STACK, MF_STACK. exact LO.
      + exact QH.
      + unhide Q16. exact Q16.
      + exact RP.
      + exact POK.
      + exact CHW0.
      + exact CHR0.
      + exact HELD0.
      + exact CBQ.
      + exact CB47.
      + refine (munch_weaken _ _ _ _ _ MU). unfold sub_fp; cbn [outside]. intros xo (O1 & _). split; [exact O1| exact I].
      + exact WM.
      + assumption.
      + exact ST.
      + exact FR.
      + exact CBC.
      + intros X. exfalso. clear - X RZE. lia.
      + exact HDRA.
    -
      assert (RZ32 : 16 < rz) by (clear - KE EM RZ16; lia).
      destruct (LCH RZ32) as (LC & _). clear LCH.
      pose proof (rw_cells_transport asegs _ m mA _ _ LC MU WM ltac:(cbn [disjoint_from cells_size csize Nat.add]; clear - BR CS SP2 CLO LO; lia)) as LCA.
      hide EM. hide EB.
      zstep. zstep.
      assert (AMOB : amo_aligned AD (Z_to_bv 64 B) = true) by (apply amo_aligned_intro_d; [clear - BR SP1 SP5 CS; lia| destruct BR as (_ & _ & B16); clear - B16; Z.div_mod_to_equations; lia]).
      amo_step_h AMOB.
      zstep. lit_branch.

      hide HDRA. hide FR. hide CBC. hide MU. hide WM.
      pose proof (munch_refl [(B, B + 8)] mA) as MUb. pose proof (wmono_refl asegs mA) as WMb.
      amo_step_h AMOB.   fix_lit_store.
      zstep. lit_branch.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mB end.
      unhide HDRA. unhide FR. unhide CBC. unhide MU. unhide WM. unhide EM. unhide EB.
      assert (DJB : forall A n0, (A + n0 <= B \/ B + 8 <= A) -> disjoint_from [(B, B + 8)] A n0) by (intros A n0 D1; cbn [disjoint_from]; clear - D1; lia).
      eapply (rw_cells_transport asegs _ mA mB) in HDRA; [| exact MUb| exact WMb| cbn [cells_size csize Nat.add]; apply DJB; clear - EM RZ32 RZM; unfold id in RZM; Z.div_mod_to_equations; lia].
      eapply (rw_cells_transport asegs _ mA mB) in FR; [| exact MUb| exact WMb| cbn [cells_size csize Nat.add]; apply DJB; clear - BR CS SP2 CLO LO; lia].
      eapply (rw_cells_transport asegs _ mA mB) in CBC; [| exact MUb| exact WMb| cbn [cells_size csize Nat.add]; apply DJB; clear - CBQ BR CS SP2 CLO LO; lia].
      rewrite EM, EB in HDRA, LCA |- *.
      eapply (arec_prim_tail ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m mB H q lo c v rz n CBA P stackw bits actx
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AO SV PE TE LOH CLO).
      + unfold AREC_STACK, CDEALLOC_STACK, MF_STACK. exact LO.
      + exact QH.
      + unhide Q16. exact Q16.
      + exact RP.
      + exact POK.
      + exact CHW0.
      + exact CHR0.
      + exact HELD0.
      + exact CBQ.
      + exact CB47.
      + rewrite <- EB. eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MUb]]; unfold sub_fp; cbn [outside]; intros xo (O1 & O2 & _); (split; [assumption| exact I]).
      + exact (wmono_trans asegs _ _ _ WM WMb).
      + assumption.
      + exact ST.
      + exact FR.
      + exact CBC.
      + intros _. exact LCA.
      + exact HDRA.
  Qed.
End AREC.
