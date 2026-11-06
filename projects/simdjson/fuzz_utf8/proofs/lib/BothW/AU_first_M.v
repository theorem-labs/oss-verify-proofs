(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes InitMem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessU ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import BImg RtCells AProto ABase MonadF AMalloc_iface ABytes F_apoison F_annot I_asan_memset.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import AU_kit AU_iface AU_consts AU_parts_iface AU_client_kit AU_h_kit AU_annot_nop AU_first_A AU_first_C AH_memcpy0.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Ltac retlit := lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; rpc) end.
Ltac ag_of_hpr H := lazymatch type of H with aheap_pres ?CI ?LB ?SP ?m ?m' => change (aheap_pres CI LB SP m m') with (magree bsegs (aclient_addr CI LB SP) m m') in H end.

(* [comment removed for export] *)
Ltac xall MU WM :=
  lazymatch type of MU with munch ?W ?mo ?mn =>
    repeat match goal with
    | H : rw_cells _ mo ?A ?cs |- _ =>
        apply (rw_cells_transport bsegs W mo mn A cs) in H;
        [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul fst snd]; lia]
    | H : stk _ mo ?loq ?hiq |- _ =>
        apply (stk_transport_disjoint bsegs W mo mn loq hiq) in H; [| exact MU| exact WM| cbn [disjoint_from]; lia]
    | H : wr_at _ mo ?A ?n |- _ => apply (wr_at_transport bsegs mo mn A n) in H; [| exact WM]
    end end.

Section CANSEC1. Context {rc : runConstT}.
Definition RSI_STACK : Z := 8192.
(* [comment removed for export] *)
Definition RSI_W : list (Z * Z) := (AVEC, AVEC + 24) :: RSI_IMGW.

(* [comment removed for export] *)
Lemma shz7_of_client_sh : forall m, client_sh m -> shz7 m.
Proof.
  intros m CS. unfold shz7, shz.
  assert (X : forall X, In X client_sh_addrs -> rw_cells bsegs m (shad X) [C1 (Z_to_bv 8 0)]).
  { intros X HX. apply c1_of_byte; [| | apply CS; exact HX]; unfold client_sh_addrs in HX; cbn [In] in HX;
      repeat (destruct HX as [<-|HX]; [vm_compute; discriminate|]); destruct HX. }
  unfold client_sh_addrs in X. repeat split; apply X; cbn [In]; tauto.
Qed.

(* [comment removed for export] *)
Lemma byte_of_c1' : forall m s b, rw_cells bsegs m s [C1 b] -> 0x6d2000 <= s -> m (wa s) = Some b.
Proof.
  intros m s b [[_ (A & B & H)] _] Hs. cbn [cells_bytes cbytes app length] in B, H.
  specialize (H 0%nat ltac:(lia)). cbn in H. rewrite Z.add_0_r in H.
  rewrite <- (mrd_no_image bsegs m s (s + 1) s (no_image_asan s (s + 1) Hs)) by lia.
  rewrite H. cbn. reflexivity.
Qed.
Lemma unpoisoned_avec : forall m, shz 0x6ad760 m -> shz 0x6ad768 m -> shz 0x6ad770 m -> unpoisoned m AVEC (AVEC + 24).
Proof.
  intros m C0 C1' C2. unfold AVEC, shz in *. split; [lia|]. split; [lia|]. intros G _ H1 H2.
  assert (E : G = 875244 \/ G = 875245 \/ G = 875246) by lia.
  exists (Z_to_bv 8 0). split; [| left; reflexivity].
  destruct E as [->|[->| ->]].
  - change (ASHOFF + 875244) with (shad 0x6ad760). apply byte_of_c1'; [exact C0| vm_compute; discriminate].
  - change (ASHOFF + 875245) with (shad 0x6ad768). apply byte_of_c1'; [exact C1'| vm_compute; discriminate].
  - change (ASHOFF + 875246) with (shad 0x6ad770). apply byte_of_c1'; [exact C2| vm_compute; discriminate].
Qed.

(* [comment removed for export] *)
Section ShPres.
  Variable CI : list (Z * Z).
  Lemma shz_pres : forall LB SP m m' X iv, aheap_pres CI LB SP m m' -> In iv CI -> fst iv <= X < snd iv -> 0 <= X < 2^47 -> shz X m -> shz X m'.
  Proof.
    intros LB SP m m' X iv HPR HIN HX XB SZ. unfold shz in *. eapply rw_cells_magree; [exact HPR| exact SZ|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat].
    intros a Ha. replace a with (shad X) by lia. right; right; right. exists X. split; [| reflexivity]. right; left. exists iv. split; [exact HIN| exact HX].
  Qed.
  Lemma shc_pres : forall LB SP m m' X, aheap_pres CI LB SP m m' -> ATOP <= X < 2^47 -> shc X m -> shc X m'.
  Proof.
    intros LB SP m m' X HPR HX SC. unfold shc in *. eapply rw_cells_magree; [exact HPR| exact SC|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat].
    intros a Ha. replace a with (shad X) by (unfold shad, ASHOFF; lia). right; right; right. exists X. split; [| reflexivity]. left. exact HX.
  Qed.
End ShPres.
Lemma aclient_addr_mono_sp' : forall CI LB SP SP' a, aclient_addr CI LB SP a -> SP' <= SP -> aclient_addr CI LB SP' a.
Proof.
  intros CI LB SP SP' a Hc HS.
  destruct Hc as [Hc|[Hc|[Hc|(a' & Ha' & ->)]]]; [left; lia| right; left; exact Hc| right; right; left; exact Hc|].
  right; right; right. exists a'. split; [| reflexivity]. destruct Ha' as [H|[H|H]]; [left; lia| right; left; exact H| right; right; exact H].
Qed.

Section M.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Hypothesis IMG_CI : forall iv, In iv client_ranges -> In iv CI.
  Hypothesis OPNEW : opnew_stmtA AI.

  Definition rsi_post (L : alayout) (RNG : footprint)
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
      (s : APS) (LBc : list ablock) (lo : Z) (m : amem)
      (p : AsanCtrl.aptr) (s' : APS) (RNG' : footprint) : machine_state -> Prop :=
    fun ms' => fp_le RNG RNG' /\ exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : amem) (V : Z),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               FR (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
      /\ magree bsegs (fun a => aclient_addr CI LBc (bv_unsigned sp) a /\ outside RSI_W a) m m'
      /\ aps_rest s' = aps_rest s
      /\ ablock_range V 8
      /\ AHEAP AI L RNG' (aps_m s') (HB p V 8 :: LBc) m'
      /\ rw_cells bsegs m' V [C8 (Z_to_bv 64 AFALLBACK)]
      /\ rw_cells bsegs m' AVEC [C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 (V + 8)); C8 (Z_to_bv 64 (V + 8))]
      /\ simdjson_statics m'.

  Definition rsi_stmt : Prop :=
    forall (L : alayout) (RNG : footprint)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (FR : bvmap 5 word) (fc : bv 32) (m : amem) (s : APS) (LBc : list ablock) (lo : Z),
      AHEAP AI L RNG (aps_m s) LBc m -> mem_inv bsegs m ->
      stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - RSI_STACK ->
      bv_unsigned sp <= al_top L -> bv_unsigned sp + 16 <= 2^47 -> bv_unsigned sp mod 16 = 0 ->
      tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 AVEC ->
      In [AMALLOC_PC; AOPNEW_RET] (al_U L) ->
      rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG ->
      aps_ok L s ->
      client_img m -> client_sh m ->
      rw_cells bsegs m AVEC [C8 w0; C8 w0; C8 w0] ->
      rw_cells bsegs m 0x6ad860 guard0 -> rw_cells bsegs m 0x6ad880 [C8 w0; C8 w0] -> rw_cells bsegs m 0x6ad8a0 guard0 ->
      rw_cells bsegs m 0x6ad8c0 [C8 w0] ->
      rw_cells bsegs m AFALLBACK [C8 w0; C8 w0; C8 w0; C8 w0; C8 w0; C4 w0] -> rw_cells bsegs m 0x6ad940 guard0 ->
      wr_at bsegs m (shad 0x6ad740) 8 ->
      unpoisoned m (bv_unsigned sp - 216) (bv_unsigned sp - 176) -> rng RNG (shad (bv_unsigned sp - 216)) 5 ->
      implMA RNG (HarnessU.opnew amalloc_M (new_handlerA AAllocAsan) CLIENT_VEC_BYTES) s
             (rsi_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc s LBc lo m)
             (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 FR (Z_to_bv 64 ARSI) fc None m (seg_rom bsegs)).

  Ltac pick_in := (left; reflexivity) + (right; pick_in).
  Ltac in_cr := apply IMG_CI; unfold client_ranges; cbn [In]; tauto.

  (* [comment removed for export] *)
  Lemma cl_outside_stack : forall L RNG st LBx m SP lo a,
    AHEAP AI L RNG st LBx m -> ATOP + 4096 <= lo -> aclient_addr CI LBx SP a -> a < lo \/ SP <= a.
  Proof.
    intros L RNG st LBx m SP lo a AHx BOT Ha. atop_facts.
    destruct Ha as [X|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - right; lia.
    - left. pose proof (AI_aci_img AI iv Hiv). unfold AIMG_HI in *. lia.
    - left. pose proof (AI_block_bounds AI _ _ _ _ _ b AHx Hb). lia.
    - left. assert (A47 : 0 <= a' < 2^47).
      { destruct Ha' as [X|[(iv & Hiv & Hr)|(c & FA' & fn & Hb' & Hr)]]; [lia| pose proof (AI_aci_img AI iv Hiv); pose proof (AI_aci_lo AI iv Hiv); unfold AIMG_HI in *; lia|].
        pose proof (AI_block_bounds AI _ _ _ _ _ _ AHx Hb') as BB. cbn [ab_addr ab_size] in BB. unfold AIMG_HI in BB. lia. }
      pose proof (shad_in_band a' A47). lia.
  Qed.
  (* [comment removed for export] *)
  Lemma cl_outside_new : forall L RNG st LBx m SP q V a,
    AHEAP AI L RNG st (HB q V 8 :: LBx) m -> aclient_addr CI LBx SP a -> SP + 0 >= ATOP -> ~ (V <= a < V + 8).
  Proof.
    intros L RNG st LBx m SP q V a AHx Ha HSP.
    destruct (AI_block AI _ _ _ _ _ _ _ _ AHx ltac:(left; reflexivity)) as (_ & (R1 & R2 & R3 & R4) & _).
    pose proof (ablk_lin _ _ R1) as (R1a & R1b & R1c & R1d). unfold AIMG_HI in R1a.
    pose proof (AI_blocks_nodup AI _ _ _ _ _ AHx) as ND. inversion ND as [|x l NI ND']; subst.
    destruct Ha as [X|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - lia.
    - pose proof (AI_aci_img AI iv Hiv). unfold AIMG_HI in *. lia.
    - assert (NE : HB q V 8 <> b) by (intros E; apply NI; rewrite E; exact Hb).
      pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AHx ltac:(left; reflexivity) ltac:(right; exact Hb) NE) as D0. cbn in D0. lia.
    - assert (A47 : 0 <= a' < 2^47).
      { atop_facts. destruct Ha' as [X|[(iv & Hiv & Hr)|(c & FA' & fn & Hb' & Hr)]]; [lia| pose proof (AI_aci_img AI iv Hiv); pose proof (AI_aci_lo AI iv Hiv); unfold AIMG_HI in *; lia|].
        pose proof (AI_block_bounds AI _ _ _ _ _ _ AHx ltac:(right; exact Hb')) as BB. cbn [ab_addr ab_size] in BB. unfold AIMG_HI in BB. lia. }
      intros X. eapply (ablk_clear_band _ _ _ R1); [| exact X]. pose proof (shad_in_band a' A47). unfold KLS in *. lia.
  Qed.

  Theorem rsi_proof : rsi_stmt.
  Proof.
    unfold rsi_stmt, RSI_STACK. intros until lo.
    intros AH MI ST BOT LOS TOP SPT SP16 TP -> HU RSTK RI RISH ROK IG USH VEC G1 IL G2 ARR SGL G3 WSH UST RSS0.
    set (SP := bv_unsigned sp) in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. fold SP in RSP. atop_facts.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (L1 & L2 & L3 & L4 & _).
    pose proof IG as (_ & VT & _).
    pose proof (shz7_of_client_sh _ USH) as SZ7.
    (* [comment removed for export] *)
    eapply implMA_evtF.
    { pose proof (AI_rtcells AI _ _ _ _ _ AH) as (_ & GOT0 & _ & _ & SHB0 & _).
      eapply rsi_a1 with (lo := lo); first [exact ST| exact MI| exact GOT0| exact SHB0| exact RI| fold SP; lia| (eapply rng_sub'; [exact RSTK| fold SP; lia])]. }
    cbv beta. fold SP. intros ms1 (m1 & j1 & j2 & -> & MU1 & WM1 & MI1 & FRR1 & ST1).
    assert (AH1 : AHEAP AI L RNG (aps_m s) LBc m1).
    { eapply (AI_frame AI); [exact AH| exact MU1| exact WM1|]. constructor; [left; left; cbn; lia| constructor]. }
    (* [comment removed for export] *)
    destruct SZ7 as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
    assert (SC4 : shc (SP + -216) m /\ shc (SP + -208) m /\ shc (SP + -200) m /\ shc (SP + -192) m /\ shc (SP + -184) m).
    { unfold shc. change 2147450880 with ASHOFF.
      repeat split; (eapply (fun P U A B => proj1 (unpoisoned8_c1 m P U A B)); [eapply unpoisoned_sub; [exact UST| lia| lia]| clear - SP16; fold SP in SP16; Z.div_mod_to_equations; lia| unfold KEND; lia]). }
    destruct SC4 as (T0 & T1 & T2 & T3 & T4). clear UST.
    unfold shz, shc, AVEC, AFALLBACK, AVTAB_SRS, ASRS_FN, guard0, w0, RSIFR in *.
    change (shad 0x6ad8c0) with 2148326168 in *. change (shad 0x6ad8e0) with 2148326172 in *. change (shad 0x16c340) with 2147637352 in *.
    change (shad 0x6ad908) with 2148326177 in *. change (shad 0x6ad768) with 2148326125 in *. change (shad 0x6ad770) with 2148326126 in *.
    change (shad 0x6ad760) with 2148326124 in *. change (shad 0x6ad740) with 2148326120 in *.
    assert (BSS : 2148344832 <= Z.shiftr (SP + -216) 3 + 2147450880 /\ Z.shiftr (SP + -184) 3 + 2147450880 + 1 <= 17594333495296
                  /\ Z.shiftr (SP + -208) 3 = Z.shiftr (SP + -216) 3 + 1 /\ Z.shiftr (SP + -200) 3 = Z.shiftr (SP + -216) 3 + 2
                  /\ Z.shiftr (SP + -192) 3 = Z.shiftr (SP + -216) 3 + 3 /\ Z.shiftr (SP + -184) 3 = Z.shiftr (SP + -216) 3 + 4)
      by (rewrite !Z.shiftr_div_pow2 by lia; clear - SP16 SPT RSP LOS BOT H; Z.div_mod_to_equations; lia).
    assert (RSSa : rng RNG (Z.shiftr (SP + -216) 3 + 2147450880) 5) by (eapply rng_sub'; [exact RSS0| unfold shad, ASHOFF; replace (SP - 216) with (SP + -216) by lia; lia]).
    set (PA := fun a => aclient_addr CI LBc SP a /\ outside RSI_W a).
    assert (PSTK : forall a, PA a -> a < lo \/ SP <= a) by (intros a [Ha _]; eapply cl_outside_stack; [exact AH| exact BOT| exact Ha]).
    assert (PIMG : forall a, PA a -> outside [(7001952, 7001952 + 24); (0x6ad860, 0x6ad862); (0x6ad880, 0x6ad890); (0x6ad8a0, 0x6ad8a2); (0x6ad8c0, 0x6ad8c8); (0x6ad8e0, 0x6ad90c); (0x6ad940, 0x6ad942)] a)
      by (intros a [_ Ha]; exact Ha).
    assert (AG1 : magree bsegs PA m m1).
    { eapply magree_mono; [eapply magree_of_munch; [exact MU1| exact WM1]|]. intros a Ha. pose proof (PSTK a Ha). cbn [outside]. lia. }
    xall MU1 WM1. clear MU1 WM1 AH MI.
    (* [comment removed for export] *)
    assert (VECB : rw_cells bsegs m1 7001952 [CB 24 (repeat (Z_to_bv 8 0) 24)])
      by (eapply rw_cells_recast; [exact VEC| cbn; split; [reflexivity| exact I]| vm_compute; reflexivity| reflexivity]).
    clear VEC.
    assert (UAV : unpoisoned m1 7001952 (7001952 + 24)) by (apply (unpoisoned_avec m1); unfold shz; assumption).
    eapply implMA_evtF.
    { pose proof (AI_rtcells AI _ _ _ _ _ AH1) as (_ & GOT1 & RIC1 & REAL1 & SHB1 & _ & INI1 & LAY1 & _).
      eapply (asan_memset_spec RNG) with (lo := lo) (junk := repeat (Z_to_bv 8 0) 24) (RLO2 := 0x6ad740) (RHI2 := 0x6ad780);
        rewrite ?unsigned_lit by lia;
        first [exact MI1| exact ST1| exact GOT1| exact RIC1| exact SHB1| exact INI1| exact LAY1| exact REAL1| exact VECB| exact UAV| exact RI| exact WSH
              | (eapply rng_sub'; [exact RSTK| lia]) | (eapply rng_sub'; [exact RI| lia]) | (eapply rng_sub'; [exact RISH| vm_compute; split; discriminate])
              | (left; lia) | (unfold app_blk, KLOW; lia) | (unfold KHIGH, KEND; repeat split; first [lia| reflexivity]) | (unfold KHIGH; lia) ]. }
    cbv beta. intros ms2 PO. destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & ST2 & VEC2).
    rewrite !unsigned_lit in MU2 by lia. rewrite !unsigned_lit in ST2 by lia. rewrite !unsigned_lit in VEC2 by lia. retlit.
    assert (AH2 : AHEAP AI L RNG (aps_m s) LBc m2).
    { eapply (AI_frame AI); [exact AH1| exact MU2| exact WM2|]. constructor; [left; left; cbn; lia| constructor; [| constructor]].
      left; right; left. exists (0x6ad740, 0x6ad780). split; [in_cr| cbn; rewrite ?unsigned_lit by lia; lia]. }
    assert (AG2 : magree bsegs PA m m2).
    { eapply magree_trans; [exact AG1|]. eapply magree_mono; [eapply magree_of_munch; [exact MU2| exact WM2]|]. intros a Ha. pose proof (PSTK a Ha). pose proof (PIMG a Ha) as PI. cbn [outside] in PI |- *. lia. }
    clear VECB UAV AG1. xall MU2 WM2. clear MU2 WM2 AH1 MI1 ST1.
    assert (VEC : rw_cells bsegs m2 7001952 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)])
      by (eapply rw_cells_recast; [exact VEC2| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity]).
    clear VEC2.
    (* [comment removed for export] *)
    eapply implMA_evtF.
    { pose proof (AI_rtcells AI _ _ _ _ _ AH2) as (_ & GOT2 & _ & _ & SHB2 & _).
      eapply rsi_a2 with (lo := lo) (sp := sp);
        first [exact ST2| exact MI2| exact GOT2| exact SHB2| exact RI| exact RISH| exact FRR1| exact VEC| exact G1| exact IL| exact G2| exact ARR| exact SGL| exact G3| exact VT
              | (split; [exact T0| split; [exact T1| split; [exact T2| split; [exact T3| exact T4]]]])
              | exact RSSa
              | (split; [exact S1| split; [exact S2| split; [exact S3| split; [exact S4| split; [exact S5| split; [exact S6| exact S7]]]]]]) | fold SP; lia| (eapply rng_sub'; [exact RSTK| fold SP; lia])]. }
    cbv beta. fold SP. intros ms3 (m3 & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & j3 & js3 & -> & MU3 & WM3 & MI3 & ST3 & FRA3 & FRE3 & FRR3 & VEC3 & SS3 & VT3 & SZ3 & SH3).
    assert (AH3 : AHEAP AI L RNG (aps_m s) LBc m3).
    { eapply (AI_frame AI); [exact AH2| exact MU3| exact WM3|]. unfold RSI_IMGW.
      constructor; [left; left; cbn; lia|].
      repeat (constructor; [left; right; left; eexists; split; [apply IMG_CI; unfold client_ranges; pick_in| cbn; lia]|]). constructor. }
    clear VEC G1 IL G2 ARR SGL G3 VT S1 S2 S3 S4 S5 S6 S7 FRR1 T0 T1 T2 T3 T4. destruct SH3 as (T0 & T1 & T2 & T3 & T4). unfold shc in T0, T1, T2, T3, T4. unfold RSI_IMGW in MU3.
    assert (AG3 : magree bsegs PA m m3).
    { eapply magree_trans; [exact AG2|]. eapply magree_mono; [eapply magree_of_munch; [exact MU3| exact WM3]|]. intros a Ha. pose proof (PSTK a Ha). pose proof (PIMG a Ha) as PI. cbn [outside] in PI |- *. lia. }
    clear AG2. xall MU3 WM3. clear MU3 WM3 AH2 MI2 ST2.
    (* [comment removed for export] *)
    eapply implMA_post_evtF.
    { unfold CLIENT_VEC_BYTES. eapply OPNEW with (lo := lo) (LB := LBc);
        first [exact AH3| exact MI3| exact BOT| exact TP| reflexivity| exact HU| exact RSTK| exact ROK
              | rewrite ?unsigned_lit by lia; first [exact ST3| unfold OPNEW_STACK_A, AMALLOC_STACK, AREQMAX in *; lia| (clear - SP16; fold SP in SP16; Z.div_mod_to_equations; lia)] ]. }
    cbv beta. intros p s4' RNG4 ms4 PO.
    destruct PO as (FLE4 & v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m4 & V & jv & -> & MI4 & ST4 & HPR4 & SO4 & VR & AH4 & VB4 & RV4 & RSV4).
    rewrite ?unsigned_lit in ST4, HPR4 by lia. retlit.
    (* [comment removed for export] *)
    destruct SS3 as (G1 & IL & G2 & ARR & SGL & G3). destruct SZ3 as (S1 & S2 & S3 & S4 & S5 & S6 & S7). clear WSH.
    fold (shc (SP + -216) m3) in T0. fold (shc (SP + -208) m3) in T1. fold (shc (SP + -200) m3) in T2. fold (shc (SP + -192) m3) in T3. fold (shc (SP + -184) m3) in T4.
    eapply (shc_pres CI) in T0; [| exact HPR4| lia]. eapply (shc_pres CI) in T1; [| exact HPR4| lia].
    eapply (shc_pres CI) in T2; [| exact HPR4| lia]. eapply (shc_pres CI) in T3; [| exact HPR4| lia]. eapply (shc_pres CI) in T4; [| exact HPR4| lia].
    eapply (shz_pres CI) in S1; [| exact HPR4| apply IMG_CI; unfold client_ranges; pick_in| cbn; lia| lia].
    eapply (shz_pres CI) in S2; [| exact HPR4| apply IMG_CI; unfold client_ranges; pick_in| cbn; lia| lia].
    eapply (shz_pres CI) in S3; [| exact HPR4| apply IMG_CI; unfold client_ranges; pick_in| cbn; lia| lia].
    eapply (shz_pres CI) in S4; [| exact HPR4| apply IMG_CI; unfold client_ranges; pick_in| cbn; lia| lia].
    eapply (shz_pres CI) in S5; [| exact HPR4| apply IMG_CI; unfold client_ranges; pick_in| cbn; lia| lia].
    eapply (shz_pres CI) in S6; [| exact HPR4| apply IMG_CI; unfold client_ranges; pick_in| cbn; lia| lia].
    eapply (shz_pres CI) in S7; [| exact HPR4| apply IMG_CI; unfold client_ranges; pick_in| cbn; lia| lia].
    unfold guard1, w0, AVEC, AFALLBACK, AFALLBACK_VT, AVTAB_SRS, ASRS_FN, EBFR, SBFR, RSIFR in *.
    ag_of_hpr HPR4.
    repeat match goal with
    | Hc : rw_cells _ m3 ?A ?cs |- _ =>
        apply (rw_cells_magree bsegs _ m3 m4 A cs HPR4) in Hc;
        [| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; intros ? ?;
           first [ left; lia | right; left; eexists; split; [apply IMG_CI; unfold client_ranges; pick_in| cbn; lia] ] ]
    end.
    assert (AG4 : magree bsegs PA m m4).
    { eapply magree_trans; [exact AG3|]. eapply magree_mono; [exact HPR4|]. intros a [Ha _]. eapply aclient_addr_mono_sp'; [exact Ha| lia]. }
    assert (PNEW : forall a, PA a -> ~ (V <= a < V + 8)) by (intros a [Ha _]; eapply cl_outside_new; [exact AH4| exact Ha| lia]).
    clear HPR4 ST3 MI3 AH3 AG3.
    (* [comment removed for export] *)
    pose proof VR as (VH & _ & VTOP & V16).
    pose proof (ablk_lin _ _ VH) as (VH1 & VH2 & VH3 & VH4). unfold AIMG_HI in VH1.
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH4 ltac:(left; reflexivity)) as (_ & _ & _ & _ & VSH & _).
    assert (SV : shc V m4).
    { unfold shc. change 2147450880 with ASHOFF. eapply (fun U A B => proj1 (unpoisoned8_c1 m4 V U A B));
        [apply (ablock_unpoisoned _ _ _ VSH); first [lia| clear - V16; Z.div_mod_to_equations; lia]| clear - V16; Z.div_mod_to_equations; lia| unfold KEND; lia]. }
    clear VSH.
    pose proof (rng_fp_le _ _ _ _ FLE4 RSTK) as RSTK4. pose proof (rng_fp_le _ _ _ _ FLE4 RI) as RI4. pose proof (rng_fp_le _ _ _ _ FLE4 RISH) as RISH4.
    assert (RSV : rng RNG4 (Z.shiftr V 3 + 2147450880) 1) by (eapply rng_sub'; [exact RSV4| unfold shad, shlen, ASHOFF; change (Z.shiftr (8 + 7) 3) with 1; lia]).
    assert (RSS : rng RNG4 (Z.shiftr (SP + -216) 3 + 2147450880) 5)
      by (eapply rng_fp_le; [exact FLE4|]; eapply rng_sub'; [exact RSS0| unfold shad, ASHOFF; replace (SP - 216) with (SP + -216) by lia; lia]).
    change (Z.to_nat 8) with 8%nat in VB4.
    (* [comment removed for export] *)
    eapply evtF_cut.
    { pose proof (AI_rtcells AI _ _ _ _ _ AH4) as (_ & GOT4 & _ & _ & SHB4 & _).
      eapply rsi_c1 with (lo := lo) (sp := sp) (V := V) (jv := jv) (j := j3) (js := js3);
        first [exact ST4| exact MI4| exact GOT4| exact SHB4| exact RI4| exact RISH4| exact VH| exact V16| exact RV4| exact RSV| exact RSS| exact FRA3| exact FRE3| exact VB4| exact VEC3| exact ARR
              | (split; [exact S1| split; [exact S2| split; [exact S3| split; [exact S4| split; [exact S5| split; [exact S6| exact S7]]]]]])
              | (split; [exact SV| split; [exact T0| split; [exact T1| split; [exact T2| split; [exact T3| exact T4]]]]])
              | fold SP; lia| (eapply rng_sub'; [exact RSTK4| fold SP; lia])]. }
    cbv beta. fold SP. intros ms5 (m5 & z5 & z6 & z7 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & j5 & -> & MU5 & WM5 & MI5 & ST5 & FRS5 & FRE5 & VB5 & VEC5 & ARR5 & SZ5 & SC5).
    assert (AH5 : AHEAP AI L RNG4 (aps_m s4') (HB p V 8 :: LBc) m5).
    { eapply (AI_frame AI); [exact AH4| exact MU5| exact WM5|]. constructor; [left; left; cbn; lia| constructor; [| constructor]].
      right; left. exists (HB p V 8). split; [left; reflexivity| cbn; lia]. }
    clear FRA3 FRE3 VB4 VEC3 ARR S1 S2 S3 S4 S5 S6 S7 SV T0 T1 T2 T3 T4. band_ind VH bVH.
    assert (AG5 : magree bsegs PA m m5).
    { eapply magree_trans; [exact AG4|]. eapply magree_mono; [eapply magree_of_munch; [exact MU5| exact WM5]|]. intros a Ha. pose proof (PSTK a Ha). pose proof (PNEW a Ha). cbn [outside]. lia. }
    clear AG4. xall MU5 WM5. clear MU5 WM5 AH4 MI4 ST4.
    (* [comment removed for export] *)
    eapply evtF_cut.
    { pose proof (AI_rtcells AI _ _ _ _ _ AH5) as (_ & _ & RIC5 & REAL5 & _ & _ & INI5 & _).
      eapply (asan_memcpy0_spec RNG4) with (lo := lo);
        rewrite ?unsigned_lit by lia;
        first [exact MI5| exact ST5| exact RIC5| exact INI5| exact REAL5| exact RI4| reflexivity
              | (eapply rng_sub'; [exact RSTK4| lia]) | (clear - V16; Z.div_mod_to_equations; lia) | unfold AMEMCPY_STACK, KHIGH in *; lia ]. }
    cbv beta. intros ms6 PO. destruct PO as (d0 & d1 & d2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & d3 & d4 & d5 & d6 & m6 & -> & MU6 & WM6 & MI6 & ST6 & _ & _).
    rewrite !unsigned_lit in MU6 by lia. rewrite !unsigned_lit in ST6 by lia. retlit.
    assert (AH6 : AHEAP AI L RNG4 (aps_m s4') (HB p V 8 :: LBc) m6).
    { eapply (AI_frame AI); [exact AH5| exact MU6| exact WM6|]. constructor; [left; left; cbn; lia| constructor; [| constructor]].
      right; left. exists (HB p V 8). split; [left; reflexivity| cbn; lia]. }
    destruct SZ5 as (S1 & S2 & S3 & S4 & S5 & S6 & S7). destruct SC5 as (SV & T0 & T1 & T2 & T3 & T4).
    unfold shz, shc, SWFR, EBFR2, AVEC, AFALLBACK, w0 in *. unfold shc6, shs5, shc in *. fold SP in T0, T1, T2, T3, T4.
    change (shad 0x6ad8c0) with 2148326168 in *. change (shad 0x6ad8e0) with 2148326172 in *. change (shad 0x16c340) with 2147637352 in *.
    change (shad 0x6ad908) with 2148326177 in *. change (shad 0x6ad768) with 2148326125 in *. change (shad 0x6ad770) with 2148326126 in *.
    change (shad 0x6ad760) with 2148326124 in *.
    assert (BSV : 2148344832 <= Z.shiftr V 3 + 2147450880 /\ Z.shiftr V 3 + 2147450880 + 1 <= 17594333495296) by (rewrite Z.shiftr_div_pow2 by lia; clear - VH1 VH4; Z.div_mod_to_equations; lia).
    assert (AG6 : magree bsegs PA m m6).
    { eapply magree_trans; [exact AG5|]. eapply magree_mono; [eapply magree_of_munch; [exact MU6| exact WM6]|]. intros a Ha. pose proof (PSTK a Ha). pose proof (PNEW a Ha). cbn [outside]. lia. }
    clear AG5. xall MU6 WM6. clear MU6 WM6 AH5 MI5 ST5.
    (* [comment removed for export] *)
    eapply evtF_cut.
    { pose proof (AI_rtcells AI _ _ _ _ _ AH6) as (_ & GOT6 & _ & _ & SHB6 & _).
      eapply rsi_c2 with (lo := lo) (sp := sp) (V := V);
        first [exact ST6| exact MI6| exact GOT6| exact SHB6| exact RI4| exact RISH4| exact VH| exact V16| exact RV4| exact RSV| exact RSS| exact FRS5| exact FRE5| exact VEC5
              | (split; [exact S1| split; [exact S2| split; [exact S3| split; [exact S4| split; [exact S5| split; [exact S6| exact S7]]]]]])
              | (split; [exact SV| split; [exact T0| split; [exact T1| split; [exact T2| split; [exact T3| exact T4]]]]])
              | fold SP; lia| (eapply rng_sub'; [exact RSTK4| fold SP; lia])]. }
cbv beta. fold SP. intros ms7 (m7 & q5 & q6 & q7 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & -> & MU7 & WM7 & MI7 & ST7 & FRW7 & FRE7 & VEC7 & SZ7 & SC7).
    assert (AH7 : AHEAP AI L RNG4 (aps_m s4') (HB p V 8 :: LBc) m7).
    { eapply (AI_frame AI); [exact AH6| exact MU7| exact WM7|]. constructor; [left; left; cbn; lia| constructor; [| constructor]].
      left; right; left. exists (0x6ad740, 0x6ad780). split; [in_cr| unfold AVEC; cbn; lia]. }
    clear FRS5 FRE5 VEC5 S1 S2 S3 S4 S5 S6 S7 SV T0 T1 T2 T3 T4. unfold AVEC in MU7.
    assert (AG7 : magree bsegs PA m m7).
    { eapply magree_trans; [exact AG6|]. eapply magree_mono; [eapply magree_of_munch; [exact MU7| exact WM7]|]. intros a Ha. pose proof (PSTK a Ha). pose proof (PIMG a Ha) as PI. cbn [outside] in PI |- *. lia. }
    clear AG6. xall MU7 WM7. clear MU7 WM7 AH6 MI6 ST6.
    (* [comment removed for export] *)
    eapply evtF_cut.
    { pose proof (poison_cells_of_aheap AI _ _ _ _ _ AH7) as PC7. pose proof (annot_cells_of_aheap AI _ _ _ _ _ AH7 (hrt_cells_of_aheap AI _ _ _ _ _ AH7)) as AC7.
      eapply (annot_nop_spec RNG4) with (lo := lo) (A := V);
        rewrite ?unsigned_lit by lia;
        first [exact MI7| exact ST7| exact PC7| exact AC7| exact RI4| (eapply rng_sub'; [exact RSTK4| lia]) | unfold ANNOT_NOP_STACK, KHIGH in *; lia ]. }
    cbv beta. intros ms8 PO. destruct PO as (f0 & f1 & f2 & g0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & f3 & f4 & f5 & f6 & m8 & -> & MU8 & WM8 & MI8 & ST8).
    rewrite !unsigned_lit in MU8 by lia. rewrite !unsigned_lit in ST8 by lia. retlit. unfold ANNOT_NOP_STACK in MU8.
    assert (AH8 : AHEAP AI L RNG4 (aps_m s4') (HB p V 8 :: LBc) m8).
    { eapply (AI_frame AI); [exact AH7| exact MU8| exact WM8|]. constructor; [left; left; cbn; lia| constructor]. }
    destruct SZ7 as (S1 & S2 & S3 & S4 & S5 & S6 & S7). destruct SC7 as (SV & T0 & T1 & T2 & T3 & T4).
    unfold shz, shc, EBFR2, AVEC, AFALLBACK, w0, ANNOT_NOP_STACK in *. unfold shc6, shs5, shc in *. fold SP in T0, T1, T2, T3, T4.
    change (shad 0x6ad8c0) with 2148326168 in *. change (shad 0x6ad8e0) with 2148326172 in *. change (shad 0x16c340) with 2147637352 in *.
    change (shad 0x6ad908) with 2148326177 in *. change (shad 0x6ad768) with 2148326125 in *. change (shad 0x6ad770) with 2148326126 in *.
    change (shad 0x6ad760) with 2148326124 in *.
    assert (AG8 : magree bsegs PA m m8).
    { eapply magree_trans; [exact AG7|]. eapply magree_mono; [eapply magree_of_munch; [exact MU8| exact WM8]|]. intros a Ha. pose proof (PSTK a Ha). cbn [outside]. lia. }
    clear AG7. xall MU8 WM8. clear MU8 WM8 AH7 MI7 ST7.
    (* [comment removed for export] *)
    eapply evtF_cut.
    { pose proof (AI_rtcells AI _ _ _ _ _ AH8) as (_ & GOT8 & _ & _ & SHB8 & _).
      eapply rsi_c3 with (lo := lo) (sp := sp) (V := V) (ra := ra) (s0 := s0) (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) (s5 := s5)
                         (s6 := s6) (s7 := s7) (s8 := s8) (s9 := s9) (s10 := s10) (s11 := s11);
        first [exact ST8| exact MI8| exact GOT8| exact SHB8| exact RI4| exact RISH4| exact VH| exact V16| exact RV4| exact RSV| exact RSS| exact FRW7| exact FRE7| exact FRR3| exact VEC7
              | (split; [exact S1| split; [exact S2| split; [exact S3| split; [exact S4| split; [exact S5| split; [exact S6| exact S7]]]]]])
              | (split; [exact SV| split; [exact T0| split; [exact T1| split; [exact T2| split; [exact T3| exact T4]]]]])
              | fold SP; lia| (eapply rng_sub'; [exact RSTK4| fold SP; lia])]. }
    cbv beta. fold SP. intros ms9 (m9 & r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & -> & MU9 & WM9 & MI9 & ST9 & VEC9 & _ & _).
    assert (AH9 : AHEAP AI L RNG4 (aps_m s4') (HB p V 8 :: LBc) m9).
    { eapply (AI_frame AI); [exact AH8| exact MU9| exact WM9|]. constructor; [left; left; cbn; lia| constructor; [| constructor]].
      left; right; left. exists (0x6ad740, 0x6ad780). split; [in_cr| unfold AVEC; cbn; lia]. }
    unfold AVEC in MU9.
    assert (AG9 : magree bsegs PA m m9).
    { eapply magree_trans; [exact AG8|]. eapply magree_mono; [eapply magree_of_munch; [exact MU9| exact WM9]|]. intros a Ha. pose proof (PSTK a Ha). pose proof (PIMG a Ha) as PI. cbn [outside] in PI |- *. lia. }
    clear FRW7 FRE7 FRR3 VEC7 S1 S2 S3 S4 S5 S6 S7 SV T0 T1 T2 T3 T4 AG8. xall MU9 WM9.
    apply evtF_done. unfold rsi_post. split; [exact FLE4|]. do 15 eexists. exists m9, V. split; [reflexivity|]. split; [exact MI9|]. split; [exact ST9|].
    split; [exact AG9|]. split; [exact SO4|]. split; [exact VR|]. split; [exact AH9|]. split; [exact VB5|]. split; [exact VEC9|].
    unfold simdjson_statics, guard1, w0, AFALLBACK, AFALLBACK_VT. split; [exact G1|]. split; [exact IL|]. split; [exact G2|]. split; [exact ARR5|]. split; [exact SGL| exact G3].
  Qed.
End M.
End CANSEC1.
