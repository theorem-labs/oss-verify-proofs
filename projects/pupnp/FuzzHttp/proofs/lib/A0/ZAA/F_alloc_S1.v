(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac STRW_merge Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells LJ LJU PEnv APrimSpec APrimSpec2 APrimLem AFrame APrimPop APrimPopR APrimPopLens APrimQ APrimFrame AFrameM
                        APrimDealloc ASec ASecD AQuar AQuarM AHeap AFoot F_prim_refill F_prim_cdealloc F_poison F_quar_Ep F_quar_E F_quar_A AQuarR AQuarS AQuarP ATacFix
                        AQuarT F_gct F_depot F_depot_C F_prim_L0 F_hooks F_prim_calloc2 F_sec_A F_alloc_env F_alloc_A F_alloc_B F_alloc_C AAllocInv AAllocCarve AAllocEnvF F_alloc_P.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition al_sneed (n : Z) : Z := a0_need n + al_rz n.
Definition al_schunk (a n : Z) : schunk := mkSC a (sec_msize (al_sneed n)) (al_sneed n).
Definition al_chunk_s (a n : Z) : qchunk := mkQC (QSec (al_schunk a n)) (al_rz n) (al_n n).

Lemma al_sec_facts : forall n, 0 <= n <= A0_MAXREQ -> 65536 < a0_need n ->
  64513 <= n /\ al_n n = n /\ al_rz n = 2048 /\ al_prim n = false /\ al_need n = al_sneed n /\ a0_cls n = 0
  /\ (exists k, a0_need n = 8 * k + 2048 /\ n <= 8 * k < n + 8 /\ rup8 n = 8 * k).
Proof.
  intros n NR NS.
  assert (N1 : 64513 <= n).
  { destruct (Z_lt_le_dec n 64513) as [LT|]; [exfalso| assumption].
    unfold a0_need, a0_rzlog in NS.
    assert (R8 : (Z.max n 8 + 7) / 8 * 8 <= Z.max n 8 + 7) by (clear; Z.div_mod_to_equations; lia).
    repeat match type of NS with context [?a <=? ?b] => destruct (Z.leb_spec a b) end;
      match type of NS with context [Z.shiftl 16 ?k] => let v := eval vm_compute in (Z.shiftl 16 k) in change (Z.shiftl 16 k) with v in NS end;
      lia. }
  assert (RZL : a0_rzlog n = 7).
  { unfold a0_rzlog. repeat match goal with |- context [?a <=? ?b] => destruct (Z.leb_spec a b); [lia|] end. reflexivity. }
  assert (RZ : al_rz n = 2048) by (unfold al_rz; rewrite RZL; reflexivity).
  assert (EN : al_n n = n) by (unfold al_n; destruct (Z.eqb_spec n 0); [lia| reflexivity]).
  assert (PR : al_prim n = false) by (unfold al_prim; apply Z.leb_gt; exact NS).
  split; [exact N1|]. split; [exact EN|]. split; [exact RZ|]. split; [exact PR|].
  split; [unfold al_need, al_sneed; rewrite PR; reflexivity|].
  split; [unfold a0_cls; replace (a0_need n <=? 65536) with false by (symmetry; apply Z.leb_gt; exact NS); reflexivity|].
  exists ((n + 7) / 8). unfold a0_need, rup8. rewrite RZL. change (Z.shiftl 16 7) with 2048.
  replace (Z.max n 8) with n by lia. split; [lia|]. split; [Z.div_mod_to_equations; lia| lia].
Qed.

Section CSEC.
  Context {HC : HasCeiling}.
  Variables (E : penv) (AL : alayout).
  Notation L := (al_thread AL).
  Notation PARR := (al_parr AL).
  Variables (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (q lo size : Z) (m : mem) (H : word -> bool) (S : asec) (avoid : list (Z * Z)).
  Notation MSZ := (sec_msize size).

  Definition csec_post : Z -> (word -> bool) -> machine_state -> Prop :=
    fun a H' ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz (a + 4096)) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ H' = sec_alloc_H AL S size a H
      /\ munch [(q - 736, q); (SEC, SEC + 620); (GSTATS_A, GSTATS_A + 16); (at_thr L + 2800, at_thr L + 3168); (PARR, PARR + 2^23);
                (a, a + MSZ); (swlo a, swhi a MSZ); (swlo (PARR + 8 * se_nres S), swhi (PARR + 8 * se_nres S) K_PARR_STEP)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo q /\ poison_env E m' /\ thread_env L m' /\ RSEC AL (sec_alloc S a size) m'
      /\ (exists ts, rw_cells asegs m' (at_thr L + 2800) [CB 368 ts])
      /\ a mod 4096 = 0 /\ 0x609000 <= a /\ app_mem a MSZ /\ anon_place a MSZ
      /\ Forall (fun iv => a + MSZ <= fst iv \/ snd iv <= a) avoid
      /\ rw_cells asegs m' (a + 32) [CB (Z.to_nat 4064) (repeat (Z_to_bv 8 0) (Z.to_nat 4064))]
      /\ rw_cells asegs m' (a + 4096) [CB (Z.to_nat (MSZ - 4096)) (repeat (Z_to_bv 8 0) (Z.to_nat (MSZ - 4096)))]
      /\ rw_cells asegs m' (sh a) [CB 512%nat (repeat (Z_to_bv 8 250) 512%nat)]
      /\ (exists j, rw_cells asegs m' (sh (a + 4096)) [CB (Z.to_nat (size / 8)) j])
      /\ rw_cells asegs m' (sh (a + 4096 + size)) [CB (Z.to_nat ((MSZ - 4096 - size) / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat ((MSZ - 4096 - size) / 8)))]
      /\ shvis H' m'
      /\ gmunch [(q - 736, q); (SEC, SEC + 620); (GSTATS_A, GSTATS_A + 16); (at_thr L + 2800, at_thr L + 3168); (PARR, PARR + 2^23);
                 (a, a + MSZ); (sh a, sh a + MSZ / 8)] m m'.

  #[using="Type"] Lemma calloc_sec_spec : forall (t0 t1 t2 a1 a4 a5 a6 a7 t3 t4 t5 t6 : word) (ts : list byte) (alo ahi : Z),
    mem_inv asegs m -> mclean H m -> shvis H m -> poison_env E m -> thread_env L m -> thread_layout_ok L -> alayout_ok AL ->
    RSEC AL S m -> rw_cells asegs m (at_thr L + 2800) [CB 368 ts] ->
    stk asegs m lo q -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo -> lo <= q - 736 -> q mod 16 = 0 -> q <= 2^47 ->
    65536 < size -> size mod 8 = 0 -> size <= 2^40 ->
    In (alo, ahi) avoid -> alo <= lo -> q <= ahi ->
    Forall (fun rg : Z * Z => In (fst rg, fst rg + snd rg) avoid) (al_regions AL) ->
    Forall (fun c => In (sc_beg c, sc_beg c + sc_msize c) avoid) (se_chunks S) -> se_n S < K_MAX_CHUNKS ->
    implA H (sec_alloc_tree AL S size avoid) csec_post
          (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz INSTANCE) a1 (wz size) (wz 8) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (wz cache_alloc_entry) fc None m (seg_rom asegs)).
  Proof.
    intros t0 t1 t2 a1 a4 a5 a6 a7 t3 t4 t5 t6 ts alo ahi MI MC SV PE TE TL AO RS TS ST LOH CLO LOQ Q16 QHI S0 S8 S40 AIN ALO AHI AREG ACH WMAX.
    unfold cache_alloc_entry. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (munch_refl [(q - 48, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof TL as (_ & T2 & _ & T4 & _).
    hide TS. carve_frame 48%nat ST.
    lz_go. do 7 zstep.
    zstep.
    replace (size <? 1) with false by (symmetry; apply Z.ltb_ge; clear - S0; lia). change (Z.b2z false) with 0.
    zstep.
    zstep.
    rewrite (zb_lxor_ones size) by (clear - S0 S40; lia).
    zstep. if_cases KB; zify_cond KB. 2: { exfalso. clear - KB S0 S40. lia. } clear KB.
    zstep. zstep. zstep. if_true.
    zstep. zstep. if_false.
    zstep. if_cases KB; zify_cond KB. 2: { exfalso. clear - KB S0. lia. } clear KB.
    do 5 zstep.

    assert (PE1 : poison_env E m1).
    { eapply (poison_env_frame2 E _ m m1 PE MU WM). unfold sec_clear. repeat (apply Forall_cons || apply Forall_nil). cbn [fst snd]. clear - LOQ CLO ACR. lia. }
    assert (TE1 : thread_env L m1).
    { eapply (thread_env_frame2 L _ m m1 TE MU WM). unfold thread_clear2. repeat (apply Forall_cons || apply Forall_nil). cbn [fst snd]. clear - LOQ CLO ACR T2 T4. lia. }
    pose proof (shvis_wmono _ m m1 SV WM) as SV1.
    assert (RS1 : RSEC AL S m1).
    { eapply (RSEC_frame_pzone AL S _ m m1 lo AO LOH CLO RS MU WM). repeat (apply Forall_cons || apply Forall_nil). unfold pzone. cbn [fst snd]. clear - LOQ. lia. }
    unhide TS. pose proof (rw_cells_transport asegs _ m m1 _ _ TS MU WM ltac:(cbn [disjoint_from cells_size csize Nat.add]; clear - LOQ CLO T4; lia)) as TS1.
    clear PE TE SV RS TS.
    rename MU into MU1, WM into WM1. hide MU1. hide WM1. hide FR.
    rewrite <- (ebind_ret_r (sec_alloc_tree AL S size avoid)).
    callAk (sec_allocate_spec E AL _ gp _ _ _ _ _ _ _ _ _ _ _ _ F fc (q + -48) lo size m1 H S avoid _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ts alo ahi MI) unfolding (fun h => idtac);
      [ assumption | exact SV1 | exact PE1 | exact TE1 | exact TL | exact AO | exact RS1 | exact TS1 | exact ST | exact CLO | clear - LOQ; lia
      | clear - Q16; Z.div_mod_to_equations; lia | clear - QHI; lia | reflexivity | reflexivity | reflexivity | reflexivity
      | clear - S0; lia | exact S8 | exact S40 | exact AIN | exact ALO | clear - AHI; lia | exact AREG | exact ACH | exact WMAX | ].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    rename POST into GMk.
    assert (MB : 4096 < MSZ <= size + 8192 /\ MSZ mod 8 = 0) by (unfold sec_msize, rup4k; clear - S0; Z.div_mod_to_equations; lia).
    destruct MB as (MB & MB8). remember MSZ as msz eqn:Emsz.
    pose proof PC7 as [_ PCC].
    layout_facts AO 1%nat LPARR. destruct LPARR as (P1 & P2 & _).
    assert (SHR : sh r + msz / 8 <= 0x10007fff8000) by (unfold sh, SHADOW_OFF; clear - PCC ACR MB PC5; Z.div_mod_to_equations; lia).
    unhide FR.
    pose proof (rw_cells_gtransport _ _ _ _ _ FR GMk WMk ltac:(cbn [disjoint_from cells_size csize Nat.add]; clear - LOQ CLO LOH T4 P2 PCC SHR MB; lia)) as FR2.
    clear FR.
    zstep. zstep. zstep. if_false. zstep.
    do 6 zstep. zstep. zstep.
    release_frame FR2 PC q.
    unhide MU1. unhide WM1.
    pose proof (munch_joinP _ _ _ _ _ MU1 MUk) as MUfin. cbn [app] in MUfin.
    pose proof (wmono_trans asegs _ _ _ WM1 WMk) as WMfin.
    pose proof (gmunch_join _ _ _ _ _ (gmunch_of_munch _ _ _ MU1) GMk) as GMfin. cbn [app] in GMfin.
    subst msz.
    lz_ret. apply evt_done. unfold csec_post.
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, m2.
    split; [reflexivity|]. split; [reflexivity|].
    split; [refine (munch_weaken _ _ _ _ _ MUfin); clear; sub_fp_solve|].
    split; [exact WMfin|]. split; [exact MI0|]. split; [exact PC|]. split; [exact PC0|]. split; [exact PC1|]. split; [exact PC2|]. split; [exact PC3|].
    split; [exact PC4|]. split; [exact PC5|]. split; [exact PC6|]. split; [exact PC7|]. split; [exact PC8|]. split; [exact PC9|]. split; [exact PC10|].
    split; [exact PC11|]. split; [exact PC12|]. split; [exact PC13|]. split; [exact PC14|].
    refine (gmunch_weaken _ _ _ _ _ GMfin); clear; sub_fp_solve.
  Qed.
End CSEC.

