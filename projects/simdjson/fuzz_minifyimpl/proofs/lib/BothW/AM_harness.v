(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessM ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import BImg RtCells AProto ABase ARep MonadF AMalloc_iface AAtexit_iface ABytes APoisonR_iface F_apoison F_annot AAnnot_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import Stdio_kit F_set_shadow_f5.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import AU_kit AU_iface AHarnessU_iface AU_parts_iface AU_client_kit AU_fuzz_kit AU_h_kit AU_first_A AU_first_M.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import AM_kitA AM_kitB AM_iface AM_model AM_clstable AM_annotw AM_vdtorf AM_lambda_iface AM_harnessA.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac pick_in := (left; reflexivity) + (right; pick_in).
Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Ltac retlit := lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; rpc) end.
Definition bx (P : Prop) : Prop := P.
Ltac box H := lazymatch type of H with ?P => change P with (bx P) in H end.
Ltac ub H T := pose proof H as T; unfold bx in T.
(* [comment removed for export] *)
Ltac xrw H MU WM :=
  lazymatch type of MU with munch ?W ?mo ?mn =>
    lazymatch type of H with rw_cells _ _ ?A ?cs =>
      apply (rw_cells_transport bsegs W mo mn A cs) in H; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul HZRB hlocals shcells3 shcells3g shrowB app repeat Datatypes.length]; lia] end end.
Ltac xrwc H MU WM CS :=
  lazymatch type of MU with munch ?W ?mo ?mn =>
    lazymatch type of H with rw_cells _ _ ?A ?cs =>
      apply (rw_cells_transport bsegs W mo mn A cs) in H; [| exact MU| exact WM| rewrite CS; cbn [disjoint_from Z.of_nat Pos.of_succ_nat Pos.succ]; lia] end end.
Ltac xst H MU WM :=
  lazymatch type of MU with munch ?W ?mo ?mn =>
    lazymatch type of H with stk _ _ ?loq ?hiq =>
      apply (stk_transport_disjoint bsegs W mo mn loq hiq) in H; [| exact MU| exact WM| cbn [disjoint_from]; lia] end end.
Ltac ag_of_hpr H := lazymatch type of H with aheap_pres ?CI ?LB ?SP ?m ?m' => change (aheap_pres CI LB SP m m') with (magree bsegs (aclient_addr CI LB SP) m m') in H end.
Ltac xag H AG tac :=
  lazymatch type of AG with magree _ ?P ?mo ?mn =>
    lazymatch type of H with
    | rw_cells _ _ ?A ?cs => apply (rw_cells_magree bsegs P mo mn A cs AG) in H; [| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul HZRB hlocals shcells3 shcells3g shrowB app repeat Datatypes.length]; intros ? ?; tac]
    | stk _ _ ?loq ?hiq => apply (stk_magree bsegs P mo mn loq hiq AG) in H; [| intros ? ?; tac]
    end end.

(* [comment removed for export] *)
Ltac xall MU WM :=
  lazymatch type of MU with munch ?W ?mo ?mn =>
    repeat match goal with
    | H : rw_cells _ mo ?A ?cs |- _ =>
        apply (rw_cells_transport bsegs W mo mn A cs) in H;
        [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul fst snd HZRB hlocals shcells3 shcells3g shrowB app repeat Datatypes.length]; lia]
    | H : stk _ mo ?loq ?hiq |- _ =>
        apply (stk_transport_disjoint bsegs W mo mn loq hiq) in H; [| exact MU| exact WM| cbn [disjoint_from]; lia]
    | H : wr_at _ mo ?A ?n |- _ => apply (wr_at_transport bsegs mo mn A n) in H; [| exact WM]
    end end.

Section CANSEC1. Context {rc : runConstT}.

Lemma implMA_getb : forall {B} RNG (k : APS -> Monad.M APS B) (s : APS) Q ms,
  implMA RNG (k s) s Q ms -> implMA RNG (Monad.mbind Monad.mget k) s Q ms.
Proof. intros B RNG k s Q ms H. exact H. Qed.
Lemma implMA_retb : forall {X Y} RNG (a : X) (f : X -> Monad.M APS Y) (s : APS) Q ms,
  implMA RNG (f a) s Q ms -> implMA RNG (Monad.mbind (Monad.mret a) f) s Q ms.
Proof. intros X Y RNG a f s Q ms H. exact H. Qed.

(* [comment removed for export] *)
Lemma got_word_of_relro : forall m A v,
  (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) -> ARELRO_LO <= A -> A + 8 <= ARELRO_HI -> rw_bytes_b bsegs A (le8 (Z_to_bv 64 v)) = true ->
  rw_cells bsegs m A [C8 (Z_to_bv 64 v)].
Proof.
  intros m A v R LO HI RB. unfold ARELRO_LO, ARELRO_HI in *.
  eapply rw_cells_recast; [apply (rw_cells_image0 bsegs m A (le8 (Z_to_bv 64 v)));
    [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply R; rewrite length_le8 in Ha; lia
    | exact RB | lia | rewrite length_le8; lia ] | cbn; split; exact I | reflexivity | reflexivity].
Qed.
Lemma poison_cells_of_art : forall m, artcells m -> (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) -> poison_cells m.
Proof.
  intros m AC R. pose proof AC as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & _).
  unfold poison_cells. split; [exact A2|]. split; [| split; [exact A4|]; split; [exact A5|]; split; [exact A8|]; split; [exact A9| exact A13]].
  apply got_word_of_relro; [exact R| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity].
Qed.
Lemma hrt_cells_of_art : forall m, artcells m -> hrt_cells m.
Proof.
  intros m AC. unfold artcells in AC.
  destruct AC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W & _ & _ & _ & _ & _ & _ & C1' & C2').
  unfold hrt_cells. split; [exact C1'| exact C2'].
Qed.
Lemma annot_cells_of_art : forall m, artcells m -> (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) -> annot_cells m.
Proof.
  intros m AC R. pose proof (hrt_cells_of_art m AC) as (H1 & H2). unfold annot_cells. split; [exact H1|]. split; [| exact H2].
  apply got_word_of_relro; [exact R| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity].
Qed.
(* [comment removed for export] *)
Lemma shf5_cells_of_art : forall m, artcells m -> (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) -> shf5_cells m.
Proof.
  intros m AC R. split.
  - apply got_word_of_relro; [exact R| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity].
  - pose proof AC as (A1 & A2 & A3 & A4 & _). exact A4.
Qed.

Section M.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variables (fflag : alayout -> Z -> Z -> Z) (rng_fs : alayout -> footprint -> Prop).
  Variable K : ALooseKit AI fflag rng_fs.
  Hypothesis IMG_CI : forall iv, In iv client_ranges -> In iv CI.
  Hypothesis SM3 : stack_malloc_3_stmt AI fflag rng_fs.
  Hypothesis AI_fake_flag : forall L RNG st LB m cls F N,
    AHEAP AI L RNG st LB m -> In (mkABlock (ABFake cls) F N) LB ->
    rw_cells bsegs m (fflag L cls F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L cls F) 1
    /\ ablk (fflag L cls F) (fflag L cls F + 1) /\ fflag L cls F + 1 <= ATOP
    /\ (forall b, In b LB -> fflag L cls F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L cls F)
    /\ ~ in_ranges CI (fflag L cls F).
  Hypothesis AI_fake_release : forall L RNG st LB m cls F N,
    AHEAP AI L RNG st (mkABlock (ABFake cls) F N :: LB) m ->
    AHEAP AI L RNG st LB (write_to_mem m (wa (fflag L cls F)) [Z_to_bv 8 0]).
  Hypothesis LAM : lambda_stmt AI fflag rng_fs K.
  Hypothesis RFSM : forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R'.

  (* [comment removed for export] *)
  Variables (L : alayout) (RNG : footprint).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (s : APS) (LB : list ablock) (D : Z) (payload : list Z) (lo : Z) (rstk : region).
  Hypothesis AH : AHEAP AI L RNG (aps_m s) LB m0.
  Hypothesis HLB : forall b, In b LB -> exists p A n, b = HB p A n.
  Hypothesis PAY : payload_atA LB D payload.
  Hypothesis BY : bytes_at bsegs m0 D (map (Z_to_bv 8) payload).
  Hypothesis FAB : Forall (fun c => 0 <= c < 256) payload.
  Hypothesis D16 : D mod 16 = 0.
  Hypothesis SZB : zlength payload < 2^26.
  Hypothesis HI : harness_invA m0.
  Hypothesis CLS : client_static s LB m0.
  Hypothesis ST : stk bsegs m0 lo (bv_unsigned sp).
  Hypothesis BOT : ATOP + 4096 <= lo.
  Hypothesis LOS : lo <= bv_unsigned sp - AHARNESS_STACK.
  Hypothesis SPG : bv_unsigned sp + 208 = al_sp0 L.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis RC : rclean m0 rstk.
  Hypothesis RLO : r_lo rstk <= lo.
  Hypothesis RHI : bv_unsigned sp <= r_hi rstk.
  Hypothesis RRLO : ATOP <= r_rlo rstk.
  Hypothesis S0E : s0 = Z_to_bv 64 (zlength payload).
  Hypothesis MI : mem_inv bsegs m0.
  Hypothesis FRM : frm0 fc.
  Hypothesis TP : tp = Z_to_bv 64 ATP.
  Hypothesis RAE : ra = Z_to_bv 64 ATRUN_RET.
  Hypothesis HUL : HU L.
  Hypothesis RSTK : rng RNG lo (al_top L - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.
  Hypothesis RFS : rng_fs L RNG.
  Hypothesis RR : rrng RNG rstk.
  Hypothesis ROK : aps_ok L s.

  Notation SP := (bv_unsigned sp).
  Notation SZ := (zlength payload).
  Let SPA : Z := SP - 256 - (SP - 256) mod 32.
  Notation FB3 F := (mkABlock (ABFake 3) F 512).

  Lemma geom : SP - 272 <= SPA <= SP - 256 /\ SPA mod 32 = 0 /\ SP + 48 <= al_top L /\ al_top L <= 2^47 /\ (ATOP - 160 <= al_bot L <= ATOP + 3936)
               /\ al_bot L + 0x800000 = al_top L /\ 0 <= SZ.
  Proof.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (L1 & L2 & L3 & L4 & _).
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    assert (T : SP + 48 <= al_top L).
    { unfold al_top. rewrite <- SPG. replace (SP + 208 - 160) with (SP + 48) by lia. pose proof (page_round_up_geA (SP + 48) ltac:(lia)). lia. }
    subst SPA. unfold zlength in *. repeat split; try lia; Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pag_outside : forall RNGx st LBF mx F a,
    AHEAP AI L RNGx st LBF mx -> In (FB3 F) LBF -> (forall b, In b LB -> In b LBF) -> ablk F (F + 512) ->
    aclient_addr CI LB SP a ->
    (a < lo \/ SP <= a) /\ ~ (F <= a < F + 512) /\ ~ (shad F <= a < shad F + 64).
  Proof.
    intros RNGx st LBF mx F a AHx HF INCL FH Ha. pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). unfold AIMG_HI in FH1.
    pose proof geom as (SPAB & SPA32 & TOP & TOP47 & CBOT & LBT & _). unfold AHARNESS_STACK in LOS.
    pose proof (fun b Hb => AI_block_bounds AI _ _ _ _ _ b AHx Hb) as BB. cbv beta in BB.
    pose proof (BB _ HF) as BF. cbn [ab_addr ab_size] in BF.
    unfold AIMG_HI, KHIGH in *. rewrite !shad_div. unfold ASHOFF.
    pose proof LOS as LOS'. pose proof BOT as BOT'.
    destruct Ha as [X|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - clear - X BF LOS' BOT' CBOT FH. Z.div_mod_to_equations. lia.
    - pose proof (AI_aci_img AI iv Hiv). unfold AIMG_HI in *. clear - H Hr BF LOS' BOT' CBOT FH. Z.div_mod_to_equations. lia.
    - destruct (HLB _ Hb) as (p & A & N & ->). cbn in Hr.
      pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AHx (INCL _ Hb) HF ltac:(discriminate)) as DJ. cbn [ab_addr ab_size] in DJ.
      destruct (AI_block AI _ _ _ _ _ _ _ _ AHx (INCL _ Hb)) as (_ & (R1 & R2 & R3 & R4) & _).
      pose proof (ablk_lin _ _ R1) as (R1a & R1b & R1c & R1d). unfold AIMG_HI in R1a. band_ind R1 bR1.
      clear - Hr DJ R1a R1b R1c R2 R3 R4 bR1r bR1hi bR1lo BF LOS' BOT' CBOT FH2 FH3. Z.div_mod_to_equations. lia.
    - assert (A47 : 0 <= a' < 2^47 /\ (ATOP <= a' \/ a' < 7159808)).
      { destruct Ha' as [X|[(iv & Hiv & Hr)|(c & FA' & fn & Hb' & Hr)]]; [atop_facts; lia| pose proof (AI_aci_img AI iv Hiv); pose proof (AI_aci_lo AI iv Hiv); unfold AIMG_HI in *; lia|].
        destruct (HLB _ Hb') as (p & A & N & E'). discriminate. }
      rewrite shad_div. unfold ASHOFF.
      split; [| split].
      + clear - A47 BF LOS' BOT' CBOT. atop_facts. Z.div_mod_to_equations. lia.
      + intros X. eapply (ablk_clear_band _ _ _ FH); [| exact X]. unfold KLS. clear - A47. Z.div_mod_to_equations. lia.
      + clear - A47 BF LOS' BOT' CBOT FH2 FH3. Z.div_mod_to_equations. lia.
  Qed.

  Lemma pag_client : forall LB' sp' a, aclient_addr CI LB SP a -> (forall b, In b LB -> In b LB') -> sp' <= SP -> aclient_addr CI LB' sp' a.
  Proof. intros LB' sp' a Ha INCL LE. eapply aclient_addr_mono_sp; [eapply aclient_addr_mono_lb; [exact Ha| exact INCL]| exact LE]. Qed.

  (* [comment removed for export] *)
  Lemma sh_client : forall LB' sp' F a, In (FB3 F) LB' -> F mod 8 = 0 -> 0 <= F -> shad F <= a < shad F + 64 -> aclient_addr CI LB' sp' a.
  Proof.
    intros LB' sp' F a HIN F8 F0 Ha. right; right; right. exists (F + 8 * (a - shad F)). split.
    - right; right. exists 3, F, 512. split; [exact HIN| lia].
    - rewrite !shad_div in *. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition PW (a : Z) : Prop := aclient_addr CI LB SP a /\ outside client_wr a.

  Definition hzfr (RNGc : footprint) (sc : APS) (LBc : list ablock) (F : Z) (m : amem) (l64 l72 l80 l88 l96 l104 l112 l128 l136 l144 : list byte) : Prop :=
       mem_inv bsegs m /\ stk bsegs m lo (SPA + 64) /\ stk bsegs m (SPA + 152) (SP + -104)
    /\ rw_cells bsegs m (SP + -104) (HZRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
    /\ rw_cells bsegs m (SPA + 64) (hlocals F (CB 8 l64) (CB 8 l72) (CB 8 l80) (CB 8 l88) l96 l104 l112 (CB 8 l128) (CB 8 l136) (CB 8 l144))
    /\ rw_cells bsegs m F [C8 (Z_to_bv 64 HMAGIC); C8 (Z_to_bv 64 HDESC); C8 (Z_to_bv 64 AFUZZ_ENTRY)]
    /\ rw_cells bsegs m (F + 504) [C8 (Z_to_bv 64 (fflag L 3 F))]
    /\ rw_cells bsegs m (shad F) shcells3
    /\ client_img m /\ client_sh m /\ client_static sc LBc m
    /\ magree bsegs PW m0 m
    /\ AHEAP AI L RNGc (aps_m sc) (FB3 F :: LBc) m
    /\ F mod 512 = 0 /\ ablk F (F + 512) /\ F + 512 <= ATOP /\ rng RNG F 512 /\ rng RNG (shad F) 64.

  Lemma payload_bounds : 0 <= D /\ D + SZ <= ATOP.
  Proof.
    destruct PAY as [(pD & HIN & _)|[EP ED]].
    - destruct (AI_block AI _ _ _ _ _ _ _ _ AH HIN) as (_ & (B1 & B2 & B3 & B4) & _). pose proof (ablk_lin _ _ B1) as (B1a & B1b & B1c & B1d). lia.
    - rewrite ED, EP. unfold AEMPTY, zlength. cbn. atop_facts. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma hz_head : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    evtF bsegs RNG (fun ms => exists (F : Z) (m : amem) (l64 l72 l80 l88 l96 l104 l112 l128 l136 l144 : list byte) (x5 x6 x7 y10 y11 y12 y13 y14 x15 x16 x17 x28 x29 x30 x31 : word),
        ms = MS (mkR (Z_to_bv 64 0xb1394) (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) y10 y11 y12 y13 y14 x15 x16 x17
                     (Z_to_bv 64 (shad F)) (Z_to_bv 64 F) (Z_to_bv 64 SZ) (Z_to_bv 64 D) (Z_to_bv 64 F) (Z_to_bv 64 ASHOFF) s8 s9 s10 s11 x28 x29 x30 x31)
                FR (Z_to_bv 64 (match aps_cl s with Some _ => HJOIN | None => HFIRST end)) fc None m (seg_rom bsegs)
        /\ hzfr RNG s LB F m l64 l72 l80 l88 l96 l104 l112 l128 l136 l144
        /\ (exists r0 r1 r2 : word, rw_cells bsegs m (F + 32) [C8 r0; C8 r1; C8 r2]))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 SZ) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 AFUZZ_ENTRY) fc None m0 (seg_rom bsegs)).
  Proof.
    intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6.
    pose proof geom as (SPAB & SPA32 & TOP & TOP47 & CBOT & LBT & SZ0).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold AHARNESS_STACK in LOS. pose proof CBOT as CBOT'. atop_facts.
    pose proof payload_bounds as DB.
    destruct HI as [IG0 USH0]. pose proof IG0 as (GSU & _ & _).
    pose proof (client_rt_of_aheap AI _ _ _ _ _ AH) as (GOT0 & RIC0 & REAL0 & SHB0 & SUA0 & INI0 & LAY0).
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (h_pro ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc D SZ lo SPA);
        first [exact ST| exact MI| exact GOT0| exact SHB0| exact GSU| exact SUA0| reflexivity| exact RI| exact SP16| eapply rng_sub'; [exact RSTK| lia]| unfold AHARNESS_STACK in *; lia]. }
    cbv beta. intros ms1 (m1 & ya1 & ya2 & -> & MU1 & WM1 & MI1 & HRB1 & ST1).
    assert (NOF3 : forall F' n', ~ In (mkABlock (ABFake 3) F' n') LB) by (intros F' n' Hin; destruct (HLB _ Hin) as (p' & A' & n'' & E'); discriminate).
    assert (AH1 : AHEAP AI L RNG (aps_m s) LB m1).
    { eapply (AI_frame AI); [exact AH| exact MU1| exact WM1|]. constructor; [left; left; cbn; lia| constructor]. }
    assert (FW1 : Forall wfar [(SP - 256, SP)]) by (constructor; [apply wfar_high; cbn; lia| constructor]).
    pose proof (client_img_munch32 _ _ _ IG0 MU1 WM1 FW1) as IG1. pose proof (client_sh_munch32 _ _ _ USH0 MU1 FW1) as USH1.
    assert (CLS1 : client_static s LB m1).
    { eapply client_static_munch32; [exact CLS| exact MU1| exact WM1| exact FW1|]. intros p' V' _ HIN'.
      destruct (AI_block AI _ _ _ _ _ _ _ _ AH HIN') as (_ & (Q1 & Q2 & Q3 & Q4) & _). cbn [disjoint_from]. lia. }
    clear FW1. box MU1. box WM1.
    (* [comment removed for export] *)
    destruct (stk_split bsegs _ lo SPA (SP + -104) ST1 ltac:(lia)) as [STL1 STU1]. clear ST1.
    eapply evtF_cut.
    { eapply SM3; first [exact AH1| exact NOF3| exact MI1| exact BOT| exact TP| exact RSTK| exact RI| exact RFS| rewrite unsigned_lit by lia; first [exact STL1| unfold SM3_STACK; lia]]. }
    cbv beta. intros ms2 PO. destruct PO as (F & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & j0 & j1 & j2 & junk & -> & MI2 & ST2 & HPR2 & AH2 & F512 & FH & FC & FFC & SHW & RF & RSF).
    rewrite ?unsigned_lit in ST2, HPR2 by lia. retlit.
    assert (INCL2 : forall b, In b LB -> In b (FB3 F :: LB)) by (intros b Hb; right; exact Hb).
    assert (AG2 : magree bsegs (aclient_addr CI LB SP) m0 m2).
    { ub MU1 T1. ub WM1 T2. eapply magree_trans.
      - eapply magree_mono; [eapply magree_of_munch; [exact T1| exact T2]|]. intros a Ha. cbn.
        destruct (pag_outside _ _ _ _ F a AH2 ltac:(left; reflexivity) INCL2 FH Ha) as (O1 & _). lia.
      - ag_of_hpr HPR2. eapply magree_mono; [exact HPR2|]. intros a Ha. eapply pag_client; [exact Ha| intros b Hb; exact Hb| lia]. }
    clear MU1 WM1.
    assert (CLS2 : client_static s LB m2) by (eapply (client_static_pres AI IMG_CI); [exact HPR2| exact CLS1]).
    assert (USH2 : client_sh m2) by (eapply (client_sh_pres AI IMG_CI); [exact HPR2| exact USH1]).
    assert (IG2 : client_img m2) by (eapply (client_img_pres AI IMG_CI); [exact IG1| exact HPR2| exact AH2| exact MI2]).
    ag_of_hpr HPR2. xag HRB1 HPR2 ltac:(left; lia). xag STU1 HPR2 ltac:(left; lia). clear STL1 MI1 AH1 CLS1 USH1 IG1 HPR2.
    pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). unfold AIMG_HI in FH1. band_ind FH bFH.
    assert (BSF : 2148344840 <= shad F /\ shad F + 64 <= 17594333495296) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    pose proof (stk_merge bsegs m2 lo SPA (SP + -104) ST2 STU1 ltac:(lia)) as ST2'. clear ST2 STU1.
    (* [comment removed for export] *)
    assert (FSP : rw_cells bsegs m2 F [C8 j0; C8 j1; C8 j2] /\ rw_cells bsegs m2 (F + 504) [C8 (Z_to_bv 64 (fflag L 3 F))]
                  /\ (exists r0 r1 r2 : word, rw_cells bsegs m2 (F + 32) [C8 r0; C8 r1; C8 r2])).
    { change [C8 j0; C8 j1; C8 j2; CB 480 junk; C8 (Z_to_bv 64 (fflag L 3 F))] with ([C8 j0; C8 j1; C8 j2] ++ [CB 480 junk] ++ [C8 (Z_to_bv 64 (fflag L 3 F))]) in FFC.
      apply (proj1 (rw_cells_app _ _ _ _ _)) in FFC. destruct FFC as [X1 X2]. apply (proj1 (rw_cells_app _ _ _ _ _)) in X2. destruct X2 as [XJ X3].
      cbn [cells_size csize Nat.add] in XJ, X3. split; [exact X1|]. split; [replace (F + 504) with (F + Z.of_nat 24 + Z.of_nat 480) by lia; exact X3|].
      apply (rw_cells_split_CB bsegs _ _ [] 480 junk [] [8;8;8;8;448]%nat) in XJ; [| reflexivity]. cbn [mk_CB_cells app] in XJ.
      lazymatch type of XJ with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?r) => change (c0 :: c1 :: c2 :: c3 :: r) with ([c0] ++ [c1] ++ [c2] ++ [c3] ++ r) in XJ end.
      apply (proj1 (rw_cells_app _ _ _ _ _)) in XJ. destruct XJ as [_ XJ]. apply (proj1 (rw_cells_app _ _ _ _ _)) in XJ. destruct XJ as [Y1 XJ].
      apply (proj1 (rw_cells_app _ _ _ _ _)) in XJ. destruct XJ as [Y2 XJ]. apply (proj1 (rw_cells_app _ _ _ _ _)) in XJ. destruct XJ as [Y3 _].
      cbn [cells_size csize Nat.add] in Y1, Y2, Y3.
      destruct (c8_of_CB _ _ _ Y1) as [r0 [Z1 _]]. destruct (c8_of_CB _ _ _ Y2) as [r1 [Z2 _]]. destruct (c8_of_CB _ _ _ Y3) as [r2 [Z3 _]].
      exists r0, r1, r2.
      apply (proj2 (rw_cells_app bsegs m2 (F + 32) [C8 r0] [C8 r1; C8 r2])). split; [replace (F + 32) with (F + Z.of_nat 24 + Z.of_nat 8) by lia; exact Z1|].
      apply (proj2 (rw_cells_app bsegs m2 _ [C8 r1] [C8 r2])). cbn [cells_size csize Nat.add].
      split; [replace (F + 32 + Z.of_nat 8) with (F + Z.of_nat 24 + Z.of_nat 8 + Z.of_nat 8) by lia; exact Z2|].
      replace (F + 32 + Z.of_nat 8 + Z.of_nat 8) with (F + Z.of_nat 24 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) by lia. exact Z3. }
    destruct FSP as (HDR2 & FLP2 & (r0 & r1 & r2 & RJ2)). clear FFC.
    (* [comment removed for export] *)
    assert (GRD2 : exists g gi, rw_cells bsegs m2 AVEC_GUARD [C1 g; C1 gi] /\ (g = Z_to_bv 8 0 \/ g = Z_to_bv 8 1)
                   /\ (if bv_eqb g (Z_to_bv 8 0) then HFIRST else HJOIN) = match aps_cl s with Some _ => HJOIN | None => HFIRST end).
    { pose proof CLS2 as (_ & _ & CLS2'). destruct (aps_cl s) as [p|].
      - destruct CLS2' as (V2 & HINV2 & _ & _ & G2 & _). exists (Z_to_bv 8 1), (Z_to_bv 8 1). split; [exact G2|]. split; [right; reflexivity| reflexivity].
      - destruct CLS2' as (_ & G2 & _). exists (Z_to_bv 8 0), (Z_to_bv 8 0). split; [exact G2|]. split; [left; reflexivity| reflexivity]. }
    destruct GRD2 as (g & gi & GRD2 & GV & GPC).
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply h_hdr with (lo := lo) (SPA := SPA) (g := g) (gi := gi);
        first [exact ST2'| exact MI2| exact HDR2| exact SHW| exact GRD2| exact GV| exact FH| exact F512| exact RF| exact RSF
              | reflexivity| exact RI| exact SP16| eapply rng_sub'; [exact RSTK| lia]| unfold AHARNESS_STACK in *; lia]. }
    cbv beta. intros ms3 (m3 & l64 & l72 & l80 & l88 & l96 & l104 & l112 & l128 & l136 & l144 & y10 & y11 & y12 & y13 & y14 & -> & MU3 & WM3 & MI3 & STL3 & STG3 & LOCS3 & HDR3 & SH3).
    rewrite GPC.
    assert (INF : In (FB3 F) (FB3 F :: LB)) by (left; reflexivity).
    assert (FW3 : Forall wfar [(SPA + 64, SPA + 152); (F, F + 24); (shad F, shad F + 44)]) by fw_far.
    pose proof (client_img_munch32 _ _ _ IG2 MU3 WM3 FW3) as IG3. pose proof (client_sh_munch32 _ _ _ USH2 MU3 FW3) as USH3.
    assert (CLS3 : client_static s LB m3).
    { eapply client_static_munch32; [exact CLS2| exact MU3| exact WM3| exact FW3|]. intros p' V' _ HIN'.
      destruct (AI_block AI _ _ _ _ _ _ _ _ AH2 ltac:(right; exact HIN')) as (_ & (Q1 & Q2 & Q3 & Q4) & _).
      pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH2 ltac:(right; exact HIN') INF ltac:(discriminate)) as D0. cbn in D0.
      pose proof (ablk_lin _ _ Q1) as (Q1a & Q1b & Q1c & Q1d). unfold AIMG_HI in Q1a. band_ind Q1 bQ1. cbn [disjoint_from]. lia. }
    clear IG2 USH2 CLS2 FW3.
    xrw HRB1 MU3 WM3. xrw FLP2 MU3 WM3. xrw RJ2 MU3 WM3.
    assert (AH3 : AHEAP AI L RNG (aps_m s) (FB3 F :: LB) m3).
    { eapply (AI_frame AI); [exact AH2| exact MU3| exact WM3|].
      constructor; [| constructor; [| constructor; [| constructor]]]; cbn [fst snd].
      - left; left. lia.
      - right; left. exists (FB3 F). split; [left; reflexivity| cbn; lia].
      - right; right. right; right. exists 3, F, 512. split; [left; reflexivity|].
        rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia. }
    assert (AG3 : magree bsegs (aclient_addr CI LB SP) m0 m3).
    { eapply magree_trans; [exact AG2|]. eapply magree_mono; [eapply magree_of_munch; [exact MU3| exact WM3]|]. intros a Ha. cbn.
      destruct (pag_outside _ _ _ _ F a AH2 ltac:(left; reflexivity) INCL2 FH Ha) as (O1 & O2 & O3). lia. }
    clear AH2 AG2 MU3 WM3 MI2.
    apply evtF_done. exists F, m3, l64, l72, l80, l88, l96, l104, l112, l128, l136, l144. do 15 eexists. split; [reflexivity|]. split; [| exists r0, r1, r2; exact RJ2].
    unfold hzfr. split; [exact MI3|]. split; [exact STL3|]. split; [exact STG3|]. split; [exact HRB1|]. split; [exact LOCS3|].
    split; [exact HDR3|]. split; [exact FLP2|]. split; [exact SH3|].
    split; [exact IG3|]. split; [exact USH3|]. split; [exact CLS3|]. split; [eapply magree_mono; [exact AG3| intros a [Ha _]; exact Ha]|]. split; [exact AH3|].
    split; [exact F512|]. split; [exact FH|]. split; [lia|]. split; [exact RF| exact RSF].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma presx_pres : forall RNGx st LBc mx F m m',
    AHEAP AI L RNGx st (FB3 F :: LBc) mx -> (forall b, In b LB -> In b LBc) -> (forall b, In b LBc -> exists q A n, b = HB q A n) -> ablk F (F + 512) ->
    aheap_pres_x CI (FB3 F :: LBc) SPA (F + 32) 24 m m' -> aheap_pres CI LBc SP m m'.
  Proof.
    intros RNGx st LBc mx F m m' AHx INCL HLBc FH HPX a Ha Hc.
    pose proof geom as (SPAB & SPA32 & TOP & TOP47 & CBOT & LBT & _). unfold AHARNESS_STACK in LOS. pose proof BOT as BOT'. atop_facts.
    pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). unfold AIMG_HI in FH1. band_ind FH bFH.
    pose proof (fun b Hb => AI_block_bounds AI _ _ _ _ _ b AHx Hb) as BB. cbv beta in BB. unfold AIMG_HI in BB.
    apply HPX; [exact Ha| |].
    - eapply aclient_addr_mono_sp; [eapply aclient_addr_mono_lb; [exact Hc| intros b Hb; right; exact Hb]| lia].
    - destruct Hc as [X|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
      + lia.
      + pose proof (AI_aci_img AI iv Hiv). unfold AIMG_HI in *. lia.
      + destruct (HLBc _ Hb) as (q & A & N & ->). cbn in Hr.
        pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AHx ltac:(right; exact Hb) ltac:(left; reflexivity) ltac:(discriminate)) as DJ. cbn [ab_addr ab_size] in DJ. lia.
      + assert (A47 : 0 <= a' < 2^47).
        { destruct Ha' as [X|[(iv & Hiv & Hr)|(c & FA' & fn & Hb' & Hr)]]; [lia| pose proof (AI_aci_img AI iv Hiv); pose proof (AI_aci_lo AI iv Hiv); unfold AIMG_HI in *; lia|].
          destruct (HLBc _ Hb') as (q & A & N & E'). discriminate. }
        intros X. apply (ablk_clear_band F (F + 512) (shad a') FH); [rewrite shad_div; unfold KLS, ASHOFF; clear - A47; Z.div_mod_to_equations; lia| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma magree_of_presx : forall LBx SPx X n m m', aheap_pres_x CI LBx SPx X n m m' -> magree bsegs (fun a => aclient_addr CI LBx SPx a /\ ~ (X <= a < X + n)) m m'.
  Proof. intros LBx SPx X n m m' H a Ha [Hc Hx]. exact (H a Ha Hc Hx). Qed.

  (* [comment removed for export] *)
  Lemma cap_shc : forall m, magree bsegs PW m0 m ->
    rw_cells bsegs m (shad (SPA + 128)) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Proof.
    intros m AG. pose proof geom as (SPAB & SPA32 & TOP & TOP47 & CBOT & LBT & _). unfold AHARNESS_STACK in LOS. pose proof BOT as BOT'. atop_facts.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct RC as [(UN & (HL1 & HL2 & HL3) & _ & _) RLT].
    assert (B : forall i, 0 <= i < 3 -> m (wa (shad (SPA + 128) + i)) = Some (Z_to_bv 8 0)).
    { intros i Hi. rewrite shad_div.
      lazymatch goal with |- context [wa ?e] => replace e with (ASHOFF + ((SPA + 128) / 8 + i)) by lia end.   (* [comment removed for export] *)
      destruct (AG (ASHOFF + ((SPA + 128) / 8 + i)) ltac:(unfold ASHOFF; Z.div_mod_to_equations; lia)) as [E _].
      - split.
        + right; right; right. exists (8 * ((SPA + 128) / 8 + i)). split; [left; Z.div_mod_to_equations; lia|]. rewrite shad_div. f_equal. Z.div_mod_to_equations. lia.
        + unfold client_wr, ASHOFF. cbn [outside]. Z.div_mod_to_equations. lia.
      - rewrite E. apply (unpoisoned_full m0 (r_lo rstk) (r_hi rstk)); [exact UN| Z.div_mod_to_equations; lia| Z.div_mod_to_equations; lia]. }
    assert (SB : 0 <= shad (SPA + 128) /\ shad (SPA + 128) + 3 <= 2^64) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    apply (proj2 (rw_cells_app bsegs m (shad (SPA + 128)) [C1 (Z_to_bv 8 0)] [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)])). split.
    { apply c1_of_byte; [lia| lia|]. rewrite <- (Z.add_0_r (shad (SPA + 128))). apply B. lia. }
    cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app bsegs m _ [C1 (Z_to_bv 8 0)] [C1 (Z_to_bv 8 0)])). split.
    { apply c1_of_byte; [lia| lia|]. replace (shad (SPA + 128) + Z.of_nat 1) with (shad (SPA + 128) + 1) by lia. apply B. lia. }
    cbn [cells_size csize Nat.add]. apply c1_of_byte; [lia| lia|]. replace (shad (SPA + 128) + Z.of_nat 1 + Z.of_nat 1) with (shad (SPA + 128) + 2) by lia. apply B. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma uchain_h : forall m k, (0 < k)%nat ->
    rw_cells bsegs m (SP + -104) (HZRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    uchain m (al_top L) AFREE_PC SPA SP k [ATRUN_RET].
  Proof.
    intros m k Hk HRB. pose proof geom as (SPAB & SPA32 & TOP & TOP47 & CBOT & LBT & SZ0). unfold AHARNESS_STACK in LOS. pose proof BOT as BOT'. atop_facts.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold HZRB in HRB.
    change [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      with ([C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] ++ [C8 s0] ++ [C8 ra]) in HRB.
    apply (proj1 (rw_cells_app _ _ _ _ _)) in HRB. destruct HRB as [_ HRB]. apply (proj1 (rw_cells_app _ _ _ _ _)) in HRB. destruct HRB as [HS0 HRA].
    cbn [cells_size csize Nat.add] in HS0, HRA.
    replace (SP + -104 + Z.of_nat 88) with (SP - 16) in HS0 by lia. replace (SP + -104 + Z.of_nat 88 + Z.of_nat 8) with (SP - 8) in HRA by lia.
    destruct HS0 as [[_ BS0] _]. destruct HRA as [[_ BRA] _]. cbn [cells_bytes cbytes app] in BS0, BRA. rewrite app_nil_r in BS0, BRA.
    rewrite S0E in BS0. rewrite RAE in BRA.
    change [ATRUN_RET] with ((if ATRUN_RET =? AFREE_PC then [] else [ATRUN_RET]) ++ []).
    eapply (uc_step m (al_top L) AFREE_PC SPA SP k SZ ATRUN_RET []); [lia| lia| lia| exact Hk| exact BS0| exact BRA| unfold ATRUN_RET; lia| lia|].
    apply uc_stop. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma shcells3_CB : forall m A, rw_cells bsegs m A shcells3 -> exists junk, rw_cells bsegs m A [CB 64 junk].
  Proof.
    intros m A H. exists (cells_bytes shcells3). eapply rw_cells_recast; [exact H| cbn; split; [reflexivity| exact I]| cbn [cells_bytes cbytes app]; rewrite app_nil_r; reflexivity| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Definition hz_fin_post (RNGx : footprint) (sc : APS) (LBc : list ablock) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : amem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               FR (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ mem_inv bsegs m' /\ stk bsegs m' lo SP
      /\ magree bsegs PW m0 m'
      /\ AHEAP AI L RNGx (aps_m sc) LBc m'
      /\ harness_invA m' /\ client_static sc LBc m'.

  Lemma hz_fin : forall (RNGx : footprint) (sc : APS) (LBc : list ablock) (F : Z) (m : amem) (h1 h2 : word) (csA : list cell)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x24 x27 y28 y29 y30 y31 : word),
    fp_le RNG RNGx ->
    (forall b, In b LB -> In b LBc) -> (forall b, In b LBc -> exists q A n, b = HB q A n) ->
    mem_inv bsegs m -> stk bsegs m lo (SPA + 64) -> stk bsegs m (SPA + 152) (SP + -104) ->
    rw_cells bsegs m (SP + -104) (HZRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells bsegs m (SPA + 64) csA -> cells_size csA = 88%nat ->
    rw_cells bsegs m F [C8 (Z_to_bv 64 HMAGIC); C8 h1; C8 h2] ->
    rw_cells bsegs m (F + 504) [C8 (Z_to_bv 64 (fflag L 3 F))] ->
    rw_cells bsegs m (shad F) (shcells3g B00) ->
    client_img m -> client_sh m -> client_static sc LBc m -> magree bsegs PW m0 m ->
    AHEAP AI L RNGx (aps_m sc) (FB3 F :: LBc) m ->
    F mod 512 = 0 -> ablk F (F + 512) -> F + 512 <= ATOP -> rng RNG F 512 -> rng RNG (shad F) 64 ->
    evtF bsegs RNGx (hz_fin_post RNGx sc LBc)
      (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (shad F)) (Z_to_bv 64 F) x20 x21 (Z_to_bv 64 F) (Z_to_bv 64 ASHOFF) x24 s9 s10 x27 y28 y29 y30 y31)
          FR (Z_to_bv 64 AVDTORF_RET) fc None m (seg_rom bsegs)).
  Proof.
    intros until y31. intros FLE INCL HLBc MI5 ST5 STG5 HRB LOCS CSA HDR FLP SH IG5 USH5 CLS5 AG5 AH5 F512 FH FC RF00 RSF00.
    pose proof geom as (SPAB & SPA32 & TOP & TOP47 & CBOT & LBT & SZ0).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold AHARNESS_STACK in LOS. pose proof CBOT as CBOT'. atop_facts.
    pose proof payload_bounds as DB.
    pose proof (rng_fp_le _ _ _ _ FLE RF00) as RF0. pose proof (rng_fp_le _ _ _ _ FLE RSF00) as RSF.
    pose proof (rng_fp_le _ _ _ _ FLE RSTK) as RSTKc. pose proof (rng_fp_le _ _ _ _ FLE RI) as RIc. pose proof (rng_fp_le _ _ _ _ FLE RISH) as RISHc.
    pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). unfold AIMG_HI in FH1. band_ind FH bFH.
    assert (BSF : 2148344840 <= shad F /\ shad F + 64 <= 17594333495296) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    assert (INF : In (FB3 F) (FB3 F :: LBc)) by (left; reflexivity).
    assert (INCL2 : forall b, In b LB -> In b (FB3 F :: LBc)) by (intros b Hb; right; apply INCL; exact Hb).
    (* [comment removed for export] *)
    assert (DV : forall W, (W = [(shad F + 4, shad F + 7); (F, F + 8)] \/ W = [(shad F, shad F + 64)] \/ (exists G, W = [(G, G + 1)] /\ ablk G (G + 1) /\ forall b, In b (FB3 F :: LBc) -> G + 1 <= ab_addr b \/ ab_addr b + ab_size b <= G)) ->
                 forall p' V', aps_cl sc = Some p' -> In (HB p' V' 8) LBc -> disjoint_from W V' 8).
    { intros W HW p' V' _ HIN'.
      destruct (AI_block AI _ _ _ _ _ _ _ _ AH5 ltac:(right; exact HIN')) as (_ & (Q1 & Q2 & Q3 & Q4) & _).
      pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH5 ltac:(right; exact HIN') INF ltac:(discriminate)) as D0. cbn in D0.
      pose proof (ablk_lin _ _ Q1) as (Q1a & Q1b & Q1c & Q1d). unfold AIMG_HI in Q1a. band_ind Q1 bQ1.
      destruct HW as [-> |[-> | (G & -> & GH' & GBL')]]; cbn [disjoint_from]; [lia| lia|].
      pose proof (GBL' _ ltac:(right; exact HIN')) as D1. cbn [ab_addr ab_size] in D1. lia. }
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply h_ret1 with (lo := lo) (SPA := SPA);
        first [exact MI5| exact SH| exact HDR| exact FH| exact F512| exact RF0| exact RSF
              | reflexivity| exact RIc| exact RISHc| exact SP16| exact DB| eapply rng_sub'; [exact RSTKc| lia]| unfold AHARNESS_STACK in *; lia]. }
    cbv beta. intros ms9 (m9 & -> & MU9 & WM9 & MI9 & SH9 & HDR9).
    assert (AH9 : AHEAP AI L RNGx (aps_m sc) (FB3 F :: LBc) m9).
    { eapply (AI_frame AI); [exact AH5| exact MU9| exact WM9|]. constructor; [| constructor; [| constructor]]; cbn [fst snd].
      - right; right. right; right. exists 3, F, 512. split; [left; reflexivity|]. rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia.
      - right; left. exists (FB3 F). split; [left; reflexivity| cbn; lia]. }
    assert (AG9 : magree bsegs PW m0 m9).
    { eapply magree_trans; [exact AG5|]. eapply magree_mono; [eapply magree_of_munch; [exact MU9| exact WM9]|]. intros a [Ha _]. cbn.
      destruct (pag_outside _ _ _ _ F a AH5 INF INCL2 FH Ha) as (O1 & O2 & O3). lia. }
    assert (FW9 : Forall wfar [(shad F + 4, shad F + 7); (F, F + 8)]) by fw_far.
    pose proof (client_img_munch32 _ _ _ IG5 MU9 WM9 FW9) as IG9. pose proof (client_sh_munch32 _ _ _ USH5 MU9 FW9) as USH9.
    assert (CLS9 : client_static sc LBc m9) by (eapply client_static_munch32; [exact CLS5| exact MU9| exact WM9| exact FW9| apply DV; left; reflexivity]).
    xrw HRB MU9 WM9. xrw FLP MU9 WM9. xrwc LOCS MU9 WM9 CSA. xst ST5 MU9 WM9. xst STG5 MU9 WM9.
    clear AH5 AG5 IG5 USH5 CLS5 MU9 WM9 MI5 SH HDR FW9.
    (* [comment removed for export] *)
    destruct (shcells3_CB _ _ SH9) as [shj DST].
    pose proof (AI_rtcells AI _ _ _ _ _ AH9) as ART9. pose proof (AI_relro AI _ _ _ _ _ AH9) as RR9.
    eapply evtF_cut.
    { eapply set_shadow_f5_spec; rewrite ?unsigned_lit by lia; [exact (shf5_cells_of_art m9 ART9 RR9)| exact DST| exact MI9| exact RIc| exact RSF]. }
    cbv beta. intros ms10 PO. destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m10 & -> & MU10 & WM10 & MI10 & DST10).
    rewrite ?unsigned_lit in MU10, DST10 by lia. unfold ASETF5_RET. retlit.
    assert (AH10 : AHEAP AI L RNGx (aps_m sc) (FB3 F :: LBc) m10).
    { eapply (AI_frame AI); [exact AH9| exact MU10| exact WM10|]. constructor; [| constructor]; cbn [fst snd].
      right; right. right; right. exists 3, F, 512. split; [left; reflexivity|]. rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia. }
    assert (AG10 : magree bsegs PW m0 m10).
    { eapply magree_trans; [exact AG9|]. eapply magree_mono; [eapply magree_of_munch; [exact MU10| exact WM10]|]. intros a [Ha _]. cbn.
      destruct (pag_outside _ _ _ _ F a AH9 INF INCL2 FH Ha) as (O1 & O2 & O3). lia. }
    assert (FW10 : Forall wfar [(shad F, shad F + 64)]) by fw_far.
    pose proof (client_img_munch32 _ _ _ IG9 MU10 WM10 FW10) as IG10. pose proof (client_sh_munch32 _ _ _ USH9 MU10 FW10) as USH10.
    assert (CLS10 : client_static sc LBc m10) by (eapply client_static_munch32; [exact CLS9| exact MU10| exact WM10| exact FW10| apply DV; right; left; reflexivity]).
    xrw HRB MU10 WM10. xrw FLP MU10 WM10. xrwc LOCS MU10 WM10 CSA. xrw HDR9 MU10 WM10. xst ST5 MU10 WM10. xst STG5 MU10 WM10.
    clear AH9 AG9 IG9 USH9 CLS9 MU10 WM10 MI9 SH9 DST ART9 RR9 FW10.
    (* [comment removed for export] *)
    destruct (AI_fake_flag _ _ _ _ _ _ _ _ AH10 INF) as (FLC & RG & GH & GC & GBL & GCI).
    pose proof (GBL _ INF) as GF. cbn [ab_addr ab_size] in GF.
    pose proof (ablk_lin _ _ GH) as (GH1 & GH2 & GH3 & GH4). unfold AIMG_HI in GH1. band_ind GH bGH.
    eapply evtF_cut.
    { eapply h_epi with (lo := lo) (SPA := SPA) (F := F) (FLG := fflag L 3 F);
        first [exact MI10| exact FLP| exact FLC| exact HRB| exact LOCS| exact CSA| exact ST5| exact STG5| exact FH| exact FC| exact F512| exact GH| exact GC| exact GF| exact RF0| exact RG
              | exact RIc| exact RISHc| exact SP16| exact DB| eapply rng_sub'; [exact RSTKc| lia]| unfold AHARNESS_STACK in *; lia]. }
    cbv beta. intros ms' (m' & -> & MU11 & WM11 & MI' & ST' & FLC').
    pose proof (AI_fake_release _ _ _ _ _ _ _ _ AH10) as AHr.
    rewrite <- (mem_eq_single m10 m' (fflag L 3 F) (Z_to_bv 8 0) ltac:(lia) ltac:(lia) MU11 (byte_of_c1 _ _ _ FLC' ltac:(lia))) in AHr.
    assert (AG' : magree bsegs PW m0 m').
    { eapply magree_trans; [exact AG10|]. eapply magree_mono; [eapply magree_of_munch; [exact MU11| exact WM11]|]. intros a [Ha _]. cbn.
      pose proof (fun b Hb => AI_block_bounds AI _ _ _ _ _ b AH10 Hb) as BB. cbv beta in BB. unfold AIMG_HI in BB.
      destruct Ha as [X|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
      + lia.
      + split; [| exact I]. assert (a <> fflag L 3 F) by (intros ->; apply GCI; exists iv; split; assumption). lia.
      + pose proof (GBL _ ltac:(right; apply INCL; exact Hb)). lia.
      + assert (A47 : 0 <= a' < 2^47) by (destruct Ha' as [X|[(iv & Hiv & Hr)|(c & FA' & fn & Hb' & Hr)]]; [lia| pose proof (AI_aci_img AI iv Hiv); pose proof (AI_aci_lo AI iv Hiv); unfold AIMG_HI in *; lia| destruct (HLB _ Hb') as (p' & A'' & N' & E'); discriminate]).
        rewrite shad_div. unfold ASHOFF. split; [| exact I]. intros X'. eapply (ablk_clear_band _ _ _ GH); [| exact X']. unfold KLS. clear - A47. Z.div_mod_to_equations. lia. }
    assert (FW11 : Forall wfar [(fflag L 3 F, fflag L 3 F + 1)]) by fw_far.
    apply evtF_done. unfold hz_fin_post. do 14 eexists. exists m'. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG'|].
    split; [exact AHr|].
    split. { split; [exact (client_img_munch32 _ _ _ IG10 MU11 WM11 FW11)| exact (client_sh_munch32 _ _ _ USH10 MU11 FW11)]. }
    eapply client_static_munch32; [exact CLS10| exact MU11| exact WM11| exact FW11|]. apply DV. right; right. exists (fflag L 3 F). split; [reflexivity|]. split; [exact GH| exact GBL].
  Qed.
  (* [comment removed for export] *)
  Lemma pw_not_blockshadow : forall a beg cap, PW a -> ablock_range beg cap -> 0 <= cap -> AIMG_HI <= beg -> 0 <= a < 2^64 ->
    ~ (shad beg <= a < shad beg + granules cap).
  Proof.
    intros a beg cap [Hc OW] (BH & _ & BT & B16) C0 BLO Ha. pose proof (ablk_lin _ _ BH) as (BH1 & BH2 & BH3 & BH4). unfold AIMG_HI in *.
    pose proof geom as (SPAB & SPA32 & TOP & TOP47 & CBOT & LBT & _). unfold AHARNESS_STACK in LOS. pose proof BOT as BOT'. pose proof LOS as LOS'. atop_facts.
    pose proof ATOP_al16 as A16.
    rewrite granules_div by lia. rewrite !shad_div. unfold ASHOFF.
    destruct Hc as [X|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - clear - X BH2 BH3 C0 H LOS' BOT'. Z.div_mod_to_equations. lia.
    - pose proof (AI_aci_img AI iv Hiv) as IM. unfold AIMG_HI in *. clear - IM Hr BH1 BH2 C0. Z.div_mod_to_equations. lia.
    - destruct (HLB _ Hb) as (p & A & N & ->). cbn in Hr.
      destruct (AI_block AI _ _ _ _ _ _ _ _ AH Hb) as (_ & (R1 & _) & _).
      intros X. apply (ablk_clear_band A (A + N) a R1); [| exact Hr]. unfold KLS. clear - X BH1 BH2 BH3 C0 H. Z.div_mod_to_equations. lia.
    - rewrite shad_div. unfold ASHOFF.
      destruct Ha' as [X|[(iv & Hiv & Hr)|(c & FA' & fn & Hb' & Hr)]].
      + clear - X BT B16 A16 BH2 C0. Z.div_mod_to_equations. lia.
      + pose proof (AI_aci_img AI iv Hiv) as IM. unfold AIMG_HI in *. clear - IM Hr BLO B16 BH2 C0. Z.div_mod_to_equations. lia.
      + destruct (HLB _ Hb') as (p & A & N & E'). discriminate.
  Qed.

  (* [comment removed for export] *)
  Definition hz_tail_post0 (RNGc : footprint) (sc : APS) (LBc : list ablock) : Z -> APS -> footprint -> machine_state -> Prop :=
    fun r s' RNG' ms' => fp_le RNGc RNG' /\ r = 0 /\ aps_rest s' = aps_rest sc /\ hz_fin_post RNG' s' LBc ms'.
  Definition hz_tail_post (RNGc : footprint) (sc : APS) (LBc : list ablock) : Z -> APS -> footprint -> machine_state -> Prop :=
    fun r s' RNG' ms' => hz_tail_post0 RNGc sc LBc r s' RNG' ms' /\ aps_cl s' = aps_cl sc.

  (* [comment removed for export] *)
  Ltac xpx H HPX tac := eapply (aheap_pres_x_rw_cells _ _ _ _ _ _ _ _ _ HPX) in H; [| tac| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul HZRB shcells3 shcells3g shrowB app]; lia].

  Lemma hz_tail : forall (p : AsanCtrl.aptr) (RNGc : footprint) (sc : APS) (LBc : list ablock) (F : Z) (m3 : amem) (l64 l72 l80 l88 l96 l104 l112 l128 l136 l144 : list byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    aps_cl sc = Some p -> fp_le RNG RNGc -> aps_ok L sc ->
    (forall b, In b LB -> In b LBc) -> (forall b, In b LBc -> exists q A n, b = HB q A n) ->
    hzfr RNGc sc LBc F m3 l64 l72 l80 l88 l96 l104 l112 l128 l136 l144 ->
    (exists r0 r1 r2 : word, rw_cells bsegs m3 (F + 32) [C8 r0; C8 r1; C8 r2]) ->
    implMA RNGc (minify_callA payload ;;; mret 0) sc (hz_tail_post RNGc sc LBc)
      (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (shad F)) (Z_to_bv 64 F) (Z_to_bv 64 SZ) (Z_to_bv 64 D) (Z_to_bv 64 F) (Z_to_bv 64 ASHOFF) s8 s9 s10 s11 x28 x29 x30 x31)
          FR (Z_to_bv 64 HJOIN) fc None m3 (seg_rom bsegs)).
  Proof.
    intros until x31. intros CL FLE AOK INCL HLBc HZ (r0 & r1 & r2 & RJ3).
    destruct HZ as (MI3 & STL3 & STG3 & HRB & LOCS3 & HDR & FLP & SH3 & IG3 & USH3 & CLS3 & AG3 & AH3 & F512 & FH & FC & RF & RSF).
    pose proof geom as (SPAB & SPA32 & TOP & TOP47 & CBOT & LBT & SZ0).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold AHARNESS_STACK in LOS. pose proof CBOT as CBOT'. atop_facts. pose proof ATOP_al16 as A16.
    pose proof payload_bounds as DB.
    pose proof (rng_fp_le _ _ _ _ FLE RF) as RFc. pose proof (rng_fp_le _ _ _ _ FLE RSF) as RSFc. pose proof (rng_fp_le _ _ _ _ FLE RSTK) as RSTKc.
    pose proof (rng_fp_le _ _ _ _ FLE RI) as RIc. pose proof (rng_fp_le _ _ _ _ FLE RISH) as RISHc. pose proof (RFSM _ _ _ FLE RFS) as RFSc.
    assert (RRc : rng RNGc (shad (r_rlo rstk)) (shad (r_rhi rstk) - shad (r_rlo rstk))) by (eapply rng_fp_le; [exact FLE| exact RR]).
    pose proof RC as [(_ & (HL1 & HL2 & HL3) & _ & _) RLT].
    pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). unfold AIMG_HI in FH1. band_ind FH bFH.
    assert (BSF : 2148344840 <= shad F /\ shad F + 64 <= 17594333495296) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    assert (BSC : 2148344840 <= shad (SPA + 128) /\ shad (SPA + 128) + 3 <= 17594333495296 /\ shad F + 64 <= shad (SPA + 128)) by (rewrite !shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    assert (ESH64 : shad (F + 32) = shad F + 4) by (rewrite !shad_div; Z.div_mod_to_equations; lia).
    assert (INF : In (FB3 F) (FB3 F :: LBc)) by (left; reflexivity).
    assert (INCL2 : forall b, In b LB -> In b (FB3 F :: LBc)) by (intros b Hb; right; apply INCL; exact Hb).
    assert (NOF1 : forall F1 n1, ~ In (mkABlock (ABFake 1) F1 n1) (FB3 F :: LBc)).
    { intros F1 n1 [E|Hin]; [discriminate| destruct (HLBc _ Hin) as (q & A & N & E'); discriminate]. }
    pose proof (proj2 (lk_of_AI AI fflag rng_fs K _ _ _ _ _ AH)) as LKT.
    assert (ABK : forall b, In b (FB3 F :: LBc) -> ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b mod 8 = 0).
    { intros b [<-|Hb]; [split; [exact FH| cbn; clear - F512; Z.div_mod_to_equations; lia]|]. destruct (HLBc _ Hb) as (q & A & N & ->). cbn.
      destruct (AI_block AI _ _ _ _ _ _ _ _ AH3 ltac:(right; exact Hb)) as (_ & (R1 & _ & _ & R4) & _). split; [exact R1| clear - R4; Z.div_mod_to_equations; lia]. }
    pose proof HUL as HU'. unfold HU, HU_TRACES in HU'.
    pose proof (Forall_inv HU') as HUa. pose proof (Forall_inv (Forall_inv_tail HU')) as HUb.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HU'))) as HUc. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HU')))) as HUd. clear HU'.
    (* [comment removed for export] *)
    pose proof CLS3 as (AR3 & AT3 & CLS3'). rewrite CL in CLS3'. destruct CLS3' as (V & HINV & VB3 & VEC3 & GU3 & G13 & IL3 & G23 & ARR3 & SGL3 & G33).
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH3 ltac:(right; exact HINV)) as (_ & (VR1 & VR2 & VR3 & VR4) & RV & RSV & VSH & _).
    pose proof (ablk_lin _ _ VR1) as (VR1a & VR1b & VR1c & VR1d). unfold AIMG_HI in VR1a. band_ind VR1 bVR.
    assert (UNV : unpoisoned m3 V (V + 8)) by (apply (ablock_unpoisoned _ _ _ VSH); first [lia| clear - VR4; Z.div_mod_to_equations; lia]).
    destruct (unpoisoned8_c1 m3 V UNV ltac:(clear - VR4; Z.div_mod_to_equations; lia) ltac:(unfold KEND; lia)) as [VSHC _].
    assert (RSV1 : rng RNGc (Z.shiftr V 3 + ASHOFF) 1) by (replace (Z.shiftr V 3 + ASHOFF) with (shad V) by (unfold shad; lia); rewrite shlenE in RSV; exact RSV).
    pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH3 ltac:(right; exact HINV) INF ltac:(discriminate)) as DJV. cbn [ab_addr ab_size] in DJV.
    (* [comment removed for export] *)
    eapply implMA_evtF.
    { eapply h_join with (lo := lo) (SPA := SPA) (V := V);
        first [exact MI3| exact LOCS3| exact SH3| exact VEC3| exact VB3| exact VSHC| exact VR1| exact FH| exact F512| exact RV| exact RSV1| exact RSFc
              | reflexivity| exact RIc| exact RISHc| exact SP16| exact DB| (clear - VR4; Z.div_mod_to_equations; lia)| eapply rng_sub'; [exact RSTKc| lia]| unfold AHARNESS_STACK in *; lia]. }
    cbv beta. intros ms4 (m4 & ya10 & -> & EY10 & MU4 & WM4 & MI4 & LOCS4 & SH4). clear ya10 EY10.
    assert (FW4 : Forall wfar [(shad F + 4, shad F + 7); (SPA + 64, SPA + 144)]) by fw_far.
    pose proof (client_img_munch32 _ _ _ IG3 MU4 WM4 FW4) as IG4. pose proof (client_sh_munch32 _ _ _ USH3 MU4 FW4) as USH4.
    assert (CLS4 : client_static sc LBc m4).
    { eapply client_static_munch32; [exact CLS3| exact MU4| exact WM4| exact FW4|]. intros p' V' _ HIN'.
      destruct (AI_block AI _ _ _ _ _ _ _ _ AH3 ltac:(right; exact HIN')) as (_ & (Q1 & Q2 & Q3 & Q4) & _).
      pose proof (ablk_lin _ _ Q1) as (Q1a & Q1b & Q1c & Q1d). unfold AIMG_HI in Q1a. band_ind Q1 bQ1. cbn [disjoint_from]. lia. }
    xrw HRB MU4 WM4. xrw HDR MU4 WM4. xrw FLP MU4 WM4. xrw RJ3 MU4 WM4. xst STL3 MU4 WM4. xst STG3 MU4 WM4.
    assert (AH4 : AHEAP AI L RNGc (aps_m sc) (FB3 F :: LBc) m4).
    { eapply (AI_frame AI); [exact AH3| exact MU4| exact WM4|]. constructor; [| constructor; [| constructor]]; cbn [fst snd].
      - right; right. right; right. exists 3, F, 512. split; [left; reflexivity|]. rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia.
      - left; left. lia. }
    assert (AG4 : magree bsegs PW m0 m4).
    { eapply magree_trans; [exact AG3|]. eapply magree_mono; [eapply magree_of_munch; [exact MU4| exact WM4]|]. intros a [Ha _]. cbn.
      destruct (pag_outside _ _ _ _ F a AH3 INF INCL2 FH Ha) as (O1 & O2 & O3). lia. }
    clear IG3 USH3 CLS3 FW4 MU4 WM4 MI3 LOCS3 SH3 VB3 VEC3 VSHC UNV VSH.
    (* [comment removed for export] *)
    destruct (stk_split bsegs _ lo SPA (SPA + 64) STL3 ltac:(lia)) as [STL4 STM4]. clear STL3.
    unfold hlocals in LOCS4.
    lazymatch type of LOCS4 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?r) =>
      change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: r) with ([c0; c1; c2; c3; c4; c5; c6; c7] ++ [c8; c9] ++ r) in LOCS4 end.
    apply (proj1 (rw_cells_app _ _ _ _ _)) in LOCS4. destruct LOCS4 as [LOCA LOCS4]. apply (proj1 (rw_cells_app _ _ _ _ _)) in LOCS4. destruct LOCS4 as [CAP LOCB].
    cbn [cells_size csize Nat.add] in CAP, LOCB. replace (SPA + 64 + Z.of_nat 64) with (SPA + 128) in CAP by lia. replace (SPA + 64 + Z.of_nat 64 + Z.of_nat 16) with (SPA + 144) in LOCB by lia.
    pose proof (cap_shc m4 AG4) as CSH4.
    pose proof CSH4 as CSH4'.
    change [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] with ([C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ++ [C1 (Z_to_bv 8 0)]) in CSH4'.
    apply (proj1 (rw_cells_app _ _ _ _ _)) in CSH4'. destruct CSH4' as [CAPSH _].
    pose proof CLS4 as (_ & _ & CLS4'). rewrite CL in CLS4'. destruct CLS4' as (V4 & _ & _ & _ & _ & _ & _ & _ & _ & SGL4 & _).
    pose proof SGL4 as FBV4.
    lazymatch type of FBV4 with rw_cells _ _ _ (?c0 :: ?r) => change (c0 :: r) with ([c0] ++ r) in FBV4 end.
    apply (proj1 (rw_cells_app _ _ _ _ _)) in FBV4. destruct FBV4 as [FBV4 _]. clear V4 SGL4.
    pose proof SH4 as SHR4. unfold shcells3g, shrowB in SHR4. cbn [app] in SHR4.
    lazymatch type of SHR4 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?r) =>
      change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: r) with ([c0; c1; c2; c3] ++ [c4; c5; c6] ++ r) in SHR4 end.
    apply (proj1 (rw_cells_app _ _ _ _ _)) in SHR4. destruct SHR4 as [_ SHR4]. apply (proj1 (rw_cells_app _ _ _ _ _)) in SHR4. destruct SHR4 as [SHR4 _].
    cbn [cells_size csize Nat.add] in SHR4. replace (shad F + Z.of_nat 4) with (shad (F + 32)) in SHR4 by (rewrite !shad_div; Z.div_mod_to_equations; lia).
    assert (WRH : wr_at bsegs m4 (shad F) (shad (F + 64) - shad F)).
    { pose proof (proj2 SH4) as W. unfold shcells3g, shrowB in W. cbn [app cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in W.
      eapply (wr_at_sub _ _ _ _ _ _ W); rewrite !shad_div; Z.div_mod_to_equations; lia. }
    assert (RSHH : rng RNGc (shad F) (shad (F + 64) - shad F)) by (eapply rng_sub'; [exact RSFc|]; rewrite !shad_div; Z.div_mod_to_equations; lia).
    pose proof (uchain_h m4 (Nat.pred UDEPTH) ltac:(unfold UDEPTH; cbn; lia) HRB) as UCH4.
    assert (UNP4 : unpoisoned m4 (r_lo rstk) (r_hi rstk)).
    { destruct RC as [(UN & (HLa & HLb & HLc) & _ & _) RLT'].
      eapply unpoisoned_agree; [exact UN|]. intros sx Hs.
      rewrite <- (shad_unshad sx). rewrite !shad_div in Hs. unfold ASHOFF in Hs.
      apply AG4; [rewrite shad_unshad; unfold ASHOFF, KEND in *; Z.div_mod_to_equations; lia|]. split.
      + right; right; right. exists (8 * (sx - ASHOFF)). split; [| reflexivity]. left. unfold ASHOFF, KEND in *. Z.div_mod_to_equations. lia.
      + rewrite shad_unshad. unfold client_wr. cbn [outside]. unfold ASHOFF in *. Z.div_mod_to_equations. lia. }
    assert (BY4 : bytes_at bsegs m4 D (map (Z_to_bv 8) payload)).
    { eapply bytes_at_magree; [exact AG4| exact BY|]. intros a Ha. rewrite length_map in Ha.
      destruct PAY as [(pD & HIN & PZ)|[EP ED]]; [| rewrite EP in Ha; cbn in Ha; lia].
      pose proof (AI_block_bounds AI _ _ _ _ _ _ AH HIN) as DBB. cbn [ab_addr ab_size] in DBB. unfold AIMG_HI in DBB.
      split; [right; right; left; exists (HB pD D SZ); split; [exact HIN| cbn; unfold zlength in *; lia]|]. unfold client_wr. cbn [outside]. unfold zlength in *. lia. }
    (* [comment removed for export] *)
    eapply (implMA_bind RNGc (minify_callA payload) (fun _ => mret 0) sc (fun _ s' R' ms' => evtF bsegs R' (hz_tail_post RNGc sc LBc 0 s' R') ms')).
    2:{ cbv beta. intros u sq Rq msq Hq. apply implMA_ret. exact Hq. }
    apply minify_call_of_lam.
    eapply (implMA_bind RNGc (lamA payload) odeleteA sc
              (lambda_post AI fflag rng_fs K L RNGc (Z_to_bv 64 ALAM_RET) (Z_to_bv 64 SPA) gp tp sp (Z_to_bv 64 SPA) (Z_to_bv 64 (shad F)) (Z_to_bv 64 F) (Z_to_bv 64 (F + 32))
                 (Z_to_bv 64 (V + 8)) (Z_to_bv 64 F) (Z_to_bv 64 ASHOFF) (Z_to_bv 64 V) s9 s10 s11 FR fc sc (FB3 F :: LBc) (F + 32) (SPA + 128) D payload lo m4)).
    { eapply LAM with (cls := 3) (FA := F) (FN := 512) (RLO2 := F) (RHI2 := F + 64) (tr := [ATRUN_RET]) (ULO := r_lo rstk) (UHI := r_hi rstk);
        rewrite ?unsigned_lit by lia;
        first [ exact AH4 | exact NOF1 | exact ABK | exact MI4 | exact STL4 | exact BOT | exact TP | exact BY4 | exact FAB | exact D16 | exact SZB | exact INF | exact RJ3 | exact SHR4 | exact WRH | exact RSHH
              | exact CAP | exact CAPSH | exact FBV4 | exact HUa | exact HUb | exact UCH4 | exact RSTKc | exact RIc | exact RISHc | exact RFSc | exact AOK | exact UNP4
              | (unfold hull64, KEND in *; lia)
              | (split; [exact IG4| exact USH4])
              | (eapply ablk_sub; [exact FH| lia| lia])
              | (unfold ALAMBDA_STACK; lia) | (unfold ALAM_RET, ALAM_STRDEL_RET; exact HUc) | (unfold ALAM_RET, AFREE_PC; rewrite ?unsigned_lit by lia; lia) | (cbn; lia)
              | (eapply rng_sub'; [exact RFc| lia]) | (eapply rng_sub'; [exact RSFc| rewrite !shad_div; Z.div_mod_to_equations; lia])
              | (eapply rng_sub'; [exact RSTKc| lia]) | (eapply rng_sub'; [exact RRc| rewrite !shad_div; Z.div_mod_to_equations; lia])
              | (destruct PAY as [(pD & HIN & PZ)|[EP ED]]; [left; exists pD; split; [right; apply INCL; exact HIN| exact PZ]| right; split; assumption])
              | reflexivity | lia | (Z.div_mod_to_equations; lia)
              | match goal with |- ?G => idtac "LAM-LEFT:" G end ]. all: fail "LAM side condition". }
    cbv beta. intros b' sv RNG5 ms5 PO5.
    destruct PO5 as (FLE5 & u0 & u1 & u2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & m5 & beg & k & cap & -> & MI5 & ST5 & SO5 & CL5 & HPX5 & [IG5 USH5] & CAP5 & CAPSH5 & RR5 & RSH5 & KK & BR5).
    rewrite ?unsigned_lit in ST5, HPX5 by lia. unfold ALAM_RET. retlit.
    pose proof (rng_fp_le _ _ _ _ FLE5 RFc) as RF5. pose proof (rng_fp_le _ _ _ _ FLE5 RSFc) as RSF5. pose proof (rng_fp_le _ _ _ _ FLE5 RSTKc) as RSTK5.
    pose proof (rng_fp_le _ _ _ _ FLE5 RIc) as RI5. pose proof (rng_fp_le _ _ _ _ FLE5 RISHc) as RISH5. pose proof (rng_fp_le _ _ _ _ FLE5 RRc) as RR5'.
    pose proof (fp_le_trans _ _ _ FLE FLE5) as FLE05.
    assert (AOK5 : aps_ok L sv) by (eapply aps_ok_rest; [exact SO5| exact AOK]).
    (* [comment removed for export] *)
    pose proof (presx_pres _ _ _ _ _ _ _ AH4 INCL HLBc FH HPX5) as PR5.
    assert (CLS5 : client_static sv LBc m5) by (unfold client_static, client_tbl; rewrite CL5; eapply (client_static_pres AI IMG_CI); [exact PR5| exact CLS4]).
    assert (AG5 : magree bsegs PW m0 m5).
    { eapply magree_trans; [exact AG4|]. ag_of_hpr PR5. eapply magree_mono; [exact PR5|]. intros a [Ha _]. eapply pag_client; [exact Ha| exact INCL| lia]. }
    pose proof (cap_shc m5 AG5) as CSH5.
    xpx HRB HPX5 ltac:(left; left; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul HZRB]; lia).
    xpx LOCA HPX5 ltac:(left; left; cbn; lia). xpx LOCB HPX5 ltac:(left; left; cbn; lia).
    xpx HDR HPX5 ltac:(left; right; right; exists 3, F, 512; split; [exact INF| cbn; lia]).
    xpx FLP HPX5 ltac:(left; right; right; exists 3, F, 512; split; [exact INF| cbn; lia]).
    xpx SH4 HPX5 ltac:(right; right; right; right; exists 3, F, 512; split; [exact INF|]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul shcells3g shrowB app]; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    pose proof (aheap_pres_x_stk _ _ _ _ _ _ _ _ _ HPX5 STM4 ltac:(lia) ltac:(lia) ltac:(lia)) as STM5.
    pose proof (aheap_pres_x_stk _ _ _ _ _ _ _ _ _ HPX5 STG3 ltac:(lia) ltac:(lia) ltac:(lia)) as STG5.
    clear HPX5 PR5 CLS4 AG4 IG4 USH4 CSH4 CAPSH CAP FBV4 SHR4 WRH RSHH UCH4 STM4 STG3 MI4 RJ3.
    assert (LOCS5 : rw_cells bsegs m5 (SPA + 64) (hlocals F (C8 (Z_to_bv 64 AVEC)) (CB 8 l72) (CB 8 l80) (C8 (Z_to_bv 64 ASHOFF)) l96 l104 l112 (C8 (Z_to_bv 64 D)) (C8 (Z_to_bv 64 SZ)) (CB 8 l144))).
    { unfold hlocals. apply (proj2 (rw_cells_app bsegs m5 (SPA + 64) [C8 (Z_to_bv 64 AVEC); CB 8 l72; CB 8 l80; C8 (Z_to_bv 64 ASHOFF); CB 8 l96; CB 8 l104; CB 8 l112; C8 (Z_to_bv 64 F)] _)). split; [exact LOCA|].
      cbn [cells_size csize Nat.add]. apply (proj2 (rw_cells_app bsegs m5 _ [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 SZ)] [CB 8 l144])). split.
      - replace (SPA + 64 + Z.of_nat 64) with (SPA + 128) by lia. exact CAP5.
      - cbn [cells_size csize Nat.add]. replace (SPA + 64 + Z.of_nat 64 + Z.of_nat 16) with (SPA + 144) by lia. exact LOCB. }
    clear LOCA CAP5 LOCB.
    (* [comment removed for export] *)
    destruct b' as [p'|].
    - (* [comment removed for export] *)
      destruct BR5 as (NR & BR & AHL5 & FULL5 & RB5 & RSB5).
      pose proof BR as (BH & _ & BT & B16). pose proof (ablk_lin _ _ BH) as (BH1 & BH2 & BH3 & BH4). unfold AIMG_HI in BH1. band_ind BH bBH.
      assert (GR : 0 <= granules cap /\ 8 * granules cap <= cap + 7) by (rewrite granules_div by lia; Z.div_mod_to_equations; lia).
      assert (BSB : 2148344840 <= shad beg /\ shad beg + granules cap <= shad (SPA + 128) /\ shad beg + granules cap <= 17594333495296) by (rewrite !shad_div; unfold ASHOFF; clear - BH1 BH3 GR H SPAB LOS BOT; Z.div_mod_to_equations; lia).
      assert (INB : In (HB p' beg cap) (HB p' beg cap :: FB3 F :: LBc)) by (left; reflexivity).
      pose proof (lk_blocks_disjoint AI fflag rng_fs K _ _ _ _ _ _ _ AHL5 INB ltac:(right; left; reflexivity) ltac:(discriminate)) as DJB. cbn [ab_addr ab_size] in DJB.
      assert (DJSB : shad beg + granules cap <= shad F \/ shad F + 64 <= shad beg) by (rewrite !shad_div; clear - DJB F512 B16 GR BH2 FH2; Z.div_mod_to_equations; lia).
      rewrite odeleteA_some.
      (* [comment removed for export] *)
      eapply implMA_evtF.
      { eapply h_mid with (lo := lo) (SPA := SPA) (V := V); first [exact MI5| exact LOCS5| reflexivity| exact RI5| exact RISH5| exact SP16| exact DB| lia| eapply rng_sub'; [exact RSTK5| lia]| unfold AHARNESS_STACK in *; lia]. }
      cbv beta. intros ms6 (m6 & -> & MU6 & WM6 & MI6 & LOCS6).
      assert (AHL6 : AHL AI fflag rng_fs K (lk_setb AI fflag rng_fs K L p' beg cap (Some (vpat cap k))) RNG5 (aps_m sv) (HB p' beg cap :: FB3 F :: LBc) m6).
      { eapply (lk_frame AI fflag rng_fs K); [exact AHL5| exact MU6| exact WM6|]. constructor; [| constructor]. cbn [fst snd]. left; left. lia. }
      assert (AG6 : magree bsegs PW m0 m6).
      { eapply magree_trans; [exact AG5|]. eapply magree_mono; [eapply magree_of_munch; [exact MU6| exact WM6]|]. intros a [Ha _]. cbn.
        destruct (pag_outside _ _ _ _ F a AH4 INF INCL2 FH Ha) as (O1 & O2 & O3). lia. }
      assert (FW6 : Forall wfar [(SPA + 144, SPA + 152)]) by fw_far.
      pose proof (client_img_munch32 _ _ _ IG5 MU6 WM6 FW6) as IG6. pose proof (client_sh_munch32 _ _ _ USH5 MU6 FW6) as USH6.
      assert (CLS6 : client_static sv LBc m6).
      { eapply client_static_munch32; [exact CLS5| exact MU6| exact WM6| exact FW6|]. intros p'' V' _ HIN'.
        destruct (AI_block AI _ _ _ _ _ _ _ _ AH4 ltac:(right; exact HIN')) as (_ & (Q1 & Q2 & Q3 & Q4) & _). cbn [disjoint_from]. lia. }
      xrw HRB MU6 WM6. xrw HDR MU6 WM6. xrw FLP MU6 WM6. xrw SH4 MU6 WM6. xrw RR5 MU6 WM6. xrw RSH5 MU6 WM6. xrw CSH5 MU6 WM6. xrw FULL5 MU6 WM6.
      xst ST5 MU6 WM6. xst STM5 MU6 WM6. xst STG5 MU6 WM6.
      destruct (lk_block AI fflag rng_fs K _ _ _ _ _ _ _ _ AHL6 INB) as (_ & _ & _ & _ & WRB & (ch & LIVE & CSZ & UBEG & KIND) & ARENA).
      clear AHL5 AG5 IG5 USH5 CLS5 MU6 WM6 MI5 LOCS5 FW6.
      pose proof (lk_rtcells AI fflag rng_fs K _ _ _ _ _ AHL6) as ART6. pose proof (lk_relro AI fflag rng_fs K _ _ _ _ _ AHL6) as RLR6. pose proof (lk_premap AI fflag rng_fs K _ _ _ _ _ AHL6) as PRM6.
      pose proof ART6 as (_ & GOT6 & _ & _ & SHB6 & _).
      unfold hlocals in LOCS6.
      lazymatch type of LOCS6 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?r) =>
        change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: r) with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9] ++ r) in LOCS6 end.
      apply (proj1 (rw_cells_app _ _ _ _ _)) in LOCS6. destruct LOCS6 as [LOCA6 LOCB6]. cbn [cells_size csize Nat.add] in LOCB6. replace (SPA + 64 + Z.of_nat 80) with (SPA + 144) in LOCB6 by lia.
      pose proof CSH5 as FUSH. change [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] with ([C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ++ [C1 (Z_to_bv 8 0)]) in FUSH.
      apply (proj1 (rw_cells_app _ _ _ _ _)) in FUSH. destruct FUSH as [_ FUSH]. cbn [cells_size csize Nat.add] in FUSH.
      replace (shad (SPA + 128) + Z.of_nat 2) with (Z.shiftr (SPA + 144) 3 + 2147450880) in FUSH by (rewrite shad_div, Z.shiftr_div_pow2 by lia; unfold ASHOFF; Z.div_mod_to_equations; lia).
      eapply implMA_evtF.
      { eapply (avdtorf_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SPA + 144) (F + 32) beg cap k lo (aps_m sv) p' ch);
          rewrite ?unsigned_lit by lia;
          first [ exact MI6 | exact ST5 | exact BOT | exact (poison_cells_of_art m6 ART6 RLR6) | exact (annot_cells_of_art m6 ART6 RLR6) | exact ART6 | exact PRM6 | exact RLR6 | exact GOT6 | exact SHB6
                | exact LOCB6 | exact FUSH | exact RR5 | exact RSH5 | exact BR | exact NR | exact KK | exact LIVE | exact CSZ | exact UBEG | exact KIND | exact FULL5 | exact ARENA | exact RI5 | exact RB5
                | (eapply ablk_sub; [exact FH| lia| lia]) | (unfold AVDTORF_STACK, AM_annotw.ANNOTW_STACK; lia)
                | (replace (shlen (cap + 7)) with (granules cap) by (rewrite shlenE, granules_div by lia; reflexivity); exact RSB5)
                | (eapply rng_sub'; [exact RF5| lia]) | (eapply rng_sub'; [exact RSF5| rewrite !shad_div; Z.div_mod_to_equations; lia])
                | (eapply rng_sub'; [exact RSTK5| lia]) | (eapply rng_sub'; [exact RR5'| rewrite !shad_div, ?Z.shiftr_div_pow2 by lia; unfold ASHOFF; Z.div_mod_to_equations; lia])
                | reflexivity | lia | (Z.div_mod_to_equations; lia)
                | match goal with |- ?G => idtac "VDT-LEFT:" G end ]. all: fail "avdtorf_live side condition". }
      cbv beta. intros ms7 PO7. destruct PO7 as (v0 & v1 & v2 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & m7 & -> & MU7 & WM7 & MI7 & ST7 & VEC7 & VSH7 & FULL7 & (mA & MUA & WMA & MUB & WMB)).
      rewrite ?unsigned_lit in MU7, ST7, MUA, MUB by lia.
      (* [comment removed for export] *)
      assert (AHLA : AHL AI fflag rng_fs K (lk_setb AI fflag rng_fs K L p' beg cap (Some (vpat cap k))) RNG5 (aps_m sv) (HB p' beg cap :: FB3 F :: LBc) mA).
      { eapply (lk_frame AI fflag rng_fs K); [exact AHL6| exact MUA| exact WMA|]. constructor; [| constructor; [| constructor]]; cbn [fst snd].
        - left; left. lia.
        - left; right; right. exists 3, F, 512. split; [right; left; reflexivity| lia]. }
      pose proof (lk_set_none AI fflag rng_fs K _ _ _ _ _ _ _ _ _ _ _ _ _ AHLA INB MUB WMB BOT ltac:(lia) ltac:(lia) ltac:(lia) FULL7) as AHLB.
      rewrite lk_collapse, (lk_restore AI fflag rng_fs K L p' beg cap LKT) in AHLB.
      assert (AG7 : magree bsegs PW m0 m7).
      { eapply magree_trans; [exact AG6|]. eapply magree_mono; [eapply magree_of_munch; [exact MU7| exact WM7]|]. intros a Hp. pose proof Hp as [Ha _]. cbn.
        destruct (pag_outside _ _ _ _ F a AH4 INF INCL2 FH Ha) as (O1 & O2 & O3).
        pose proof (pw_not_blockshadow a beg cap Hp BR ltac:(lia) ltac:(unfold AIMG_HI; lia)). lia. }
      assert (CLS7 : client_static sv LBc m7).
      { eapply client_static_munch32; [exact CLS6| exact MU7| exact WM7| fw_far|]. intros p'' V' _ HIN'.
        destruct (AI_block AI _ _ _ _ _ _ _ _ AH4 ltac:(right; exact HIN')) as (_ & (Q1 & Q2 & Q3 & Q4) & _).
        pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH4 ltac:(right; exact HIN') INF ltac:(discriminate)) as D0. cbn in D0.
        pose proof (lk_hb_ids AI fflag rng_fs K _ _ _ _ _ AHL6) as ND6. unfold hb_ids in ND6. cbn [flat_map ab_kind app] in ND6. apply NoDup_cons_iff in ND6. destruct ND6 as [NI6 _].
        assert (NE6 : HB p' beg cap <> HB p'' V' 8) by (intros E; injection E; intros _ _ Ep; apply NI6; rewrite Ep; exact (hb_ids_in _ _ _ _ HIN')).
        pose proof (lk_blocks_disjoint AI fflag rng_fs K _ _ _ _ _ _ _ AHL6 INB ltac:(right; right; exact HIN') NE6) as D1. cbn [ab_addr ab_size] in D1.
        pose proof (ablk_lin _ _ Q1) as (Q1a & Q1b & Q1c & Q1d). unfold AIMG_HI in Q1a. band_ind Q1 bQ1. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF.
        clear - Q1a Q1b Q1c Q1d Q4 bQ1r bQ1hi bQ1lo D0 D1 B16 GR BH1 BH2 BH3 H SPAB LOS BOT FH1 FH3. Z.div_mod_to_equations. lia. }
      assert (FW7 : Forall wfar [(lo, SPA); (F + 32 + 8, F + 32 + 16); (shad beg, shad beg + granules cap)]) by fw_far.
      pose proof (client_img_munch32 _ _ _ IG6 MU7 WM7 FW7) as IG7. pose proof (client_sh_munch32 _ _ _ USH6 MU7 FW7) as USH7.
      xrw HRB MU7 WM7. xrw HDR MU7 WM7. xrw FLP MU7 WM7. xrw SH4 MU7 WM7. xrw CSH5 MU7 WM7. xrw LOCA6 MU7 WM7. xrw LOCB6 MU7 WM7.
      xst STM5 MU7 WM7. xst STG5 MU7 WM7.
      clear AHL6 AHLA AG6 IG6 USH6 CLS6 MUA WMA MUB WMB mA MU7 WM7 MI6 ART6 RLR6 PRM6 GOT6 SHB6 FUSH RR5 RSH5 FULL5 WRB ARENA LIVE CSZ UBEG KIND FW7.
      (* [comment removed for export] *)
      pose proof (lk_hb_ids AI fflag rng_fs K _ _ _ _ _ AHLB) as ND7.
      eapply implMA_post_evtF.
      { eapply implMA_cl; [apply cl_stable_opdelete|].
        eapply (lk_opdel_sz AI fflag rng_fs K) with (L := L) (lo := lo) (A := beg) (n := cap) (p := p') (tr := [ATRUN_RET]);
          rewrite ?unsigned_lit by lia;
          first [ exact AHLB | exact INB | exact MI7 | exact ST7 | exact BOT | exact TP | exact HUd | exact RSTK5 | exact AOK5
                | exact (uchain_h m7 UDEPTH ltac:(unfold UDEPTH; lia) HRB)
                | (unfold AFREE_STACK; lia) | (unfold AVDTORF_RET, AFREE_PC; rewrite ?unsigned_lit by lia; lia) | (cbn; lia) | reflexivity | lia | (Z.div_mod_to_equations; lia)
                | match goal with |- ?G => idtac "ODL-LEFT:" G end ]. all: fail "opdelete side condition". }
      cbv beta. intros [] sw RNG8 ms8 [[SO8 PO8] CL8].
      destruct PO8 as (FLE8 & w0' & w1 & w2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & m8 & -> & MI8 & ST8 & HPR8 & AHL8).
      rewrite ?unsigned_lit in ST8, HPR8 by lia. unfold AVDTORF_RET. retlit.
      rewrite (lb_remove_headA p' beg cap (FB3 F :: LBc) ND7) in HPR8, AHL8.
      pose proof (lk_to_AI AI fflag rng_fs K _ _ _ _ _ AHL8 LKT) as AH8.
      pose proof (fp_le_trans _ _ _ FLE5 FLE8) as FLE58.
      assert (CLS8 : client_static sw LBc m8).
      { unfold client_static, client_tbl. rewrite CL8.
        eapply (client_static_pres AI IMG_CI sv LBc SP m7 m8); [eapply aheap_pres_weaken; [exact HPR8| lia| intros b Hb; right; exact Hb]| exact CLS7]. }
      assert (AG8 : magree bsegs PW m0 m8).
      { eapply magree_trans; [exact AG7|]. ag_of_hpr HPR8. eapply magree_mono; [exact HPR8|]. intros a [Ha _]. eapply pag_client; [exact Ha| exact INCL2| lia]. }
      pose proof (client_img_pres AI IMG_CI _ _ _ _ _ _ _ _ IG7 HPR8 AH8 MI8) as IG8.
      pose proof (client_sh_pres AI IMG_CI _ _ _ _ HPR8 USH7) as USH8.
      ag_of_hpr HPR8.
      xag HRB HPR8 ltac:(left; lia). xag LOCA6 HPR8 ltac:(left; lia). xag LOCB6 HPR8 ltac:(left; lia).
      xag HDR HPR8 ltac:(right; right; left; eexists; split; [exact INF| cbn; lia]). xag FLP HPR8 ltac:(right; right; left; eexists; split; [exact INF| cbn; lia]).
      xag SH4 HPR8 ltac:(eapply sh_client; [exact INF| Z.div_mod_to_equations; lia| lia| lia]).
      xag STM5 HPR8 ltac:(left; lia). xag STG5 HPR8 ltac:(left; lia).
      apply evtF_done.
      eapply evtF_mono.
      { eapply (hz_fin RNG8 sw LBc F m8) ;
          first [ exact (fp_le_trans _ _ _ FLE05 FLE8) | exact INCL | exact HLBc | exact MI8 | exact STG5 | exact HRB | exact HDR | exact FLP | exact SH4 | exact IG8 | exact USH8 | exact CLS8 | exact AG8 | exact AH8
                | exact F512 | exact FH | exact FC | exact RF | exact RSF | reflexivity
                | (eapply stk_merge; [exact ST8| exact STM5| lia])
                | (apply (proj2 (rw_cells_app bsegs m8 (SPA + 64) [C8 (Z_to_bv 64 AVEC); CB 8 l72; CB 8 l80; C8 (Z_to_bv 64 ASHOFF); CB 8 l96; CB 8 l104; CB 8 l112; C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 SZ)] [C8 (Z_to_bv 64 (F + 32))]));
                   split; [exact LOCA6| cbn [cells_size csize Nat.add]; replace (SPA + 64 + Z.of_nat 80) with (SPA + 144) by lia; exact LOCB6])
                | match goal with |- ?G => idtac "FIN-LEFT:" G end ]. all: fail "hz_fin premise". }
      cbv beta. intros ms' PO. unfold hz_tail_post, hz_tail_post0. split; [| congruence]. split; [exact FLE58|]. split; [reflexivity|]. split; [congruence| exact PO].
    - (* [comment removed for export] *)
      destruct BR5 as (Eb & Ec & AH5). subst beg cap. assert (k = 0) by lia. subst k.
      rewrite odeleteA_none. apply implMA_ret. apply evtF_done.
      eapply evtF_cut.
      { eapply h_mid with (lo := lo) (SPA := SPA) (V := V); first [exact MI5| exact LOCS5| reflexivity| exact RI5| exact RISH5| exact SP16| exact DB| lia| eapply rng_sub'; [exact RSTK5| lia]| unfold AHARNESS_STACK in *; lia]. }
      cbv beta. intros ms6 (m6 & -> & MU6 & WM6 & MI6 & LOCS6).
      assert (AH6 : AHEAP AI L RNG5 (aps_m sv) (FB3 F :: LBc) m6).
      { eapply (AI_frame AI); [exact AH5| exact MU6| exact WM6|]. constructor; [| constructor]. cbn [fst snd]. left; left. lia. }
      assert (AG6 : magree bsegs PW m0 m6).
      { eapply magree_trans; [exact AG5|]. eapply magree_mono; [eapply magree_of_munch; [exact MU6| exact WM6]|]. intros a [Ha _]. cbn.
        destruct (pag_outside _ _ _ _ F a AH4 INF INCL2 FH Ha) as (O1 & O2 & O3). lia. }
      assert (FW6 : Forall wfar [(SPA + 144, SPA + 152)]) by fw_far.
      pose proof (client_img_munch32 _ _ _ IG5 MU6 WM6 FW6) as IG6. pose proof (client_sh_munch32 _ _ _ USH5 MU6 FW6) as USH6.
      assert (CLS6 : client_static sv LBc m6).
      { eapply client_static_munch32; [exact CLS5| exact MU6| exact WM6| exact FW6|]. intros p'' V' _ HIN'.
        destruct (AI_block AI _ _ _ _ _ _ _ _ AH4 ltac:(right; exact HIN')) as (_ & (Q1 & Q2 & Q3 & Q4) & _). cbn [disjoint_from]. lia. }
      xrw HRB MU6 WM6. xrw HDR MU6 WM6. xrw FLP MU6 WM6. xrw SH4 MU6 WM6. xrw RR5 MU6 WM6. xrw RSH5 MU6 WM6. xrw CSH5 MU6 WM6.
      xst ST5 MU6 WM6. xst STM5 MU6 WM6. xst STG5 MU6 WM6.
      clear AG5 IG5 USH5 CLS5 MU6 WM6 MI5 LOCS5 FW6.
      pose proof (client_rt_of_aheap AI _ _ _ _ _ AH6) as (GOT6 & _ & _ & SHB6 & _).
      unfold hlocals in LOCS6.
      lazymatch type of LOCS6 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?r) =>
        change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: r) with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9] ++ r) in LOCS6 end.
      apply (proj1 (rw_cells_app _ _ _ _ _)) in LOCS6. destruct LOCS6 as [LOCA6 LOCB6]. cbn [cells_size csize Nat.add] in LOCB6. replace (SPA + 64 + Z.of_nat 80) with (SPA + 144) in LOCB6 by lia.
      pose proof CSH5 as FUSH. change [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] with ([C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ++ [C1 (Z_to_bv 8 0)]) in FUSH.
      apply (proj1 (rw_cells_app _ _ _ _ _)) in FUSH. destruct FUSH as [_ FUSH]. cbn [cells_size csize Nat.add] in FUSH.
      replace (shad (SPA + 128) + Z.of_nat 2) with (Z.shiftr (SPA + 144) 3 + 2147450880) in FUSH by (rewrite shad_div, Z.shiftr_div_pow2 by lia; unfold ASHOFF; Z.div_mod_to_equations; lia).
      replace (0 + 0) with 0 in RR5 by lia.
      eapply evtF_cut.
      { eapply (avdtorf_null _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SPA + 144) (F + 32) lo);
          rewrite ?unsigned_lit by lia;
          first [ exact MI6 | exact ST5 | exact BOT | exact GOT6 | exact SHB6 | exact LOCB6 | exact FUSH | exact RR5 | exact RSH5 | exact RI5
                | (eapply ablk_sub; [exact FH| lia| lia])
                | (eapply rng_sub'; [exact RF5| lia]) | (eapply rng_sub'; [exact RSF5| rewrite !shad_div; Z.div_mod_to_equations; lia])
                | (eapply rng_sub'; [exact RSTK5| lia]) | (eapply rng_sub'; [exact RR5'| rewrite !shad_div, ?Z.shiftr_div_pow2 by lia; unfold ASHOFF; Z.div_mod_to_equations; lia])
                | reflexivity | lia | (Z.div_mod_to_equations; lia)
                | match goal with |- ?G => idtac "VDN-LEFT:" G end ]. all: fail "avdtorf_null side condition". }
      cbv beta. intros ms7 PO7. destruct PO7 as (v0 & v1 & v2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & m7 & -> & MU7 & WM7 & MI7 & ST7).
      rewrite ?unsigned_lit in MU7, ST7 by lia. unfold AVDTORF_RET. retlit.
      assert (AH7 : AHEAP AI L RNG5 (aps_m sv) (FB3 F :: LBc) m7).
      { eapply (AI_frame AI); [exact AH6| exact MU7| exact WM7|]. constructor; [| constructor]. cbn [fst snd]. left; left. lia. }
      assert (AG7 : magree bsegs PW m0 m7).
      { eapply magree_trans; [exact AG6|]. eapply magree_mono; [eapply magree_of_munch; [exact MU7| exact WM7]|]. intros a [Ha _]. cbn.
        destruct (pag_outside _ _ _ _ F a AH4 INF INCL2 FH Ha) as (O1 & O2 & O3). lia. }
      assert (FW7 : Forall wfar [(SPA - 32, SPA)]) by fw_far.
      pose proof (client_img_munch32 _ _ _ IG6 MU7 WM7 FW7) as IG7. pose proof (client_sh_munch32 _ _ _ USH6 MU7 FW7) as USH7.
      assert (CLS7 : client_static sv LBc m7).
      { eapply client_static_munch32; [exact CLS6| exact MU7| exact WM7| exact FW7|]. intros p'' V' _ HIN'.
        destruct (AI_block AI _ _ _ _ _ _ _ _ AH4 ltac:(right; exact HIN')) as (_ & (Q1 & Q2 & Q3 & Q4) & _). cbn [disjoint_from]. lia. }
      xrw HRB MU7 WM7. xrw HDR MU7 WM7. xrw FLP MU7 WM7. xrw SH4 MU7 WM7. xrw LOCA6 MU7 WM7. xrw LOCB6 MU7 WM7.
      xst STM5 MU7 WM7. xst STG5 MU7 WM7.
      eapply evtF_mono.
      { eapply (hz_fin RNG5 sv LBc F m7) ;
          first [ exact FLE05 | exact INCL | exact HLBc | exact MI7 | exact STG5 | exact HRB | exact HDR | exact FLP | exact SH4 | exact IG7 | exact USH7 | exact CLS7 | exact AG7 | exact AH7
                | exact F512 | exact FH | exact FC | exact RF | exact RSF | reflexivity
                | (eapply stk_merge; [exact ST7| exact STM5| lia])
                | (apply (proj2 (rw_cells_app bsegs m7 (SPA + 64) [C8 (Z_to_bv 64 AVEC); CB 8 l72; CB 8 l80; C8 (Z_to_bv 64 ASHOFF); CB 8 l96; CB 8 l104; CB 8 l112; C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 SZ)] [C8 (Z_to_bv 64 (F + 32))]));
                   split; [exact LOCA6| cbn [cells_size csize Nat.add]; replace (SPA + 64 + Z.of_nat 80) with (SPA + 144) by lia; exact LOCB6])
                | match goal with |- ?G => idtac "FIN-LEFT:" G end ]. all: fail "hz_fin premise". }
      cbv beta. intros ms' PO. unfold hz_tail_post, hz_tail_post0. split; [| exact CL5]. split; [exact FLE5|]. split; [reflexivity|]. split; [exact SO5| exact PO].
  Qed.
  (* [comment removed for export] *)
  Lemma astk_of_agree : forall m', magree bsegs PW m0 m' -> astk_shadow_pres SP m0 m'.
  Proof.
    intros m' AG' a Ha. pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof geom as (SPAB & SPA32 & TOP & TOP47 & CBOT & LBT & SZ0). unfold AHARNESS_STACK in LOS. pose proof LOS as LOS'. pose proof BOT as BOT'. atop_facts.
    rewrite <- (shad_unshad a). apply AG'; [rewrite shad_unshad; rewrite !shad_div in Ha; unfold ASHOFF in *; Z.div_mod_to_equations; lia|].
    split.
    - right; right; right. exists (8 * (a - ASHOFF)). split; [| reflexivity]. left. pose proof ATOP_al16. rewrite !shad_div in Ha. unfold ASHOFF in *. Z.div_mod_to_equations. lia.
    - rewrite shad_unshad. rewrite !shad_div in Ha. unfold ASHOFF in Ha. unfold client_wr. cbn [outside]. Z.div_mod_to_equations. lia.
  Qed.

  Notation POST := (fuzz_oneU_post AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo m0).

  (* [comment removed for export] *)
  Theorem hz_later : forall (p : AsanCtrl.aptr) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    aps_cl s = Some p ->
    implMA RNG (fuzz_oneA AAllocAsan payload) s POST
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 SZ) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               FR (Z_to_bv 64 AFUZZ_ENTRY) fc None m0 (seg_rom bsegs)).
  Proof.
    intros p t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 CL.
    (* [comment removed for export] *)
    rewrite fuzz_oneA_unfold. unfold HarnessM.client_init. apply implMA_bind_assoc. apply implMA_getb. cbv beta. rewrite CL. apply implMA_retb.
    eapply implMA_evtF; [apply hz_head|]. cbv beta.
    intros ms (F & m3 & l64 & l72 & l80 & l88 & l96 & l104 & l112 & l128 & l136 & l144 & x5 & x6 & x7 & y10 & y11 & y12 & y13 & y14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & -> & HZ & RJ).
    rewrite CL.
    eapply implMA_mono.
    { eapply (hz_tail p RNG s LB F m3); [exact CL| apply fp_le_refl| exact ROK| intros b Hb; exact Hb| exact HLB| exact HZ| exact RJ]. }
    cbv beta. intros r s' R' ms' [(FLE' & -> & SO' & PO') CL']. destruct PO' as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MI' & ST' & AG' & AHr & HI' & CLS').
    unfold fuzz_oneU_post. split; [exact FLE'|].
    do 14 eexists. exists FR, fc, m', LB. split; [reflexivity|]. split; [reflexivity|]. split; [exact MI'|]. split; [exact FRM|]. split; [exact ST'|].
    split; [exact AG'|]. split; [apply astk_of_agree; exact AG'|]. split; [exact AHr|]. split; [exact HI'|]. split; [exact CLS'|].
    split; [exact SO'|]. rewrite CL. split; [reflexivity|]. rewrite CL'. exact CL.
  Qed.

  (* [comment removed for export] *)
  Hypothesis RSI : rsi_stmt AI.
  Hypothesis ACXA : acxa_atexit_stmt.
  (* [comment removed for export] *)
  Hypothesis AI_lsan : forall L RNG st LB m, AHEAP AI L RNG st LB m -> rw_cells bsegs m 0x6b1eb8 [C4 (Z_to_bv 64 0)].
  Hypothesis AI_frame_lsan : forall L RNG st LB m m' W, AHEAP AI L RNG st LB m -> munch W m m' -> wmono bsegs m m' ->
    Forall (fun iv => aclient_range CI LB (ATOP + 4096) (fst iv) (snd iv - fst iv) \/ iv = (0x6b1eb8, 0x6b1ebc)) W ->
    rw_cells bsegs m' 0x6b1eb8 [C4 (Z_to_bv 64 0)] -> AHEAP AI L RNG st LB m'.

  Ltac p5out := unfold RSI_W, AU_first_A.RSI_IMGW, AVEC; cbn [outside]; lia.
  Ltac p5 INF IMG_CI :=
    first [ split; [left; lia| p5out]
          | split; [right; right; left; eexists; split; [exact INF| cbn; lia]| p5out]
          | split; [eapply sh_client; [exact INF| Z.div_mod_to_equations; lia| lia| lia]| p5out]
          | split; [right; left; eexists; split; [apply IMG_CI; unfold client_ranges; pick_in| cbn; lia]| p5out] ].
  Ltac p5img IMG_CI := cbv beta; split; [right; left; eexists; split; [apply IMG_CI; unfold client_ranges; pick_in| cbn; lia]| p5out].
  Ltac img_gen IG MU WM := eapply client_img_munch_gen; [exact IG| exact MU| exact WM| | | | | | | |]; unfold AGOT_ERRC, AERRC, AMSG_SH, AJT_SH, AJT, AREAL_STRLEN; cbn [disjoint_from]; lia.

  Theorem hz_first : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    aps_cl s = None ->
    implMA RNG (fuzz_oneA AAllocAsan payload) s POST
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 SZ) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               FR (Z_to_bv 64 AFUZZ_ENTRY) fc None m0 (seg_rom bsegs)).
  Proof.
    intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 CL.
    pose proof geom as (SPAB & SPA32 & TOP & TOP47 & CBOT & LBT & SZ0).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold AHARNESS_STACK in LOS. pose proof CBOT as CBOT'. atop_facts.
    pose proof payload_bounds as DB.
    pose proof HUL as HU'. unfold HU, HU_TRACES in HU'. pose proof (Forall_inv HU') as HUa. clear HU'.
    (* [comment removed for export] *)
    rewrite fuzz_oneA_unfold. unfold HarnessM.client_init. apply implMA_bind_assoc. apply implMA_getb. cbv beta. rewrite CL.
    apply implMA_bind_assoc.
    eapply implMA_evtF; [apply hz_head|]. cbv beta.
    intros ms (F & m3 & l64 & l72 & l80 & l88 & l96 & l104 & l112 & l128 & l136 & l144 & x5 & x6 & x7 & y10 & y11 & y12 & y13 & y14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & -> & HZ & (r0 & r1 & r2 & RJ)).
    rewrite CL.
    destruct HZ as (MI3 & STL3 & STG3 & HRB & LOCS & HDR & FLP & SH3 & IG3 & USH3 & CLS3 & AG3 & AH3 & F512 & FH & FC & RF & RSF).
    destruct CLS3 as (AR3 & AT3 & CLS3'). rewrite CL in CLS3'. destruct CLS3' as (VEC & GRD & G1 & IL & G2 & ARR & SGL & G3 & WSH).
    pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). unfold AIMG_HI in FH1. band_ind FH bFH.
    assert (BSF : 2148344840 <= shad F /\ shad F + 64 <= 17594333495296) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    assert (INF : In (FB3 F) (FB3 F :: LB)) by (left; reflexivity).
    assert (INCL2 : forall b, In b LB -> In b (FB3 F :: LB)) by (intros b Hb; right; exact Hb).
    (* [comment removed for export] *)
    eapply implMA_evtF.
    { eapply h_w1 with (lo := lo); first [exact MI3| exact GRD| exact LOCS| reflexivity| exact RI| exact RISH| exact SP16| exact DB| eapply rng_sub'; [exact RSTK| lia]| unfold AHARNESS_STACK in *; lia]. }
    cbv beta. intros ms4 (m4 & z11 & z12 & -> & MU4 & WM4 & MI4 & GRD4 & LOC4).
    unfold AVEC_GUARD, AVEC, AFALLBACK, guard0, w0 in *.
    assert (AH4 : AHEAP AI L RNG (aps_m s) (FB3 F :: LB) m4).
    { eapply (AI_frame AI); [exact AH3| exact MU4| exact WM4|]. constructor; [| constructor; [| constructor]].
      - left; right; left. exists (0x6afb40, 0x6afb42). split; [apply IMG_CI; unfold client_ranges; cbn [In]; tauto| cbn; lia].
      - cbn [fst snd]. left; left. lia. }
    assert (AG4 : magree bsegs PW m0 m4).
    { eapply magree_trans; [exact AG3|].
      eapply magree_mono; [eapply magree_of_munch; [exact MU4| exact WM4]|]. intros a [Ha OW]. cbn [outside].
      destruct (pag_outside _ _ _ _ F a AH3 INF INCL2 FH Ha) as (O1 & _). unfold client_wr in OW. cbn [outside] in OW. lia. }
    assert (USH4 : client_sh m4).
    { eapply client_sh_munch_gen; [exact USH3| exact MU4|]. intros X HX. unfold client_sh_addrs in HX. cbn [In] in HX. cbn [outside].
      repeat (destruct HX as [<-|HX]; [rewrite shad_div; unfold ASHOFF; cbn; lia|]). destruct HX. }
    assert (IG4 : client_img m4) by (img_gen IG3 MU4 WM4).
    assert (AR4 : atexit_rt m4) by (eapply atexit_rt_munch_gen; [exact AR3| exact MU4| exact WM4| cbn; lia| cbn; lia]).
    assert (AT4 : ATEXIT (client_tbl s) m4) by (eapply ATEXIT_munch_gen; [exact AT3| exact MU4| exact WM4| cbn; lia]).
    clear GRD LOCS AG3 IG3 USH3 AR3 AT3. xall MU4 WM4. clear MU4 WM4 AH3 MI3.
    (* [comment removed for export] *)
    destruct (stk_split bsegs _ lo SPA (SPA + 64) STL3 ltac:(lia)) as [STL4 STM4]. clear STL3.
    assert (UST : unpoisoned m4 (SPA - 216) (SPA - 176) /\ rng RNG (shad (SPA - 216)) 5).
    { destruct RC as [(UN & (HL1 & HL2 & HL3) & _ & _) RLT]. split.
      - eapply unpoisoned_agree; [eapply unpoisoned_sub; [exact UN| lia| lia]|]. intros sx Hs.
        rewrite <- (shad_unshad sx). rewrite !shad_div in Hs. unfold ASHOFF in Hs.
        apply AG4; [rewrite shad_unshad; unfold ASHOFF; Z.div_mod_to_equations; lia|]. split.
        + right; right; right. exists (8 * (sx - ASHOFF)). split; [| reflexivity]. left. unfold ASHOFF. Z.div_mod_to_equations. lia.
        + rewrite shad_unshad. unfold client_wr. cbn [outside]. Z.div_mod_to_equations. lia.
      - eapply rng_sub'; [exact RR|]. unfold hull64 in *. rewrite !shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia. }
    destruct UST as [UST RSS].
    eapply implMA_bind.
    { eapply RSI with (lo := lo) (LBc := FB3 F :: LB);
        rewrite ?unsigned_lit by lia;
        first [exact AH4| exact MI4| exact STL4| exact BOT| exact TP| reflexivity| exact HUa| exact RSTK| exact RI| exact RISH| exact ROK| exact IG4| exact USH4
              | exact VEC| exact G1| exact IL| exact G2| exact ARR| exact SGL| exact G3| exact WSH| exact UST| exact RSS
              | unfold RSI_STACK; lia| (clear - SPA32; Z.div_mod_to_equations; lia)| lia
              | match goal with |- ?G => idtac "RSI-LEFT:" G end ]. all: fail "rsi side condition". }
    cbv beta. intros p sx RNG5 ms5 PO.
    destruct PO as (FLE5 & u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m5 & V & -> & MI5 & ST5 & AG45 & SO5 & VR & AH5 & VB5 & VEC5 & SS5).
    rewrite ?unsigned_lit in ST5, AG45 by lia. retlit.
    (* [comment removed for export] *)
    xag HRB AG45 ltac:(p5 INF IMG_CI). xag LOC4 AG45 ltac:(p5 INF IMG_CI). xag HDR AG45 ltac:(p5 INF IMG_CI). xag FLP AG45 ltac:(p5 INF IMG_CI).
    xag SH3 AG45 ltac:(p5 INF IMG_CI). xag RJ AG45 ltac:(p5 INF IMG_CI). xag GRD4 AG45 ltac:(p5 INF IMG_CI). xag STM4 AG45 ltac:(p5 INF IMG_CI). xag STG3 AG45 ltac:(p5 INF IMG_CI).
    assert (USH5 : client_sh m5).
    { eapply client_sh_magree; [exact USH4| exact AG45|]. intros X HX. unfold client_sh_addrs in HX. cbn [In] in HX. cbv beta.
      repeat (destruct HX as [<-|HX];
        [split; [right; right; right; eexists; split; [| reflexivity]; right; left; eexists; split; [apply IMG_CI; unfold client_ranges; pick_in| cbn; lia]
                | rewrite shad_div; unfold ASHOFF; cbn; p5out]|]). destruct HX. }
    assert (IG5 : client_img m5).
    { eapply (client_img_magree AI); [exact IG4| exact AG45| | exact AH5| exact MI5]. intros a Ha. unfold client_x_addr, AERRC, AMSG_SH, AJT_SH, AJT, AREAL_STRLEN in Ha.
      destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]].
      - p5img IMG_CI.
      - p5img IMG_CI.
      - split; [| p5out]. right; right; right. exists (8 * (a - ASHOFF)). split; [| rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia].
        right; left. exists (0x24480, 0x24500). split; [apply IMG_CI; unfold client_ranges; pick_in| cbn [fst snd]; unfold ASHOFF; lia].
      - split; [| p5out]. right; right; right. exists (8 * (a - ASHOFF)). split; [| rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia].
        right; left. exists (0x178460, 0x178760). split; [apply IMG_CI; unfold client_ranges; pick_in| cbn [fst snd]; unfold ASHOFF; lia].
      - p5img IMG_CI.
      - p5img IMG_CI. }
    assert (AR5 : atexit_rt m5) by (eapply atexit_rt_magree; [exact AR4| exact AG45|]; intros a [Ha|Ha]; p5img IMG_CI).
    assert (AT5 : ATEXIT (client_tbl s) m5) by (eapply ATEXIT_magree; [exact AT4| exact AG45|]; intros a Ha; p5img IMG_CI).
    assert (AG5 : magree bsegs PW m0 m5).
    { eapply magree_trans; [exact AG4|]. eapply magree_mono; [exact AG45|]. intros a [Ha OW]. split.
      - eapply pag_client; [exact Ha| exact INCL2| lia].
      - unfold client_wr in OW. cbn [outside] in OW. p5out. }
    clear AG45 AG4 USH4 AR4 AT4 IG4 UST VEC G1 IL G2 ARR SGL G3 WSH AH4 MI4 STL4.
    (* [comment removed for export] *)
    apply implMA_updb. set (sc := a_set_cl AAllocAsan (Some p) sx).
    assert (CLc : aps_cl sc = Some p) by reflexivity.
    assert (SOc : aps_rest sc = aps_rest s) by (rewrite <- SO5; reflexivity).
    assert (AH5c : AHEAP AI L RNG5 (aps_m sc) (HB p V 8 :: FB3 F :: LB) m5) by exact AH5.
    clear AH5.
    pose proof (rng_fp_le _ _ _ _ FLE5 RSTK) as RSTK5. pose proof (rng_fp_le _ _ _ _ FLE5 RI) as RI5. pose proof (rng_fp_le _ _ _ _ FLE5 RISH) as RISH5.
    (* [comment removed for export] *)
    eapply implMA_evtF; [eapply h_w2; first [exact MI5| reflexivity| exact RI5| exact RISH5| exact SP16| exact DB| eapply rng_sub'; [exact RSTK5| lia]| unfold AHARNESS_STACK in *; lia]|].
    cbv beta. intros ms6 ->.
    unfold client_tbl in AT5. rewrite CL in AT5.
    destruct (atexit_main_split _ AT5) as (xf3 & xf4 & xa3 & xa4 & fj & aj & REST & SLOT & F34 & A34). clear AT5.
    pose proof REST as (FIN & LOCK & HEAD & _).
    destruct AR5 as (REAL & (cdt & thr & sec & tm1 & LIBC)).
    eapply implMA_evtF.
    { pose proof (AI_rtcells AI _ _ _ _ _ AH5c) as (_ & _ & _ & _ & _ & _ & INI5 & _).
      eapply ACXA with (lo := lo) (cdt := cdt) (thr := thr) (sec := sec) (tm1 := tm1) (f4 := xf3) (f5 := xf4) (a04 := xa3) (a05 := xa4);
        rewrite ?unsigned_lit by lia;
        first [exact ST5| exact INI5| exact (atexit_got_of_aheap AI _ _ _ _ _ AH5c MI5)| exact (AI_lsan _ _ _ _ _ AH5c)| exact REAL| exact LIBC| exact FIN| exact LOCK| exact SLOT| exact HEAD
              | exact F34| exact A34| exact MI5| exact TP| exact RI5| (eapply rng_sub'; [exact RSTK5| lia])| unfold KHIGH; lia
              | match goal with |- ?G => idtac "ACXA-LEFT:" G end ]. all: fail "acxa side condition". }
    cbv beta. intros ms7 PO. destruct PO as (e0 & e1 & e2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & e3 & e4 & e5 & e6 & m6 & -> & MU6 & WM6 & MI6 & ST6 & CNT6 & SLOT6 & F6 & A6).
    rewrite ?unsigned_lit in MU6 by lia. rewrite ?unsigned_lit in ST6 by lia. retlit.
    assert (INF5 : In (FB3 F) (HB p V 8 :: FB3 F :: LB)) by (right; left; reflexivity).
    assert (INCL5 : forall b, In b LB -> In b (HB p V 8 :: FB3 F :: LB)) by (intros b Hb; right; right; exact Hb).
    pose proof VR as (VH & _ & VTOP & V16). pose proof (ablk_lin _ _ VH) as (VH1 & VH2 & VH3 & VH4). unfold AIMG_HI in VH1. band_ind VH bVH.
    assert (AH6 : AHEAP AI L RNG5 (aps_m sc) (HB p V 8 :: FB3 F :: LB) m6).
    { eapply AI_frame_lsan; [exact AH5c| exact MU6| exact WM6| | exact CNT6].
      constructor; [left; left; left; cbn; lia|]. constructor; [right; reflexivity|].
      repeat (constructor; [left; left; right; left; exists (0x6d1ef8, 0x6d2118); split; [apply IMG_CI; unfold client_ranges; cbn [In]; tauto| cbn; lia]|]). constructor. }
    assert (AG6 : magree bsegs PW m0 m6).
    { eapply magree_trans; [exact AG5|]. eapply magree_mono; [eapply magree_of_munch; [exact MU6| exact WM6]|]. intros a [Ha OW]. cbn [outside].
      destruct (pag_outside _ _ _ _ F a AH5c INF5 INCL5 FH Ha) as (O1 & _). unfold client_wr in OW. cbn [outside] in OW. lia. }
    assert (USH6 : client_sh m6).
    { eapply client_sh_munch_gen; [exact USH5| exact MU6|]. intros X HX. unfold client_sh_addrs in HX. cbn [In] in HX. cbn [outside].
      repeat (destruct HX as [<-|HX]; [rewrite shad_div; unfold ASHOFF; cbn; lia|]). destruct HX. }
    assert (IG6 : client_img m6) by (img_gen IG5 MU6 WM6).
    assert (REST6 : atx_rest fj aj m6) by (eapply atx_rest_transport; [exact REST| exact MU6| exact WM6| cbn; lia| cbn; lia| cbn; lia| cbn; lia| cbn; lia]).
    assert (AT6 : ATEXIT (client_tbl sc) m6).
    { unfold client_tbl. rewrite CLc. eapply atexit_run_join; [exact REST6| exact SLOT6| exact F6| exact A6]. }
    destruct SS5 as (G1 & IL & G2 & ARR & SGL & G3).
    clear SLOT F34 A34 FIN LOCK HEAD REST USH5 AG5 CNT6 SLOT6 F6 A6.
    unfold guard1, w0, AFALLBACK, AFALLBACK_VT, AVEC in *.
    xall MU6 WM6. clear MU6 WM6 AH5c MI5 ST5.
    (* [comment removed for export] *)
    eapply implMA_evtF.
    { eapply h_w3 with (lo := lo); first [exact MI6| exact GRD4| exact LOC4| reflexivity| exact RI5| exact RISH5| exact SP16| exact DB| eapply rng_sub'; [exact RSTK5| lia]| unfold AHARNESS_STACK in *; lia]. }
    cbv beta. intros ms8 (m7 & -> & MU7 & WM7 & MI7 & GRD7 & LOC7).
    unfold AVEC_GUARD in MU7.
    assert (AH7 : AHEAP AI L RNG5 (aps_m sc) (HB p V 8 :: FB3 F :: LB) m7).
    { eapply (AI_frame AI); [exact AH6| exact MU7| exact WM7|]. constructor; [| constructor].
      left; right; left. exists (0x6afb40, 0x6afb42). split; [apply IMG_CI; unfold client_ranges; cbn [In]; tauto| cbn; lia]. }
    assert (AG7 : magree bsegs PW m0 m7).
    { eapply magree_trans; [exact AG6|]. eapply magree_mono; [eapply magree_of_munch; [exact MU7| exact WM7]|]. intros a [Ha OW]. cbn [outside].
      unfold client_wr in OW. cbn [outside] in OW. lia. }
    assert (USH7 : client_sh m7).
    { eapply client_sh_munch_gen; [exact USH6| exact MU7|]. intros X HX. unfold client_sh_addrs in HX. cbn [In] in HX. cbn [outside].
      repeat (destruct HX as [<-|HX]; [rewrite shad_div; unfold ASHOFF; cbn; lia|]). destruct HX. }
    assert (IG7 : client_img m7) by (img_gen IG6 MU7 WM7).
    assert (AT7 : ATEXIT (client_tbl sc) m7) by (eapply ATEXIT_munch_gen; [exact AT6| exact MU7| exact WM7| cbn; lia]).
    assert (AR7 : atexit_rt m7) by (eapply atexit_rt_munch_gen; [split; [exact REAL| exists cdt, thr, sec, tm1; exact LIBC]| exact MU7| exact WM7| cbn; lia| cbn; lia]).
    clear GRD4 LOC4 USH6 AT6 AG6 REST6. xall MU7 WM7. clear MU7 WM7 AH6 MI6.
    (* [comment removed for export] *)
    assert (LOC7' : rw_cells bsegs m7 (SPA + 64) (hlocals F (CB 8 l64) (CB 8 (le8 (Z_to_bv 64 F))) (CB 8 (le8 (Z_to_bv 64 F))) (CB 8 l88) l96 l104 l112 (CB 8 l128) (CB 8 l136) (CB 8 l144))).
    { unfold hlocals in *. eapply rw_cells_recast; [exact LOC7| | cbn [cells_bytes cbytes app]; reflexivity| cbn [cells_size csize Nat.add]; reflexivity].
      pose proof LOC7 as [[WF _] _]. cbn in WF |- *. rewrite ?length_le8. tauto. }
    (* [comment removed for export] *)
    pose proof (stk_merge bsegs m7 lo SPA (SPA + 64) ST6 STM4 ltac:(lia)) as STL7.
    assert (AH7' : AHEAP AI L RNG5 (aps_m sc) (FB3 F :: HB p V 8 :: LB) m7) by (eapply (AI_perm AI); [apply Permutation.perm_swap| exact AH7]).
    eapply implMA_mono.
    { eapply (hz_tail p RNG5 sc (HB p V 8 :: LB) F m7); [exact CLc| exact FLE5| eapply aps_ok_rest; [exact SOc| exact ROK]| intros b Hb; right; exact Hb| | | exists r0, r1, r2; exact RJ].
      - intros b [<-|Hb]; [eexists _, _, _; reflexivity| apply HLB; exact Hb].
      - unfold hzfr. split; [exact MI7|]. split; [exact STL7|]. split; [exact STG3|]. split; [exact HRB|]. split; [exact LOC7'|].
        split; [exact HDR|]. split; [exact FLP|]. split; [exact SH3|]. split; [exact IG7|]. split; [exact USH7|].
        split. { split; [exact AR7|]. split; [exact AT7|]. rewrite CLc. exists V. split; [left; reflexivity|].
                 unfold AVEC, AVEC_GUARD, AFALLBACK, AFALLBACK_VT, guard1, w0.
                 split; [exact VB5|]. split; [exact VEC5|]. split; [exact GRD7|]. split; [exact G1|]. split; [exact IL|]. split; [exact G2|]. split; [exact ARR|]. split; [exact SGL| exact G3]. }
        split; [exact AG7|]. split; [exact AH7'|]. split; [exact F512|]. split; [exact FH|]. split; [lia|]. split; [exact RF| exact RSF]. }
    cbv beta. intros r s' R' ms' [(FLE' & -> & SO' & PO') CL']. destruct PO' as (k0 & k1 & k2 & n1 & n2 & n3 & n4 & n5 & n6 & n7 & k3 & k4 & k5 & k6 & m' & -> & MI' & ST' & AG' & AHr & HI' & CLS').
    unfold fuzz_oneU_post. split; [exact (fp_le_trans _ _ _ FLE5 FLE')|].
    do 14 eexists. exists FR, fc, m', (HB p V 8 :: LB). split; [reflexivity|]. split; [reflexivity|]. split; [exact MI'|]. split; [exact FRM|]. split; [exact ST'|].
    split; [exact AG'|]. split; [apply astk_of_agree; exact AG'|]. split; [exact AHr|]. split; [exact HI'|]. split; [exact CLS'|].
    split; [rewrite SO'; exact SOc|]. rewrite CL. exists p, V. split; [reflexivity|]. rewrite CL'. exact CLc.
  Qed.
End M.

(* [comment removed for export] *)
Section Final.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variables (fflag : alayout -> Z -> Z -> Z) (rng_fs : alayout -> footprint -> Prop).
  Variable K : ALooseKit AI fflag rng_fs.
  Hypothesis IMG_CI : forall iv, In iv client_ranges -> In iv CI.
  Hypothesis SM3 : stack_malloc_3_stmt AI fflag rng_fs.
  Hypothesis AI_fake_flag : forall L RNG st LB m cls F N,
    AHEAP AI L RNG st LB m -> In (mkABlock (ABFake cls) F N) LB ->
    rw_cells bsegs m (fflag L cls F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L cls F) 1
    /\ ablk (fflag L cls F) (fflag L cls F + 1) /\ fflag L cls F + 1 <= ATOP
    /\ (forall b, In b LB -> fflag L cls F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L cls F)
    /\ ~ in_ranges CI (fflag L cls F).
  Hypothesis AI_fake_release : forall L RNG st LB m cls F N,
    AHEAP AI L RNG st (mkABlock (ABFake cls) F N :: LB) m ->
    AHEAP AI L RNG st LB (write_to_mem m (wa (fflag L cls F)) [Z_to_bv 8 0]).
  Hypothesis LAM : lambda_stmt AI fflag rng_fs K.
  Hypothesis RFSM : forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R'.
  Hypothesis RSI : rsi_stmt AI.
  Hypothesis ACXA : acxa_atexit_stmt.
  Hypothesis AI_lsan : forall L RNG st LB m, AHEAP AI L RNG st LB m -> rw_cells bsegs m 0x6b1eb8 [C4 (Z_to_bv 64 0)].
  Hypothesis AI_frame_lsan : forall L RNG st LB m m' W, AHEAP AI L RNG st LB m -> munch W m m' -> wmono bsegs m m' ->
    Forall (fun iv => aclient_range CI LB (ATOP + 4096) (fst iv) (snd iv - fst iv) \/ iv = (0x6b1eb8, 0x6b1ebc)) W ->
    rw_cells bsegs m' 0x6b1eb8 [C4 (Z_to_bv 64 0)] -> AHEAP AI L RNG st LB m'.

  Theorem fuzz_oneU_proof : fuzz_oneU_stmt AI rng_fs.
  Proof.
    unfold fuzz_oneU_stmt. intros until rstk.
    intros AH HLB PAY BY FA D16 SZB HI CLS ST BOT LOS SPG SP16 RC RLO RHI RRLO S0E MI FRM TP -> -> RAE HUL RSTK RI RISH RFS RR ROK.
    destruct (aps_cl s) as [p|] eqn:CL.
    - eapply (hz_later AI fflag rng_fs K IMG_CI SM3 AI_fake_flag AI_fake_release LAM RFSM); eassumption.
    - eapply (hz_first AI fflag rng_fs K IMG_CI SM3 AI_fake_flag AI_fake_release LAM RFSM); eassumption.
  Qed.
End Final.
End CANSEC1.
