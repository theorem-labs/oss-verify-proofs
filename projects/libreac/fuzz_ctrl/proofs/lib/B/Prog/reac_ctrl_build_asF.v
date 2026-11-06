(* The footprint twin of reac_ctrl_build_as.v (image B; RECIPE.md steps 1-2 (a working note, not in this delivery)): the same run as an
   ExecF.evtF under a footprint RNG, by the script of reac_ctrl_build_as.v over StepF's step. Every access of this
   run closes from one rng premise of reac_ctrl_build_as_contract_F: the frame stores and loads of the 80-byte
   frame (inside the window), the two 8-byte loads of the GOT cell and of the runtime cell that hold the shadow
   offset, the 8-byte load of the switch-table word at BA_SW + 8 b and the 1-byte load of its shadow byte (both
   inside the image and the image-shadow ranges).
   The two callees are taken as hypotheses in the same place as the old theorem takes their plain contracts, here
   in footprint form: reac_box_model_upstream_width_contract_F (published by its owner in
   reac_box_model_upstream_width_c.v) and ctrl_emit_as_contract_F, the FINAL text its owner a Theorem Labs lane published
   for image B in lib/B/Prog/ctrl_emit_as_c.v (imported below), with ctrl_emit_as_contract_of_F, the machine check
   that the hypothesis asks for nothing ctrl_emit_as_contract lacks.
   reac_ctrl_build_as.v and its theorem are unchanged (the halts proofs use them). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
(* lib.Prog's reac_ctrl_build_as_c and reac_ctrl_build_as only for the models ba_go, ba_E, ba_X, ba_tbl, ba_row,
   ba_fr and their lemmas (ba_facts, ba_E_eq, ba_len_eq, ba_res, ba_go_true, ba_go_false, ba_cases, ba_fr_len), which
   B's do not define; B's, imported after them, shadow the names both define (REAC_CTRL_BUILD_AS,
   REAC_CTRL_BUILD_AS_K, BA_FR, reac_ctrl_build_as_contract, reac_ctrl_build_as_holds). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcPorts RcPortsLib RcBox RcSynth RcLay
  RcLayLib RcFin RcEmit RcEmitLib RcAsan RcAsanLib RcLeafLib reac_ctrl_build_as_c reac_ctrl_build_as.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT asan_stack_malloc_c RcAsanFP RcAsanFPLib
  ctrl_emit_as_c reac_box_model_upstream_width_c reac_ctrl_build_as_c reac_box_model_block_c reac_ctrl_build_as.
(* the image range by name (N3), for the lifted stretch's footprint premise *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import ImgBounds.
(* Last: StepF's step / if_cases (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF RngBytes StepF.
Import ListNotations.
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------------------- *)
(* The 8-aligned word cover of the shadow bytes of [p, q], the rng term the footprint premises spell out. The
   section below takes its ground covers in this named form, so that the divisions in their bounds stay out of
   the context `lia` reads; each converts to the spelled-out form where a callee takes it. *)
Definition ba_shcov (RNG : footprint) (p q : Z) : Prop :=
  rng RNG (shadow_addr p / 8 * 8) (shadow_addr q / 8 * 8 + 8 - shadow_addr p / 8 * 8).

(* Shadow-cover algebra: the only two places a division is reasoned about. Each hands the two bounds of rng_sub
   to Z.div_mod_to_equations. *)

(* A range [p, q] inside the image has the cover of its shadow inside the image-shadow range. *)
Lemma ba_shcov_img : forall RNG p q, rng RNG 0x7fffa000 0xbdc00 ->
  0x10000 <= p -> p <= q -> q < 0x10000 + 0x5ee000 ->
  rng RNG (shadow_addr p / 8 * 8) (shadow_addr q / 8 * 8 + 8 - shadow_addr p / 8 * 8).
Proof.
  intros RNG p q H Hlo Hpq Hhi. unfold shadow_addr, ASAN_K in *.
  eapply rng_sub; [exact H | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia].
Qed.

(* The byte-exact shadow span of [a, b] inside the cover of [p, q]. *)
Lemma ba_shcov_byte : forall RNG p q a b,
  rng RNG (shadow_addr p / 8 * 8) (shadow_addr q / 8 * 8 + 8 - shadow_addr p / 8 * 8) ->
  p <= a -> a <= b -> b <= q -> rng RNG (a / 8 + ASAN_K) (b / 8 - a / 8 + 1).
Proof.
  intros RNG p q a b H Hpa Hab Hbq. unfold shadow_addr, ASAN_K in *.
  eapply rng_sub; [exact H | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia].
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* The section's named cover ba_shcov RNG p q is the callee's rng_shcov RNG p n when q = p + n - 1: the two
   spell the same rng term. *)
Lemma ba_rng_shcov : forall RNG p n q, q = p + n - 1 -> ba_shcov RNG p q -> rng_shcov RNG p n.
Proof. intros RNG p n q -> H. exact H. Qed.

(* The thread-cell footprint premise carries from the start memory to a later one: `acl_tls_rng` of
   lib/B/Prog/RcAsanFPLib.v (its one home; this file used to carry a copy of the text). *)
(* ---------------------------------------------------------------------------------------------------------- *)
Local Ltac lia ::= em_lia.

Section BuildF.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a5 a6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (o md b d s ns FS : Z) (mb nb db sb junk : list byte) (RNG : footprint).

  Local Abbreviation SP0 := (bv_unsigned sp).
  Local Abbreviation LO := (bv_unsigned sp - 4640).
  Local Abbreviation NN := (bm_uw md (firstn 8 (skipn 16 mb))).
  Local Abbreviation LEN := (52 + 36 * bm_uw md (firstn 8 (skipn 16 mb))).
  Local Abbreviation GO := (ba_go o md b).
  Local Abbreviation EE := (ba_E (bm_uw md (firstn 8 (skipn 16 mb))) mb b).
  Local Abbreviation NM := ((b = 5 \/ b = 6) /\ has mb <> 0 /\ rname mb <> 0).
  Local Abbreviation RR := (if ba_go o md b && ba_E (bm_uw md (firstn 8 (skipn 16 mb))) mb b
                            then 52 + 36 * bm_uw md (firstn 8 (skipn 16 mb)) else 0).
  Local Abbreviation WW := [(bv_unsigned sp - 4640, bv_unsigned sp);
                            (o, o + (if ba_go o md b && ba_E (bm_uw md (firstn 8 (skipn 16 mb))) mb b
                                     then 52 + 36 * bm_uw md (firstn 8 (skipn 16 mb)) else 0))].
  Local Abbreviation DD := [(BA_FR + 72, BA_FR + 240); (md, md + 296); (d, d + 6); (s, s + 6);
                            (o, o + (if ba_go o md b && ba_E (bm_uw md (firstn 8 (skipn 16 mb))) mb b
                                     then 52 + 36 * bm_uw md (firstn 8 (skipn 16 mb)) else 0))].

  Hypothesis HEA : ctrl_emit_as_contract_F.
  Hypothesis HUW : reac_box_model_upstream_width_contract_F.
  Hypothesis Ho : 0 <= o < 2^64.
  Hypothesis Hmd : 0 <= md < 2^64.
  Hypothesis Hb : 0 <= b < 2^64.
  Hypothesis Hns : -2^31 <= ns <= 0.
  Hypothesis HS16 : SP0 mod 16 = 0.
  Hypothesis HST : em_stk rsegs m LO SP0.
  Hypothesis HT : em_at rsegs m (BA_FR + 72) ba_tbl.
  Hypothesis DsT : ly_dj LO SP0 (BA_FR + 72) (BA_FR + 240).
  Hypothesis Hdb : length db = 6%nat.
  Hypothesis HD : em_at rsegs m d db.
  Hypothesis Dsd : ly_dj LO SP0 d (d + 6).
  Hypothesis Hsb : length sb = 6%nat.
  Hypothesis HSb : em_at rsegs m s sb.
  Hypothesis Dss : ly_dj LO SP0 s (s + 6).
  Hypothesis HM : md <> 0 -> md mod 8 = 0 /\ md + 296 <= 2^64 /\ length mb = 296%nat /\ em_at rsegs m md mb /\
                             ly_dj LO SP0 md (md + 296).
  Hypothesis HN : md <> 0 -> NM -> name_ok nb /\ em_at rsegs m (rname mb) nb /\
                                   ly_dj LO SP0 (rname mb) (rname mb + Z.of_nat (length nb)).
  Hypothesis Ho1492 : o <> 0 -> o + 1492 <= 2^64.
  Hypothesis HEo : GO && EE = true ->
       rw_cells rsegs m o [CB (Z.to_nat LEN) junk] /\ ly_dj LO SP0 o (o + LEN) /\
       ly_dj o (o + LEN) (BA_FR + 72) (BA_FR + 240) /\ ly_dj o (o + LEN) md (md + 296) /\
       (NM -> ly_dj o (o + LEN) (rname mb) (rname mb + Z.of_nat (length nb))) /\
       ly_dj o (o + LEN) d (d + 6) /\ ly_dj o (o + LEN) s (s + 6).
  Hypothesis MI0 : em_mi rsegs m.
  Hypothesis HAC : asan_cells m.
  Hypothesis HSW : shadow_rw m.
  Hypothesis HHM : HIGHMEM_BEG <= LO.
  Hypothesis HAE : SP0 <= APPMEM_END.
  Hypothesis AWIN : addressable m LO 4640.
  Hypothesis ASW : addressable m BA_SW 56.
  Hypothesis ATB : addressable m (BA_FR + 72) 168.
  Hypothesis AD : addressable m d 6.
  Hypothesis AS : addressable m s 6.
  Hypothesis APD : app_mem (d + 6) /\ app_mem (d + 7).
  Hypothesis APS : app_mem (s + 6) /\ app_mem (s + 7).
  Hypothesis AM : md <> 0 -> addressable m md 296.
  Hypothesis AN : md <> 0 -> NM -> addressable m (rname mb) (Z.of_nat (length nb)).
  Hypothesis AO : GO && EE = true -> addressable m o LEN /\ app_mem (o + LEN) /\ (o + LEN <= RT_LO \/ RT_HI <= o).
  Hypothesis AJ14 : b = 1 -> addressable m JOIN_0014 32.
  Hypothesis AJ13 : b = 2 -> addressable m JOIN_0013 32.
  Hypothesis FP : fp [0%nat; 1%nat] m (bv_unsigned tp) FS LO SP0 WW DD.
  Hypothesis FPN : md <> 0 -> NM -> fp_dj [(rname mb, rname mb + Z.of_nat (length nb))] (fp_w [0%nat; 1%nat] FS).
  Hypothesis FPT : reac_ctrl_build_as_tls m (bv_unsigned tp) FS LO SP0.
  (* the footprint premises, in the order of reac_ctrl_build_as_contract_F; each ground shadow cover in the
     named form ba_shcov *)
  Hypothesis RRB : rng_bytes RNG.
  Hypothesis RIMG : rng RNG 0x10000 0x5ee000.
  Hypothesis RISH : rng RNG 0x7fffa000 0xbdc00.
  Hypothesis RWIN : rng RNG LO 4640.
  Hypothesis RWSH : ba_shcov RNG LO (SP0 - 1).
  Hypothesis RGK : rng RNG GOT_CELL_K 8.
  Hypothesis RCK : rng RNG CELL_K 8.
  Hypothesis RFS : rng RNG FS FS_SIZE.
  Hypothesis RFSS : ba_shcov RNG FS (FS + FS_SIZE - 1).
  Hypothesis RTLS : forall (DT TS C T DB : word) (kk : Z),
    asan_tls_cells m (bv_unsigned tp) DT TS C T DB kk ->
    Forall (fun r => rng RNG (fst r) (snd r - fst r)) (fp_tls (bv_unsigned tp) DT TS C T DB kk).
  Hypothesis RMD : md <> 0 -> rng RNG md 296 /\ ba_shcov RNG md (md + 295).
  Hypothesis RDD : rng RNG d 6.
  Hypothesis RDS : ba_shcov RNG d (d + 5).
  Hypothesis RSD : rng RNG s 6.
  Hypothesis RSS : ba_shcov RNG s (s + 5).
  Hypothesis RNB : md <> 0 -> NM -> rng RNG (rname mb) (Z.of_nat (length nb)) /\
    ba_shcov RNG (rname mb) (rname mb + Z.of_nat (length nb) - 1).
  Hypothesis ROO : GO && EE = true -> rng RNG o LEN /\ ba_shcov RNG o (o + LEN - 1).

  Definition aRESbF (m' : word -> option byte) : Prop :=
    bytes_at rsegs m' o
      (em_fr db sb (bv_unsigned a5 mod 65536) (Z_to_bv 8 205) (Z_to_bv 8 234) (ba_X md mb nb b) LEN)
    /\ em_wok NN = true
    /\ (b <= 1 -> blocksum (ba_X md mb nb b) = 0)
    /\ (blocksum (ly_Z md mb nb b) = 0 -> ba_X md mb nb b = ly_Z md mb nb b).

  Definition aQbF : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                      (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 RR)
                    a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch (WW ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]) m m'
      /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' LO SP0
      /\ asan_cells m' /\ shadow_rw m' /\ addressable m' LO 4640
      /\ fp [0%nat; 1%nat] m' (bv_unsigned tp) FS LO SP0 WW DD
      /\ (GO = false -> munch [(SP0 - 80, SP0)] m m')
      /\ (GO && EE = true -> aRESbF m').

  Lemma arng_spF : 4640 <= SP0 < 2^64.
  Proof. pose proof (zr_word sp) as R. unfold inr64 in R. destruct HST as (H1 & _). lia. Qed.

  Lemma aframe_subF : forall X, sub_fp [(SP0 + -80, SP0)] ((LO, SP0) :: X).
  Proof. intros X x Hx. cbn [outside] in *. destruct Hx as [H1 _]. split; [lia | exact I]. Qed.

  Lemma ain_subF : forall lo', LO <= lo' -> sub_fp [(lo', SP0)] [(LO, SP0)].
  Proof. intros lo' H x Hx. cbn [outside] in *. destruct Hx as [H1 _]. split; [lia | exact I]. Qed.

  (* The jump state (the B twin of image A's Theorem Labs lane block): the machine at ctrl_emit_as's entry 0x853c4,
     after the frame pop and the tail jump, with the registers ctrl_emit_as's contract reads (a0 = o, a1 = the row
     address, a2 = md, a3 = d, a4 = s, a6 = NN, a7 = g = 0, t3 = the braid word a6, t4 = ns), ra, sp, gp, tp,
     s0..s11 and a5 as at entry, and a memory that differs from m only inside [LO, SP0).  The lifted stretch ends
     here; ctrl_emit_as (which reaches the fake-stack allocator through ctrl_lay_block) is applied at this cut. *)
  Definition aJumpF (ms' : machine_state) : Prop :=
    exists (t0' t1' t2' a0' a1' a2' a3' a4' a6' a7' t3' t4' t5' t6' : word) (mu : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5 a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 CTRL_EMIT_AS) fc None mu (seg_rom rsegs)
      /\ a0' = Z_to_bv 64 o /\ a1' = Z_to_bv 64 (BA_FR + 24 * ba_row b) /\ a2' = Z_to_bv 64 md
      /\ a3' = Z_to_bv 64 d /\ a4' = Z_to_bv 64 s /\ a6' = Z_to_bv 64 NN /\ a7' = Z_to_bv 64 0
      /\ t3' = a6 /\ t4' = Z_to_bv 64 ns
      /\ munch [(LO, SP0)] m mu /\ wmono rsegs m mu /\ mem_inv rsegs mu /\ stk rsegs mu LO SP0.

  (* The stretch's return of 0: the return state with a0 = 0, a memory that differs from m only inside the
     80-byte frame, wmono, mem_inv and the stack window.  No asan or side-stack conjunct (the caller's memory
     facts follow from munch). *)
  Definition aRet0F : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                      (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0)
                    a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch [(SP0 - 80, SP0)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' LO SP0.

  (* The lifted stretch's post: the jump state when the arguments pass the checks, else the return of 0. *)
  Definition aStretchF (ms' : machine_state) : Prop :=
    (GO = true /\ aJumpF ms') \/ (GO = false /\ aRet0F ms').

  (* The asan facts in a memory that differs from m only inside [LO, SP0) (no side-stack premise: atrF0 is what
     the stretch uses; atrF adds fp for the whole-function proof). *)
  Lemma atrF0 : forall W' mc, munch W' m mc -> wmono rsegs m mc -> sub_fp W' [(LO, SP0)] ->
    asan_cells mc /\ shadow_rw mc /\ (forall p n, addressable m p n -> addressable mc p n).
  Proof.
    intros W' mc MU WM Hs.
    assert (SHo : forall x, in_shadow x -> outside W' x)
      by (intros x Hx; exact (fl_shadow_out W' LO SP0 x Hs HHM Hx)).
    split; [|split].
    - apply (fl_asan_cells W' m mc HAC MU). intros x Hx. apply (fl_out_lo W' LO SP0 x Hs). left.
      unfold RT_LO, RT_HI, HIGHMEM_BEG in *. lia.
    - exact (fl_shadow_rw W' m mc HSW MU WM SHo).
    - intros p n H. exact (fl_addressable W' m mc p n H MU SHo).
  Qed.

  (* The asan facts of atrF0 plus the side stack (the whole-function proof uses this one). *)
  Lemma atrF : forall W' mc, munch W' m mc -> wmono rsegs m mc -> sub_fp W' [(LO, SP0)] ->
    asan_cells mc /\ shadow_rw mc /\ fp [0%nat; 1%nat] mc (bv_unsigned tp) FS LO SP0 WW DD /\
    (forall p n, addressable m p n -> addressable mc p n).
  Proof.
    intros W' mc MU WM Hs.
    destruct (atrF0 W' mc MU WM Hs) as (AC0 & SW0 & AD0).
    split; [exact AC0|]. split; [exact SW0|]. split; [|exact AD0].
    exact (fl_fp _ m mc (bv_unsigned tp) FS LO SP0 _ DD W' FP MU WM Hs).
  Qed.

  (* 0x8538c: a refusal returns 0. *)
  Lemma afailF : forall (x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                       u3 u4 u5 u6 : word) (mc : word -> option byte) (j : list byte),
    GO = false ->
    rw_cells rsegs mc (SP0 + -80) [CB 8 j; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -80) ->
    munch [(SP0 + -80, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evtF rsegs RNG aQbF
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -80)) gp tp u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
               x22 x23 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x8538c) fc None mc (seg_rom rsegs)).
  Proof.
    intros x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 u3 u4 u5 u6 mc j
      HG FR ST MU WM MI.
    pose proof arng_spF as Rsp. pose proof ST as (Rlo & _ & _).
    destruct (atrF _ mc MU WM (ain_subF (SP0 + -80) ltac:(lia))) as (AC1 & SW1 & FP1 & ADT1).
    do 12 step.
    apply evtF_done. unfold aQbF.
    assert (R0 : RR = 0) by (rewrite HG; reflexivity). rewrite R0 in FP1 |- *.
    do 14 eexists. exists mc.
    split; [reflexivity|].
    split; [exact (munch_weaken _ _ m mc (aframe_subF _) MU)|].
    split; [exact WM|]. split; [exact MI|].
    split; [release_frame FR ST (bv_unsigned sp); exact ST|].
    split; [exact AC1|]. split; [exact SW1|]. split; [exact (ADT1 _ _ AWIN)|]. split; [exact FP1|].
    split.
    - intros _. apply (munch_weaken [(SP0 + -80, SP0)]); [|exact MU].
      intros x Hx. cbn [outside] in *. destruct Hx as [H1 _]. split; [lia | exact I].
    - rewrite HG. intros H. cbn [andb] in H. discriminate H.
  Qed.

  (* 0x8538c, for the stretch: afailF's script with the asan and side-stack conjuncts left out (aRet0F). *)
  Lemma afail_retF : forall (x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                       u3 u4 u5 u6 : word) (mc : word -> option byte) (j : list byte),
    GO = false ->
    rw_cells rsegs mc (SP0 + -80) [CB 8 j; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -80) ->
    munch [(SP0 + -80, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evtF rsegs RNG aRet0F
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -80)) gp tp u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
               x22 x23 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x8538c) fc None mc (seg_rom rsegs)).
  Proof.
    intros x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 u3 u4 u5 u6 mc j
      HG FR ST MU WM MI.
    pose proof arng_spF as Rsp. pose proof ST as (Rlo & _ & _).
    do 12 step.
    apply evtF_done. unfold aRet0F.
    do 14 eexists. exists mc.
    split; [reflexivity|].
    split.
    { apply (munch_weaken [(SP0 + -80, SP0)]); [|exact MU].
      intros x Hx. cbn [outside] in *. destruct Hx as [H1 _]. split; [lia | exact I]. }
    split; [exact WM|]. split; [exact MI|].
    release_frame FR ST (bv_unsigned sp); exact ST.
  Qed.

  (* B1 of the glue draft: the state at ctrl_emit_as's entry 0x853c4, where the tail jump of 0x85330 lands.  The
     registers are the ones ctrl_emit_as_contract_F asks for (a0 = o, a1 = the row address, a2 = md, a3 = d,
     a4 = s, a6 = NN, a7 = g = 0, t3 = the braid word a6, t4 = ns); the memory facts are the ones the run below
     the jump carries.  Cutting the lemma here keeps the prefix free of the ctrl_emit_as cut. *)
  Definition AT_853c4 (u0 u1 u2 u5 u6 : word) : machine_state -> Prop :=
    fun ms => exists mu : word -> option byte,
      ms = MS (mkR ra sp gp tp u0 u1 u2 s0 s1 (Z_to_bv 64 o)
                   (Z_to_bv 64 (BA_FR + 24 * ba_row b)) (Z_to_bv 64 md) (Z_to_bv 64 d) (Z_to_bv 64 s) a5
                   (Z_to_bv 64 NN) (Z_to_bv 64 0) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a6 (Z_to_bv 64 ns) u5 u6)
              F (Z_to_bv 64 0x853c4) fc None mu (seg_rom rsegs)
      /\ munch [(LO, SP0)] m mu /\ wmono rsegs m mu /\ mem_inv rsegs mu /\ stk rsegs mu LO SP0.

  (* 0x85330 .. 0x853c4: the width call, the frame pops and the tail jump to ctrl_emit_as (B1: the prefix). *)
  Lemma atail_pre : forall (u0 u1 u2 x10 x11 x12 x13 x14 u3 u4 u5 u6 : word) (mc : word -> option byte)
                       (j : list byte) (f : Z),
    GO = true -> f = BA_FR + 24 * ba_row b ->
    rw_cells rsegs mc (SP0 + -80) [CB 8 j; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -80) ->
    munch [(SP0 + -80, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evtF rsegs RNG (AT_853c4 u0 u1 u2 u5 u6)
      (MS (mkR ra (Z_to_bv 64 (SP0 + -80)) gp tp u0 u1 u2 (Z_to_bv 64 ns) a6 x10 x11 x12 x13 x14 a5 a6
               (Z_to_bv 64 ns) a5 (Z_to_bv 64 s) (Z_to_bv 64 d) (Z_to_bv 64 md) (Z_to_bv 64 o) (Z_to_bv 64 f)
               s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x85330) fc None mc (seg_rom rsegs)).
  Proof.
    intros u0 u1 u2 x10 x11 x12 x13 x14 u3 u4 u5 u6 mc j f HG -> FR ST MU WM MI.
    pose proof arng_spF as Rsp. pose proof ST as (Rlo & _ & _).
    pose proof HG as HG'. apply andb_true_iff in HG' as [HG1 Hb6]. apply andb_true_iff in HG1 as [Ho0 Hm0].
    apply negb_true_iff, Z.eqb_neq in Ho0. apply negb_true_iff, Z.eqb_neq in Hm0. apply Z.leb_le in Hb6.
    assert (Hb6' : 0 <= b <= 6) by lia.
    destruct (ba_facts b Hb6') as (FK & KR & FBB & FC & FL & FG & FA & F18 & F19 & FAO & FAL).
    destruct (HM Hm0) as (M8 & M296 & ML & HMm & DM).
    pose proof DM as DMu. unfold ly_dj in DMu.
    pose proof (em_obj0 rsegs m mc (SP0 + -80) SP0 md mb 296 MU HMm ltac:(rewrite ML; reflexivity)
                  ltac:(lia)) as HMc.
    pose proof (bm_uw_range md (firstn 8 (skipn 16 mb))) as RN.
    destruct (atrF0 _ mc MU WM (ain_subF (SP0 + -80) ltac:(lia))) as (AC1 & SW1 & ADT1).
    (* reac_box_model_upstream_width(m) *)
    step. step.
    eapply evtF_cut.
    { eapply HUW with (mp := md) (lo := LO) (bs := firstn 8 (skipn 16 mb)).
      - rewrite unsigned_lit by lia. reflexivity.
      - intros _. split; [lia|]. split.
        + rewrite length_firstn, length_skipn, ML. reflexivity.
        + pose proof (ly_bytes_sub rsegs mc md mb 16 8 HMc ltac:(rewrite ML; lia)) as H16.
          change (Z.of_nat 16) with 16 in H16. exact H16.
      - rewrite unsigned_lit by lia. exact ST.
      - rewrite unsigned_lit by lia. unfold REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME. lia.
      - intros _. rewrite unsigned_lit by lia. unfold REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME. lia.
      - exact AC1.
      - exact SW1.
      - intros _. exact M8.
      - intros _. apply (aaddr_sub mc md 296); [exact (ADT1 _ _ (AM Hm0)) | lia | lia | lia].
      - intros x Hx. rewrite unsigned_lit by lia. unfold REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME.
        cbn [outside]. split; [|exact I].
        unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *. lia.
      - rewrite unsigned_lit by lia. unfold REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME.
        eapply rng_sub; [exact RWIN | lia | lia].
      - exact RGK.
      - exact RCK.
      - intros _. split.
        + eapply rng_sub; [exact (proj1 (RMD Hm0)) | lia | lia].
        + eapply (ba_shcov_byte _ md (md + 295)); [exact (proj2 (RMD Hm0)) | lia | lia | lia]. }
    intros ms' (y1 & y2 & y3 & y4 & mu & -> & MUu & WMu & MIu & STu). afixret.
    rewrite unsigned_lit in MUu, STu by lia. unfold REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME in MUu.
    pose proof (MIu MI) as MI2.
    pose proof (rw_cells_transport rsegs [(SP0 + -80 - 16, SP0 + -80)] mc mu (SP0 + -80) _ FR MUu WMu
                  ltac:(cbn [disjoint_from cells_size csize]; lia)) as FR2.
    (* the arguments, the restores and the jump *)
    do 21 step.
    release_frame FR2 STu (bv_unsigned sp).
    (* the memory at the jump differs from m only inside [LO, SP0) *)
    assert (MUt : munch [(LO, SP0)] m mu).
    { apply (munch_trans _ m mc mu).
      - apply (munch_weaken _ _ m mc (ain_subF (SP0 + -80) ltac:(lia)) MU).
      - apply (munch_weaken _ _ mc mu (ain_subF (SP0 + -80 - 16) ltac:(lia))). eapply munch_weaken; [|exact MUu].
        intros x Hx. cbn [outside] in *. destruct Hx as [H1 _]. split; [lia | exact I]. }
    pose proof (wmono_trans rsegs m mc mu WM WMu) as WMt.
    apply evtF_done. unfold AT_853c4. eexists.
    split; [reflexivity|]. split; [exact MUt|]. split; [exact WMt|]. split; [exact MI2 | exact STu].
  Qed.

  (* 0x85330 .. 0x853c4 for the stretch: atail_pre's run, with the concrete state at the jump read as aJumpF.
     The B twin of image A's atail_jumpF. *)
  Lemma atail_jumpF : forall (u0 u1 u2 x10 x11 x12 x13 x14 u3 u4 u5 u6 : word) (mc : word -> option byte)
                       (j : list byte) (f : Z),
    GO = true -> f = BA_FR + 24 * ba_row b ->
    rw_cells rsegs mc (SP0 + -80) [CB 8 j; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -80) ->
    munch [(SP0 + -80, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evtF rsegs RNG aJumpF
      (MS (mkR ra (Z_to_bv 64 (SP0 + -80)) gp tp u0 u1 u2 (Z_to_bv 64 ns) a6 x10 x11 x12 x13 x14 a5 a6
               (Z_to_bv 64 ns) a5 (Z_to_bv 64 s) (Z_to_bv 64 d) (Z_to_bv 64 md) (Z_to_bv 64 o) (Z_to_bv 64 f)
               s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x85330) fc None mc (seg_rom rsegs)).
  Proof.
    intros u0 u1 u2 x10 x11 x12 x13 x14 u3 u4 u5 u6 mc j f HG Ef FR ST MU WM MI.
    eapply evtF_cut;
      [ exact (atail_pre u0 u1 u2 x10 x11 x12 x13 x14 u3 u4 u5 u6 mc j f HG Ef FR ST MU WM MI) |].
    intros ms' HA. unfold AT_853c4 in HA. destruct HA as (mu & -> & MUt & WMt & MI2 & STu).
    apply evtF_done. unfold aJumpF, CTRL_EMIT_AS.
    do 14 eexists. exists mu.
    split; [reflexivity|].
    do 9 (split; [reflexivity|]).
    split; [exact MUt|]. split; [exact WMt|]. split; [exact MI2 | exact STu].
  Qed.

  (* 0x853c4 ..: the whole ctrl_emit_as run (the one cut) and the post mapping (B1: the emit half).  The proof
     text is the one atailF carried; only the facts at 0x853c4 are now premises instead of context. *)
  Lemma atail_emit : forall (u0 u1 u2 u5 u6 : word) (ms : machine_state),
    GO = true -> AT_853c4 u0 u1 u2 u5 u6 ms -> evtF rsegs RNG aQbF ms.
  Proof.
    intros u0 u1 u2 u5 u6 ms HG HA. unfold AT_853c4 in HA.
    destruct HA as (mu & -> & MUt & WMt & MI2 & STu).
    pose proof arng_spF as Rsp. pose proof STu as (Rlo & _ & _).
    pose proof HG as HG'. apply andb_true_iff in HG' as [HG1 Hb6]. apply andb_true_iff in HG1 as [Ho0 Hm0].
    apply negb_true_iff, Z.eqb_neq in Ho0. apply negb_true_iff, Z.eqb_neq in Hm0. apply Z.leb_le in Hb6.
    assert (Hb6' : 0 <= b <= 6) by lia.
    destruct (ba_facts b Hb6') as (FK & KR & FBB & FC & FL & FG & FA & F18 & F19 & FAO & FAL).
    destruct (HM Hm0) as (M8 & M296 & ML & HMm & DM).
    pose proof DM as DMu. unfold ly_dj in DMu.
    pose proof (bm_uw_range md (firstn 8 (skipn 16 mb))) as RN.
    destruct (atrF _ mu MUt WMt (fun x Hx => Hx)) as (AC2 & SW2 & FP2 & ADT2).
    (* the facts ctrl_emit_as needs, in the memory at the jump *)
    pose proof DsT as DsTu. unfold ly_dj in DsTu.
    pose proof (aba_row_at rsegs mu b
                  (em_obj0 rsegs m mu LO SP0 (BA_FR + 72) ba_tbl 168 MUt HT ltac:(vm_compute; reflexivity)
                     ltac:(lia)) Hb6')
      as HRc.
    pose proof Dsd as Dsdu. unfold ly_dj in Dsdu. pose proof Dss as Dssu. unfold ly_dj in Dssu.
    pose proof (em_obj0 rsegs m mu LO SP0 d db 6 MUt HD ltac:(rewrite Hdb; reflexivity) ltac:(lia)) as HDc.
    pose proof (em_obj0 rsegs m mu LO SP0 s sb 6 MUt HSb ltac:(rewrite Hsb; reflexivity) ltac:(lia)) as HSc.
    pose proof (em_obj0 rsegs m mu LO SP0 md mb 296 MUt HMm ltac:(rewrite ML; reflexivity) ltac:(lia)) as HMu.
    assert (NMc : forall X : Prop, (NM -> X) ->
              (3 <= ly_k (ba_fr (ba_row b)) <= 9 /\
               (ly_bb (ly_k (ba_fr (ba_row b))) = 5 \/ ly_bb (ly_k (ba_fr (ba_row b))) = 6)) /\
              has mb <> 0 /\ rname mb <> 0 -> X).
    { intros X HX ((_ & B56) & H1 & H2). apply HX. rewrite FK, FBB in B56. split; [exact B56 | split; assumption]. }
    (* the data ranges apart from the class-1 side-stack bytes *)
    pose proof (fl_fp_dj _ _ _ _ _ _ _ _ FP) as DJ.
    apply fl_dj_cons in DJ as (DJT & DJ). apply fl_dj_cons in DJ as (DJM & DJ).
    apply fl_dj_cons in DJ as (DJd & DJ). apply fl_dj_cons in DJ as (DJs & DJo).
    pose proof KR as Rrow.
    assert (DJf : fp_dj [(BA_FR + 24 * ba_row b, BA_FR + 24 * ba_row b + 24)] (fp_w [0%nat; 1%nat] FS))
      by (apply (fl_dj_sub _ _ _ _ _ DJT); lia).
    assert (AF : addressable mu (BA_FR + 24 * ba_row b) 24)
      by (apply (aaddr_sub mu (BA_FR + 72) 168); [exact (ADT2 _ _ ATB) | lia | lia | lia]).
    pose proof HEA as HE. unfold ctrl_emit_as_contract_F, CTRL_EMIT_AS_K in HE. cbv zeta in HE.
    eapply evtF_cut.
    { eapply HE with (o := o) (f := BA_FR + 24 * ba_row b) (md := md) (d := d) (s := s) (g := 0) (n := NN)
        (ns := ns) (FS := FS) (row := ba_fr (ba_row b)) (tb := []) (mb := mb) (nb := nb) (gb := []) (db := db)
        (sb := sb) (junk := junk).
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - lia.
      - lia.
      - lia.
      - exact HS16.
      - exact STu.
      - apply (em_dj_sub _ _ _ _ _ _ _ _ DsT); lia.
      - intros K2. exfalso. rewrite FK in K2. lia.
      - exact DM.
      - apply NMc. intros NMx. destruct (HN Hm0 NMx) as (_ & _ & DN). exact DN.
      - exact Dsd.
      - exact Dss.
      - intros G0. exfalso. exact (G0 eq_refl).
      - unfold BA_FR. lia.
      - unfold BA_FR. lia.
      - unfold BA_FR. lia.
      - apply ba_fr_len.
      - exact HRc.
      - rewrite FK. lia.
      - rewrite FC. destruct (b <=? 1); lia.
      - lia.
      - lia.
      - lia.
      - rewrite FAO, FAL. lia.
      - intros K2. exfalso. rewrite FK in K2. lia.
      - rewrite FC. destruct (b <=? 1); intros C2; exfalso; lia.
      - intros L2. lia.
      - exact Hm0.
      - exact M8.
      - exact M296.
      - exact ML.
      - exact HMu.
      - apply NMc. intros NMx. destruct (HN Hm0 NMx) as (NO & NB & DN). split; [exact NO|].
        pose proof DN as DNu. unfold ly_dj in DNu.
        exact (em_obj0 rsegs m mu LO SP0 _ nb _ MUt NB eq_refl ltac:(lia)).
      - lia.
      - exact (Ho1492 Ho0).
      - rewrite (ba_E_eq b NN mb Hb6'), (ba_len_eq b NN Hb6'). intros E1.
        assert (GE : GO && EE = true) by (rewrite HG; exact E1).
        destruct (HEo GE) as (HO & Dso & DoT & Dom & Don & Dod & Dos).
        pose proof Dso as Dsou. unfold ly_dj in Dsou.
        split.
        { apply (rw_cells_transport rsegs [(LO, SP0)] m mu o _ HO MUt WMt).
          cbn [disjoint_from cells_size csize]. lia. }
        split; [exact Dso|]. split; [apply (em_dj_sub _ _ _ _ _ _ _ _ DoT); lia|].
        split; [intros K2; exfalso; rewrite FK in K2; lia|].
        split; [exact Dom|]. split; [apply NMc; exact Don|].
        split; [exact Dod|]. split; [exact Dos|].
        intros G0. exfalso. exact (G0 eq_refl).
      - exact Hdb.
      - exact HDc.
      - exact Hsb.
      - exact HSc.
      - intros G0. exfalso. exact (G0 eq_refl).
      - intros _. lia.
      - exact MI2.
      - exact AC2.
      - exact SW2.
      - exact HHM.
      - exact HAE.
      - exact (ADT2 _ _ AWIN).
      - exact AF.
      - exact (ADT2 _ _ (AM Hm0)).
      - exact (ADT2 _ _ AD).
      - exact (ADT2 _ _ AS).
      - exact APD.
      - exact APS.
      - intros K2. exfalso. rewrite FK in K2. lia.
      - apply NMc. intros NMx. exact (ADT2 _ _ (AN Hm0 NMx)).
      - intros G0. exfalso. exact (G0 eq_refl).
      - intros G0. exfalso. exact (G0 eq_refl).
      - rewrite (ba_E_eq b NN mb Hb6'), (ba_len_eq b NN Hb6'). intros E1.
        assert (GE : GO && EE = true) by (rewrite HG; exact E1).
        destruct (AO GE) as (AOo & AOe & AOr). split; [exact (ADT2 _ _ AOo)|]. split; assumption.
      - intros K5. rewrite FK in K5. apply ADT2, AJ14. rewrite <- FBB, K5. reflexivity.
      - intros K6. rewrite FK in K6. apply ADT2, AJ13. rewrite <- FBB, K6. reflexivity.
      - rewrite (ba_E_eq b NN mb Hb6'), (ba_len_eq b NN Hb6').
        rewrite HG in FP2, DJo. cbn [andb] in FP2, DJo.
        apply (fl_fp_D _ _ _ _ _ _ _ _ _ FP2).
        apply fl_dj_cons. split; [exact DJf|]. apply fl_dj_cons. split; [exact DJM|].
        apply fl_dj_cons. split; [exact DJd|]. apply fl_dj_cons. split; [exact DJs|]. exact DJo.
      - intros K2. exfalso. rewrite FK in K2. lia.
      - apply NMc. intros NMx. exact (FPN Hm0 NMx).
      - intros G0. exfalso. exact (G0 eq_refl).
      - unfold ctrl_emit_as_tls. exact (fl_tls _ m mu _ FS _ _ _ _ _ _ FP MUt (fun x Hx => Hx) FPT).
      (* the footprint premises of ctrl_emit_as, in the order of ctrl_emit_as_contract_F *)
      - exact RRB.
      - exact RWIN.
      - apply (ba_rng_shcov _ _ _ (SP0 - 1)); [lia | exact RWSH].
      - exact RFS.
      - exact RFSS.
      - exact RIMG.
      - (* the thread-cell premise, taken at m, carried to the memory mu of the jump (the run wrote only
           [LO, SP0) before it, inside fp's W) *)
        assert (SUBj : sub_fp [(LO, SP0)] WW)
          by (intros x Hx; cbn [outside] in *; destruct Hx as [H1 _]; split; [exact H1 | exact I]).
        unfold rng_tls.
        exact (acl_tls_rng _ m mu _ FS _ _ _ _ [(LO, SP0)]
                 (fun l => Forall (fun r : ivl => rng RNG (fst r) (snd r - fst r)) l) FP MUt SUBj RTLS).
      - eapply rng_sub; [exact RIMG | unfold BA_FR; lia | unfold BA_FR; lia].
      - unfold rng_shcov. apply ba_shcov_img; [exact RISH | unfold BA_FR; lia | lia | unfold BA_FR; lia].
      - exact (proj1 (RMD Hm0)).
      - apply (ba_rng_shcov _ _ _ (md + 295)); [lia | exact (proj2 (RMD Hm0))].
      - exact RDD.
      - apply (ba_rng_shcov _ _ _ (d + 5)); [lia | exact RDS].
      - exact RSD.
      - apply (ba_rng_shcov _ _ _ (s + 5)); [lia | exact RSS].
      - rewrite (ba_E_eq b NN mb Hb6'), (ba_len_eq b NN Hb6'). intros E1.
        assert (GE : GO && EE = true) by (rewrite HG; exact E1).
        exact (ROO GE).
      - intros K2. exfalso. rewrite FK in K2. lia.
      - apply NMc. intros NMx. exact (RNB Hm0 NMx).
      - intros G0. exfalso. exact (G0 eq_refl).
      (* the shadow covers of the two JOIN blocks: inside the image, so inside the image-shadow range *)
      - intros _. unfold rng_shcov.
        apply ba_shcov_img; [exact RISH | unfold JOIN_0014; lia | lia | unfold JOIN_0014; lia].
      - intros _. unfold rng_shcov.
        apply ba_shcov_img; [exact RISH | unfold JOIN_0013; lia | lia | unfold JOIN_0013; lia]. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> &
                MU' & WM' & MI' & ST' & AC' & SW' & AW' & FP' & RES').
    apply evtF_done. unfold aQbF.
    rewrite (ba_E_eq b NN mb Hb6'), (ba_len_eq b NN Hb6') in MU', FP'. rewrite (ba_E_eq b NN mb Hb6') in RES'.
    rewrite (ba_E_eq b NN mb Hb6'), (ba_len_eq b NN Hb6').
    rewrite HG. cbn [andb].
    rewrite HG in DJo. cbn [andb] in DJo.
    do 14 eexists. exists m'.
    split; [reflexivity|].
    split.
    { apply (munch_trans _ m mu m'); [|exact MU'].
      apply (munch_weaken [(LO, SP0)] _ m mu); [|exact MUt].
      intros x Hx. cbn [outside app] in *. destruct Hx as [H1 _]. split; [exact H1 | exact I]. }
    split; [exact (wmono_trans rsegs m mu m' WMt WM')|]. split; [exact MI'|]. split; [exact ST'|].
    split; [exact AC'|]. split; [exact SW'|]. split; [exact AW'|].
    split.
    { apply (fl_fp_D _ _ _ _ _ _ _ _ _ FP').
      apply fl_dj_cons. split; [exact DJT|]. apply fl_dj_cons. split; [exact DJM|].
      apply fl_dj_cons. split; [exact DJd|]. apply fl_dj_cons. split; [exact DJs|]. exact DJo. }
    split; [intros H; discriminate H|].
    intros E1. destruct (RES' E1) as (B & W & CL).
    exact (ba_res rsegs m' o b md NN (bv_unsigned a5 mod 65536) mb nb [] [] db sb Hb6' B W CL).
  Qed.

  (* atailF as it was, from the two halves (B1). *)
  Lemma atailF : forall (u0 u1 u2 x10 x11 x12 x13 x14 u3 u4 u5 u6 : word) (mc : word -> option byte)
                       (j : list byte) (f : Z),
    GO = true -> f = BA_FR + 24 * ba_row b ->
    rw_cells rsegs mc (SP0 + -80) [CB 8 j; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -80) ->
    munch [(SP0 + -80, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evtF rsegs RNG aQbF
      (MS (mkR ra (Z_to_bv 64 (SP0 + -80)) gp tp u0 u1 u2 (Z_to_bv 64 ns) a6 x10 x11 x12 x13 x14 a5 a6
               (Z_to_bv 64 ns) a5 (Z_to_bv 64 s) (Z_to_bv 64 d) (Z_to_bv 64 md) (Z_to_bv 64 o) (Z_to_bv 64 f)
               s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x85330) fc None mc (seg_rom rsegs)).
  Proof.
    intros u0 u1 u2 x10 x11 x12 x13 x14 u3 u4 u5 u6 mc j f HG Ef FR ST MU WM MI.
    eapply evtF_cut;
      [ exact (atail_pre u0 u1 u2 x10 x11 x12 x13 x14 u3 u4 u5 u6 mc j f HG Ef FR ST MU WM MI)
      | intros ms' HA; exact (atail_emit u0 u1 u2 u5 u6 ms' HG HA) ].
  Qed.

  (* B2 of the glue draft: the entry with a post VARIABLE QB.  The refusal arms end at aQbF (HQ0 lifts them), and
     the go arm hands the state at 0x853c4 to HQ1, so a caller can stop the run at the tail jump. *)
  Lemma amainF_Q : forall (QB : machine_state -> Prop),
    (forall ms, GO = false -> aQbF ms -> QB ms) ->
    (forall u0 u1 u2 u5 u6 ms, GO = true -> AT_853c4 u0 u1 u2 u5 u6 ms -> evtF rsegs RNG QB ms) ->
    forall (t0 t1 t2 t3 t4 t5 t6 : word),
    evtF rsegs RNG QB
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 md) (Z_to_bv 64 b) (Z_to_bv 64 d)
               (Z_to_bv 64 s) a5 a6 (Z_to_bv 64 ns) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8528c) fc None m (seg_rom rsegs)).
  Proof.
    intros QB HQ0 HQ1 t0 t1 t2 t3 t4 t5 t6.
    pose proof arng_spF as Rsp.
    pose proof (HST : stk rsegs m (bv_unsigned sp - 4640) (bv_unsigned sp)) as ST. pose proof ST as (Rlo & _ & _).
    pose proof (MI0 : mem_inv rsegs m) as MI.
    pose proof (munch_refl [(bv_unsigned sp + -80, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    (* the literal-address copies of the two runtime cells (the image and image-shadow premises are literal) *)
    pose proof RGK as RGKu. unfold GOT_CELL_K in RGKu.
    pose proof RCK as RCKu. unfold CELL_K in RCKu.
    (* the runtime's cells and the switch table's shadow, apart from the frame *)
    assert (HW : forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
                   outside [(bv_unsigned sp + -80, bv_unsigned sp)] x).
    { intros x Hx. cbn [outside]. split; [|exact I].
      unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *. lia. }
    pose proof (rt_asan_rt m _ HAC HW) as HRT.
    pose proof (rt_shadow_rd m BA_SW 56 _ ASW (fun x Hx => HW x (or_intror (or_intror Hx)))) as HSR.
    pose proof (rt_addressable m BA_SW 56 ASW) as HAD.
    pose proof (rt_rt3 m BA_SW 56 ASW) as H3.
    step. carve_frame 80%nat ST. do 9 step.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    pose proof (asan_rt_munch rsegs m m1 _ _ ASAN_K _ _ HRT MU (fun x Hx => Hx)) as HRT1.
    pose proof (asan_shadow_rd_munch rsegs m m1 ASAN_K BA_SW 56 _ _ HSR MU (fun x Hx => Hx)) as HSR1.
    pose proof (asan_addressable_munch rsegs m m1 ASAN_K BA_SW 56 _ _ HAD HSR MU (fun x Hx => Hx)) as HAD1.
    pose proof (asan_rt3_munch rsegs m m1 ASAN_K BA_SW 56 _ _ H3 HSR MU (fun x Hx => Hx)) as H31.
    (* o = 0 *)
    step. rewrite rc_eqb by lia. destruct (Z.eqb_spec o 0) as [O0|O0]; cbv iota.
    { assert (HGF : GO = false) by (apply ba_go_false; left; exact O0).
      eapply evtF_mono;
        [ eapply afailF; [exact HGF | eassumption ..] | intros ms_ HP_; exact (HQ0 ms_ HGF HP_) ]. }
    (* m = 0 *)
    step. step. rewrite rc_eqb by lia. destruct (Z.eqb_spec md 0) as [M0|M0]; cbv iota.
    { assert (HGF : GO = false) by (apply ba_go_false; right; left; exact M0).
      eapply evtF_mono;
        [ eapply afailF; [exact HGF | eassumption ..] | intros ms_ HP_; exact (HQ0 ms_ HGF HP_) ]. }
    (* b > 6 *)
    step. step. step. rewrite rc_ltu by lia. destruct (Z.ltb_spec 6 b) as [B6|B6]; cbv iota.
    { assert (HGF : GO = false) by (apply ba_go_false; right; right; exact B6).
      eapply evtF_mono;
        [ eapply afailF; [exact HGF | eassumption ..] | intros ms_ HP_; exact (HQ0 ms_ HGF HP_) ]. }
    assert (HG : GO = true) by (apply ba_go_true; assumption).
    (* the shadow byte of the table word b is 0 *)
    destruct (asan_shadow_read_at rsegs m1 ASAN_K BA_SW 56 _ (8 * b) ((BA_SW + 8 * b) / 8 + ASAN_K) HSR1
                ltac:(lia) eq_refl) as (k & RK & BK).
    pose proof (asan_check_8 rsegs m1 ASAN_K BA_SW 56 (8 * b) k HAD1 H31 ltac:(lia) ltac:(lia)
                  ltac:(unfold BA_SW; lia) BK) as K0.
    pose proof (rc_signed0_unsigned0 k K0) as K0u.
    pose proof (asan_rt_got_read rsegs m1 _ _ ASAN_K _ HRT1) as RG.
    pose proof (asan_rt_cell_read rsegs m1 _ _ ASAN_K _ HRT1) as RC.
    unfold GOT_CELL_K, CELL_K in RG, RC.
    (* the shadow bytes of the seven table words, in the shape the check computes them: the address is
       (BA_SW + 8 b) >> 3 + ASAN_K, and ASAN_K comes from the runtime cell, so it stays a constant. *)
    assert (RSHSW : rng RNG (17200 + ASAN_K) 7)
      by (eapply rng_sub; [exact RISH | unfold ASAN_K; lia | unfold ASAN_K; lia]).
    (* row(b) from the table, f = CTRL_FRAMES + 24 row(b), and the pointer check (0x85314: ~f0 < 24 row(b) traps;
       f0 = CTRL_FRAMES, so it does not) *)
    destruct (ba_cases b ltac:(lia)) as [Eb|[Eb|[Eb|[Eb|[Eb|[Eb|Eb]]]]]]; rewrite Eb in RK |- *;
      unfold BA_SW, ASAN_K in RK;
      do 11 step;
      rewrite (rcl_zxb_eqb k 0) by lia; rewrite K0u; cbn [Z.eqb negb];
      do 8 step;
      match goal with |- context [bv_ltu ?x ?y] => replace (bv_ltu x y) with false by (vm_compute; reflexivity) end;
      cbv iota;
      do 6 step;
      (eapply evtF_cut;
        [ eapply atail_pre; [exact HG | rewrite Eb; reflexivity | eassumption ..]
        | intros ms_ HA_; exact (HQ1 _ _ _ _ _ ms_ HG HA_) ]).
  Qed.

  (* amainF as it was, from amainF_Q (B2). *)
  Lemma amainF : forall (t0 t1 t2 t3 t4 t5 t6 : word),
    evtF rsegs RNG aQbF
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 md) (Z_to_bv 64 b) (Z_to_bv 64 d)
               (Z_to_bv 64 s) a5 a6 (Z_to_bv 64 ns) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8528c) fc None m (seg_rom rsegs)).
  Proof.
    exact (amainF_Q aQbF (fun _ _ h => h) (fun u0 u1 u2 u5 u6 ms HG HA => atail_emit u0 u1 u2 u5 u6 ms HG HA)).
  Qed.

  (* The lifted stretch [entry, tail jump) (or the return of 0): amainF_Q's script with the refusal arms ended at
     aRet0F and the go arm at aJumpF, so that nothing in it reads the side stack (atrF0, afail_retF,
     atail_jumpF).  The B twin of image A's amain_stretchF. *)
  Lemma amain_stretchF : forall (t0 t1 t2 t3 t4 t5 t6 : word),
    evtF rsegs RNG aStretchF
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 md) (Z_to_bv 64 b) (Z_to_bv 64 d)
               (Z_to_bv 64 s) a5 a6 (Z_to_bv 64 ns) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8528c) fc None m (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 t3 t4 t5 t6.
    pose proof arng_spF as Rsp.
    pose proof (HST : stk rsegs m (bv_unsigned sp - 4640) (bv_unsigned sp)) as ST. pose proof ST as (Rlo & _ & _).
    pose proof (MI0 : mem_inv rsegs m) as MI.
    pose proof (munch_refl [(bv_unsigned sp + -80, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    (* the literal-address copies of the two runtime cells (the image and image-shadow premises are literal) *)
    pose proof RGK as RGKu. unfold GOT_CELL_K in RGKu.
    pose proof RCK as RCKu. unfold CELL_K in RCKu.
    (* the runtime's cells and the switch table's shadow, apart from the frame *)
    assert (HW : forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
                   outside [(bv_unsigned sp + -80, bv_unsigned sp)] x).
    { intros x Hx. cbn [outside]. split; [|exact I].
      unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *. lia. }
    pose proof (rt_asan_rt m _ HAC HW) as HRT.
    pose proof (rt_shadow_rd m BA_SW 56 _ ASW (fun x Hx => HW x (or_intror (or_intror Hx)))) as HSR.
    pose proof (rt_addressable m BA_SW 56 ASW) as HAD.
    pose proof (rt_rt3 m BA_SW 56 ASW) as H3.
    step. carve_frame 80%nat ST. do 9 step.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    pose proof (asan_rt_munch rsegs m m1 _ _ ASAN_K _ _ HRT MU (fun x Hx => Hx)) as HRT1.
    pose proof (asan_shadow_rd_munch rsegs m m1 ASAN_K BA_SW 56 _ _ HSR MU (fun x Hx => Hx)) as HSR1.
    pose proof (asan_addressable_munch rsegs m m1 ASAN_K BA_SW 56 _ _ HAD HSR MU (fun x Hx => Hx)) as HAD1.
    pose proof (asan_rt3_munch rsegs m m1 ASAN_K BA_SW 56 _ _ H3 HSR MU (fun x Hx => Hx)) as H31.
    (* o = 0 *)
    step. rewrite rc_eqb by lia. destruct (Z.eqb_spec o 0) as [O0|O0]; cbv iota.
    { eapply evtF_cut; [eapply afail_retF; [apply ba_go_false; left; exact O0 | eassumption ..] |
      intros ms' HQ; apply evtF_done; right; split; [apply ba_go_false; left; exact O0 | exact HQ]]. }
    (* m = 0 *)
    step. step. rewrite rc_eqb by lia. destruct (Z.eqb_spec md 0) as [M0|M0]; cbv iota.
    { eapply evtF_cut; [eapply afail_retF; [apply ba_go_false; right; left; exact M0 | eassumption ..] |
      intros ms' HQ; apply evtF_done; right; split; [apply ba_go_false; right; left; exact M0 | exact HQ]]. }
    (* b > 6 *)
    step. step. step. rewrite rc_ltu by lia. destruct (Z.ltb_spec 6 b) as [B6|B6]; cbv iota.
    { eapply evtF_cut; [eapply afail_retF; [apply ba_go_false; right; right; exact B6 | eassumption ..] |
      intros ms' HQ; apply evtF_done; right; split; [apply ba_go_false; right; right; exact B6 | exact HQ]]. }
    assert (HG : GO = true) by (apply ba_go_true; assumption).
    (* the shadow byte of the table word b is 0 *)
    destruct (asan_shadow_read_at rsegs m1 ASAN_K BA_SW 56 _ (8 * b) ((BA_SW + 8 * b) / 8 + ASAN_K) HSR1
                ltac:(lia) eq_refl) as (k & RK & BK).
    pose proof (asan_check_8 rsegs m1 ASAN_K BA_SW 56 (8 * b) k HAD1 H31 ltac:(lia) ltac:(lia)
                  ltac:(unfold BA_SW; lia) BK) as K0.
    pose proof (rc_signed0_unsigned0 k K0) as K0u.
    pose proof (asan_rt_got_read rsegs m1 _ _ ASAN_K _ HRT1) as RG.
    pose proof (asan_rt_cell_read rsegs m1 _ _ ASAN_K _ HRT1) as RC.
    unfold GOT_CELL_K, CELL_K in RG, RC.
    assert (RSHSW : rng RNG (17200 + ASAN_K) 7)
      by (eapply rng_sub; [exact RISH | unfold ASAN_K; lia | unfold ASAN_K; lia]).
    (* row(b) from the table, f = CTRL_FRAMES + 24 row(b), and the pointer check (0x85314: ~f0 < 24 row(b) traps;
       f0 = CTRL_FRAMES, so it does not) *)
    destruct (ba_cases b ltac:(lia)) as [Eb|[Eb|[Eb|[Eb|[Eb|[Eb|Eb]]]]]]; rewrite Eb in RK |- *;
      unfold BA_SW, ASAN_K in RK;
      do 11 step;
      rewrite (rcl_zxb_eqb k 0) by lia; rewrite K0u; cbn [Z.eqb negb];
      do 8 step;
      match goal with |- context [bv_ltu ?x ?y] => replace (bv_ltu x y) with false by (vm_compute; reflexivity) end;
      cbv iota;
      do 6 step;
      (eapply evtF_cut;
        [ eapply atail_jumpF; [exact HG | rewrite Eb; reflexivity | eassumption ..]
        | intros ms' HJ; apply evtF_done; left; split; [exact HG | exact HJ] ]).
  Qed.

  (* -------------------------------------------------------------------------------------------------------- *)
  (* Route (C) (a Theorem Labs lane 2026-10-29 09:20Z): the stretch's lemmas without HSW.  The stretch read `shadow_rw m` only to
     feed reac_box_model_upstream_width's contract (a Theorem Labs lane 11:26Z), and that callee's _on contract,
     reac_box_model_upstream_width_contract_F_on (HUW_on), has no shadow premise.  The _on lemmas below cite HUW_on;
     none of them uses HSW or HUW.  The lemmas above are unchanged. *)
  Hypothesis HUW_on : reac_box_model_upstream_width_contract_F_on.

  (* atrF0 without its shadow_rw conjunct, the one conjunct that read HSW. *)
  Lemma atrF0_on : forall W' mc, munch W' m mc -> wmono rsegs m mc -> sub_fp W' [(LO, SP0)] ->
    asan_cells mc /\ (forall p n, addressable m p n -> addressable mc p n).
  Proof.
    intros W' mc MU WM Hs.
    assert (SHo : forall x, in_shadow x -> outside W' x)
      by (intros x Hx; exact (fl_shadow_out W' LO SP0 x Hs HHM Hx)).
    split.
    - apply (fl_asan_cells W' m mc HAC MU). intros x Hx. apply (fl_out_lo W' LO SP0 x Hs). left.
      unfold RT_LO, RT_HI, HIGHMEM_BEG in *. lia.
    - intros p n H. exact (fl_addressable W' m mc p n H MU SHo).
  Qed.

  (* atail_pre on HUW_on: atrF0_on for the asan facts; HUW_on asks for no shadow fact. *)
  Lemma atail_pre_on : forall (u0 u1 u2 x10 x11 x12 x13 x14 u3 u4 u5 u6 : word) (mc : word -> option byte)
                       (j : list byte) (f : Z),
    GO = true -> f = BA_FR + 24 * ba_row b ->
    rw_cells rsegs mc (SP0 + -80) [CB 8 j; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -80) ->
    munch [(SP0 + -80, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evtF rsegs RNG (AT_853c4 u0 u1 u2 u5 u6)
      (MS (mkR ra (Z_to_bv 64 (SP0 + -80)) gp tp u0 u1 u2 (Z_to_bv 64 ns) a6 x10 x11 x12 x13 x14 a5 a6
               (Z_to_bv 64 ns) a5 (Z_to_bv 64 s) (Z_to_bv 64 d) (Z_to_bv 64 md) (Z_to_bv 64 o) (Z_to_bv 64 f)
               s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x85330) fc None mc (seg_rom rsegs)).
  Proof.
    intros u0 u1 u2 x10 x11 x12 x13 x14 u3 u4 u5 u6 mc j f HG -> FR ST MU WM MI.
    pose proof arng_spF as Rsp. pose proof ST as (Rlo & _ & _).
    pose proof HG as HG'. apply andb_true_iff in HG' as [HG1 Hb6]. apply andb_true_iff in HG1 as [Ho0 Hm0].
    apply negb_true_iff, Z.eqb_neq in Ho0. apply negb_true_iff, Z.eqb_neq in Hm0. apply Z.leb_le in Hb6.
    assert (Hb6' : 0 <= b <= 6) by lia.
    destruct (ba_facts b Hb6') as (FK & KR & FBB & FC & FL & FG & FA & F18 & F19 & FAO & FAL).
    destruct (HM Hm0) as (M8 & M296 & ML & HMm & DM).
    pose proof DM as DMu. unfold ly_dj in DMu.
    pose proof (em_obj0 rsegs m mc (SP0 + -80) SP0 md mb 296 MU HMm ltac:(rewrite ML; reflexivity)
                  ltac:(lia)) as HMc.
    pose proof (bm_uw_range md (firstn 8 (skipn 16 mb))) as RN.
    destruct (atrF0_on _ mc MU WM (ain_subF (SP0 + -80) ltac:(lia))) as (AC1 & ADT1).
    (* reac_box_model_upstream_width(m) *)
    step. step.
    eapply evtF_cut.
    { eapply HUW_on with (mp := md) (lo := LO) (bs := firstn 8 (skipn 16 mb)).
      - rewrite unsigned_lit by lia. reflexivity.
      - intros _. split; [lia|]. split.
        + rewrite length_firstn, length_skipn, ML. reflexivity.
        + pose proof (ly_bytes_sub rsegs mc md mb 16 8 HMc ltac:(rewrite ML; lia)) as H16.
          change (Z.of_nat 16) with 16 in H16. exact H16.
      - rewrite unsigned_lit by lia. exact ST.
      - rewrite unsigned_lit by lia. unfold REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME. lia.
      - intros _. rewrite unsigned_lit by lia. unfold REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME. lia.
      - exact AC1.
      - intros _. exact M8.
      - intros _. apply (aaddr_sub mc md 296); [exact (ADT1 _ _ (AM Hm0)) | lia | lia | lia].
      - intros x Hx. rewrite unsigned_lit by lia. unfold REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME.
        cbn [outside]. split; [|exact I].
        unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *. lia.
      - rewrite unsigned_lit by lia. unfold REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME.
        eapply rng_sub; [exact RWIN | lia | lia].
      - exact RGK.
      - exact RCK.
      - intros _. split.
        + eapply rng_sub; [exact (proj1 (RMD Hm0)) | lia | lia].
        + eapply (ba_shcov_byte _ md (md + 295)); [exact (proj2 (RMD Hm0)) | lia | lia | lia]. }
    intros ms' (y1 & y2 & y3 & y4 & mu & -> & MUu & WMu & MIu & STu). afixret.
    rewrite unsigned_lit in MUu, STu by lia. unfold REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME in MUu.
    pose proof (MIu MI) as MI2.
    pose proof (rw_cells_transport rsegs [(SP0 + -80 - 16, SP0 + -80)] mc mu (SP0 + -80) _ FR MUu WMu
                  ltac:(cbn [disjoint_from cells_size csize]; lia)) as FR2.
    (* the arguments, the restores and the jump *)
    do 21 step.
    release_frame FR2 STu (bv_unsigned sp).
    (* the memory at the jump differs from m only inside [LO, SP0) *)
    assert (MUt : munch [(LO, SP0)] m mu).
    { apply (munch_trans _ m mc mu).
      - apply (munch_weaken _ _ m mc (ain_subF (SP0 + -80) ltac:(lia)) MU).
      - apply (munch_weaken _ _ mc mu (ain_subF (SP0 + -80 - 16) ltac:(lia))). eapply munch_weaken; [|exact MUu].
        intros x Hx. cbn [outside] in *. destruct Hx as [H1 _]. split; [lia | exact I]. }
    pose proof (wmono_trans rsegs m mc mu WM WMu) as WMt.
    apply evtF_done. unfold AT_853c4. eexists.
    split; [reflexivity|]. split; [exact MUt|]. split; [exact WMt|]. split; [exact MI2 | exact STu].
  Qed.

  (* atail_jumpF on atail_pre_on. *)
  Lemma atail_jumpF_on : forall (u0 u1 u2 x10 x11 x12 x13 x14 u3 u4 u5 u6 : word) (mc : word -> option byte)
                       (j : list byte) (f : Z),
    GO = true -> f = BA_FR + 24 * ba_row b ->
    rw_cells rsegs mc (SP0 + -80) [CB 8 j; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -80) ->
    munch [(SP0 + -80, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evtF rsegs RNG aJumpF
      (MS (mkR ra (Z_to_bv 64 (SP0 + -80)) gp tp u0 u1 u2 (Z_to_bv 64 ns) a6 x10 x11 x12 x13 x14 a5 a6
               (Z_to_bv 64 ns) a5 (Z_to_bv 64 s) (Z_to_bv 64 d) (Z_to_bv 64 md) (Z_to_bv 64 o) (Z_to_bv 64 f)
               s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x85330) fc None mc (seg_rom rsegs)).
  Proof.
    intros u0 u1 u2 x10 x11 x12 x13 x14 u3 u4 u5 u6 mc j f HG Ef FR ST MU WM MI.
    eapply evtF_cut;
      [ exact (atail_pre_on u0 u1 u2 x10 x11 x12 x13 x14 u3 u4 u5 u6 mc j f HG Ef FR ST MU WM MI) |].
    intros ms' HA. unfold AT_853c4 in HA. destruct HA as (mu & -> & MUt & WMt & MI2 & STu).
    apply evtF_done. unfold aJumpF, CTRL_EMIT_AS.
    do 14 eexists. exists mu.
    split; [reflexivity|].
    do 9 (split; [reflexivity|]).
    split; [exact MUt|]. split; [exact WMt|]. split; [exact MI2 | exact STu].
  Qed.

  (* amain_stretchF on atail_jumpF_on: its script, so the stretch reads neither HSW nor HUW (only HUW_on). *)
  Lemma amain_stretchF_on : forall (t0 t1 t2 t3 t4 t5 t6 : word),
    evtF rsegs RNG aStretchF
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 md) (Z_to_bv 64 b) (Z_to_bv 64 d)
               (Z_to_bv 64 s) a5 a6 (Z_to_bv 64 ns) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8528c) fc None m (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 t3 t4 t5 t6.
    pose proof arng_spF as Rsp.
    pose proof (HST : stk rsegs m (bv_unsigned sp - 4640) (bv_unsigned sp)) as ST. pose proof ST as (Rlo & _ & _).
    pose proof (MI0 : mem_inv rsegs m) as MI.
    pose proof (munch_refl [(bv_unsigned sp + -80, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    (* the literal-address copies of the two runtime cells (the image and image-shadow premises are literal) *)
    pose proof RGK as RGKu. unfold GOT_CELL_K in RGKu.
    pose proof RCK as RCKu. unfold CELL_K in RCKu.
    (* the runtime's cells and the switch table's shadow, apart from the frame *)
    assert (HW : forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
                   outside [(bv_unsigned sp + -80, bv_unsigned sp)] x).
    { intros x Hx. cbn [outside]. split; [|exact I].
      unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *. lia. }
    pose proof (rt_asan_rt m _ HAC HW) as HRT.
    pose proof (rt_shadow_rd m BA_SW 56 _ ASW (fun x Hx => HW x (or_intror (or_intror Hx)))) as HSR.
    pose proof (rt_addressable m BA_SW 56 ASW) as HAD.
    pose proof (rt_rt3 m BA_SW 56 ASW) as H3.
    step. carve_frame 80%nat ST. do 9 step.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    pose proof (asan_rt_munch rsegs m m1 _ _ ASAN_K _ _ HRT MU (fun x Hx => Hx)) as HRT1.
    pose proof (asan_shadow_rd_munch rsegs m m1 ASAN_K BA_SW 56 _ _ HSR MU (fun x Hx => Hx)) as HSR1.
    pose proof (asan_addressable_munch rsegs m m1 ASAN_K BA_SW 56 _ _ HAD HSR MU (fun x Hx => Hx)) as HAD1.
    pose proof (asan_rt3_munch rsegs m m1 ASAN_K BA_SW 56 _ _ H3 HSR MU (fun x Hx => Hx)) as H31.
    (* o = 0 *)
    step. rewrite rc_eqb by lia. destruct (Z.eqb_spec o 0) as [O0|O0]; cbv iota.
    { eapply evtF_cut; [eapply afail_retF; [apply ba_go_false; left; exact O0 | eassumption ..] |
      intros ms' HQ; apply evtF_done; right; split; [apply ba_go_false; left; exact O0 | exact HQ]]. }
    (* m = 0 *)
    step. step. rewrite rc_eqb by lia. destruct (Z.eqb_spec md 0) as [M0|M0]; cbv iota.
    { eapply evtF_cut; [eapply afail_retF; [apply ba_go_false; right; left; exact M0 | eassumption ..] |
      intros ms' HQ; apply evtF_done; right; split; [apply ba_go_false; right; left; exact M0 | exact HQ]]. }
    (* b > 6 *)
    step. step. step. rewrite rc_ltu by lia. destruct (Z.ltb_spec 6 b) as [B6|B6]; cbv iota.
    { eapply evtF_cut; [eapply afail_retF; [apply ba_go_false; right; right; exact B6 | eassumption ..] |
      intros ms' HQ; apply evtF_done; right; split; [apply ba_go_false; right; right; exact B6 | exact HQ]]. }
    assert (HG : GO = true) by (apply ba_go_true; assumption).
    (* the shadow byte of the table word b is 0 *)
    destruct (asan_shadow_read_at rsegs m1 ASAN_K BA_SW 56 _ (8 * b) ((BA_SW + 8 * b) / 8 + ASAN_K) HSR1
                ltac:(lia) eq_refl) as (k & RK & BK).
    pose proof (asan_check_8 rsegs m1 ASAN_K BA_SW 56 (8 * b) k HAD1 H31 ltac:(lia) ltac:(lia)
                  ltac:(unfold BA_SW; lia) BK) as K0.
    pose proof (rc_signed0_unsigned0 k K0) as K0u.
    pose proof (asan_rt_got_read rsegs m1 _ _ ASAN_K _ HRT1) as RG.
    pose proof (asan_rt_cell_read rsegs m1 _ _ ASAN_K _ HRT1) as RC.
    unfold GOT_CELL_K, CELL_K in RG, RC.
    assert (RSHSW : rng RNG (17200 + ASAN_K) 7)
      by (eapply rng_sub; [exact RISH | unfold ASAN_K; lia | unfold ASAN_K; lia]).
    (* row(b) from the table, f = CTRL_FRAMES + 24 row(b), and the pointer check (0x85314: ~f0 < 24 row(b) traps;
       f0 = CTRL_FRAMES, so it does not) *)
    destruct (ba_cases b ltac:(lia)) as [Eb|[Eb|[Eb|[Eb|[Eb|[Eb|Eb]]]]]]; rewrite Eb in RK |- *;
      unfold BA_SW, ASAN_K in RK;
      do 11 step;
      rewrite (rcl_zxb_eqb k 0) by lia; rewrite K0u; cbn [Z.eqb negb];
      do 8 step;
      match goal with |- context [bv_ltu ?x ?y] => replace (bv_ltu x y) with false by (vm_compute; reflexivity) end;
      cbv iota;
      do 6 step;
      (eapply evtF_cut;
        [ eapply atail_jumpF_on; [exact HG | rewrite Eb; reflexivity | eassumption ..]
        | intros ms' HJ; apply evtF_done; left; split; [exact HG | exact HJ] ]).
  Qed.
End BuildF.

Theorem reac_ctrl_build_as_F_holds :
  ctrl_emit_as_contract_F -> reac_box_model_upstream_width_contract_F -> reac_ctrl_build_as_contract_F.
Proof.
  intros HEA HUW. unfold reac_ctrl_build_as_contract_F, REAC_CTRL_BUILD_AS, REAC_CTRL_BUILD_AS_K.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m o md b d s ns FS mb nb db sb junk.
  cbv zeta.
  intros Ha0 Ha1 Ha2 Ha3 Ha4 -> Hns HS16 HST HT DsT Hdb HD Dsd Hsb HSb Dss HM HN Ho1492 HEo MI0
    HAC HSW HHM HAE AWIN ASW ATB AD AS APD APS AM AN AO AJ14 AJ13 FP FPN FPT
    RRB RIMG RISH RWIN RWSH RGK RCK RFS RFSS RTLS RMD RDD RDS RSD RSS RNB ROO.
  pose proof (rc_word_range a0 o Ha0) as Ro. apply rc_word in Ha0. subst a0.
  pose proof (rc_word_range a1 md Ha1) as Rmd. apply rc_word in Ha1. subst a1.
  pose proof (rc_word_range a2 b Ha2) as Rb. apply rc_word in Ha2. subst a2.
  apply rc_word in Ha3. subst a3.
  apply rc_word in Ha4. subst a4.
  eapply amainF; eassumption.
Qed.

(* RECIPE step 1: the old theorem's statement, back from the footprint form at ExecF.RNG_all, from the same two
   callee contracts (in footprint form) as the old theorem. *)
Theorem reac_ctrl_build_as_holds_of_F :
  ctrl_emit_as_contract_F -> reac_box_model_upstream_width_contract_F -> reac_ctrl_build_as_contract.
Proof.
  intros HEA HUW. exact (reac_ctrl_build_as_contract_of_F (reac_ctrl_build_as_F_holds HEA HUW)).
Qed.

(* The LIFTED STRETCH for the cgif-form glue (the B twin of image A's Theorem Labs lane block): the run from entry to the
   tail jump (ctrl_emit_as's entry 0x853c4, the registers its contract reads, a memory that differs from m only
   inside [Lo, S)) when the arguments pass the checks, else to the return of 0 (a memory that differs from m only
   inside the 80-byte frame).  No ctrl_emit_as premise: ctrl_emit_as contains a fake-stack event (through
   ctrl_lay_block), so the glue applies it at this cut by its cgif spec.  reac_box_model_upstream_width (a leaf,
   no event) stays inside, on its _F contract.  Premises: exactly those amain_stretchF uses -- its frame, the
   switch table's shadow, the model at md, the asan cells and the image / image-shadow / GOT / CELL_K footprint;
   the side stack, the thread cells and o / d / s / the name are ctrl_emit_as's accesses and are not premises
   here. *)
Definition reac_ctrl_build_as_stretch_F : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o md b d s ns : Z) (mb db sb : list byte),
    let S := bv_unsigned sp in
    let Lo := S - REAC_CTRL_BUILD_AS_K in
    let n := bm_uw md (firstn 8 (skipn 16 mb)) in
    let go := ba_go o md b in
    bv_unsigned a0 = o -> bv_unsigned a1 = md -> bv_unsigned a2 = b -> bv_unsigned a3 = d -> bv_unsigned a4 = s ->
    a7 = Z_to_bv 64 ns ->
    stk rsegs m Lo S ->
    length db = 6%nat -> length sb = 6%nat ->
    (md <> 0 -> md mod 8 = 0 /\ md + 296 <= 2^64 /\ length mb = 296%nat /\ bytes_at rsegs m md mb /\
                ly_dj Lo S md (md + 296)) ->
    mem_inv rsegs m ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= Lo -> addressable m BA_SW 56 -> (md <> 0 -> addressable m md 296) ->
    rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    (* the shadow of that span, in the literal form reac_ctrl_build_as_c.v:182 publishes
       (0x7fffa000 = shadow_addr IMG_LO, 0xbdc00 = (IMG_HI - IMG_LO) / 8) *)
    rng RNG 0x7fffa000 0xbdc00 ->
    rng RNG Lo REAC_CTRL_BUILD_AS_K ->
    rng RNG GOT_CELL_K 8 -> rng RNG CELL_K 8 ->
    (md <> 0 -> rng RNG md 296 /\
       rng RNG (shadow_addr md / 8 * 8) (shadow_addr (md + 295) / 8 * 8 + 8 - shadow_addr md / 8 * 8)) ->
    evtF rsegs RNG
      (fun ms' =>
         (go = true /\ (exists (t0' t1' t2' a0' a1' a2' a3' a4' a6' a7' t3' t4' t5' t6' : word)
                               (mu : word -> option byte),
            ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5 a6' a7'
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (Z_to_bv 64 CTRL_EMIT_AS) fc None mu (seg_rom rsegs)
            /\ a0' = Z_to_bv 64 o /\ a1' = Z_to_bv 64 (BA_FR + 24 * ba_row b) /\ a2' = Z_to_bv 64 md
            /\ a3' = Z_to_bv 64 d /\ a4' = Z_to_bv 64 s /\ a6' = Z_to_bv 64 n /\ a7' = Z_to_bv 64 0
            /\ t3' = a6 /\ t4' = Z_to_bv 64 ns
            /\ munch [(Lo, S)] m mu /\ wmono rsegs m mu /\ mem_inv rsegs mu /\ stk rsegs mu Lo S))
         \/
         (go = false /\ (exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                                (m' : word -> option byte),
            ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0)
                          a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (ret_pc ra) fc None m' (seg_rom rsegs)
            /\ munch [(S - 80, S)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' Lo S)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_BUILD_AS) fc None m (seg_rom rsegs)).

Theorem reac_ctrl_build_as_stretch_F_holds :
  reac_box_model_upstream_width_contract_F -> reac_ctrl_build_as_stretch_F.
Proof.
  intros HUW. unfold reac_ctrl_build_as_stretch_F, REAC_CTRL_BUILD_AS, REAC_CTRL_BUILD_AS_K.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m o md b d s ns mb db sb.
  cbv zeta.
  intros Ha0 Ha1 Ha2 Ha3 Ha4 -> HST Hdb Hsb HM MI0 HAC HSW HHM ASW AM RIMG RISH RWIN RGK RCK RMD.
  cbv [IMG_LO IMG_HI] in RIMG. change (0x5fe000 - 0x10000) with 0x5ee000 in RIMG.
  pose proof (rc_word_range a0 o Ha0) as Ro. apply rc_word in Ha0. subst a0.
  pose proof (rc_word_range a1 md Ha1) as Rmd. apply rc_word in Ha1. subst a1.
  pose proof (rc_word_range a2 b Ha2) as Rb. apply rc_word in Ha2. subst a2.
  apply rc_word in Ha3. subst a3.
  apply rc_word in Ha4. subst a4.
  (* the Section states the three memory facts through RcEmitLib's wrappers *)
  try fold em_stk in HST. try fold em_at in HM. try fold em_mi in MI0.
  eapply amain_stretchF; eassumption.
Qed.

(* Route (C) (a Theorem Labs lane 2026-10-29 09:20Z): the lifted stretch without the universal shadow premise.
   reac_ctrl_build_as_stretch_F_on is reac_ctrl_build_as_stretch_F with ONE change: the premise `shadow_rw m` is
   dropped (`asan_cells m` stays).  a Theorem Labs lane measured (11:26Z) that the stretch used `shadow_rw m` only to feed
   reac_box_model_upstream_width's contract, whose proof never uses it.  reac_ctrl_build_as_stretch_F_holds_on proves
   the new statement from that callee's premise-free contract reac_box_model_upstream_width_contract_F_on
   (lib/B/Prog/reac_box_model_upstream_width_c.v, no shadow premise) by amain_stretchF_on, so no shadow premise is
   left.  reac_ctrl_build_as_stretch_F_of_on gives the old statement back.  The old names
   (reac_ctrl_build_as_stretch_F, reac_ctrl_build_as_stretch_F_holds, and the section's atrF0, atail_pre,
   atail_jumpF, amain_stretchF) are byte-identical.  rule 24: no function proved (the narrowed twin of the stretch
   proved above). *)
Definition reac_ctrl_build_as_stretch_F_on : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o md b d s ns : Z) (mb db sb : list byte),
    let S := bv_unsigned sp in
    let Lo := S - REAC_CTRL_BUILD_AS_K in
    let n := bm_uw md (firstn 8 (skipn 16 mb)) in
    let go := ba_go o md b in
    bv_unsigned a0 = o -> bv_unsigned a1 = md -> bv_unsigned a2 = b -> bv_unsigned a3 = d -> bv_unsigned a4 = s ->
    a7 = Z_to_bv 64 ns ->
    stk rsegs m Lo S ->
    length db = 6%nat -> length sb = 6%nat ->
    (md <> 0 -> md mod 8 = 0 /\ md + 296 <= 2^64 /\ length mb = 296%nat /\ bytes_at rsegs m md mb /\
                ly_dj Lo S md (md + 296)) ->
    mem_inv rsegs m ->
    asan_cells m ->
    HIGHMEM_BEG <= Lo -> addressable m BA_SW 56 -> (md <> 0 -> addressable m md 296) ->
    rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    (* the shadow of that span, in the literal form reac_ctrl_build_as_c.v:182 publishes
       (0x7fffa000 = shadow_addr IMG_LO, 0xbdc00 = (IMG_HI - IMG_LO) / 8) *)
    rng RNG 0x7fffa000 0xbdc00 ->
    rng RNG Lo REAC_CTRL_BUILD_AS_K ->
    rng RNG GOT_CELL_K 8 -> rng RNG CELL_K 8 ->
    (md <> 0 -> rng RNG md 296 /\
       rng RNG (shadow_addr md / 8 * 8) (shadow_addr (md + 295) / 8 * 8 + 8 - shadow_addr md / 8 * 8)) ->
    evtF rsegs RNG
      (fun ms' =>
         (go = true /\ (exists (t0' t1' t2' a0' a1' a2' a3' a4' a6' a7' t3' t4' t5' t6' : word)
                               (mu : word -> option byte),
            ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5 a6' a7'
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (Z_to_bv 64 CTRL_EMIT_AS) fc None mu (seg_rom rsegs)
            /\ a0' = Z_to_bv 64 o /\ a1' = Z_to_bv 64 (BA_FR + 24 * ba_row b) /\ a2' = Z_to_bv 64 md
            /\ a3' = Z_to_bv 64 d /\ a4' = Z_to_bv 64 s /\ a6' = Z_to_bv 64 n /\ a7' = Z_to_bv 64 0
            /\ t3' = a6 /\ t4' = Z_to_bv 64 ns
            /\ munch [(Lo, S)] m mu /\ wmono rsegs m mu /\ mem_inv rsegs mu /\ stk rsegs mu Lo S))
         \/
         (go = false /\ (exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                                (m' : word -> option byte),
            ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0)
                          a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (ret_pc ra) fc None m' (seg_rom rsegs)
            /\ munch [(S - 80, S)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' Lo S)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_BUILD_AS) fc None m (seg_rom rsegs)).

Theorem reac_ctrl_build_as_stretch_F_holds_on :
  reac_box_model_upstream_width_contract_F_on -> reac_ctrl_build_as_stretch_F_on.
Proof.
  intros HUW_on. unfold reac_ctrl_build_as_stretch_F_on, REAC_CTRL_BUILD_AS, REAC_CTRL_BUILD_AS_K.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m o md b d s ns mb db sb.
  cbv zeta.
  intros Ha0 Ha1 Ha2 Ha3 Ha4 -> HST Hdb Hsb HM MI0 HAC HHM ASW AM RIMG RISH RWIN RGK RCK RMD.
  cbv [IMG_LO IMG_HI] in RIMG. change (0x5fe000 - 0x10000) with 0x5ee000 in RIMG.
  pose proof (rc_word_range a0 o Ha0) as Ro. apply rc_word in Ha0. subst a0.
  pose proof (rc_word_range a1 md Ha1) as Rmd. apply rc_word in Ha1. subst a1.
  pose proof (rc_word_range a2 b Ha2) as Rb. apply rc_word in Ha2. subst a2.
  apply rc_word in Ha3. subst a3.
  apply rc_word in Ha4. subst a4.
  (* the Section states the three memory facts through RcEmitLib's wrappers *)
  try fold em_stk in HST. try fold em_at in HM. try fold em_mi in MI0.
  eapply amain_stretchF_on; eassumption.
Qed.

(* The old statement from the new one: the old premise `shadow_rw m` is dropped. *)
Lemma reac_ctrl_build_as_stretch_F_of_on : reac_ctrl_build_as_stretch_F_on -> reac_ctrl_build_as_stretch_F.
Proof.
  intros H. unfold reac_ctrl_build_as_stretch_F.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m o md b d s ns mb db sb.
  cbv zeta.
  intros Ha0 Ha1 Ha2 Ha3 Ha4 Ha7 HST Hdb Hsb HM MI0 HAC HSW HHM ASW AM RIMG RISH RWIN RGK RCK RMD.
  exact (H RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m o md b d s ns mb db sb Ha0 Ha1 Ha2 Ha3 Ha4 Ha7 HST Hdb Hsb HM MI0 HAC HHM ASW AM RIMG RISH RWIN
           RGK RCK RMD).
Qed.

Locate OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_build_asF.reac_ctrl_build_as_stretch_F_on.
Print Assumptions OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_build_asF.reac_ctrl_build_as_stretch_F_on.
Locate OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_build_asF.reac_ctrl_build_as_stretch_F_holds_on.
Print Assumptions OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_build_asF.reac_ctrl_build_as_stretch_F_holds_on.
Locate OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_build_asF.reac_ctrl_build_as_stretch_F_of_on.
Print Assumptions OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_build_asF.reac_ctrl_build_as_stretch_F_of_on.
Locate OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_build_asF.amain_stretchF_on.
Print Assumptions OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_build_asF.amain_stretchF_on.
