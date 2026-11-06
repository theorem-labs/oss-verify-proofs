(* The footprint twin of reac_ctrl_build_as.v (image A; RECIPE.md steps 1-2 (a working note, not in this delivery)): the same run as an
   ExecF.evtF under a footprint RNG, by the script of reac_ctrl_build_as.v over StepF's step. Every access of this
   run closes from one rng premise of reac_ctrl_build_as_contract_F: the frame stores and loads of the 80-byte
   frame (inside the window), the two 8-byte loads of the GOT cell and of the runtime cell that hold the shadow
   offset, the 8-byte load of the switch-table word at BA_SW + 8 b and the 1-byte load of its shadow byte (both
   inside the image and the image-shadow ranges).
   The two callees are taken as hypotheses in the same place as the old theorem takes their plain contracts, here
   in footprint form: reac_box_model_upstream_width_contract_F (published by its owner in
   reac_box_model_upstream_width_c.v) and ctrl_emit_as_contract_F, the FINAL text its owner a Theorem Labs lane published
   for image A in lib/A/Prog/ctrl_emit_as_c.v (imported below), with ctrl_emit_as_contract_of_F, the machine check
   that the hypothesis asks for nothing ctrl_emit_as_contract lacks.
   reac_ctrl_build_as.v and its theorem are unchanged (the halts proofs use them).
   PER-MEMORY TLS FOOTPRINT (a Theorem Labs lane, 2026-10-28; route (a), a Theorem Labs lane's segF-rerun-recipe.md (a working note, not in this delivery)): the thread-cell
   premise of reac_ctrl_build_as_contract_F (and the Section hypothesis RTLS) is stated over THIS run's memory m,
   not `forall mm` (a Theorem Labs lane's premise check, signature #1: the `forall mm` form holds only for an
   everything-footprint, so no RNG_W (w_H W) satisfies it). Proof change: the tail jump discharges ctrl_emit_as's
   per-memory ctrl_emit_as_rtls at the jump memory mu by ba_rtls_W (the text of RcAsanFPLib.fl_tls_W with rng in
   place of fp_dj); nothing else. No new proof obligation.
   LEMMA BOUNDARY AT THE TAIL JUMP (a Theorem Labs lane; a Theorem Labs lane 22:56Z: the bridge lifts only silent runs, and
   ctrl_emit_as reaches __asan_stack_malloc_1 through ctrl_lay_block): the old atailF is split at the jump into
   atail_jumpF (to the jump state aJumpF) and aemitF (ctrl_emit_as's contract from aJumpF), each the old script's
   own lines; amain_stretchF is amainF's script with the jump arm ended at aJumpF and the refusals at aRet0F (no
   asan / side-stack conjunct, so the stretch needs only the premises it reads); amainF, reac_ctrl_build_as_F_holds
   and reac_ctrl_build_as_holds_of_F keep their statements. The glue lifts reac_ctrl_build_as_stretch_F_holds
   (the 21 premises amain_stretchF uses, post = the jump state or the return of 0; no ctrl_emit_as premise).
   PROVENANCE: source proved run a working branch d69f7c708f6 (lib/A/Prog/reac_ctrl_build_as{,_c,F}.v);
   image root (internal path), ELF sha256
   aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (= FACTS ed6b6b7b0ab index/binaries.tsv (a working note, not in this delivery));
   symbols from the unstripped twin (internal path) (same PT_LOADs); tool:
   none (the script re-run over lib/Lib/StepF, no relocation); compare:
   basf_consts.py, 10 checks OK (REAC_CTRL_BUILD_AS, BA_SW and its 7
   words = ba_row, BA_FR rows 3..9 = ba_tbl, CELL_K, the GOT_CELL_K slot's content, the shadow numeral 17200). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcPorts RcPortsLib RcBox RcSynth RcLay
  RcLayLib RcFin RcEmit RcEmitLib RcAsan RcAsanLib RcLeafLib reac_ctrl_build_as_c reac_ctrl_build_as.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT asan_stack_malloc_c RcAsanFP RcAsanFPLib
  ctrl_emit_as_c reac_box_model_upstream_width_c reac_ctrl_build_as_c reac_box_model_block_c reac_ctrl_build_as.
(* Last: StepF's step / if_cases (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF RngBytes StepF.
(* route (C): the callee's CLOSED _on theorem, so the old-name theorems below keep their statements. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_box_model_upstream_widthF.
(* route (C): the region transport across a munch outside the shadow (fl_shadow_rw_on), for the _on lemmas below. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOnK.
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

(* The thread cells' footprint premise survives writes inside fp's W: the proof text of RcAsanFPLib.fl_tls_W with
   rng in place of fp_dj (fl_cols gives the cells outside the writes, fl_tls_same that the pointers read from them
   are those of m, so the cells are m's).  Used once, at the tail jump, to state the TLS footprint per memory. *)
Lemma ba_rtls_W : forall cs m m' TP FS lo hi W D W' (RNG : footprint),
  fp cs m TP FS lo hi W D -> munch W' m m' -> sub_fp W' W ->
  (forall DT TS C T DB k, asan_tls_cells m TP DT TS C T DB k ->
     Forall (fun r => rng RNG (fst r) (snd r - fst r)) (fp_tls TP DT TS C T DB k)) ->
  forall DT TS C T DB k, asan_tls_cells m' TP DT TS C T DB k ->
     Forall (fun r => rng RNG (fst r) (snd r - fst r)) (fp_tls TP DT TS C T DB k).
Proof.
  intros cs m m' TP FS lo hi W D W' RNG (DT0 & TS0 & C0 & T0 & DB0 & k0 & HT0 & _ & _ & _ & _ & _ & _ & _ & HWd & _)
    Hm Hs Htls DT TS C T DB k HT.
  pose proof (fl_cols W W' _ HWd Hs) as Hc. apply Forall_app in Hc as [Hc _].
  destruct (fl_tls_same m m' W' TP DT0 TS0 C0 T0 DB0 k0 DT TS C T DB k HT0 HT Hm Hc) as (E1 & E2 & E3 & E4 & E5 & E6).
  subst DT0 TS0 C0 T0 DB0 k0. exact (Htls DT TS C T DB k HT0).
Qed.

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
  Local Abbreviation DD := [(lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 72, lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 240); (md, md + 296); (d, d + 6); (s, s + 6);
                            (o, o + (if ba_go o md b && ba_E (bm_uw md (firstn 8 (skipn 16 mb))) mb b
                                     then 52 + 36 * bm_uw md (firstn 8 (skipn 16 mb)) else 0))].

  Hypothesis HEA : ctrl_emit_as_contract_F.
  (* route (C): the callee on its _on twin; used only by the _on lemmas (aemitF_on), so the old lemmas keep their
     generalized types. *)
  Hypothesis HEA_on : ctrl_emit_as_contract_F_on.
  (* route (C): the callee on its _on twin (no shadow_rw premise), so the stretch reads no shadow_rw. *)
  Hypothesis HUW : reac_box_model_upstream_width_contract_F_on.
  Hypothesis Ho : 0 <= o < 2^64.
  Hypothesis Hmd : 0 <= md < 2^64.
  Hypothesis Hb : 0 <= b < 2^64.
  Hypothesis Hns : -2^31 <= ns <= 0.
  Hypothesis HS16 : SP0 mod 16 = 0.
  Hypothesis HST : em_stk rsegs m LO SP0.
  Hypothesis HT : em_at rsegs m (lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 72) ba_tbl.
  Hypothesis DsT : ly_dj LO SP0 (lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 72) (lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 240).
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
       ly_dj o (o + LEN) (lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 72) (lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 240) /\ ly_dj o (o + LEN) md (md + 296) /\
       (NM -> ly_dj o (o + LEN) (rname mb) (rname mb + Z.of_nat (length nb))) /\
       ly_dj o (o + LEN) d (d + 6) /\ ly_dj o (o + LEN) s (s + 6).
  Hypothesis MI0 : em_mi rsegs m.
  Hypothesis HAC : asan_cells m.
  Hypothesis HSW : shadow_rw m.
  (* route (C): the region premise of reac_ctrl_build_as_contract_F_on (ctrl_emit_as's region at the tail jump);
     used only by the _on lemmas (aemitF_on). *)
  Hypothesis HSW_on : A.ShadowRwOn.shadow_rw_on
    (lib.A.Prog.reac_ctrl_build_as_c.reac_ctrl_build_as_shadow_R SP0 FS o md d s b mb nb) m.
  Hypothesis HHM : HIGHMEM_BEG <= LO.
  Hypothesis HAE : SP0 <= APPMEM_END.
  Hypothesis AWIN : addressable m LO 4640.
  Hypothesis ASW : addressable m BA_SW 56.
  Hypothesis ATB : addressable m (lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 72) 168.
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
  (* per memory: the thread cells of THIS run's memory m (a Theorem Labs lane's signature #1 removed the `forall mm` form) *)
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


  (* The jump state (a Theorem Labs lane, route (a) lemma boundary at the tail jump; a Theorem Labs lane 22:56Z): the machine at
     ctrl_emit_as's entry 0x849d8, after the frame pop at 0x8499c and the jump at 0x849a0, with the eight
     argument registers ctrl_emit_as's
     contract reads (a0 = o, a1 = f, a2 = md, a3 = d, a4 = s, a6 = n, a7 = g = 0, t4 = ns), ra, sp, gp, tp, s0..s11
     and a5 as at entry, and a memory that differs from m only inside [LO, SP0).  The lifted stretch ends here;
     ctrl_emit_as (which reaches the fake-stack allocator through ctrl_lay_block) is applied at this cut. *)
  Definition aJumpF (ms' : machine_state) : Prop :=
    exists (t0' t1' t2' a0' a1' a2' a3' a4' a6' a7' t3' t4' t5' t6' : word) (mu : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5 a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 CTRL_EMIT_AS) fc None mu (seg_rom rsegs)
      /\ a0' = Z_to_bv 64 o /\ a1' = Z_to_bv 64 (lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 24 * ba_row b) /\ a2' = Z_to_bv 64 md
      /\ a3' = Z_to_bv 64 d /\ a4' = Z_to_bv 64 s /\ a6' = Z_to_bv 64 NN /\ a7' = Z_to_bv 64 0
      /\ t4' = Z_to_bv 64 ns
      /\ munch [(LO, SP0)] m mu /\ wmono rsegs m mu /\ mem_inv rsegs mu /\ stk rsegs mu LO SP0.

  (* The stretch's return of 0 (a Theorem Labs lane, 2026-10-29; two Theorem Labs lanes 00:12Z: the stretch owes only what
     it reads): the return state with a0 = 0, a memory that differs from m only inside the 80-byte frame, wmono,
     mem_inv and the stack window. No asan or side-stack conjunct (the caller's memory facts follow from munch). *)
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

  Lemma arng_spF : 4640 <= SP0 < 2^64.
  Proof. pose proof (zr_word sp) as R. unfold inr64 in R. destruct HST as (H1 & _). lia. Qed.

  Lemma aframe_subF : forall X, sub_fp [(SP0 + -80, SP0)] ((LO, SP0) :: X).
  Proof. intros X x Hx. cbn [outside] in *. destruct Hx as [H1 _]. split; [lia | exact I]. Qed.

  Lemma ain_subF : forall lo', LO <= lo' -> sub_fp [(lo', SP0)] [(LO, SP0)].
  Proof. intros lo' H x Hx. cbn [outside] in *. destruct Hx as [H1 _]. split; [lia | exact I]. Qed.

  (* The asan facts in a memory that differs from m only inside [LO, SP0) (no side-stack premise: atrF0 is what
     the stretch uses; atrF adds fp for the whole-function proof). *)
  (* route (C): the asan facts without shadow_rw (what the stretch's callee needs now). *)
  Lemma atrF0n : forall W' mc, munch W' m mc -> wmono rsegs m mc -> sub_fp W' [(LO, SP0)] ->
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

  Lemma atrF : forall W' mc, munch W' m mc -> wmono rsegs m mc -> sub_fp W' [(LO, SP0)] ->
    asan_cells mc /\ shadow_rw mc /\ fp [0%nat; 1%nat] mc (bv_unsigned tp) FS LO SP0 WW DD /\
    (forall p n, addressable m p n -> addressable mc p n).
  Proof.
    intros W' mc MU WM Hs.
    destruct (atrF0 W' mc MU WM Hs) as (AC0 & SW0 & AD0).
    split; [exact AC0|]. split; [exact SW0|]. split; [|exact AD0].
    exact (fl_fp _ m mc (bv_unsigned tp) FS LO SP0 _ DD W' FP MU WM Hs).
  Qed.

  (* 0x849a4: a refusal returns 0. *)
  Lemma afailF : forall (x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                       u3 u4 u5 u6 : word) (mc : word -> option byte) (j : list byte),
    GO = false ->
    rw_cells rsegs mc (SP0 + -80) [CB 8 j; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -80) ->
    munch [(SP0 + -80, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evtF rsegs RNG aQbF
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -80)) gp tp u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
               x22 x23 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x849a4) fc None mc (seg_rom rsegs)).
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

  (* 0x849a4, for the stretch: afailF's script with the asan and side-stack conjuncts left out (aRet0F). *)
  Lemma afail_retF : forall (x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                       u3 u4 u5 u6 : word) (mc : word -> option byte) (j : list byte),
    GO = false ->
    rw_cells rsegs mc (SP0 + -80) [CB 8 j; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -80) ->
    munch [(SP0 + -80, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evtF rsegs RNG aRet0F
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -80)) gp tp u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
               x22 x23 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x849a4) fc None mc (seg_rom rsegs)).
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

  (* 0x84948 .. 0x849a0: the width (reac_box_model_upstream_width on its footprint contract, a leaf with no
     fake-stack event, inside the stretch), the frame pop (0x8499c), and the tail jump (0x849a0): ends at
     ctrl_emit_as's entry. *)
  Lemma atail_jumpF : forall (u0 u1 u2 x10 x11 x12 x13 x14 u3 u4 u5 u6 : word) (mc : word -> option byte)
                       (j : list byte) (f : Z),
    GO = true -> f = lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 24 * ba_row b ->
    rw_cells rsegs mc (SP0 + -80) [CB 8 j; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -80) ->
    munch [(SP0 + -80, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evtF rsegs RNG aJumpF
      (MS (mkR ra (Z_to_bv 64 (SP0 + -80)) gp tp u0 u1 u2 (Z_to_bv 64 ns) a6 x10 x11 x12 x13 x14 a5 a6
               (Z_to_bv 64 ns) a5 (Z_to_bv 64 s) (Z_to_bv 64 d) (Z_to_bv 64 md) (Z_to_bv 64 o) (Z_to_bv 64 f)
               s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x84948) fc None mc (seg_rom rsegs)).
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
    destruct (atrF0n _ mc MU WM (ain_subF (SP0 + -80) ltac:(lia))) as (AC1 & ADT1).
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
    apply evtF_done. unfold aJumpF.
    do 14 eexists. exists mu.
    split; [reflexivity|].
    do 8 (split; [reflexivity|]).
    split; [exact MUt|]. split; [exact WMt|]. split; [exact MI2|]. exact STu.
  Qed.

  (* ctrl_emit_as from the jump state (the script of the old atailF after the jump, unchanged): its footprint
     contract, then the return through ra. *)
  Lemma aemitF : forall ms', GO = true -> aJumpF ms' -> evtF rsegs RNG aQbF ms'.
  Proof.
    intros ms' HG (jt0 & jt1 & jt2 & ja0 & ja1 & ja2 & ja3 & ja4 & ja6 & ja7 & jt3 & jt4 & jt5 & jt6 & mu & -> &
                   E0 & E1 & E2 & E3 & E4 & E6 & E7 & E9 & MUt & WMt & MI2 & STu).
    subst ja0 ja1 ja2 ja3 ja4 ja6 ja7 jt4.
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
                  (em_obj0 rsegs m mu LO SP0 (lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 72) ba_tbl 168 MUt HT ltac:(vm_compute; reflexivity)
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
    assert (DJf : fp_dj [(lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 24 * ba_row b, lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 24 * ba_row b + 24)] (fp_w [0%nat; 1%nat] FS))
      by (apply (fl_dj_sub _ _ _ _ _ DJT); lia).
    assert (AF : addressable mu (lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 24 * ba_row b) 24)
      by (apply (aaddr_sub mu (lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 72) 168); [exact (ADT2 _ _ ATB) | lia | lia | lia]).
    pose proof HEA as HE. unfold ctrl_emit_as_contract_F, CTRL_EMIT_AS_K in HE. cbv zeta in HE.
    eapply evtF_cut.
    { eapply HE with (o := o) (f := lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 24 * ba_row b) (md := md) (d := d) (s := s) (g := 0) (n := NN)
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
      - unfold lib.A.Prog.reac_ctrl_build_as_c.BA_FR. lia.
      - unfold lib.A.Prog.reac_ctrl_build_as_c.BA_FR. lia.
      - unfold lib.A.Prog.reac_ctrl_build_as_c.BA_FR. lia.
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
      - exact RIMG.
      - exact RWIN.
      - exact RWSH.
      - exact RFS.
      - exact RFSS.
      - unfold ctrl_emit_as_rtls.
        refine (ba_rtls_W _ m mu _ FS _ _ _ _ _ RNG FP MUt _ RTLS).
        intros x Hx. cbn [outside app] in *. destruct Hx as [H1 _]. split; [exact H1 | exact I].
      - eapply rng_sub; [exact RIMG | unfold lib.A.Prog.reac_ctrl_build_as_c.BA_FR; lia | unfold lib.A.Prog.reac_ctrl_build_as_c.BA_FR; lia].
      - apply ba_shcov_img; [exact RISH | unfold lib.A.Prog.reac_ctrl_build_as_c.BA_FR; lia | lia | unfold lib.A.Prog.reac_ctrl_build_as_c.BA_FR; lia].
      - exact (proj1 (RMD Hm0)).
      - exact (proj2 (RMD Hm0)).
      - exact RDD.
      - exact RDS.
      - exact RSD.
      - exact RSS.
      - intros K2. exfalso. rewrite FK in K2. lia.
      - apply NMc. intros NMx. exact (RNB Hm0 NMx).
      - intros G0. exfalso. exact (G0 eq_refl).
      - rewrite (ba_E_eq b NN mb Hb6'), (ba_len_eq b NN Hb6'). intros E1.
        assert (GE : GO && EE = true) by (rewrite HG; exact E1).
        exact (ROO GE).
      (* the shadow covers of the two JOIN blocks: inside the image, so inside the image-shadow range *)
      - intros _. apply ba_shcov_img; [exact RISH | unfold JOIN_0014; lia | lia | unfold JOIN_0014; lia].
      - intros _. apply ba_shcov_img; [exact RISH | unfold JOIN_0013; lia | lia | unfold JOIN_0013; lia]. }
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


  (* The lifted stretch [entry, tail jump) (or the return of 0): amainF's script with the jump arm ended at
     aJumpF. *)
  Lemma amain_stretchF : forall (t0 t1 t2 t3 t4 t5 t6 : word),
    evtF rsegs RNG aStretchF
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 md) (Z_to_bv 64 b) (Z_to_bv 64 d)
               (Z_to_bv 64 s) a5 a6 (Z_to_bv 64 ns) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x848ac) fc None m (seg_rom rsegs)).
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
    (* the shadow bytes of the seven table words, in the shape the check computes them: the address is
       (BA_SW + 8 b) >> 3 + ASAN_K, and ASAN_K comes from the runtime cell, so it stays a constant. *)
    assert (RSHSW : rng RNG (17200 + ASAN_K) 7)
      by (eapply rng_sub; [exact RISH | unfold ASAN_K; lia | unfold ASAN_K; lia]).
    (* row(b) from the table and f = CTRL_FRAMES + 24 row(b) *)
    destruct (ba_cases b ltac:(lia)) as [Eb|[Eb|[Eb|[Eb|[Eb|[Eb|Eb]]]]]]; rewrite Eb in RK |- *;
      unfold BA_SW, ASAN_K in RK;
      do 11 step;
      rewrite (rcl_zxb_eqb k 0) by lia; rewrite K0u; cbn [Z.eqb negb];
      do 12 step;
      (eapply evtF_cut; [eapply atail_jumpF; [exact HG | rewrite Eb; reflexivity | eassumption ..] |
       intros ms' HJ; apply evtF_done; left; split; [exact HG | exact HJ]]).
  Qed.

  Lemma amainF : forall (t0 t1 t2 t3 t4 t5 t6 : word),
    evtF rsegs RNG aQbF
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 md) (Z_to_bv 64 b) (Z_to_bv 64 d)
               (Z_to_bv 64 s) a5 a6 (Z_to_bv 64 ns) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x848ac) fc None m (seg_rom rsegs)).
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
    { eapply afailF; [apply ba_go_false; left; exact O0 | eassumption ..]. }
    (* m = 0 *)
    step. step. rewrite rc_eqb by lia. destruct (Z.eqb_spec md 0) as [M0|M0]; cbv iota.
    { eapply afailF; [apply ba_go_false; right; left; exact M0 | eassumption ..]. }
    (* b > 6 *)
    step. step. step. rewrite rc_ltu by lia. destruct (Z.ltb_spec 6 b) as [B6|B6]; cbv iota.
    { eapply afailF; [apply ba_go_false; right; right; exact B6 | eassumption ..]. }
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
    (* row(b) from the table and f = CTRL_FRAMES + 24 row(b) *)
    destruct (ba_cases b ltac:(lia)) as [Eb|[Eb|[Eb|[Eb|[Eb|[Eb|Eb]]]]]]; rewrite Eb in RK |- *;
      unfold BA_SW, ASAN_K in RK;
      do 11 step;
      rewrite (rcl_zxb_eqb k 0) by lia; rewrite K0u; cbn [Z.eqb negb];
      do 12 step;
      (eapply evtF_cut; [eapply atail_jumpF; [exact HG | rewrite Eb; reflexivity | eassumption ..] |
       intros ms' HJ; exact (aemitF ms' HG HJ)]).
  Qed.

  (* ---- route (C): the _on twin of amainF, for reac_ctrl_build_as_contract_F_on. aQbF with its `shadow_rw m'`
     conjunct replaced by the _on post's region transport. ---- *)
  Definition aQbF_on : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                      (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 RR)
                    a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch (WW ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]) m m'
      /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' LO SP0
      /\ asan_cells m' /\ (forall P : Z -> Prop, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m')
      /\ addressable m' LO 4640
      /\ fp [0%nat; 1%nat] m' (bv_unsigned tp) FS LO SP0 WW DD
      /\ (GO = false -> munch [(SP0 - 80, SP0)] m m')
      /\ (GO && EE = true -> aRESbF m').

  (* The refusal arm: from the stretch's return of 0 (aRet0F), the memory facts afailF gets from atrF, without
     shadow_rw: asan_cells and addressable by atrF0n, fp by fl_fp, and the region transport by
     A.ShadowRwOnK.fl_shadow_rw_on along the frame munch [(SP0 - 80, SP0)] (no shadow byte there: fl_shadow_out). *)
  Lemma aret0F_on : forall ms', GO = false -> aRet0F ms' -> evtF rsegs RNG aQbF_on ms'.
  Proof.
    intros ms' HG (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> &
                   MU & WM & MI & ST).
    pose proof arng_spF as Rsp.
    assert (Hs : sub_fp [(SP0 - 80, SP0)] [(LO, SP0)]) by (apply ain_subF; lia).
    destruct (atrF0n _ m' MU WM Hs) as (AC1 & ADT1).
    pose proof (fl_fp _ m m' (bv_unsigned tp) FS LO SP0 _ DD _ FP MU WM Hs) as FP1.
    apply evtF_done. unfold aQbF_on.
    assert (R0 : RR = 0) by (rewrite HG; reflexivity). rewrite R0 in FP1 |- *.
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [reflexivity|].
    split.
    { apply (munch_weaken [(SP0 - 80, SP0)]); [|exact MU].
      intros x Hx. cbn [outside app] in *. destruct Hx as [H1 _]. split; [lia | exact I]. }
    split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact AC1|].
    split.
    { intros P HP. exact (A.ShadowRwOnK.fl_shadow_rw_on P _ m m' HP MU WM
                            (fun x Hx => fl_shadow_out _ LO SP0 x Hs HHM Hx)). }
    split; [exact (ADT1 _ _ AWIN)|]. split; [exact FP1|].
    split; [intros _; exact MU|].
    rewrite HG. intros H. cbn [andb] in H. discriminate H.
  Qed.

  (* ctrl_emit_as from the jump state on its _on contract (HEA_on): aemitF's script, with the asan facts at the jump
     memory mu from atrF0n / fl_fp (no shadow_rw), the region premise from HSW_on along the munch inside [LO, SP0)
     (fl_shadow_rw_on; no shadow byte there: fl_shadow_out), and the post's transport composed through mu. *)
  Lemma aemitF_on : forall ms', GO = true -> aJumpF ms' -> evtF rsegs RNG aQbF_on ms'.
  Proof.
    intros ms' HG (jt0 & jt1 & jt2 & ja0 & ja1 & ja2 & ja3 & ja4 & ja6 & ja7 & jt3 & jt4 & jt5 & jt6 & mu & -> &
                   E0 & E1 & E2 & E3 & E4 & E6 & E7 & E9 & MUt & WMt & MI2 & STu).
    subst ja0 ja1 ja2 ja3 ja4 ja6 ja7 jt4.
    pose proof arng_spF as Rsp. pose proof STu as (Rlo & _ & _).
    pose proof HG as HG'. apply andb_true_iff in HG' as [HG1 Hb6]. apply andb_true_iff in HG1 as [Ho0 Hm0].
    apply negb_true_iff, Z.eqb_neq in Ho0. apply negb_true_iff, Z.eqb_neq in Hm0. apply Z.leb_le in Hb6.
    assert (Hb6' : 0 <= b <= 6) by lia.
    destruct (ba_facts b Hb6') as (FK & KR & FBB & FC & FL & FG & FA & F18 & F19 & FAO & FAL).
    destruct (HM Hm0) as (M8 & M296 & ML & HMm & DM).
    pose proof DM as DMu. unfold ly_dj in DMu.
    pose proof (bm_uw_range md (firstn 8 (skipn 16 mb))) as RN.
    destruct (atrF0n _ mu MUt WMt (fun x Hx => Hx)) as (AC2 & ADT2).
    pose proof (fl_fp _ m mu (bv_unsigned tp) FS LO SP0 _ DD _ FP MUt WMt (fun x Hx => Hx)) as FP2.
    (* the region at the jump memory: HSW_on along the munch inside [LO, SP0), which holds no shadow byte *)
    assert (SHo : forall x, in_shadow x -> outside [(LO, SP0)] x)
      by (intros x Hx; exact (fl_shadow_out [(LO, SP0)] LO SP0 x (fun y Hy => Hy) HHM Hx)).
    pose proof (A.ShadowRwOnK.fl_shadow_rw_on _ _ m mu HSW_on MUt WMt SHo) as SW2.
    unfold lib.A.Prog.reac_ctrl_build_as_c.reac_ctrl_build_as_shadow_R in SW2.
    (* the facts ctrl_emit_as needs, in the memory at the jump *)
    pose proof DsT as DsTu. unfold ly_dj in DsTu.
    pose proof (aba_row_at rsegs mu b
                  (em_obj0 rsegs m mu LO SP0 (lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 72) ba_tbl 168 MUt HT ltac:(vm_compute; reflexivity)
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
    assert (DJf : fp_dj [(lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 24 * ba_row b, lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 24 * ba_row b + 24)] (fp_w [0%nat; 1%nat] FS))
      by (apply (fl_dj_sub _ _ _ _ _ DJT); lia).
    assert (AF : addressable mu (lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 24 * ba_row b) 24)
      by (apply (aaddr_sub mu (lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 72) 168); [exact (ADT2 _ _ ATB) | lia | lia | lia]).
    pose proof HEA_on as HE. unfold ctrl_emit_as_contract_F_on, CTRL_EMIT_AS_K in HE. cbv zeta in HE.
    eapply evtF_cut.
    { eapply HE with (o := o) (f := lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 24 * ba_row b) (md := md) (d := d) (s := s) (g := 0) (n := NN)
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
      - unfold lib.A.Prog.reac_ctrl_build_as_c.BA_FR. lia.
      - unfold lib.A.Prog.reac_ctrl_build_as_c.BA_FR. lia.
      - unfold lib.A.Prog.reac_ctrl_build_as_c.BA_FR. lia.
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
      (* the footprint premises of ctrl_emit_as, in the order of ctrl_emit_as_contract_F_on *)
      - exact RRB.
      - exact RIMG.
      - exact RWIN.
      - exact RWSH.
      - exact RFS.
      - exact RFSS.
      - unfold ctrl_emit_as_rtls.
        refine (ba_rtls_W _ m mu _ FS _ _ _ _ _ RNG FP MUt _ RTLS).
        intros x Hx. cbn [outside app] in *. destruct Hx as [H1 _]. split; [exact H1 | exact I].
      - eapply rng_sub; [exact RIMG | unfold lib.A.Prog.reac_ctrl_build_as_c.BA_FR; lia | unfold lib.A.Prog.reac_ctrl_build_as_c.BA_FR; lia].
      - apply ba_shcov_img; [exact RISH | unfold lib.A.Prog.reac_ctrl_build_as_c.BA_FR; lia | lia | unfold lib.A.Prog.reac_ctrl_build_as_c.BA_FR; lia].
      - exact (proj1 (RMD Hm0)).
      - exact (proj2 (RMD Hm0)).
      - exact RDD.
      - exact RDS.
      - exact RSD.
      - exact RSS.
      - intros K2. exfalso. rewrite FK in K2. lia.
      - apply NMc. intros NMx. exact (RNB Hm0 NMx).
      - intros G0. exfalso. exact (G0 eq_refl).
      - rewrite (ba_E_eq b NN mb Hb6'), (ba_len_eq b NN Hb6'). intros E1.
        assert (GE : GO && EE = true) by (rewrite HG; exact E1).
        exact (ROO GE).
      (* the shadow covers of the two JOIN blocks: inside the image, so inside the image-shadow range *)
      - intros _. apply ba_shcov_img; [exact RISH | unfold JOIN_0014; lia | lia | unfold JOIN_0014; lia].
      - intros _. apply ba_shcov_img; [exact RISH | unfold JOIN_0013; lia | lia | unfold JOIN_0013; lia]. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> &
                MU' & WM' & MI' & ST' & AC' & SW' & AW' & FP' & RES').
    apply evtF_done. unfold aQbF_on.
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
    split; [exact AC'|].
    split.
    { intros P HP. apply SW'. exact (A.ShadowRwOnK.fl_shadow_rw_on P _ m mu HP MUt WMt SHo). }
    split; [exact AW'|].
    split.
    { apply (fl_fp_D _ _ _ _ _ _ _ _ _ FP').
      apply fl_dj_cons. split; [exact DJT|]. apply fl_dj_cons. split; [exact DJM|].
      apply fl_dj_cons. split; [exact DJd|]. apply fl_dj_cons. split; [exact DJs|]. exact DJo. }
    split; [intros H; discriminate H|].
    intros E1. destruct (RES' E1) as (B & W & CL).
    exact (ba_res rsegs m' o b md NN (bv_unsigned a5 mod 65536) mb nb [] [] db sb Hb6' B W CL).
  Qed.

  (* The whole run on the _on contract: the lifted stretch (amain_stretchF, no shadow_rw premise), then the return of
     0 by aret0F_on or ctrl_emit_as from the jump state by aemitF_on. *)
  Lemma amainF_on : forall (t0 t1 t2 t3 t4 t5 t6 : word),
    evtF rsegs RNG aQbF_on
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 md) (Z_to_bv 64 b) (Z_to_bv 64 d)
               (Z_to_bv 64 s) a5 a6 (Z_to_bv 64 ns) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x848ac) fc None m (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 t3 t4 t5 t6.
    eapply evtF_cut; [exact (amain_stretchF t0 t1 t2 t3 t4 t5 t6)|].
    intros ms' [(HG & HJ) | (HG & HR)].
    - exact (aemitF_on ms' HG HJ).
    - exact (aret0F_on ms' HG HR).
  Qed.
End BuildF.

Theorem reac_ctrl_build_as_F_holds :
  ctrl_emit_as_contract_F -> reac_box_model_upstream_width_contract_F -> reac_ctrl_build_as_contract_F.
Proof.
  intros HEA _.
  (* route (C): the Section takes the callee's _on twin; its closed theorem replaces the old premise. *)
  pose proof reac_box_model_upstream_widthF.reac_box_model_upstream_width_F_holds_on as HUW.
  unfold reac_ctrl_build_as_contract_F, lib.A.Prog.reac_ctrl_build_as_c.REAC_CTRL_BUILD_AS, lib.A.Prog.reac_ctrl_build_as_c.REAC_CTRL_BUILD_AS_K.
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
  ctrl_emit_as_contract_F -> reac_box_model_upstream_width_contract_F -> lib.A.Prog.reac_ctrl_build_as_c.reac_ctrl_build_as_contract.
Proof.
  intros HEA HUW. exact (reac_ctrl_build_as_contract_of_F (reac_ctrl_build_as_F_holds HEA HUW)).
Qed.

(* route (C): the _on contract, from ctrl_emit_as's _on contract: reac_ctrl_build_as_F_holds's script with the region
   premise in HSW's place and amainF_on. *)
Theorem reac_ctrl_build_as_F_holds_on :
  ctrl_emit_as_contract_F_on -> lib.A.Prog.reac_ctrl_build_as_c.reac_ctrl_build_as_contract_F_on.
Proof.
  intros HEA_on.
  pose proof reac_box_model_upstream_widthF.reac_box_model_upstream_width_F_holds_on as HUW.
  unfold lib.A.Prog.reac_ctrl_build_as_c.reac_ctrl_build_as_contract_F_on, lib.A.Prog.reac_ctrl_build_as_c.REAC_CTRL_BUILD_AS,
    lib.A.Prog.reac_ctrl_build_as_c.REAC_CTRL_BUILD_AS_K.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m o md b d s ns FS mb nb db sb junk.
  cbv zeta.
  intros Ha0 Ha1 Ha2 Ha3 Ha4 -> Hns HS16 HST HT DsT Hdb HD Dsd Hsb HSb Dss HM HN Ho1492 HEo MI0
    HAC HSW_on HHM HAE AWIN ASW ATB AD AS APD APS AM AN AO AJ14 AJ13 FP FPN FPT
    RRB RIMG RISH RWIN RWSH RGK RCK RFS RFSS RTLS RMD RDD RDS RSD RSS RNB ROO.
  pose proof (rc_word_range a0 o Ha0) as Ro. apply rc_word in Ha0. subst a0.
  pose proof (rc_word_range a1 md Ha1) as Rmd. apply rc_word in Ha1. subst a1.
  pose proof (rc_word_range a2 b Ha2) as Rb. apply rc_word in Ha2. subst a2.
  apply rc_word in Ha3. subst a3.
  apply rc_word in Ha4. subst a4.
  eapply amainF_on; eassumption.
Qed.

(* The LIFTED STRETCH for the cgif-form glue (a Theorem Labs lane, route (a); a Theorem Labs lane 22:56Z): the run from entry to the
   tail jump (ctrl_emit_as's entry, its eight argument registers, a memory that differs from m only inside [Lo, S))
   when the arguments pass the checks, else to the return of 0 (a memory that differs from m only inside the
   80-byte frame). No ctrl_emit_as premise: ctrl_emit_as contains a fake-stack event (via ctrl_lay_block), so the
   glue applies it at this cut by its cgif spec.  reac_box_model_upstream_width (a leaf, no event) stays inside,
   on its _F contract.  Premises: exactly those amain_stretchF uses (two Theorem Labs lanes 00:12Z: the stretch
   owes only what it reads), i.e. its frame, the switch table's shadow, the model at md, the asan cells and the
   image / image-shadow / GOT / CELL_K footprint; the side stack, the thread cells and o / d / s / the name are
   ctrl_emit_as's accesses and are not premises here. *)
Definition reac_ctrl_build_as_stretch_F : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o md b d s ns : Z) (mb db sb : list byte),
    let S := bv_unsigned sp in
    let Lo := S - lib.A.Prog.reac_ctrl_build_as_c.REAC_CTRL_BUILD_AS_K in
    let n := bm_uw md (firstn 8 (skipn 16 mb)) in
    let go := ba_go o md b in
    bv_unsigned a0 = o -> bv_unsigned a1 = md -> bv_unsigned a2 = b -> bv_unsigned a3 = d -> bv_unsigned a4 = s ->
    a7 = Z_to_bv 64 ns ->
    stk rsegs m Lo S ->
    length db = 6%nat -> length sb = 6%nat ->
    (md <> 0 -> md mod 8 = 0 /\ md + 296 <= 2^64 /\ length mb = 296%nat /\ bytes_at rsegs m md mb /\
                ly_dj Lo S md (md + 296)) ->
    mem_inv rsegs m ->
    (* asan *)
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= Lo -> addressable m BA_SW 56 -> (md <> 0 -> addressable m md 296) ->
    (* the footprint: one rng premise per region the stretch and upstream_width read or write *)
    rng RNG 0x10000 0x5ee000 ->
    rng RNG 0x7fffa000 0xbdc00 ->
    rng RNG Lo lib.A.Prog.reac_ctrl_build_as_c.REAC_CTRL_BUILD_AS_K ->
    rng RNG GOT_CELL_K 8 -> rng RNG CELL_K 8 ->
    (md <> 0 -> rng RNG md 296 /\
       rng RNG (shadow_addr md / 8 * 8) (shadow_addr (md + 295) / 8 * 8 + 8 - shadow_addr md / 8 * 8)) ->
    evtF rsegs RNG
      (fun ms' =>
         (go = true /\ (exists (t0' t1' t2' a0' a1' a2' a3' a4' a6' a7' t3' t4' t5' t6' : word) (mu : word -> option byte),
            ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5 a6' a7'
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (Z_to_bv 64 CTRL_EMIT_AS) fc None mu (seg_rom rsegs)
            /\ a0' = Z_to_bv 64 o /\ a1' = Z_to_bv 64 (lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 24 * ba_row b) /\ a2' = Z_to_bv 64 md
            /\ a3' = Z_to_bv 64 d /\ a4' = Z_to_bv 64 s /\ a6' = Z_to_bv 64 n /\ a7' = Z_to_bv 64 0
            /\ t4' = Z_to_bv 64 ns
            /\ munch [(Lo, S)] m mu /\ wmono rsegs m mu /\ mem_inv rsegs mu /\ stk rsegs mu Lo S))
         \/
         (go = false /\ (exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                                (m' : word -> option byte),
            ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0)
                          a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (ret_pc ra) fc None m' (seg_rom rsegs)
            /\ munch [(S - 80, S)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' Lo S)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 lib.A.Prog.reac_ctrl_build_as_c.REAC_CTRL_BUILD_AS) fc None m (seg_rom rsegs)).

(* route (C) (a Theorem Labs lane 09:20Z; a Theorem Labs lane form rule 09:37Z): the stretch's _on twin. It reads no shadow byte through a
   universal shadow_rw premise (the switch-table and model shadow come from `addressable`, the callee is on its _on
   twin), and its post never stated shadow_rw, so the premise is DROPPED. The old name follows by dropping it. *)
Definition reac_ctrl_build_as_stretch_F_on : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o md b d s ns : Z) (mb db sb : list byte),
    let S := bv_unsigned sp in
    let Lo := S - lib.A.Prog.reac_ctrl_build_as_c.REAC_CTRL_BUILD_AS_K in
    let n := bm_uw md (firstn 8 (skipn 16 mb)) in
    let go := ba_go o md b in
    bv_unsigned a0 = o -> bv_unsigned a1 = md -> bv_unsigned a2 = b -> bv_unsigned a3 = d -> bv_unsigned a4 = s ->
    a7 = Z_to_bv 64 ns ->
    stk rsegs m Lo S ->
    length db = 6%nat -> length sb = 6%nat ->
    (md <> 0 -> md mod 8 = 0 /\ md + 296 <= 2^64 /\ length mb = 296%nat /\ bytes_at rsegs m md mb /\
                ly_dj Lo S md (md + 296)) ->
    mem_inv rsegs m ->
    (* asan *)
    asan_cells m ->
    HIGHMEM_BEG <= Lo -> addressable m BA_SW 56 -> (md <> 0 -> addressable m md 296) ->
    (* the footprint: one rng premise per region the stretch and upstream_width read or write *)
    rng RNG 0x10000 0x5ee000 ->
    rng RNG 0x7fffa000 0xbdc00 ->
    rng RNG Lo lib.A.Prog.reac_ctrl_build_as_c.REAC_CTRL_BUILD_AS_K ->
    rng RNG GOT_CELL_K 8 -> rng RNG CELL_K 8 ->
    (md <> 0 -> rng RNG md 296 /\
       rng RNG (shadow_addr md / 8 * 8) (shadow_addr (md + 295) / 8 * 8 + 8 - shadow_addr md / 8 * 8)) ->
    evtF rsegs RNG
      (fun ms' =>
         (go = true /\ (exists (t0' t1' t2' a0' a1' a2' a3' a4' a6' a7' t3' t4' t5' t6' : word) (mu : word -> option byte),
            ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5 a6' a7'
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (Z_to_bv 64 CTRL_EMIT_AS) fc None mu (seg_rom rsegs)
            /\ a0' = Z_to_bv 64 o /\ a1' = Z_to_bv 64 (lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 24 * ba_row b) /\ a2' = Z_to_bv 64 md
            /\ a3' = Z_to_bv 64 d /\ a4' = Z_to_bv 64 s /\ a6' = Z_to_bv 64 n /\ a7' = Z_to_bv 64 0
            /\ t4' = Z_to_bv 64 ns
            /\ munch [(Lo, S)] m mu /\ wmono rsegs m mu /\ mem_inv rsegs mu /\ stk rsegs mu Lo S))
         \/
         (go = false /\ (exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                                (m' : word -> option byte),
            ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0)
                          a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (ret_pc ra) fc None m' (seg_rom rsegs)
            /\ munch [(S - 80, S)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' Lo S)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 lib.A.Prog.reac_ctrl_build_as_c.REAC_CTRL_BUILD_AS) fc None m (seg_rom rsegs)).

Theorem reac_ctrl_build_as_stretch_F_on_holds : reac_ctrl_build_as_stretch_F_on.
Proof.
  pose proof reac_box_model_upstream_widthF.reac_box_model_upstream_width_F_holds_on as HUW.
  unfold reac_ctrl_build_as_stretch_F_on, lib.A.Prog.reac_ctrl_build_as_c.REAC_CTRL_BUILD_AS, lib.A.Prog.reac_ctrl_build_as_c.REAC_CTRL_BUILD_AS_K.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m o md b d s ns mb db sb.
  cbv zeta.
  intros Ha0 Ha1 Ha2 Ha3 Ha4 -> HST Hdb Hsb HM MI0 HAC HHM ASW AM RIMG RISH RWIN RGK RCK RMD.
  pose proof (rc_word_range a0 o Ha0) as Ro. apply rc_word in Ha0. subst a0.
  pose proof (rc_word_range a1 md Ha1) as Rmd. apply rc_word in Ha1. subst a1.
  pose proof (rc_word_range a2 b Ha2) as Rb. apply rc_word in Ha2. subst a2.
  apply rc_word in Ha3. subst a3.
  apply rc_word in Ha4. subst a4.
  eapply amain_stretchF; eassumption.
Qed.

Lemma reac_ctrl_build_as_stretch_F_of_on : reac_ctrl_build_as_stretch_F_on -> reac_ctrl_build_as_stretch_F.
Proof.
  intros HO. unfold reac_ctrl_build_as_stretch_F_on in HO. unfold reac_ctrl_build_as_stretch_F.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m o md b d s ns mb db sb.
  cbv zeta in HO |- *.
  intros Ha0 Ha1 Ha2 Ha3 Ha4 Ha7 HST Hdb Hsb HM MI0 HAC _ HHM ASW AM RIMG RISH RWIN RGK RCK RMD.
  exact (HO RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m o md b d s ns mb db sb
           Ha0 Ha1 Ha2 Ha3 Ha4 Ha7 HST Hdb Hsb HM MI0 HAC HHM ASW AM RIMG RISH RWIN RGK RCK RMD).
Qed.

(* The old name, from the _on twin (its upstream_width premise is no longer used: the closed _on theorem is). *)
Theorem reac_ctrl_build_as_stretch_F_holds :
  reac_box_model_upstream_width_contract_F -> reac_ctrl_build_as_stretch_F.
Proof. intros _. exact (reac_ctrl_build_as_stretch_F_of_on reac_ctrl_build_as_stretch_F_on_holds). Qed.
