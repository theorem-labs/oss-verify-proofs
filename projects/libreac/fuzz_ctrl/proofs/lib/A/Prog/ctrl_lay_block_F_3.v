(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its addresses changed; 109 of its 234 lines of code are new or changed and 3728 lines of the source are left out. *)
(* ctrl_lay_block, image A (asan, entry 0x855f4): STRETCH k = 3 of the footprint (_F) re-run of its proved v1.9
   run -- the silent stretch 0x85718 -> 0x85824, from the dispatch entry (DISP_T) to the cut
   `jal 85b44 <reac_box_model_block>`, on the 3 <= ly_k fr <= 9 path.  The split of record is
   ctrl_lay_block-stretches.md (a working note, not in this delivery); the shared skeleton (Require order,
   provenance, store_ok helpers) is lib/A/Prog/ctrl_lay_block_F_common.v.  ctrl_lay_block.v is unchanged apart from comment text.

   SOURCE SCRIPT (a working branch d69f7c708f6, lib/A/Prog/ctrl_lay_block.v): ly_dispatch :2147-2215,
   its common prefix :2156-2170 and the k = 3 .. 9 arms :2210-2214, then ly_boxcall :3913-3956 up to (but not
   including) `eapply BOXC` :3957 -- the three moves at 0x85818 / 0x8581c / 0x85820.  Every tactic is the old one
   over StepF: the same steps, the same shadow check at f + 2, the same jump table at 0x211b4.

   WHAT THE STRETCH READS (the rng premises below, in the recipe's order):
   - the window [S - K, S) of its own stk premise (LC);
   - the 24-byte f record (the checked `lbu` of the kind byte at f + 2) and its 3 shadow bytes (the `lb` at
     shadow_addr (f + 2) = shadow_addr f, since f mod 8 = 0);
   - the image [IMG_LO, IMG_HI) of lib/A/Prog/ImgBounds.v: the jump-table word at 0x211b4 + 4 * k (0x85748), the
     only image-constant read the function itself makes.
   No other access occurs: the arms 0x857c0 / 0x857c8 / 0x857f4 / 0x857fc / 0x85804 / 0x85814 and the three moves
   at 0x85818 .. 0x85820 are register-only.  No StepF access was reported uncovered.

   PROVENANCE (route (a) condition 4; the five conditions are quoted in ctrl_lay_block_F_common.v):
   - image root (internal path)
     -> (internal path)
   - ELF sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd
   - compare: fuzz_ctrl.objdump.txt (a working note, not in this delivery), ctrl_lay_block 0x855f4 .. 0x85988
   - FACTS of record ed6b6b7b0ab (origin/regen/libreac-v190-on-338), PAU (internal path)
   - auditor a Theorem Labs lane.

   NOTE ON THE REQUIRE LIST (for the auditor).  ctrl_lay_block_F_common.v requires its dependencies with
   `Require Import`, and Import is not transitive, so a file that only requires the skeleton sees the skeleton's
   four helpers and nothing else.  The skeleton's own list is therefore repeated below, AFTER the skeleton and in
   the skeleton's order (lib.Lib ExecF StepF last).  COMMON-CANDIDATE: make those requires `Require Export` in
   ctrl_lay_block_F_common.v.  Nobody edits the skeleton. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import ctrl_lay_block_F_common.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcPorts RcPortsLib RcBox RcSynth
  RcSynthLib RcLay RcLayLib RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c asan_memset_c asan_memcpy_c reac_box_model_block_c ctrl_lay_block_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import ctrl_lay_block.
(* IMG_LO / IMG_HI come from ImgBounds.v only (a Theorem Labs lane, 23:53Z). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import ImgBounds.
(* Last: StepF's step / if_false / finish / store_done (evtF goals) shadow the evt engine's. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* The metadata-byte access of the instrumented check is written (f + 2) / 8 + ASAN_K and its rng premise
   shadow_addr f = f / 8 + ASAN_K holds a division too; StepF's arithmetic has no Euclidean equations, so that
   one access goes through Z.div_mod_to_equations (f mod 8 = 0 is F8, in the context).  Every other access of the
   stretch closes with the stock solve_acc1.  (Same device as lib/A/Prog/reac_ctrl_classify_box_frameF.v's cls_accF (the file is not in this delivery), and as
   cls_accF (lib/A/Prog/reac_ctrl_classify_box_frame_Fs_on.v:58), a Theorem Labs lane's text.) *)
Ltac lay3_accF :=
  lazymatch goal with
  | |- acc_in ?RNG (?x, ?nn) =>
      let E := addr_expr x in
      lazymatch E with
      | context [Z.div _ _] =>
          let nz := eval cbv in (Z.of_nat nn) in
          match goal with
          | H : rng RNG ?lo ?len |- _ =>
              lazymatch lo with
              | context [Z.div _ _] =>
                  apply (rng_acc_varZ RNG lo len x nn nz H (@eq_refl Z nz));
                  cbv [wa]; rewrite ?MState.unsigned_lit_wrap;
                  unfold ASAN_K; Z.div_mod_to_equations; lia
              end
          end
      end
  end.
Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.acc_hint ::= lay3_accF.

(* The old file's shadow-check tactics over evtF: an Ltac body binds the tactics in scope where it is written, so
   ctrl_lay_block.v's evt forms (:313-354) cannot serve here.  Same text, evtF for evt. *)
Ltac steps_until_ifF :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step; steps_until_ifF
  | _ => idtac
  end.

Ltac bjoinF G r := lazymatch goal with |- evtF _ _ _ (MS ?R _ _ _ _ _ _) => exact (G (reg_get R r)) end.

Ltac chk_coreF X RX r SH pre extra :=
  let k := fresh "k" in let RK := fresh "RK" in let OK := fresh "OK" in let KR := fresh "KR" in
  destruct SH as (k & RK & OK & KR);
  pre X RX; steps_until_ifF; clear RK;
  unfold sxb; rewrite (rc_eqb0_signed (bv_signed k)) by (clear -KR; lia);
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (if _ then _ else ?B) ?fc ?rv ?mm ?ro) =>
      let G := fresh "G" in
      enough (G : forall rr : word, evtF segs RNG Q (MS (bvmap_set r rr R) F B fc rv mm ro));
      [ let K0 := fresh "K0" in
        destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
        [ bjoinF G r
        | step; rewrite ?(unsigned_lit X) by (clear -RX; lia); rewrite rc_land7; extra X;
          step;
          let MB := fresh "MB" in pose proof (Z.mod_pos_bound X 8 eq_refl) as MB;
          first [ rewrite (rc_lts_signed (X mod 8) (bv_signed k)) by (clear -MB KR; lia);
                  replace (X mod 8 <? bv_signed k) with true
                    by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK]; [exfalso; exact (K0 OK) | clear -OK; lia])
                | rewrite (rc_lts_signed (X mod 8 + 1) (bv_signed k)) by (clear -MB KR; lia);
                  replace (X mod 8 + 1 <? bv_signed k) with true
                    by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK]; [exfalso; exact (K0 OK) | clear -OK; lia])
                | rewrite (rc_lts_signed (X mod 8 + 3) (bv_signed k)) by (clear -MB KR; lia);
                  replace (X mod 8 + 3 <? bv_signed k) with true
                    by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK]; [exfalso; exact (K0 OK) | clear -OK; lia]) ];
          clear MB; bjoinF G r ]
      | intros ?; simp_regs; clear OK KR ]
  end.

Ltac pre_srF X RX := step; rewrite ?(unsigned_lit X) by (clear -RX; lia); rewrite rc_shr3.
Ltac no_extraF X := idtac.

Section K3.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p f md g FS : Z) (fr ob tb mb nb gb : list byte).

  Local Notation S := (bv_unsigned sp).
  Local Notation K := CTRL_LAY_BLOCK_K.
  Local Notation SP2 := ((S - 128) / 32 * 32).

  (* Section L's hypotheses (ctrl_lay_block.v :410-474), verbatim and in its order.  The four contract hypotheses
     of Section L (asan_stack_malloc_1_contract, asan_memset_contract, asan_memcpy_contract,
     reac_box_model_block_contract) are NOT here: this stretch contains no call. *)
  Hypothesis Rp : 0 <= p < 2^64.
  Hypothesis Rf : 0 <= f < 2^64.
  Hypothesis Rmd : 0 <= md < 2^64.
  Hypothesis Rg : 0 <= g < 2^64.
  Hypothesis SP16 : S mod 16 = 0.
  Hypothesis ST0 : stk rsegs m (S - K) S.
  Hypothesis DJ1 : ly_dj (S - K) S (p + 18) (p + 50).
  Hypothesis DJ2 : ly_dj (S - K) S f (f + 24).
  Hypothesis DJ3 : ly_k fr = 2 -> ly_dj (S - K) S (ly_tm fr) (ly_tm fr + 32).
  Hypothesis DJ3g : g <> 0 -> ly_al fr <> 0 -> ly_dj (S - K) S g (g + ly_al fr).
  Hypothesis DJ3m : 3 <= ly_k fr <= 9 -> md <> 0 ->
    ly_dj (S - K) S md (md + 296) /\
    ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
       ly_dj (S - K) S (rname mb) (rname mb + Z.of_nat (length nb))).
  Hypothesis F8 : f mod 8 = 0.
  Hypothesis F24 : f + 24 <= 2^64.
  Hypothesis FL : length fr = 24%nat.
  Hypothesis FB : bytes_at rsegs m f fr.
  Hypothesis K9 : ly_k fr <= 9.
  Hypothesis AOL : ly_ao fr + ly_al fr <= 32.
  Hypothesis TM : ly_k fr = 2 -> ly_tm fr + 32 <= 2^64 /\ length tb = 32%nat /\ ro_bytes rsegs (ly_tm fr) tb.
  Hypothesis P0 : p <> 0.
  Hypothesis P50 : p + 50 <= 2^64.
  Hypothesis BLK : rw_cells rsegs m (p + 18) [CB 32 ob].
  Hypothesis DB1 : ly_dj (p + 18) (p + 50) f (f + 24).
  Hypothesis DB2 : ly_k fr = 2 -> ly_dj (p + 18) (p + 50) (ly_tm fr) (ly_tm fr + 32).
  Hypothesis DB3 : 3 <= ly_k fr <= 9 -> md <> 0 -> ly_dj (p + 18) (p + 50) md (md + 296).
  Hypothesis DBN : 3 <= ly_k fr <= 9 -> md <> 0 -> (ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) ->
    has mb <> 0 -> rname mb <> 0 -> ly_dj (p + 18) (p + 50) (rname mb) (rname mb + Z.of_nat (length nb)).
  Hypothesis MDP : 3 <= ly_k fr <= 9 -> md <> 0 ->
    md mod 8 = 0 /\ length mb = 296%nat /\ bytes_at rsegs m md mb /\
    ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
       name_ok nb /\ bytes_at rsegs m (rname mb) nb).
  Hypothesis GP : g <> 0 -> ly_al fr <> 0 ->
    Z.of_nat (length gb) = ly_al fr /\ bytes_at rsegs m g gb /\ ly_dj (p + 18) (p + 50) g (g + ly_al fr).
  Hypothesis MI0 : mem_inv rsegs m.
  Hypothesis AC0 : asan_cells m.
  Hypothesis SR0 : shadow_rw m.
  Hypothesis HHM : HIGHMEM_BEG <= S - K.
  Hypothesis HAE : S <= APPMEM_END.
  Hypothesis AW0 : addressable m (S - K) K.
  Hypothesis AF : addressable m f 24.
  Hypothesis AR : addressable m (p + 18) 32.
  Hypothesis AP50 : app_mem (p + 50).
  Hypothesis ARDJ : p + 50 <= RT_LO \/ RT_HI <= p + 18.
  Hypothesis ATM : ly_k fr = 2 -> addressable m (ly_tm fr) 32.
  Hypothesis AG : g <> 0 -> ly_al fr <> 0 ->
    addressable m g (ly_al fr) /\ app_mem (g + ly_al fr) /\ app_mem (g + 7) /\ app_mem (p + 25 + ly_ao fr).
  Hypothesis AMD : 3 <= ly_k fr <= 9 -> md <> 0 ->
    addressable m md 296 /\
    ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
       addressable m (rname mb) (Z.of_nat (length nb))).
  Hypothesis AJ5 : ly_k fr = 5 -> addressable m JOIN_0014 32.
  Hypothesis AJ6 : ly_k fr = 6 -> addressable m JOIN_0013 32.
  Hypothesis FP0 : fp [0%nat; 1%nat] m (bv_unsigned tp) FS (S - K) S
    (ctrl_lay_block_W p S) (ctrl_lay_block_D p f).
  Hypothesis FPT : ly_k fr = 2 -> fp_dj [(ly_tm fr, ly_tm fr + 32)] (fp_w [0%nat; 1%nat] FS).
  Hypothesis FPG : g <> 0 -> ly_al fr <> 0 -> fp_dj [(g, g + ly_al fr)] (fp_w [0%nat; 1%nat] FS).
  Hypothesis FPM : 3 <= ly_k fr <= 9 -> md <> 0 ->
    fp_dj [(md, md + 296)] (fp_w [0%nat; 1%nat] FS) /\
    ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
       fp_dj [(rname mb, rname mb + Z.of_nat (length nb))] (fp_w [0%nat; 1%nat] FS)).
  Hypothesis TLS0 : ctrl_lay_block_tls m (bv_unsigned tp) FS (S - K) S.

  (* Section L's own predicates and the one Section L lemma this stretch uses, applied to this section's
     variables (and, for the lemma, to the Section L hypotheses it was discharged over: outside L they are its
     arguments by name). *)
  Local Notation FIl := (ctrl_lay_block.FI sp tp p f FS).
  Local Notation LCl := (ctrl_lay_block.LC ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m p f FS fr).
  Local Notation LC_addr_fl :=
    (ctrl_lay_block.LC_addr_f ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m p f md g FS fr tb mb nb gb
       Rp Rf Rmd Rg SP16 DJ2 FL K9 TM P0 MDP HHM AF AR FP0).

  (* The post of this stretch and the pre of the glue's reac_box_model_block_contract step, at pc 0x85824 (the
     `jal 85b44 <reac_box_model_block>` itself is the cut, so it is NOT taken here): a0 = md, a1 = b = ly_bb k,
     a2 = s7 = frb + 32, sp = spc, the callee-saved set as at 0x85818, memory mc unchanged, and the facts the
     callee contract needs -- FI, LC at ly_zero and the addressable output block. *)
  Definition lay_F_pre_box (mc : word -> option byte) (gj : list byte) (frb sfr spc j : Z) (w120 : word)
    : machine_state -> Prop :=
    fun ms' => exists (xra x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      ms' = MS (mkR xra (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 SP2)
                    (Z_to_bv 64 md) (Z_to_bv 64 (ly_bb (ly_k fr))) (Z_to_bv 64 (frb + 32))
                    x13 x14 x15 x16 x17
                    (Z_to_bv 64 sfr) (Z_to_bv 64 g) (Z_to_bv 64 f) (Z_to_bv 64 (p + 18)) (Z_to_bv 64 md)
                    (Z_to_bv 64 (frb + 32)) (Z_to_bv 64 (shadow_addr frb)) (Z_to_bv 64 frb)
                    (Z_to_bv 64 ASAN_K) s11 x28 x29 x30 x31)
               F (Z_to_bv 64 0x85824) fc None mc (seg_rom rsegs) /\
      FIl mc frb sfr spc j w120 /\ LCl mc gj ly_zero /\ addressable mc (frb + 32) 32 /\
      3 <= ly_k fr <= 9.

  (* 0x85818 .. 0x85820: s7 = frb + 32 (the frame's middle 32 bytes), a0 = s6 = md, a2 = s7; then the state at
     the cut.  This is ly_boxcall :3955 -- the first three of its four `step`s; the fourth is the `jal` itself,
     which the glue takes with reac_box_model_block_contract.  ly_boxcall's prelude :3915-3954 (RFRB, SPC, BBR,
     AOUT, FRW, the output bytes obx, OW, RWO, SPC64, USP) is what its `eapply BOXC` :3957 needs, not what the
     three register moves need, so it is not re-proved here: the stretch stops at the cut. *)
  Lemma lay_F_boxarm : forall (RNG : footprint) (mc : word -> option byte) (gj : list byte)
      (b frb sfr spc j : Z) (w120 : word)
      (xra x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    b = ly_bb (ly_k fr) -> 3 <= ly_k fr <= 9 ->
    FIl mc frb sfr spc j w120 -> LCl mc gj ly_zero -> addressable mc (frb + 32) 32 ->
    evtF rsegs RNG (lay_F_pre_box mc gj frb sfr spc j w120)
      (MS (mkR xra (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 SP2)
               x10 (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 sfr) (Z_to_bv 64 g) (Z_to_bv 64 f) (Z_to_bv 64 (p + 18)) (Z_to_bv 64 md)
               (Z_to_bv 64 p) (Z_to_bv 64 (shadow_addr frb)) (Z_to_bv 64 frb) (Z_to_bv 64 ASAN_K) s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 0x85818) fc None mc (seg_rom rsegs)).
  Proof.
    intros RNG mc gj b frb sfr spc j w120 xra x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
      -> KB9 FIH LCH AO.
    step. step. step.
    apply evtF_done. hnf.
    do 13 eexists.
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact FIH|]. split; [exact LCH|]. split; [exact AO | exact KB9].
  Qed.

  (* 0x85718 .. 0x85824 on the 3 <= k <= 9 path: the checked load of the kind byte k at f + 2, the k <= 9 bound
     check, the jump through the table at 0x211b4, the arm's `li a1, ly_bb k` and the three moves at the box call.
     ly_dispatch :2156-2170 + :2210-2214, then lay_F_boxarm. *)
  Lemma ctrl_lay_block_F_3 : forall (RNG : footprint) (mc : word -> option byte) (gj : list byte)
      (frb sfr spc j : Z) (w120 : word)
      (xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    rng RNG (S - K) K -> rng RNG f 24 -> rng RNG (shadow_addr f) 3 -> rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    3 <= ly_k fr <= 9 ->
    FIl mc frb sfr spc j w120 -> LCl mc gj ly_zero -> addressable mc (frb + 32) 32 ->
    evtF rsegs RNG (lay_F_pre_box mc gj frb sfr spc j w120)
      (MS (mkR xra (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 SP2)
               x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 sfr) (Z_to_bv 64 g) (Z_to_bv 64 f) (Z_to_bv 64 (p + 18)) (Z_to_bv 64 md)
               (Z_to_bv 64 p) (Z_to_bv 64 (shadow_addr frb)) (Z_to_bv 64 frb) (Z_to_bv 64 ASAN_K) s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 0x85718) fc None mc (seg_rom rsegs)).
  Proof.
    intros RNG mc gj frb sfr spc j w120 xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
      RSTK RFB RFSH RIMG KB FIH LCH AFR.
    unfold IMG_LO, IMG_HI in RIMG. unfold shadow_addr in RFSH.
    pose proof (LC_addr_fl mc gj ly_zero LCH) as AFc.
    pose proof LCH as (FR & ST & MU & WM & MI & BK & FBc).
    pose proof (rd_byte rsegs mc f fr 2 FBc ltac:(lia)) as R2.
    step.
    pose proof (acl_shadow mc f 24 2 1 (f + 2) AFc ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite Z.add_mod by lia; rewrite F8; cbn; lia) eq_refl) as SH2.
    assert (RX2 : 0 <= f + 2 < 2^64) by lia.
    chk_coreF (f + 2) RX2 (Z_to_bv 5 12) SH2 pre_srF no_extraF.
    step. clear R2. step. step. rewrite (rc_u8_gtu fr 2 9) by lia.
    replace (9 <? rc_u8 fr 2) with false by (symmetry; apply Z.ltb_ge; unfold ly_k in K9; lia). cbv iota.
    assert (KC : ly_k fr = 3 \/ ly_k fr = 4 \/ ly_k fr = 5 \/ ly_k fr = 6 \/ ly_k fr = 7 \/ ly_k fr = 8 \/
                 ly_k fr = 9) by lia.
    destruct KC as [KE|[KE|[KE|[KE|[KE|[KE|KE]]]]]]; rewrite (rc_zxb_lit fr 2 _ KE); do 8 step;
      repeat lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x85818) _ _ _ _) => fail | _ => step end;
      (eapply lay_F_boxarm; [unfold ly_bb; rewrite KE; reflexivity | exact KB | exact FIH | exact LCH
                            | exact AFR]).
  Qed.

  (* Recipe step 4: the _F statement is the old one plus the footprint premises and nothing weaker -- at RNG_all
     the stretch is the plain Exec.evt run from the dispatch entry to the box call. *)
  Corollary ctrl_lay_block_F_3_of_F : forall (mc : word -> option byte) (gj : list byte)
      (frb sfr spc j : Z) (w120 : word)
      (xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    3 <= ly_k fr <= 9 ->
    FIl mc frb sfr spc j w120 -> LCl mc gj ly_zero -> addressable mc (frb + 32) 32 ->
    evt rsegs (lay_F_pre_box mc gj frb sfr spc j w120)
      (MS (mkR xra (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 SP2)
               x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 sfr) (Z_to_bv 64 g) (Z_to_bv 64 f) (Z_to_bv 64 (p + 18)) (Z_to_bv 64 md)
               (Z_to_bv 64 p) (Z_to_bv 64 (shadow_addr frb)) (Z_to_bv 64 frb) (Z_to_bv 64 ASAN_K) s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 0x85718) fc None mc (seg_rom rsegs)).
  Proof.
    intros mc gj frb sfr spc j w120 xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
      KB FIH LCH AFR.
    eapply evtF_evt. eapply ctrl_lay_block_F_3; try eassumption.
    - apply rng_all; pose proof HHM; pose proof HAE;
        unfold HIGHMEM_BEG, APPMEM_END, CTRL_LAY_BLOCK_K in *; lia.
    - apply rng_all; lia.
    - apply rng_all; [ unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia
                     | unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia ].
    - apply rng_all; unfold IMG_LO, IMG_HI; lia.
  Qed.

End K3.
