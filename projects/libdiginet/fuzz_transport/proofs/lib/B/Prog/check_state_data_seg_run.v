(* check_state_data_seg_run: the two straight-line footprint runs (lib/Lib/ExecF.v evtF) of check_state_data in
   image B (fuzz_transport.asan-ubsan, entry 0x857cc = transportb_sigma TB_check_state_data, 460 bytes):
     csd_run_call_F  the entry to the call of the bcmp wrapper at 0x858a4: the 32-byte frame and its four saves,
                     GOT.ndata and its test, OW.ndata and its test, the alignment test of p, the shadow base through
                     its GOT word, the instrumented check of n->body_len, &OW.dn[g] and its two pointer tests, the
                     instrumented check of OW.dn[g].len, the loads of the two lengths and their compare, the
                     instrumented checks of n->body and OW.dn[g].body and their loads;
     csd_run_ret_F   the call's return (0x858a8, the wrapper answered 0) to the `ret` at 0x85928: the counter
                     compare and the retry compare, each behind its two instrumented checks, and the epilogue.
   Every instrumented check passes without its error path: the shadow byte of the granule it reads is 0, a premise
   here; the walk lib/B/Prog/check_state_data_cgW.v gets it from the read range of the notice and from the record's
   zero-shadow row for OW. The alignment test passes on p mod 8 = 0. g = GOT.ndata is 0 or 1 (the code's two tests)
   and d = 256 + 24 g is the offset of OW.dn[g] in OW, so every address inside OW, and each pointer test of &OW.dn[g],
   is a literal on each branch. Image A's twin is lib/A/Prog/check_state_data_seg_run.v; the code differs by the
   alignment test, the pointer tests and the order of the loads.
   The functional content is the plain walk lib/Prog/T/check_state_data.v, step for step, at image B's addresses. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA AsanKAProof.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.

(* ---- the addresses ---- *)

Definition CSD_ENTRY : Z := transportb_sigma TB_check_state_data.
Definition CSD_BCMP : Z := transportb_sigma TB___interceptor_trampoline_bcmp.
(* the return address of the call at 0x858a4 *)
Definition CSD_RET : Z := CSD_ENTRY + 0xdc.
(* `addi sp,sp,-32` at the entry; no realignment and no side-stack frame *)
Definition CSD_FRAME : Z := 32.
(* the frame: s2, s1, s0 and ra at sp - 32, sp - 24, sp - 16 and sp - 8 *)
Definition csd_fr (c2 c1 c0 cra : word) : list cell := [C8 c2; C8 c1; C8 c0; C8 cra].

(* ---- small facts ---- *)

Lemma csd_rd : forall m a bs n, bytes_at rsegs m a bs -> length bs = n ->
  ov_read_bytes rsegs m (wa a) n = Some bs.
Proof.
  intros m a bs n H <-.
  pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) H ltac:(lia)) as R.
  change (Z.of_nat 0) with 0 in R. rewrite Z.add_0_r, skipn_O, firstn_all in R. exact R.
Qed.

(* A slice of a byte list, read at a register whose value is the slice's address. *)
Lemma csd_rd_sub : forall m (w : word) a (bs : list byte) (k : Z) (n : nat),
  bytes_at rsegs m a bs -> 0 <= k -> (Z.to_nat k + n <= length bs)%nat -> bv_unsigned w = a + k ->
  ov_read_bytes rsegs m w n = Some (TW.sub bs k n).
Proof.
  intros m w a bs k n H Hk Hn E. rewrite <- (Z_to_bv_bv_unsigned w), E.
  change (Z_to_bv 64 (a + k)) with (wa (a + k)). exact (bytes_at_read rsegs m a bs k n H Hk Hn).
Qed.

(* A signed compare of two values in range. *)
Lemma csd_lts : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_lts. rewrite !signed_lit by lia. reflexivity. Qed.

(* The length of a slice of the world. *)
Lemma csd_lsub : forall (Bw : list byte) k (n : nat), length Bw = Z.to_nat TW.W_LEN ->
  0 <= k -> k + Z.of_nat n <= TW.W_LEN -> length (TW.sub Bw k n) = n.
Proof.
  intros Bw k n L Hk Hn. apply TWL.length_sub; [lia|]. rewrite L. unfold TW.W_LEN in *. lia.
Qed.

Lemma csd_s32_range : forall (Bw : list byte) k, -2^31 <= TW.s32_at Bw k < 2^31.
Proof.
  intros Bw k. unfold TW.s32_at.
  pose proof (bv_swrap_in_range 32 (TW.u_at Bw k 4) ltac:(lia)) as R.
  unfold bv_half_modulus, bv_modulus in R. change (2 ^ Z.of_N 32 / 2) with (2^31) in R. lia.
Qed.

(* The pc of a run's first state, as a literal. *)
Ltac csd_pc := lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let v := eval vm_compute in pc in change pc with v
  end.

(* A branch whose condition is closed. *)
Ltac csd_br b := lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b by (vm_compute; reflexivity); cbv iota
  end.

(* A `bne` of two values the model makes equal: the equation H closes the compare up to conversion. *)
Ltac csd_bne H := lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false by
        (symmetry; apply (proj2 (Bool.negb_false_iff _)); unfold bv_eqb; apply Z.eqb_eq;
         f_equal; f_equal; first [exact H | rewrite H; reflexivity])
  end; cbv iota.

(* ---- the entry to the call of the bcmp wrapper (0x857cc .. 0x858a4) ---- *)

Lemma csd_run_call_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo p g d on : Z) (NB Bw : list byte),
    (g = 0 /\ d = 256) \/ (g = 1 /\ d = 280) ->
    0 < p -> p mod 8 = 0 -> p + 72 <= 2 ^ 47 ->
    length NB = 72%nat ->
    0x10007fff8000 + 32 <= bv_unsigned sp -> bv_unsigned sp <= 2 ^ 47 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp ->
    (p + 72 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= p) ->
    tw_at TMAP_B (csw_view m) Bw ->
    TW.s32_at Bw TW.A_GOT_ndata = g ->
    TW.s32_at Bw TW.A_OW_ndata = on -> g < on ->
    TW.u_at NB 56 8 = TW.u_at Bw (TW.OFF_OW + (d + 8)) 8 ->
    bytes_at rsegs m GOT_CELL_K (le8 (wa CELL_K)) ->
    bytes_at rsegs m CELL_K (le8 (wa ASAN_K)) ->
    bytes_at rsegs m p NB ->
    mrd rsegs m (wa ((p + 48) / 8 + ASAN_K)) = Some (Z_to_bv 8 0) ->
    mrd rsegs m (wa ((p + 56) / 8 + ASAN_K)) = Some (Z_to_bv 8 0) ->
    mrd rsegs m (wa ((TB_OW + d) / 8 + ASAN_K)) = Some (Z_to_bv 8 0) ->
    mrd rsegs m (wa ((TB_OW + d + 8) / 8 + ASAN_K)) = Some (Z_to_bv 8 0) ->
    ExecF.rng RNG (bv_unsigned sp + -32) 32 ->
    ExecF.rng RNG GOT_CELL_K 8 ->
    ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG (TB_GOT + 220) 4 ->
    ExecF.rng RNG TB_OW 304 ->
    ExecF.rng RNG p 72 ->
    ExecF.rng RNG ((p + 48) / 8 + ASAN_K) 1 ->
    ExecF.rng RNG ((p + 56) / 8 + ASAN_K) 1 ->
    ExecF.rng RNG ((TB_OW + d) / 8 + ASAN_K) 1 ->
    ExecF.rng RNG ((TB_OW + d + 8) / 8 + ASAN_K) 1 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (m1 : word -> option byte) (r13 r14 : word),
         ms' = MS (mkR (Z_to_bv 64 CSD_RET) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2
                       (Z_to_bv 64 p) (Z_to_bv 64 (TB_OW + d))
                       (Z_to_bv 64 (TW.u_at NB 48 8)) (Z_to_bv 64 (TW.u_at Bw (TW.OFF_OW + d) 8))
                       (Z_to_bv 64 (TW.u_at NB 56 8)) r13 r14
                       a5 a6 a7 (Z_to_bv 64 ASAN_K) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CSD_BCMP) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
         stk rsegs m1 lo (bv_unsigned sp + -32) /\
         rw_cells rsegs m1 (bv_unsigned sp + -32) (csd_fr s2 s1 s0 ra))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CSD_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo p g d on NB Bw HG HP0 HP8 HPHI LNB HSP HSPT ST HLO HOFFP HW EG EON HLT HEQ
    BGOTC BCELL BNB SH48 SH56 SHDB SHDL RFR RGOTC RCELL RGOT ROW RP RS48 RS56 RSDB RSDL.
  pose proof (u64_range sp) as Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  pose proof (tw_len TMAP_B _ Bw HW) as LBw.
  pose proof (csd_s32_range Bw TW.A_OW_ndata) as RON. rewrite EON in RON.
  assert (HDB : 256 <= d <= 280) by (destruct HG as [[_ ->]|[_ ->]]; lia).
  pose proof (rng_sub' _ _ _ (TB_OW + d) 8 ROW ltac:(unfold TB_OW; lia)) as RWDB.
  pose proof (rng_sub' _ _ _ (TB_OW + (d + 8)) 8 ROW ltac:(unfold TB_OW; lia)) as RWDL.
  pose proof (rng_sub' _ _ _ (TB_GOT + 220) 4 RGOT ltac:(lia)) as RWGN.
  pose proof (rng_sub' _ _ _ (TB_OW + 220) 4 ROW ltac:(unfold TB_OW; lia)) as RWON.
  unfold GOT_CELL_K, CELL_K, ASAN_K, TB_GOT, TB_OW in *.
  (* p as the number of a register word *)
  assert (Up : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  remember (Z_to_bv 64 p) as pw eqn:Epw. clear Epw. subst p.
  (* the four slices of the world the run reads *)
  assert (LGN : length (TW.sub Bw (TW.OFF_GOT + 220) 4) = 4%nat)
    by (apply csd_lsub; [exact LBw | unfold TW.OFF_GOT; lia | unfold TW.OFF_GOT, TW.W_LEN; lia]).
  assert (LON : length (TW.sub Bw (TW.OFF_OW + 220) 4) = 4%nat)
    by (apply csd_lsub; [exact LBw | unfold TW.OFF_OW; lia | unfold TW.OFF_OW, TW.W_LEN; lia]).
  assert (LDB : length (TW.sub Bw (TW.OFF_OW + d) 8) = 8%nat)
    by (apply csd_lsub; [exact LBw | unfold TW.OFF_OW; lia | unfold TW.OFF_OW, TW.W_LEN; lia]).
  assert (LDL : length (TW.sub Bw (TW.OFF_OW + (d + 8)) 8) = 8%nat)
    by (apply csd_lsub; [exact LBw | unfold TW.OFF_OW; lia | unfold TW.OFF_OW, TW.W_LEN; lia]).
  pose proof (tw_bytes_at rsegs m TMAP_B Bw TW.OFF_GOT TB_GOT TW.SZ_GOT 220 4 TMAP_B_ok HW TMAP_B_GOT
    ltac:(lia) ltac:(unfold TW.SZ_GOT; lia)) as BGN.
  pose proof (tw_bytes_at rsegs m TMAP_B Bw TW.OFF_OW TB_OW TW.SZ_OW 220 4 TMAP_B_ok HW TMAP_B_OW
    ltac:(lia) ltac:(unfold TW.SZ_OW; lia)) as BON.
  pose proof (tw_bytes_at rsegs m TMAP_B Bw TW.OFF_OW TB_OW TW.SZ_OW d 8 TMAP_B_ok HW TMAP_B_OW
    ltac:(lia) ltac:(unfold TW.SZ_OW; lia)) as BDB.
  pose proof (tw_bytes_at rsegs m TMAP_B Bw TW.OFF_OW TB_OW TW.SZ_OW (d + 8) 8 TMAP_B_ok HW TMAP_B_OW
    ltac:(lia) ltac:(unfold TW.SZ_OW; lia)) as BDL.
  clear HW.
  (* keep the byte facts off transport_chunks: they are carried past the four saves by hand *)
  pose proof (conj BGOTC (conj BCELL (conj BNB (conj BGN (conj BON (conj BDB BDL)))))) as KEEP.
  clear BGOTC BCELL BNB BGN BON BDB BDL.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  csd_pc.
  (* 0x857cc .. 0x857dc: the frame and the four saves *)
  do 5 step.
  match goal with MU' : munch _ m ?mm |- _ =>
    rename MU' into MU1; first [constr_eq mm m0 | rename mm into m0] end.
  destruct KEEP as (BGOTC & BCELL & BNB & BGN & BON & BDB & BDL).
  assert (BGOTC0 : bytes_at rsegs m0 0xa3cf0 (le8 (wa 0xac678)))
    by (apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite length_le8; lia | exact BGOTC]).
  assert (BCELL0 : bytes_at rsegs m0 0xac678 (le8 (wa 0x7fff8000)))
    by (apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite length_le8; lia | exact BCELL]).
  assert (BNB0 : bytes_at rsegs m0 (bv_unsigned pw) NB)
    by (apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite LNB; lia | exact BNB]).
  assert (BGN0 : bytes_at rsegs m0 (TB_GOT + 220) (TW.sub Bw (TW.OFF_GOT + 220) 4))
    by (apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite LGN; unfold TB_GOT; lia | exact BGN]).
  assert (BON0 : bytes_at rsegs m0 (TB_OW + 220) (TW.sub Bw (TW.OFF_OW + 220) 4))
    by (apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite LON; unfold TB_OW; lia | exact BON]).
  assert (BDB0 : bytes_at rsegs m0 (TB_OW + d) (TW.sub Bw (TW.OFF_OW + d) 8))
    by (apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite LDB; unfold TB_OW; lia | exact BDB]).
  assert (BDL0 : bytes_at rsegs m0 (TB_OW + (d + 8)) (TW.sub Bw (TW.OFF_OW + (d + 8)) 8))
    by (apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite LDL; unfold TB_OW; lia | exact BDL]).
  clear BGOTC BCELL BNB BGN BON BDB BDL.
  assert (SH480 : mrd rsegs m0 (wa ((bv_unsigned pw + 48) / 8 + 2147450880)) = Some (Z_to_bv 8 0))
    by (apply (mrd_tp m m0 _ _ _ _ MU1); [Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | exact SH48]).
  assert (SH560 : mrd rsegs m0 (wa ((bv_unsigned pw + 56) / 8 + 2147450880)) = Some (Z_to_bv 8 0))
    by (apply (mrd_tp m m0 _ _ _ _ MU1); [Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | exact SH56]).
  assert (SHDB0 : mrd rsegs m0 (wa ((TB_OW + d) / 8 + 2147450880)) = Some (Z_to_bv 8 0))
    by (apply (mrd_tp m m0 _ _ _ _ MU1);
        [unfold TB_OW; Z.div_mod_to_equations; lia | unfold TB_OW; Z.div_mod_to_equations; lia | exact SHDB]).
  assert (SHDL0 : mrd rsegs m0 (wa ((TB_OW + d + 8) / 8 + 2147450880)) = Some (Z_to_bv 8 0))
    by (apply (mrd_tp m m0 _ _ _ _ MU1);
        [unfold TB_OW; Z.div_mod_to_equations; lia | unfold TB_OW; Z.div_mod_to_equations; lia | exact SHDL]).
  clear SH48 SH56 SHDB SHDL.
  (* 0x857e0 .. 0x857e4: a1 = GOT.ndata *)
  pose proof (csd_rd m0 _ _ 4 BGN0 LGN) as RDGN.
  step. step. rewrite lw_world. change (TW.OFF_GOT + 220) with TW.A_GOT_ndata. rewrite EG.
  (* 0x857e8 .. 0x857ec: 1 <s g goes to the trap; the model gives g <= 1 *)
  step. step.
  rewrite (csd_lts 1 g) by (destruct HG as [[-> _]|[-> _]]; lia).
  replace (1 <? g) with false by (symmetry; apply Z.ltb_ge; destruct HG as [[-> _]|[-> _]]; lia).
  cbv iota.
  (* 0x857f0: s0 = p; 0x857f4 .. 0x857f8: a2 = OW *)
  step. step. step.
  (* 0x857fc: a0 = OW.ndata *)
  pose proof (csd_rd m0 _ _ 4 BON0 LON) as RDON.
  step. rewrite lw_world. change (TW.OFF_OW + 220) with TW.A_OW_ndata. rewrite EON.
  (* 0x85800: OW.ndata <=s g goes to the trap; the model gives g < OW.ndata *)
  step. rewrite (csd_lts g on) by (destruct HG as [[-> _]|[-> _]]; lia).
  replace (g <? on) with true by (symmetry; apply Z.ltb_lt; lia). cbv beta iota delta [negb].
  (* 0x85804 .. 0x85808: p & 7 <> 0 goes to the unimp word; p mod 8 = 0 *)
  step.
  lazymatch goal with |- context [Z.land (bv_unsigned pw) ?X] =>
    replace (Z.land (bv_unsigned pw) X) with 0
      by (change X with (Z.ones 3); rewrite Z.land_ones by lia; symmetry; exact HP8)
  end.
  step. csd_br false.
  (* 0x8580c .. 0x85814: s2 = the shadow base, through its GOT word *)
  pose proof (csd_rd m0 _ _ 8 BGOTC0 (length_le8 _)) as RDG.
  pose proof (csd_rd m0 _ _ 8 BCELL0 (length_le8 _)) as RDS.
  step. step. step.
  (* 0x85818 .. 0x85828: the instrumented check of the 8-byte load at p + 56 *)
  step. gen_addi pw w56 U56.
  pose proof (rng_sub' _ _ _ (bv_unsigned w56) 8 RP ltac:(lia)) as RW56.
  step. gen_shr w56 h56 H56. rewrite U56 in H56.
  step. gen_addi h56 k56 K56. rewrite H56 in K56.
  pose proof (rng_sub' _ _ _ (bv_unsigned k56) 1 RS56 ltac:(lia)) as RK56.
  pose proof (rdw0 m0 k56 _ _ SH560 ltac:(lia)) as R56. step. clear R56.
  step. csd_br false.
  (* 0x8582c .. 0x8583c: s1 = OW + 256 + 24 g (&OW.dn[g]); the two branches of g *)
  destruct HG as [[-> ->]|[-> ->]];
  do 5 step;
  (* 0x85840: s1 = 0 goes to the unimp word *)
  step; csd_br false;
  (* 0x85844 .. 0x85854: (s1 <u OW + 256) <> (g <s 0) goes to the unimp word *)
  do 4 step;
  step; csd_br false;
  (* 0x85858 .. 0x85868: the instrumented check of the load of OW.dn[g].len *)
  do 3 step;
  (pose proof (rd1 m0 _ _ SHDL0) as RDSL);
  step; clear RDSL;
  step; csd_br false;
  (* 0x8586c: a2 = n->body_len *)
  (pose proof (csd_rd_sub m0 w56 _ NB 56 8 BNB0 ltac:(lia) ltac:(rewrite LNB; lia) ltac:(lia)) as RD56);
  step; clear RD56; rewrite ld_world;
  (* 0x85870: a0 = OW.dn[g].len *)
  (pose proof (csd_rd m0 _ _ 8 BDL0 LDL) as RDDL);
  step; clear RDDL; rewrite ld_world;
  (* 0x85874: the two differ goes to the trap; the model makes them equal *)
  step; csd_bne HEQ;
  (* 0x85878 .. 0x85888: the instrumented check of the 8-byte load at p + 48 *)
  step; gen_addi pw w48 U48;
  (pose proof (rng_sub' _ _ _ (bv_unsigned w48) 8 RP ltac:(lia)) as RW48);
  step; gen_shr w48 h48 H48; rewrite U48 in H48;
  step; gen_addi h48 k48 K48; rewrite H48 in K48;
  (pose proof (rng_sub' _ _ _ (bv_unsigned k48) 1 RS48 ltac:(lia)) as RK48);
  (pose proof (rdw0 m0 k48 _ _ SH480 ltac:(lia)) as R48);
  step; clear R48;
  step; csd_br false;
  (* 0x8588c .. 0x85898: the instrumented check of the load of OW.dn[g].body *)
  do 2 step;
  (pose proof (rd1 m0 _ _ SHDB0) as RDSB);
  step; clear RDSB;
  step; csd_br false;
  (* 0x8589c: a0 = n->body; 0x858a0: a1 = OW.dn[g].body *)
  (pose proof (csd_rd_sub m0 w48 _ NB 48 8 BNB0 ltac:(lia) ltac:(rewrite LNB; lia) ltac:(lia)) as RD48);
  step; clear RD48; rewrite ld_world;
  (pose proof (csd_rd m0 _ _ 8 BDB0 LDB) as RDDB);
  step; clear RDDB; rewrite ld_world;
  (* 0x858a4: the call of the bcmp wrapper *)
  step;
  apply evtF_done; exists m0; do 2 eexists;
  (split; [reflexivity|]); (split; [exact MU1|]); (split; [assumption|]);
  (split; [exact ST | exact FR]).
Qed.

(* ---- the call's return to the `ret` (0x858a8 .. 0x85928) ---- *)

Lemma csd_run_ret_F :
  forall (RNG : ExecF.footprint)
         (ra2 sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (c2 c1 c0 cra : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo p d : Z) (NB Bw : list byte),
    (d = 256 \/ d = 280) ->
    0 < p -> p mod 8 = 0 -> p + 72 <= 2 ^ 47 ->
    length NB = 72%nat -> length Bw = Z.to_nat TW.W_LEN ->
    0x10007fff8000 + 32 <= bv_unsigned sp -> bv_unsigned sp <= 2 ^ 47 ->
    stk rsegs m lo (bv_unsigned sp + -32) -> lo + 32 <= bv_unsigned sp ->
    rw_cells rsegs m (bv_unsigned sp + -32) (csd_fr c2 c1 c0 cra) ->
    (p + 72 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= p) ->
    TW.u_at NB 64 4 = TW.u_at Bw (TW.OFF_OW + (d + 16)) 4 ->
    TW.u_at NB 68 2 = TW.u_at Bw (TW.OFF_OW + (d + 20)) 2 ->
    bytes_at rsegs m p NB ->
    bytes_at rsegs m (TB_OW + (d + 16)) (TW.sub Bw (TW.OFF_OW + (d + 16)) 4) ->
    bytes_at rsegs m (TB_OW + (d + 20)) (TW.sub Bw (TW.OFF_OW + (d + 20)) 2) ->
    mrd rsegs m (wa ((p + 64) / 8 + ASAN_K)) = Some (Z_to_bv 8 0) ->
    mrd rsegs m (wa ((TB_OW + d + 16) / 8 + ASAN_K)) = Some (Z_to_bv 8 0) ->
    ExecF.rng RNG (bv_unsigned sp + -32) 32 ->
    ExecF.rng RNG TB_OW 304 ->
    ExecF.rng RNG p 72 ->
    ExecF.rng RNG ((p + 64) / 8 + ASAN_K) 1 ->
    ExecF.rng RNG ((TB_OW + d + 16) / 8 + ASAN_K) 1 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (r10 r11 r12 spx : word),
         ms' = MS (mkR cra spx gp tp t0 t1 t2 c0 c1 r10 r11 r12 a3 a4 a5 a6 a7 c2
                       s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc cra) fc None m (seg_rom rsegs) /\
         bv_unsigned spx = bv_unsigned sp /\ stk rsegs m lo (bv_unsigned sp))
      (MS (mkR ra2 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2
               (Z_to_bv 64 p) (Z_to_bv 64 (TB_OW + d)) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 ASAN_K) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CSD_RET) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra2 sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    c2 c1 c0 cra F fc m lo p d NB Bw HD HP0 HP8 HPHI LNB LBw HSP HSPT ST HLO FR HOFFP HC HR
    BNB BDC BDR SH64 SHDC RFR ROW RP RS64 RSDC.
  pose proof (u64_range sp) as Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  assert (HDB : 256 <= d <= 280) by (destruct HD as [ Hd0 | Hd0 ]; rewrite Hd0; lia).
  pose proof (rng_sub' _ _ _ (TB_OW + (d + 16)) 4 ROW ltac:(unfold TB_OW; lia)) as RWDC.
  pose proof (rng_sub' _ _ _ (TB_OW + (d + 20)) 2 ROW ltac:(unfold TB_OW; lia)) as RWDR.
  unfold ASAN_K, TB_OW in *. unfold csd_fr in FR.
  assert (Up : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  remember (Z_to_bv 64 p) as pw eqn:Epw. clear Epw. subst p.
  assert (LDC : length (TW.sub Bw (TW.OFF_OW + (d + 16)) 4) = 4%nat)
    by (apply csd_lsub; [exact LBw | unfold TW.OFF_OW; lia | unfold TW.OFF_OW, TW.W_LEN; lia]).
  assert (LDR : length (TW.sub Bw (TW.OFF_OW + (d + 20)) 2) = 2%nat)
    by (apply csd_lsub; [exact LBw | unfold TW.OFF_OW; lia | unfold TW.OFF_OW, TW.W_LEN; lia]).
  assert (HCS : TW.s32_at NB 64 = TW.s32_at Bw (TW.OFF_OW + (d + 16)))
    by (unfold TW.s32_at; rewrite HC; reflexivity).
  csd_pc.
  (* 0x858a8: the wrapper answered 0, so the trap is not taken *)
  step. csd_br false.
  (* 0x858ac .. 0x858bc: the instrumented check of the 4-byte load at p + 64 *)
  step. gen_addi pw w64 U64.
  pose proof (rng_sub' _ _ _ (bv_unsigned w64) 4 RP ltac:(lia)) as RW64.
  step. gen_shr w64 h64 H64. rewrite U64 in H64.
  step. gen_addi h64 k64 K64. rewrite H64 in K64.
  pose proof (rng_sub' _ _ _ (bv_unsigned k64) 1 RS64 ltac:(lia)) as RK64.
  pose proof (rdw0 m k64 _ _ SH64 ltac:(lia)) as R64. step. clear R64.
  step. csd_br false.
  (* the two branches of g, so that every address inside OW is a literal *)
  destruct HD as [ Hd1 | Hd1 ]; rewrite Hd1 in *; clear Hd1;
  (* 0x858c0 .. 0x858cc: a1 = OW.dn[g].counter's address and its check *)
  step;
  do 2 step;
  (pose proof (rd1 m _ _ SHDC) as RDSC);
  step; clear RDSC;
  (* 0x858d0: a0 = n->counter *)
  (pose proof (csd_rd_sub m w64 _ NB 64 4 BNB ltac:(lia) ltac:(rewrite LNB; lia) ltac:(lia)) as RD64);
  step; clear RD64; rewrite lw_world;
  (* 0x858d4: the shadow byte is 0 *)
  step; csd_br false;
  (* 0x858d8: a1 = OW.dn[g].counter *)
  (pose proof (csd_rd m _ _ 4 BDC LDC) as RDDC);
  step; clear RDDC; rewrite lw_world;
  (* 0x858dc: the two differ goes to the trap; the model makes them equal *)
  step; csd_bne HCS;
  (* 0x858e0 .. 0x858f0: the instrumented check of the 2-byte load at p + 68 *)
  step; gen_addi pw w68 U68;
  (pose proof (rng_sub' _ _ _ (bv_unsigned w68) 2 RP ltac:(lia)) as RW68);
  step; gen_shr w68 h68 H68; rewrite U68 in H68;
  step; gen_addi h68 k68 K68; rewrite H68 in K68;
  (pose proof (rng_sub' _ _ _ (bv_unsigned k68) 1 RS64 ltac:(Z.div_mod_to_equations; lia)) as RK68);
  (pose proof (rdw0 m k68 _ _ SH64 ltac:(Z.div_mod_to_equations; lia)) as R68);
  step; clear R68;
  step; csd_br false;
  (* 0x858f4 .. 0x85900: s1 = OW.dn[g].retry's address and its check *)
  do 3 step;
  (pose proof (rd1 m _ _ SHDC) as RDSR);
  step; clear RDSR;
  (* 0x85904: a0 = n->retry *)
  (pose proof (csd_rd_sub m w68 _ NB 68 2 BNB ltac:(lia) ltac:(rewrite LNB; lia) ltac:(lia)) as RD68);
  step; clear RD68; rewrite lhu_world;
  step; csd_br false;
  (* 0x8590c: a1 = OW.dn[g].retry *)
  (pose proof (csd_rd m _ _ 2 BDR LDR) as RDDR);
  step; clear RDDR; rewrite lhu_world;
  step; csd_bne HR;
  (* 0x85914 .. 0x85928: the epilogue *)
  do 5 step;
  release_frame FR ST (bv_unsigned sp);
  step;
  apply evtF_done; do 4 eexists;
  (split; [reflexivity|]);
  (split; [rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia | exact ST]).
Qed.
