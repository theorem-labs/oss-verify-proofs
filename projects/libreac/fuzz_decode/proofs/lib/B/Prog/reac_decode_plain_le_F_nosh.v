(* reac_decode_plain_le: the footprint contract WITHOUT its `shadow_rw m` premise, image B.

   reac_decode_plain_le_contract_F_nosh is reac_decode_plain_le_contract_F (reac_decode_plain_le_F_c.v, frozen, untouched) with the premise `shadow_rw m` (every shadow
   byte present; lib/B/AsanCells.v:32) removed and nothing else changed. reac_decode_plain_le_holds_F_nosh is proved by the SAME
   script as reac_decode_plain_le_holds_F (reac_decode_plain_le_F.v), with only the hypothesis name SRW dropped from its intro / destruct patterns
   and the one `shadow_rw_munch` line that discharged reac_frame_inspect's (now absent) shadow_rw premise removed; it
   takes reac_frame_inspect_contract_F_nosh in place of reac_frame_inspect_contract_F. The original proof never uses SRW:
   its shadow loads read the bytes from the `addressable` premise. This is why callers need not supply whole-band
   shadow presence (a Theorem Labs lane 03:36Z / 03:43Z, same route as a Theorem Labs lane's for reac_braid_encode). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import AsanKA AsanKAProof reac_frame_inspect_c reac_decode_plain_le_c ReacDecodeLib reac_decode_plain_le.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import reac_frame_inspect_F_c reac_frame_inspect_F reac_decode_plain_le_F_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import reac_decode_plain_le_F.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import reac_frame_inspect_F_nosh.

Definition reac_decode_plain_le_contract_F_nosh : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte)
         (raw mode out nch ns lo : Z),
    a0 = Z_to_bv 64 raw -> a2 = Z_to_bv 64 mode -> a3 = Z_to_bv 64 out ->
    0 <= raw < 2^64 -> 0 <= mode < 2^64 -> 0 <= out < 2^64 ->
    (bv_unsigned a1 = 1492 -> length bs = 1492%nat /\ bytes_at rsegs m raw bs) ->
    -2^31 <= nch < 2^31 -> -2^31 <= ns < 2^31 ->
    bytes_at rsegs m (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns)) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_DECODE_PLAIN_LE_D <= bv_unsigned sp ->
    (bv_unsigned a1 = 1492 -> off_stk sp REAC_DECODE_PLAIN_LE_D raw 1492) ->
    off_stk sp REAC_DECODE_PLAIN_LE_D (mode + 4) 8 ->
    (plain_ok (bv_unsigned a1) bs nch ns = true ->
       wr_at rsegs m out (3 * nch * ns) /\ out + 3 * nch * ns < 2^64 /\
       (out + 3 * nch * ns <= raw \/ raw + 1492 <= out) /\
       off_stk sp REAC_DECODE_PLAIN_LE_D out (3 * nch * ns)) ->
    app_mem (bv_unsigned sp - REAC_DECODE_PLAIN_LE_D) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m -> off_stk sp REAC_DECODE_PLAIN_LE_D GOT_CELL_K (MIDEND + 8 - GOT_CELL_K) ->
    (bv_unsigned a1 = 1492 -> addressable m raw 1492) ->
    (inspect_wf (bv_unsigned a1) bs = true -> addressable m (mode + 4) 8) ->
    (plain_ok (bv_unsigned a1) bs nch ns = true -> addressable m out (3 * nch * ns)) ->
    (bv_unsigned a1 = 1492 -> raw <> 0) ->
    (inspect_wf (bv_unsigned a1) bs = true -> mode <> 0 /\ mode mod 4 = 0) ->
    (plain_ok (bv_unsigned a1) bs nch ns = true -> out <> 0) ->
    ExecF.rng RNG (bv_unsigned sp - REAC_DECODE_PLAIN_LE_D) REAC_DECODE_PLAIN_LE_D ->
    ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    (bv_unsigned a1 = 1492 ->
       ExecF.rng RNG raw 1492 /\ ExecF.rng RNG (raw / 8 + ASAN_K) ((raw + 1491) / 8 - raw / 8 + 1)) ->
    (inspect_wf (bv_unsigned a1) bs = true ->
       ExecF.rng RNG (mode + 4) 8 /\
       ExecF.rng RNG ((mode + 4) / 8 + ASAN_K) ((mode + 11) / 8 - (mode + 4) / 8 + 1)) ->
    (plain_ok (bv_unsigned a1) bs nch ns = true ->
       ExecF.rng RNG out (3 * nch * ns) /\
       ExecF.rng RNG (out / 8 + ASAN_K) ((out + 3 * nch * ns - 1) / 8 - out / 8 + 1)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1
                       (Z_to_bv 64 (if plain_ok (bv_unsigned a1) bs nch ns then ns else -1))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         (if plain_ok (bv_unsigned a1) bs nch ns
          then munch [(bv_unsigned sp - REAC_DECODE_PLAIN_LE_D, bv_unsigned sp); (out, out + 3 * nch * ns)] m m' /\
               bytes_at rsegs m' out (plain_out bs nch ns)
          else munch [(bv_unsigned sp - REAC_DECODE_PLAIN_LE_D, bv_unsigned sp)] m m'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_DECODE_PLAIN_LE) fc None m (seg_rom rsegs)).

Theorem reac_decode_plain_le_holds_F_nosh : reac_frame_inspect_contract_F_nosh -> reac_decode_plain_le_contract_F_nosh.
Proof.
  intros HI. unfold reac_decode_plain_le_contract_F_nosh, REAC_DECODE_PLAIN_LE, REAC_DECODE_PLAIN_LE_D.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m bs raw mode out nch ns lo E0 E2 E3 Rraw Rmode Rout HB Rnch Rns HM ST LO DR DM HO APS1 APS2 CELLS DC AR AM AO
    NR NM NO RSTK RGC RCK HRAW HMODE HOUT.
  subst a0 a2 a3.
  pose proof (u64_range sp) as Rsp.
  assert (Hlo : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold GOT_CELL_K, CELL_K in RGC, RCK.
  pose proof (conj HM CELLS) as PK. clear HM CELLS.
  carve_frame 48%nat ST.
  do 6 step.
  destruct PK as (HM & CELLS).
  unfold off_stk, GOT_CELL_K, MIDEND in DC.
  curmemF ltac:(fun mm => assert (CELLS1 : asan_cells mm)
    by (eapply asan_cells_munch; [exact CELLS | exact MU | unfold MIDEND, GOT_CELL_K; lia])).
  pose proof CELLS1 as (CK & GCK & _).
  unfold CELL_K, GOT_CELL_K, ASAN_K in CK, GCK.
  pose proof (rd_all _ _ _ GCK) as RDG. rewrite length_le8 in RDG.
  pose proof (rd_all _ _ _ CK) as RDS. rewrite length_le8 in RDS.
  do 3 step. step. step. clear RDG RDS CK GCK. step. step.
  curmemF ltac:(fun mm => eapply ExecF.evtF_cut;
    [eapply (HI RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm bs lo) |]).
  { rewrite unsigned_lit by lia. exact ST. }
  { unfold REAC_FRAME_INSPECT_FRAME. rewrite unsigned_lit by lia. lia. }
  { unfold REAC_FRAME_INSPECT_FRAME. intros L. destruct (HB L) as [LEN BB]. specialize (DR L). specialize (AR L).
    unfold off_stk in DR. rewrite (unsigned_lit raw) by lia. rewrite unsigned_lit by lia.
    pose proof (bytes_at_bound _ _ _ _ BB) as BBB. rewrite LEN in BBB.
    split; [exact LEN|]. split; [eapply bytes_tp; [exact MU | rewrite LEN; lia | exact BB]|].
    split; [exact (NR L)|].
    split; [unfold off_stk; rewrite unsigned_lit by lia; lia|].
    split; [replace (bv_unsigned sp + -48 - 16) with (bv_unsigned sp - 64) by lia; exact APS1|].
    split; [apply (app_win (bv_unsigned sp) 64); [lia | exact APS1 | exact APS2 | lia]|].
    split; [exact CELLS1|].
    split; [unfold off_stk, GOT_CELL_K; rewrite unsigned_lit by lia; lia|].
    split; [unfold off_stk, CELL_K; rewrite unsigned_lit by lia; lia|].
    eapply addr_win; [exact AR | exact MU | lia | exact APS1 | exact APS2]. }
  { unfold REAC_FRAME_INSPECT_FRAME. rewrite unsigned_lit by lia. apply (ExecF.rng_sub _ _ _ _ _ RSTK); lia. }
  { intros L. destruct (HRAW L) as [RR RSR]. rewrite (unsigned_lit raw) by lia.
    split; [exact RGC|]. split; [exact RCK|].
    split; [apply (ExecF.rng_sub _ _ _ _ _ RR); lia|].
    split; [apply (ExecF.rng_sub _ _ _ _ _ RR); lia|].
    split; apply (ExecF.rng_sub _ _ _ _ _ RSR); Z.div_mod_to_equations; lia. }
  intros ms' (a1' & a2' & a3' & a4' & m2 & -> & MU2 & WM2 & ST2).
  replace (ret_pc (Z_to_bv 64 531136)) with (Z_to_bv 64 531136) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  unfold REAC_FRAME_INSPECT_FRAME in MU2, ST2. rewrite unsigned_lit in MU2, ST2 by lia.
  assert (MU0 : munch [(bv_unsigned sp + -64, bv_unsigned sp)] m m2)
    by (eapply munch_trans; [eapply munch_wider; [ | | exact MU]; lia | eapply munch_wider; [ | | exact MU2]; lia]).
  assert (WM0 : wmono rsegs m m2) by (eapply wmono_trans; [exact WM | exact WM2]).
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -48)
     [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 junk))))); C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    by (eapply rw_cells_transport; [exact FR | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize]; split; [lia | exact I]]).
  clear FR MU2 WM2 ST MU WM CELLS1.
  step. rewrite inspect_valid_bit. step. step.
  destruct (inspect_wf (bv_unsigned a1) bs) eqn:W.
  2:{ if_true.
      assert (PO : plain_ok (bv_unsigned a1) bs nch ns = false) by (unfold plain_ok; rewrite W; reflexivity).
      eapply pl_exitF with (r := -1).
      all: first [ exact FR2 | exact ST2 | exact WM0 | lia | exact RSTK
                 | rewrite PO; first [reflexivity | exact MU0] ]. }
  if_false.
  assert (L : bv_unsigned a1 = 1492) by (unfold inspect_wf in W; rewrite !andb_true_iff, !Z.eqb_eq in W; tauto).
  destruct (HB L) as [LEN BB]. specialize (DR L). specialize (AR L). specialize (AM eq_refl).
  specialize (NR L). destruct (NM eq_refl) as [NM0 NM4].
  destruct (HRAW L) as [RR RSR]. destruct (HMODE eq_refl) as [RM RSM].
  unfold off_stk in DR, DM.
  pose proof (bytes_at_bound _ _ _ _ BB) as BBB. rewrite LEN in BBB.
  apply bytes_at_app in HM. destruct HM as [HM1 HM2]. rewrite length_le4 in HM2.
  replace (mode + 4 + Z.of_nat 4) with (mode + 8) in HM2 by lia.
  apply (bytes_tp m m2 _ _ _ _ MU0) in HM1; [| rewrite length_le4; lia].
  apply (bytes_tp m m2 _ _ _ _ MU0) in HM2; [| rewrite length_le4; lia].
  pose proof (bytes_at_bound _ _ _ _ HM2) as HMB. rewrite length_le4 in HMB.
  pose proof (rd_all _ _ _ HM1) as HR1. rewrite length_le4 in HR1.
  pose proof (rd_all _ _ _ HM2) as HR2. rewrite length_le4 in HR2.
  assert (MU0' : munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m2)
    by (eapply munch_wider; [ | | exact MU0]; lia).
  assert (AM2 : addressable m2 (mode + 4) 8)
    by (eapply addr_win; [exact AM | exact MU0' | lia | exact APS1 | exact APS2]).
  step. cnd false.
  step. step. cnd false.
  step. cnd false.
  st. rewrite (land3_0 mode) by lia.
  step. cnd false.
  destruct (addr_four m2 (mode + 4) 8 (mode + 4) AM2 ltac:(lia) ltac:(lia)) as (k1 & MK1 & SK1).
  eapply pb_m1F; [ rewrite unsigned_lit by lia; reflexivity | lia | exact MK1 | exact SK1
    | exact (rng_shadow_byte _ (mode + 4) (mode + 11) (mode + 4) RSM ltac:(lia) ltac:(lia)) | intros y11 y12 y13 ].
  destruct (addr_four m2 (mode + 4) 8 (mode + 8) AM2 ltac:(lia) ltac:(lia)) as (k2 & MK2 & SK2).
  eapply pb_m2F; [ rewrite unsigned_lit by lia; reflexivity | lia | exact MK2 | exact SK2
    | rewrite unsigned_lit by lia; exact HR1
    | exact (rng_shadow_byte _ (mode + 4) (mode + 11) (mode + 8) RSM ltac:(lia) ltac:(lia))
    | rewrite unsigned_lit by lia; apply (ExecF.rng_sub _ _ _ _ _ RM); lia
    | intros z11 z12 z14 Z11 ].
  apply wv in Z11. subst z11.
  rewrite sx32_lit by lia.
  step. rewrite lts0_lit by lia. brq BN.
  2:{ assert (PO : plain_ok (bv_unsigned a1) bs nch ns = false)
        by (apply not_true_iff_false; rewrite plain_ok_spec; lia).
      eapply pl_exitF with (r := -1).
      all: first [ exact FR2 | exact ST2 | exact WM0 | lia | exact RSTK
                 | rewrite PO; first [reflexivity | exact MU0] ]. }
  pose proof (ExecF.rng_sub' _ _ _ (mode + 8) 4 RM ltac:(lia)) as RM8.
  step. rewrite sx32_lit by lia.
  clear RM8.
  step. rewrite lts0_lit by lia. brq BS.
  2:{ assert (PO : plain_ok (bv_unsigned a1) bs nch ns = false)
        by (apply not_true_iff_false; rewrite plain_ok_spec; lia).
      eapply pl_exitF with (r := -1).
      all: first [ exact FR2 | exact ST2 | exact WM0 | lia | exact RSTK
                 | rewrite PO; first [reflexivity | exact MU0] ]. }
  assert (0 <= ns * nch < 2^62) by nia.
  step. step. step. rewrite (unsigned_lit ns), (unsigned_lit nch) by lia. brq BM.
  { assert (PO : plain_ok (bv_unsigned a1) bs nch ns = false)
        by (apply not_true_iff_false; rewrite plain_ok_spec; lia).
      eapply pl_exitF with (r := -1).
      all: first [ exact FR2 | exact ST2 | exact WM0 | lia | exact RSTK
                 | rewrite PO; first [reflexivity | exact MU0] ]. }
  assert (PO : plain_ok (bv_unsigned a1) bs nch ns = true) by (rewrite plain_ok_spec; split; [exact W | lia]).
  destruct (HO PO) as (HW & HoutN & DOR & DOS). specialize (AO PO). specialize (NO PO). unfold off_stk in DOS.
  destruct (HOUT PO) as [RO RSO].
  do 6 step.
  destruct (geom_le nch ns BN BS ltac:(lia)) as (G1 & G2).
  assert (I0 : INV ra sp s0 s1 s2 s3 m bs raw out nch ns lo
                 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 junk))))) m2 0).
  { split; [|split; [exact FR2|split; [exact ST2|split; [|split; [|split; [exact WM0|]]]]]].
    - eapply bytes_tp; [exact MU0' | rewrite LEN; lia | exact BB].
    - eapply wr_at_transport; [exact HW | exact WM0].
    - apply munch_extend. exact MU0.
    - intros i Hi. lia. }
  eapply pl_outerF with (K := Z.to_nat (nch - 0)) (ch := 0) (ra := ra) (sp := sp) (s0 := s0) (s1 := s1) (s2 := s2)
    (s3 := s3) (a1 := a1) (m := m) (bs := bs) (raw := raw) (mode := mode) (out := out) (nch := nch) (ns := ns) (lo := lo)
    (jk := firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 junk))))).
  all: first [ assumption | reflexivity | lia
             | (eapply INV_idx; [exact I0 | lia])
             | (intros x Hx; apply (app_win (bv_unsigned sp) 64); [lia | exact APS1 | exact APS2 | lia])
             | ufin ].
Qed.

(* The twin implies the original: take the footprint that allows every access. *)
