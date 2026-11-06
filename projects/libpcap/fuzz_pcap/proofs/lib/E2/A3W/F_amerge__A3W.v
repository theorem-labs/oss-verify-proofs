(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From Stdlib Require Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AQConst.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanEmbed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_amerge.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AKitR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma firstn_S_snoc : forall {X} (l : list X) i x, nth_error l i = Some x -> firstn (Datatypes.S i) l = firstn i l ++ [x].
Proof.
  intros X l. induction l as [|y l IH]; intros [|i] x H; cbn in *; try discriminate.
  - inversion H. reflexivity.
  - rewrite (IH i x H). reflexivity.
Qed.

Definition amerge_entry : Z := 0x35c84.
Definition amerge_loop : Z := 0x35cbc.     (* [comment removed for export] *)
Definition amerge_copy : Z := 0x35cf4.     (* [comment removed for export] *)
Definition amerge_copied : Z := 0x35d08.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma mcopy_loop_spec : forall RNG (d : nat) (i n SRC DST : Z) (src ws0 : list word)
    ra sp gp tp t0 t1 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 (F : bvmap 5 word) fc (m : amem),
  d = Z.to_nat (n - i) ->
  0 <= i < n -> length src = Z.to_nat n -> (n <= Z.of_nat (length ws0))%Z ->
  u64arr asegs m SRC src ->
  u64arr asegs m DST (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) ws0) ->
  mem_inv asegs m ->
  0 <= SRC -> SRC + 8 * n < 2^47 -> 0 <= DST -> DST + 8 * Z.of_nat (length ws0) < 2^47 ->
  (SRC + 8 * n <= DST \/ DST + 8 * Z.of_nat (length ws0) <= SRC) ->
  rng RNG SRC (8 * n) -> rng RNG DST (8 * n) ->
  evtF asegs RNG (fun ms' => exists t5' m',
      ms' = MS (mkR ra sp gp tp t0 t1 (Z_to_bv 64 (SRC + 8 * n)) s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (DST + 8 * n)) (Z_to_bv 64 (SRC + 8 * n)) t5' t6) F (Z_to_bv 64 amerge_copied) fc None m' (seg_rom asegs)
      /\ munch [(DST, DST + 8 * n)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ u64arr asegs m' SRC src /\ u64arr asegs m' DST (src ++ skipn (Z.to_nat n) ws0))
    (MS (mkR ra sp gp tp t0 t1 (Z_to_bv 64 (SRC + 8 * i)) s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (DST + 8 * i)) (Z_to_bv 64 (SRC + 8 * n)) t5 t6) F (Z_to_bv 64 amerge_copy) fc None m (seg_rom asegs)).
Proof.
  intros RNG d. induction d as [|d IH]; intros until m; intros HD I LS LW SRCA DSTA MI S0 S1 D0 D1 DJ RS RD; [lia|].
  unfold amerge_copy, amerge_copied in *.
  pose proof (munch_refl [(DST, DST + 8 * n)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  destruct (nth_error src (Z.to_nat i)) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; lia].
  assert (LD : length (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) ws0) = length ws0) by (rewrite length_app, length_firstn, length_skipn; lia).
  pose proof (u64arr_read asegs _ _ src i w (wa (SRC + 8 * i)) SRCA NTH ltac:(lia) eq_refl) as RDV.
  assert (RS1 : rng RNG (SRC + 8 * i) 8) by (eapply rng_sub'; [exact RS| lia]).
  assert (RD1 : rng RNG (DST + 8 * i) 8) by (eapply rng_sub'; [exact RD| lia]).
  step. clear RDV RS1.                                   (* [comment removed for export] *)
  zstep.                                                 (* [comment removed for export] *)
  setreg 7 (Z_to_bv 64 (SRC + 8 * (i + 1))) ltac:(f_equal; clear; lia).
  pose proof (u64arr_store_ok asegs m DST _ i (wa (DST + 8 * i)) DSTA ltac:(rewrite LD; lia) eq_refl) as SOK.
  step.                                                  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ ?a (le8 ?v)) _) =>
    let E := lazymatch a with wa ?E => E | Z_to_bv _ ?E => E end in
    pose proof (u64arr_write asegs m DST _ i v DSTA ltac:(rewrite LD; lia)) as DST2;
    replace (DST + 8 * i)%Z with E in DST2 by lia
  end.
  replace (upd (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) ws0) (Z.to_nat i) w)
     with (firstn (Z.to_nat (i + 1)) src ++ skipn (Z.to_nat (i + 1)) ws0) in DST2.
  2:{ rewrite upd_firstn_skipn by (rewrite LD; lia).
      rewrite firstn_app, firstn_firstn, Nat.min_id, length_firstn.
      replace (Z.to_nat i - Nat.min (Z.to_nat i) (length src))%nat with 0%nat by lia. rewrite firstn_O, app_nil_r.
      rewrite skipn_app, length_firstn. replace (Datatypes.S (Z.to_nat i) - Nat.min (Z.to_nat i) (length src))%nat with 1%nat by lia.
      rewrite skipn_skipn. replace (1 + Z.to_nat i)%nat with (Z.to_nat (i + 1)) by lia.
      replace (Z.to_nat (i + 1)) with (Datatypes.S (Z.to_nat i)) at 1 by lia.
      rewrite (firstn_S_snoc _ _ _ NTH), (skipn_all2 (firstn (Z.to_nat i) src)) by (rewrite length_firstn; lia).
      rewrite <- app_assoc. reflexivity. }
  assert (SRC2 : u64arr asegs (write_to_mem m (wa (DST + 8 * i)) (le8 w)) SRC src).
  { apply Arr.u64arr_frame; [exact SRCA| lia| rewrite length_le8; lia| rewrite length_le8; lia]. }
  clear DSTA SRCA. store_done. try clear SOK. clear RD1.
  zstep.                                                 (* [comment removed for export] *)
  setreg 28 (Z_to_bv 64 (DST + 8 * (i + 1))) ltac:(f_equal; clear; lia).
  step. if_cases K; zify_cond K.                         (* [comment removed for export] *)
  - (* [comment removed for export] *)
    rewrite ?unsigned_lit in K by lia.
    eapply evtF_mono.
    { eapply (IH (i + 1) n SRC DST src ws0); try eassumption; try lia. }
    cbv beta. intros ms' (t5' & m' & -> & MU2 & WM2 & MI2 & SR3 & DS3).
    exists t5', m'. split; [reflexivity|].
    split; [eapply munch_trans; [exact MU| exact MU2]|]. split; [eapply wmono_trans; [exact WM| exact WM2]|].
    split; [exact MI2|]. split; [exact SR3| exact DS3].
  - (* [comment removed for export] *)
    rewrite ?unsigned_lit in K by lia. assert (EI : i + 1 = n) by lia.
    apply evtF_done. rewrite EI in DST2 |- *. eexists _, _. split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact SRC2|].
    rewrite firstn_all2 in DST2 by lia. exact DST2.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma u64arr_app2 : forall m A ws1 ws2,
  u64arr asegs m A ws1 -> u64arr asegs m (A + 8 * Z.of_nat (length ws1)) ws2 -> u64arr asegs m A (ws1 ++ ws2).
Proof.
  intros m A ws1 ws2 [HB HW] [HB2 HW2]. split.
  - rewrite u64s_app. apply bytes_at_app. split; [exact HB|]. rewrite u64s_length.
    replace (A + Z.of_nat (8 * length ws1)) with (A + 8 * Z.of_nat (length ws1)) by lia. exact HB2.
  - rewrite length_app. (nd_pre HW 3%nat; intros H0 H1 HW; nd_post). (nd_pre HW2 3%nat; intros H2 H3 HW2; nd_post).
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i (8 * Z.of_nat (length ws1))); [apply HW; lia|].
    replace (A + i) with (A + 8 * Z.of_nat (length ws1) + (i - 8 * Z.of_nat (length ws1))) by lia. apply HW2. lia.
Qed.

#[using="Type"] Lemma u64arr_app_inv : forall m A ws1 ws2, u64arr asegs m A (ws1 ++ ws2) ->
  u64arr asegs m A ws1 /\ u64arr asegs m (A + 8 * Z.of_nat (length ws1)) ws2.
Proof.
  intros m A ws1 ws2 [HB HW]. rewrite u64s_app in HB. apply bytes_at_app in HB. destruct HB as [HB1 HB2].
  rewrite u64s_length in HB2. replace (A + Z.of_nat (8 * length ws1)) with (A + 8 * Z.of_nat (length ws1)) in HB2 by lia.
  rewrite length_app in HW. (nd_pre HW 3%nat; intros H0 H1 HW; nd_post).
  split; split; try assumption.
  - split; [lia|]. split; [lia|]. intros i Hi. apply HW. lia.
  - split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + 8 * Z.of_nat (length ws1) + i) with (A + (8 * Z.of_nat (length ws1) + i)) by lia. apply HW. lia.
Qed.

#[using="Type"] Lemma junk_of_u64arr : forall m A ws, u64arr asegs m A ws -> junk_at m A (8 * Z.of_nat (length ws)).
Proof.
  intros m A ws [B W]. exists (u64s ws). split; [split|].
  - cbn. split; [rewrite u64s_length; lia| exact I].
  - cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize Nat.add]. replace (Z.of_nat (Z.to_nat (8 * Z.of_nat (length ws)) + 0)) with (8 * Z.of_nat (length ws)) by lia. exact W.
Qed.

#[using="Type"] Lemma u64arr_of_junk : forall m A n, junk_at m A (8 * n) -> 0 <= n ->
  exists ws, u64arr asegs m A ws /\ length ws = Z.to_nat n.
Proof.
  intros m A n [bs H] Hn. replace (Z.to_nat (8 * n)) with (8 * Z.to_nat n)%nat in H by lia.
  destruct (u64arr_of_CB m A (Z.to_nat n) bs H) as [U L]. exists (words_of_bytes bs). split; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mcore_post (ra sp gp tp s0 s1 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (CUR NXT LST nxn szc szn cc cn ls : Z) (ec en : list word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t2 t3 t4 t5 m',
    ms' = MS (mkR ra sp gp tp (Z_to_bv 64 NXT) (Z_to_bv 64 (cc + cn)) t2 s0 s1 (Z_to_bv 64 LST) a1 a2 (Z_to_bv 64 ls) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x35d28) fc None m' (seg_rom asegs)
    /\ munch [(CUR + 8, CUR + 24); (CUR + 24 + 8 * cc, CUR + 24 + 8 * (cc + cn)); (NXT + 8, NXT + 24)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' CUR [C8 (Z_to_bv 64 NXT); C8 (Z_to_bv 64 (szc + szn - Q_BATCH_BYTES)); C8 (Z_to_bv 64 (cc + cn))]
    /\ u64arr asegs m' (CUR + 24) (ec ++ en)
    /\ junk_at m' (CUR + 24 + 8 * (cc + cn)) (Q_BATCH_BYTES - 24 - 8 * (cc + cn))
    /\ rw_cells asegs m' NXT [C8 (Z_to_bv 64 nxn); C8 (Z_to_bv 64 Q_BATCH_BYTES); C8 (Z_to_bv 64 0)]
    /\ junk_at m' (NXT + 24) (Q_BATCH_BYTES - 24).

Definition mcore_spec__stmt : Prop := forall RNG ra sp gp tp t2 s0 s1 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 (F : bvmap 5 word) fc (m : amem)
    (CUR NXT LST nxn szc szn cc cn ls lf ll lb : Z) (ec en : list word),
  mem_inv asegs m ->
  rw_cells asegs m CUR [C8 (Z_to_bv 64 NXT); C8 (Z_to_bv 64 szc); C8 (Z_to_bv 64 cc)] ->
  u64arr asegs m (CUR + 24) ec -> length ec = Z.to_nat cc ->
  junk_at m (CUR + 24 + 8 * cc) (Q_BATCH_BYTES - 24 - 8 * cc) ->
  rw_cells asegs m NXT [C8 (Z_to_bv 64 nxn); C8 (Z_to_bv 64 szn); C8 (Z_to_bv 64 cn)] ->
  u64arr asegs m (NXT + 24) en -> length en = Z.to_nat cn ->
  junk_at m (NXT + 24 + 8 * cn) (Q_BATCH_BYTES - 24 - 8 * cn) ->
  rw_cells asegs m LST [C8 (Z_to_bv 64 ls); C8 (Z_to_bv 64 lf); C8 (Z_to_bv 64 ll); C8 (Z_to_bv 64 lb)] ->
  Q_BATCH_BYTES <= szc < 2^63 -> 0 <= szn < 2^63 -> 0 <= cc -> 0 <= cn -> cc + cn <= Q_BATCH -> 0 <= nxn < 2^64 -> 0 <= ls < 2^64 ->
  AIMG_HI <= CUR -> CUR + Q_BATCH_BYTES <= ATOP -> AIMG_HI <= NXT -> NXT + Q_BATCH_BYTES <= ATOP ->
  (CUR + Q_BATCH_BYTES <= NXT \/ NXT + Q_BATCH_BYTES <= CUR) ->
  (LST + 32 <= CUR \/ CUR + Q_BATCH_BYTES <= LST) -> (LST + 32 <= NXT \/ NXT + Q_BATCH_BYTES <= LST) -> 0 <= LST -> LST + 32 <= ATOP ->
  a6 = Z_to_bv 64 (2^64 - Q_BATCH_BYTES) -> a7 = Z_to_bv 64 Q_BATCH_BYTES ->
  rng RNG CUR Q_BATCH_BYTES -> rng RNG NXT Q_BATCH_BYTES -> rng RNG LST 32 ->
  evtF asegs RNG (mcore_post ra sp gp tp s0 s1 a1 a2 (Z_to_bv 64 CUR) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 F fc CUR NXT LST nxn szc szn cc cn ls ec en m)
    (MS (mkR ra sp gp tp (Z_to_bv 64 NXT) (Z_to_bv 64 (cn + cc)) t2 s0 s1 (Z_to_bv 64 LST) a1 a2 a3 (Z_to_bv 64 CUR) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 cn) (Z_to_bv 64 cc) t5 t6) F (Z_to_bv 64 0x35ccc) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 4).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 5).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 6).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 7).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 8).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 9).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 10).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 11).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 12).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 13).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 14).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 15).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 16).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 17).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 18).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 19).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 20).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 21).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 22).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 23).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 24).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 25).
Variable F : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 26).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 27).
Variable m : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 28).
Variable CUR : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 29).
Variable NXT : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 30).
Variable LST : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 31).
Variable nxn : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 32).
Variable szc : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 33).
Variable szn : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 34).
Variable cc : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 35).
Variable cn : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 36).
Variable ls : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 37).
Variable lf : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 38).
Variable ll : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 39).
Variable lb : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 40).
Variable ec : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 41).
Variable en : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 42).
#[using="Type"] Lemma mcore_spec__body : ltac:(let T := type of (fun (h : mcore_spec__stmt) => h RNG ra sp gp tp t2 s0 s1 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 F fc m CUR NXT LST nxn szc szn cc cn ls lf ll lb ec en) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t2, (s0, (s1, (a1, (a2, (a3, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t5, (t6, (F, (fc, (m, (CUR, (NXT, (LST, (nxn, (szc, (szn, (cc, (cn, (ls, (lf, (ll, (lb, (ec, en))))))))))))))))))))))))))))))))))))))))))) as _.
 intros MI CC EC LEC JC CN EN LEN JN LS SZC SZN C0 N0 FIT NXN LSR C1 C2 N1 N2 DCN DLC DLN L1 L2 -> -> RC RN RL.
  unfold AIMG_HI, Q_BATCH_BYTES, Q_BATCH in *.
  pose proof (munch_refl [(CUR + 8, CUR + 24); (CUR + 24 + 8 * cc, CUR + 24 + 8 * (cc + cn)); (NXT + 8, NXT + 24)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  step.                                                   (* [comment removed for export] *)
  zstep.                                                  (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0.                        (* [comment removed for export] *)
  { exfalso. revert K0 SZC. clear. intros K0 SZC. rewrite ?unsigned_lit in K0 by lia. rewrite Z.shiftr_div_pow2 in K0 by lia.
    rewrite ?unsigned_lit in K0 by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations. lia. }
  clear K0.
  step. if_cases KZ; zify_cond KZ.                        (* [comment removed for export] *)
  - (* [comment removed for export] *)
    rewrite ?unsigned_lit in KZ by lia.
    assert (cn = 0) by lia. subst cn.
    assert (en = []) by (destruct en; [reflexivity| cbn in LEN; lia]). subst en.
    step.                                                 (* [comment removed for export] *)
    zstep.                                                (* [comment removed for export] *)
    step.                                                 (* [comment removed for export] *)
    zstep.                                                (* [comment removed for export] *)
    setreg 7 (Z_to_bv 64 (szc + szn - 8192)) ltac:(apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.pow_pos Pos.iter Z.mul]; 
                                                    clear -SZC SZN; Z.div_mod_to_equations; lia).
    destruct JC as [jc JC]. destruct JN as [jn JN].
    step.                                                 (* [comment removed for export] *)
    step.                                                 (* [comment removed for export] *)
    step.                                                 (* [comment removed for export] *)
    step.                                                 (* [comment removed for export] *)
    apply evtF_done. unfold mcore_post, Q_BATCH_BYTES. rewrite !Z.add_0_r. replace (cc + 0) with cc in MU by lia.
    replace (0 + cc) with cc in * by lia.
    replace (NXT + 24 + 8 * 0) with (NXT + 24) in JN by lia. replace (8192 - 24 - 8 * 0) with (8192 - 24) in JN by lia.
    do 4 eexists. exists m1. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact CC|].
    split; [rewrite app_nil_r; exact EC|]. split; [exists jc; exact JC|]. split; [exact CN|]. exists jn; exact JN.
  - (* [comment removed for export] *)
    rewrite ?unsigned_lit in KZ by lia.
    do 6 zstep.                                           (* [comment removed for export] *)
    setreg 7 (Z_to_bv 64 (NXT + 24 + 8 * 0)) ltac:(f_equal; clear; lia).
    setreg 28 (Z_to_bv 64 (CUR + 24 + 8 * cc + 8 * 0)) ltac:(rewrite ?Z.shiftl_mul_pow2 by (clear; lia); f_equal; clear -C0; lia).
    setreg 29 (Z_to_bv 64 (NXT + 24 + 8 * cn)) ltac:(rewrite ?Z.shiftl_mul_pow2 by (clear; lia); f_equal; clear -N0; lia).
    replace (8192 - 24 - 8 * cc) with (8 * cn + (8192 - 24 - 8 * cc - 8 * cn)) in JC by lia.
    destruct (junk_split m _ _ _ JC ltac:(lia) ltac:(lia)) as [J1 J2]. clear JC.
    (nd_pre (u64arr_of_junk m _ cn J1 ltac:(lia)) 3%nat; intros ws0 WS0 LWS0; nd_post). clear J1.
    destruct J2 as [jc J2]. destruct JN as [jn JN].
    eapply evtF_cut.
    { eapply (mcopy_loop_spec RNG _ 0 cn (NXT + 24) (CUR + 24 + 8 * cc) en ws0); try reflexivity.
      - lia.
      - exact LEN.
      - rewrite LWS0. lia.
      - exact EN.
      - cbn [Z.to_nat firstn skipn app]. exact WS0.
      - exact MI.
      - lia. - lia. - lia.
      - rewrite LWS0. lia.
      - rewrite LWS0. destruct DCN; [right| left]; lia.
      - eapply rng_sub'; [exact RN| lia].
      - eapply rng_sub'; [exact RC| lia]. }
    cbv beta. intros ms' (t5' & m3 & -> & MU3 & WM3 & MI3 & SR3 & DS3).
    xport CC MU3 WM3 ltac:(clear -C0 N0; lia).
    xport CN MU3 WM3 ltac:(clear -C0 N0 FIT DCN; lia).
    xport LS MU3 WM3 ltac:(clear -C0 N0 FIT DLC; lia).
    xport EC MU3 WM3 ltac:(rewrite ?LEC; clear -C0 N0; lia).
    xport J2 MU3 WM3 ltac:(clear -C0 N0 FIT; lia).
    xport JN MU3 WM3 ltac:(clear -C0 N0 FIT DCN; lia).
    clear MI WS0 MU WM. box MU3.
    rewrite skipn_all2 in DS3 by (rewrite LWS0; lia). rewrite app_nil_r in DS3. box DS3. box SR3.
    snapshot [(CUR + 8, CUR + 24); (NXT + 8, NXT + 24)]%Z MUs WMs.
    step.                                                 (* [comment removed for export] *)
    zstep.                                                (* [comment removed for export] *)
    step.                                                 (* [comment removed for export] *)
    zstep.                                                (* [comment removed for export] *)
    setreg 7 (Z_to_bv 64 (szc + szn - 8192)) ltac:(apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.pow_pos Pos.iter Z.mul];
                                                    clear -SZC SZN; Z.div_mod_to_equations; lia).
    step.                                                 (* [comment removed for export] *)
    step.                                                 (* [comment removed for export] *)
    step.                                                 (* [comment removed for export] *)
    step.                                                 (* [comment removed for export] *)
    apply evtF_done. unfold mcore_post, Q_BATCH_BYTES. unbox MU3.
    unbox DS3. xport DS3 MUs WMs ltac:(rewrite ?LEN; clear -C0 N0 DCN FIT; lia).
    unbox SR3. xport SR3 MUs WMs ltac:(rewrite ?LEN; clear -C0 N0 DCN FIT; lia).
    replace (cn + cc) with (cc + cn) in * by lia.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] =>
      assert (MUF : munch [(CUR + 8, CUR + 24); (CUR + 24 + 8 * cc, CUR + 24 + 8 * (cc + cn)); (NXT + 8, NXT + 24)]%Z m mx)
        by (eapply (munch_trans_w _ _ _ _ _ _ MU3 MUs); solve_sub_fpw ltac:(clear -C0 N0; lia)) end.
    do 4 eexists. eexists. split; [reflexivity|].
    split; [exact MUF|]. split; [first [exact WM3 | eapply wmono_trans; [exact WM3| exact WMs]]|]. split; [assumption|]. split; [exact CC|].
    split. { apply u64arr_app2; [exact EC|]. rewrite LEC, Z2Nat.id by lia. exact DS3. }
    split. { exists jc. replace (CUR + 24 + 8 * (cc + cn)) with (CUR + 24 + 8 * cc + 8 * cn) by lia.
             replace (8192 - 24 - 8 * (cc + cn)) with (8192 - 24 - 8 * cc - 8 * cn) by lia. exact J2. }
    split; [exact CN|].
    replace (8192 - 24) with (8 * cn + (8192 - 24 - 8 * cn)) by lia. apply junk_merge; [| | lia| lia].
    + replace (8 * cn) with (8 * Z.of_nat (length en)) by (rewrite LEN; lia). apply junk_of_u64arr. exact SR3.
    + exists jn. exact JN.
Qed.
End Zd1.
#[using="Type"] Lemma mcore_spec : ltac:(let t := eval cbv delta [mcore_spec__stmt] in mcore_spec__stmt in exact t).
Proof. exact mcore_spec__body. Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition munlink_post (tfull : bool) (ra sp gp tp t0 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (CUR NXT LST TMP TL nxn szc cc szn cn ls lf ll lb tn tf tb ex : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t1 t2 a3 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 LST) (Z_to_bv 64 TMP) (Z_to_bv 64 (ex + Q_BATCH_BYTES)) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x35d98) fc None m' (seg_rom asegs)
    /\ munch ([(CUR, CUR + 8); (NXT, NXT + 8); (LST, LST + 24); (TMP, TMP + 32)] ++ (if tfull then [(TL, TL + 8)] else []))%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' CUR [C8 (Z_to_bv 64 nxn); C8 (Z_to_bv 64 szc); C8 (Z_to_bv 64 cc)]
    /\ rw_cells asegs m' NXT [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 szn); C8 (Z_to_bv 64 cn)]
    /\ rw_cells asegs m' LST [C8 (Z_to_bv 64 (ls - 1)); C8 (Z_to_bv 64 lf); C8 (Z_to_bv 64 (if ll =? NXT then CUR else ll)); C8 (Z_to_bv 64 lb)]
    /\ rw_cells asegs m' TMP [C8 (Z_to_bv 64 (tn + 1)); C8 (Z_to_bv 64 (if tfull then tf else NXT)); C8 (Z_to_bv 64 NXT); C8 (Z_to_bv 64 (tb + Q_BATCH_BYTES))]
    /\ (if tfull then rw_cells asegs m' TL [C8 (Z_to_bv 64 NXT)] else True).

Definition munlink_spec__stmt : Prop := forall (tfull : bool) RNG ra sp gp tp t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : amem)
    (CUR NXT LST TMP TL nxn szc cc szn cn ls lf ll lb tn tf tl tb ex tlx : Z),
  mem_inv asegs m ->
  rw_cells asegs m CUR [C8 (Z_to_bv 64 NXT); C8 (Z_to_bv 64 szc); C8 (Z_to_bv 64 cc)] ->
  rw_cells asegs m NXT [C8 (Z_to_bv 64 nxn); C8 (Z_to_bv 64 szn); C8 (Z_to_bv 64 cn)] ->
  rw_cells asegs m LST [C8 (Z_to_bv 64 ls); C8 (Z_to_bv 64 lf); C8 (Z_to_bv 64 ll); C8 (Z_to_bv 64 lb)] ->
  rw_cells asegs m TMP [C8 (Z_to_bv 64 tn); C8 (Z_to_bv 64 tf); C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 tb)] ->
  (if tfull then tl = TL else True) -> 0 <= tl < 2^64 ->
  0 < ls < 2^63 -> 0 <= ll < 2^64 -> 0 <= nxn < 2^64 -> 0 <= tn < 2^63 -> 0 <= tf < 2^64 -> 0 <= tb -> tb + Q_BATCH_BYTES < 2^63 ->
  0 <= ex -> ex + Q_BATCH_BYTES < 2^63 ->
  AIMG_HI <= CUR -> CUR + Q_BATCH_BYTES <= ATOP -> AIMG_HI <= NXT -> NXT + Q_BATCH_BYTES <= ATOP ->
  0 <= LST -> LST + 32 <= ATOP -> 0 <= TMP -> TMP + 32 <= 2^47 ->
  (CUR + Q_BATCH_BYTES <= NXT \/ NXT + Q_BATCH_BYTES <= CUR) ->
  (LST + 32 <= CUR \/ CUR + Q_BATCH_BYTES <= LST) -> (LST + 32 <= NXT \/ NXT + Q_BATCH_BYTES <= LST) ->
  (TMP + 32 <= CUR \/ CUR + Q_BATCH_BYTES <= TMP) -> (TMP + 32 <= NXT \/ NXT + Q_BATCH_BYTES <= TMP) ->
  (TMP + 32 <= LST \/ LST + 32 <= TMP) ->
  (if tfull then 0 < tn /\ rw_cells asegs m TL [C8 (Z_to_bv 64 tlx)] /\ AIMG_HI <= TL /\ TL + Q_BATCH_BYTES <= ATOP
                 /\ (TL + Q_BATCH_BYTES <= CUR \/ CUR + Q_BATCH_BYTES <= TL) /\ (TL + Q_BATCH_BYTES <= NXT \/ NXT + Q_BATCH_BYTES <= TL)
                 /\ (LST + 32 <= TL \/ TL + Q_BATCH_BYTES <= LST) /\ (TMP + 32 <= TL \/ TL + Q_BATCH_BYTES <= TMP) /\ rng RNG TL 8
   else tn = 0) ->
  a7 = Z_to_bv 64 Q_BATCH_BYTES ->
  rng RNG CUR Q_BATCH_BYTES -> rng RNG NXT Q_BATCH_BYTES -> rng RNG LST 32 -> rng RNG TMP 32 ->
  evtF asegs RNG (munlink_post tfull ra sp gp tp (Z_to_bv 64 NXT) s0 s1 (Z_to_bv 64 CUR) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
                     CUR NXT LST TMP TL nxn szc cc szn cn ls lf ll lb tn tf tb ex m)
    (MS (mkR ra sp gp tp (Z_to_bv 64 NXT) t1 t2 s0 s1 (Z_to_bv 64 LST) (Z_to_bv 64 TMP) (Z_to_bv 64 ex) (Z_to_bv 64 ls) (Z_to_bv 64 CUR) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x35d28) fc None m (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable tfull : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 9).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 10).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 11).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 12).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 13).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 14).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 15).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 16).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 17).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 18).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 19).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 20).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 21).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 22).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 23).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 24).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 25).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 26).
Variable F : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 27).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 28).
Variable m : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 29).
Variable CUR : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 30).
Variable NXT : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 31).
Variable LST : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 32).
Variable TMP : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 33).
Variable TL : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 34).
Variable nxn : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 35).
Variable szc : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 36).
Variable cc : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 37).
Variable szn : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 38).
Variable cn : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 39).
Variable ls : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 40).
Variable lf : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 41).
Variable ll : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 42).
Variable lb : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 43).
Variable tn : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 44).
Variable tf : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 45).
Variable tl : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 46).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 47).
Variable ex : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 48).
Variable tlx : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 49).
#[using="Type"] Lemma munlink_spec__body : ltac:(let T := type of (fun (h : munlink_spec__stmt) => h tfull RNG ra sp gp tp t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m CUR NXT LST TMP TL nxn szc cc szn cn ls lf ll lb tn tf tl tb ex tlx) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (tfull, (RNG, (ra, (sp, (gp, (tp, (t1, (t2, (s0, (s1, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (CUR, (NXT, (LST, (TMP, (TL, (nxn, (szc, (cc, (szn, (cn, (ls, (lf, (ll, (lb, (tn, (tf, (tl, (tb, (ex, tlx)))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros MI CC CN LS TM TLE TLR LSR LLR NXN TN TF TB TB2 EX EX2 C1 C2 N1 N2 L1 L2 T1 T2 DCN DLC DLN DTC DTN DTL TFULL -> RC RN RL RT.
  unfold AIMG_HI, Q_BATCH_BYTES in *.
  destruct tfull.
  - (nd_pre TFULL 9%nat; intros TN1 TLC TL1 TL2 DTLC DTLN DTLL DTLT RTL; nd_post). subst tl.
    pose proof (munch_refl ([(CUR, CUR + 8); (NXT, NXT + 8); (LST, LST + 24); (TMP, TMP + 32)] ++ [(TL, TL + 8)])%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM. cbn [app] in MU.
    step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.   (* [comment removed for export] *)
    step. step. step.                                     (* [comment removed for export] *)
    step. if_cases KL; zify_cond KL.                      (* [comment removed for export] *)
    + (* [comment removed for export] *)
      rewrite ?unsigned_lit in KL by lia.
      step. zstep. step. step. step.                      (* [comment removed for export] *)
      step. if_cases KT; zify_cond KT; [| exfalso; rewrite ?unsigned_lit in KT by lia; lia]. clear KT.   (* [comment removed for export] *)
      step. step. zstep. step.                            (* [comment removed for export] *)
      step. step. step. zstep. zstep. step.               (* [comment removed for export] *)
      apply evtF_done. unfold munlink_post. cbn [app].
      replace (ll =? NXT) with true by (symmetry; apply Z.eqb_eq; lia).
      replace (ls + -1) with (ls - 1) in LS by lia.
      do 3 eexists. eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact CC|]. split; [exact CN|]. split; [exact LS|]. split; [exact TM| exact TLC].
    + (* [comment removed for export] *)
      rewrite ?unsigned_lit in KL by lia.
      zstep. step. step. step.                            (* [comment removed for export] *)
      step. if_cases KT; zify_cond KT; [exfalso; rewrite ?unsigned_lit in KT by lia; lia|]. clear KT.   (* [comment removed for export] *)
      step. step. zstep. step.                            (* [comment removed for export] *)
      step. step. step. zstep. zstep. step.               (* [comment removed for export] *)
      apply evtF_done. unfold munlink_post. cbn [app].
      replace (ll =? NXT) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (ls + -1) with (ls - 1) in LS by lia.
      do 3 eexists. eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact CC|]. split; [exact CN|]. split; [exact LS|]. split; [exact TM| exact TLC].
  - subst tn. clear TLE.
    pose proof (munch_refl ([(CUR, CUR + 8); (NXT, NXT + 8); (LST, LST + 24); (TMP, TMP + 32)] ++ [])%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM. cbn [app] in MU.
    step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.   (* [comment removed for export] *)
    step. step. step.                                     (* [comment removed for export] *)
    step. if_cases KL; zify_cond KL.                      (* [comment removed for export] *)
    + rewrite ?unsigned_lit in KL by lia.
      step. zstep. step. step. step.                      (* [comment removed for export] *)
      step. if_cases KT; zify_cond KT; [exfalso; rewrite ?unsigned_lit in KT by lia; lia|]. clear KT.   (* [comment removed for export] *)
      step. zstep.                                        (* [comment removed for export] *)
      step. step. step. zstep. zstep. step.               (* [comment removed for export] *)
      apply evtF_done. unfold munlink_post. cbn [app].
      replace (ll =? NXT) with true by (symmetry; apply Z.eqb_eq; lia).
      replace (ls + -1) with (ls - 1) in LS by lia. change (0 + 1) with 1.
      do 3 eexists. eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact CC|]. split; [exact CN|]. split; [exact LS|]. split; [exact TM| exact I].
    + rewrite ?unsigned_lit in KL by lia.
      zstep. step. step. step.                            (* [comment removed for export] *)
      step. if_cases KT; zify_cond KT; [| exfalso; rewrite ?unsigned_lit in KT by lia; lia]. clear KT.   (* [comment removed for export] *)
      step. zstep.                                        (* [comment removed for export] *)
      step. step. step. zstep. zstep. step.               (* [comment removed for export] *)
      apply evtF_done. unfold munlink_post. cbn [app].
      replace (ll =? NXT) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (ls + -1) with (ls - 1) in LS by lia. change (0 + 1) with 1.
      do 3 eexists. eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact CC|]. split; [exact CN|]. split; [exact LS|]. split; [exact TM| exact I].
Qed.
End Zd2.
#[using="Type"] Lemma munlink_spec : ltac:(let t := eval cbv delta [munlink_spec__stmt] in munlink_spec__stmt in exact t).
Proof. exact munlink_spec__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bq := (abatch * qbatchc)%type.
Definition baddr (L : alayout) (x : bq) : Z := abatch_addr L (qb_slot (snd x)).
(* [comment removed for export] *)
Definition bq_merge (cur nx : bq) : bq :=
  (mkABatch (b_count (fst cur) + b_count (fst nx)) (b_size (fst cur) + (b_size (fst nx) - Q_BATCH_BYTES)) (b_chunks (fst nx) ++ b_chunks (fst cur)),
   mkQB (qb_slot (snd cur)) (qb_ks (snd nx) ++ qb_ks (snd cur))).
Definition bq_empty (nx : bq) : bq := (mkABatch 0 Q_BATCH_BYTES [], mkQB (qb_slot (snd nx)) []).

Fixpoint merge_bq (cur : bq) (rest : list bq) {struct rest} : list bq * list bq :=
  match rest with
  | [] => ([cur], [])
  | nx :: rest' =>
      if b_count (fst cur) + b_count (fst nx) <=? Q_BATCH then
        let '(l, ex) := merge_bq (bq_merge cur nx) rest' in (l, bq_empty nx :: ex)
      else
        let '(l, ex) := merge_bq nx rest' in (cur :: l, ex)
  end.

#[using="Type"] Lemma merge_bq_fst : forall rest cur,
  let '(l, ex, exb) := merge_batches (fst cur) (map fst rest) in
  map fst (fst (merge_bq cur rest)) = l /\ map fst (snd (merge_bq cur rest)) = ex /\ exb = Q_BATCH_BYTES * Z.of_nat (length (snd (merge_bq cur rest))).
Proof.
  induction rest as [|nx rest IH]; intros cur; cbn [merge_batches merge_bq map fst snd length].
  - cbn. repeat split; reflexivity.
  - destruct (b_count (fst cur) + b_count (fst nx) <=? Q_BATCH) eqn:E.
    + specialize (IH (bq_merge cur nx)). cbn [bq_merge fst] in IH.
      destruct (merge_batches _ (map fst rest)) as [[l ex] exb]. destruct (merge_bq _ rest) as [l2 ex2]. cbn [fst snd map length] in *.
      (nd_pre IH 3%nat; intros A B C; nd_post). rewrite A, B. repeat split; try reflexivity. lia.
    + specialize (IH nx). destruct (merge_batches (fst nx) (map fst rest)) as [[l ex] exb]. destruct (merge_bq nx rest) as [l2 ex2].
      cbn [fst snd map length] in *. (nd_pre IH 3%nat; intros A B C; nd_post). rewrite A, B. repeat split; try reflexivity. exact C.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tfirst (L : alayout) (T : list bq) (tf0 : Z) : Z := match T with [] => tf0 | x :: _ => baddr L x end.
Definition tlast (L : alayout) (T : list bq) (tl0 : Z) : Z := List.last (map (baddr L) T) tl0.

#[using="Type"] Lemma tlast_app1 : forall L T x tl0, tlast L (T ++ [x]) tl0 = baddr L x.
Proof. intros. unfold tlast. rewrite map_app. cbn. rewrite last_last. reflexivity. Qed.
#[using="Type"] Lemma tfirst_app : forall L T U tf0, T <> [] -> tfirst L (T ++ U) tf0 = tfirst L T tf0.
Proof. intros L [|x T] U tf0 H; [congruence| reflexivity]. Qed.
#[using="Type"] Lemma tlast_cons_ne : forall L x T tl0, T <> [] -> tlast L (x :: T) tl0 = tlast L T tl0.
Proof. intros L x [|y T] tl0 H; [congruence|]. unfold tlast. cbn [map]. destruct (map (baddr L) T); reflexivity. Qed.

#[using="Type"] Lemma merge_bq_ne : forall rest cur, fst (merge_bq cur rest) <> [].
Proof.
  induction rest as [|nx rest IH]; intros cur; cbn; [congruence|].
  destruct (_ <=? _); [specialize (IH (bq_merge cur nx)); destruct (merge_bq _ rest) | specialize (IH nx); destruct (merge_bq nx rest)]; cbn in *; congruence.
Qed.
#[using="Type"] Lemma merge_bq_first : forall L rest cur tf0, tfirst L (fst (merge_bq cur rest)) tf0 = baddr L cur.
Proof.
  induction rest as [|nx rest IH]; intros cur tf0; cbn; [reflexivity|].
  destruct (_ <=? _).
  - specialize (IH (bq_merge cur nx) tf0). destruct (merge_bq _ rest). cbn in *. rewrite IH. reflexivity.
  - destruct (merge_bq nx rest). reflexivity.
Qed.

(* [comment removed for export] *)
Definition bgeom (L : alayout) (LST TMP : Z) (x : bq) : Prop :=
  AIMG_HI <= baddr L x /\ baddr L x + Q_BATCH_BYTES <= ATOP
  /\ (LST + 32 <= baddr L x \/ baddr L x + Q_BATCH_BYTES <= LST)
  /\ (TMP + 32 <= baddr L x \/ baddr L x + Q_BATCH_BYTES <= TMP).

#[using="Type"] Lemma baddr_disj : forall L x y, qb_slot (snd x) <> qb_slot (snd y) -> 0 <= qb_slot (snd x) -> 0 <= qb_slot (snd y) ->
  baddr L x + Q_BATCH_BYTES <= baddr L y \/ baddr L y + Q_BATCH_BYTES <= baddr L x.
Proof.
  intros L x y NE X Y. unfold baddr, abatch_addr, aslot_addr, Q_BATCH_BYTES. rewrite size_of_class_24.
  destruct (Z.lt_ge_cases (qb_slot (snd x)) (qb_slot (snd y))); [left| right]; nia.
Qed.

Section Loop.
  Variables (L : alayout) (RNG : footprint) (LST TMP lf lb tf0 tl0 : Z).
  Variables (ra sp gp tp s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32).

  Definition chain (m : amem) (X : list bq) (nxt : Z) : Prop := abatches_to L m (map fst X) (map snd X) nxt.

  Definition mloop_post (P : list bq) (cur : bq) (R T : list bq) (tb ex : Z) (m : amem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a3 a4 t3 t4 t5 m',
      let '(l, e) := merge_bq cur R in
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 LST) (Z_to_bv 64 TMP) (Z_to_bv 64 (ex + Q_BATCH_BYTES * Z.of_nat (length e))) a3 a4
                   (Z_to_bv 64 Q_BATCH) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x35da0) fc None m' (seg_rom asegs)
      /\ munch ([(LST, LST + 24); (TMP, TMP + 32)] ++ map (fun x => (baddr L x, baddr L x + Q_BATCH_BYTES)) (cur :: R ++ T))%Z m m'
      /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' LST [C8 (Z_to_bv 64 (Z.of_nat (length (P ++ l)))); C8 (Z_to_bv 64 lf); C8 (Z_to_bv 64 (tlast L l 0)); C8 (Z_to_bv 64 lb)]
      /\ chain m' (P ++ l) 0
      /\ rw_cells asegs m' TMP [C8 (Z_to_bv 64 (Z.of_nat (length (T ++ e)))); C8 (Z_to_bv 64 (tfirst L (T ++ e) tf0));
                               C8 (Z_to_bv 64 (tlast L (T ++ e) tl0)); C8 (Z_to_bv 64 (tb + Q_BATCH_BYTES * Z.of_nat (length e)))]
      /\ chain m' (T ++ e) 0.

  #[using="Type"] Lemma qaddrs_map : forall X, qaddrs L (map snd X) = map (baddr L) X.
  Proof. induction X as [|x X IH]; [reflexivity|]. cbn [map qaddrs]. rewrite <- IH. reflexivity. Qed.
  #[using="Type"] Lemma hd_qaddrs : forall X nxt, hd nxt (qaddrs L (map snd X)) = tfirst L X nxt.
  Proof. intros [|x X] nxt; reflexivity. Qed.

  #[using="Type"] Lemma chain_app : forall m X Y nxt, chain m (X ++ Y) nxt <-> chain m X (tfirst L Y nxt) /\ chain m Y nxt.
  Proof.
    intros. unfold chain. rewrite !map_app. rewrite abatches_to_app by (rewrite !length_map; reflexivity).
    rewrite <- (hd_qaddrs Y nxt). tauto.
  Qed.
  #[using="Type"] Lemma chain_cons : forall m x Y nxt, chain m (x :: Y) nxt <-> abatch_cells L m (fst x) (snd x) (tfirst L Y nxt) /\ chain m Y nxt.
  Proof. intros. unfold chain. cbn [map abatches_to]. rewrite <- (hd_qaddrs Y nxt). tauto. Qed.
  #[using="Type"] Lemma chain_nil : forall m nxt, chain m [] nxt.
  Proof. intros. exact I. Qed.

  #[using="Type"] Lemma tfirst_pos : forall X nxt, Forall (bgeom L LST TMP) X -> X <> [] -> AIMG_HI <= tfirst L X nxt.
  Proof. intros [|x X] nxt HF NE; [congruence|]. cbn. inversion HF; subst. destruct H1 as (A & _). exact A. Qed.

  #[using="Type"] Lemma chain_frame : forall W m m' X nxt, chain m X nxt -> munch W m m' -> wmono asegs m m' ->
    Forall (fun x => disjoint_from W (baddr L x) Q_BATCH_BYTES) X -> chain m' X nxt.
  Proof.
    intros W m m' X nxt CH MU WM HF. unfold chain in *. eapply abatches_to_frame; [exact MU| exact WM| exact CH|].
    intros q Hq. apply in_map_iff in Hq. (nd_pre Hq 2%nat; intros x ndR1__; nd_post; destruct ndR1__ as (<- & ndR2__); rename ndR2__ into Hx). exact (proj1 (Forall_forall _ _) HF x Hx).
  Qed.

  (* [comment removed for export] *)
  Definition abatch_rest (m : amem) (b : abatch) (q : qbatchc) : Prop :=
    let B := abatch_addr L (qb_slot q) in
       rw_cells asegs m (B + 8) [C8 (Z_to_bv 64 (b_size b)); C8 (Z_to_bv 64 (b_count b))]
    /\ u64arr asegs m (B + 24) (map (Z_to_bv 64) (qhdrs L (b_chunks b) (qb_ks q)))
    /\ junk_at m (B + 24 + 8 * b_count b) (Q_BATCH_BYTES - 24 - 8 * b_count b)
    /\ b_count b = Z.of_nat (length (b_chunks b)) /\ length (qb_ks q) = length (b_chunks b)
    /\ 0 <= b_count b <= Q_BATCH.
  #[using="Type"] Lemma abatch_cells_split : forall m b q nx,
    abatch_cells L m b q nx <-> rw_cells asegs m (abatch_addr L (qb_slot q)) [C8 (Z_to_bv 64 nx)] /\ abatch_rest m b q.
  Proof.
    intros. unfold abatch_cells, abatch_rest. cbv zeta.
    rewrite (rw_cells_app asegs m (abatch_addr L (qb_slot q)) [C8 (Z_to_bv 64 nx)] [C8 (Z_to_bv 64 (b_size b)); C8 (Z_to_bv 64 (b_count b))]).
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. tauto.
  Qed.

  #[using="Type"] Lemma qhdrs_app : forall (a b : list achunk) (ka kb : list Z), length ka = length a ->
    qhdrs L (a ++ b) (ka ++ kb) = qhdrs L b kb ++ qhdrs L a ka.
  Proof.
    induction a as [|x a IH]; intros b [|k ka] kb LEN; cbn in *; try lia.
    - rewrite app_nil_r. reflexivity.
    - rewrite IH by lia. rewrite app_assoc. reflexivity.
  Qed.

  #[using="Type"] Lemma Forall_perm_slots : forall (f : bq -> Z) (Pr : bq -> Prop) (X Y : list bq),
    (forall x, In x Y -> exists x', In x' X /\ f x' = f x /\ (Pr x' -> Pr x)) -> Forall Pr X -> Forall Pr Y.
  Proof.
    intros f Pr X Y H HF. apply Forall_forall. intros x Hx. (nd_pre (H x Hx) 4%nat; intros x' Hx' _ HP; nd_post). apply HP.
    exact (proj1 (Forall_forall _ _) HF x' Hx').
  Qed.

  #[using="Type"] Lemma nodup_mid : forall (f : bq -> Z) l1 a l2, NoDup (map f (l1 ++ a :: l2)) -> forall x, In x (l1 ++ l2) -> f x <> f a.
  Proof.
    intros f l1 a l2 ND x Hx E. rewrite map_app in ND. cbn [map] in ND.
    (nd_pre (proj1 (list_relations.list.NoDup_app _ _) ND) 3%nat; intros _ NI ND2; nd_post).
    destruct (proj1 (list_relations.list.NoDup_cons _ _) ND2) as [NA _].
    apply in_app_iff in Hx. destruct Hx as [Hx|Hx].
    - refine (NI (f x) _ _). { apply list_elem_of_In. apply in_map. exact Hx. } rewrite E. left.
    - apply NA. rewrite <- E. apply list_elem_of_In. apply in_map. exact Hx.
  Qed.

  #[using="Type"] Lemma tlast_in : forall X d, X <> [] -> exists x, In x X /\ tlast L X d = baddr L x.
  Proof.
    induction X as [|x X IH]; intros d NE; [congruence|]. destruct X as [|y X'].
    - exists x. split; [left; reflexivity| reflexivity].
    - (nd_pre (IH d ltac:(congruence)) 3%nat; intros z Hz E; nd_post). exists z. split; [right; exact Hz|]. rewrite tlast_cons_ne by congruence. exact E.
  Qed.
  #[using="Type"] Lemma tfirst_in : forall X d, X <> [] -> exists x, In x X /\ tfirst L X d = baddr L x.
  Proof. intros [|x X] d NE; [congruence|]. exists x. split; [left; reflexivity| reflexivity]. Qed.

  #[using="Type"] Lemma bq_eq_dec : forall x y : bq, {x = y} + {x <> y}.
  Proof. intros. repeat (decide equality). Qed.

  #[using="Type"] Lemma sub_fp_incl : forall W W', (forall iv, In iv W -> In iv W') -> sub_fp W W'.
  Proof.
    intros W W' H. apply sub_fp_by_incl'. apply Forall_forall. intros iv Hiv. apply Exists_exists. exists iv. split; [apply H; exact Hiv| cbn; lia].
  Qed.

  (* [comment removed for export] *)
  Hypothesis A6 : a6 = Z_to_bv 64 (2^64 - Q_BATCH_BYTES).
  Hypothesis A7 : a7 = Z_to_bv 64 Q_BATCH_BYTES.
  Hypothesis L1 : 0 <= LST. Hypothesis L2 : LST + 32 <= ATOP.
  Hypothesis T1 : 0 <= TMP. Hypothesis T2 : TMP + 32 <= 2^47.
  Hypothesis DTL : TMP + 32 <= LST \/ LST + 32 <= TMP.
  Hypothesis RL : rng RNG LST 32. Hypothesis RT : rng RNG TMP 32.
  Hypothesis TF0 : 0 <= tf0 < 2^64. Hypothesis TL0 : 0 <= tl0 < 2^64. Hypothesis LF : 0 <= lf < 2^64. Hypothesis LB : 0 <= lb < 2^64.

  Lemma mloop_spec : forall (d : nat) (P : list bq) (cur : bq) (R T : list bq) (tb ex : Z) (t1 t2 a3 t3 t4 t5 : word) (m : amem),
    d = length R -> R <> [] ->
    mem_inv asegs m ->
    rw_cells asegs m LST [C8 (Z_to_bv 64 (Z.of_nat (length (P ++ cur :: R)))); C8 (Z_to_bv 64 lf); C8 (Z_to_bv 64 (tlast L (cur :: R) 0)); C8 (Z_to_bv 64 lb)] ->
    chain m (P ++ cur :: R) 0 ->
    rw_cells asegs m TMP [C8 (Z_to_bv 64 (Z.of_nat (length T))); C8 (Z_to_bv 64 (tfirst L T tf0)); C8 (Z_to_bv 64 (tlast L T tl0)); C8 (Z_to_bv 64 tb)] ->
    chain m T 0 ->
    Forall (bgeom L LST TMP) (P ++ cur :: R ++ T) -> Forall (fun x => 0 <= qb_slot (snd x)) (P ++ cur :: R ++ T) ->
    NoDup (map (fun x => qb_slot (snd x)) (P ++ cur :: R ++ T)) ->
    Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) (cur :: R) -> batches_bytes (map fst (cur :: R)) < 2^62 ->
    Forall (fun x => rng RNG (baddr L x) Q_BATCH_BYTES) (cur :: R ++ T) ->
    0 <= tb -> tb + Q_BATCH_BYTES * (Z.of_nat (length R) + 1) < 2^62 -> 0 <= ex -> ex + Q_BATCH_BYTES * (Z.of_nat (length R) + 1) < 2^62 ->
    Z.of_nat (length (P ++ cur :: R ++ T)) < 2^40 ->
    evtF asegs RNG (mloop_post P cur R T tb ex m)
      (MS (mkR ra sp gp tp (Z_to_bv 64 (baddr L (hd cur R))) t1 t2 s0 s1 (Z_to_bv 64 LST) (Z_to_bv 64 TMP) (Z_to_bv 64 ex) a3 (Z_to_bv 64 (baddr L cur))
               (Z_to_bv 64 Q_BATCH) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 amerge_loop) fc None m (seg_rom asegs)).
  Proof using A6 A7 L1 L2 T1 T2 DTL RL RT TF0 TL0 LF LB.   (* [comment removed for export] *)
    induction d as [|d IH]; intros until m; intros HD RNE MI LS CH TM CT GEO SL ND SZ SZS RB TB0 TB1 EX0 EX1 LEN40.
    { exfalso. destruct R; [congruence| cbn in HD; lia]. }
    destruct R as [|nx R']; [congruence|]. cbn [hd].
    pose proof CH as CH0.
    destruct (proj1 (chain_app _ _ _ _) CH) as [CHP CHR]. clear CH.
    destruct (proj1 (chain_cons _ _ _ _) CHR) as [BC CHR1]. clear CHR. destruct (proj1 (chain_cons _ _ _ _) CHR1) as [BN CHR']. clear CHR1.
    (nd_pre BC 6%nat; intros CC EC JC CCNT CLEN CRNG; nd_post). (nd_pre BN 6%nat; intros CN EN JN NCNT NLEN NRNG; nd_post).
    assert (GC : bgeom L LST TMP cur) by (eapply (proj1 (Forall_forall _ _) GEO); apply in_app_iff; right; left; reflexivity).
    assert (GN : bgeom L LST TMP nx) by (eapply (proj1 (Forall_forall _ _) GEO); apply in_app_iff; right; right; left; reflexivity).
    assert (RC : rng RNG (baddr L cur) Q_BATCH_BYTES) by (pose proof (Forall_inv RB) as X; exact X).
    assert (RN : rng RNG (baddr L nx) Q_BATCH_BYTES) by (pose proof (Forall_inv (Forall_inv_tail RB)) as X; exact X).
    assert (DCN : baddr L cur + Q_BATCH_BYTES <= baddr L nx \/ baddr L nx + Q_BATCH_BYTES <= baddr L cur).
    { apply (baddr_disj L cur nx).
      - intros E. rewrite map_app in ND. cbn [map] in ND. (nd_pre (proj1 (list_relations.list.NoDup_app _ _) ND) 3%nat; intros _ _ ND2; nd_post).
        destruct (proj1 (list_relations.list.NoDup_cons _ _) ND2) as [NI _]. apply NI. rewrite E. left.
      - eapply (proj1 (Forall_forall _ _) SL). apply in_app_iff; right; left; reflexivity.
      - eapply (proj1 (Forall_forall _ _) SL). apply in_app_iff; right; right; left; reflexivity. }
    pose proof (Forall_inv SZ) as SZC. pose proof (Forall_inv (Forall_inv_tail SZ)) as SZN. cbn beta in SZC, SZN.
    cbn [map] in SZS. rewrite !batches_bytes_cons in SZS.
    pose proof (batches_bytes_lb (map fst R') ltac:(rewrite Forall_map; exact (Forall_inv_tail (Forall_inv_tail SZ)))) as SZR.
    unfold bgeom, amerge_loop, AIMG_HI, Q_BATCH_BYTES, Q_BATCH in GC, GN, RC, RN, DCN, CC, EC, JC, CN, EN, JN, CRNG, NRNG, SZC, SZN, L2 |- *.
    unfold baddr in GC, GN, RC, RN, DCN, CC, CN |- *. cbn [fst snd tfirst baddr] in GC, GN, RC, RN, DCN, CC, EC, JC, CN, EN, JN, CCNT, CLEN, CRNG, NCNT, NLEN, NRNG, SZC, SZN |- *.
    set (CUR := abatch_addr L (qb_slot (snd cur))) in *. set (NXT := abatch_addr L (qb_slot (snd nx))) in *.
    (nd_pre GC 4%nat; intros GC1 GC2 GC3 GC4; nd_post). (nd_pre GN 4%nat; intros GN1 GN2 GN3 GN4; nd_post).
    unfold baddr in CC. cbn [fst snd] in CC. fold NXT in CC.
    (* [comment removed for export] *)
    step. step. zstep.                                    (* [comment removed for export] *)
    step. if_cases KF; zify_cond KF.                      (* [comment removed for export] *)
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in KF by lia.
      zstep.                                              (* [comment removed for export] *)
      step.                                               (* [comment removed for export] *)
      step. if_cases KE; zify_cond KE.                    (* [comment removed for export] *)
      + (* [comment removed for export] *)
        assert (GR : Forall (bgeom L LST TMP) R').
        { apply Forall_app in GEO. destruct GEO as [_ G2]. do 2 apply Forall_inv_tail in G2. apply Forall_app in G2. destruct G2 as [G2 _]. exact G2. }
        assert (RNIL : R' = []).
        { destruct R' as [|r R'']; [reflexivity| exfalso].
          pose proof (tfirst_pos (r :: R'') 0 GR ltac:(congruence)) as X. unfold AIMG_HI in X. cbn [tfirst] in X, KE.
          pose proof (Forall_inv GR) as Y. unfold bgeom, Q_BATCH_BYTES in Y. cbv beta in Y. (nd_pre Y 3%nat; intros Y1 Y Y3; nd_post).
          rewrite Z.mod_small in KE by (clear -X Y; lia). clear -X KE. lia. }
        subst R'. clear GR KE.
        assert (MB : merge_bq cur [nx] = ([cur; nx], [])).
        { cbn [merge_bq]. unfold Q_BATCH. destruct (Z.leb_spec0 (b_count (fst cur) + b_count (fst nx)) 1021); [exfalso; clear -KF l; lia| reflexivity]. }
        apply evtF_done. unfold mloop_post. rewrite MB. cbv beta iota zeta. cbn [length Z.of_nat app Pos.of_succ_nat].
        rewrite !app_nil_r, Z.mul_0_r, !Z.add_0_r.
        do 8 eexists. exists m. split; [reflexivity|].
        split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|].
        split. { replace (length (P ++ [cur; nx])) with (length (P ++ cur :: nx :: [])) by reflexivity. exact LS. }
        split; [exact CH0|]. split; [exact TM| exact CT].
      + (* [comment removed for export] *)
        assert (RNE' : R' <> []) by (intros ->; cbn in KE; rewrite ?unsigned_lit in KE by lia; lia).
        assert (TFE : tfirst L R' 0 = baddr L (hd nx R')) by (destruct R'; [congruence| reflexivity]).
        rewrite TFE.
        eapply evtF_mono.
        { eapply (IH (P ++ [cur]) nx R' T tb ex); try eassumption.
          - cbn in HD. lia.
          - rewrite <- app_assoc. cbn [app]. rewrite tlast_cons_ne in LS by congruence. exact LS.
          - rewrite <- app_assoc. cbn [app]. exact CH0.
          - rewrite <- app_assoc. cbn [app]. exact GEO.
          - rewrite <- app_assoc. cbn [app]. exact SL.
          - rewrite <- app_assoc. cbn [app]. exact ND.
          - exact (Forall_inv_tail SZ).
          - cbn [map]. rewrite batches_bytes_cons. clear -SZS SZC. lia.
          - exact (Forall_inv_tail RB).
          - revert TB1. clear. cbn [length]. unfold Q_BATCH_BYTES. intros. lia.
          - revert EX1. clear. cbn [length]. unfold Q_BATCH_BYTES. intros. lia.
          - rewrite <- app_assoc. cbn [app]. exact LEN40. }
        cbv beta. unfold mloop_post. intros ms' (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & m' & POST).
        assert (MB : merge_bq cur (nx :: R') = (cur :: fst (merge_bq nx R'), snd (merge_bq nx R'))).
        { cbn [merge_bq]. unfold Q_BATCH. destruct (Z.leb_spec0 (b_count (fst cur) + b_count (fst nx)) 1021); [exfalso; clear -KF l; lia|].
          destruct (merge_bq nx R'); reflexivity. }
        rewrite MB. destruct (merge_bq nx R') as [l' e'] eqn:MB'. cbn [fst snd].
        (destruct POST as (-> & ndR1__); nd_pre ndR1__ 7%nat; intros MU' WM' MI' LS' CH' TM' CT'; nd_post).
        do 8 eexists. exists m'. split; [reflexivity|].
        split. { eapply munch_weaken; [| exact MU']. intros x Hx. revert Hx. cbn [map app]. unfold outside. cbn. clear. tauto. }   (* [comment removed for export] *)
        split; [exact WM'|]. split; [exact MI'|].
        split. { rewrite <- app_assoc in LS'. cbn [app] in LS'. rewrite tlast_cons_ne by (pose proof (merge_bq_ne R' nx) as NE; rewrite MB' in NE; exact NE). exact LS'. }
        split. { rewrite <- app_assoc in CH'. exact CH'. }
        split; [exact TM'| exact CT'].
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in KF by lia.
      assert (GR : Forall (bgeom L LST TMP) R').
      { pose proof GEO as G. apply Forall_app in G. destruct G as [_ G2]. do 2 apply Forall_inv_tail in G2. apply Forall_app in G2. destruct G2 as [G2 _]. exact G2. }
      assert (NXN : 0 <= tfirst L R' 0 < 2^64).
      { destruct R' as [|r R'']; [cbn; lia|]. pose proof (Forall_inv GR) as Y. unfold bgeom, AIMG_HI, Q_BATCH_BYTES in Y. cbn [tfirst]. clear -Y. lia. }
      assert (LEC : length (map (Z_to_bv 64) (qhdrs L (b_chunks (fst cur)) (qb_ks (snd cur)))) = Z.to_nat (b_count (fst cur)))
        by (rewrite length_map, qhdrs_length by exact CLEN; lia).
      assert (LEN : length (map (Z_to_bv 64) (qhdrs L (b_chunks (fst nx)) (qb_ks (snd nx)))) = Z.to_nat (b_count (fst nx)))
        by (rewrite length_map, qhdrs_length by exact NLEN; lia).
      eapply evtF_cut.
      { eapply (mcore_spec RNG) with (LST := LST) (CUR := CUR) (NXT := NXT); try reflexivity.
        all: try eassumption.
        all: clear -SZC SZN SZS SZR CRNG NRNG KF NXN LEN40 GC1 GC2 GC3 GC4 GN1 GN2 GN3 GN4 DCN L1 L2; unfold Q_BATCH, Q_BATCH_BYTES in *.
        all: try lia.
        revert LEN40; clear; rewrite !length_app; cbn [length]; rewrite ?length_app; cbn [length]; intros; lia. }
      cbv beta. intros ms1 (y2 & y3 & y4 & y5 & m1 & -> & MUc & WMc & MI1 & CC1 & EC1 & JC1 & CN1 & JN1). clear MI.
      unfold Q_BATCH_BYTES in CC1, JC1, CN1, JN1.
      (* [comment removed for export] *)
      assert (OTH : forall x, In x (P ++ R' ++ T) ->
                (baddr L x + 8192 <= CUR \/ CUR + 8192 <= baddr L x) /\ (baddr L x + 8192 <= NXT \/ NXT + 8192 <= baddr L x)
                /\ bgeom L LST TMP x /\ 0 <= qb_slot (snd x)).
      { intros x Hx.
        assert (INA : In x (P ++ cur :: (nx :: R') ++ T)).
        { apply in_app_iff in Hx. apply in_app_iff. destruct Hx as [Hx|Hx]; [left; exact Hx| right; right]. cbn [app]. right. exact Hx. }
        pose proof (proj1 (Forall_forall _ _) SL x INA) as SX. pose proof (proj1 (Forall_forall _ _) GEO x INA) as GX. cbv beta in SX.
        assert (SC : 0 <= qb_slot (snd cur)) by (eapply (proj1 (Forall_forall _ _) SL); apply in_app_iff; right; left; reflexivity).
        assert (SN : 0 <= qb_slot (snd nx)) by (eapply (proj1 (Forall_forall _ _) SL); apply in_app_iff; right; right; left; reflexivity).
        assert (N1 : qb_slot (snd x) <> qb_slot (snd cur)).
        { apply (nodup_mid (fun x => qb_slot (snd x)) P cur ((nx :: R') ++ T) ND x).
          apply in_app_iff in Hx. apply in_app_iff. destruct Hx as [Hx|Hx]; [left; exact Hx| right; cbn [app]; right; exact Hx]. }
        assert (N2 : qb_slot (snd x) <> qb_slot (snd nx)).
        { apply (nodup_mid (fun x => qb_slot (snd x)) (P ++ [cur]) nx (R' ++ T)); [rewrite <- app_assoc; exact ND|].
          apply in_app_iff in Hx. apply in_app_iff. destruct Hx as [Hx|Hx]; [left; apply in_app_iff; left; exact Hx| right; exact Hx]. }
        pose proof (baddr_disj L x cur N1 SX SC) as D1. pose proof (baddr_disj L x nx N2 SX SN) as D2.
        unfold baddr, Q_BATCH_BYTES in D1, D2 |- *. cbn [snd] in D1, D2. fold CUR in D1. fold NXT in D2. clear -D1 D2 GX SX; tauto. }   (* [comment removed for export] *)
      (* [comment removed for export] *)
      assert (DJc : forall x, In x (P ++ R' ++ T) ->
        disjoint_from [(CUR + 8, CUR + 24); (CUR + 24 + 8 * b_count (fst cur), CUR + 24 + 8 * (b_count (fst cur) + b_count (fst nx))); (NXT + 8, NXT + 24)]%Z (baddr L x) 8192).
      { intros x Hx. (nd_pre (OTH x Hx) 3%nat; intros D1 D2 _; nd_post). cbn. clear -D1 D2 CRNG NRNG KF. lia. }
      xport LS MUc WMc ltac:(clear -GC3 GN3 CRNG NRNG KF; lia).
      xport TM MUc WMc ltac:(clear -GC4 GN4 CRNG NRNG KF; lia).
      assert (CHP1 : chain m1 P CUR).
      { eapply chain_frame; [exact CHP| exact MUc| exact WMc|]. apply Forall_forall. intros x Hx. apply DJc. apply in_app_iff. left. exact Hx. }
      assert (CHR1 : chain m1 R' 0).
      { eapply chain_frame; [exact CHR'| exact MUc| exact WMc|]. apply Forall_forall. intros x Hx. apply DJc. apply in_app_iff. right. apply in_app_iff. left. exact Hx. }
      assert (CT1 : chain m1 T 0).
      { eapply chain_frame; [exact CT| exact MUc| exact WMc|]. apply Forall_forall. intros x Hx. apply DJc. apply in_app_iff. right. apply in_app_iff. right. exact Hx. }
      clear CHP CHR' CT DJc.
      (* [comment removed for export] *)
      assert (GB : forall x, In x (P ++ cur :: (nx :: R') ++ T) -> 6303744 <= baddr L x /\ baddr L x + 8192 <= ATOP
                                                            /\ (LST + 32 <= baddr L x \/ baddr L x + 8192 <= LST) /\ (TMP + 32 <= baddr L x \/ baddr L x + 8192 <= TMP)).
      { intros x Hx. pose proof (proj1 (Forall_forall _ _) GEO x Hx) as G. unfold bgeom, AIMG_HI, Q_BATCH_BYTES in G. exact G. }
      assert (LLR : 0 <= tlast L (cur :: nx :: R') 0 < 2^64).
      { (nd_pre (tlast_in (cur :: nx :: R') 0 ltac:(congruence)) 3%nat; intros z Hz ndR1__; nd_post; revert ndR1__; intros ->).
        assert (INz : In z (P ++ cur :: (nx :: R') ++ T)).
        { apply in_app_iff. right. destruct Hz as [<-|[<-|Hz]]; [left; reflexivity| right; left; reflexivity| right; right; apply in_app_iff; left; exact Hz]. }
        (nd_pre (GB z INz) 3%nat; intros B1 B2 _; nd_post). clear -B1 B2. lia. }
      assert (TFR : 0 <= tfirst L T tf0 < 2^64 /\ 0 <= tlast L T tl0 < 2^64).
      { destruct T as [|t T']; [cbn; clear -TF0 TL0; lia|].
        (nd_pre (tfirst_in (t :: T') tf0 ltac:(congruence)) 3%nat; intros z1 Hz1 ndR1__; nd_post; revert ndR1__; intros ->). (nd_pre (tlast_in (t :: T') tl0 ltac:(congruence)) 3%nat; intros z2 Hz2 ndR1__; nd_post; revert ndR1__; intros ->).
        (nd_pre (GB z1 ltac:(apply in_app_iff; right; right; apply in_app_iff; right; exact Hz1)) 3%nat; intros B1 B2 _; nd_post).
        (nd_pre (GB z2 ltac:(apply in_app_iff; right; right; apply in_app_iff; right; exact Hz2)) 3%nat; intros B3 B4 _; nd_post). clear -B1 B2 B3 B4. lia. }
      assert (LSP : 0 < Z.of_nat (length (P ++ cur :: nx :: R')) < 2^63).
      { revert LEN40. clear. rewrite !length_app. cbn [length]. rewrite ?length_app. cbn [length]. intros. lia. }
      (* [comment removed for export] *)
      destruct (list_eq_dec bq_eq_dec T []) as [TNIL|TNE].
      + (* [comment removed for export] *) subst T.
        eapply evtF_cut.
        { eapply (munlink_spec false RNG) with (CUR := CUR) (NXT := NXT) (LST := LST) (TMP := TMP) (TL := 0) (tlx := 0)
            (nxn := tfirst L R' 0) (szc := b_size (fst cur) + b_size (fst nx) - 8192) (cc := b_count (fst cur) + b_count (fst nx))
            (szn := 8192) (cn := 0) (ls := Z.of_nat (length (P ++ cur :: nx :: R'))) (lf := lf) (ll := tlast L (cur :: nx :: R') 0) (lb := lb)
            (tn := 0) (tf := tf0) (tl := tl0) (tb := tb) (ex := ex);
            try reflexivity; try eassumption; try exact I.
          all: unfold Q_BATCH_BYTES; revert TB0 TB1 EX0 EX1; clear; cbn [length]; unfold Q_BATCH_BYTES; intros; lia. }
        cbv beta. intros ms2 (z1 & z2 & z3 & m2 & -> & MUu & WMu & MI2 & CC2 & CN2 & LS2 & TM2 & _). cbn [app] in MUu. clear MI1.
        step.                                             (* [comment removed for export] *)
        step. if_cases KX; zify_cond KX.                  (* [comment removed for export] *)
        * (* [comment removed for export] *)
          assert (RNE' : R' <> []) by (intros ->; cbn in KX; rewrite ?unsigned_lit in KX by lia; lia).
          assert (TFE : tfirst L R' 0 = baddr L (hd nx R')) by (destruct R'; [congruence| reflexivity]).
          assert (MB : merge_bq cur (nx :: R') = (fst (merge_bq (bq_merge cur nx) R'), bq_empty nx :: snd (merge_bq (bq_merge cur nx) R'))).
          { cbn [merge_bq]. unfold Q_BATCH. destruct (Z.leb_spec0 (b_count (fst cur) + b_count (fst nx)) 1021); [| exfalso; clear -KF n; lia].
            destruct (merge_bq (bq_merge cur nx) R'); reflexivity. }
          (* [comment removed for export] *)
          xport EC1 MUu WMu ltac:(rewrite length_app, ?LEC, ?LEN; clear -CRNG NRNG KF DCN GC3 GC4; lia).
          destruct JC1 as [jc JC1]. xport JC1 MUu WMu ltac:(clear -CRNG NRNG KF DCN GC3 GC4; lia).
          destruct JN1 as [jn JN1]. xport JN1 MUu WMu ltac:(clear -CRNG NRNG KF DCN GN3 GN4; lia).
          assert (CHP2 : chain m2 P CUR).
          { eapply chain_frame; [exact CHP1| exact MUu| exact WMu|]. apply Forall_forall. intros x Hx.
            (nd_pre (OTH x ltac:(apply in_app_iff; left; exact Hx)) 4%nat; intros D1 D2 (G1 & G2 & G3 & G4) _; nd_post). unfold Q_BATCH_BYTES in *. cbn. clear -D1 D2 G3 G4. lia. }
          assert (CHR2 : chain m2 R' 0).
          { eapply chain_frame; [exact CHR1| exact MUu| exact WMu|]. apply Forall_forall. intros x Hx.
            (nd_pre (OTH x ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hx)) 4%nat; intros D1 D2 (G1 & G2 & G3 & G4) _; nd_post). unfold Q_BATCH_BYTES in *. cbn. clear -D1 D2 G3 G4. lia. }
          (* [comment removed for export] *)
          assert (LLN : (tlast L (cur :: nx :: R') 0 =? NXT) = false).
          { apply Z.eqb_neq. rewrite 2!tlast_cons_ne by congruence. (nd_pre (tlast_in R' 0 RNE') 3%nat; intros z Hz ndR1__; nd_post; revert ndR1__; intros ->).
            (nd_pre (OTH z ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hz)) 3%nat; intros _ D2 _; nd_post). clear -D2. lia. }
          rewrite LLN in LS2. rewrite TFE.
          replace (baddr L (hd nx R')) with (baddr L (hd (bq_merge cur nx) R')) by (destruct R'; [congruence| reflexivity]).
          setreg 14 (Z_to_bv 64 (baddr L (bq_merge cur nx))) ltac:(unfold baddr; cbn [bq_merge snd qb_slot]; reflexivity).
          unfold Q_BATCH_BYTES.
          eapply evtF_mono.
          { eapply (IH P (bq_merge cur nx) R' [bq_empty nx] (tb + 8192) (ex + 8192)).
            - cbn in HD. clear -HD. lia.
            - exact RNE'.
            - exact MI2.
            - (* [comment removed for export] *) rewrite length_app in LS2 |- *. cbn [length] in LS2 |- *.
              replace (Z.of_nat (length P + S (S (length R'))) - 1) with (Z.of_nat (length P + S (length R'))) in LS2 by lia.
              rewrite tlast_cons_ne by exact RNE'. rewrite 2!tlast_cons_ne in LS2 by congruence. exact LS2.
            - (* [comment removed for export] *) apply (proj2 (chain_app _ _ _ _)). cbn [tfirst]. unfold baddr. cbn [bq_merge snd qb_slot]. fold CUR. split; [exact CHP2|].
              apply (proj2 (chain_cons _ _ _ _)). split; [| exact CHR2].
              unfold abatch_cells. cbn [fst snd bq_merge b_size b_count b_chunks qb_slot qb_ks]. fold CUR. unfold Q_BATCH_BYTES, Q_BATCH.
              replace (b_size (fst cur) + (b_size (fst nx) - 8192)) with (b_size (fst cur) + b_size (fst nx) - 8192) by lia.
              split; [exact CC2|]. split; [rewrite qhdrs_app, map_app by exact NLEN; exact EC1|].
              split; [exists jc; exact JC1|]. rewrite !length_app. clear -CCNT NCNT CLEN NLEN CRNG NRNG KF. lia.
            - (* [comment removed for export] *) cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat tfirst tlast map List.last]. unfold baddr. cbn [bq_empty snd qb_slot]. fold NXT.
              unfold Q_BATCH_BYTES. replace (0 + 1) with 1 in TM2 by lia. exact TM2.
            - (* [comment removed for export] *) apply (proj2 (chain_cons _ _ _ _)). split; [| apply chain_nil].
              unfold abatch_cells. cbn [fst snd tfirst bq_empty b_size b_count b_chunks qb_slot qb_ks qhdrs map length Z.of_nat]. fold NXT. unfold Q_BATCH_BYTES, Q_BATCH.
              split; [exact CN2|]. split; [apply u64arr_nil; clear -GN1 GN2; lia|].
              split; [exists jn; rewrite Z.mul_0_r, Z.add_0_r, Z.sub_0_r; exact JN1|]. clear. lia.
            - (* [comment removed for export] *) apply Forall_forall. intros x Hx. apply in_app_iff in Hx. cbn [app In] in Hx.
              destruct Hx as [Hx|[E|Hx]]; [| subst x| apply in_app_iff in Hx; destruct Hx as [Hx|[E|F0]]; [| subst x| destruct F0]].
              + eapply (proj1 (Forall_forall _ _) GEO). apply in_app_iff. left. exact Hx.
              + unfold bgeom, baddr, AIMG_HI, Q_BATCH_BYTES. cbn [bq_merge snd qb_slot]. fold CUR. clear -GC1 GC2 GC3 GC4. tauto.
              + eapply (proj1 (Forall_forall _ _) GEO). apply in_app_iff. right. right. apply in_app_iff. left. right. exact Hx.
              + unfold bgeom, baddr, AIMG_HI, Q_BATCH_BYTES. cbn [bq_empty snd qb_slot]. fold NXT. clear -GN1 GN2 GN3 GN4. tauto.
            - (* [comment removed for export] *) apply Forall_forall. intros x Hx. apply in_app_iff in Hx. cbn [app In] in Hx.
              destruct Hx as [Hx|[E|Hx]]; [| subst x| apply in_app_iff in Hx; destruct Hx as [Hx|[E|F0]]; [| subst x| destruct F0]].
              + eapply (proj1 (Forall_forall _ _) SL). apply in_app_iff. left. exact Hx.
              + cbn [bq_merge snd qb_slot]. eapply (proj1 (Forall_forall _ _) SL). apply in_app_iff. right. left. reflexivity.
              + eapply (proj1 (Forall_forall _ _) SL). apply in_app_iff. right. right. apply in_app_iff. left. right. exact Hx.
              + cbn [bq_empty snd qb_slot]. eapply (proj1 (Forall_forall _ _) SL). apply in_app_iff. right. right. left. reflexivity.
            - (* [comment removed for export] *) rewrite app_nil_r in ND. revert ND. rewrite !map_app. cbn [map]. rewrite !map_app. cbn [map bq_merge bq_empty snd qb_slot app].
              intros ND. refine (proj1 (list_relations.list.NoDup_Permutation_proper _ _ _) ND).
              apply Permutation_app_head. apply perm_skip. apply Permutation_cons_append.
            - (* [comment removed for export] *) constructor; [| exact (Forall_inv_tail (Forall_inv_tail SZ))]. cbn [fst bq_merge b_size]. unfold Q_BATCH_BYTES in *. clear -SZC SZN. lia.
            - cbn [map fst bq_merge b_size]. rewrite batches_bytes_cons. cbn [b_size]. clear -SZS SZC SZN. unfold Q_BATCH_BYTES in *. lia.
            - (* [comment removed for export] *) rewrite app_nil_r in RB. constructor; [unfold baddr; cbn [bq_merge snd qb_slot]; fold CUR; exact RC|]. apply Forall_app. split; [exact (Forall_inv_tail (Forall_inv_tail RB))|].
              constructor; [unfold baddr; cbn [bq_empty snd qb_slot]; fold NXT; exact RN| constructor].
            - clear -TB0; lia.
            - revert TB1; clear; cbn [length]; unfold Q_BATCH_BYTES; intros; lia.
            - clear -EX0; lia.
            - revert EX1; clear; cbn [length]; unfold Q_BATCH_BYTES; intros; lia.
            - revert LEN40; clear; rewrite !length_app; cbn [length]; rewrite ?length_app; cbn [length]; intros; lia. }
          cbv beta. unfold mloop_post. rewrite MB. destruct (merge_bq (bq_merge cur nx) R') as [l' e']. cbn [fst snd].
          intros ms' (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & m' & -> & MU' & WM' & MI' & LS' & CH' & TM' & CT').
          cbn [length app] in TM' |- *. unfold Q_BATCH_BYTES in TM' |- *.
          replace (ex + 8192 * Z.of_nat (S (length e'))) with (ex + 8192 + 8192 * Z.of_nat (length e')) by lia.
          replace (tb + 8192 * Z.of_nat (S (length e'))) with (tb + 8192 + 8192 * Z.of_nat (length e')) by lia.
          do 8 eexists. exists m'. split; [reflexivity|].
          split. { (* [comment removed for export] *)
            unfold baddr. cbn [map app snd bq_merge bq_empty qb_slot] in MU' |- *. fold CUR in MU' |- *. fold NXT in MU' |- *.
            lazymatch goal with |- munch ?W _ _ =>
              assert (MU12 : munch W m m2) by (eapply (munch_trans_w _ _ _ _ _ _ MUc MUu); solve_sub_fpw ltac:(clear -CRNG NRNG KF; lia));
              eapply (munch_trans_w _ _ _ _ _ _ MU12 MU'); apply sub_fp_incl; [intros iv Hiv; exact Hiv|] end.
            intros iv Hiv. cbn [In app] in Hiv |- *. rewrite app_nil_r. rewrite map_app in Hiv. cbn [map] in Hiv.
            destruct Hiv as [H|[H|[H|H]]]; [clear -H; tauto| clear -H; tauto| clear -H; tauto|]. apply in_app_iff in H. destruct H as [H|[H|[]]]; [right; right; right; right; exact H| clear -H; tauto]. }   (* [comment removed for export] *)
          split; [eapply wmono_trans; [exact WMc| eapply wmono_trans; [exact WMu| exact WM']]|]. split; [exact MI'|].
          split; [exact LS'|]. split; [exact CH'|]. split; [exact TM'| exact CT'].
        * (* [comment removed for export] *)
          assert (RNIL : R' = []).
          { destruct R' as [|r R'']; [reflexivity| exfalso].
            pose proof (tfirst_pos (r :: R'') 0 GR ltac:(congruence)) as X. unfold AIMG_HI in X. cbn [tfirst] in X, KX.
            pose proof (Forall_inv GR) as Y. unfold bgeom, Q_BATCH_BYTES in Y. cbv beta in Y. (nd_pre Y 3%nat; intros Y1 Y Y3; nd_post).
            rewrite ?unsigned_lit in KX by (clear -X Y; lia). clear -X KX. lia. }
          subst R'. clear GR KX.
          assert (MB : merge_bq cur [nx] = ([bq_merge cur nx], [bq_empty nx])).
          { cbn [merge_bq]. unfold Q_BATCH. destruct (Z.leb_spec0 (b_count (fst cur) + b_count (fst nx)) 1021); [reflexivity| exfalso; clear -KF n; lia]. }
          (* [comment removed for export] *)
          xport EC1 MUu WMu ltac:(rewrite length_app, ?LEC, ?LEN; clear -CRNG NRNG KF DCN GC3 GC4; lia).
          destruct JC1 as [jc JC1]. xport JC1 MUu WMu ltac:(clear -CRNG NRNG KF DCN GC3 GC4; lia).
          destruct JN1 as [jn JN1]. xport JN1 MUu WMu ltac:(clear -CRNG NRNG KF DCN GN3 GN4; lia).
          assert (CHP2 : chain m2 P CUR).
          { eapply chain_frame; [exact CHP1| exact MUu| exact WMu|]. apply Forall_forall. intros x Hx.
            (nd_pre (OTH x ltac:(apply in_app_iff; left; exact Hx)) 4%nat; intros D1 D2 (G1 & G2 & G3 & G4) _; nd_post). unfold Q_BATCH_BYTES in *. cbn. clear -D1 D2 G3 G4. lia. }
          apply evtF_done. unfold mloop_post. rewrite MB. cbv beta iota zeta. cbn [length Z.of_nat app Pos.of_succ_nat Pos.to_nat].
          rewrite !Z.mul_1_r.
          do 8 eexists. exists m2. split; [reflexivity|].
          split. { cbn [map app]. unfold baddr, Q_BATCH_BYTES. cbn [snd]. fold CUR. fold NXT. eapply (munch_trans_w _ _ _ _ _ _ MUc MUu); solve_sub_fpw ltac:(clear -CRNG NRNG KF; lia). }
          split; [eapply wmono_trans; [exact WMc| exact WMu]|]. split; [exact MI2|].
          split. { rewrite length_app in LS2 |- *. cbn [length] in LS2 |- *.
                   replace (Z.of_nat (length P + 2) - 1) with (Z.of_nat (length P + 1)) in LS2 by lia.
                   cbn [tlast map List.last] in LS2. rewrite Z.eqb_refl in LS2. exact LS2. }
          split. { apply (proj2 (chain_app _ _ _ _)). split; [exact CHP2|]. apply (proj2 (chain_cons _ _ _ _)). split; [| apply chain_nil].
                   unfold abatch_cells. cbn [fst snd tfirst bq_merge b_size b_count b_chunks qb_slot qb_ks]. fold CUR. unfold Q_BATCH_BYTES, Q_BATCH.
                   cbn [tfirst] in CC2. replace (b_size (fst cur) + (b_size (fst nx) - 8192)) with (b_size (fst cur) + b_size (fst nx) - 8192) by lia.
                   split; [exact CC2|]. split.
                   - rewrite qhdrs_app, map_app by exact NLEN. exact EC1.
                   - split; [exists jc; exact JC1|]. rewrite !length_app. clear -CCNT NCNT CLEN NLEN CRNG NRNG KF. lia. }
          split. { unfold Q_BATCH_BYTES. replace (0 + 1) with 1 in TM2 by lia. exact TM2. }
          apply (proj2 (chain_cons _ _ _ _)). split; [| apply chain_nil].
          unfold abatch_cells. cbn [fst snd tfirst bq_empty b_size b_count b_chunks qb_slot qb_ks qhdrs map length Z.of_nat]. fold NXT. unfold Q_BATCH_BYTES, Q_BATCH.
          split; [exact CN2|]. split; [apply u64arr_nil; clear -GN1 GN2; lia|].
          split; [exists jn; rewrite Z.mul_0_r, Z.add_0_r, Z.sub_0_r; exact JN1|]. clear. lia.
      + (* [comment removed for export] *)
        (nd_pre (exists_last TNE) 3%nat; intros T0 tl ET; nd_post). rewrite ET in *. clear ET TNE.
        destruct (proj1 (chain_app _ _ _ _) CT1) as [CT0 CTL]. cbn [tfirst] in CT0.
        destruct (proj1 (chain_cons _ _ _ _) CTL) as [BTL _]. clear CTL. cbn [fst snd tfirst] in BTL.
        destruct (proj1 (abatch_cells_split _ _ _ _) BTL) as [TLN TLR]. clear BTL.
        unfold baddr in CT0. set (TL := abatch_addr L (qb_slot (snd tl))) in *.
        assert (INtl : In tl (P ++ R' ++ T0 ++ [tl])) by (apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity).
        (nd_pre (OTH tl INtl) 4%nat; intros DTLC DTLN (GT1 & GT2 & GT3 & GT4) STL; nd_post). unfold baddr, Q_BATCH_BYTES in DTLC, DTLN, GT1, GT2, GT3, GT4. fold TL in DTLC, DTLN, GT1, GT2, GT3, GT4.
        assert (RTL : rng RNG TL 8192).
        { pose proof (proj1 (Forall_forall _ _) RB tl ltac:(right; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity)) as X. unfold baddr in X. exact X. }
        assert (TLl : tlast L (T0 ++ [tl]) tl0 = TL) by (rewrite tlast_app1; reflexivity).
        eapply evtF_cut.
        { eapply (munlink_spec true RNG) with (CUR := CUR) (NXT := NXT) (LST := LST) (TMP := TMP) (TL := TL) (tlx := 0)
            (nxn := tfirst L R' 0) (szc := b_size (fst cur) + b_size (fst nx) - 8192) (cc := b_count (fst cur) + b_count (fst nx))
            (szn := 8192) (cn := 0) (ls := Z.of_nat (length (P ++ cur :: nx :: R'))) (lf := lf) (ll := tlast L (cur :: nx :: R') 0) (lb := lb)
            (tn := Z.of_nat (length (T0 ++ [tl]))) (tf := tfirst L (T0 ++ [tl]) tf0) (tl := tlast L (T0 ++ [tl]) tl0) (tb := tb) (ex := ex);
            try reflexivity; try eassumption; try exact I.
          all: try (revert TB0 TB1 EX0 EX1; clear; cbn [length]; unfold Q_BATCH_BYTES; intros; lia).
          all: try (clear -TFR; tauto).
          - revert LEN40. clear. rewrite !length_app. cbn [length]. rewrite ?length_app. cbn [length]. intros. lia.
          - (* [comment removed for export] *) unfold AIMG_HI, Q_BATCH_BYTES. split; [rewrite length_app; cbn [length]; clear; lia|]. split; [exact TLN|].
            split; [exact GT1|]. split; [exact GT2|]. split; [exact DTLC|]. split; [exact DTLN|]. split; [exact GT3|]. split; [exact GT4|].
            eapply rng_sub'; [exact RTL| clear; lia]. }
        cbv beta. intros ms2 (z1 & z2 & z3 & m2 & -> & MUu & WMu & MI2 & CC2 & CN2 & LS2 & TM2 & TL2). cbn [app] in MUu. clear MI1.
        (* [comment removed for export] *)
        assert (NTL : forall x, In x (P ++ R' ++ T0) -> qb_slot (snd x) <> qb_slot (snd tl)).
        { intros x Hx. apply (nodup_mid (fun x => qb_slot (snd x)) (P ++ cur :: nx :: R' ++ T0) tl []).
          - revert ND. clear. intros ND.
            match goal with |- NoDup ?l => match type of ND with NoDup ?l' => replace l with l'; [exact ND|] end end.
            rewrite !map_app. cbn [map]. rewrite ?map_app. cbn [map app]. repeat (rewrite <- ?app_assoc; cbn [app]). reflexivity.
          - rewrite app_nil_r. apply in_app_iff in Hx. apply in_app_iff. destruct Hx as [Hx|Hx]; [left; exact Hx| right; right; right].
            apply in_app_iff in Hx. apply in_app_iff. exact Hx. }
        assert (DSTL : forall x, In x (P ++ R' ++ T0) -> abatch_addr L (qb_slot (snd x)) + 8192 <= TL \/ TL + 8192 <= abatch_addr L (qb_slot (snd x))).
        { intros x Hx. pose proof (baddr_disj L x tl (NTL x Hx)) as D. unfold baddr, Q_BATCH_BYTES in D. apply D.
          - eapply (proj1 (Forall_forall _ _) SL). apply in_app_iff in Hx. apply in_app_iff. destruct Hx as [Hx|Hx]; [left; exact Hx| right; right].
            apply in_app_iff in Hx. apply in_app_iff. destruct Hx as [Hx|Hx]; [left; right; exact Hx| right; apply in_app_iff; left; exact Hx].
          - exact STL. }
        xport EC1 MUu WMu ltac:(rewrite length_app, ?LEC, ?LEN; clear -CRNG NRNG KF DCN GC3 GC4 DTLC; lia).
        destruct JC1 as [jc JC1]. xport JC1 MUu WMu ltac:(clear -CRNG NRNG KF DCN GC3 GC4 DTLC; lia).
        destruct JN1 as [jn JN1]. xport JN1 MUu WMu ltac:(clear -CRNG NRNG KF DCN GN3 GN4 DTLN; lia).
        assert (CHP2 : chain m2 P CUR).
        { eapply chain_frame; [exact CHP1| exact MUu| exact WMu|]. apply Forall_forall. intros x Hx.
          pose proof (DSTL x ltac:(apply in_app_iff; left; exact Hx)) as D3.
          (nd_pre (OTH x ltac:(apply in_app_iff; left; exact Hx)) 4%nat; intros D1 D2 (G1 & G2 & G3 & G4) _; nd_post). unfold baddr, Q_BATCH_BYTES in *. cbn. clear -D1 D2 D3 G3 G4. lia. }
        assert (CHR2 : chain m2 R' 0).
        { eapply chain_frame; [exact CHR1| exact MUu| exact WMu|]. apply Forall_forall. intros x Hx.
          pose proof (DSTL x ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hx)) as D3.
          (nd_pre (OTH x ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hx)) 4%nat; intros D1 D2 (G1 & G2 & G3 & G4) _; nd_post). unfold baddr, Q_BATCH_BYTES in *. cbn. clear -D1 D2 D3 G3 G4. lia. }
        assert (CT02 : chain m2 T0 TL).
        { eapply chain_frame; [exact CT0| exact MUu| exact WMu|]. apply Forall_forall. intros x Hx.
          pose proof (DSTL x ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Hx)) as D3.
          (nd_pre (OTH x ltac:(apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; exact Hx)) 4%nat; intros D1 D2 (G1 & G2 & G3 & G4) _; nd_post). unfold baddr, Q_BATCH_BYTES in *. cbn. clear -D1 D2 D3 G3 G4. lia. }
        (* [comment removed for export] *)
        (nd_pre TLR 6%nat; intros TLR1 TLR2 TLR3 TLR4 TLR5 TLR6; nd_post). fold TL in TLR1, TLR2, TLR3. unfold Q_BATCH_BYTES, Q_BATCH in TLR3, TLR6.
        xport TLR1 MUu WMu ltac:(clear -DTLC DTLN GT3 GT4; lia).
        xport TLR2 MUu WMu ltac:(rewrite length_map, qhdrs_length by exact TLR5; clear -DTLC DTLN GT3 GT4 TLR4 TLR6; lia).
        destruct TLR3 as [jt TLR3]. xport TLR3 MUu WMu ltac:(clear -DTLC DTLN GT3 GT4 TLR6; lia).
        assert (CT2 : chain m2 ((T0 ++ [tl]) ++ [bq_empty nx]) 0).
        { apply (proj2 (chain_app _ _ _ _)). split.
          - apply (proj2 (chain_app _ _ _ _)). cbn [tfirst app]. unfold baddr. fold TL. split; [exact CT02|].
            apply (proj2 (chain_cons _ _ _ _)). split; [| apply chain_nil]. cbn [tfirst]. unfold baddr. cbn [bq_empty snd qb_slot]. fold NXT.
            apply (proj2 (abatch_cells_split _ _ _ _)). fold TL. split; [exact TL2|]. split; [exact TLR1|]. split; [exact TLR2|].
            split; [exists jt; unfold Q_BATCH_BYTES; exact TLR3|]. unfold Q_BATCH. exact (conj TLR4 (conj TLR5 TLR6)).
          - apply (proj2 (chain_cons _ _ _ _)). split; [| apply chain_nil].
            unfold abatch_cells. cbn [fst snd tfirst bq_empty b_size b_count b_chunks qb_slot qb_ks qhdrs map length Z.of_nat]. fold NXT. unfold Q_BATCH_BYTES, Q_BATCH.
            split; [exact CN2|]. split; [apply u64arr_nil; clear -GN1 GN2; lia|].
            split; [exists jn; rewrite Z.mul_0_r, Z.add_0_r, Z.sub_0_r; exact JN1|]. clear. lia. }
        clear CT0 CT02 TLR1 TLR2 TLR3 TL2 TLN.
        (* [comment removed for export] *)
        assert (MU12 : munch ([(LST, LST + 24); (TMP, TMP + 32)] ++ map (fun x => (baddr L x, baddr L x + 8192)) (cur :: (nx :: R') ++ T0 ++ [tl]))%Z m m2).
        { eapply (munch_trans_w _ _ _ _ _ _ MUc MUu).
          - unfold baddr. cbn [map app snd]. fold CUR. fold NXT. solve_sub_fpw ltac:(clear -CRNG NRNG KF; lia).
          - apply sub_fp_by_incl'. unfold baddr. cbn [map app snd]. fold CUR. fold NXT. fold TL.
            repeat (apply Forall_cons; [first [ find_ivw ltac:(clear; lia)
                                               | apply Exists_exists; exists (TL, TL + 8192)%Z; split; [| cbn; clear; lia];
                                                 right; right; right; right; rewrite map_app, in_app_iff; right; rewrite map_app, in_app_iff; right; left; reflexivity ] |]).
            apply Forall_nil. }
        step.                                             (* [comment removed for export] *)
        step. if_cases KX; zify_cond KX.                  (* [comment removed for export] *)
        * (* [comment removed for export] *)
          assert (RNE' : R' <> []) by (intros ->; cbn in KX; rewrite ?unsigned_lit in KX by lia; lia).
          assert (TFE : tfirst L R' 0 = baddr L (hd nx R')) by (destruct R'; [congruence| reflexivity]).
          assert (MB : merge_bq cur (nx :: R') = (fst (merge_bq (bq_merge cur nx) R'), bq_empty nx :: snd (merge_bq (bq_merge cur nx) R'))).
          { cbn [merge_bq]. unfold Q_BATCH. destruct (Z.leb_spec0 (b_count (fst cur) + b_count (fst nx)) 1021); [| exfalso; clear -KF n; lia].
            destruct (merge_bq (bq_merge cur nx) R'); reflexivity. }
          assert (LLN : (tlast L (cur :: nx :: R') 0 =? NXT) = false).
          { apply Z.eqb_neq. rewrite 2!tlast_cons_ne by congruence. (nd_pre (tlast_in R' 0 RNE') 3%nat; intros z Hz ndR1__; nd_post; revert ndR1__; intros ->).
            (nd_pre (OTH z ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hz)) 3%nat; intros _ D2 _; nd_post). clear -D2. lia. }
          rewrite LLN in LS2. rewrite TFE.
          replace (baddr L (hd nx R')) with (baddr L (hd (bq_merge cur nx) R')) by (destruct R'; [congruence| reflexivity]).
          setreg 14 (Z_to_bv 64 (baddr L (bq_merge cur nx))) ltac:(unfold baddr; cbn [bq_merge snd qb_slot]; reflexivity).
          unfold Q_BATCH_BYTES.
          eapply evtF_mono.
          { eapply (IH P (bq_merge cur nx) R' ((T0 ++ [tl]) ++ [bq_empty nx]) (tb + 8192) (ex + 8192)).
            - cbn in HD. clear -HD. lia.
            - exact RNE'.
            - exact MI2.
            - rewrite length_app in LS2 |- *. cbn [length] in LS2 |- *.
              replace (Z.of_nat (length P + S (S (length R'))) - 1) with (Z.of_nat (length P + S (length R'))) in LS2 by lia.
              rewrite tlast_cons_ne by exact RNE'. rewrite 2!tlast_cons_ne in LS2 by congruence. exact LS2.
            - apply (proj2 (chain_app _ _ _ _)). cbn [tfirst]. unfold baddr. cbn [bq_merge snd qb_slot]. fold CUR. split; [exact CHP2|].
              apply (proj2 (chain_cons _ _ _ _)). split; [| exact CHR2].
              unfold abatch_cells. cbn [fst snd bq_merge b_size b_count b_chunks qb_slot qb_ks]. fold CUR. unfold Q_BATCH_BYTES, Q_BATCH.
              replace (b_size (fst cur) + (b_size (fst nx) - 8192)) with (b_size (fst cur) + b_size (fst nx) - 8192) by lia.
              split; [exact CC2|]. split; [rewrite qhdrs_app, map_app by exact NLEN; exact EC1|].
              split; [exists jc; exact JC1|]. rewrite !length_app. clear -CCNT NCNT CLEN NLEN CRNG NRNG KF. lia.
            - rewrite tfirst_app by (destruct T0; cbn; congruence). rewrite tlast_app1. unfold baddr. cbn [bq_empty snd qb_slot]. fold NXT.
              rewrite !length_app in TM2 |- *. cbn [length] in TM2 |- *. unfold Q_BATCH_BYTES in TM2.
              replace (Z.of_nat (length (T0 ++ [tl]) + 1)) with (Z.of_nat (length T0 + 1) + 1) by (rewrite length_app; cbn [length]; lia).
              exact TM2.
            - exact CT2.
            - apply Forall_forall. intros x Hx. apply in_app_iff in Hx. cbn [app In] in Hx.
              destruct Hx as [Hx|[E|Hx]]; [| subst x| apply in_app_iff in Hx; destruct Hx as [Hx|Hx]; [| apply in_app_iff in Hx; destruct Hx as [Hx|[E|F0]]; [| subst x| destruct F0]]].
              + eapply (proj1 (Forall_forall _ _) GEO). apply in_app_iff. left. exact Hx.
              + unfold bgeom, baddr, AIMG_HI, Q_BATCH_BYTES. cbn [bq_merge snd qb_slot]. fold CUR. clear -GC1 GC2 GC3 GC4. tauto.
              + eapply (proj1 (Forall_forall _ _) GEO). apply in_app_iff. right. right. apply in_app_iff. left. right. exact Hx.
              + eapply (proj1 (Forall_forall _ _) GEO). apply in_app_iff. right. right. apply in_app_iff. right. exact Hx.
              + unfold bgeom, baddr, AIMG_HI, Q_BATCH_BYTES. cbn [bq_empty snd qb_slot]. fold NXT. clear -GN1 GN2 GN3 GN4. tauto.
            - apply Forall_forall. intros x Hx. apply in_app_iff in Hx. cbn [app In] in Hx.
              destruct Hx as [Hx|[E|Hx]]; [| subst x| apply in_app_iff in Hx; destruct Hx as [Hx|Hx]; [| apply in_app_iff in Hx; destruct Hx as [Hx|[E|F0]]; [| subst x| destruct F0]]].
              + eapply (proj1 (Forall_forall _ _) SL). apply in_app_iff. left. exact Hx.
              + cbn [bq_merge snd qb_slot]. eapply (proj1 (Forall_forall _ _) SL). apply in_app_iff. right. left. reflexivity.
              + eapply (proj1 (Forall_forall _ _) SL). apply in_app_iff. right. right. apply in_app_iff. left. right. exact Hx.
              + eapply (proj1 (Forall_forall _ _) SL). apply in_app_iff. right. right. apply in_app_iff. right. exact Hx.
              + cbn [bq_empty snd qb_slot]. eapply (proj1 (Forall_forall _ _) SL). apply in_app_iff. right. right. left. reflexivity.
            - revert ND. rewrite !map_app. cbn [map]. rewrite !map_app. cbn [map bq_merge bq_empty snd qb_slot app]. rewrite ?map_app. cbn [map].
              intros ND. refine (proj1 (list_relations.list.NoDup_Permutation_proper _ _ _) ND).
              apply Permutation_app_head. apply perm_skip. repeat (rewrite <- ?app_assoc; cbn [app]).
              match goal with |- Permutation _ (?l1 ++ ?l2 ++ [?t; ?b]) =>
                replace (l1 ++ l2 ++ [t; b]) with ((l1 ++ l2 ++ [t]) ++ [b]) by (rewrite <- !app_assoc; reflexivity) end.
              apply Permutation_cons_append.
            - constructor; [| exact (Forall_inv_tail (Forall_inv_tail SZ))]. cbn [fst bq_merge b_size]. unfold Q_BATCH_BYTES in *. clear -SZC SZN. lia.
            - cbn [map fst bq_merge b_size]. rewrite batches_bytes_cons. cbn [b_size]. clear -SZS SZC SZN. unfold Q_BATCH_BYTES in *. lia.
            - apply Forall_forall. intros x Hx. cbn [app In] in Hx.
              destruct Hx as [E|Hx]; [subst x| apply in_app_iff in Hx; destruct Hx as [Hx|Hx]; [| apply in_app_iff in Hx; destruct Hx as [Hx|[E|F0]]; [| subst x| destruct F0]]].
              + unfold baddr. cbn [bq_merge snd qb_slot]. fold CUR. exact RC.
              + eapply (proj1 (Forall_forall _ _) RB). right. apply in_app_iff. left. right. exact Hx.
              + eapply (proj1 (Forall_forall _ _) RB). right. apply in_app_iff. right. exact Hx.
              + unfold baddr. cbn [bq_empty snd qb_slot]. fold NXT. exact RN.
            - clear -TB0; lia.
            - revert TB1; clear; cbn [length]; unfold Q_BATCH_BYTES; intros; lia.
            - clear -EX0; lia.
            - revert EX1; clear; cbn [length]; unfold Q_BATCH_BYTES; intros; lia.
            - revert LEN40; clear; rewrite !length_app; cbn [length]; rewrite ?length_app; cbn [length]; intros; lia. }
          cbv beta. unfold mloop_post. rewrite MB. destruct (merge_bq (bq_merge cur nx) R') as [l' e']. cbn [fst snd].
          intros ms' (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & m' & -> & MU' & WM' & MI' & LS' & CH' & TM' & CT').
          rewrite <- !app_assoc in TM', CT'. cbn [app] in TM', CT'.
          rewrite !length_app in TM' |- *. cbn [length app] in TM' |- *. unfold Q_BATCH_BYTES in TM' |- *.
          replace (ex + 8192 * Z.of_nat (S (length e'))) with (ex + 8192 + 8192 * Z.of_nat (length e')) by lia.
          replace (tb + 8192 * Z.of_nat (S (length e'))) with (tb + 8192 + 8192 * Z.of_nat (length e')) by lia.
          do 8 eexists. exists m'. split; [reflexivity|].
          split. { eapply (munch_trans_w _ _ _ _ _ _ MU12 MU'); apply sub_fp_incl; [intros iv Hiv; exact Hiv|].
                   intros iv Hiv. apply in_app_iff in Hiv. destruct Hiv as [Hiv|Hiv].
                   { cbn [In] in Hiv. destruct Hiv as [H|[H|[]]]; [left; exact H| right; left; exact H]. }
                   apply in_map_iff in Hiv. (nd_pre Hiv 2%nat; intros x ndR1__; nd_post; destruct ndR1__ as (<- & ndR2__); rename ndR2__ into Hx). right. right. apply in_map_iff.
                   destruct Hx as [<-|Hx]; [exists cur; split; [reflexivity| left; reflexivity]|].
                   apply in_app_iff in Hx. destruct Hx as [Hx|Hx]; [exists x; split; [reflexivity| right; right; apply in_app_iff; left; exact Hx]|].
                   apply in_app_iff in Hx. destruct Hx as [Hx|[<-|[]]]; [exists x; split; [reflexivity| right; right; apply in_app_iff; right; exact Hx]|].
                   exists nx; split; [reflexivity| right; left; reflexivity]. }
          split; [eapply wmono_trans; [exact WMc| eapply wmono_trans; [exact WMu| exact WM']]|]. split; [exact MI'|].
          split. { revert LS'. rewrite ?length_app. intros X; exact X. } split; [exact CH'|].
          rewrite <- !app_assoc. cbn [app]. split; [| exact CT'].
          revert TM'. rewrite ?length_app. cbn [length]. intros X.
          first [exact X| replace (length T0 + 1 + S (length e'))%nat with (length T0 + S (S (length e')))%nat by lia; exact X].
        * (* [comment removed for export] *)
          assert (RNIL : R' = []).
          { destruct R' as [|r R'']; [reflexivity| exfalso].
            pose proof (tfirst_pos (r :: R'') 0 GR ltac:(congruence)) as X. unfold AIMG_HI in X. cbn [tfirst] in X, KX.
            pose proof (Forall_inv GR) as Y. unfold bgeom, Q_BATCH_BYTES in Y. cbv beta in Y. (nd_pre Y 3%nat; intros Y1 Y Y3; nd_post).
            rewrite ?unsigned_lit in KX by (clear -X Y; lia). clear -X KX. lia. }
          subst R'. clear GR KX.
          assert (MB : merge_bq cur [nx] = ([bq_merge cur nx], [bq_empty nx])).
          { cbn [merge_bq]. unfold Q_BATCH. destruct (Z.leb_spec0 (b_count (fst cur) + b_count (fst nx)) 1021); [reflexivity| exfalso; clear -KF n; lia]. }
          apply evtF_done. unfold mloop_post. rewrite MB. cbv beta iota zeta. cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat].
          rewrite !Z.mul_1_r.
          do 8 eexists. exists m2. split; [reflexivity|].
          split. { exact MU12. }
          split; [eapply wmono_trans; [exact WMc| exact WMu]|]. split; [exact MI2|].
          split. { rewrite length_app in LS2 |- *. cbn [length] in LS2 |- *.
                   replace (Z.of_nat (length P + 2) - 1) with (Z.of_nat (length P + 1)) in LS2 by lia.
                   cbn [tlast map List.last] in LS2. rewrite Z.eqb_refl in LS2. exact LS2. }
          split. { apply (proj2 (chain_app _ _ _ _)). split; [exact CHP2|]. apply (proj2 (chain_cons _ _ _ _)). split; [| apply chain_nil].
                   unfold abatch_cells. cbn [fst snd tfirst bq_merge b_size b_count b_chunks qb_slot qb_ks]. fold CUR. unfold Q_BATCH_BYTES, Q_BATCH.
                   cbn [tfirst] in CC2. replace (b_size (fst cur) + (b_size (fst nx) - 8192)) with (b_size (fst cur) + b_size (fst nx) - 8192) by lia.
                   split; [exact CC2|]. split.
                   - rewrite qhdrs_app, map_app by exact NLEN. exact EC1.
                   - split; [exists jc; exact JC1|]. rewrite !length_app. clear -CCNT NCNT CLEN NLEN CRNG NRNG KF. lia. }
          split; [| exact CT2].
          lazymatch type of TM2 with rw_cells _ _ _ ?l2 => lazymatch goal with |- rw_cells _ _ _ ?l1 => replace l1 with l2; [exact TM2|] end end.
          rewrite (tfirst_app L (T0 ++ [tl]) [bq_empty nx] tf0) by (destruct T0; cbn; congruence). rewrite tlast_app1. unfold baddr. cbn [bq_empty snd qb_slot]. fold NXT.
          rewrite !length_app. cbn [length]. unfold Q_BATCH_BYTES.
          replace (Z.of_nat (length T0 + 1 + 1)) with (Z.of_nat (length T0 + 1) + 1) by lia. reflexivity.
  Qed.
End Loop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End CANSEC1.
Notation AMERGE_STACK := 16 (only parsing).

Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition amerge_fun (X : list bq) : list bq * list bq :=
  match X with [] => ([], []) | cur :: R => merge_bq cur R end.

Definition amerge_post (L : alayout) (LST TMP lb tf0 tl0 tb lo : Z) (X T : list bq)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    let '(l, e) := amerge_fun X in
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 LST) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch ([(bv_unsigned sp - AMERGE_STACK, bv_unsigned sp); (LST, LST + 32); (TMP, TMP + 32)]
              ++ map (fun x => (baddr L x, baddr L x + Q_BATCH_BYTES)) (X ++ T))%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' LST [C8 (Z_to_bv 64 (Z.of_nat (length l))); C8 (Z_to_bv 64 (tfirst L X 0)); C8 (Z_to_bv 64 (tlast L l 0));
                             C8 (Z_to_bv 64 (lb - Q_BATCH_BYTES * Z.of_nat (length e)))]
    /\ chain L m' l 0
    /\ rw_cells asegs m' TMP [C8 (Z_to_bv 64 (Z.of_nat (length (T ++ e)))); C8 (Z_to_bv 64 (tfirst L (T ++ e) tf0));
                             C8 (Z_to_bv 64 (tlast L (T ++ e) tl0)); C8 (Z_to_bv 64 (tb + Q_BATCH_BYTES * Z.of_nat (length e)))]
    /\ chain L m' (T ++ e) 0.

#[using="Type"] Lemma disj_objs_above : forall L LST TMP Y A n, Forall (bgeom L LST TMP) Y -> ATOP <= A ->
  disjoint_from (map (fun x => (baddr L x, baddr L x + Q_BATCH_BYTES)) Y) A n.
Proof.
  intros L LST TMP Y A n HF HA. apply disjoint_from_Forall. apply Forall_map. eapply Forall_impl; [| exact HF].
  intros x (G1 & G2 & _). cbn [fst snd]. left. unfold Q_BATCH_BYTES in *. lia.
Qed.

#[using="Type"] Lemma merge_bq_baddr_in : forall L R cur x, In x (fst (merge_bq cur R) ++ snd (merge_bq cur R)) ->
  exists y, In y (cur :: R) /\ baddr L y = baddr L x.
Proof.
  induction R as [|nx R IH]; intros cur x Hx; cbn [merge_bq fst snd app] in Hx.
  - destruct Hx as [<-|[]]. exists cur. split; [left; reflexivity| reflexivity].
  - destruct (b_count (fst cur) + b_count (fst nx) <=? Q_BATCH).
    + specialize (IH (bq_merge cur nx) x). destruct (merge_bq (bq_merge cur nx) R) as [l e]. cbn [fst snd] in Hx, IH.
      assert (Hx' : In x (l ++ e) \/ x = bq_empty nx).
      { apply in_app_iff in Hx. destruct Hx as [Hx|[<-|Hx]]; [left; apply in_app_iff; left; exact Hx| right; reflexivity| left; apply in_app_iff; right; exact Hx]. }
      destruct Hx' as [Hx'| ->].
      * (nd_pre (IH Hx') 3%nat; intros y Hy EY; nd_post). destruct Hy as [<-|Hy].
        -- exists cur. split; [left; reflexivity| exact EY].
        -- exists y. split; [right; right; exact Hy| exact EY].
      * exists nx. split; [right; left; reflexivity| reflexivity].
    + specialize (IH nx x). destruct (merge_bq nx R) as [l e]. cbn [fst snd] in Hx, IH.
      destruct Hx as [<-|Hx].
      * exists cur. split; [left; reflexivity| reflexivity].
      * (nd_pre (IH Hx) 3%nat; intros y Hy EY; nd_post). exists y. split; [right; exact Hy| exact EY].
Qed.

#[using="Type"] Lemma amerge_spec : forall L RNG (LST TMP lb tf0 tl0 tb lo : Z) (X T : list bq)
    ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : amem),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - AMERGE_STACK ->
  mem_inv asegs m ->
  rw_cells asegs m LST [C8 (Z_to_bv 64 (Z.of_nat (length X))); C8 (Z_to_bv 64 (tfirst L X 0)); C8 (Z_to_bv 64 (tlast L X 0)); C8 (Z_to_bv 64 lb)] ->
  chain L m X 0 ->
  rw_cells asegs m TMP [C8 (Z_to_bv 64 (Z.of_nat (length T))); C8 (Z_to_bv 64 (tfirst L T tf0)); C8 (Z_to_bv 64 (tlast L T tl0)); C8 (Z_to_bv 64 tb)] ->
  chain L m T 0 ->
  Forall (bgeom L LST TMP) (X ++ T) -> Forall (fun x => 0 <= qb_slot (snd x)) (X ++ T) ->
  NoDup (map (fun x => qb_slot (snd x)) (X ++ T)) ->
  Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) X -> batches_bytes (map fst X) < 2^62 ->
  0 <= LST -> LST + 32 <= ATOP -> 0 <= TMP -> TMP + 32 <= 2^47 -> (TMP + 32 <= LST \/ LST + 32 <= TMP) ->
  (bv_unsigned sp <= TMP \/ TMP + 32 <= lo) ->
  0 <= tf0 < 2^64 -> 0 <= tl0 < 2^64 -> 0 <= lb < 2^64 -> 0 <= tb -> tb + Q_BATCH_BYTES * Z.of_nat (length X) < 2^62 ->
  Z.of_nat (length (X ++ T)) < 2^40 ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG LST 32 -> rng RNG TMP 32 ->
  Forall (fun x => rng RNG (baddr L x) Q_BATCH_BYTES) (X ++ T) ->
  evtF asegs RNG (amerge_post L LST TMP lb tf0 tl0 tb lo X T ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 LST) (Z_to_bv 64 TMP) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 amerge_entry) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST CEIL LO MI LS CH TM CT GEO SL ND SZ SZS L1 L2 T1 T2 DTL DTS TF0 TL0 LB TB0 TB1 LEN40 RSTK RL RT RB.
  unfold amerge_entry. atop_facts. unfold Q_BATCH_BYTES in TB1.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (LST + 24, LST + 32)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 16%nat ST.
  step. step.                                  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac chain_over CHx MUx WMx GEOx sel :=
    eapply chain_frame in CHx; [| exact MUx | exact WMx |
      apply Forall_forall; let xg := fresh "xg" in let Hxg := fresh "Hxg" in let Gx := fresh "Gx" in intros xg Hxg;
      lazymatch type of GEOx with Forall (bgeom ?L ?LST ?TMP) _ =>
        assert (Gx : bgeom L LST TMP xg) by (eapply (proj1 (Forall_forall _ _) GEOx); apply in_app_iff; sel (); exact Hxg) end;
      unfold bgeom, AIMG_HI, Q_BATCH_BYTES in Gx; unfold Q_BATCH_BYTES; cbn [disjoint_from fst snd]; lia ].
  (* [comment removed for export] *)
  Local Ltac exit2 sp MU WM ST FR CH CT GEO LS TM :=
    step; zstep;                               (* [comment removed for export] *)
    step;                                      (* [comment removed for export] *)
    step; step; step;                          (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp);
    chain_over CH MU WM GEO ltac:(fun _ => left); chain_over CT MU WM GEO ltac:(fun _ => right);
    apply evtF_done; unfold amerge_post; cbn [amerge_fun merge_bq length Z.of_nat Pos.of_succ_nat Pos.to_nat tfirst tlast map List.last];
    rewrite !app_nil_r, !Z.mul_0_r, !Z.sub_0_r, !Z.add_0_r in *;
    do 14 eexists; eexists; split; [reflexivity|];
    split; [ eapply munch_weaken; [| exact MU]; apply sub_fp_by_incl';
             constructor; [apply Exists_exists; eexists; split; [left; reflexivity| cbn; lia]|];
             constructor; [apply Exists_exists; eexists; split; [right; left; reflexivity| cbn; lia]|]; constructor |];
    split; [exact WM|]; split; [assumption|]; split; [exact ST|];
    split; [exact LS|]; split; [exact CH|]; split; [exact TM| exact CT].
  destruct X as [|cur R].
  - (* [comment removed for export] *)
    cbn [tfirst tlast map List.last length Z.of_nat] in LS.
    step. step. if_lit.                        (* [comment removed for export] *)
    exit2 sp MU WM ST FR CH CT GEO LS TM.
  - (* [comment removed for export] *)
    pose proof CH as CH0.
    destruct (proj1 (chain_cons _ _ _ _ _) CH) as [BC CHR]. clear CH. rename CH0 into CH.
    (nd_pre BC 6%nat; intros CC EC JC CCNT CLEN CRNG; nd_post).
    assert (GC : bgeom L LST TMP cur) by (eapply (proj1 (Forall_forall _ _) GEO); left; reflexivity).
    assert (RC : rng RNG (baddr L cur) Q_BATCH_BYTES) by (pose proof (Forall_inv RB) as X; exact X).
    unfold bgeom, AIMG_HI, Q_BATCH_BYTES in GC, RC. unfold baddr in GC, RC. cbn [fst snd] in CC, GC, RC. cbn [tfirst tlast map List.last] in LS. unfold baddr in LS.
    set (CUR := abatch_addr L (qb_slot (snd cur))) in *. (nd_pre GC 4%nat; intros GC1 GC2 GC3 GC4; nd_post).
    xport CC MU WM ltac:(clear -GC2 GC3 CEIL LO; lia).
    clear EC JC.
    step. step. if_cases KC; zify_cond KC.     (* [comment removed for export] *)
    { exfalso. rewrite ?unsigned_lit in KC by (clear -GC1 GC2; lia). clear -KC GC1. lia. }
    clear KC.
    destruct R as [|nx R'].
    + (* [comment removed for export] *)
      cbn [tfirst] in CC.
      step. step. if_lit.                      (* [comment removed for export] *)
      clear CC. exit2 sp MU WM ST FR CH CT GEO LS TM.
    + (* [comment removed for export] *)
      assert (GN : bgeom L LST TMP nx) by (eapply (proj1 (Forall_forall _ _) GEO); right; left; reflexivity).
      unfold bgeom, AIMG_HI, Q_BATCH_BYTES, baddr in GN. cbn [tfirst] in CC. unfold baddr in CC.
      set (NXT := abatch_addr L (qb_slot (snd nx))) in *. (nd_pre GN 4%nat; intros GN1 GN2 GN3 GN4; nd_post).
      step. step. if_cases KN; zify_cond KN.   (* [comment removed for export] *)
      { exfalso. rewrite ?unsigned_lit in KN by (clear -GN1 GN2; lia). clear -KN GN1. lia. }
      clear KN.
      step. step. step. step. step.            (* [comment removed for export] *)
      chain_over CH MU WM GEO ltac:(fun _ => left). chain_over CT MU WM GEO ltac:(fun _ => right).
      clear CC CHR.
      eapply evtF_cut.
      { eapply (mloop_spec L RNG LST TMP CUR lb tf0 tl0) with (P := []) (R := nx :: R') (T := T) (tb := tb) (ex := 0) (d := length (nx :: R'));
          try eassumption; try reflexivity.
        - apply Z_to_bv_eqm. reflexivity.
        - clear -GC1 GC2. lia.
        - congruence.
        - revert TB1. clear. unfold Q_BATCH_BYTES. cbn [length]. intros; lia.
        - revert LEN40. clear. unfold Q_BATCH_BYTES. rewrite length_app. cbn [length]. intros; lia. }
      cbv beta. unfold mloop_post, amerge_post. cbn [amerge_fun].
      destruct (merge_bq cur (nx :: R')) as [l e] eqn:MB.
      intros ms' (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & m' & -> & MU' & WM' & MI' & LS' & CH' & TM' & CT').
      clear LS TM MI.
      xport FR MU' WM' ltac:(cbn [app disjoint_from fst snd]; split; [clear -CEIL LO L2; lia| split; [clear -DTS LO; lia| eapply disj_objs_above; [exact GEO| atop_facts; clear -CEIL LO; lia]]]).
      xport ST MU' WM' ltac:(cbn [app disjoint_from fst snd]; split; [clear -CEIL LO L2; lia| split; [clear -DTS LO; lia| eapply disj_objs_above; [exact GEO| atop_facts; clear -CEIL LO; lia]]]).
      box MU'.
      snapshot [(bv_unsigned sp + -16, bv_unsigned sp); (LST + 24, LST + 32)]%Z MUe WMe.
      step. zstep.                             (* [comment removed for export] *)
      setreg 11%Z (Z_to_bv 64 (lb - Q_BATCH_BYTES * Z.of_nat (length e))) ltac:(apply Z_to_bv_eqm; unfold Q_BATCH_BYTES; clear; Z.div_mod_to_equations; lia).
      step.                                    (* [comment removed for export] *)
      step. step. step.                        (* [comment removed for export] *)
      release_frame FR ST (bv_unsigned sp).
      apply evtF_done. cbn [length app] in LS'. cbn [app] in CH'.
      do 14 eexists. eexists. split; [reflexivity|].
      split. { (* [comment removed for export] *)
        unbox MU'.
        lazymatch goal with |- munch ?W m ?mf =>
          assert (S1 : sub_fp [(bv_unsigned sp + -16, bv_unsigned sp); (LST + 24, LST + 32)]%Z W);
          [ apply sub_fp_by_incl';
            constructor; [apply Exists_exists; eexists; split; [left; reflexivity| cbn; clear; lia]|];
            constructor; [apply Exists_exists; eexists; split; [right; left; reflexivity| cbn; clear; lia]|]; constructor |] end.
        lazymatch goal with |- munch ?W m ?mf =>
          assert (MU2 : munch W m0 mf); [eapply (munch_trans_w W _ _ _ _ _ MU' MUe); [| exact S1]
                                        |eapply (munch_trans_w W _ _ _ _ _ MU MU2); [exact S1| intros z Hz; exact Hz]] end.
        apply sub_fp_by_incl'. apply Forall_app. split.
        - constructor; [apply Exists_exists; eexists; split; [right; left; reflexivity| cbn; clear; lia]|].
          constructor; [apply Exists_exists; eexists; split; [right; right; left; reflexivity| cbn; clear; lia]|]. constructor.
        - apply Forall_map. apply Forall_forall. intros x Hx. apply Exists_exists. eexists. split; [right; right; right; apply in_map; exact Hx|]. cbn; clear; lia. }
      split; [eapply wmono_trans; [exact WM| first [exact WM'| eapply wmono_trans; [exact WM'| exact WMe]]]|]. split; [assumption|]. split; [exact ST|].
      split. { cbn [tfirst]. unfold baddr. fold CUR. exact LS'. }
      split. { eapply chain_frame; [exact CH'| exact MUe| exact WMe|]. apply Forall_forall. intros x Hx.
               (nd_pre (merge_bq_baddr_in L (nx :: R') cur x ltac:(rewrite MB; apply in_app_iff; left; exact Hx)) 3%nat; intros y Hy EY; nd_post).
               rewrite <- EY. pose proof (proj1 (Forall_forall _ _) GEO y ltac:(apply in_app_iff; left; exact Hy)) as G.
               unfold bgeom, AIMG_HI, Q_BATCH_BYTES in G. unfold Q_BATCH_BYTES. cbn [disjoint_from fst snd]. clear -G CEIL LO. lia. }
      split; [exact TM'|].
      eapply chain_frame; [exact CT'| exact MUe| exact WMe|]. apply Forall_app. split.
      * apply Forall_forall. intros x Hx. pose proof (proj1 (Forall_forall _ _) GEO x ltac:(apply in_app_iff; right; exact Hx)) as G.
        unfold bgeom, AIMG_HI, Q_BATCH_BYTES in G. unfold Q_BATCH_BYTES. cbn [disjoint_from fst snd]. clear -G CEIL LO. lia.
      * apply Forall_forall. intros x Hx.
        (nd_pre (merge_bq_baddr_in L (nx :: R') cur x ltac:(rewrite MB; apply in_app_iff; right; exact Hx)) 3%nat; intros y Hy EY; nd_post).
        rewrite <- EY. pose proof (proj1 (Forall_forall _ _) GEO y ltac:(apply in_app_iff; left; exact Hy)) as G.
        unfold bgeom, AIMG_HI, Q_BATCH_BYTES in G. unfold Q_BATCH_BYTES. cbn [disjoint_from fst snd]. clear -G CEIL LO. lia.
Qed.
End CANSEC2.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AKitR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma firstn_S_snoc : forall {X} (l : list X) i x, nth_error l i = Some x -> firstn (Datatypes.S i) l = firstn i l ++ [x].
Proof.
  intros X l. induction l as [|y l IH]; intros [|i] x H; cbn in *; try discriminate.
  - inversion H. reflexivity.
  - rewrite (IH i x H). reflexivity.
Qed.

Definition amerge_entry : Z := 0x35cec.
Definition amerge_loop : Z := 0x35d24.     (* [comment removed for export] *)
Definition amerge_copy : Z := 0x35d5c.     (* [comment removed for export] *)
Definition amerge_copied : Z := 0x35d70.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma mcopy_loop_spec : forall RNG (d : nat) (i n SRC DST : Z) (src ws0 : list word)
    ra sp gp tp t0 t1 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 (F : bvmap 5 word) fc (m : amem),
  d = Z.to_nat (n - i) ->
  0 <= i < n -> length src = Z.to_nat n -> (n <= Z.of_nat (length ws0))%Z ->
  u64arr asegs m SRC src ->
  u64arr asegs m DST (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) ws0) ->
  mem_inv asegs m ->
  0 <= SRC -> SRC + 8 * n < 2^47 -> 0 <= DST -> DST + 8 * Z.of_nat (length ws0) < 2^47 ->
  (SRC + 8 * n <= DST \/ DST + 8 * Z.of_nat (length ws0) <= SRC) ->
  rng RNG SRC (8 * n) -> rng RNG DST (8 * n) ->
  evtF asegs RNG (fun ms' => exists t5' m',
      ms' = MS (mkR ra sp gp tp t0 t1 (Z_to_bv 64 (SRC + 8 * n)) s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (DST + 8 * n)) (Z_to_bv 64 (SRC + 8 * n)) t5' t6) F (Z_to_bv 64 amerge_copied) fc None m' (seg_rom asegs)
      /\ munch [(DST, DST + 8 * n)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ u64arr asegs m' SRC src /\ u64arr asegs m' DST (src ++ skipn (Z.to_nat n) ws0))
    (MS (mkR ra sp gp tp t0 t1 (Z_to_bv 64 (SRC + 8 * i)) s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (DST + 8 * i)) (Z_to_bv 64 (SRC + 8 * n)) t5 t6) F (Z_to_bv 64 amerge_copy) fc None m (seg_rom asegs)).
Proof.
  intros RNG d. induction d as [|d IH]; intros until m; intros HD I LS LW SRCA DSTA MI S0 S1 D0 D1 DJ RS RD; [lia|].
  unfold amerge_copy, amerge_copied in *.
  pose proof (munch_refl [(DST, DST + 8 * n)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  destruct (nth_error src (Z.to_nat i)) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; lia].
  assert (LD : length (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) ws0) = length ws0) by (rewrite length_app, length_firstn, length_skipn; lia).
  pose proof (u64arr_read asegs _ _ src i w (wa (SRC + 8 * i)) SRCA NTH ltac:(lia) eq_refl) as RDV.
  assert (RS1 : rng RNG (SRC + 8 * i) 8) by (eapply rng_sub'; [exact RS| lia]).
  assert (RD1 : rng RNG (DST + 8 * i) 8) by (eapply rng_sub'; [exact RD| lia]).
  step. clear RDV RS1.                                   (* [comment removed for export] *)
  zstep.                                                 (* [comment removed for export] *)
  setreg 7 (Z_to_bv 64 (SRC + 8 * (i + 1))) ltac:(f_equal; clear; lia).
  pose proof (u64arr_store_ok asegs m DST _ i (wa (DST + 8 * i)) DSTA ltac:(rewrite LD; lia) eq_refl) as SOK.
  step.                                                  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ ?a (le8 ?v)) _) =>
    let E := lazymatch a with wa ?E => E | Z_to_bv _ ?E => E end in
    pose proof (u64arr_write asegs m DST _ i v DSTA ltac:(rewrite LD; lia)) as DST2;
    replace (DST + 8 * i)%Z with E in DST2 by lia
  end.
  replace (upd (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) ws0) (Z.to_nat i) w)
     with (firstn (Z.to_nat (i + 1)) src ++ skipn (Z.to_nat (i + 1)) ws0) in DST2.
  2:{ rewrite upd_firstn_skipn by (rewrite LD; lia).
      rewrite firstn_app, firstn_firstn, Nat.min_id, length_firstn.
      replace (Z.to_nat i - Nat.min (Z.to_nat i) (length src))%nat with 0%nat by lia. rewrite firstn_O, app_nil_r.
      rewrite skipn_app, length_firstn. replace (Datatypes.S (Z.to_nat i) - Nat.min (Z.to_nat i) (length src))%nat with 1%nat by lia.
      rewrite skipn_skipn. replace (1 + Z.to_nat i)%nat with (Z.to_nat (i + 1)) by lia.
      replace (Z.to_nat (i + 1)) with (Datatypes.S (Z.to_nat i)) at 1 by lia.
      rewrite (firstn_S_snoc _ _ _ NTH), (skipn_all2 (firstn (Z.to_nat i) src)) by (rewrite length_firstn; lia).
      rewrite <- app_assoc. reflexivity. }
  assert (SRC2 : u64arr asegs (write_to_mem m (wa (DST + 8 * i)) (le8 w)) SRC src).
  { apply Arr.u64arr_frame; [exact SRCA| lia| rewrite length_le8; lia| rewrite length_le8; lia]. }
  clear DSTA SRCA. store_done. try clear SOK. clear RD1.
  zstep.                                                 (* [comment removed for export] *)
  setreg 28 (Z_to_bv 64 (DST + 8 * (i + 1))) ltac:(f_equal; clear; lia).
  step. if_cases K; zify_cond K.                         (* [comment removed for export] *)
  - (* [comment removed for export] *)
    rewrite ?unsigned_lit in K by lia.
    eapply evtF_mono.
    { eapply (IH (i + 1) n SRC DST src ws0); try eassumption; try lia. }
    cbv beta. intros ms' (t5' & m' & -> & MU2 & WM2 & MI2 & SR3 & DS3).
    exists t5', m'. split; [reflexivity|].
    split; [eapply munch_trans; [exact MU| exact MU2]|]. split; [eapply wmono_trans; [exact WM| exact WM2]|].
    split; [exact MI2|]. split; [exact SR3| exact DS3].
  - (* [comment removed for export] *)
    rewrite ?unsigned_lit in K by lia. assert (EI : i + 1 = n) by lia.
    apply evtF_done. rewrite EI in DST2 |- *. eexists _, _. split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact SRC2|].
    rewrite firstn_all2 in DST2 by lia. exact DST2.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma u64arr_app2 : forall m A ws1 ws2,
  u64arr asegs m A ws1 -> u64arr asegs m (A + 8 * Z.of_nat (length ws1)) ws2 -> u64arr asegs m A (ws1 ++ ws2).
Proof.
  intros m A ws1 ws2 [HB HW] [HB2 HW2]. split.
  - rewrite u64s_app. apply bytes_at_app. split; [exact HB|]. rewrite u64s_length.
    replace (A + Z.of_nat (8 * length ws1)) with (A + 8 * Z.of_nat (length ws1)) by lia. exact HB2.
  - rewrite length_app. (nd_pre HW 3%nat; intros H0 H1 HW; nd_post). (nd_pre HW2 3%nat; intros H2 H3 HW2; nd_post).
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i (8 * Z.of_nat (length ws1))); [apply HW; lia|].
    replace (A + i) with (A + 8 * Z.of_nat (length ws1) + (i - 8 * Z.of_nat (length ws1))) by lia. apply HW2. lia.
Qed.

#[using="Type"] Lemma u64arr_app_inv : forall m A ws1 ws2, u64arr asegs m A (ws1 ++ ws2) ->
  u64arr asegs m A ws1 /\ u64arr asegs m (A + 8 * Z.of_nat (length ws1)) ws2.
Proof.
  intros m A ws1 ws2 [HB HW]. rewrite u64s_app in HB. apply bytes_at_app in HB. destruct HB as [HB1 HB2].
  rewrite u64s_length in HB2. replace (A + Z.of_nat (8 * length ws1)) with (A + 8 * Z.of_nat (length ws1)) in HB2 by lia.
  rewrite length_app in HW. (nd_pre HW 3%nat; intros H0 H1 HW; nd_post).
  split; split; try assumption.
  - split; [lia|]. split; [lia|]. intros i Hi. apply HW. lia.
  - split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + 8 * Z.of_nat (length ws1) + i) with (A + (8 * Z.of_nat (length ws1) + i)) by lia. apply HW. lia.
Qed.

#[using="Type"] Lemma junk_of_u64arr : forall m A ws, u64arr asegs m A ws -> junk_at m A (8 * Z.of_nat (length ws)).
Proof.
  intros m A ws [B W]. exists (u64s ws). split; [split|].
  - cbn. split; [rewrite u64s_length; lia| exact I].
  - cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize Nat.add]. replace (Z.of_nat (Z.to_nat (8 * Z.of_nat (length ws)) + 0)) with (8 * Z.of_nat (length ws)) by lia. exact W.
Qed.

#[using="Type"] Lemma u64arr_of_junk : forall m A n, junk_at m A (8 * n) -> 0 <= n ->
  exists ws, u64arr asegs m A ws /\ length ws = Z.to_nat n.
Proof.
  intros m A n [bs H] Hn. replace (Z.to_nat (8 * n)) with (8 * Z.to_nat n)%nat in H by lia.
  destruct (u64arr_of_CB m A (Z.to_nat n) bs H) as [U L]. exists (words_of_bytes bs). split; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mcore_post (ra sp gp tp s0 s1 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (CUR NXT LST nxn szc szn cc cn ls : Z) (ec en : list word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t2 t3 t4 t5 m',
    ms' = MS (mkR ra sp gp tp (Z_to_bv 64 NXT) (Z_to_bv 64 (cc + cn)) t2 s0 s1 (Z_to_bv 64 LST) a1 a2 (Z_to_bv 64 ls) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x35d90) fc None m' (seg_rom asegs)
    /\ munch [(CUR + 8, CUR + 24); (CUR + 24 + 8 * cc, CUR + 24 + 8 * (cc + cn)); (NXT + 8, NXT + 24)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' CUR [C8 (Z_to_bv 64 NXT); C8 (Z_to_bv 64 (szc + szn - Q_BATCH_BYTES)); C8 (Z_to_bv 64 (cc + cn))]
    /\ u64arr asegs m' (CUR + 24) (ec ++ en)
    /\ junk_at m' (CUR + 24 + 8 * (cc + cn)) (Q_BATCH_BYTES - 24 - 8 * (cc + cn))
    /\ rw_cells asegs m' NXT [C8 (Z_to_bv 64 nxn); C8 (Z_to_bv 64 Q_BATCH_BYTES); C8 (Z_to_bv 64 0)]
    /\ junk_at m' (NXT + 24) (Q_BATCH_BYTES - 24).

Definition mcore_spec__stmt : Prop := forall RNG ra sp gp tp t2 s0 s1 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 (F : bvmap 5 word) fc (m : amem)
    (CUR NXT LST nxn szc szn cc cn ls lf ll lb : Z) (ec en : list word),
  mem_inv asegs m ->
  rw_cells asegs m CUR [C8 (Z_to_bv 64 NXT); C8 (Z_to_bv 64 szc); C8 (Z_to_bv 64 cc)] ->
  u64arr asegs m (CUR + 24) ec -> length ec = Z.to_nat cc ->
  junk_at m (CUR + 24 + 8 * cc) (Q_BATCH_BYTES - 24 - 8 * cc) ->
  rw_cells asegs m NXT [C8 (Z_to_bv 64 nxn); C8 (Z_to_bv 64 szn); C8 (Z_to_bv 64 cn)] ->
  u64arr asegs m (NXT + 24) en -> length en = Z.to_nat cn ->
  junk_at m (NXT + 24 + 8 * cn) (Q_BATCH_BYTES - 24 - 8 * cn) ->
  rw_cells asegs m LST [C8 (Z_to_bv 64 ls); C8 (Z_to_bv 64 lf); C8 (Z_to_bv 64 ll); C8 (Z_to_bv 64 lb)] ->
  Q_BATCH_BYTES <= szc < 2^63 -> 0 <= szn < 2^63 -> 0 <= cc -> 0 <= cn -> cc + cn <= Q_BATCH -> 0 <= nxn < 2^64 -> 0 <= ls < 2^64 ->
  AIMG_HI <= CUR -> CUR + Q_BATCH_BYTES <= ATOP -> AIMG_HI <= NXT -> NXT + Q_BATCH_BYTES <= ATOP ->
  (CUR + Q_BATCH_BYTES <= NXT \/ NXT + Q_BATCH_BYTES <= CUR) ->
  (LST + 32 <= CUR \/ CUR + Q_BATCH_BYTES <= LST) -> (LST + 32 <= NXT \/ NXT + Q_BATCH_BYTES <= LST) -> 0 <= LST -> LST + 32 <= ATOP ->
  a6 = Z_to_bv 64 (2^64 - Q_BATCH_BYTES) -> a7 = Z_to_bv 64 Q_BATCH_BYTES ->
  rng RNG CUR Q_BATCH_BYTES -> rng RNG NXT Q_BATCH_BYTES -> rng RNG LST 32 ->
  evtF asegs RNG (mcore_post ra sp gp tp s0 s1 a1 a2 (Z_to_bv 64 CUR) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 F fc CUR NXT LST nxn szc szn cc cn ls ec en m)
    (MS (mkR ra sp gp tp (Z_to_bv 64 NXT) (Z_to_bv 64 (cn + cc)) t2 s0 s1 (Z_to_bv 64 LST) a1 a2 a3 (Z_to_bv 64 CUR) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 cn) (Z_to_bv 64 cc) t5 t6) F (Z_to_bv 64 0x35d34) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 4).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 5).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 6).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 7).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 8).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 9).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 10).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 11).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 12).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 13).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 14).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 15).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 16).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 17).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 18).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 19).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 20).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 21).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 22).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 23).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 24).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 25).
Variable F : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 26).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 27).
Variable m : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 28).
Variable CUR : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 29).
Variable NXT : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 30).
Variable LST : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 31).
Variable nxn : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 32).
Variable szc : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 33).
Variable szn : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 34).
Variable cc : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 35).
Variable cn : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 36).
Variable ls : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 37).
Variable lf : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 38).
Variable ll : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 39).
Variable lb : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 40).
Variable ec : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 41).
Variable en : ltac2:(SecDietF.SzSecF.ty 'mcore_spec__stmt 42).
#[using="Type"] Lemma mcore_spec__body : ltac:(let T := type of (fun (h : mcore_spec__stmt) => h RNG ra sp gp tp t2 s0 s1 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 F fc m CUR NXT LST nxn szc szn cc cn ls lf ll lb ec en) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t2, (s0, (s1, (a1, (a2, (a3, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t5, (t6, (F, (fc, (m, (CUR, (NXT, (LST, (nxn, (szc, (szn, (cc, (cn, (ls, (lf, (ll, (lb, (ec, en))))))))))))))))))))))))))))))))))))))))))) as _.
 intros MI CC EC LEC JC CN EN LEN JN LS SZC SZN C0 N0 FIT NXN LSR C1 C2 N1 N2 DCN DLC DLN L1 L2 -> -> RC RN RL.
  unfold AIMG_HI, Q_BATCH_BYTES, Q_BATCH in *.
  pose proof (munch_refl [(CUR + 8, CUR + 24); (CUR + 24 + 8 * cc, CUR + 24 + 8 * (cc + cn)); (NXT + 8, NXT + 24)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  step.                                                   (* [comment removed for export] *)
  zstep.                                                  (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0.                        (* [comment removed for export] *)
  { exfalso. revert K0 SZC. clear. intros K0 SZC. rewrite ?unsigned_lit in K0 by lia. rewrite Z.shiftr_div_pow2 in K0 by lia.
    rewrite ?unsigned_lit in K0 by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations. lia. }
  clear K0.
  step. if_cases KZ; zify_cond KZ.                        (* [comment removed for export] *)
  - (* [comment removed for export] *)
    rewrite ?unsigned_lit in KZ by lia.
    assert (cn = 0) by lia. subst cn.
    assert (en = []) by (destruct en; [reflexivity| cbn in LEN; lia]). subst en.
    step.                                                 (* [comment removed for export] *)
    zstep.                                                (* [comment removed for export] *)
    step.                                                 (* [comment removed for export] *)
    zstep.                                                (* [comment removed for export] *)
    setreg 7 (Z_to_bv 64 (szc + szn - 8192)) ltac:(apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.pow_pos Pos.iter Z.mul]; 
                                                    clear -SZC SZN; Z.div_mod_to_equations; lia).
    destruct JC as [jc JC]. destruct JN as [jn JN].
    step.                                                 (* [comment removed for export] *)
    step.                                                 (* [comment removed for export] *)
    step.                                                 (* [comment removed for export] *)
    step.                                                 (* [comment removed for export] *)
    apply evtF_done. unfold mcore_post, Q_BATCH_BYTES. rewrite !Z.add_0_r. replace (cc + 0) with cc in MU by lia.
    replace (0 + cc) with cc in * by lia.
    replace (NXT + 24 + 8 * 0) with (NXT + 24) in JN by lia. replace (8192 - 24 - 8 * 0) with (8192 - 24) in JN by lia.
    do 4 eexists. exists m1. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact CC|].
    split; [rewrite app_nil_r; exact EC|]. split; [exists jc; exact JC|]. split; [exact CN|]. exists jn; exact JN.
  - (* [comment removed for export] *)
    rewrite ?unsigned_lit in KZ by lia.
    do 6 zstep.                                           (* [comment removed for export] *)
    setreg 7 (Z_to_bv 64 (NXT + 24 + 8 * 0)) ltac:(f_equal; clear; lia).
    setreg 28 (Z_to_bv 64 (CUR + 24 + 8 * cc + 8 * 0)) ltac:(rewrite ?Z.shiftl_mul_pow2 by (clear; lia); f_equal; clear -C0; lia).
    setreg 29 (Z_to_bv 64 (NXT + 24 + 8 * cn)) ltac:(rewrite ?Z.shiftl_mul_pow2 by (clear; lia); f_equal; clear -N0; lia).
    replace (8192 - 24 - 8 * cc) with (8 * cn + (8192 - 24 - 8 * cc - 8 * cn)) in JC by lia.
    destruct (junk_split m _ _ _ JC ltac:(lia) ltac:(lia)) as [J1 J2]. clear JC.
    (nd_pre (u64arr_of_junk m _ cn J1 ltac:(lia)) 3%nat; intros ws0 WS0 LWS0; nd_post). clear J1.
    destruct J2 as [jc J2]. destruct JN as [jn JN].
    eapply evtF_cut.
    { eapply (mcopy_loop_spec RNG _ 0 cn (NXT + 24) (CUR + 24 + 8 * cc) en ws0); try reflexivity.
      - lia.
      - exact LEN.
      - rewrite LWS0. lia.
      - exact EN.
      - cbn [Z.to_nat firstn skipn app]. exact WS0.
      - exact MI.
      - lia. - lia. - lia.
      - rewrite LWS0. lia.
      - rewrite LWS0. destruct DCN; [right| left]; lia.
      - eapply rng_sub'; [exact RN| lia].
      - eapply rng_sub'; [exact RC| lia]. }
    cbv beta. intros ms' (t5' & m3 & -> & MU3 & WM3 & MI3 & SR3 & DS3).
    xport CC MU3 WM3 ltac:(clear -C0 N0; lia).
    xport CN MU3 WM3 ltac:(clear -C0 N0 FIT DCN; lia).
    xport LS MU3 WM3 ltac:(clear -C0 N0 FIT DLC; lia).
    xport EC MU3 WM3 ltac:(rewrite ?LEC; clear -C0 N0; lia).
    xport J2 MU3 WM3 ltac:(clear -C0 N0 FIT; lia).
    xport JN MU3 WM3 ltac:(clear -C0 N0 FIT DCN; lia).
    clear MI WS0 MU WM. box MU3.
    rewrite skipn_all2 in DS3 by (rewrite LWS0; lia). rewrite app_nil_r in DS3. box DS3. box SR3.
    snapshot [(CUR + 8, CUR + 24); (NXT + 8, NXT + 24)]%Z MUs WMs.
    step.                                                 (* [comment removed for export] *)
    zstep.                                                (* [comment removed for export] *)
    step.                                                 (* [comment removed for export] *)
    zstep.                                                (* [comment removed for export] *)
    setreg 7 (Z_to_bv 64 (szc + szn - 8192)) ltac:(apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.pow_pos Pos.iter Z.mul];
                                                    clear -SZC SZN; Z.div_mod_to_equations; lia).
    step.                                                 (* [comment removed for export] *)
    step.                                                 (* [comment removed for export] *)
    step.                                                 (* [comment removed for export] *)
    step.                                                 (* [comment removed for export] *)
    apply evtF_done. unfold mcore_post, Q_BATCH_BYTES. unbox MU3.
    unbox DS3. xport DS3 MUs WMs ltac:(rewrite ?LEN; clear -C0 N0 DCN FIT; lia).
    unbox SR3. xport SR3 MUs WMs ltac:(rewrite ?LEN; clear -C0 N0 DCN FIT; lia).
    replace (cn + cc) with (cc + cn) in * by lia.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] =>
      assert (MUF : munch [(CUR + 8, CUR + 24); (CUR + 24 + 8 * cc, CUR + 24 + 8 * (cc + cn)); (NXT + 8, NXT + 24)]%Z m mx)
        by (eapply (munch_trans_w _ _ _ _ _ _ MU3 MUs); solve_sub_fpw ltac:(clear -C0 N0; lia)) end.
    do 4 eexists. eexists. split; [reflexivity|].
    split; [exact MUF|]. split; [first [exact WM3 | eapply wmono_trans; [exact WM3| exact WMs]]|]. split; [assumption|]. split; [exact CC|].
    split. { apply u64arr_app2; [exact EC|]. rewrite LEC, Z2Nat.id by lia. exact DS3. }
    split. { exists jc. replace (CUR + 24 + 8 * (cc + cn)) with (CUR + 24 + 8 * cc + 8 * cn) by lia.
             replace (8192 - 24 - 8 * (cc + cn)) with (8192 - 24 - 8 * cc - 8 * cn) by lia. exact J2. }
    split; [exact CN|].
    replace (8192 - 24) with (8 * cn + (8192 - 24 - 8 * cn)) by lia. apply junk_merge; [| | lia| lia].
    + replace (8 * cn) with (8 * Z.of_nat (length en)) by (rewrite LEN; lia). apply junk_of_u64arr. exact SR3.
    + exists jn. exact JN.
Qed.
End Zd1.
#[using="Type"] Lemma mcore_spec : ltac:(let t := eval cbv delta [mcore_spec__stmt] in mcore_spec__stmt in exact t).
Proof. exact mcore_spec__body. Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition munlink_post (tfull : bool) (ra sp gp tp t0 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (CUR NXT LST TMP TL nxn szc cc szn cn ls lf ll lb tn tf tb ex : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t1 t2 a3 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 LST) (Z_to_bv 64 TMP) (Z_to_bv 64 (ex + Q_BATCH_BYTES)) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x35e00) fc None m' (seg_rom asegs)
    /\ munch ([(CUR, CUR + 8); (NXT, NXT + 8); (LST, LST + 24); (TMP, TMP + 32)] ++ (if tfull then [(TL, TL + 8)] else []))%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' CUR [C8 (Z_to_bv 64 nxn); C8 (Z_to_bv 64 szc); C8 (Z_to_bv 64 cc)]
    /\ rw_cells asegs m' NXT [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 szn); C8 (Z_to_bv 64 cn)]
    /\ rw_cells asegs m' LST [C8 (Z_to_bv 64 (ls - 1)); C8 (Z_to_bv 64 lf); C8 (Z_to_bv 64 (if ll =? NXT then CUR else ll)); C8 (Z_to_bv 64 lb)]
    /\ rw_cells asegs m' TMP [C8 (Z_to_bv 64 (tn + 1)); C8 (Z_to_bv 64 (if tfull then tf else NXT)); C8 (Z_to_bv 64 NXT); C8 (Z_to_bv 64 (tb + Q_BATCH_BYTES))]
    /\ (if tfull then rw_cells asegs m' TL [C8 (Z_to_bv 64 NXT)] else True).

Definition munlink_spec__stmt : Prop := forall (tfull : bool) RNG ra sp gp tp t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : amem)
    (CUR NXT LST TMP TL nxn szc cc szn cn ls lf ll lb tn tf tl tb ex tlx : Z),
  mem_inv asegs m ->
  rw_cells asegs m CUR [C8 (Z_to_bv 64 NXT); C8 (Z_to_bv 64 szc); C8 (Z_to_bv 64 cc)] ->
  rw_cells asegs m NXT [C8 (Z_to_bv 64 nxn); C8 (Z_to_bv 64 szn); C8 (Z_to_bv 64 cn)] ->
  rw_cells asegs m LST [C8 (Z_to_bv 64 ls); C8 (Z_to_bv 64 lf); C8 (Z_to_bv 64 ll); C8 (Z_to_bv 64 lb)] ->
  rw_cells asegs m TMP [C8 (Z_to_bv 64 tn); C8 (Z_to_bv 64 tf); C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 tb)] ->
  (if tfull then tl = TL else True) -> 0 <= tl < 2^64 ->
  0 < ls < 2^63 -> 0 <= ll < 2^64 -> 0 <= nxn < 2^64 -> 0 <= tn < 2^63 -> 0 <= tf < 2^64 -> 0 <= tb -> tb + Q_BATCH_BYTES < 2^63 ->
  0 <= ex -> ex + Q_BATCH_BYTES < 2^63 ->
  AIMG_HI <= CUR -> CUR + Q_BATCH_BYTES <= ATOP -> AIMG_HI <= NXT -> NXT + Q_BATCH_BYTES <= ATOP ->
  0 <= LST -> LST + 32 <= ATOP -> 0 <= TMP -> TMP + 32 <= 2^47 ->
  (CUR + Q_BATCH_BYTES <= NXT \/ NXT + Q_BATCH_BYTES <= CUR) ->
  (LST + 32 <= CUR \/ CUR + Q_BATCH_BYTES <= LST) -> (LST + 32 <= NXT \/ NXT + Q_BATCH_BYTES <= LST) ->
  (TMP + 32 <= CUR \/ CUR + Q_BATCH_BYTES <= TMP) -> (TMP + 32 <= NXT \/ NXT + Q_BATCH_BYTES <= TMP) ->
  (TMP + 32 <= LST \/ LST + 32 <= TMP) ->
  (if tfull then 0 < tn /\ rw_cells asegs m TL [C8 (Z_to_bv 64 tlx)] /\ AIMG_HI <= TL /\ TL + Q_BATCH_BYTES <= ATOP
                 /\ (TL + Q_BATCH_BYTES <= CUR \/ CUR + Q_BATCH_BYTES <= TL) /\ (TL + Q_BATCH_BYTES <= NXT \/ NXT + Q_BATCH_BYTES <= TL)
                 /\ (LST + 32 <= TL \/ TL + Q_BATCH_BYTES <= LST) /\ (TMP + 32 <= TL \/ TL + Q_BATCH_BYTES <= TMP) /\ rng RNG TL 8
   else tn = 0) ->
  a7 = Z_to_bv 64 Q_BATCH_BYTES ->
  rng RNG CUR Q_BATCH_BYTES -> rng RNG NXT Q_BATCH_BYTES -> rng RNG LST 32 -> rng RNG TMP 32 ->
  evtF asegs RNG (munlink_post tfull ra sp gp tp (Z_to_bv 64 NXT) s0 s1 (Z_to_bv 64 CUR) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
                     CUR NXT LST TMP TL nxn szc cc szn cn ls lf ll lb tn tf tb ex m)
    (MS (mkR ra sp gp tp (Z_to_bv 64 NXT) t1 t2 s0 s1 (Z_to_bv 64 LST) (Z_to_bv 64 TMP) (Z_to_bv 64 ex) (Z_to_bv 64 ls) (Z_to_bv 64 CUR) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x35d90) fc None m (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable tfull : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 9).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 10).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 11).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 12).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 13).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 14).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 15).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 16).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 17).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 18).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 19).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 20).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 21).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 22).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 23).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 24).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 25).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 26).
Variable F : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 27).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 28).
Variable m : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 29).
Variable CUR : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 30).
Variable NXT : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 31).
Variable LST : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 32).
Variable TMP : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 33).
Variable TL : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 34).
Variable nxn : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 35).
Variable szc : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 36).
Variable cc : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 37).
Variable szn : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 38).
Variable cn : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 39).
Variable ls : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 40).
Variable lf : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 41).
Variable ll : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 42).
Variable lb : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 43).
Variable tn : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 44).
Variable tf : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 45).
Variable tl : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 46).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 47).
Variable ex : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 48).
Variable tlx : ltac2:(SecDietF.SzSecF.ty 'munlink_spec__stmt 49).
#[using="Type"] Lemma munlink_spec__body : ltac:(let T := type of (fun (h : munlink_spec__stmt) => h tfull RNG ra sp gp tp t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m CUR NXT LST TMP TL nxn szc cc szn cn ls lf ll lb tn tf tl tb ex tlx) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (tfull, (RNG, (ra, (sp, (gp, (tp, (t1, (t2, (s0, (s1, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (CUR, (NXT, (LST, (TMP, (TL, (nxn, (szc, (cc, (szn, (cn, (ls, (lf, (ll, (lb, (tn, (tf, (tl, (tb, (ex, tlx)))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros MI CC CN LS TM TLE TLR LSR LLR NXN TN TF TB TB2 EX EX2 C1 C2 N1 N2 L1 L2 T1 T2 DCN DLC DLN DTC DTN DTL TFULL -> RC RN RL RT.
  unfold AIMG_HI, Q_BATCH_BYTES in *.
  destruct tfull.
  - (nd_pre TFULL 9%nat; intros TN1 TLC TL1 TL2 DTLC DTLN DTLL DTLT RTL; nd_post). subst tl.
    pose proof (munch_refl ([(CUR, CUR + 8); (NXT, NXT + 8); (LST, LST + 24); (TMP, TMP + 32)] ++ [(TL, TL + 8)])%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM. cbn [app] in MU.
    step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.   (* [comment removed for export] *)
    step. step. step.                                     (* [comment removed for export] *)
    step. if_cases KL; zify_cond KL.                      (* [comment removed for export] *)
    + (* [comment removed for export] *)
      rewrite ?unsigned_lit in KL by lia.
      step. zstep. step. step. step.                      (* [comment removed for export] *)
      step. if_cases KT; zify_cond KT; [| exfalso; rewrite ?unsigned_lit in KT by lia; lia]. clear KT.   (* [comment removed for export] *)
      step. step. zstep. step.                            (* [comment removed for export] *)
      step. step. step. zstep. zstep. step.               (* [comment removed for export] *)
      apply evtF_done. unfold munlink_post. cbn [app].
      replace (ll =? NXT) with true by (symmetry; apply Z.eqb_eq; lia).
      replace (ls + -1) with (ls - 1) in LS by lia.
      do 3 eexists. eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact CC|]. split; [exact CN|]. split; [exact LS|]. split; [exact TM| exact TLC].
    + (* [comment removed for export] *)
      rewrite ?unsigned_lit in KL by lia.
      zstep. step. step. step.                            (* [comment removed for export] *)
      step. if_cases KT; zify_cond KT; [exfalso; rewrite ?unsigned_lit in KT by lia; lia|]. clear KT.   (* [comment removed for export] *)
      step. step. zstep. step.                            (* [comment removed for export] *)
      step. step. step. zstep. zstep. step.               (* [comment removed for export] *)
      apply evtF_done. unfold munlink_post. cbn [app].
      replace (ll =? NXT) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (ls + -1) with (ls - 1) in LS by lia.
      do 3 eexists. eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact CC|]. split; [exact CN|]. split; [exact LS|]. split; [exact TM| exact TLC].
  - subst tn. clear TLE.
    pose proof (munch_refl ([(CUR, CUR + 8); (NXT, NXT + 8); (LST, LST + 24); (TMP, TMP + 32)] ++ [])%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM. cbn [app] in MU.
    step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.   (* [comment removed for export] *)
    step. step. step.                                     (* [comment removed for export] *)
    step. if_cases KL; zify_cond KL.                      (* [comment removed for export] *)
    + rewrite ?unsigned_lit in KL by lia.
      step. zstep. step. step. step.                      (* [comment removed for export] *)
      step. if_cases KT; zify_cond KT; [exfalso; rewrite ?unsigned_lit in KT by lia; lia|]. clear KT.   (* [comment removed for export] *)
      step. zstep.                                        (* [comment removed for export] *)
      step. step. step. zstep. zstep. step.               (* [comment removed for export] *)
      apply evtF_done. unfold munlink_post. cbn [app].
      replace (ll =? NXT) with true by (symmetry; apply Z.eqb_eq; lia).
      replace (ls + -1) with (ls - 1) in LS by lia. change (0 + 1) with 1.
      do 3 eexists. eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact CC|]. split; [exact CN|]. split; [exact LS|]. split; [exact TM| exact I].
    + rewrite ?unsigned_lit in KL by lia.
      zstep. step. step. step.                            (* [comment removed for export] *)
      step. if_cases KT; zify_cond KT; [| exfalso; rewrite ?unsigned_lit in KT by lia; lia]. clear KT.   (* [comment removed for export] *)
      step. zstep.                                        (* [comment removed for export] *)
      step. step. step. zstep. zstep. step.               (* [comment removed for export] *)
      apply evtF_done. unfold munlink_post. cbn [app].
      replace (ll =? NXT) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (ls + -1) with (ls - 1) in LS by lia. change (0 + 1) with 1.
      do 3 eexists. eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact CC|]. split; [exact CN|]. split; [exact LS|]. split; [exact TM| exact I].
Qed.
End Zd2.
#[using="Type"] Lemma munlink_spec : ltac:(let t := eval cbv delta [munlink_spec__stmt] in munlink_spec__stmt in exact t).
Proof. exact munlink_spec__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bq := (abatch * qbatchc)%type.
Definition baddr (L : alayout) (x : bq) : Z := abatch_addr L (qb_slot (snd x)).
(* [comment removed for export] *)
Definition bq_merge (cur nx : bq) : bq :=
  (mkABatch (b_count (fst cur) + b_count (fst nx)) (b_size (fst cur) + (b_size (fst nx) - Q_BATCH_BYTES)) (b_chunks (fst nx) ++ b_chunks (fst cur)),
   mkQB (qb_slot (snd cur)) (qb_ks (snd nx) ++ qb_ks (snd cur))).
Definition bq_empty (nx : bq) : bq := (mkABatch 0 Q_BATCH_BYTES [], mkQB (qb_slot (snd nx)) []).

Fixpoint merge_bq (cur : bq) (rest : list bq) {struct rest} : list bq * list bq :=
  match rest with
  | [] => ([cur], [])
  | nx :: rest' =>
      if b_count (fst cur) + b_count (fst nx) <=? Q_BATCH then
        let '(l, ex) := merge_bq (bq_merge cur nx) rest' in (l, bq_empty nx :: ex)
      else
        let '(l, ex) := merge_bq nx rest' in (cur :: l, ex)
  end.

#[using="Type"] Lemma merge_bq_fst : forall rest cur,
  let '(l, ex, exb) := merge_batches (fst cur) (map fst rest) in
  map fst (fst (merge_bq cur rest)) = l /\ map fst (snd (merge_bq cur rest)) = ex /\ exb = Q_BATCH_BYTES * Z.of_nat (length (snd (merge_bq cur rest))).
Proof.
  induction rest as [|nx rest IH]; intros cur; cbn [merge_batches merge_bq map fst snd length].
  - cbn. repeat split; reflexivity.
  - destruct (b_count (fst cur) + b_count (fst nx) <=? Q_BATCH) eqn:E.
    + specialize (IH (bq_merge cur nx)). cbn [bq_merge fst] in IH.
      destruct (merge_batches _ (map fst rest)) as [[l ex] exb]. destruct (merge_bq _ rest) as [l2 ex2]. cbn [fst snd map length] in *.
      (nd_pre IH 3%nat; intros A B C; nd_post). rewrite A, B. repeat split; try reflexivity. lia.
    + specialize (IH nx). destruct (merge_batches (fst nx) (map fst rest)) as [[l ex] exb]. destruct (merge_bq nx rest) as [l2 ex2].
      cbn [fst snd map length] in *. (nd_pre IH 3%nat; intros A B C; nd_post). rewrite A, B. repeat split; try reflexivity. exact C.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tfirst (L : alayout) (T : list bq) (tf0 : Z) : Z := match T with [] => tf0 | x :: _ => baddr L x end.
Definition tlast (L : alayout) (T : list bq) (tl0 : Z) : Z := List.last (map (baddr L) T) tl0.

#[using="Type"] Lemma tlast_app1 : forall L T x tl0, tlast L (T ++ [x]) tl0 = baddr L x.
Proof. intros. unfold tlast. rewrite map_app. cbn. rewrite last_last. reflexivity. Qed.
#[using="Type"] Lemma tfirst_app : forall L T U tf0, T <> [] -> tfirst L (T ++ U) tf0 = tfirst L T tf0.
Proof. intros L [|x T] U tf0 H; [congruence| reflexivity]. Qed.
#[using="Type"] Lemma tlast_cons_ne : forall L x T tl0, T <> [] -> tlast L (x :: T) tl0 = tlast L T tl0.
Proof. intros L x [|y T] tl0 H; [congruence|]. unfold tlast. cbn [map]. destruct (map (baddr L) T); reflexivity. Qed.

#[using="Type"] Lemma merge_bq_ne : forall rest cur, fst (merge_bq cur rest) <> [].
Proof.
  induction rest as [|nx rest IH]; intros cur; cbn; [congruence|].
  destruct (_ <=? _); [specialize (IH (bq_merge cur nx)); destruct (merge_bq _ rest) | specialize (IH nx); destruct (merge_bq nx rest)]; cbn in *; congruence.
Qed.
#[using="Type"] Lemma merge_bq_first : forall L rest cur tf0, tfirst L (fst (merge_bq cur rest)) tf0 = baddr L cur.
Proof.
  induction rest as [|nx rest IH]; intros cur tf0; cbn; [reflexivity|].
  destruct (_ <=? _).
  - specialize (IH (bq_merge cur nx) tf0). destruct (merge_bq _ rest). cbn in *. rewrite IH. reflexivity.
  - destruct (merge_bq nx rest). reflexivity.
Qed.

(* [comment removed for export] *)
Definition bgeom (L : alayout) (LST TMP : Z) (x : bq) : Prop :=
  AIMG_HI <= baddr L x /\ baddr L x + Q_BATCH_BYTES <= ATOP
  /\ (LST + 32 <= baddr L x \/ baddr L x + Q_BATCH_BYTES <= LST)
  /\ (TMP + 32 <= baddr L x \/ baddr L x + Q_BATCH_BYTES <= TMP).

#[using="Type"] Lemma baddr_disj : forall L x y, qb_slot (snd x) <> qb_slot (snd y) -> 0 <= qb_slot (snd x) -> 0 <= qb_slot (snd y) ->
  baddr L x + Q_BATCH_BYTES <= baddr L y \/ baddr L y + Q_BATCH_BYTES <= baddr L x.
Proof.
  intros L x y NE X Y. unfold baddr, abatch_addr, aslot_addr, Q_BATCH_BYTES. rewrite size_of_class_24.
  destruct (Z.lt_ge_cases (qb_slot (snd x)) (qb_slot (snd y))); [left| right]; nia.
Qed.

Section Loop.
  Variables (L : alayout) (RNG : footprint) (LST TMP lf lb tf0 tl0 : Z).
  Variables (ra sp gp tp s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32).

  Definition chain (m : amem) (X : list bq) (nxt : Z) : Prop := abatches_to L m (map fst X) (map snd X) nxt.

  Definition mloop_post (P : list bq) (cur : bq) (R T : list bq) (tb ex : Z) (m : amem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a3 a4 t3 t4 t5 m',
      let '(l, e) := merge_bq cur R in
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 LST) (Z_to_bv 64 TMP) (Z_to_bv 64 (ex + Q_BATCH_BYTES * Z.of_nat (length e))) a3 a4
                   (Z_to_bv 64 Q_BATCH) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x35e08) fc None m' (seg_rom asegs)
      /\ munch ([(LST, LST + 24); (TMP, TMP + 32)] ++ map (fun x => (baddr L x, baddr L x + Q_BATCH_BYTES)) (cur :: R ++ T))%Z m m'
      /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' LST [C8 (Z_to_bv 64 (Z.of_nat (length (P ++ l)))); C8 (Z_to_bv 64 lf); C8 (Z_to_bv 64 (tlast L l 0)); C8 (Z_to_bv 64 lb)]
      /\ chain m' (P ++ l) 0
      /\ rw_cells asegs m' TMP [C8 (Z_to_bv 64 (Z.of_nat (length (T ++ e)))); C8 (Z_to_bv 64 (tfirst L (T ++ e) tf0));
                               C8 (Z_to_bv 64 (tlast L (T ++ e) tl0)); C8 (Z_to_bv 64 (tb + Q_BATCH_BYTES * Z.of_nat (length e)))]
      /\ chain m' (T ++ e) 0.

  #[using="Type"] Lemma qaddrs_map : forall X, qaddrs L (map snd X) = map (baddr L) X.
  Proof. induction X as [|x X IH]; [reflexivity|]. cbn [map qaddrs]. rewrite <- IH. reflexivity. Qed.
  #[using="Type"] Lemma hd_qaddrs : forall X nxt, hd nxt (qaddrs L (map snd X)) = tfirst L X nxt.
  Proof. intros [|x X] nxt; reflexivity. Qed.

  #[using="Type"] Lemma chain_app : forall m X Y nxt, chain m (X ++ Y) nxt <-> chain m X (tfirst L Y nxt) /\ chain m Y nxt.
  Proof.
    intros. unfold chain. rewrite !map_app. rewrite abatches_to_app by (rewrite !length_map; reflexivity).
    rewrite <- (hd_qaddrs Y nxt). tauto.
  Qed.
  #[using="Type"] Lemma chain_cons : forall m x Y nxt, chain m (x :: Y) nxt <-> abatch_cells L m (fst x) (snd x) (tfirst L Y nxt) /\ chain m Y nxt.
  Proof. intros. unfold chain. cbn [map abatches_to]. rewrite <- (hd_qaddrs Y nxt). tauto. Qed.
  #[using="Type"] Lemma chain_nil : forall m nxt, chain m [] nxt.
  Proof. intros. exact I. Qed.

  #[using="Type"] Lemma tfirst_pos : forall X nxt, Forall (bgeom L LST TMP) X -> X <> [] -> AIMG_HI <= tfirst L X nxt.
  Proof. intros [|x X] nxt HF NE; [congruence|]. cbn. inversion HF; subst. destruct H1 as (A & _). exact A. Qed.

  #[using="Type"] Lemma chain_frame : forall W m m' X nxt, chain m X nxt -> munch W m m' -> wmono asegs m m' ->
    Forall (fun x => disjoint_from W (baddr L x) Q_BATCH_BYTES) X -> chain m' X nxt.
  Proof.
    intros W m m' X nxt CH MU WM HF. unfold chain in *. eapply abatches_to_frame; [exact MU| exact WM| exact CH|].
    intros q Hq. apply in_map_iff in Hq. (nd_pre Hq 2%nat; intros x ndR1__; nd_post; destruct ndR1__ as (<- & ndR2__); rename ndR2__ into Hx). exact (proj1 (Forall_forall _ _) HF x Hx).
  Qed.

  (* [comment removed for export] *)
  Definition abatch_rest (m : amem) (b : abatch) (q : qbatchc) : Prop :=
    let B := abatch_addr L (qb_slot q) in
       rw_cells asegs m (B + 8) [C8 (Z_to_bv 64 (b_size b)); C8 (Z_to_bv 64 (b_count b))]
    /\ u64arr asegs m (B + 24) (map (Z_to_bv 64) (qhdrs L (b_chunks b) (qb_ks q)))
    /\ junk_at m (B + 24 + 8 * b_count b) (Q_BATCH_BYTES - 24 - 8 * b_count b)
    /\ b_count b = Z.of_nat (length (b_chunks b)) /\ length (qb_ks q) = length (b_chunks b)
    /\ 0 <= b_count b <= Q_BATCH.
  #[using="Type"] Lemma abatch_cells_split : forall m b q nx,
    abatch_cells L m b q nx <-> rw_cells asegs m (abatch_addr L (qb_slot q)) [C8 (Z_to_bv 64 nx)] /\ abatch_rest m b q.
  Proof.
    intros. unfold abatch_cells, abatch_rest. cbv zeta.
    rewrite (rw_cells_app asegs m (abatch_addr L (qb_slot q)) [C8 (Z_to_bv 64 nx)] [C8 (Z_to_bv 64 (b_size b)); C8 (Z_to_bv 64 (b_count b))]).
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. tauto.
  Qed.

  #[using="Type"] Lemma qhdrs_app : forall (a b : list achunk) (ka kb : list Z), length ka = length a ->
    qhdrs L (a ++ b) (ka ++ kb) = qhdrs L b kb ++ qhdrs L a ka.
  Proof.
    induction a as [|x a IH]; intros b [|k ka] kb LEN; cbn in *; try lia.
    - rewrite app_nil_r. reflexivity.
    - rewrite IH by lia. rewrite app_assoc. reflexivity.
  Qed.

  #[using="Type"] Lemma Forall_perm_slots : forall (f : bq -> Z) (Pr : bq -> Prop) (X Y : list bq),
    (forall x, In x Y -> exists x', In x' X /\ f x' = f x /\ (Pr x' -> Pr x)) -> Forall Pr X -> Forall Pr Y.
  Proof.
    intros f Pr X Y H HF. apply Forall_forall. intros x Hx. (nd_pre (H x Hx) 4%nat; intros x' Hx' _ HP; nd_post). apply HP.
    exact (proj1 (Forall_forall _ _) HF x' Hx').
  Qed.

  #[using="Type"] Lemma nodup_mid : forall (f : bq -> Z) l1 a l2, NoDup (map f (l1 ++ a :: l2)) -> forall x, In x (l1 ++ l2) -> f x <> f a.
  Proof.
    intros f l1 a l2 ND x Hx E. rewrite map_app in ND. cbn [map] in ND.
    (nd_pre (proj1 (list_relations.list.NoDup_app _ _) ND) 3%nat; intros _ NI ND2; nd_post).
    destruct (proj1 (list_relations.list.NoDup_cons _ _) ND2) as [NA _].
    apply in_app_iff in Hx. destruct Hx as [Hx|Hx].
    - refine (NI (f x) _ _). { apply list_elem_of_In. apply in_map. exact Hx. } rewrite E. left.
    - apply NA. rewrite <- E. apply list_elem_of_In. apply in_map. exact Hx.
  Qed.

  #[using="Type"] Lemma tlast_in : forall X d, X <> [] -> exists x, In x X /\ tlast L X d = baddr L x.
  Proof.
    induction X as [|x X IH]; intros d NE; [congruence|]. destruct X as [|y X'].
    - exists x. split; [left; reflexivity| reflexivity].
    - (nd_pre (IH d ltac:(congruence)) 3%nat; intros z Hz E; nd_post). exists z. split; [right; exact Hz|]. rewrite tlast_cons_ne by congruence. exact E.
  Qed.
  #[using="Type"] Lemma tfirst_in : forall X d, X <> [] -> exists x, In x X /\ tfirst L X d = baddr L x.
  Proof. intros [|x X] d NE; [congruence|]. exists x. split; [left; reflexivity| reflexivity]. Qed.

  #[using="Type"] Lemma bq_eq_dec : forall x y : bq, {x = y} + {x <> y}.
  Proof. intros. repeat (decide equality). Qed.

  #[using="Type"] Lemma sub_fp_incl : forall W W', (forall iv, In iv W -> In iv W') -> sub_fp W W'.
  Proof.
    intros W W' H. apply sub_fp_by_incl'. apply Forall_forall. intros iv Hiv. apply Exists_exists. exists iv. split; [apply H; exact Hiv| cbn; lia].
  Qed.

  (* [comment removed for export] *)
  Hypothesis A6 : a6 = Z_to_bv 64 (2^64 - Q_BATCH_BYTES).
  Hypothesis A7 : a7 = Z_to_bv 64 Q_BATCH_BYTES.
  Hypothesis L1 : 0 <= LST. Hypothesis L2 : LST + 32 <= ATOP.
  Hypothesis T1 : 0 <= TMP. Hypothesis T2 : TMP + 32 <= 2^47.
  Hypothesis DTL : TMP + 32 <= LST \/ LST + 32 <= TMP.
  Hypothesis RL : rng RNG LST 32. Hypothesis RT : rng RNG TMP 32.
  Hypothesis TF0 : 0 <= tf0 < 2^64. Hypothesis TL0 : 0 <= tl0 < 2^64. Hypothesis LF : 0 <= lf < 2^64. Hypothesis LB : 0 <= lb < 2^64.

  Lemma mloop_spec : forall (d : nat) (P : list bq) (cur : bq) (R T : list bq) (tb ex : Z) (t1 t2 a3 t3 t4 t5 : word) (m : amem),
    d = length R -> R <> [] ->
    mem_inv asegs m ->
    rw_cells asegs m LST [C8 (Z_to_bv 64 (Z.of_nat (length (P ++ cur :: R)))); C8 (Z_to_bv 64 lf); C8 (Z_to_bv 64 (tlast L (cur :: R) 0)); C8 (Z_to_bv 64 lb)] ->
    chain m (P ++ cur :: R) 0 ->
    rw_cells asegs m TMP [C8 (Z_to_bv 64 (Z.of_nat (length T))); C8 (Z_to_bv 64 (tfirst L T tf0)); C8 (Z_to_bv 64 (tlast L T tl0)); C8 (Z_to_bv 64 tb)] ->
    chain m T 0 ->
    Forall (bgeom L LST TMP) (P ++ cur :: R ++ T) -> Forall (fun x => 0 <= qb_slot (snd x)) (P ++ cur :: R ++ T) ->
    NoDup (map (fun x => qb_slot (snd x)) (P ++ cur :: R ++ T)) ->
    Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) (cur :: R) -> batches_bytes (map fst (cur :: R)) < 2^62 ->
    Forall (fun x => rng RNG (baddr L x) Q_BATCH_BYTES) (cur :: R ++ T) ->
    0 <= tb -> tb + Q_BATCH_BYTES * (Z.of_nat (length R) + 1) < 2^62 -> 0 <= ex -> ex + Q_BATCH_BYTES * (Z.of_nat (length R) + 1) < 2^62 ->
    Z.of_nat (length (P ++ cur :: R ++ T)) < 2^40 ->
    evtF asegs RNG (mloop_post P cur R T tb ex m)
      (MS (mkR ra sp gp tp (Z_to_bv 64 (baddr L (hd cur R))) t1 t2 s0 s1 (Z_to_bv 64 LST) (Z_to_bv 64 TMP) (Z_to_bv 64 ex) a3 (Z_to_bv 64 (baddr L cur))
               (Z_to_bv 64 Q_BATCH) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 amerge_loop) fc None m (seg_rom asegs)).
  Proof using A6 A7 L1 L2 T1 T2 DTL RL RT TF0 TL0 LF LB.   (* [comment removed for export] *)
    induction d as [|d IH]; intros until m; intros HD RNE MI LS CH TM CT GEO SL ND SZ SZS RB TB0 TB1 EX0 EX1 LEN40.
    { exfalso. destruct R; [congruence| cbn in HD; lia]. }
    destruct R as [|nx R']; [congruence|]. cbn [hd].
    pose proof CH as CH0.
    destruct (proj1 (chain_app _ _ _ _) CH) as [CHP CHR]. clear CH.
    destruct (proj1 (chain_cons _ _ _ _) CHR) as [BC CHR1]. clear CHR. destruct (proj1 (chain_cons _ _ _ _) CHR1) as [BN CHR']. clear CHR1.
    (nd_pre BC 6%nat; intros CC EC JC CCNT CLEN CRNG; nd_post). (nd_pre BN 6%nat; intros CN EN JN NCNT NLEN NRNG; nd_post).
    assert (GC : bgeom L LST TMP cur) by (eapply (proj1 (Forall_forall _ _) GEO); apply in_app_iff; right; left; reflexivity).
    assert (GN : bgeom L LST TMP nx) by (eapply (proj1 (Forall_forall _ _) GEO); apply in_app_iff; right; right; left; reflexivity).
    assert (RC : rng RNG (baddr L cur) Q_BATCH_BYTES) by (pose proof (Forall_inv RB) as X; exact X).
    assert (RN : rng RNG (baddr L nx) Q_BATCH_BYTES) by (pose proof (Forall_inv (Forall_inv_tail RB)) as X; exact X).
    assert (DCN : baddr L cur + Q_BATCH_BYTES <= baddr L nx \/ baddr L nx + Q_BATCH_BYTES <= baddr L cur).
    { apply (baddr_disj L cur nx).
      - intros E. rewrite map_app in ND. cbn [map] in ND. (nd_pre (proj1 (list_relations.list.NoDup_app _ _) ND) 3%nat; intros _ _ ND2; nd_post).
        destruct (proj1 (list_relations.list.NoDup_cons _ _) ND2) as [NI _]. apply NI. rewrite E. left.
      - eapply (proj1 (Forall_forall _ _) SL). apply in_app_iff; right; left; reflexivity.
      - eapply (proj1 (Forall_forall _ _) SL). apply in_app_iff; right; right; left; reflexivity. }
    pose proof (Forall_inv SZ) as SZC. pose proof (Forall_inv (Forall_inv_tail SZ)) as SZN. cbn beta in SZC, SZN.
    cbn [map] in SZS. rewrite !batches_bytes_cons in SZS.
    pose proof (batches_bytes_lb (map fst R') ltac:(rewrite Forall_map; exact (Forall_inv_tail (Forall_inv_tail SZ)))) as SZR.
    unfold bgeom, amerge_loop, AIMG_HI, Q_BATCH_BYTES, Q_BATCH in GC, GN, RC, RN, DCN, CC, EC, JC, CN, EN, JN, CRNG, NRNG, SZC, SZN, L2 |- *.
    unfold baddr in GC, GN, RC, RN, DCN, CC, CN |- *. cbn [fst snd tfirst baddr] in GC, GN, RC, RN, DCN, CC, EC, JC, CN, EN, JN, CCNT, CLEN, CRNG, NCNT, NLEN, NRNG, SZC, SZN |- *.
    set (CUR := abatch_addr L (qb_slot (snd cur))) in *. set (NXT := abatch_addr L (qb_slot (snd nx))) in *.
    (nd_pre GC 4%nat; intros GC1 GC2 GC3 GC4; nd_post). (nd_pre GN 4%nat; intros GN1 GN2 GN3 GN4; nd_post).
    unfold baddr in CC. cbn [fst snd] in CC. fold NXT in CC.
    (* [comment removed for export] *)
    step. step. zstep.                                    (* [comment removed for export] *)
    step. if_cases KF; zify_cond KF.                      (* [comment removed for export] *)
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in KF by lia.
      zstep.                                              (* [comment removed for export] *)
      step.                                               (* [comment removed for export] *)
      step. if_cases KE; zify_cond KE.                    (* [comment removed for export] *)
      + (* [comment removed for export] *)
        assert (GR : Forall (bgeom L LST TMP) R').
        { apply Forall_app in GEO. destruct GEO as [_ G2]. do 2 apply Forall_inv_tail in G2. apply Forall_app in G2. destruct G2 as [G2 _]. exact G2. }
        assert (RNIL : R' = []).
        { destruct R' as [|r R'']; [reflexivity| exfalso].
          pose proof (tfirst_pos (r :: R'') 0 GR ltac:(congruence)) as X. unfold AIMG_HI in X. cbn [tfirst] in X, KE.
          pose proof (Forall_inv GR) as Y. unfold bgeom, Q_BATCH_BYTES in Y. cbv beta in Y. (nd_pre Y 3%nat; intros Y1 Y Y3; nd_post).
          rewrite Z.mod_small in KE by (clear -X Y; lia). clear -X KE. lia. }
        subst R'. clear GR KE.
        assert (MB : merge_bq cur [nx] = ([cur; nx], [])).
        { cbn [merge_bq]. unfold Q_BATCH. destruct (Z.leb_spec0 (b_count (fst cur) + b_count (fst nx)) 1021); [exfalso; clear -KF l; lia| reflexivity]. }
        apply evtF_done. unfold mloop_post. rewrite MB. cbv beta iota zeta. cbn [length Z.of_nat app Pos.of_succ_nat].
        rewrite !app_nil_r, Z.mul_0_r, !Z.add_0_r.
        do 8 eexists. exists m. split; [reflexivity|].
        split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|].
        split. { replace (length (P ++ [cur; nx])) with (length (P ++ cur :: nx :: [])) by reflexivity. exact LS. }
        split; [exact CH0|]. split; [exact TM| exact CT].
      + (* [comment removed for export] *)
        assert (RNE' : R' <> []) by (intros ->; cbn in KE; rewrite ?unsigned_lit in KE by lia; lia).
        assert (TFE : tfirst L R' 0 = baddr L (hd nx R')) by (destruct R'; [congruence| reflexivity]).
        rewrite TFE.
        eapply evtF_mono.
        { eapply (IH (P ++ [cur]) nx R' T tb ex); try eassumption.
          - cbn in HD. lia.
          - rewrite <- app_assoc. cbn [app]. rewrite tlast_cons_ne in LS by congruence. exact LS.
          - rewrite <- app_assoc. cbn [app]. exact CH0.
          - rewrite <- app_assoc. cbn [app]. exact GEO.
          - rewrite <- app_assoc. cbn [app]. exact SL.
          - rewrite <- app_assoc. cbn [app]. exact ND.
          - exact (Forall_inv_tail SZ).
          - cbn [map]. rewrite batches_bytes_cons. clear -SZS SZC. lia.
          - exact (Forall_inv_tail RB).
          - revert TB1. clear. cbn [length]. unfold Q_BATCH_BYTES. intros. lia.
          - revert EX1. clear. cbn [length]. unfold Q_BATCH_BYTES. intros. lia.
          - rewrite <- app_assoc. cbn [app]. exact LEN40. }
        cbv beta. unfold mloop_post. intros ms' (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & m' & POST).
        assert (MB : merge_bq cur (nx :: R') = (cur :: fst (merge_bq nx R'), snd (merge_bq nx R'))).
        { cbn [merge_bq]. unfold Q_BATCH. destruct (Z.leb_spec0 (b_count (fst cur) + b_count (fst nx)) 1021); [exfalso; clear -KF l; lia|].
          destruct (merge_bq nx R'); reflexivity. }
        rewrite MB. destruct (merge_bq nx R') as [l' e'] eqn:MB'. cbn [fst snd].
        (destruct POST as (-> & ndR1__); nd_pre ndR1__ 7%nat; intros MU' WM' MI' LS' CH' TM' CT'; nd_post).
        do 8 eexists. exists m'. split; [reflexivity|].
        split. { eapply munch_weaken; [| exact MU']. intros x Hx. revert Hx. cbn [map app]. unfold outside. cbn. clear. tauto. }   (* [comment removed for export] *)
        split; [exact WM'|]. split; [exact MI'|].
        split. { rewrite <- app_assoc in LS'. cbn [app] in LS'. rewrite tlast_cons_ne by (pose proof (merge_bq_ne R' nx) as NE; rewrite MB' in NE; exact NE). exact LS'. }
        split. { rewrite <- app_assoc in CH'. exact CH'. }
        split; [exact TM'| exact CT'].
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in KF by lia.
      assert (GR : Forall (bgeom L LST TMP) R').
      { pose proof GEO as G. apply Forall_app in G. destruct G as [_ G2]. do 2 apply Forall_inv_tail in G2. apply Forall_app in G2. destruct G2 as [G2 _]. exact G2. }
      assert (NXN : 0 <= tfirst L R' 0 < 2^64).
      { destruct R' as [|r R'']; [cbn; lia|]. pose proof (Forall_inv GR) as Y. unfold bgeom, AIMG_HI, Q_BATCH_BYTES in Y. cbn [tfirst]. clear -Y. lia. }
      assert (LEC : length (map (Z_to_bv 64) (qhdrs L (b_chunks (fst cur)) (qb_ks (snd cur)))) = Z.to_nat (b_count (fst cur)))
        by (rewrite length_map, qhdrs_length by exact CLEN; lia).
      assert (LEN : length (map (Z_to_bv 64) (qhdrs L (b_chunks (fst nx)) (qb_ks (snd nx)))) = Z.to_nat (b_count (fst nx)))
        by (rewrite length_map, qhdrs_length by exact NLEN; lia).
      eapply evtF_cut.
      { eapply (mcore_spec RNG) with (LST := LST) (CUR := CUR) (NXT := NXT); try reflexivity.
        all: try eassumption.
        all: clear -SZC SZN SZS SZR CRNG NRNG KF NXN LEN40 GC1 GC2 GC3 GC4 GN1 GN2 GN3 GN4 DCN L1 L2; unfold Q_BATCH, Q_BATCH_BYTES in *.
        all: try lia.
        revert LEN40; clear; rewrite !length_app; cbn [length]; rewrite ?length_app; cbn [length]; intros; lia. }
      cbv beta. intros ms1 (y2 & y3 & y4 & y5 & m1 & -> & MUc & WMc & MI1 & CC1 & EC1 & JC1 & CN1 & JN1). clear MI.
      unfold Q_BATCH_BYTES in CC1, JC1, CN1, JN1.
      (* [comment removed for export] *)
      assert (OTH : forall x, In x (P ++ R' ++ T) ->
                (baddr L x + 8192 <= CUR \/ CUR + 8192 <= baddr L x) /\ (baddr L x + 8192 <= NXT \/ NXT + 8192 <= baddr L x)
                /\ bgeom L LST TMP x /\ 0 <= qb_slot (snd x)).
      { intros x Hx.
        assert (INA : In x (P ++ cur :: (nx :: R') ++ T)).
        { apply in_app_iff in Hx. apply in_app_iff. destruct Hx as [Hx|Hx]; [left; exact Hx| right; right]. cbn [app]. right. exact Hx. }
        pose proof (proj1 (Forall_forall _ _) SL x INA) as SX. pose proof (proj1 (Forall_forall _ _) GEO x INA) as GX. cbv beta in SX.
        assert (SC : 0 <= qb_slot (snd cur)) by (eapply (proj1 (Forall_forall _ _) SL); apply in_app_iff; right; left; reflexivity).
        assert (SN : 0 <= qb_slot (snd nx)) by (eapply (proj1 (Forall_forall _ _) SL); apply in_app_iff; right; right; left; reflexivity).
        assert (N1 : qb_slot (snd x) <> qb_slot (snd cur)).
        { apply (nodup_mid (fun x => qb_slot (snd x)) P cur ((nx :: R') ++ T) ND x).
          apply in_app_iff in Hx. apply in_app_iff. destruct Hx as [Hx|Hx]; [left; exact Hx| right; cbn [app]; right; exact Hx]. }
        assert (N2 : qb_slot (snd x) <> qb_slot (snd nx)).
        { apply (nodup_mid (fun x => qb_slot (snd x)) (P ++ [cur]) nx (R' ++ T)); [rewrite <- app_assoc; exact ND|].
          apply in_app_iff in Hx. apply in_app_iff. destruct Hx as [Hx|Hx]; [left; apply in_app_iff; left; exact Hx| right; exact Hx]. }
        pose proof (baddr_disj L x cur N1 SX SC) as D1. pose proof (baddr_disj L x nx N2 SX SN) as D2.
        unfold baddr, Q_BATCH_BYTES in D1, D2 |- *. cbn [snd] in D1, D2. fold CUR in D1. fold NXT in D2. clear -D1 D2 GX SX; tauto. }   (* [comment removed for export] *)
      (* [comment removed for export] *)
      assert (DJc : forall x, In x (P ++ R' ++ T) ->
        disjoint_from [(CUR + 8, CUR + 24); (CUR + 24 + 8 * b_count (fst cur), CUR + 24 + 8 * (b_count (fst cur) + b_count (fst nx))); (NXT + 8, NXT + 24)]%Z (baddr L x) 8192).
      { intros x Hx. (nd_pre (OTH x Hx) 3%nat; intros D1 D2 _; nd_post). cbn. clear -D1 D2 CRNG NRNG KF. lia. }
      xport LS MUc WMc ltac:(clear -GC3 GN3 CRNG NRNG KF; lia).
      xport TM MUc WMc ltac:(clear -GC4 GN4 CRNG NRNG KF; lia).
      assert (CHP1 : chain m1 P CUR).
      { eapply chain_frame; [exact CHP| exact MUc| exact WMc|]. apply Forall_forall. intros x Hx. apply DJc. apply in_app_iff. left. exact Hx. }
      assert (CHR1 : chain m1 R' 0).
      { eapply chain_frame; [exact CHR'| exact MUc| exact WMc|]. apply Forall_forall. intros x Hx. apply DJc. apply in_app_iff. right. apply in_app_iff. left. exact Hx. }
      assert (CT1 : chain m1 T 0).
      { eapply chain_frame; [exact CT| exact MUc| exact WMc|]. apply Forall_forall. intros x Hx. apply DJc. apply in_app_iff. right. apply in_app_iff. right. exact Hx. }
      clear CHP CHR' CT DJc.
      (* [comment removed for export] *)
      assert (GB : forall x, In x (P ++ cur :: (nx :: R') ++ T) -> 6307840 <= baddr L x /\ baddr L x + 8192 <= ATOP
                                                            /\ (LST + 32 <= baddr L x \/ baddr L x + 8192 <= LST) /\ (TMP + 32 <= baddr L x \/ baddr L x + 8192 <= TMP)).
      { intros x Hx. pose proof (proj1 (Forall_forall _ _) GEO x Hx) as G. unfold bgeom, AIMG_HI, Q_BATCH_BYTES in G. exact G. }
      assert (LLR : 0 <= tlast L (cur :: nx :: R') 0 < 2^64).
      { (nd_pre (tlast_in (cur :: nx :: R') 0 ltac:(congruence)) 3%nat; intros z Hz ndR1__; nd_post; revert ndR1__; intros ->).
        assert (INz : In z (P ++ cur :: (nx :: R') ++ T)).
        { apply in_app_iff. right. destruct Hz as [<-|[<-|Hz]]; [left; reflexivity| right; left; reflexivity| right; right; apply in_app_iff; left; exact Hz]. }
        (nd_pre (GB z INz) 3%nat; intros B1 B2 _; nd_post). clear -B1 B2. lia. }
      assert (TFR : 0 <= tfirst L T tf0 < 2^64 /\ 0 <= tlast L T tl0 < 2^64).
      { destruct T as [|t T']; [cbn; clear -TF0 TL0; lia|].
        (nd_pre (tfirst_in (t :: T') tf0 ltac:(congruence)) 3%nat; intros z1 Hz1 ndR1__; nd_post; revert ndR1__; intros ->). (nd_pre (tlast_in (t :: T') tl0 ltac:(congruence)) 3%nat; intros z2 Hz2 ndR1__; nd_post; revert ndR1__; intros ->).
        (nd_pre (GB z1 ltac:(apply in_app_iff; right; right; apply in_app_iff; right; exact Hz1)) 3%nat; intros B1 B2 _; nd_post).
        (nd_pre (GB z2 ltac:(apply in_app_iff; right; right; apply in_app_iff; right; exact Hz2)) 3%nat; intros B3 B4 _; nd_post). clear -B1 B2 B3 B4. lia. }
      assert (LSP : 0 < Z.of_nat (length (P ++ cur :: nx :: R')) < 2^63).
      { revert LEN40. clear. rewrite !length_app. cbn [length]. rewrite ?length_app. cbn [length]. intros. lia. }
      (* [comment removed for export] *)
      destruct (list_eq_dec bq_eq_dec T []) as [TNIL|TNE].
      + (* [comment removed for export] *) subst T.
        eapply evtF_cut.
        { eapply (munlink_spec false RNG) with (CUR := CUR) (NXT := NXT) (LST := LST) (TMP := TMP) (TL := 0) (tlx := 0)
            (nxn := tfirst L R' 0) (szc := b_size (fst cur) + b_size (fst nx) - 8192) (cc := b_count (fst cur) + b_count (fst nx))
            (szn := 8192) (cn := 0) (ls := Z.of_nat (length (P ++ cur :: nx :: R'))) (lf := lf) (ll := tlast L (cur :: nx :: R') 0) (lb := lb)
            (tn := 0) (tf := tf0) (tl := tl0) (tb := tb) (ex := ex);
            try reflexivity; try eassumption; try exact I.
          all: unfold Q_BATCH_BYTES; revert TB0 TB1 EX0 EX1; clear; cbn [length]; unfold Q_BATCH_BYTES; intros; lia. }
        cbv beta. intros ms2 (z1 & z2 & z3 & m2 & -> & MUu & WMu & MI2 & CC2 & CN2 & LS2 & TM2 & _). cbn [app] in MUu. clear MI1.
        step.                                             (* [comment removed for export] *)
        step. if_cases KX; zify_cond KX.                  (* [comment removed for export] *)
        * (* [comment removed for export] *)
          assert (RNE' : R' <> []) by (intros ->; cbn in KX; rewrite ?unsigned_lit in KX by lia; lia).
          assert (TFE : tfirst L R' 0 = baddr L (hd nx R')) by (destruct R'; [congruence| reflexivity]).
          assert (MB : merge_bq cur (nx :: R') = (fst (merge_bq (bq_merge cur nx) R'), bq_empty nx :: snd (merge_bq (bq_merge cur nx) R'))).
          { cbn [merge_bq]. unfold Q_BATCH. destruct (Z.leb_spec0 (b_count (fst cur) + b_count (fst nx)) 1021); [| exfalso; clear -KF n; lia].
            destruct (merge_bq (bq_merge cur nx) R'); reflexivity. }
          (* [comment removed for export] *)
          xport EC1 MUu WMu ltac:(rewrite length_app, ?LEC, ?LEN; clear -CRNG NRNG KF DCN GC3 GC4; lia).
          destruct JC1 as [jc JC1]. xport JC1 MUu WMu ltac:(clear -CRNG NRNG KF DCN GC3 GC4; lia).
          destruct JN1 as [jn JN1]. xport JN1 MUu WMu ltac:(clear -CRNG NRNG KF DCN GN3 GN4; lia).
          assert (CHP2 : chain m2 P CUR).
          { eapply chain_frame; [exact CHP1| exact MUu| exact WMu|]. apply Forall_forall. intros x Hx.
            (nd_pre (OTH x ltac:(apply in_app_iff; left; exact Hx)) 4%nat; intros D1 D2 (G1 & G2 & G3 & G4) _; nd_post). unfold Q_BATCH_BYTES in *. cbn. clear -D1 D2 G3 G4. lia. }
          assert (CHR2 : chain m2 R' 0).
          { eapply chain_frame; [exact CHR1| exact MUu| exact WMu|]. apply Forall_forall. intros x Hx.
            (nd_pre (OTH x ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hx)) 4%nat; intros D1 D2 (G1 & G2 & G3 & G4) _; nd_post). unfold Q_BATCH_BYTES in *. cbn. clear -D1 D2 G3 G4. lia. }
          (* [comment removed for export] *)
          assert (LLN : (tlast L (cur :: nx :: R') 0 =? NXT) = false).
          { apply Z.eqb_neq. rewrite 2!tlast_cons_ne by congruence. (nd_pre (tlast_in R' 0 RNE') 3%nat; intros z Hz ndR1__; nd_post; revert ndR1__; intros ->).
            (nd_pre (OTH z ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hz)) 3%nat; intros _ D2 _; nd_post). clear -D2. lia. }
          rewrite LLN in LS2. rewrite TFE.
          replace (baddr L (hd nx R')) with (baddr L (hd (bq_merge cur nx) R')) by (destruct R'; [congruence| reflexivity]).
          setreg 14 (Z_to_bv 64 (baddr L (bq_merge cur nx))) ltac:(unfold baddr; cbn [bq_merge snd qb_slot]; reflexivity).
          unfold Q_BATCH_BYTES.
          eapply evtF_mono.
          { eapply (IH P (bq_merge cur nx) R' [bq_empty nx] (tb + 8192) (ex + 8192)).
            - cbn in HD. clear -HD. lia.
            - exact RNE'.
            - exact MI2.
            - (* [comment removed for export] *) rewrite length_app in LS2 |- *. cbn [length] in LS2 |- *.
              replace (Z.of_nat (length P + S (S (length R'))) - 1) with (Z.of_nat (length P + S (length R'))) in LS2 by lia.
              rewrite tlast_cons_ne by exact RNE'. rewrite 2!tlast_cons_ne in LS2 by congruence. exact LS2.
            - (* [comment removed for export] *) apply (proj2 (chain_app _ _ _ _)). cbn [tfirst]. unfold baddr. cbn [bq_merge snd qb_slot]. fold CUR. split; [exact CHP2|].
              apply (proj2 (chain_cons _ _ _ _)). split; [| exact CHR2].
              unfold abatch_cells. cbn [fst snd bq_merge b_size b_count b_chunks qb_slot qb_ks]. fold CUR. unfold Q_BATCH_BYTES, Q_BATCH.
              replace (b_size (fst cur) + (b_size (fst nx) - 8192)) with (b_size (fst cur) + b_size (fst nx) - 8192) by lia.
              split; [exact CC2|]. split; [rewrite qhdrs_app, map_app by exact NLEN; exact EC1|].
              split; [exists jc; exact JC1|]. rewrite !length_app. clear -CCNT NCNT CLEN NLEN CRNG NRNG KF. lia.
            - (* [comment removed for export] *) cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat tfirst tlast map List.last]. unfold baddr. cbn [bq_empty snd qb_slot]. fold NXT.
              unfold Q_BATCH_BYTES. replace (0 + 1) with 1 in TM2 by lia. exact TM2.
            - (* [comment removed for export] *) apply (proj2 (chain_cons _ _ _ _)). split; [| apply chain_nil].
              unfold abatch_cells. cbn [fst snd tfirst bq_empty b_size b_count b_chunks qb_slot qb_ks qhdrs map length Z.of_nat]. fold NXT. unfold Q_BATCH_BYTES, Q_BATCH.
              split; [exact CN2|]. split; [apply u64arr_nil; clear -GN1 GN2; lia|].
              split; [exists jn; rewrite Z.mul_0_r, Z.add_0_r, Z.sub_0_r; exact JN1|]. clear. lia.
            - (* [comment removed for export] *) apply Forall_forall. intros x Hx. apply in_app_iff in Hx. cbn [app In] in Hx.
              destruct Hx as [Hx|[E|Hx]]; [| subst x| apply in_app_iff in Hx; destruct Hx as [Hx|[E|F0]]; [| subst x| destruct F0]].
              + eapply (proj1 (Forall_forall _ _) GEO). apply in_app_iff. left. exact Hx.
              + unfold bgeom, baddr, AIMG_HI, Q_BATCH_BYTES. cbn [bq_merge snd qb_slot]. fold CUR. clear -GC1 GC2 GC3 GC4. tauto.
              + eapply (proj1 (Forall_forall _ _) GEO). apply in_app_iff. right. right. apply in_app_iff. left. right. exact Hx.
              + unfold bgeom, baddr, AIMG_HI, Q_BATCH_BYTES. cbn [bq_empty snd qb_slot]. fold NXT. clear -GN1 GN2 GN3 GN4. tauto.
            - (* [comment removed for export] *) apply Forall_forall. intros x Hx. apply in_app_iff in Hx. cbn [app In] in Hx.
              destruct Hx as [Hx|[E|Hx]]; [| subst x| apply in_app_iff in Hx; destruct Hx as [Hx|[E|F0]]; [| subst x| destruct F0]].
              + eapply (proj1 (Forall_forall _ _) SL). apply in_app_iff. left. exact Hx.
              + cbn [bq_merge snd qb_slot]. eapply (proj1 (Forall_forall _ _) SL). apply in_app_iff. right. left. reflexivity.
              + eapply (proj1 (Forall_forall _ _) SL). apply in_app_iff. right. right. apply in_app_iff. left. right. exact Hx.
              + cbn [bq_empty snd qb_slot]. eapply (proj1 (Forall_forall _ _) SL). apply in_app_iff. right. right. left. reflexivity.
            - (* [comment removed for export] *) rewrite app_nil_r in ND. revert ND. rewrite !map_app. cbn [map]. rewrite !map_app. cbn [map bq_merge bq_empty snd qb_slot app].
              intros ND. refine (proj1 (list_relations.list.NoDup_Permutation_proper _ _ _) ND).
              apply Permutation_app_head. apply perm_skip. apply Permutation_cons_append.
            - (* [comment removed for export] *) constructor; [| exact (Forall_inv_tail (Forall_inv_tail SZ))]. cbn [fst bq_merge b_size]. unfold Q_BATCH_BYTES in *. clear -SZC SZN. lia.
            - cbn [map fst bq_merge b_size]. rewrite batches_bytes_cons. cbn [b_size]. clear -SZS SZC SZN. unfold Q_BATCH_BYTES in *. lia.
            - (* [comment removed for export] *) rewrite app_nil_r in RB. constructor; [unfold baddr; cbn [bq_merge snd qb_slot]; fold CUR; exact RC|]. apply Forall_app. split; [exact (Forall_inv_tail (Forall_inv_tail RB))|].
              constructor; [unfold baddr; cbn [bq_empty snd qb_slot]; fold NXT; exact RN| constructor].
            - clear -TB0; lia.
            - revert TB1; clear; cbn [length]; unfold Q_BATCH_BYTES; intros; lia.
            - clear -EX0; lia.
            - revert EX1; clear; cbn [length]; unfold Q_BATCH_BYTES; intros; lia.
            - revert LEN40; clear; rewrite !length_app; cbn [length]; rewrite ?length_app; cbn [length]; intros; lia. }
          cbv beta. unfold mloop_post. rewrite MB. destruct (merge_bq (bq_merge cur nx) R') as [l' e']. cbn [fst snd].
          intros ms' (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & m' & -> & MU' & WM' & MI' & LS' & CH' & TM' & CT').
          cbn [length app] in TM' |- *. unfold Q_BATCH_BYTES in TM' |- *.
          replace (ex + 8192 * Z.of_nat (S (length e'))) with (ex + 8192 + 8192 * Z.of_nat (length e')) by lia.
          replace (tb + 8192 * Z.of_nat (S (length e'))) with (tb + 8192 + 8192 * Z.of_nat (length e')) by lia.
          do 8 eexists. exists m'. split; [reflexivity|].
          split. { (* [comment removed for export] *)
            unfold baddr. cbn [map app snd bq_merge bq_empty qb_slot] in MU' |- *. fold CUR in MU' |- *. fold NXT in MU' |- *.
            lazymatch goal with |- munch ?W _ _ =>
              assert (MU12 : munch W m m2) by (eapply (munch_trans_w _ _ _ _ _ _ MUc MUu); solve_sub_fpw ltac:(clear -CRNG NRNG KF; lia));
              eapply (munch_trans_w _ _ _ _ _ _ MU12 MU'); apply sub_fp_incl; [intros iv Hiv; exact Hiv|] end.
            intros iv Hiv. cbn [In app] in Hiv |- *. rewrite app_nil_r. rewrite map_app in Hiv. cbn [map] in Hiv.
            destruct Hiv as [H|[H|[H|H]]]; [clear -H; tauto| clear -H; tauto| clear -H; tauto|]. apply in_app_iff in H. destruct H as [H|[H|[]]]; [right; right; right; right; exact H| clear -H; tauto]. }   (* [comment removed for export] *)
          split; [eapply wmono_trans; [exact WMc| eapply wmono_trans; [exact WMu| exact WM']]|]. split; [exact MI'|].
          split; [exact LS'|]. split; [exact CH'|]. split; [exact TM'| exact CT'].
        * (* [comment removed for export] *)
          assert (RNIL : R' = []).
          { destruct R' as [|r R'']; [reflexivity| exfalso].
            pose proof (tfirst_pos (r :: R'') 0 GR ltac:(congruence)) as X. unfold AIMG_HI in X. cbn [tfirst] in X, KX.
            pose proof (Forall_inv GR) as Y. unfold bgeom, Q_BATCH_BYTES in Y. cbv beta in Y. (nd_pre Y 3%nat; intros Y1 Y Y3; nd_post).
            rewrite ?unsigned_lit in KX by (clear -X Y; lia). clear -X KX. lia. }
          subst R'. clear GR KX.
          assert (MB : merge_bq cur [nx] = ([bq_merge cur nx], [bq_empty nx])).
          { cbn [merge_bq]. unfold Q_BATCH. destruct (Z.leb_spec0 (b_count (fst cur) + b_count (fst nx)) 1021); [reflexivity| exfalso; clear -KF n; lia]. }
          (* [comment removed for export] *)
          xport EC1 MUu WMu ltac:(rewrite length_app, ?LEC, ?LEN; clear -CRNG NRNG KF DCN GC3 GC4; lia).
          destruct JC1 as [jc JC1]. xport JC1 MUu WMu ltac:(clear -CRNG NRNG KF DCN GC3 GC4; lia).
          destruct JN1 as [jn JN1]. xport JN1 MUu WMu ltac:(clear -CRNG NRNG KF DCN GN3 GN4; lia).
          assert (CHP2 : chain m2 P CUR).
          { eapply chain_frame; [exact CHP1| exact MUu| exact WMu|]. apply Forall_forall. intros x Hx.
            (nd_pre (OTH x ltac:(apply in_app_iff; left; exact Hx)) 4%nat; intros D1 D2 (G1 & G2 & G3 & G4) _; nd_post). unfold Q_BATCH_BYTES in *. cbn. clear -D1 D2 G3 G4. lia. }
          apply evtF_done. unfold mloop_post. rewrite MB. cbv beta iota zeta. cbn [length Z.of_nat app Pos.of_succ_nat Pos.to_nat].
          rewrite !Z.mul_1_r.
          do 8 eexists. exists m2. split; [reflexivity|].
          split. { cbn [map app]. unfold baddr, Q_BATCH_BYTES. cbn [snd]. fold CUR. fold NXT. eapply (munch_trans_w _ _ _ _ _ _ MUc MUu); solve_sub_fpw ltac:(clear -CRNG NRNG KF; lia). }
          split; [eapply wmono_trans; [exact WMc| exact WMu]|]. split; [exact MI2|].
          split. { rewrite length_app in LS2 |- *. cbn [length] in LS2 |- *.
                   replace (Z.of_nat (length P + 2) - 1) with (Z.of_nat (length P + 1)) in LS2 by lia.
                   cbn [tlast map List.last] in LS2. rewrite Z.eqb_refl in LS2. exact LS2. }
          split. { apply (proj2 (chain_app _ _ _ _)). split; [exact CHP2|]. apply (proj2 (chain_cons _ _ _ _)). split; [| apply chain_nil].
                   unfold abatch_cells. cbn [fst snd tfirst bq_merge b_size b_count b_chunks qb_slot qb_ks]. fold CUR. unfold Q_BATCH_BYTES, Q_BATCH.
                   cbn [tfirst] in CC2. replace (b_size (fst cur) + (b_size (fst nx) - 8192)) with (b_size (fst cur) + b_size (fst nx) - 8192) by lia.
                   split; [exact CC2|]. split.
                   - rewrite qhdrs_app, map_app by exact NLEN. exact EC1.
                   - split; [exists jc; exact JC1|]. rewrite !length_app. clear -CCNT NCNT CLEN NLEN CRNG NRNG KF. lia. }
          split. { unfold Q_BATCH_BYTES. replace (0 + 1) with 1 in TM2 by lia. exact TM2. }
          apply (proj2 (chain_cons _ _ _ _)). split; [| apply chain_nil].
          unfold abatch_cells. cbn [fst snd tfirst bq_empty b_size b_count b_chunks qb_slot qb_ks qhdrs map length Z.of_nat]. fold NXT. unfold Q_BATCH_BYTES, Q_BATCH.
          split; [exact CN2|]. split; [apply u64arr_nil; clear -GN1 GN2; lia|].
          split; [exists jn; rewrite Z.mul_0_r, Z.add_0_r, Z.sub_0_r; exact JN1|]. clear. lia.
      + (* [comment removed for export] *)
        (nd_pre (exists_last TNE) 3%nat; intros T0 tl ET; nd_post). rewrite ET in *. clear ET TNE.
        destruct (proj1 (chain_app _ _ _ _) CT1) as [CT0 CTL]. cbn [tfirst] in CT0.
        destruct (proj1 (chain_cons _ _ _ _) CTL) as [BTL _]. clear CTL. cbn [fst snd tfirst] in BTL.
        destruct (proj1 (abatch_cells_split _ _ _ _) BTL) as [TLN TLR]. clear BTL.
        unfold baddr in CT0. set (TL := abatch_addr L (qb_slot (snd tl))) in *.
        assert (INtl : In tl (P ++ R' ++ T0 ++ [tl])) by (apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity).
        (nd_pre (OTH tl INtl) 4%nat; intros DTLC DTLN (GT1 & GT2 & GT3 & GT4) STL; nd_post). unfold baddr, Q_BATCH_BYTES in DTLC, DTLN, GT1, GT2, GT3, GT4. fold TL in DTLC, DTLN, GT1, GT2, GT3, GT4.
        assert (RTL : rng RNG TL 8192).
        { pose proof (proj1 (Forall_forall _ _) RB tl ltac:(right; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity)) as X. unfold baddr in X. exact X. }
        assert (TLl : tlast L (T0 ++ [tl]) tl0 = TL) by (rewrite tlast_app1; reflexivity).
        eapply evtF_cut.
        { eapply (munlink_spec true RNG) with (CUR := CUR) (NXT := NXT) (LST := LST) (TMP := TMP) (TL := TL) (tlx := 0)
            (nxn := tfirst L R' 0) (szc := b_size (fst cur) + b_size (fst nx) - 8192) (cc := b_count (fst cur) + b_count (fst nx))
            (szn := 8192) (cn := 0) (ls := Z.of_nat (length (P ++ cur :: nx :: R'))) (lf := lf) (ll := tlast L (cur :: nx :: R') 0) (lb := lb)
            (tn := Z.of_nat (length (T0 ++ [tl]))) (tf := tfirst L (T0 ++ [tl]) tf0) (tl := tlast L (T0 ++ [tl]) tl0) (tb := tb) (ex := ex);
            try reflexivity; try eassumption; try exact I.
          all: try (revert TB0 TB1 EX0 EX1; clear; cbn [length]; unfold Q_BATCH_BYTES; intros; lia).
          all: try (clear -TFR; tauto).
          - revert LEN40. clear. rewrite !length_app. cbn [length]. rewrite ?length_app. cbn [length]. intros. lia.
          - (* [comment removed for export] *) unfold AIMG_HI, Q_BATCH_BYTES. split; [rewrite length_app; cbn [length]; clear; lia|]. split; [exact TLN|].
            split; [exact GT1|]. split; [exact GT2|]. split; [exact DTLC|]. split; [exact DTLN|]. split; [exact GT3|]. split; [exact GT4|].
            eapply rng_sub'; [exact RTL| clear; lia]. }
        cbv beta. intros ms2 (z1 & z2 & z3 & m2 & -> & MUu & WMu & MI2 & CC2 & CN2 & LS2 & TM2 & TL2). cbn [app] in MUu. clear MI1.
        (* [comment removed for export] *)
        assert (NTL : forall x, In x (P ++ R' ++ T0) -> qb_slot (snd x) <> qb_slot (snd tl)).
        { intros x Hx. apply (nodup_mid (fun x => qb_slot (snd x)) (P ++ cur :: nx :: R' ++ T0) tl []).
          - revert ND. clear. intros ND.
            match goal with |- NoDup ?l => match type of ND with NoDup ?l' => replace l with l'; [exact ND|] end end.
            rewrite !map_app. cbn [map]. rewrite ?map_app. cbn [map app]. repeat (rewrite <- ?app_assoc; cbn [app]). reflexivity.
          - rewrite app_nil_r. apply in_app_iff in Hx. apply in_app_iff. destruct Hx as [Hx|Hx]; [left; exact Hx| right; right; right].
            apply in_app_iff in Hx. apply in_app_iff. exact Hx. }
        assert (DSTL : forall x, In x (P ++ R' ++ T0) -> abatch_addr L (qb_slot (snd x)) + 8192 <= TL \/ TL + 8192 <= abatch_addr L (qb_slot (snd x))).
        { intros x Hx. pose proof (baddr_disj L x tl (NTL x Hx)) as D. unfold baddr, Q_BATCH_BYTES in D. apply D.
          - eapply (proj1 (Forall_forall _ _) SL). apply in_app_iff in Hx. apply in_app_iff. destruct Hx as [Hx|Hx]; [left; exact Hx| right; right].
            apply in_app_iff in Hx. apply in_app_iff. destruct Hx as [Hx|Hx]; [left; right; exact Hx| right; apply in_app_iff; left; exact Hx].
          - exact STL. }
        xport EC1 MUu WMu ltac:(rewrite length_app, ?LEC, ?LEN; clear -CRNG NRNG KF DCN GC3 GC4 DTLC; lia).
        destruct JC1 as [jc JC1]. xport JC1 MUu WMu ltac:(clear -CRNG NRNG KF DCN GC3 GC4 DTLC; lia).
        destruct JN1 as [jn JN1]. xport JN1 MUu WMu ltac:(clear -CRNG NRNG KF DCN GN3 GN4 DTLN; lia).
        assert (CHP2 : chain m2 P CUR).
        { eapply chain_frame; [exact CHP1| exact MUu| exact WMu|]. apply Forall_forall. intros x Hx.
          pose proof (DSTL x ltac:(apply in_app_iff; left; exact Hx)) as D3.
          (nd_pre (OTH x ltac:(apply in_app_iff; left; exact Hx)) 4%nat; intros D1 D2 (G1 & G2 & G3 & G4) _; nd_post). unfold baddr, Q_BATCH_BYTES in *. cbn. clear -D1 D2 D3 G3 G4. lia. }
        assert (CHR2 : chain m2 R' 0).
        { eapply chain_frame; [exact CHR1| exact MUu| exact WMu|]. apply Forall_forall. intros x Hx.
          pose proof (DSTL x ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hx)) as D3.
          (nd_pre (OTH x ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hx)) 4%nat; intros D1 D2 (G1 & G2 & G3 & G4) _; nd_post). unfold baddr, Q_BATCH_BYTES in *. cbn. clear -D1 D2 D3 G3 G4. lia. }
        assert (CT02 : chain m2 T0 TL).
        { eapply chain_frame; [exact CT0| exact MUu| exact WMu|]. apply Forall_forall. intros x Hx.
          pose proof (DSTL x ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Hx)) as D3.
          (nd_pre (OTH x ltac:(apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; exact Hx)) 4%nat; intros D1 D2 (G1 & G2 & G3 & G4) _; nd_post). unfold baddr, Q_BATCH_BYTES in *. cbn. clear -D1 D2 D3 G3 G4. lia. }
        (* [comment removed for export] *)
        (nd_pre TLR 6%nat; intros TLR1 TLR2 TLR3 TLR4 TLR5 TLR6; nd_post). fold TL in TLR1, TLR2, TLR3. unfold Q_BATCH_BYTES, Q_BATCH in TLR3, TLR6.
        xport TLR1 MUu WMu ltac:(clear -DTLC DTLN GT3 GT4; lia).
        xport TLR2 MUu WMu ltac:(rewrite length_map, qhdrs_length by exact TLR5; clear -DTLC DTLN GT3 GT4 TLR4 TLR6; lia).
        destruct TLR3 as [jt TLR3]. xport TLR3 MUu WMu ltac:(clear -DTLC DTLN GT3 GT4 TLR6; lia).
        assert (CT2 : chain m2 ((T0 ++ [tl]) ++ [bq_empty nx]) 0).
        { apply (proj2 (chain_app _ _ _ _)). split.
          - apply (proj2 (chain_app _ _ _ _)). cbn [tfirst app]. unfold baddr. fold TL. split; [exact CT02|].
            apply (proj2 (chain_cons _ _ _ _)). split; [| apply chain_nil]. cbn [tfirst]. unfold baddr. cbn [bq_empty snd qb_slot]. fold NXT.
            apply (proj2 (abatch_cells_split _ _ _ _)). fold TL. split; [exact TL2|]. split; [exact TLR1|]. split; [exact TLR2|].
            split; [exists jt; unfold Q_BATCH_BYTES; exact TLR3|]. unfold Q_BATCH. exact (conj TLR4 (conj TLR5 TLR6)).
          - apply (proj2 (chain_cons _ _ _ _)). split; [| apply chain_nil].
            unfold abatch_cells. cbn [fst snd tfirst bq_empty b_size b_count b_chunks qb_slot qb_ks qhdrs map length Z.of_nat]. fold NXT. unfold Q_BATCH_BYTES, Q_BATCH.
            split; [exact CN2|]. split; [apply u64arr_nil; clear -GN1 GN2; lia|].
            split; [exists jn; rewrite Z.mul_0_r, Z.add_0_r, Z.sub_0_r; exact JN1|]. clear. lia. }
        clear CT0 CT02 TLR1 TLR2 TLR3 TL2 TLN.
        (* [comment removed for export] *)
        assert (MU12 : munch ([(LST, LST + 24); (TMP, TMP + 32)] ++ map (fun x => (baddr L x, baddr L x + 8192)) (cur :: (nx :: R') ++ T0 ++ [tl]))%Z m m2).
        { eapply (munch_trans_w _ _ _ _ _ _ MUc MUu).
          - unfold baddr. cbn [map app snd]. fold CUR. fold NXT. solve_sub_fpw ltac:(clear -CRNG NRNG KF; lia).
          - apply sub_fp_by_incl'. unfold baddr. cbn [map app snd]. fold CUR. fold NXT. fold TL.
            repeat (apply Forall_cons; [first [ find_ivw ltac:(clear; lia)
                                               | apply Exists_exists; exists (TL, TL + 8192)%Z; split; [| cbn; clear; lia];
                                                 right; right; right; right; rewrite map_app, in_app_iff; right; rewrite map_app, in_app_iff; right; left; reflexivity ] |]).
            apply Forall_nil. }
        step.                                             (* [comment removed for export] *)
        step. if_cases KX; zify_cond KX.                  (* [comment removed for export] *)
        * (* [comment removed for export] *)
          assert (RNE' : R' <> []) by (intros ->; cbn in KX; rewrite ?unsigned_lit in KX by lia; lia).
          assert (TFE : tfirst L R' 0 = baddr L (hd nx R')) by (destruct R'; [congruence| reflexivity]).
          assert (MB : merge_bq cur (nx :: R') = (fst (merge_bq (bq_merge cur nx) R'), bq_empty nx :: snd (merge_bq (bq_merge cur nx) R'))).
          { cbn [merge_bq]. unfold Q_BATCH. destruct (Z.leb_spec0 (b_count (fst cur) + b_count (fst nx)) 1021); [| exfalso; clear -KF n; lia].
            destruct (merge_bq (bq_merge cur nx) R'); reflexivity. }
          assert (LLN : (tlast L (cur :: nx :: R') 0 =? NXT) = false).
          { apply Z.eqb_neq. rewrite 2!tlast_cons_ne by congruence. (nd_pre (tlast_in R' 0 RNE') 3%nat; intros z Hz ndR1__; nd_post; revert ndR1__; intros ->).
            (nd_pre (OTH z ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hz)) 3%nat; intros _ D2 _; nd_post). clear -D2. lia. }
          rewrite LLN in LS2. rewrite TFE.
          replace (baddr L (hd nx R')) with (baddr L (hd (bq_merge cur nx) R')) by (destruct R'; [congruence| reflexivity]).
          setreg 14 (Z_to_bv 64 (baddr L (bq_merge cur nx))) ltac:(unfold baddr; cbn [bq_merge snd qb_slot]; reflexivity).
          unfold Q_BATCH_BYTES.
          eapply evtF_mono.
          { eapply (IH P (bq_merge cur nx) R' ((T0 ++ [tl]) ++ [bq_empty nx]) (tb + 8192) (ex + 8192)).
            - cbn in HD. clear -HD. lia.
            - exact RNE'.
            - exact MI2.
            - rewrite length_app in LS2 |- *. cbn [length] in LS2 |- *.
              replace (Z.of_nat (length P + S (S (length R'))) - 1) with (Z.of_nat (length P + S (length R'))) in LS2 by lia.
              rewrite tlast_cons_ne by exact RNE'. rewrite 2!tlast_cons_ne in LS2 by congruence. exact LS2.
            - apply (proj2 (chain_app _ _ _ _)). cbn [tfirst]. unfold baddr. cbn [bq_merge snd qb_slot]. fold CUR. split; [exact CHP2|].
              apply (proj2 (chain_cons _ _ _ _)). split; [| exact CHR2].
              unfold abatch_cells. cbn [fst snd bq_merge b_size b_count b_chunks qb_slot qb_ks]. fold CUR. unfold Q_BATCH_BYTES, Q_BATCH.
              replace (b_size (fst cur) + (b_size (fst nx) - 8192)) with (b_size (fst cur) + b_size (fst nx) - 8192) by lia.
              split; [exact CC2|]. split; [rewrite qhdrs_app, map_app by exact NLEN; exact EC1|].
              split; [exists jc; exact JC1|]. rewrite !length_app. clear -CCNT NCNT CLEN NLEN CRNG NRNG KF. lia.
            - rewrite tfirst_app by (destruct T0; cbn; congruence). rewrite tlast_app1. unfold baddr. cbn [bq_empty snd qb_slot]. fold NXT.
              rewrite !length_app in TM2 |- *. cbn [length] in TM2 |- *. unfold Q_BATCH_BYTES in TM2.
              replace (Z.of_nat (length (T0 ++ [tl]) + 1)) with (Z.of_nat (length T0 + 1) + 1) by (rewrite length_app; cbn [length]; lia).
              exact TM2.
            - exact CT2.
            - apply Forall_forall. intros x Hx. apply in_app_iff in Hx. cbn [app In] in Hx.
              destruct Hx as [Hx|[E|Hx]]; [| subst x| apply in_app_iff in Hx; destruct Hx as [Hx|Hx]; [| apply in_app_iff in Hx; destruct Hx as [Hx|[E|F0]]; [| subst x| destruct F0]]].
              + eapply (proj1 (Forall_forall _ _) GEO). apply in_app_iff. left. exact Hx.
              + unfold bgeom, baddr, AIMG_HI, Q_BATCH_BYTES. cbn [bq_merge snd qb_slot]. fold CUR. clear -GC1 GC2 GC3 GC4. tauto.
              + eapply (proj1 (Forall_forall _ _) GEO). apply in_app_iff. right. right. apply in_app_iff. left. right. exact Hx.
              + eapply (proj1 (Forall_forall _ _) GEO). apply in_app_iff. right. right. apply in_app_iff. right. exact Hx.
              + unfold bgeom, baddr, AIMG_HI, Q_BATCH_BYTES. cbn [bq_empty snd qb_slot]. fold NXT. clear -GN1 GN2 GN3 GN4. tauto.
            - apply Forall_forall. intros x Hx. apply in_app_iff in Hx. cbn [app In] in Hx.
              destruct Hx as [Hx|[E|Hx]]; [| subst x| apply in_app_iff in Hx; destruct Hx as [Hx|Hx]; [| apply in_app_iff in Hx; destruct Hx as [Hx|[E|F0]]; [| subst x| destruct F0]]].
              + eapply (proj1 (Forall_forall _ _) SL). apply in_app_iff. left. exact Hx.
              + cbn [bq_merge snd qb_slot]. eapply (proj1 (Forall_forall _ _) SL). apply in_app_iff. right. left. reflexivity.
              + eapply (proj1 (Forall_forall _ _) SL). apply in_app_iff. right. right. apply in_app_iff. left. right. exact Hx.
              + eapply (proj1 (Forall_forall _ _) SL). apply in_app_iff. right. right. apply in_app_iff. right. exact Hx.
              + cbn [bq_empty snd qb_slot]. eapply (proj1 (Forall_forall _ _) SL). apply in_app_iff. right. right. left. reflexivity.
            - revert ND. rewrite !map_app. cbn [map]. rewrite !map_app. cbn [map bq_merge bq_empty snd qb_slot app]. rewrite ?map_app. cbn [map].
              intros ND. refine (proj1 (list_relations.list.NoDup_Permutation_proper _ _ _) ND).
              apply Permutation_app_head. apply perm_skip. repeat (rewrite <- ?app_assoc; cbn [app]).
              match goal with |- Permutation _ (?l1 ++ ?l2 ++ [?t; ?b]) =>
                replace (l1 ++ l2 ++ [t; b]) with ((l1 ++ l2 ++ [t]) ++ [b]) by (rewrite <- !app_assoc; reflexivity) end.
              apply Permutation_cons_append.
            - constructor; [| exact (Forall_inv_tail (Forall_inv_tail SZ))]. cbn [fst bq_merge b_size]. unfold Q_BATCH_BYTES in *. clear -SZC SZN. lia.
            - cbn [map fst bq_merge b_size]. rewrite batches_bytes_cons. cbn [b_size]. clear -SZS SZC SZN. unfold Q_BATCH_BYTES in *. lia.
            - apply Forall_forall. intros x Hx. cbn [app In] in Hx.
              destruct Hx as [E|Hx]; [subst x| apply in_app_iff in Hx; destruct Hx as [Hx|Hx]; [| apply in_app_iff in Hx; destruct Hx as [Hx|[E|F0]]; [| subst x| destruct F0]]].
              + unfold baddr. cbn [bq_merge snd qb_slot]. fold CUR. exact RC.
              + eapply (proj1 (Forall_forall _ _) RB). right. apply in_app_iff. left. right. exact Hx.
              + eapply (proj1 (Forall_forall _ _) RB). right. apply in_app_iff. right. exact Hx.
              + unfold baddr. cbn [bq_empty snd qb_slot]. fold NXT. exact RN.
            - clear -TB0; lia.
            - revert TB1; clear; cbn [length]; unfold Q_BATCH_BYTES; intros; lia.
            - clear -EX0; lia.
            - revert EX1; clear; cbn [length]; unfold Q_BATCH_BYTES; intros; lia.
            - revert LEN40; clear; rewrite !length_app; cbn [length]; rewrite ?length_app; cbn [length]; intros; lia. }
          cbv beta. unfold mloop_post. rewrite MB. destruct (merge_bq (bq_merge cur nx) R') as [l' e']. cbn [fst snd].
          intros ms' (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & m' & -> & MU' & WM' & MI' & LS' & CH' & TM' & CT').
          rewrite <- !app_assoc in TM', CT'. cbn [app] in TM', CT'.
          rewrite !length_app in TM' |- *. cbn [length app] in TM' |- *. unfold Q_BATCH_BYTES in TM' |- *.
          replace (ex + 8192 * Z.of_nat (S (length e'))) with (ex + 8192 + 8192 * Z.of_nat (length e')) by lia.
          replace (tb + 8192 * Z.of_nat (S (length e'))) with (tb + 8192 + 8192 * Z.of_nat (length e')) by lia.
          do 8 eexists. exists m'. split; [reflexivity|].
          split. { eapply (munch_trans_w _ _ _ _ _ _ MU12 MU'); apply sub_fp_incl; [intros iv Hiv; exact Hiv|].
                   intros iv Hiv. apply in_app_iff in Hiv. destruct Hiv as [Hiv|Hiv].
                   { cbn [In] in Hiv. destruct Hiv as [H|[H|[]]]; [left; exact H| right; left; exact H]. }
                   apply in_map_iff in Hiv. (nd_pre Hiv 2%nat; intros x ndR1__; nd_post; destruct ndR1__ as (<- & ndR2__); rename ndR2__ into Hx). right. right. apply in_map_iff.
                   destruct Hx as [<-|Hx]; [exists cur; split; [reflexivity| left; reflexivity]|].
                   apply in_app_iff in Hx. destruct Hx as [Hx|Hx]; [exists x; split; [reflexivity| right; right; apply in_app_iff; left; exact Hx]|].
                   apply in_app_iff in Hx. destruct Hx as [Hx|[<-|[]]]; [exists x; split; [reflexivity| right; right; apply in_app_iff; right; exact Hx]|].
                   exists nx; split; [reflexivity| right; left; reflexivity]. }
          split; [eapply wmono_trans; [exact WMc| eapply wmono_trans; [exact WMu| exact WM']]|]. split; [exact MI'|].
          split. { revert LS'. rewrite ?length_app. intros X; exact X. } split; [exact CH'|].
          rewrite <- !app_assoc. cbn [app]. split; [| exact CT'].
          revert TM'. rewrite ?length_app. cbn [length]. intros X.
          first [exact X| replace (length T0 + 1 + S (length e'))%nat with (length T0 + S (S (length e')))%nat by lia; exact X].
        * (* [comment removed for export] *)
          assert (RNIL : R' = []).
          { destruct R' as [|r R'']; [reflexivity| exfalso].
            pose proof (tfirst_pos (r :: R'') 0 GR ltac:(congruence)) as X. unfold AIMG_HI in X. cbn [tfirst] in X, KX.
            pose proof (Forall_inv GR) as Y. unfold bgeom, Q_BATCH_BYTES in Y. cbv beta in Y. (nd_pre Y 3%nat; intros Y1 Y Y3; nd_post).
            rewrite ?unsigned_lit in KX by (clear -X Y; lia). clear -X KX. lia. }
          subst R'. clear GR KX.
          assert (MB : merge_bq cur [nx] = ([bq_merge cur nx], [bq_empty nx])).
          { cbn [merge_bq]. unfold Q_BATCH. destruct (Z.leb_spec0 (b_count (fst cur) + b_count (fst nx)) 1021); [reflexivity| exfalso; clear -KF n; lia]. }
          apply evtF_done. unfold mloop_post. rewrite MB. cbv beta iota zeta. cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat].
          rewrite !Z.mul_1_r.
          do 8 eexists. exists m2. split; [reflexivity|].
          split. { exact MU12. }
          split; [eapply wmono_trans; [exact WMc| exact WMu]|]. split; [exact MI2|].
          split. { rewrite length_app in LS2 |- *. cbn [length] in LS2 |- *.
                   replace (Z.of_nat (length P + 2) - 1) with (Z.of_nat (length P + 1)) in LS2 by lia.
                   cbn [tlast map List.last] in LS2. rewrite Z.eqb_refl in LS2. exact LS2. }
          split. { apply (proj2 (chain_app _ _ _ _)). split; [exact CHP2|]. apply (proj2 (chain_cons _ _ _ _)). split; [| apply chain_nil].
                   unfold abatch_cells. cbn [fst snd tfirst bq_merge b_size b_count b_chunks qb_slot qb_ks]. fold CUR. unfold Q_BATCH_BYTES, Q_BATCH.
                   cbn [tfirst] in CC2. replace (b_size (fst cur) + (b_size (fst nx) - 8192)) with (b_size (fst cur) + b_size (fst nx) - 8192) by lia.
                   split; [exact CC2|]. split.
                   - rewrite qhdrs_app, map_app by exact NLEN. exact EC1.
                   - split; [exists jc; exact JC1|]. rewrite !length_app. clear -CCNT NCNT CLEN NLEN CRNG NRNG KF. lia. }
          split; [| exact CT2].
          lazymatch type of TM2 with rw_cells _ _ _ ?l2 => lazymatch goal with |- rw_cells _ _ _ ?l1 => replace l1 with l2; [exact TM2|] end end.
          rewrite (tfirst_app L (T0 ++ [tl]) [bq_empty nx] tf0) by (destruct T0; cbn; congruence). rewrite tlast_app1. unfold baddr. cbn [bq_empty snd qb_slot]. fold NXT.
          rewrite !length_app. cbn [length]. unfold Q_BATCH_BYTES.
          replace (Z.of_nat (length T0 + 1 + 1)) with (Z.of_nat (length T0 + 1) + 1) by lia. reflexivity.
  Qed.
End Loop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End CANSEC1.
Notation AMERGE_STACK := 16 (only parsing).

Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition amerge_fun (X : list bq) : list bq * list bq :=
  match X with [] => ([], []) | cur :: R => merge_bq cur R end.

Definition amerge_post (L : alayout) (LST TMP lb tf0 tl0 tb lo : Z) (X T : list bq)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    let '(l, e) := amerge_fun X in
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 LST) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch ([(bv_unsigned sp - AMERGE_STACK, bv_unsigned sp); (LST, LST + 32); (TMP, TMP + 32)]
              ++ map (fun x => (baddr L x, baddr L x + Q_BATCH_BYTES)) (X ++ T))%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' LST [C8 (Z_to_bv 64 (Z.of_nat (length l))); C8 (Z_to_bv 64 (tfirst L X 0)); C8 (Z_to_bv 64 (tlast L l 0));
                             C8 (Z_to_bv 64 (lb - Q_BATCH_BYTES * Z.of_nat (length e)))]
    /\ chain L m' l 0
    /\ rw_cells asegs m' TMP [C8 (Z_to_bv 64 (Z.of_nat (length (T ++ e)))); C8 (Z_to_bv 64 (tfirst L (T ++ e) tf0));
                             C8 (Z_to_bv 64 (tlast L (T ++ e) tl0)); C8 (Z_to_bv 64 (tb + Q_BATCH_BYTES * Z.of_nat (length e)))]
    /\ chain L m' (T ++ e) 0.

#[using="Type"] Lemma disj_objs_above : forall L LST TMP Y A n, Forall (bgeom L LST TMP) Y -> ATOP <= A ->
  disjoint_from (map (fun x => (baddr L x, baddr L x + Q_BATCH_BYTES)) Y) A n.
Proof.
  intros L LST TMP Y A n HF HA. apply disjoint_from_Forall. apply Forall_map. eapply Forall_impl; [| exact HF].
  intros x (G1 & G2 & _). cbn [fst snd]. left. unfold Q_BATCH_BYTES in *. lia.
Qed.

#[using="Type"] Lemma merge_bq_baddr_in : forall L R cur x, In x (fst (merge_bq cur R) ++ snd (merge_bq cur R)) ->
  exists y, In y (cur :: R) /\ baddr L y = baddr L x.
Proof.
  induction R as [|nx R IH]; intros cur x Hx; cbn [merge_bq fst snd app] in Hx.
  - destruct Hx as [<-|[]]. exists cur. split; [left; reflexivity| reflexivity].
  - destruct (b_count (fst cur) + b_count (fst nx) <=? Q_BATCH).
    + specialize (IH (bq_merge cur nx) x). destruct (merge_bq (bq_merge cur nx) R) as [l e]. cbn [fst snd] in Hx, IH.
      assert (Hx' : In x (l ++ e) \/ x = bq_empty nx).
      { apply in_app_iff in Hx. destruct Hx as [Hx|[<-|Hx]]; [left; apply in_app_iff; left; exact Hx| right; reflexivity| left; apply in_app_iff; right; exact Hx]. }
      destruct Hx' as [Hx'| ->].
      * (nd_pre (IH Hx') 3%nat; intros y Hy EY; nd_post). destruct Hy as [<-|Hy].
        -- exists cur. split; [left; reflexivity| exact EY].
        -- exists y. split; [right; right; exact Hy| exact EY].
      * exists nx. split; [right; left; reflexivity| reflexivity].
    + specialize (IH nx x). destruct (merge_bq nx R) as [l e]. cbn [fst snd] in Hx, IH.
      destruct Hx as [<-|Hx].
      * exists cur. split; [left; reflexivity| reflexivity].
      * (nd_pre (IH Hx) 3%nat; intros y Hy EY; nd_post). exists y. split; [right; exact Hy| exact EY].
Qed.

#[using="Type"] Lemma amerge_spec : forall L RNG (LST TMP lb tf0 tl0 tb lo : Z) (X T : list bq)
    ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : amem),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - AMERGE_STACK ->
  mem_inv asegs m ->
  rw_cells asegs m LST [C8 (Z_to_bv 64 (Z.of_nat (length X))); C8 (Z_to_bv 64 (tfirst L X 0)); C8 (Z_to_bv 64 (tlast L X 0)); C8 (Z_to_bv 64 lb)] ->
  chain L m X 0 ->
  rw_cells asegs m TMP [C8 (Z_to_bv 64 (Z.of_nat (length T))); C8 (Z_to_bv 64 (tfirst L T tf0)); C8 (Z_to_bv 64 (tlast L T tl0)); C8 (Z_to_bv 64 tb)] ->
  chain L m T 0 ->
  Forall (bgeom L LST TMP) (X ++ T) -> Forall (fun x => 0 <= qb_slot (snd x)) (X ++ T) ->
  NoDup (map (fun x => qb_slot (snd x)) (X ++ T)) ->
  Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) X -> batches_bytes (map fst X) < 2^62 ->
  0 <= LST -> LST + 32 <= ATOP -> 0 <= TMP -> TMP + 32 <= 2^47 -> (TMP + 32 <= LST \/ LST + 32 <= TMP) ->
  (bv_unsigned sp <= TMP \/ TMP + 32 <= lo) ->
  0 <= tf0 < 2^64 -> 0 <= tl0 < 2^64 -> 0 <= lb < 2^64 -> 0 <= tb -> tb + Q_BATCH_BYTES * Z.of_nat (length X) < 2^62 ->
  Z.of_nat (length (X ++ T)) < 2^40 ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG LST 32 -> rng RNG TMP 32 ->
  Forall (fun x => rng RNG (baddr L x) Q_BATCH_BYTES) (X ++ T) ->
  evtF asegs RNG (amerge_post L LST TMP lb tf0 tl0 tb lo X T ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 LST) (Z_to_bv 64 TMP) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 amerge_entry) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST CEIL LO MI LS CH TM CT GEO SL ND SZ SZS L1 L2 T1 T2 DTL DTS TF0 TL0 LB TB0 TB1 LEN40 RSTK RL RT RB.
  unfold amerge_entry. atop_facts. unfold Q_BATCH_BYTES in TB1.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (LST + 24, LST + 32)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 16%nat ST.
  step. step.                                  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac chain_over CHx MUx WMx GEOx sel :=
    eapply chain_frame in CHx; [| exact MUx | exact WMx |
      apply Forall_forall; let xg := fresh "xg" in let Hxg := fresh "Hxg" in let Gx := fresh "Gx" in intros xg Hxg;
      lazymatch type of GEOx with Forall (bgeom ?L ?LST ?TMP) _ =>
        assert (Gx : bgeom L LST TMP xg) by (eapply (proj1 (Forall_forall _ _) GEOx); apply in_app_iff; sel (); exact Hxg) end;
      unfold bgeom, AIMG_HI, Q_BATCH_BYTES in Gx; unfold Q_BATCH_BYTES; cbn [disjoint_from fst snd]; lia ].
  (* [comment removed for export] *)
  Local Ltac exit2 sp MU WM ST FR CH CT GEO LS TM :=
    step; zstep;                               (* [comment removed for export] *)
    step;                                      (* [comment removed for export] *)
    step; step; step;                          (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp);
    chain_over CH MU WM GEO ltac:(fun _ => left); chain_over CT MU WM GEO ltac:(fun _ => right);
    apply evtF_done; unfold amerge_post; cbn [amerge_fun merge_bq length Z.of_nat Pos.of_succ_nat Pos.to_nat tfirst tlast map List.last];
    rewrite !app_nil_r, !Z.mul_0_r, !Z.sub_0_r, !Z.add_0_r in *;
    do 14 eexists; eexists; split; [reflexivity|];
    split; [ eapply munch_weaken; [| exact MU]; apply sub_fp_by_incl';
             constructor; [apply Exists_exists; eexists; split; [left; reflexivity| cbn; lia]|];
             constructor; [apply Exists_exists; eexists; split; [right; left; reflexivity| cbn; lia]|]; constructor |];
    split; [exact WM|]; split; [assumption|]; split; [exact ST|];
    split; [exact LS|]; split; [exact CH|]; split; [exact TM| exact CT].
  destruct X as [|cur R].
  - (* [comment removed for export] *)
    cbn [tfirst tlast map List.last length Z.of_nat] in LS.
    step. step. if_lit.                        (* [comment removed for export] *)
    exit2 sp MU WM ST FR CH CT GEO LS TM.
  - (* [comment removed for export] *)
    pose proof CH as CH0.
    destruct (proj1 (chain_cons _ _ _ _ _) CH) as [BC CHR]. clear CH. rename CH0 into CH.
    (nd_pre BC 6%nat; intros CC EC JC CCNT CLEN CRNG; nd_post).
    assert (GC : bgeom L LST TMP cur) by (eapply (proj1 (Forall_forall _ _) GEO); left; reflexivity).
    assert (RC : rng RNG (baddr L cur) Q_BATCH_BYTES) by (pose proof (Forall_inv RB) as X; exact X).
    unfold bgeom, AIMG_HI, Q_BATCH_BYTES in GC, RC. unfold baddr in GC, RC. cbn [fst snd] in CC, GC, RC. cbn [tfirst tlast map List.last] in LS. unfold baddr in LS.
    set (CUR := abatch_addr L (qb_slot (snd cur))) in *. (nd_pre GC 4%nat; intros GC1 GC2 GC3 GC4; nd_post).
    xport CC MU WM ltac:(clear -GC2 GC3 CEIL LO; lia).
    clear EC JC.
    step. step. if_cases KC; zify_cond KC.     (* [comment removed for export] *)
    { exfalso. rewrite ?unsigned_lit in KC by (clear -GC1 GC2; lia). clear -KC GC1. lia. }
    clear KC.
    destruct R as [|nx R'].
    + (* [comment removed for export] *)
      cbn [tfirst] in CC.
      step. step. if_lit.                      (* [comment removed for export] *)
      clear CC. exit2 sp MU WM ST FR CH CT GEO LS TM.
    + (* [comment removed for export] *)
      assert (GN : bgeom L LST TMP nx) by (eapply (proj1 (Forall_forall _ _) GEO); right; left; reflexivity).
      unfold bgeom, AIMG_HI, Q_BATCH_BYTES, baddr in GN. cbn [tfirst] in CC. unfold baddr in CC.
      set (NXT := abatch_addr L (qb_slot (snd nx))) in *. (nd_pre GN 4%nat; intros GN1 GN2 GN3 GN4; nd_post).
      step. step. if_cases KN; zify_cond KN.   (* [comment removed for export] *)
      { exfalso. rewrite ?unsigned_lit in KN by (clear -GN1 GN2; lia). clear -KN GN1. lia. }
      clear KN.
      step. step. step. step. step.            (* [comment removed for export] *)
      chain_over CH MU WM GEO ltac:(fun _ => left). chain_over CT MU WM GEO ltac:(fun _ => right).
      clear CC CHR.
      eapply evtF_cut.
      { eapply (mloop_spec L RNG LST TMP CUR lb tf0 tl0) with (P := []) (R := nx :: R') (T := T) (tb := tb) (ex := 0) (d := length (nx :: R'));
          try eassumption; try reflexivity.
        - apply Z_to_bv_eqm. reflexivity.
        - clear -GC1 GC2. lia.
        - congruence.
        - revert TB1. clear. unfold Q_BATCH_BYTES. cbn [length]. intros; lia.
        - revert LEN40. clear. unfold Q_BATCH_BYTES. rewrite length_app. cbn [length]. intros; lia. }
      cbv beta. unfold mloop_post, amerge_post. cbn [amerge_fun].
      destruct (merge_bq cur (nx :: R')) as [l e] eqn:MB.
      intros ms' (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & m' & -> & MU' & WM' & MI' & LS' & CH' & TM' & CT').
      clear LS TM MI.
      xport FR MU' WM' ltac:(cbn [app disjoint_from fst snd]; split; [clear -CEIL LO L2; lia| split; [clear -DTS LO; lia| eapply disj_objs_above; [exact GEO| atop_facts; clear -CEIL LO; lia]]]).
      xport ST MU' WM' ltac:(cbn [app disjoint_from fst snd]; split; [clear -CEIL LO L2; lia| split; [clear -DTS LO; lia| eapply disj_objs_above; [exact GEO| atop_facts; clear -CEIL LO; lia]]]).
      box MU'.
      snapshot [(bv_unsigned sp + -16, bv_unsigned sp); (LST + 24, LST + 32)]%Z MUe WMe.
      step. zstep.                             (* [comment removed for export] *)
      setreg 11%Z (Z_to_bv 64 (lb - Q_BATCH_BYTES * Z.of_nat (length e))) ltac:(apply Z_to_bv_eqm; unfold Q_BATCH_BYTES; clear; Z.div_mod_to_equations; lia).
      step.                                    (* [comment removed for export] *)
      step. step. step.                        (* [comment removed for export] *)
      release_frame FR ST (bv_unsigned sp).
      apply evtF_done. cbn [length app] in LS'. cbn [app] in CH'.
      do 14 eexists. eexists. split; [reflexivity|].
      split. { (* [comment removed for export] *)
        unbox MU'.
        lazymatch goal with |- munch ?W m ?mf =>
          assert (S1 : sub_fp [(bv_unsigned sp + -16, bv_unsigned sp); (LST + 24, LST + 32)]%Z W);
          [ apply sub_fp_by_incl';
            constructor; [apply Exists_exists; eexists; split; [left; reflexivity| cbn; clear; lia]|];
            constructor; [apply Exists_exists; eexists; split; [right; left; reflexivity| cbn; clear; lia]|]; constructor |] end.
        lazymatch goal with |- munch ?W m ?mf =>
          assert (MU2 : munch W m0 mf); [eapply (munch_trans_w W _ _ _ _ _ MU' MUe); [| exact S1]
                                        |eapply (munch_trans_w W _ _ _ _ _ MU MU2); [exact S1| intros z Hz; exact Hz]] end.
        apply sub_fp_by_incl'. apply Forall_app. split.
        - constructor; [apply Exists_exists; eexists; split; [right; left; reflexivity| cbn; clear; lia]|].
          constructor; [apply Exists_exists; eexists; split; [right; right; left; reflexivity| cbn; clear; lia]|]. constructor.
        - apply Forall_map. apply Forall_forall. intros x Hx. apply Exists_exists. eexists. split; [right; right; right; apply in_map; exact Hx|]. cbn; clear; lia. }
      split; [eapply wmono_trans; [exact WM| first [exact WM'| eapply wmono_trans; [exact WM'| exact WMe]]]|]. split; [assumption|]. split; [exact ST|].
      split. { cbn [tfirst]. unfold baddr. fold CUR. exact LS'. }
      split. { eapply chain_frame; [exact CH'| exact MUe| exact WMe|]. apply Forall_forall. intros x Hx.
               (nd_pre (merge_bq_baddr_in L (nx :: R') cur x ltac:(rewrite MB; apply in_app_iff; left; exact Hx)) 3%nat; intros y Hy EY; nd_post).
               rewrite <- EY. pose proof (proj1 (Forall_forall _ _) GEO y ltac:(apply in_app_iff; left; exact Hy)) as G.
               unfold bgeom, AIMG_HI, Q_BATCH_BYTES in G. unfold Q_BATCH_BYTES. cbn [disjoint_from fst snd]. clear -G CEIL LO. lia. }
      split; [exact TM'|].
      eapply chain_frame; [exact CT'| exact MUe| exact WMe|]. apply Forall_app. split.
      * apply Forall_forall. intros x Hx. pose proof (proj1 (Forall_forall _ _) GEO x ltac:(apply in_app_iff; right; exact Hx)) as G.
        unfold bgeom, AIMG_HI, Q_BATCH_BYTES in G. unfold Q_BATCH_BYTES. cbn [disjoint_from fst snd]. clear -G CEIL LO. lia.
      * apply Forall_forall. intros x Hx.
        (nd_pre (merge_bq_baddr_in L (nx :: R') cur x ltac:(rewrite MB; apply in_app_iff; right; exact Hx)) 3%nat; intros y Hy EY; nd_post).
        rewrite <- EY. pose proof (proj1 (Forall_forall _ _) GEO y ltac:(apply in_app_iff; left; exact Hy)) as G.
        unfold bgeom, AIMG_HI, Q_BATCH_BYTES in G. unfold Q_BATCH_BYTES. cbn [disjoint_from fst snd]. clear -G CEIL LO. lia.
Qed.
End CANSEC2.
End TwB.
End F_amerge.

(* [comment removed for export] *)
Module F_aqrec_iface.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_amerge__A3W.F_amerge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Fixpoint deq_bq (l : list bq) (bytes min_size : Z) {struct l} : list bq * list bq * Z :=
  match l with
  | [] => ([], [], bytes)
  | b :: l' => if min_size <? bytes
               then let '(taken, rest, bytes') := deq_bq l' (bytes - b_size (fst b)) min_size in (b :: taken, rest, bytes')
               else ([], l, bytes)
  end.

#[using="Type"] Lemma deq_bq_fst : forall l bytes min_size,
  let '(taken, rest, bytes') := deq_bq l bytes min_size in
  dequeue_while (map fst l) bytes min_size = (map fst taken, map fst rest, bytes').
Proof.
  induction l as [|b l IH]; intros bytes min_size; cbn [deq_bq dequeue_while map]; [reflexivity|].
  destruct (min_size <? bytes); [| reflexivity].
  specialize (IH (bytes - b_size (fst b)) min_size). destruct (deq_bq l (bytes - b_size (fst b)) min_size) as [[tk rs] b2].
  rewrite IH. reflexivity.
Qed.

(* [comment removed for export] *)
Definition qrec_mergeb (nb bytes : Z) : bool :=
  (Q_BATCH_BYTES * nb <? bytes) && (bytes * 100 <? Q_BATCH_BYTES * nb * 200).

(* [comment removed for export] *)
Definition qrec_fun (X : list bq) (bytes min_size : Z) : list bq * list bq * Z :=
  let '(gl, ex) := (if qrec_mergeb (Z.of_nat (length X)) bytes then amerge_fun X else (X, [])) in
  let '(taken, rest, bytes2) := deq_bq gl (bytes - Q_BATCH_BYTES * Z.of_nat (length ex)) min_size in
  (rest, ex ++ taken, bytes2).

End CANSEC1.
Notation QREC_FRAME := 80 (only parsing).
Notation QREC_FRONT_STACK := 96 (only parsing).   (* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition qrec_front_post (L : alayout) (X : list bq) (bytes min_size lo : Z)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 xs0 xs1 xs2 xs3 xs4 a0 a4 a5 a6 a7 t3 t4 t5 t6 tbw : word) m',
    let '(rest, T, bytes2) := qrec_fun X bytes min_size in
    ms' = MS (mkR (Z_to_bv 64 0x35c10) (Z_to_bv 64 (bv_unsigned sp - QREC_FRAME)) gp tp t0 t1 t2 xs0 xs1
                  a0 (Z_to_bv 64 (bv_unsigned sp - QREC_FRAME)) a2 a3 a4 a5 a6 a7 xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x35e08) fc None m' (seg_rom asegs)
    /\ munch ([(bv_unsigned sp - QREC_FRONT_STACK, bv_unsigned sp); (AQ_MUTEX, AQ_MUTEX + 4); (AQ_GCACHE, AQ_GCACHE + 32)]
              ++ map (fun x => (baddr L x, baddr L x + Q_BATCH_BYTES)) X)%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp - QREC_FRAME)
    (* [comment removed for export] *)
    /\ rw_cells asegs m' (bv_unsigned sp - QREC_FRAME)
         [C8 (Z_to_bv 64 (Z.of_nat (length T))); C8 (Z_to_bv 64 (tfirst L T 0)); C8 (Z_to_bv 64 (tlast L T 0)); C8 tbw]
    /\ rw_cells asegs m' (bv_unsigned sp - 48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    (* [comment removed for export] *)
    /\ rw_cells asegs m' AQ_MUTEX [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    (* [comment removed for export] *)
    /\ rw_cells asegs m' AQ_GCACHE [C8 (Z_to_bv 64 (Z.of_nat (length rest))); C8 (Z_to_bv 64 (tfirst L rest 0)); C8 (Z_to_bv 64 (tlast L rest 0));
                                    C8 (Z_to_bv 64 bytes2)]
    /\ chain L m' rest 0 /\ chain L m' T 0
    /\ bytes2 = batches_bytes (map fst rest) /\ bytes2 <= min_size.

Definition qrec_front_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (X : list bq) (bytes min_size lo : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - QREC_FRONT_STACK -> bv_unsigned sp <= 2^47 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 AQUAR_Q -> a1 = Z_to_bv 64 min_size -> 0 <= min_size < 2^63 ->
  (* [comment removed for export] *)
  rw_cells asegs m AQ_MUTEX [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  (* [comment removed for export] *)
  rw_cells asegs m AQ_GCACHE [C8 (Z_to_bv 64 (Z.of_nat (length X))); C8 (Z_to_bv 64 (tfirst L X 0)); C8 (Z_to_bv 64 (tlast L X 0)); C8 (Z_to_bv 64 bytes)] ->
  chain L m X 0 ->
  Forall (bgeom L AQ_GCACHE (bv_unsigned sp - QREC_FRAME)) X -> Forall (fun x => 0 <= qb_slot (snd x)) X ->
  NoDup (map (fun x => qb_slot (snd x)) X) ->
  Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) X -> bytes = batches_bytes (map fst X) -> bytes < 2^56 ->
  Z.of_nat (length X) < 2^40 ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> Forall (fun x => rng RNG (baddr L x) Q_BATCH_BYTES) X ->
  evtF asegs RNG (qrec_front_post L X bytes min_size lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x35aa0) fc None m (seg_rom asegs)).
End CANSEC2.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_amerge__A3W.F_amerge.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Fixpoint deq_bq (l : list bq) (bytes min_size : Z) {struct l} : list bq * list bq * Z :=
  match l with
  | [] => ([], [], bytes)
  | b :: l' => if min_size <? bytes
               then let '(taken, rest, bytes') := deq_bq l' (bytes - b_size (fst b)) min_size in (b :: taken, rest, bytes')
               else ([], l, bytes)
  end.

#[using="Type"] Lemma deq_bq_fst : forall l bytes min_size,
  let '(taken, rest, bytes') := deq_bq l bytes min_size in
  dequeue_while (map fst l) bytes min_size = (map fst taken, map fst rest, bytes').
Proof.
  induction l as [|b l IH]; intros bytes min_size; cbn [deq_bq dequeue_while map]; [reflexivity|].
  destruct (min_size <? bytes); [| reflexivity].
  specialize (IH (bytes - b_size (fst b)) min_size). destruct (deq_bq l (bytes - b_size (fst b)) min_size) as [[tk rs] b2].
  rewrite IH. reflexivity.
Qed.

(* [comment removed for export] *)
Definition qrec_mergeb (nb bytes : Z) : bool :=
  (Q_BATCH_BYTES * nb <? bytes) && (bytes * 100 <? Q_BATCH_BYTES * nb * 200).

(* [comment removed for export] *)
Definition qrec_fun (X : list bq) (bytes min_size : Z) : list bq * list bq * Z :=
  let '(gl, ex) := (if qrec_mergeb (Z.of_nat (length X)) bytes then amerge_fun X else (X, [])) in
  let '(taken, rest, bytes2) := deq_bq gl (bytes - Q_BATCH_BYTES * Z.of_nat (length ex)) min_size in
  (rest, ex ++ taken, bytes2).

End CANSEC1.
Notation QREC_FRAME := 80 (only parsing).
Notation QREC_FRONT_STACK := 96 (only parsing).   (* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition qrec_front_post (L : alayout) (X : list bq) (bytes min_size lo : Z)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 xs0 xs1 xs2 xs3 xs4 a0 a4 a5 a6 a7 t3 t4 t5 t6 tbw : word) m',
    let '(rest, T, bytes2) := qrec_fun X bytes min_size in
    ms' = MS (mkR (Z_to_bv 64 0x35c78) (Z_to_bv 64 (bv_unsigned sp - QREC_FRAME)) gp tp t0 t1 t2 xs0 xs1
                  a0 (Z_to_bv 64 (bv_unsigned sp - QREC_FRAME)) a2 a3 a4 a5 a6 a7 xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x35e70) fc None m' (seg_rom asegs)
    /\ munch ([(bv_unsigned sp - QREC_FRONT_STACK, bv_unsigned sp); (AQ_MUTEX, AQ_MUTEX + 4); (AQ_GCACHE, AQ_GCACHE + 32)]
              ++ map (fun x => (baddr L x, baddr L x + Q_BATCH_BYTES)) X)%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp - QREC_FRAME)
    (* [comment removed for export] *)
    /\ rw_cells asegs m' (bv_unsigned sp - QREC_FRAME)
         [C8 (Z_to_bv 64 (Z.of_nat (length T))); C8 (Z_to_bv 64 (tfirst L T 0)); C8 (Z_to_bv 64 (tlast L T 0)); C8 tbw]
    /\ rw_cells asegs m' (bv_unsigned sp - 48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    (* [comment removed for export] *)
    /\ rw_cells asegs m' AQ_MUTEX [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    (* [comment removed for export] *)
    /\ rw_cells asegs m' AQ_GCACHE [C8 (Z_to_bv 64 (Z.of_nat (length rest))); C8 (Z_to_bv 64 (tfirst L rest 0)); C8 (Z_to_bv 64 (tlast L rest 0));
                                    C8 (Z_to_bv 64 bytes2)]
    /\ chain L m' rest 0 /\ chain L m' T 0
    /\ bytes2 = batches_bytes (map fst rest) /\ bytes2 <= min_size.

Definition qrec_front_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (X : list bq) (bytes min_size lo : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - QREC_FRONT_STACK -> bv_unsigned sp <= 2^47 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 AQUAR_Q -> a1 = Z_to_bv 64 min_size -> 0 <= min_size < 2^63 ->
  (* [comment removed for export] *)
  rw_cells asegs m AQ_MUTEX [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  (* [comment removed for export] *)
  rw_cells asegs m AQ_GCACHE [C8 (Z_to_bv 64 (Z.of_nat (length X))); C8 (Z_to_bv 64 (tfirst L X 0)); C8 (Z_to_bv 64 (tlast L X 0)); C8 (Z_to_bv 64 bytes)] ->
  chain L m X 0 ->
  Forall (bgeom L AQ_GCACHE (bv_unsigned sp - QREC_FRAME)) X -> Forall (fun x => 0 <= qb_slot (snd x)) X ->
  NoDup (map (fun x => qb_slot (snd x)) X) ->
  Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) X -> bytes = batches_bytes (map fst X) -> bytes < 2^56 ->
  Z.of_nat (length X) < 2^40 ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> Forall (fun x => rng RNG (baddr L x) Q_BATCH_BYTES) X ->
  evtF asegs RNG (qrec_front_post L X bytes min_size lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x35b08) fc None m (seg_rom asegs)).
End CANSEC2.
End TwB.
End F_aqrec_iface.

(* [comment removed for export] *)
Module F_aqrec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AKitR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_amerge__A3W.F_amerge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_amerge__A3W.F_aqrec_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition bslot (x : bq) : Z := qb_slot (snd x).
#[using="Type"] Lemma bslot_merge : forall cur nx, bslot (bq_merge cur nx) = bslot cur. Proof. reflexivity. Qed.
#[using="Type"] Lemma bslot_empty : forall nx, bslot (bq_empty nx) = bslot nx. Proof. reflexivity. Qed.
#[using="Type"] Lemma merge_bq_slots : forall R cur,
  Permutation (map bslot (fst (merge_bq cur R) ++ snd (merge_bq cur R))) (map bslot (cur :: R)).
Proof.
  induction R as [|nx R IH]; intros cur; cbn [merge_bq fst snd app map]; [apply Permutation_refl|].
  destruct (b_count (fst cur) + b_count (fst nx) <=? Q_BATCH).
  - specialize (IH (bq_merge cur nx)). destruct (merge_bq (bq_merge cur nx) R) as [l e]. cbn [fst snd] in IH |- *.
    rewrite map_app in IH |- *. cbn [map] in IH |- *. rewrite bslot_merge in IH. rewrite bslot_empty.
    eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|].
    apply (Permutation_trans (l' := bslot nx :: bslot cur :: map bslot R)); [| apply perm_swap].
    apply perm_skip. exact IH.
  - specialize (IH nx). destruct (merge_bq nx R) as [l e]. cbn [fst snd] in IH |- *.
    cbn [app map]. apply perm_skip. exact IH.
Qed.
#[using="Type"] Lemma merge_bq_sizes : forall R cur,
  Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) (cur :: R) ->
  Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) (fst (merge_bq cur R) ++ snd (merge_bq cur R)).
Proof.
  induction R as [|nx R IH]; intros cur HF; cbn [merge_bq fst snd].
  - rewrite app_nil_r. exact HF.
  - pose proof (Forall_inv HF) as HC. pose proof (Forall_inv (Forall_inv_tail HF)) as HN. pose proof (Forall_inv_tail (Forall_inv_tail HF)) as HR.
    cbv beta in HC, HN.
    destruct (b_count (fst cur) + b_count (fst nx) <=? Q_BATCH).
    + specialize (IH (bq_merge cur nx)). destruct (merge_bq (bq_merge cur nx) R) as [l e]. cbn [fst snd] in IH |- *.
      assert (HM : Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) (bq_merge cur nx :: R)).
      { constructor; [| exact HR]. cbn [bq_merge fst b_size]. lia. }
      specialize (IH HM). apply Forall_app in IH as [I1 I2]. apply Forall_app. split; [exact I1|]. constructor; [| exact I2].
      cbn [bq_empty fst b_size]. lia.
    + specialize (IH nx ltac:(constructor; assumption)). destruct (merge_bq nx R) as [l e]. cbn [fst snd] in IH |- *.
      cbn [app]. constructor; [exact HC| exact IH].
Qed.
#[using="Type"] Lemma merge_bq_bytes : forall R cur,
  batches_bytes (map fst (fst (merge_bq cur R))) + Q_BATCH_BYTES * Z.of_nat (length (snd (merge_bq cur R)))
  = batches_bytes (map fst (cur :: R)).
Proof.
  induction R as [|nx R IH]; intros cur; cbn [merge_bq fst snd].
  - cbn [length map]. lia.
  - destruct (b_count (fst cur) + b_count (fst nx) <=? Q_BATCH).
    + specialize (IH (bq_merge cur nx)). destruct (merge_bq (bq_merge cur nx) R) as [l e]. cbn [fst snd] in IH |- *.
      cbn [map length] in IH |- *. rewrite !batches_bytes_cons in *. cbn [bq_merge fst b_size] in IH. rewrite Nat2Z.inj_succ. lia.
    + specialize (IH nx). destruct (merge_bq nx R) as [l e]. cbn [fst snd] in IH |- *.
      cbn [map length app] in IH |- *. rewrite !batches_bytes_cons in *. lia.
Qed.
#[using="Type"] Lemma merge_bq_length : forall R cur,
  length (fst (merge_bq cur R) ++ snd (merge_bq cur R)) = length (cur :: R).
Proof.
  intros R cur. pose proof (Permutation_length (merge_bq_slots R cur)) as H. rewrite !length_map in H. exact H.
Qed.
#[using="Type"] Lemma baddr_inj : forall L x y, baddr L x = baddr L y -> bslot x = bslot y.
Proof. intros L x y E. unfold baddr, abatch_addr, aslot_addr, bslot in *. rewrite size_of_class_24 in E. lia. Qed.

#[using="Type"] Lemma batches_bytes_nonneg : forall (l : list bq),
  Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) l -> 0 <= batches_bytes (map fst l).
Proof.
  intros l HF. pose proof (batches_bytes_lb (map fst l) ltac:(rewrite Forall_map; exact HF)). unfold Q_BATCH_BYTES in *. lia.
Qed.

#[using="Type"] Lemma Forall_rot : forall (P : bq -> Prop) b G T, Forall P ((b :: G) ++ T) -> Forall P (G ++ (T ++ [b])).
Proof.
  intros P b G T H. apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall _ _) H).
  apply in_app_iff in Hx. destruct Hx as [Hx|Hx]; [right; apply in_app_iff; left; exact Hx|].
  apply in_app_iff in Hx. destruct Hx as [Hx|[<-|[]]]; [right; apply in_app_iff; right; exact Hx| left; reflexivity].
Qed.
#[using="Type"] Lemma NoDup_rot : forall b G T, base.NoDup (map bslot ((b :: G) ++ T)) -> base.NoDup (map bslot (G ++ (T ++ [b]))).
Proof.
  intros b G T ND. refine (proj1 (list_relations.list.NoDup_Permutation_proper _ _ _) ND).
  apply Permutation_map. rewrite app_assoc. cbn [app]. apply (Permutation_cons_append (G ++ T) b).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition aqrec_lh : Z := 0x35b9c.      (* [comment removed for export] *)
Definition aqrec_lt : Z := 0x35b98.      (* [comment removed for export] *)
Definition aqrec_join : Z := 0x35bf8.    (* [comment removed for export] *)

Section Front.
  Variables (L : alayout) (RNG : footprint) (MIN lo : Z).
  Variables (ra gp tp xs0 xs1 a2 a3 xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variable SPP : Z.   (* [comment removed for export] *)
  Hypothesis MIN0 : 0 <= MIN < 2^63.
  Hypothesis SPP0 : ATOP + 16 <= SPP.
  Hypothesis SPP1 : SPP + 80 <= 2^47.
  Hypothesis RT : rng RNG SPP 32.
  Hypothesis RG : rng RNG AQ_GCACHE 32.

  (* [comment removed for export] *)
  Definition deq_W (tfull : bool) (B TL : Z) : list (Z * Z) :=
    ((SPP, SPP + 32) :: (AQ_GCACHE, AQ_GCACHE + 32) :: (B, B + 8) :: (if tfull then [(TL, TL + 8)] else []))%Z.

  Definition deq_body_post (tfull : bool) (B TL nxn bsz nb gl gb tn : Z) (st1 tf st2 tb cw tls tlc : word) (m : amem) : machine_state -> Prop :=
    fun ms' => exists (tb' : word) m',
      ms' = MS (mkR ra (Z_to_bv 64 SPP) gp tp (Z_to_bv 64 nxn) (Z_to_bv 64 B) (Z_to_bv 64 (gb - bsz)) xs0 xs1 (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 MIN) a2 a3
                    (Z_to_bv 64 (tn + 1)) (Z_to_bv 64 B) (Z_to_bv 64 (nb - 1)) (Z_to_bv 64 nxn) xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 aqrec_lt) fc None m' (seg_rom asegs)
      /\ munch (deq_W tfull B TL) m m'
      /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' AQ_GCACHE [C8 (Z_to_bv 64 (nb - 1)); C8 (Z_to_bv 64 nxn); C8 (Z_to_bv 64 (if nxn =? 0 then 0 else gl)); C8 (Z_to_bv 64 (gb - bsz))]
      /\ rw_cells asegs m' B [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 bsz); C8 cw]
      /\ rw_cells asegs m' SPP [C8 st1; C8 (if tfull then tf else Z_to_bv 64 B); C8 st2; C8 tb']
      /\ (if tfull then rw_cells asegs m' TL [C8 (Z_to_bv 64 B); C8 tls; C8 tlc] else True).

  Definition deq_body_spec__stmt : Prop := forall (tfull : bool) (B TL nxn bsz nb gl gb tn : Z) (st1 tf st2 tb cw tlx tls tlc a7 t1 t2 : word) (m : amem),
    mem_inv asegs m ->
    rw_cells asegs m AQ_GCACHE [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 gl); C8 (Z_to_bv 64 gb)] ->
    rw_cells asegs m B [C8 (Z_to_bv 64 nxn); C8 (Z_to_bv 64 bsz); C8 cw] ->
    rw_cells asegs m SPP [C8 st1; C8 tf; C8 st2; C8 tb] ->
    (if tfull then rw_cells asegs m TL [C8 tlx; C8 tls; C8 tlc] /\ 0 < tn /\ AIMG_HI <= TL /\ TL + Q_BATCH_BYTES <= ATOP /\ (B + Q_BATCH_BYTES <= TL \/ TL + Q_BATCH_BYTES <= B)
               /\ rng RNG TL Q_BATCH_BYTES
     else tn = 0) ->
    0 < nb < 2^63 -> 0 <= nxn < 2^64 -> 0 <= gl < 2^64 -> 0 <= bsz <= gb -> gb < 2^63 -> 0 <= tn < 2^62 ->
    AIMG_HI <= B -> B + Q_BATCH_BYTES <= ATOP -> rng RNG B Q_BATCH_BYTES ->
    evtF asegs RNG (deq_body_post tfull B TL nxn bsz nb gl gb tn st1 tf st2 tb cw tls tlc m)
      (MS (mkR ra (Z_to_bv 64 SPP) gp tp (Z_to_bv 64 B) t1 t2 xs0 xs1 (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 MIN) a2 a3
               (Z_to_bv 64 tn) (Z_to_bv 64 TL) (Z_to_bv 64 nb) a7 xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 aqrec_lh) fc None m (seg_rom asegs)).
  Section Zd1.   (* [comment removed for export] *)
  Variable tfull : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 0).
  Variable B : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 1).
  Variable TL : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 2).
  Variable nxn : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 3).
  Variable bsz : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 4).
  Variable nb : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 5).
  Variable gl : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 6).
  Variable gb : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 7).
  Variable tn : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 8).
  Variable st1 : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 9).
  Variable tf : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 10).
  Variable st2 : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 11).
  Variable tb : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 12).
  Variable cw : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 13).
  Variable tlx : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 14).
  Variable tls : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 15).
  Variable tlc : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 16).
  Variable a7 : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 17).
  Variable t1 : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 18).
  Variable t2 : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 19).
  Variable m : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 20).
  #[using="SPP0 RT RG"] Lemma deq_body_spec__body : ltac:(let T := type of (fun (h : deq_body_spec__stmt) => h tfull B TL nxn bsz nb gl gb tn st1 tf st2 tb cw tlx tls tlc a7 t1 t2 m) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
  Proof.
    pose proof (fun (_ : True) => (tfull, (B, (TL, (nxn, (bsz, (nb, (gl, (gb, (tn, (st1, (tf, (st2, (tb, (cw, (tlx, (tls, (tlc, (a7, (t1, (t2, m))))))))))))))))))))) as _.
 intros MI GC BC TM TF NB NXN GL BSZ GB TN B0 B1 RB.
    unfold aqrec_lh, AIMG_HI, Q_BATCH_BYTES, AQ_GCACHE, AQUAR_Q in *.
    destruct tfull.
    - (nd_pre TF 6%nat; intros TLC TN1 TL0 TL1 DBT RTL; nd_post).
      pose proof (munch_refl (deq_W true B TL) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold deq_W, AQ_GCACHE in MU.
      (* [comment removed for export] *)
      assert (CONT : forall m1, mem_inv asegs m1 -> munch [(SPP, SPP + 32); (0xab310, 0xab310 + 32); (B, B + 8); (TL, TL + 8)]%Z m m1 -> wmono asegs m m1 ->
        rw_cells asegs m1 0xab310 [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 nxn); C8 (Z_to_bv 64 (if nxn =? 0 then 0 else gl)); C8 (Z_to_bv 64 gb)] ->
        rw_cells asegs m1 B [C8 (Z_to_bv 64 nxn); C8 (Z_to_bv 64 bsz); C8 cw] ->
        rw_cells asegs m1 SPP [C8 st1; C8 tf; C8 st2; C8 tb] ->
        rw_cells asegs m1 TL [C8 tlx; C8 tls; C8 tlc] ->
        evtF asegs RNG (deq_body_post true B TL nxn bsz nb gl gb tn st1 tf st2 tb cw tls tlc m)
          (MS (mkR ra (Z_to_bv 64 SPP) gp tp (Z_to_bv 64 B) t1 t2 xs0 xs1 (Z_to_bv 64 0xab270) (Z_to_bv 64 MIN) a2 a3
                   (Z_to_bv 64 tn) (Z_to_bv 64 TL) (Z_to_bv 64 nb) (Z_to_bv 64 nxn) xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x35bb0) fc None m1 (seg_rom asegs))).
      { clear MI MU WM GC BC TM TLC. intros m1 MI MU WM GC BC TM TLC.
        zstep. step.                                     (* [comment removed for export] *)
        step. step. zstep. step.                         (* [comment removed for export] *)
        zstep. step.                                     (* [comment removed for export] *)
        step. if_cases K2; zify_cond K2; [| exfalso; rewrite ?unsigned_lit in K2 by lia; lia].   (* [comment removed for export] *)
        step.                                            (* [comment removed for export] *)
        step. step. step. step.                          (* [comment removed for export] *)
        step. zstep. zstep. zstep.                       (* [comment removed for export] *)
        replace (nb + -1) with (nb - 1) in * by lia.
        apply evtF_done. unfold deq_body_post, aqrec_lt, deq_W, AQ_GCACHE, AQUAR_Q. finish. all: eassumption. }
      step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].   (* [comment removed for export] *)
      step. step.                                        (* [comment removed for export] *)
      step. if_cases K1; zify_cond K1.                   (* [comment removed for export] *)
      + rewrite ?unsigned_lit in K1 by lia. eapply CONT; try eassumption. replace (nxn =? 0) with false by (symmetry; apply Z.eqb_neq; lia). exact GC.
      + rewrite ?unsigned_lit in K1 by lia. step.        (* [comment removed for export] *)
        eapply CONT; try eassumption. replace (nxn =? 0) with true by (symmetry; apply Z.eqb_eq; lia). exact GC.
    - pose proof TF as TN1. clear TF. subst tn.
      pose proof (munch_refl (deq_W false B TL) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold deq_W, AQ_GCACHE in MU.
      assert (CONT : forall m1, mem_inv asegs m1 -> munch [(SPP, SPP + 32); (0xab310, 0xab310 + 32); (B, B + 8)]%Z m m1 -> wmono asegs m m1 ->
        rw_cells asegs m1 0xab310 [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 nxn); C8 (Z_to_bv 64 (if nxn =? 0 then 0 else gl)); C8 (Z_to_bv 64 gb)] ->
        rw_cells asegs m1 B [C8 (Z_to_bv 64 nxn); C8 (Z_to_bv 64 bsz); C8 cw] ->
        rw_cells asegs m1 SPP [C8 st1; C8 tf; C8 st2; C8 tb] ->
        evtF asegs RNG (deq_body_post false B TL nxn bsz nb gl gb 0 st1 tf st2 tb cw tls tlc m)
          (MS (mkR ra (Z_to_bv 64 SPP) gp tp (Z_to_bv 64 B) t1 t2 xs0 xs1 (Z_to_bv 64 0xab270) (Z_to_bv 64 MIN) a2 a3
                   (Z_to_bv 64 0) (Z_to_bv 64 TL) (Z_to_bv 64 nb) (Z_to_bv 64 nxn) xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x35bb0) fc None m1 (seg_rom asegs))).
      { clear MI MU WM GC BC TM. intros m1 MI MU WM GC BC TM.
        zstep. step.                                     (* [comment removed for export] *)
        step. step. zstep. step.                         (* [comment removed for export] *)
        zstep. step.                                     (* [comment removed for export] *)
        step. if_lit.                                    (* [comment removed for export] *)
        step.                                            (* [comment removed for export] *)
        step. step.                                      (* [comment removed for export] *)
        step. step. step. step.                          (* [comment removed for export] *)
        step. zstep. zstep. zstep.                       (* [comment removed for export] *)
        replace (nb + -1) with (nb - 1) in * by lia.
        apply evtF_done. unfold deq_body_post, aqrec_lt, deq_W, AQ_GCACHE, AQUAR_Q. finish. all: try eassumption. all: try exact I. }
      step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].   (* [comment removed for export] *)
      step. step.                                        (* [comment removed for export] *)
      step. if_cases K1; zify_cond K1.                   (* [comment removed for export] *)
      + rewrite ?unsigned_lit in K1 by lia. eapply CONT; try eassumption. replace (nxn =? 0) with false by (symmetry; apply Z.eqb_neq; lia). exact GC.
      + rewrite ?unsigned_lit in K1 by lia. step.        (* [comment removed for export] *)
        eapply CONT; try eassumption. replace (nxn =? 0) with true by (symmetry; apply Z.eqb_eq; lia). exact GC.
  Qed.
  End Zd1.
  #[using="SPP0 RT RG"] Lemma deq_body_spec : ltac:(let t := eval cbv delta [deq_body_spec__stmt] in deq_body_spec__stmt in exact t).
  Proof. exact deq_body_spec__body. Qed.

  (* [comment removed for export] *)
  Definition WL (G T : list bq) : list (Z * Z) :=
    ([(SPP, SPP + 32); (AQ_GCACHE, AQ_GCACHE + 32)] ++ map (fun x => (baddr L x, baddr L x + Q_BATCH_BYTES)) (G ++ T))%Z.

  Definition deq_loop_post (G T : list bq) (m : amem) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a4 a5 a6 a7 tb' : word) m',
      let '(taken, rest, bytes2) := deq_bq G (batches_bytes (map fst G)) MIN in
      ms' = MS (mkR ra (Z_to_bv 64 SPP) gp tp t0 t1 t2 xs0 xs1 (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 MIN) a2 a3 a4 a5 a6 a7 xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 aqrec_join) fc None m' (seg_rom asegs)
      /\ munch (WL G T) m m'
      /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' AQ_GCACHE [C8 (Z_to_bv 64 (Z.of_nat (length rest))); C8 (Z_to_bv 64 (tfirst L rest 0)); C8 (Z_to_bv 64 (tlast L rest 0)); C8 (Z_to_bv 64 bytes2)]
      /\ chain L m' rest 0
      /\ rw_cells asegs m' SPP [C8 (Z_to_bv 64 (Z.of_nat (length (T ++ taken)))); C8 (Z_to_bv 64 (tfirst L (T ++ taken) 0)); C8 (Z_to_bv 64 (tlast L (T ++ taken) 0)); C8 tb']
      /\ chain L m' (T ++ taken) 0
      /\ bytes2 = batches_bytes (map fst rest) /\ bytes2 <= MIN.

  #[using="rc"] Lemma deq_bq_go : forall (b : bq) l bytes mn, mn < bytes ->
    deq_bq (b :: l) bytes mn = (let '(taken, rest, bytes') := deq_bq l (bytes - b_size (fst b)) mn in (b :: taken, rest, bytes')).
  Proof. intros b l bytes mn H. cbn [deq_bq]. destruct (Z.ltb_spec mn bytes); [reflexivity| lia]. Qed.
  #[using="rc"] Lemma deq_bq_stop : forall l bytes mn, ~ mn < bytes -> deq_bq l bytes mn = ([], l, bytes).
  Proof. intros [|b l] bytes mn H; cbn [deq_bq]; [reflexivity|]. destruct (Z.ltb_spec mn bytes); [lia| reflexivity]. Qed.

  #[using="Type"] Lemma deq_bq_split : forall l bytes mn, (let '(taken, rest, _) := deq_bq l bytes mn in taken ++ rest) = l.
  Proof.
    induction l as [|b l IH]; intros bytes mn; cbn [deq_bq]; [reflexivity|].
    destruct (mn <? bytes); [| reflexivity]. specialize (IH (bytes - b_size (fst b)) mn).
    destruct (deq_bq l (bytes - b_size (fst b)) mn) as [[tk rs] b2]. cbn [app]. rewrite IH. reflexivity.
  Qed.

  #[using="Type"] Lemma bgeom_num : forall x, bgeom L AQ_GCACHE SPP x ->
    AIMG_HI <= baddr L x /\ baddr L x + Q_BATCH_BYTES <= ATOP /\ (AQ_GCACHE + 32 <= baddr L x \/ baddr L x + Q_BATCH_BYTES <= AQ_GCACHE)
    /\ (SPP + 32 <= baddr L x \/ baddr L x + Q_BATCH_BYTES <= SPP).
  Proof. intros x H. exact H. Qed.

  #[using="Type"] Lemma tfirst_range : forall X, Forall (bgeom L AQ_GCACHE SPP) X -> 0 <= tfirst L X 0 < 2^64 /\ (X <> [] -> AIMG_HI <= tfirst L X 0).
  Proof.
    intros [|x X] HF; cbn [tfirst]; [split; [lia| congruence]|].
    (pose proof (Forall_inv HF) as ndP__; nd_pre ndP__ 3%nat; intros A B _; nd_post). unfold AIMG_HI, Q_BATCH_BYTES in *. split; [lia| intros _; exact A].
  Qed.
  #[using="Type"] Lemma tlast_range : forall X, Forall (bgeom L AQ_GCACHE SPP) X -> 0 <= tlast L X 0 < 2^64.
  Proof.
    intros X HF. destruct X as [|x X']; [cbn; lia|].
    (nd_pre (tlast_in L (x :: X') 0 ltac:(congruence)) 3%nat; intros z Hz ndR1__; nd_post; revert ndR1__; intros ->).
    (pose proof (proj1 (Forall_forall _ _) HF z Hz) as ndP__; nd_pre ndP__ 3%nat; intros A B _; nd_post). unfold AIMG_HI, Q_BATCH_BYTES in *. lia.
  Qed.

  #[using="MIN0 SPP0 RT RG"] Lemma deq_loop_spec : forall (d : nat) (G T : list bq) (st1 st2 tb a7 t1 t2 : word) (m : amem),
    d = length G ->
    MIN < batches_bytes (map fst G) ->
    mem_inv asegs m ->
    rw_cells asegs m AQ_GCACHE [C8 (Z_to_bv 64 (Z.of_nat (length G))); C8 (Z_to_bv 64 (tfirst L G 0)); C8 (Z_to_bv 64 (tlast L G 0)); C8 (Z_to_bv 64 (batches_bytes (map fst G)))] ->
    chain L m G 0 ->
    rw_cells asegs m SPP [C8 st1; C8 (Z_to_bv 64 (tfirst L T 0)); C8 st2; C8 tb] ->
    chain L m T 0 ->
    Forall (bgeom L AQ_GCACHE SPP) (G ++ T) -> Forall (fun x => 0 <= bslot x) (G ++ T) -> base.NoDup (map bslot (G ++ T)) ->
    Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) G -> batches_bytes (map fst G) < 2^56 ->
    Z.of_nat (length (G ++ T)) < 2^40 ->
    Forall (fun x => rng RNG (baddr L x) Q_BATCH_BYTES) (G ++ T) ->
    evtF asegs RNG (deq_loop_post G T m)
      (MS (mkR ra (Z_to_bv 64 SPP) gp tp (Z_to_bv 64 (tfirst L G 0)) t1 t2 xs0 xs1 (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 MIN) a2 a3
               (Z_to_bv 64 (Z.of_nat (length T))) (Z_to_bv 64 (tlast L T 0)) (Z_to_bv 64 (Z.of_nat (length G))) a7 xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 aqrec_lh) fc None m (seg_rom asegs)).
  Proof.
    induction d as [|d IH]; intros until m; intros HD GO MI GC CH TM CT GEO SL ND SZ SZS LEN40 RB.
    { exfalso. destruct G; [cbn in GO; clear -GO MIN0; lia| cbn in HD; lia]. }
    destruct G as [|b G']; [cbn in HD; lia|].
    (* [comment removed for export] *)
    destruct (proj1 (chain_cons L _ _ _ _) CH) as [BCELLS CHR]. clear CH.
    (nd_pre BCELLS 6%nat; intros BC EB JB BCNT BLEN BRNG; nd_post). cbn [fst snd] in BC, EB, JB, BCNT, BLEN, BRNG.
    (pose proof (bgeom_num b (Forall_inv GEO)) as ndP__; nd_pre ndP__ 4%nat; intros GB1 GB2 GB3 GB4; nd_post).
    pose proof (Forall_inv RB) as RBb. cbv beta in RBb.
    pose proof (Forall_inv SZ) as SZb. cbv beta in SZb.
    assert (GEO' : Forall (bgeom L AQ_GCACHE SPP) G') by (apply Forall_app in GEO as [GEO _]; exact (Forall_inv_tail GEO)).
    assert (GEOT : Forall (bgeom L AQ_GCACHE SPP) T) by (apply Forall_app in GEO as [_ GEO]; exact GEO).
    pose proof (tfirst_range G' GEO') as [NXN NXP]. pose proof (tlast_range (b :: G') ltac:(apply Forall_app in GEO as [GEO _]; exact GEO)) as GL.
    pose proof (batches_bytes_nonneg G' (Forall_inv_tail SZ)) as SZR.
    cbn [map] in SZS, GO. rewrite !batches_bytes_cons in SZS, GO.
    assert (LENG : 0 < Z.of_nat (length (b :: G')) < 2^40 /\ 0 <= Z.of_nat (length T) < 2^40).
    { revert LEN40. clear. rewrite length_app. cbn [length]. intros. lia. }
    unfold AIMG_HI, Q_BATCH_BYTES, AQ_GCACHE in GB1, GB2, GB3, GB4.
    fold (baddr L b) in BC, EB, JB. set (B := baddr L b) in *.
    cbn [tfirst] in GC |- *. fold B in GC. fold B.
    (* [comment removed for export] *)
    assert (E1 : Z.of_nat (length (b :: G')) - 1 = Z.of_nat (length G')) by (clear; cbn [length]; lia).
    assert (E2 : (if tfirst L G' 0 =? 0 then 0 else tlast L (b :: G') 0) = tlast L G' 0).
    { destruct G' as [|c G'']; [reflexivity|]. specialize (NXP ltac:(congruence)). unfold AIMG_HI in NXP.
      destruct (Z.eqb_spec (tfirst L (c :: G'') 0) 0); [exfalso; clear -NXP e; lia|]. rewrite tlast_cons_ne by congruence. reflexivity. }
    assert (E3 : b_size (fst b) + batches_bytes (map fst G') - b_size (fst b) = batches_bytes (map fst G')) by (clear; lia).
    assert (E3' : batches_bytes (map fst (b :: G')) - b_size (fst b) = batches_bytes (map fst G')) by (clear; cbn [map]; rewrite batches_bytes_cons; lia).
    atop_facts. unfold AQ_GCACHE, AQUAR_Q in *.
    (* [comment removed for export] *)
    assert (OTH : forall x, In x (G' ++ T) -> bslot x <> bslot b /\ 0 <= bslot x /\ bgeom L AQ_GCACHE SPP x).
    { intros x Hx. split; [| split].
      - apply (nodup_mid bslot [] b (G' ++ T) ND x Hx).
      - eapply (proj1 (Forall_forall _ _) SL). right. exact Hx.
      - eapply (proj1 (Forall_forall _ _) GEO). right. exact Hx. }
    assert (SLb : 0 <= bslot b) by (eapply (proj1 (Forall_forall _ _) SL); left; reflexivity).
    assert (DJB : forall x, In x (G' ++ T) -> baddr L x + 8192 <= B \/ B + 8192 <= baddr L x).
    { intros x Hx. (nd_pre (OTH x Hx) 3%nat; intros N1 S1 _; nd_post). pose proof (baddr_disj L x b N1 S1 SLb) as D. unfold Q_BATCH_BYTES in D. exact D. }
    destruct (list_eq_dec bq_eq_dec T []) as [TNIL|TNE].
    - (* [comment removed for export] *)
      subst T. cbn [tfirst tlast map List.last length Z.of_nat] in TM |- *.
      eapply evtF_cut.
      { eapply (deq_body_spec false B 0 (tfirst L G' 0) (b_size (fst b)) (Z.of_nat (length (b :: G'))) (tlast L (b :: G') 0)
                  (b_size (fst b) + batches_bytes (map fst G')) 0 st1 (Z_to_bv 64 0) st2 tb (Z_to_bv 64 (b_count (fst b))) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)).
        1: exact MI. 1: exact GC. 1: exact BC. 1: exact TM. 1: reflexivity. 9: exact RBb.
        all: clear -GB1 GB2 GB3 GB4 NXN GL SZb SZR SZS LENG BRNG; unfold AIMG_HI, Q_BATCH_BYTES, Q_BATCH in *; lia. }
      cbv beta. intros ms1 (tb' & m1 & -> & MUc & WMc & MI1 & GC1 & BC1 & TM1 & _). clear MI.
      rewrite E1, E2, E3 in GC1. unfold deq_W, AQ_GCACHE in MUc. unfold AQ_GCACHE in GC1.
      (* [comment removed for export] *)
      assert (REB : forall mf, munch [(SPP, SPP + 32); (0xab310, 0xab310 + 32); (B, B + 8)]%Z m mf -> wmono asegs m mf ->
                rw_cells asegs mf B [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (b_size (fst b))); C8 (Z_to_bv 64 (b_count (fst b)))] ->
                chain L mf G' 0 /\ chain L mf [b] 0).
      { intros mf MUf WMf BCf. split.
        - eapply chain_frame; [exact CHR| exact MUf| exact WMf|]. apply Forall_forall. intros x Hx.
          (nd_pre (OTH x ltac:(apply in_app_iff; left; exact Hx)) 3%nat; intros _ _ Gx; nd_post). apply bgeom_num in Gx. specialize (DJB x ltac:(apply in_app_iff; left; exact Hx)).
          unfold AIMG_HI, Q_BATCH_BYTES, AQ_GCACHE in *. cbn. clear -Gx DJB. lia.
        - pose proof EB as EBf. xport EBf MUf WMf ltac:(clear -BRNG BCNT BLEN GB3 GB4; rewrite length_map, qhdrs_length by exact BLEN; unfold AQ_GCACHE, Q_BATCH_BYTES, Q_BATCH in *; lia).
          destruct JB as [jb JBf]. xport JBf MUf WMf ltac:(clear -BRNG GB3 GB4; unfold AQ_GCACHE, Q_BATCH_BYTES, Q_BATCH in *; lia).
          apply (proj2 (chain_cons L _ _ _ _)). split; [| apply chain_nil]. unfold abatch_cells. cbn [tfirst]. fold B.
          split; [exact BCf|]. split; [exact EBf|]. split; [exists jb; exact JBf|]. clear -BCNT BLEN BRNG. tauto. }
      clear BC.
      unfold aqrec_lt. step. if_cases KX; zify_cond KX.          (* [comment removed for export] *)
      + rewrite E3 in KX. rewrite ?Z.mod_small, ?unsigned_lit in KX by (clear -MIN0 SZR SZS SZb; unfold Q_BATCH_BYTES in SZb; lia).
        step. step.                                             (* [comment removed for export] *)
        apply evtF_done. unfold deq_loop_post, aqrec_join.
        rewrite deq_bq_go by exact GO. rewrite E3'. rewrite deq_bq_stop by (clear -KX; lia).
        cbn [app length Z.of_nat Pos.of_succ_nat Pos.to_nat tfirst tlast map List.last]. fold B.
        do 9 eexists. split; [reflexivity|].
        split. { eapply munch_weaken; [| exact MUc]. unfold WL, AQ_GCACHE, Q_BATCH_BYTES. rewrite app_nil_r. cbn [map app]. fold B.
                 solve_sub_fpw ltac:(clear; lia). }
        destruct (REB _ MUc WMc BC1) as [CHR1 CHB].
        split; [exact WMc|]. split; [exact MI1|].
        split; [exact GC1|]. split; [exact CHR1|]. split; [exact TM1|]. split; [exact CHB|].
        split; [reflexivity| clear -KX; lia].
      + rewrite E3 in KX. rewrite ?Z.mod_small, ?unsigned_lit in KX by (clear -MIN0 SZR SZS SZb; unfold Q_BATCH_BYTES in SZb; lia).
        destruct (REB _ MUc WMc BC1) as [CHR1 CHB].
        rewrite E1. replace (0 + 1) with (Z.of_nat (length [b])) by reflexivity.
        change (Z_to_bv 64 B) with (Z_to_bv 64 (tlast L [b] 0)) at 2.
        eapply evtF_mono.
        { eapply (IH G' [b] st1 st2 tb'); [cbn in HD; clear -HD; lia| exact KX| exact MI1| exact GC1| exact CHR1| exact TM1| exact CHB| ..].
          - exact (Forall_rot _ _ _ _ GEO).
          - exact (Forall_rot _ _ _ _ SL).
          - exact (NoDup_rot _ _ _ ND).
          - exact (Forall_inv_tail SZ).
          - clear -SZS SZb; unfold Q_BATCH_BYTES in SZb; lia.
          - revert LEN40; clear; rewrite !length_app; cbn [length]; intros; lia.
          - exact (Forall_rot _ _ _ _ RB). }
        cbv beta. unfold deq_loop_post, aqrec_join. intros ms' (y0 & y1 & y2 & y4 & y5 & y6 & y7 & tb'' & m' & POST).
        rewrite deq_bq_go by exact GO. rewrite E3'. destruct (deq_bq G' (batches_bytes (map fst G')) MIN) as [[tk rs] b2].
        (destruct POST as (-> & ndR1__); nd_pre ndR1__ 9%nat; intros MU' WM' MI' GC' CH' TM' CT' HB2 HB3; nd_post).
        cbn [app] in TM', CT' |- *.
        do 9 eexists. split; [reflexivity|].
        split. { eapply (munch_trans_w _ _ _ _ _ _ MUc MU').
                 - unfold WL, Q_BATCH_BYTES. rewrite app_nil_r. cbn [map app]. fold B. solve_sub_fpw ltac:(clear; lia).
                 - unfold WL. apply sub_fp_incl. intros iv Hiv. apply in_app_iff in Hiv. apply in_app_iff. destruct Hiv as [Hiv|Hiv]; [left; exact Hiv| right].
                   rewrite app_nil_r. rewrite map_app in Hiv. cbn [map] in Hiv |- *. apply in_app_iff in Hiv. destruct Hiv as [Hiv|[Hiv|[]]]; [right; exact Hiv| left; exact Hiv]. }
        split; [eapply wmono_trans; [exact WMc| exact WM']|]. split; [exact MI'|].
        split; [exact GC'|]. split; [exact CH'|]. split; [exact TM'|]. split; [exact CT'|]. split; [exact HB2| exact HB3].
    - (* [comment removed for export] *)
      destruct (exists_last TNE) as [T0 [tl ET]].
      pose proof CT as CT'. rewrite ET in CT'. destruct (proj1 (chain_app L _ _ _ _) CT') as [CT0 CTL]. clear CT CT'. cbn [tfirst] in CT0.
      destruct (proj1 (chain_cons L _ _ _ _) CTL) as [TLCELLS _]. clear CTL.
      (nd_pre TLCELLS 6%nat; intros TLC ETL JTL TCNT TLEN TRNG; nd_post). cbn [fst snd tfirst] in TLC, ETL, JTL, TCNT, TLEN, TRNG.
      assert (INTL : In tl (G' ++ T)) by (rewrite ET; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity).
      (nd_pre (OTH tl INTL) 3%nat; intros NTL STL GTL; nd_post). apply bgeom_num in GTL. (nd_pre GTL 4%nat; intros GT1 GT2 GT3 GT4; nd_post).
      pose proof (DJB tl INTL) as DBT.
      assert (RTL : rng RNG (baddr L tl) Q_BATCH_BYTES) by (eapply (proj1 (Forall_forall _ _) RB); right; exact INTL).
      unfold AIMG_HI, Q_BATCH_BYTES, AQ_GCACHE in GT1, GT2, GT3, GT4.
      fold (baddr L tl) in TLC, ETL, JTL. set (TL := baddr L tl) in *.
      replace (tlast L T 0) with TL by (rewrite ET, tlast_app1; reflexivity).
      assert (OTT : forall x, In x (G' ++ T0) -> bslot x <> bslot tl).
      { intros x Hx. apply (nodup_mid bslot (b :: G' ++ T0) tl [] ); [| apply in_app_iff; left; right; exact Hx].
        cbn [app]. rewrite ET in ND. cbn [app] in ND. rewrite <- app_assoc. exact ND. }
      assert (DJT : forall x, In x (G' ++ T0) -> baddr L x + 8192 <= TL \/ TL + 8192 <= baddr L x).
      { intros x Hx. assert (Hx' : In x (G' ++ T)).
        { rewrite ET. apply in_app_iff in Hx. apply in_app_iff. destruct Hx as [Hx|Hx]; [left; exact Hx| right; apply in_app_iff; left; exact Hx]. }
        (nd_pre (OTH x Hx') 3%nat; intros _ S1 _; nd_post).
        pose proof (baddr_disj L x tl (OTT x Hx) S1 STL) as D. unfold Q_BATCH_BYTES in D. exact D. }
      assert (LENT : 0 < Z.of_nat (length T)) by (rewrite ET; clear; rewrite length_app; cbn [length]; lia).
      eapply evtF_cut.
      { eapply (deq_body_spec true B TL (tfirst L G' 0) (b_size (fst b)) (Z.of_nat (length (b :: G'))) (tlast L (b :: G') 0)
                  (b_size (fst b) + batches_bytes (map fst G')) (Z.of_nat (length T)) st1 (Z_to_bv 64 (tfirst L T 0)) st2 tb
                  (Z_to_bv 64 (b_count (fst b))) (Z_to_bv 64 0) (Z_to_bv 64 (b_size (fst tl))) (Z_to_bv 64 (b_count (fst tl)))).
        1: exact MI. 1: exact GC. 1: exact BC. 1: exact TM.
        1: { split; [exact TLC|]. split; [exact LENT| split; [| split; [| split; [clear -DBT; unfold Q_BATCH_BYTES; lia| unfold Q_BATCH_BYTES; exact RTL]]]].
             - clear -GT1; unfold AIMG_HI; lia.
             - clear -GT2; unfold Q_BATCH_BYTES; lia. }
        9: exact RBb.
        all: clear -GB1 GB2 GB3 GB4 NXN GL SZb SZR SZS LENG BRNG; unfold AIMG_HI, Q_BATCH_BYTES, Q_BATCH in *; lia. }
      cbv beta. intros ms1 (tb' & m1 & -> & MUc & WMc & MI1 & GC1 & BC1 & TM1 & TLC1). clear MI.
      rewrite E1, E2, E3 in GC1. unfold deq_W, AQ_GCACHE in MUc. unfold AQ_GCACHE in GC1.
      (* [comment removed for export] *)
      assert (REB : forall mf, munch [(SPP, SPP + 32); (0xab310, 0xab310 + 32); (B, B + 8); (TL, TL + 8)]%Z m mf -> wmono asegs m mf ->
                rw_cells asegs mf B [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (b_size (fst b))); C8 (Z_to_bv 64 (b_count (fst b)))] ->
                rw_cells asegs mf TL [C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 (b_size (fst tl))); C8 (Z_to_bv 64 (b_count (fst tl)))] ->
                chain L mf G' 0 /\ chain L mf (T ++ [b]) 0).
      { intros mf MUf WMf BCf TLCf. split.
        - eapply chain_frame; [exact CHR| exact MUf| exact WMf|]. apply Forall_forall. intros x Hx.
          (nd_pre (OTH x ltac:(apply in_app_iff; left; exact Hx)) 3%nat; intros Nx Sx Gx; nd_post). apply bgeom_num in Gx. specialize (DJB x ltac:(apply in_app_iff; left; exact Hx)).
          pose proof (DJT x ltac:(apply in_app_iff; left; exact Hx)) as DxT.
          unfold AIMG_HI, Q_BATCH_BYTES, AQ_GCACHE in *. cbn. clear -Gx DJB DxT. lia.
        - pose proof EB as EBf. xport EBf MUf WMf ltac:(clear -BRNG BCNT BLEN GB3 GB4 DBT; rewrite length_map, qhdrs_length by exact BLEN; unfold AQ_GCACHE, Q_BATCH_BYTES, Q_BATCH in *; lia).
          destruct JB as [jb JBf]. xport JBf MUf WMf ltac:(clear -BRNG GB3 GB4 DBT; unfold AQ_GCACHE, Q_BATCH_BYTES, Q_BATCH in *; lia).
          pose proof ETL as ETf. xport ETf MUf WMf ltac:(clear -TRNG TCNT TLEN GT3 GT4 DBT; rewrite length_map, qhdrs_length by exact TLEN; unfold AQ_GCACHE, Q_BATCH_BYTES, Q_BATCH in *; lia).
          destruct JTL as [jt JTf]. xport JTf MUf WMf ltac:(clear -TRNG GT3 GT4 DBT; unfold AQ_GCACHE, Q_BATCH_BYTES, Q_BATCH in *; lia).
          rewrite ET. apply (proj2 (chain_app L _ _ _ _)). split.
          + apply (proj2 (chain_app L _ _ _ _)). cbn [tfirst]. fold TL. fold B. split.
            * eapply chain_frame; [exact CT0| exact MUf| exact WMf|]. apply Forall_forall. intros x Hx.
              assert (HxT : In x (G' ++ T)) by (rewrite ET; apply in_app_iff; right; apply in_app_iff; left; exact Hx).
              (nd_pre (OTH x HxT) 3%nat; intros _ _ Gx; nd_post). apply bgeom_num in Gx.
              specialize (DJB x HxT). specialize (DJT x ltac:(apply in_app_iff; right; exact Hx)).
              unfold AIMG_HI, Q_BATCH_BYTES, AQ_GCACHE in *. cbn. clear -Gx DJB DJT. lia.
            * apply (proj2 (chain_cons L _ _ _ _)). split; [| apply chain_nil]. unfold abatch_cells. cbn [tfirst fst snd]. fold TL. fold B.
              split; [exact TLCf|]. split; [exact ETf|]. split; [exists jt; exact JTf|]. clear -TCNT TLEN TRNG. tauto.
          + apply (proj2 (chain_cons L _ _ _ _)). split; [| apply chain_nil]. unfold abatch_cells. cbn [tfirst]. fold B.
            split; [exact BCf|]. split; [exact EBf|]. split; [exists jb; exact JBf|]. clear -BCNT BLEN BRNG. tauto. }
      clear BC TLC.
      assert (TF : tfirst L (T ++ [b]) 0 = tfirst L T 0) by (apply tfirst_app; exact TNE).
      assert (TLN : Z.of_nat (length (T ++ [b])) = Z.of_nat (length T) + 1) by (clear; rewrite length_app; cbn [length]; lia).
      (* [comment removed for export] *)
      assert (SUB : sub_fp [(SPP, SPP + 32); (0xab310, 0xab310 + 32); (B, B + 8); (TL, TL + 8)]%Z (WL (b :: G') T)).
      { unfold WL, Q_BATCH_BYTES, AQ_GCACHE. apply sub_fp_by_incl'.
        constructor; [apply Exists_exists; eexists; split; [left; reflexivity| cbn; clear; lia]|].
        constructor; [apply Exists_exists; eexists; split; [right; left; reflexivity| cbn; clear; lia]|].
        constructor; [apply Exists_exists; eexists; split; [right; right; apply in_map_iff; exists b; split; [reflexivity| left; reflexivity]| cbn; fold B; clear; lia]|].
        constructor; [apply Exists_exists; eexists; split; [right; right; apply in_map_iff; exists tl; split; [reflexivity| right; exact INTL]| cbn; fold TL; clear; lia]|].
        constructor. }
      unfold aqrec_lt. step. if_cases KX; zify_cond KX.          (* [comment removed for export] *)
      + rewrite E3 in KX. rewrite ?Z.mod_small, ?unsigned_lit in KX by (clear -MIN0 SZR SZS SZb; unfold Q_BATCH_BYTES in SZb; lia).
        step. step.                                             (* [comment removed for export] *)
        apply evtF_done. unfold deq_loop_post, aqrec_join.
        rewrite deq_bq_go by exact GO. rewrite E3'. rewrite deq_bq_stop by (clear -KX; lia).
        rewrite TF, TLN, tlast_app1. fold B.
        cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat tfirst tlast map List.last].
        do 9 eexists. split; [reflexivity|].
        split; [eapply munch_weaken; [exact SUB| exact MUc]|].
        destruct (REB _ MUc WMc BC1 TLC1) as [CHR1 CHB].
        split; [exact WMc|]. split; [exact MI1|].
        split; [exact GC1|]. split; [exact CHR1|]. split; [exact TM1|]. split; [exact CHB|].
        split; [reflexivity| clear -KX; lia].
      + rewrite E3 in KX. rewrite ?Z.mod_small, ?unsigned_lit in KX by (clear -MIN0 SZR SZS SZb; unfold Q_BATCH_BYTES in SZb; lia).
        destruct (REB _ MUc WMc BC1 TLC1) as [CHR1 CHB].
        rewrite E1. rewrite <- TLN. rewrite <- TF in TM1.
        replace (Z_to_bv 64 B) with (Z_to_bv 64 (tlast L (T ++ [b]) 0)) by (rewrite tlast_app1; reflexivity).
        eapply evtF_mono.
        { eapply (IH G' (T ++ [b]) st1 st2 tb'); [cbn in HD; clear -HD; lia| exact KX| exact MI1| exact GC1| exact CHR1| exact TM1| exact CHB| ..].
          - exact (Forall_rot _ _ _ _ GEO).
          - exact (Forall_rot _ _ _ _ SL).
          - exact (NoDup_rot _ _ _ ND).
          - exact (Forall_inv_tail SZ).
          - clear -SZS SZb; unfold Q_BATCH_BYTES in SZb; lia.
          - revert LEN40; clear; rewrite !length_app; cbn [length]; intros; lia.
          - exact (Forall_rot _ _ _ _ RB). }
        cbv beta. unfold deq_loop_post, aqrec_join. intros ms' (y0 & y1 & y2 & y4 & y5 & y6 & y7 & tb'' & m' & POST).
        rewrite deq_bq_go by exact GO. rewrite E3'. destruct (deq_bq G' (batches_bytes (map fst G')) MIN) as [[tk rs] b2].
        (destruct POST as (-> & ndR1__); nd_pre ndR1__ 9%nat; intros MU' WM' MI' GC' CH' TM' CT' HB2 HB3; nd_post).
        rewrite <- app_assoc in TM', CT'. cbn [app] in TM', CT'.
        do 9 eexists. split; [reflexivity|].
        split. { eapply (munch_trans_w _ _ _ _ _ _ MUc MU'); [exact SUB|].
                 unfold WL. apply sub_fp_incl. intros iv Hiv. apply in_app_iff in Hiv. apply in_app_iff. destruct Hiv as [Hiv|Hiv]; [left; exact Hiv| right].
                 rewrite !map_app in Hiv. rewrite map_app. cbn [map] in Hiv |- *. apply in_app_iff in Hiv. rewrite in_app_iff.
                 destruct Hiv as [Hiv|Hiv]; [left; right; exact Hiv|]. apply in_app_iff in Hiv. destruct Hiv as [Hiv|[Hiv|[]]]; [right; exact Hiv| left; left; exact Hiv]. }
        split; [eapply wmono_trans; [exact WMc| exact WM']|]. split; [exact MI'|].
        split; [exact GC'|]. split; [exact CH'|]. split; [exact TM'|]. split; [exact CT'|]. split; [exact HB2| exact HB3].
  Qed.
End Front.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma disj_objs_below : forall L LST TMP Y A n, Forall (bgeom L LST TMP) Y -> A + n <= AIMG_HI ->
  disjoint_from (map (fun x => (baddr L x, baddr L x + Q_BATCH_BYTES)) Y) A n.
Proof.
  intros L LST TMP Y A n HF HA. apply disjoint_from_Forall. apply Forall_map. eapply Forall_impl; [| exact HF].
  intros x (G1 & G2 & _). cbn [fst snd]. right. unfold AIMG_HI, Q_BATCH_BYTES in *. lia.
Qed.

#[using="Type"] Lemma bgeom_baddr : forall L LST TMP x y, baddr L y = baddr L x -> bgeom L LST TMP y -> bgeom L LST TMP x.
Proof. intros L LST TMP x y E H. unfold bgeom in *. rewrite <- E. exact H. Qed.

(* [comment removed for export] *)
Definition WQ (L : alayout) (sp : Z) (X : list bq) : list (Z * Z) :=
  ((sp - 96, sp) :: (AQ_MUTEX, AQ_MUTEX + 4) :: (AQ_GCACHE, AQ_GCACHE + 32) :: map (fun x => (baddr L x, baddr L x + Q_BATCH_BYTES)) X)%Z.

Definition qrec_front__stmt : Prop := qrec_front_stmt.
Section Zd2.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'qrec_front__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'qrec_front__stmt 1).
Variable X : ltac2:(SecDietF.SzSecF.ty 'qrec_front__stmt 2).
Variable bytes : ltac2:(SecDietF.SzSecF.ty 'qrec_front__stmt 3).
Variable min_size : ltac2:(SecDietF.SzSecF.ty 'qrec_front__stmt 4).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'qrec_front__stmt 5).
#[using="Type"] Lemma qrec_front__body : ltac:(let T := type of (fun (h : qrec_front__stmt) => h L RNG X bytes min_size lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (X, (bytes, (min_size, lo)))))) as _.
 intros until m.
  intros ST CEIL LO SP47 MI -> -> MIN0 MX GC CH GEO SL ND SZ BY BY56 LEN40 RIMG RTLS RSTK RB.
  atop_facts. unfold AQUAR_Q, AQ_MUTEX, AQ_GCACHE in *.
  word_range sp SPR.
  pose proof (batches_bytes_lb (map fst X) ltac:(rewrite Forall_map; exact SZ)) as BYLB. rewrite length_map, <- BY in BYLB. unfold Q_BATCH_BYTES in BYLB.
  change (@length (abatch * qbatchc) X) with (@length bq X) in BYLB.
  assert (RT : rng RNG (bv_unsigned sp + -80) 32) by (eapply (rng_sub _ _ _ _ _ RSTK); clear -LO SPR; lia).
  assert (RG : rng RNG 0xab310 32) by (eapply (rng_sub _ _ _ _ _ RIMG); clear; lia).
  assert (RMX : rng RNG 0xab308 4) by (eapply (rng_sub _ _ _ _ _ RIMG); clear; lia).
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (0xab308, 0xab308 + 4); (0xab310, 0xab310 + 32)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  assert (CONT2 : forall (m2 : amem) (rest T : list bq) (bytes2 : Z) (tb' rax t0 t1 t2 xs0 xs1 xs2 xs3 xs4 a4 a5 a6 a7 u3 u4 u5 u6 : word),
    qrec_fun X bytes min_size = (rest, T, bytes2) ->
    mem_inv asegs m2 -> boxed (munch (WQ L (bv_unsigned sp) X) m m2) -> wmono asegs m m2 -> stk asegs m2 lo (bv_unsigned sp + -80) ->
    rw_cells asegs m2 0xab308 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
    rw_cells asegs m2 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m2 (bv_unsigned sp + -80) [C8 (Z_to_bv 64 (Z.of_nat (length T))); C8 (Z_to_bv 64 (tfirst L T 0)); C8 (Z_to_bv 64 (tlast L T 0)); C8 tb'] ->
    rw_cells asegs m2 0xab310 [C8 (Z_to_bv 64 (Z.of_nat (length rest))); C8 (Z_to_bv 64 (tfirst L rest 0)); C8 (Z_to_bv 64 (tlast L rest 0)); C8 (Z_to_bv 64 bytes2)] ->
    chain L m2 rest 0 -> chain L m2 T 0 -> bytes2 = batches_bytes (map fst rest) -> bytes2 <= min_size ->
    Forall (bgeom L 0xab310 (bv_unsigned sp + -80)) (rest ++ T) ->
    evtF asegs RNG (qrec_front_post L X bytes min_size lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 F fc m)
      (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 xs0 xs1 (Z_to_bv 64 0xab270) (Z_to_bv 64 min_size) a2 a3 a4 a5 a6 a7
               xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6) F (Z_to_bv 64 aqrec_join) fc None m2 (seg_rom asegs))).
  { clear MI MU WM ST MX GC CH. intros m2 rest T bytes2 tb' rax x1 y1 y2 xs0 xs1 xs2 xs3 xs4 y4 y5 y6 y7 u3 u4 u5 u6 QF MI MUP WM ST MX FRS TM GC CHR CT HB2 HB3 GEO2.
    pose proof (munch_refl [(0xab308, 0xab308 + 4)]%Z m2) as MU.
    pose proof (wmono_refl asegs m2) as WM2.
    unfold aqrec_join.
    step.                                      (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    zstep. step.                               (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mf _) =>
      assert (CHR' : chain L mf rest 0) by (eapply chain_frame; [exact CHR| exact MU| exact WM2|]; apply Forall_forall; intros x Hx;
        pose proof (proj1 (Forall_forall _ _) GEO2 x ltac:(apply in_app_iff; left; exact Hx)) as (Gx & _); unfold AIMG_HI in Gx; cbn; clear -Gx; lia);
      assert (CT' : chain L mf T 0) by (eapply chain_frame; [exact CT| exact MU| exact WM2|]; apply Forall_forall; intros x Hx;
        pose proof (proj1 (Forall_forall _ _) GEO2 x ltac:(apply in_app_iff; right; exact Hx)) as (Gx & _); unfold AIMG_HI in Gx; cbn; clear -Gx; lia)
    end.
    apply evtF_done. unfold qrec_front_post. rewrite QF. unbox MUP.
    do 19 eexists. split; [reflexivity|].
    split; [eapply (munch_trans_w _ _ _ _ _ _ MUP MU); [intros z Hz; exact Hz| unfold WQ; solve_sub_fpw ltac:(clear; lia)]|].
    split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact TM|]. split; [exact FRS|]. split; [exact MX|].
    split; [exact GC|]. split; [exact CHR'|]. split; [exact CT'|]. split; [exact HB2| exact HB3]. }
  (* [comment removed for export] *)
  assert (CONT1 : forall (m1 : amem) (G T0 : list bq) (tb rax t0 t1 t2 xs0 xs1 xs2 xs3 xs4 a4 a5 a7 u3 u4 u5 u6 : word),
    (if qrec_mergeb (Z.of_nat (length X)) bytes then amerge_fun X else (X, [])) = (G, T0) ->
    bytes - Q_BATCH_BYTES * Z.of_nat (length T0) = batches_bytes (map fst G) ->
    mem_inv asegs m1 -> boxed (munch (WQ L (bv_unsigned sp) X) m m1) -> wmono asegs m m1 -> stk asegs m1 lo (bv_unsigned sp + -80) ->
    rw_cells asegs m1 0xab308 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
    rw_cells asegs m1 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m1 (bv_unsigned sp + -80) [C8 (Z_to_bv 64 (Z.of_nat (length T0))); C8 (Z_to_bv 64 (tfirst L T0 0)); C8 (Z_to_bv 64 (tlast L T0 0)); C8 tb] ->
    rw_cells asegs m1 0xab310 [C8 (Z_to_bv 64 (Z.of_nat (length G))); C8 (Z_to_bv 64 (tfirst L G 0)); C8 (Z_to_bv 64 (tlast L G 0)); C8 (Z_to_bv 64 (batches_bytes (map fst G)))] ->
    chain L m1 G 0 -> chain L m1 T0 0 ->
    Forall (bgeom L 0xab310 (bv_unsigned sp + -80)) (G ++ T0) -> Forall (fun x => 0 <= bslot x) (G ++ T0) -> base.NoDup (map bslot (G ++ T0)) ->
    Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) G -> batches_bytes (map fst G) < 2^56 -> Z.of_nat (length (G ++ T0)) < 2^40 ->
    Forall (fun x => rng RNG (baddr L x) Q_BATCH_BYTES) (G ++ T0) ->
    (forall x, In x (G ++ T0) -> exists y, In y X /\ baddr L y = baddr L x) ->
    evtF asegs RNG (qrec_front_post L X bytes min_size lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 F fc m)
      (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 xs0 xs1 (Z_to_bv 64 0xab270) (Z_to_bv 64 min_size) a2 a3 a4 a5
               (Z_to_bv 64 (Z.of_nat (length G))) a7 xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6) F (Z_to_bv 64 0x35b5c) fc None m1 (seg_rom asegs))).
  { clear MI MU WM ST MX GC CH. intros m1 G T0 tb rax x1 y1 y2 xs0 xs1 xs2 xs3 xs4 y4 y5 y7 u3 u4 u5 u6 QF HBY MI MUP WM ST MX FRS TM GC CHR CT GEO1 SL1 ND1 SZ1 SZS1 LEN1 RB1 INX.
    pose proof (batches_bytes_nonneg G SZ1) as GB0.
    pose proof (tfirst_range L (bv_unsigned sp + -80) G ltac:(apply Forall_app in GEO1 as [G1 _]; exact G1)) as [TF0 _].
    pose proof (tlast_range L (bv_unsigned sp + -80) T0 ltac:(apply Forall_app in GEO1 as [_ G1]; exact G1)) as TL0.
    assert (LENS : 0 <= Z.of_nat (length G) < 2^40 /\ 0 <= Z.of_nat (length T0) < 2^40) by (revert LEN1; clear; rewrite length_app; intros; lia).
    step. step. step.                          (* [comment removed for export] *)
    step. if_cases KL; zify_cond KL.           (* [comment removed for export] *)
    - rewrite ?Z.mod_small, ?unsigned_lit in KL by (clear -MIN0 GB0 SZS1; lia).
      eapply (CONT2 m1 G T0 (batches_bytes (map fst G)) tb); try eassumption.
      + unfold qrec_fun. rewrite QF, HBY, deq_bq_stop by (clear -KL; lia). rewrite app_nil_r. reflexivity.
      + reflexivity.
    - rewrite ?Z.mod_small, ?unsigned_lit in KL by (clear -MIN0 GB0 SZS1; lia).
      step. step.                              (* [comment removed for export] *)
      eapply evtF_cut.
      { eapply deq_loop_spec with (d := length G) (G := G) (T := T0); [..| reflexivity| exact KL| exact MI| exact GC| exact CHR| exact TM| exact CT
          | exact GEO1| exact SL1| exact ND1| exact SZ1| exact SZS1| exact LEN1| exact RB1].
        all: try assumption. all: atop_facts; clear -CEIL LO SP47 SPR MIN0; lia. }
      cbv beta. unfold deq_loop_post. intros ms2 (z0 & z1 & z2 & z4 & z5 & z6 & z7 & tb' & m2 & POST).
      pose proof (deq_bq_split G (batches_bytes (map fst G)) min_size) as SPLIT.
      destruct (deq_bq G (batches_bytes (map fst G)) min_size) as [[tk rs] b2] eqn:DQ.
      (destruct POST as (-> & ndR1__); nd_pre ndR1__ 9%nat; intros MU' WM' MI' GC' CH' TM' CT' HB2 HB3; nd_post). clear MI.
      assert (GEO2 : Forall (bgeom L 0xab310 (bv_unsigned sp + -80)) (rs ++ T0 ++ tk)).
      { apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall _ _) GEO1). rewrite <- SPLIT. rewrite <- app_assoc. apply in_app_iff in Hx. apply in_app_iff.
        destruct Hx as [Hx|Hx]; [right; apply in_app_iff; left; exact Hx|]. apply in_app_iff in Hx. destruct Hx as [Hx|Hx]; [right; apply in_app_iff; right; exact Hx| left; exact Hx]. }
      (* [comment removed for export] *)
      xport MX MU' WM' ltac:(unfold WL, AQ_GCACHE; cbn [app disjoint_from fst snd]; split; [clear -LO CEIL; lia| split; [clear; lia| eapply disj_objs_below; [exact GEO1| unfold AIMG_HI; clear; lia]]]).
      xport FRS MU' WM' ltac:(unfold WL, AQ_GCACHE; cbn [app disjoint_from fst snd]; split; [clear; lia| split; [clear -LO CEIL; lia| eapply disj_objs_above; [exact GEO1| atop_facts; clear -LO CEIL; lia]]]).
      xport ST MU' WM' ltac:(unfold WL, AQ_GCACHE; cbn [app disjoint_from fst snd]; split; [clear; lia| split; [clear -LO CEIL; lia| eapply disj_objs_above; [exact GEO1| atop_facts; clear -LO CEIL; lia]]]).
      unbox MUP.
      eapply (CONT2 m2 rs (T0 ++ tk) b2 tb'); try eassumption.
      + unfold qrec_fun. rewrite QF, HBY, DQ. reflexivity.
      + apply Box. eapply (munch_trans_w _ _ _ _ _ _ MUP MU'); [intros z Hz; exact Hz|].
        unfold WL, WQ, AQ_GCACHE, AQ_MUTEX. cbn [app]. apply sub_fp_by_incl'.
        constructor; [apply Exists_exists; eexists; split; [left; reflexivity| cbn; clear; lia]|].
        constructor; [apply Exists_exists; eexists; split; [right; right; left; reflexivity| cbn; clear; lia]|].
        apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv. (nd_pre Hiv 2%nat; intros x ndR1__; nd_post; destruct ndR1__ as (<- & ndR2__); rename ndR2__ into Hx). (nd_pre (INX x Hx) 3%nat; intros y Hy EY; nd_post).
        apply Exists_exists. eexists. split; [right; right; right; apply in_map_iff; exists y; split; [reflexivity| exact Hy]| cbn; rewrite EY; clear; lia].
      + eapply wmono_trans; [exact WM| exact WM']. }
  (* [comment removed for export] *)
  carve_frame 80%nat ST.
  do 7 step.                                   (* [comment removed for export] *)
  do 4 step.                                   (* [comment removed for export] *)
  zstep. step. zstep. step.                    (* [comment removed for export] *)
  apply (rw_C1x4_to_C4 _ _ 0 1 ltac:(lia) ltac:(lia)) in MX. change (0 + 256 * 1) with 256 in MX.
  amo_step. lits.                              (* [comment removed for export] *)
  do 4 zstep.                                  (* [comment removed for export] *)
  amo_step.                                    (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  zstep. step. if_lit.                         (* [comment removed for export] *)
  apply (rw_C4_to_C1x4 _ _ 1 1 ltac:(lia) ltac:(lia)) in MX.
  step. step. zstep.                           (* [comment removed for export] *)
  setreg 14%Z (Z_to_bv 64 (8192 * Z.of_nat (length X))) ltac:(rewrite ?Z.shiftl_mul_pow2 by (clear; lia); try apply Z_to_bv_eqm; clear -LEN40; Z.div_mod_to_equations; lia).
  step. if_cases KC; zify_cond KC.             (* [comment removed for export] *)
  { exfalso. rewrite ?Z.mod_small, ?unsigned_lit in KC by (clear -BY56 BYLB LEN40; lia). clear -KC BYLB. lia. }
  clear KC.
  (* [comment removed for export] *)
  apply (proj1 (rw_cells_app asegs _ _ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])) in FR.
  destruct FR as [TM FRS].
  lazymatch type of FRS with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + -48) in FRS by (cbn; clear; lia) end.
  (* [comment removed for export] *)
  assert (SL' : Forall (fun x => 0 <= bslot x) (X ++ [])) by (rewrite app_nil_r; exact SL).
  assert (INX0 : forall x, In x (X ++ []) -> exists y, In y X /\ baddr L y = baddr L x) by (intros x Hx; rewrite app_nil_r in Hx; exists x; split; [exact Hx| reflexivity]).
  step. if_cases KM1; zify_cond KM1.           (* [comment removed for export] *)
  - rewrite ?Z.mod_small, ?unsigned_lit in KM1 by (clear -BY56 BYLB LEN40; lia).
    eapply (CONT1 _ X [] (Z_to_bv 64 0)); try eassumption.
    + unfold qrec_mergeb, Q_BATCH_BYTES. destruct (Z.ltb_spec (8192 * Z.of_nat (length X)) bytes) as [Hl|Hl]; [exfalso; clear -KM1 Hl; lia|]. reflexivity.
    + cbn [length]. rewrite <- BY. clear; lia.
    + apply Box. eapply munch_weaken; [| exact MU]. unfold WQ, AQ_MUTEX, AQ_GCACHE. solve_sub_fpw ltac:(clear; lia).
    + rewrite <- BY. exact GC.
    + eapply chain_frame; [exact CH| exact MU| exact WM|]. apply Forall_forall. intros x Hx.
      (pose proof (proj1 (Forall_forall _ _) GEO x Hx) as ndP__; nd_pre ndP__ 4%nat; intros G1 G2 G3 G4; nd_post). unfold AIMG_HI, Q_BATCH_BYTES in *. cbn. clear -G1 G2 G3 CEIL LO. lia.
    + apply chain_nil.
    + rewrite app_nil_r. exact GEO.
    + rewrite app_nil_r. exact ND.
    + rewrite <- BY. exact BY56.
    + rewrite app_nil_r. exact LEN40.
    + rewrite app_nil_r. exact RB.
  - rewrite ?Z.mod_small, ?unsigned_lit in KM1 by (clear -BY56 BYLB LEN40; lia).
    step. step. zstep. zstep.                  (* [comment removed for export] *)
    step. if_cases KM2; zify_cond KM2.         (* [comment removed for export] *)
    + rewrite ?Z.mod_small, ?unsigned_lit in KM2 by (clear -BY56 BYLB LEN40; lia).
      eapply (CONT1 _ X [] (Z_to_bv 64 0)); try eassumption.
      * unfold qrec_mergeb, Q_BATCH_BYTES. destruct (Z.ltb_spec (bytes * 100) (8192 * Z.of_nat (length X) * 200)) as [Hl|Hl]; [exfalso; clear -KM2 Hl; lia|].
        rewrite andb_false_r. reflexivity.
      * cbn [length]. rewrite <- BY. clear; lia.
      * apply Box. eapply munch_weaken; [| exact MU]. unfold WQ, AQ_MUTEX, AQ_GCACHE. solve_sub_fpw ltac:(clear; lia).
      * rewrite <- BY. exact GC.
      * eapply chain_frame; [exact CH| exact MU| exact WM|]. apply Forall_forall. intros x Hx.
        (pose proof (proj1 (Forall_forall _ _) GEO x Hx) as ndP__; nd_pre ndP__ 4%nat; intros G1 G2 G3 G4; nd_post). unfold AIMG_HI, Q_BATCH_BYTES in *. cbn. clear -G1 G2 G3 CEIL LO. lia.
      * apply chain_nil.
      * rewrite app_nil_r. exact GEO.
      * rewrite app_nil_r. exact ND.
      * rewrite <- BY. exact BY56.
      * rewrite app_nil_r. exact LEN40.
      * rewrite app_nil_r. exact RB.
    + rewrite ?Z.mod_small, ?unsigned_lit in KM2 by (clear -BY56 BYLB LEN40; lia).
      (* [comment removed for export] *)
      do 7 zstep.                              (* [comment removed for export] *)
      step.                                    (* [comment removed for export] *)
      destruct X as [|cur R]; [exfalso; cbn [length Z.of_nat] in KM1, KM2; clear -KM1 KM2; lia|].
      eapply evtF_cut.
      { eapply (amerge_spec L RNG 0xab310 (bv_unsigned sp + -80) bytes 0 0 0 lo (cur :: R) []);
          rewrite ?unsigned_lit by (clear -SPR LO CEIL; lia); try eassumption; try reflexivity; try apply chain_nil; try (rewrite app_nil_r; eassumption).
        all: try (clear -CEIL LO SP47 SPR BY56 BYLB LEN40 MIN0; atop_facts; cbn [length]; lia).
        all: try (rewrite <- BY; clear -BY56; lia).
        - eapply chain_frame; [exact CH| exact MU| exact WM|]. apply Forall_forall. intros x Hx.
          (pose proof (proj1 (Forall_forall _ _) GEO x Hx) as ndP__; nd_pre ndP__ 4%nat; intros G1 G2 G3 G4; nd_post). unfold AIMG_HI, Q_BATCH_BYTES in *. cbn. clear -G1 G2 G3 CEIL LO. lia.
        - unfold Q_BATCH_BYTES. clear -LEN40. lia.
        - eapply (rng_sub _ _ _ _ _ RSTK); clear -LO CEIL SPR; lia. }
      cbv beta. unfold amerge_post. cbn [amerge_fun].
      destruct (merge_bq cur R) as [l e] eqn:MB.
      intros ms1 (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m1 & -> & MU' & WM' & MI' & ST' & LS' & CH' & TM' & CT').
      rewrite ?unsigned_lit in MU' by (clear -SPR LO CEIL; lia). rewrite ?unsigned_lit in ST' by (clear -SPR LO CEIL; lia).
      replace (ret_pc (Z_to_bv 64 0x35b48)) with (Z_to_bv 64 0x35b48) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      clear MI. rewrite app_nil_r in MU'. cbn [app] in TM', CT'.
      pose proof (merge_bq_baddr_in L R cur) as INX1. rewrite MB in INX1. cbn [fst snd] in INX1.
      assert (GEO1 : Forall (bgeom L 0xab310 (bv_unsigned sp + -80)) (l ++ e)).
      { apply Forall_forall. intros x Hx. (nd_pre (INX1 x Hx) 3%nat; intros y Hy EY; nd_post). eapply bgeom_baddr; [exact EY|]. exact (proj1 (Forall_forall _ _) GEO y Hy). }
      xport MX MU' WM' ltac:(cbn [app disjoint_from fst snd]; split; [clear -LO CEIL; lia| split; [clear; lia| split; [clear -LO CEIL; lia| eapply disj_objs_below; [exact GEO| unfold AIMG_HI; clear; lia]]]]).
      xport FRS MU' WM' ltac:(cbn [app disjoint_from fst snd]; split; [clear; lia| split; [clear -LO CEIL; lia| split; [clear; lia| eapply disj_objs_above; [exact GEO| atop_facts; clear -LO CEIL; lia]]]]).
      pose proof (merge_bq_bytes R cur) as MBY. rewrite MB in MBY. cbn [fst snd] in MBY. rewrite <- BY in MBY.
      replace (bytes - Q_BATCH_BYTES * Z.of_nat (length e)) with (batches_bytes (map fst l)) in LS' by (clear -MBY; lia).
      replace (tfirst L (cur :: R) 0) with (tfirst L l 0) in LS' by (pose proof (merge_bq_first L R cur 0) as E1; rewrite MB in E1; cbn [fst] in E1; rewrite E1; reflexivity).
      do 4 zstep.                              (* [comment removed for export] *)
      step.                                    (* [comment removed for export] *)
      eapply (CONT1 m1 l e); try eassumption.
      * unfold qrec_mergeb, Q_BATCH_BYTES. cbn [amerge_fun].
        destruct (Z.ltb_spec (8192 * Z.of_nat (length (cur :: R))) bytes) as [Hl|Hl]; [| exfalso; clear -KM1 Hl; lia].
        destruct (Z.ltb_spec (bytes * 100) (8192 * Z.of_nat (length (cur :: R)) * 200)) as [Hl2|Hl2]; [| exfalso; clear -KM2 Hl2; lia].
        cbn [andb]. exact MB.
      * clear -MBY; lia.
      * apply Box. eapply (munch_trans_w _ _ _ _ _ _ MU MU'); unfold WQ, AQ_MUTEX, AQ_GCACHE, Q_BATCH_BYTES; cbn [app].
        -- solve_sub_fpw ltac:(clear; lia).
        -- apply sub_fp_by_incl'.
           constructor; [apply Exists_exists; eexists; split; [left; reflexivity| cbn; clear; lia]|].
           constructor; [apply Exists_exists; eexists; split; [right; right; left; reflexivity| cbn; clear; lia]|].
           constructor; [apply Exists_exists; eexists; split; [left; reflexivity| cbn; clear; lia]|].
           apply Forall_forall. intros iv Hiv. apply Exists_exists. exists iv. split; [right; right; right; exact Hiv| clear; lia].
      * eapply wmono_trans; [exact WM| exact WM'].
      * apply Forall_forall. intros x Hx. (nd_pre (INX1 x Hx) 3%nat; intros y Hy EY; nd_post). rewrite <- (baddr_inj L _ _ EY). exact (proj1 (Forall_forall _ _) SL y Hy).
      * refine (proj1 (list_relations.list.NoDup_Permutation_proper _ _ _) ND). pose proof (merge_bq_slots R cur) as P. rewrite MB in P. cbn [fst snd] in P.
        apply Permutation_sym. exact P.
      * pose proof (merge_bq_sizes R cur SZ) as S1. rewrite MB in S1. cbn [fst snd] in S1. apply Forall_app in S1 as [S1 _]. exact S1.
      * clear -MBY BY56. unfold Q_BATCH_BYTES in MBY. lia.
      * pose proof (merge_bq_length R cur) as L1. rewrite MB in L1. cbn [fst snd] in L1. rewrite L1. exact LEN40.
      * apply Forall_forall. intros x Hx. (nd_pre (INX1 x Hx) 3%nat; intros y Hy EY; nd_post). rewrite <- EY. exact (proj1 (Forall_forall _ _) RB y Hy).
Qed.
End Zd2.
#[using="Type"] Theorem qrec_front : ltac:(let t := eval cbv delta [qrec_front__stmt] in qrec_front__stmt in exact t).
Proof. exact qrec_front__body. Qed.

End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AKitR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_amerge__A3W.F_amerge.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_amerge__A3W.F_aqrec_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition bslot (x : bq) : Z := qb_slot (snd x).
#[using="Type"] Lemma bslot_merge : forall cur nx, bslot (bq_merge cur nx) = bslot cur. Proof. reflexivity. Qed.
#[using="Type"] Lemma bslot_empty : forall nx, bslot (bq_empty nx) = bslot nx. Proof. reflexivity. Qed.
#[using="Type"] Lemma merge_bq_slots : forall R cur,
  Permutation (map bslot (fst (merge_bq cur R) ++ snd (merge_bq cur R))) (map bslot (cur :: R)).
Proof.
  induction R as [|nx R IH]; intros cur; cbn [merge_bq fst snd app map]; [apply Permutation_refl|].
  destruct (b_count (fst cur) + b_count (fst nx) <=? Q_BATCH).
  - specialize (IH (bq_merge cur nx)). destruct (merge_bq (bq_merge cur nx) R) as [l e]. cbn [fst snd] in IH |- *.
    rewrite map_app in IH |- *. cbn [map] in IH |- *. rewrite bslot_merge in IH. rewrite bslot_empty.
    eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|].
    apply (Permutation_trans (l' := bslot nx :: bslot cur :: map bslot R)); [| apply perm_swap].
    apply perm_skip. exact IH.
  - specialize (IH nx). destruct (merge_bq nx R) as [l e]. cbn [fst snd] in IH |- *.
    cbn [app map]. apply perm_skip. exact IH.
Qed.
#[using="Type"] Lemma merge_bq_sizes : forall R cur,
  Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) (cur :: R) ->
  Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) (fst (merge_bq cur R) ++ snd (merge_bq cur R)).
Proof.
  induction R as [|nx R IH]; intros cur HF; cbn [merge_bq fst snd].
  - rewrite app_nil_r. exact HF.
  - pose proof (Forall_inv HF) as HC. pose proof (Forall_inv (Forall_inv_tail HF)) as HN. pose proof (Forall_inv_tail (Forall_inv_tail HF)) as HR.
    cbv beta in HC, HN.
    destruct (b_count (fst cur) + b_count (fst nx) <=? Q_BATCH).
    + specialize (IH (bq_merge cur nx)). destruct (merge_bq (bq_merge cur nx) R) as [l e]. cbn [fst snd] in IH |- *.
      assert (HM : Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) (bq_merge cur nx :: R)).
      { constructor; [| exact HR]. cbn [bq_merge fst b_size]. lia. }
      specialize (IH HM). apply Forall_app in IH as [I1 I2]. apply Forall_app. split; [exact I1|]. constructor; [| exact I2].
      cbn [bq_empty fst b_size]. lia.
    + specialize (IH nx ltac:(constructor; assumption)). destruct (merge_bq nx R) as [l e]. cbn [fst snd] in IH |- *.
      cbn [app]. constructor; [exact HC| exact IH].
Qed.
#[using="Type"] Lemma merge_bq_bytes : forall R cur,
  batches_bytes (map fst (fst (merge_bq cur R))) + Q_BATCH_BYTES * Z.of_nat (length (snd (merge_bq cur R)))
  = batches_bytes (map fst (cur :: R)).
Proof.
  induction R as [|nx R IH]; intros cur; cbn [merge_bq fst snd].
  - cbn [length map]. lia.
  - destruct (b_count (fst cur) + b_count (fst nx) <=? Q_BATCH).
    + specialize (IH (bq_merge cur nx)). destruct (merge_bq (bq_merge cur nx) R) as [l e]. cbn [fst snd] in IH |- *.
      cbn [map length] in IH |- *. rewrite !batches_bytes_cons in *. cbn [bq_merge fst b_size] in IH. rewrite Nat2Z.inj_succ. lia.
    + specialize (IH nx). destruct (merge_bq nx R) as [l e]. cbn [fst snd] in IH |- *.
      cbn [map length app] in IH |- *. rewrite !batches_bytes_cons in *. lia.
Qed.
#[using="Type"] Lemma merge_bq_length : forall R cur,
  length (fst (merge_bq cur R) ++ snd (merge_bq cur R)) = length (cur :: R).
Proof.
  intros R cur. pose proof (Permutation_length (merge_bq_slots R cur)) as H. rewrite !length_map in H. exact H.
Qed.
#[using="Type"] Lemma baddr_inj : forall L x y, baddr L x = baddr L y -> bslot x = bslot y.
Proof. intros L x y E. unfold baddr, abatch_addr, aslot_addr, bslot in *. rewrite size_of_class_24 in E. lia. Qed.

#[using="Type"] Lemma batches_bytes_nonneg : forall (l : list bq),
  Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) l -> 0 <= batches_bytes (map fst l).
Proof.
  intros l HF. pose proof (batches_bytes_lb (map fst l) ltac:(rewrite Forall_map; exact HF)). unfold Q_BATCH_BYTES in *. lia.
Qed.

#[using="Type"] Lemma Forall_rot : forall (P : bq -> Prop) b G T, Forall P ((b :: G) ++ T) -> Forall P (G ++ (T ++ [b])).
Proof.
  intros P b G T H. apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall _ _) H).
  apply in_app_iff in Hx. destruct Hx as [Hx|Hx]; [right; apply in_app_iff; left; exact Hx|].
  apply in_app_iff in Hx. destruct Hx as [Hx|[<-|[]]]; [right; apply in_app_iff; right; exact Hx| left; reflexivity].
Qed.
#[using="Type"] Lemma NoDup_rot : forall b G T, base.NoDup (map bslot ((b :: G) ++ T)) -> base.NoDup (map bslot (G ++ (T ++ [b]))).
Proof.
  intros b G T ND. refine (proj1 (list_relations.list.NoDup_Permutation_proper _ _ _) ND).
  apply Permutation_map. rewrite app_assoc. cbn [app]. apply (Permutation_cons_append (G ++ T) b).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition aqrec_lh : Z := 0x35c04.      (* [comment removed for export] *)
Definition aqrec_lt : Z := 0x35c00.      (* [comment removed for export] *)
Definition aqrec_join : Z := 0x35c60.    (* [comment removed for export] *)

Section Front.
  Variables (L : alayout) (RNG : footprint) (MIN lo : Z).
  Variables (ra gp tp xs0 xs1 a2 a3 xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variable SPP : Z.   (* [comment removed for export] *)
  Hypothesis MIN0 : 0 <= MIN < 2^63.
  Hypothesis SPP0 : ATOP + 16 <= SPP.
  Hypothesis SPP1 : SPP + 80 <= 2^47.
  Hypothesis RT : rng RNG SPP 32.
  Hypothesis RG : rng RNG AQ_GCACHE 32.

  (* [comment removed for export] *)
  Definition deq_W (tfull : bool) (B TL : Z) : list (Z * Z) :=
    ((SPP, SPP + 32) :: (AQ_GCACHE, AQ_GCACHE + 32) :: (B, B + 8) :: (if tfull then [(TL, TL + 8)] else []))%Z.

  Definition deq_body_post (tfull : bool) (B TL nxn bsz nb gl gb tn : Z) (st1 tf st2 tb cw tls tlc : word) (m : amem) : machine_state -> Prop :=
    fun ms' => exists (tb' : word) m',
      ms' = MS (mkR ra (Z_to_bv 64 SPP) gp tp (Z_to_bv 64 nxn) (Z_to_bv 64 B) (Z_to_bv 64 (gb - bsz)) xs0 xs1 (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 MIN) a2 a3
                    (Z_to_bv 64 (tn + 1)) (Z_to_bv 64 B) (Z_to_bv 64 (nb - 1)) (Z_to_bv 64 nxn) xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 aqrec_lt) fc None m' (seg_rom asegs)
      /\ munch (deq_W tfull B TL) m m'
      /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' AQ_GCACHE [C8 (Z_to_bv 64 (nb - 1)); C8 (Z_to_bv 64 nxn); C8 (Z_to_bv 64 (if nxn =? 0 then 0 else gl)); C8 (Z_to_bv 64 (gb - bsz))]
      /\ rw_cells asegs m' B [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 bsz); C8 cw]
      /\ rw_cells asegs m' SPP [C8 st1; C8 (if tfull then tf else Z_to_bv 64 B); C8 st2; C8 tb']
      /\ (if tfull then rw_cells asegs m' TL [C8 (Z_to_bv 64 B); C8 tls; C8 tlc] else True).

  Definition deq_body_spec__stmt : Prop := forall (tfull : bool) (B TL nxn bsz nb gl gb tn : Z) (st1 tf st2 tb cw tlx tls tlc a7 t1 t2 : word) (m : amem),
    mem_inv asegs m ->
    rw_cells asegs m AQ_GCACHE [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 gl); C8 (Z_to_bv 64 gb)] ->
    rw_cells asegs m B [C8 (Z_to_bv 64 nxn); C8 (Z_to_bv 64 bsz); C8 cw] ->
    rw_cells asegs m SPP [C8 st1; C8 tf; C8 st2; C8 tb] ->
    (if tfull then rw_cells asegs m TL [C8 tlx; C8 tls; C8 tlc] /\ 0 < tn /\ AIMG_HI <= TL /\ TL + Q_BATCH_BYTES <= ATOP /\ (B + Q_BATCH_BYTES <= TL \/ TL + Q_BATCH_BYTES <= B)
               /\ rng RNG TL Q_BATCH_BYTES
     else tn = 0) ->
    0 < nb < 2^63 -> 0 <= nxn < 2^64 -> 0 <= gl < 2^64 -> 0 <= bsz <= gb -> gb < 2^63 -> 0 <= tn < 2^62 ->
    AIMG_HI <= B -> B + Q_BATCH_BYTES <= ATOP -> rng RNG B Q_BATCH_BYTES ->
    evtF asegs RNG (deq_body_post tfull B TL nxn bsz nb gl gb tn st1 tf st2 tb cw tls tlc m)
      (MS (mkR ra (Z_to_bv 64 SPP) gp tp (Z_to_bv 64 B) t1 t2 xs0 xs1 (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 MIN) a2 a3
               (Z_to_bv 64 tn) (Z_to_bv 64 TL) (Z_to_bv 64 nb) a7 xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 aqrec_lh) fc None m (seg_rom asegs)).
  Section Zd1.   (* [comment removed for export] *)
  Variable tfull : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 0).
  Variable B : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 1).
  Variable TL : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 2).
  Variable nxn : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 3).
  Variable bsz : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 4).
  Variable nb : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 5).
  Variable gl : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 6).
  Variable gb : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 7).
  Variable tn : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 8).
  Variable st1 : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 9).
  Variable tf : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 10).
  Variable st2 : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 11).
  Variable tb : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 12).
  Variable cw : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 13).
  Variable tlx : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 14).
  Variable tls : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 15).
  Variable tlc : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 16).
  Variable a7 : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 17).
  Variable t1 : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 18).
  Variable t2 : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 19).
  Variable m : ltac2:(SecDietF.SzSecF.ty 'deq_body_spec__stmt 20).
  #[using="SPP0 RT RG"] Lemma deq_body_spec__body : ltac:(let T := type of (fun (h : deq_body_spec__stmt) => h tfull B TL nxn bsz nb gl gb tn st1 tf st2 tb cw tlx tls tlc a7 t1 t2 m) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
  Proof.
    pose proof (fun (_ : True) => (tfull, (B, (TL, (nxn, (bsz, (nb, (gl, (gb, (tn, (st1, (tf, (st2, (tb, (cw, (tlx, (tls, (tlc, (a7, (t1, (t2, m))))))))))))))))))))) as _.
 intros MI GC BC TM TF NB NXN GL BSZ GB TN B0 B1 RB.
    unfold aqrec_lh, AIMG_HI, Q_BATCH_BYTES, AQ_GCACHE, AQUAR_Q in *.
    destruct tfull.
    - (nd_pre TF 6%nat; intros TLC TN1 TL0 TL1 DBT RTL; nd_post).
      pose proof (munch_refl (deq_W true B TL) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold deq_W, AQ_GCACHE in MU.
      (* [comment removed for export] *)
      assert (CONT : forall m1, mem_inv asegs m1 -> munch [(SPP, SPP + 32); (0xab710, 0xab710 + 32); (B, B + 8); (TL, TL + 8)]%Z m m1 -> wmono asegs m m1 ->
        rw_cells asegs m1 0xab710 [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 nxn); C8 (Z_to_bv 64 (if nxn =? 0 then 0 else gl)); C8 (Z_to_bv 64 gb)] ->
        rw_cells asegs m1 B [C8 (Z_to_bv 64 nxn); C8 (Z_to_bv 64 bsz); C8 cw] ->
        rw_cells asegs m1 SPP [C8 st1; C8 tf; C8 st2; C8 tb] ->
        rw_cells asegs m1 TL [C8 tlx; C8 tls; C8 tlc] ->
        evtF asegs RNG (deq_body_post true B TL nxn bsz nb gl gb tn st1 tf st2 tb cw tls tlc m)
          (MS (mkR ra (Z_to_bv 64 SPP) gp tp (Z_to_bv 64 B) t1 t2 xs0 xs1 (Z_to_bv 64 0xab670) (Z_to_bv 64 MIN) a2 a3
                   (Z_to_bv 64 tn) (Z_to_bv 64 TL) (Z_to_bv 64 nb) (Z_to_bv 64 nxn) xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x35c18) fc None m1 (seg_rom asegs))).
      { clear MI MU WM GC BC TM TLC. intros m1 MI MU WM GC BC TM TLC.
        zstep. step.                                     (* [comment removed for export] *)
        step. step. zstep. step.                         (* [comment removed for export] *)
        zstep. step.                                     (* [comment removed for export] *)
        step. if_cases K2; zify_cond K2; [| exfalso; rewrite ?unsigned_lit in K2 by lia; lia].   (* [comment removed for export] *)
        step.                                            (* [comment removed for export] *)
        step. step. step. step.                          (* [comment removed for export] *)
        step. zstep. zstep. zstep.                       (* [comment removed for export] *)
        replace (nb + -1) with (nb - 1) in * by lia.
        apply evtF_done. unfold deq_body_post, aqrec_lt, deq_W, AQ_GCACHE, AQUAR_Q. finish. all: eassumption. }
      step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].   (* [comment removed for export] *)
      step. step.                                        (* [comment removed for export] *)
      step. if_cases K1; zify_cond K1.                   (* [comment removed for export] *)
      + rewrite ?unsigned_lit in K1 by lia. eapply CONT; try eassumption. replace (nxn =? 0) with false by (symmetry; apply Z.eqb_neq; lia). exact GC.
      + rewrite ?unsigned_lit in K1 by lia. step.        (* [comment removed for export] *)
        eapply CONT; try eassumption. replace (nxn =? 0) with true by (symmetry; apply Z.eqb_eq; lia). exact GC.
    - pose proof TF as TN1. clear TF. subst tn.
      pose proof (munch_refl (deq_W false B TL) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold deq_W, AQ_GCACHE in MU.
      assert (CONT : forall m1, mem_inv asegs m1 -> munch [(SPP, SPP + 32); (0xab710, 0xab710 + 32); (B, B + 8)]%Z m m1 -> wmono asegs m m1 ->
        rw_cells asegs m1 0xab710 [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 nxn); C8 (Z_to_bv 64 (if nxn =? 0 then 0 else gl)); C8 (Z_to_bv 64 gb)] ->
        rw_cells asegs m1 B [C8 (Z_to_bv 64 nxn); C8 (Z_to_bv 64 bsz); C8 cw] ->
        rw_cells asegs m1 SPP [C8 st1; C8 tf; C8 st2; C8 tb] ->
        evtF asegs RNG (deq_body_post false B TL nxn bsz nb gl gb 0 st1 tf st2 tb cw tls tlc m)
          (MS (mkR ra (Z_to_bv 64 SPP) gp tp (Z_to_bv 64 B) t1 t2 xs0 xs1 (Z_to_bv 64 0xab670) (Z_to_bv 64 MIN) a2 a3
                   (Z_to_bv 64 0) (Z_to_bv 64 TL) (Z_to_bv 64 nb) (Z_to_bv 64 nxn) xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x35c18) fc None m1 (seg_rom asegs))).
      { clear MI MU WM GC BC TM. intros m1 MI MU WM GC BC TM.
        zstep. step.                                     (* [comment removed for export] *)
        step. step. zstep. step.                         (* [comment removed for export] *)
        zstep. step.                                     (* [comment removed for export] *)
        step. if_lit.                                    (* [comment removed for export] *)
        step.                                            (* [comment removed for export] *)
        step. step.                                      (* [comment removed for export] *)
        step. step. step. step.                          (* [comment removed for export] *)
        step. zstep. zstep. zstep.                       (* [comment removed for export] *)
        replace (nb + -1) with (nb - 1) in * by lia.
        apply evtF_done. unfold deq_body_post, aqrec_lt, deq_W, AQ_GCACHE, AQUAR_Q. finish. all: try eassumption. all: try exact I. }
      step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].   (* [comment removed for export] *)
      step. step.                                        (* [comment removed for export] *)
      step. if_cases K1; zify_cond K1.                   (* [comment removed for export] *)
      + rewrite ?unsigned_lit in K1 by lia. eapply CONT; try eassumption. replace (nxn =? 0) with false by (symmetry; apply Z.eqb_neq; lia). exact GC.
      + rewrite ?unsigned_lit in K1 by lia. step.        (* [comment removed for export] *)
        eapply CONT; try eassumption. replace (nxn =? 0) with true by (symmetry; apply Z.eqb_eq; lia). exact GC.
  Qed.
  End Zd1.
  #[using="SPP0 RT RG"] Lemma deq_body_spec : ltac:(let t := eval cbv delta [deq_body_spec__stmt] in deq_body_spec__stmt in exact t).
  Proof. exact deq_body_spec__body. Qed.

  (* [comment removed for export] *)
  Definition WL (G T : list bq) : list (Z * Z) :=
    ([(SPP, SPP + 32); (AQ_GCACHE, AQ_GCACHE + 32)] ++ map (fun x => (baddr L x, baddr L x + Q_BATCH_BYTES)) (G ++ T))%Z.

  Definition deq_loop_post (G T : list bq) (m : amem) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a4 a5 a6 a7 tb' : word) m',
      let '(taken, rest, bytes2) := deq_bq G (batches_bytes (map fst G)) MIN in
      ms' = MS (mkR ra (Z_to_bv 64 SPP) gp tp t0 t1 t2 xs0 xs1 (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 MIN) a2 a3 a4 a5 a6 a7 xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 aqrec_join) fc None m' (seg_rom asegs)
      /\ munch (WL G T) m m'
      /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' AQ_GCACHE [C8 (Z_to_bv 64 (Z.of_nat (length rest))); C8 (Z_to_bv 64 (tfirst L rest 0)); C8 (Z_to_bv 64 (tlast L rest 0)); C8 (Z_to_bv 64 bytes2)]
      /\ chain L m' rest 0
      /\ rw_cells asegs m' SPP [C8 (Z_to_bv 64 (Z.of_nat (length (T ++ taken)))); C8 (Z_to_bv 64 (tfirst L (T ++ taken) 0)); C8 (Z_to_bv 64 (tlast L (T ++ taken) 0)); C8 tb']
      /\ chain L m' (T ++ taken) 0
      /\ bytes2 = batches_bytes (map fst rest) /\ bytes2 <= MIN.

  #[using="rc"] Lemma deq_bq_go : forall (b : bq) l bytes mn, mn < bytes ->
    deq_bq (b :: l) bytes mn = (let '(taken, rest, bytes') := deq_bq l (bytes - b_size (fst b)) mn in (b :: taken, rest, bytes')).
  Proof. intros b l bytes mn H. cbn [deq_bq]. destruct (Z.ltb_spec mn bytes); [reflexivity| lia]. Qed.
  #[using="rc"] Lemma deq_bq_stop : forall l bytes mn, ~ mn < bytes -> deq_bq l bytes mn = ([], l, bytes).
  Proof. intros [|b l] bytes mn H; cbn [deq_bq]; [reflexivity|]. destruct (Z.ltb_spec mn bytes); [lia| reflexivity]. Qed.

  #[using="Type"] Lemma deq_bq_split : forall l bytes mn, (let '(taken, rest, _) := deq_bq l bytes mn in taken ++ rest) = l.
  Proof.
    induction l as [|b l IH]; intros bytes mn; cbn [deq_bq]; [reflexivity|].
    destruct (mn <? bytes); [| reflexivity]. specialize (IH (bytes - b_size (fst b)) mn).
    destruct (deq_bq l (bytes - b_size (fst b)) mn) as [[tk rs] b2]. cbn [app]. rewrite IH. reflexivity.
  Qed.

  #[using="Type"] Lemma bgeom_num : forall x, bgeom L AQ_GCACHE SPP x ->
    AIMG_HI <= baddr L x /\ baddr L x + Q_BATCH_BYTES <= ATOP /\ (AQ_GCACHE + 32 <= baddr L x \/ baddr L x + Q_BATCH_BYTES <= AQ_GCACHE)
    /\ (SPP + 32 <= baddr L x \/ baddr L x + Q_BATCH_BYTES <= SPP).
  Proof. intros x H. exact H. Qed.

  #[using="Type"] Lemma tfirst_range : forall X, Forall (bgeom L AQ_GCACHE SPP) X -> 0 <= tfirst L X 0 < 2^64 /\ (X <> [] -> AIMG_HI <= tfirst L X 0).
  Proof.
    intros [|x X] HF; cbn [tfirst]; [split; [lia| congruence]|].
    (pose proof (Forall_inv HF) as ndP__; nd_pre ndP__ 3%nat; intros A B _; nd_post). unfold AIMG_HI, Q_BATCH_BYTES in *. split; [lia| intros _; exact A].
  Qed.
  #[using="Type"] Lemma tlast_range : forall X, Forall (bgeom L AQ_GCACHE SPP) X -> 0 <= tlast L X 0 < 2^64.
  Proof.
    intros X HF. destruct X as [|x X']; [cbn; lia|].
    (nd_pre (tlast_in L (x :: X') 0 ltac:(congruence)) 3%nat; intros z Hz ndR1__; nd_post; revert ndR1__; intros ->).
    (pose proof (proj1 (Forall_forall _ _) HF z Hz) as ndP__; nd_pre ndP__ 3%nat; intros A B _; nd_post). unfold AIMG_HI, Q_BATCH_BYTES in *. lia.
  Qed.

  #[using="MIN0 SPP0 RT RG"] Lemma deq_loop_spec : forall (d : nat) (G T : list bq) (st1 st2 tb a7 t1 t2 : word) (m : amem),
    d = length G ->
    MIN < batches_bytes (map fst G) ->
    mem_inv asegs m ->
    rw_cells asegs m AQ_GCACHE [C8 (Z_to_bv 64 (Z.of_nat (length G))); C8 (Z_to_bv 64 (tfirst L G 0)); C8 (Z_to_bv 64 (tlast L G 0)); C8 (Z_to_bv 64 (batches_bytes (map fst G)))] ->
    chain L m G 0 ->
    rw_cells asegs m SPP [C8 st1; C8 (Z_to_bv 64 (tfirst L T 0)); C8 st2; C8 tb] ->
    chain L m T 0 ->
    Forall (bgeom L AQ_GCACHE SPP) (G ++ T) -> Forall (fun x => 0 <= bslot x) (G ++ T) -> base.NoDup (map bslot (G ++ T)) ->
    Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) G -> batches_bytes (map fst G) < 2^56 ->
    Z.of_nat (length (G ++ T)) < 2^40 ->
    Forall (fun x => rng RNG (baddr L x) Q_BATCH_BYTES) (G ++ T) ->
    evtF asegs RNG (deq_loop_post G T m)
      (MS (mkR ra (Z_to_bv 64 SPP) gp tp (Z_to_bv 64 (tfirst L G 0)) t1 t2 xs0 xs1 (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 MIN) a2 a3
               (Z_to_bv 64 (Z.of_nat (length T))) (Z_to_bv 64 (tlast L T 0)) (Z_to_bv 64 (Z.of_nat (length G))) a7 xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 aqrec_lh) fc None m (seg_rom asegs)).
  Proof.
    induction d as [|d IH]; intros until m; intros HD GO MI GC CH TM CT GEO SL ND SZ SZS LEN40 RB.
    { exfalso. destruct G; [cbn in GO; clear -GO MIN0; lia| cbn in HD; lia]. }
    destruct G as [|b G']; [cbn in HD; lia|].
    (* [comment removed for export] *)
    destruct (proj1 (chain_cons L _ _ _ _) CH) as [BCELLS CHR]. clear CH.
    (nd_pre BCELLS 6%nat; intros BC EB JB BCNT BLEN BRNG; nd_post). cbn [fst snd] in BC, EB, JB, BCNT, BLEN, BRNG.
    (pose proof (bgeom_num b (Forall_inv GEO)) as ndP__; nd_pre ndP__ 4%nat; intros GB1 GB2 GB3 GB4; nd_post).
    pose proof (Forall_inv RB) as RBb. cbv beta in RBb.
    pose proof (Forall_inv SZ) as SZb. cbv beta in SZb.
    assert (GEO' : Forall (bgeom L AQ_GCACHE SPP) G') by (apply Forall_app in GEO as [GEO _]; exact (Forall_inv_tail GEO)).
    assert (GEOT : Forall (bgeom L AQ_GCACHE SPP) T) by (apply Forall_app in GEO as [_ GEO]; exact GEO).
    pose proof (tfirst_range G' GEO') as [NXN NXP]. pose proof (tlast_range (b :: G') ltac:(apply Forall_app in GEO as [GEO _]; exact GEO)) as GL.
    pose proof (batches_bytes_nonneg G' (Forall_inv_tail SZ)) as SZR.
    cbn [map] in SZS, GO. rewrite !batches_bytes_cons in SZS, GO.
    assert (LENG : 0 < Z.of_nat (length (b :: G')) < 2^40 /\ 0 <= Z.of_nat (length T) < 2^40).
    { revert LEN40. clear. rewrite length_app. cbn [length]. intros. lia. }
    unfold AIMG_HI, Q_BATCH_BYTES, AQ_GCACHE in GB1, GB2, GB3, GB4.
    fold (baddr L b) in BC, EB, JB. set (B := baddr L b) in *.
    cbn [tfirst] in GC |- *. fold B in GC. fold B.
    (* [comment removed for export] *)
    assert (E1 : Z.of_nat (length (b :: G')) - 1 = Z.of_nat (length G')) by (clear; cbn [length]; lia).
    assert (E2 : (if tfirst L G' 0 =? 0 then 0 else tlast L (b :: G') 0) = tlast L G' 0).
    { destruct G' as [|c G'']; [reflexivity|]. specialize (NXP ltac:(congruence)). unfold AIMG_HI in NXP.
      destruct (Z.eqb_spec (tfirst L (c :: G'') 0) 0); [exfalso; clear -NXP e; lia|]. rewrite tlast_cons_ne by congruence. reflexivity. }
    assert (E3 : b_size (fst b) + batches_bytes (map fst G') - b_size (fst b) = batches_bytes (map fst G')) by (clear; lia).
    assert (E3' : batches_bytes (map fst (b :: G')) - b_size (fst b) = batches_bytes (map fst G')) by (clear; cbn [map]; rewrite batches_bytes_cons; lia).
    atop_facts. unfold AQ_GCACHE, AQUAR_Q in *.
    (* [comment removed for export] *)
    assert (OTH : forall x, In x (G' ++ T) -> bslot x <> bslot b /\ 0 <= bslot x /\ bgeom L AQ_GCACHE SPP x).
    { intros x Hx. split; [| split].
      - apply (nodup_mid bslot [] b (G' ++ T) ND x Hx).
      - eapply (proj1 (Forall_forall _ _) SL). right. exact Hx.
      - eapply (proj1 (Forall_forall _ _) GEO). right. exact Hx. }
    assert (SLb : 0 <= bslot b) by (eapply (proj1 (Forall_forall _ _) SL); left; reflexivity).
    assert (DJB : forall x, In x (G' ++ T) -> baddr L x + 8192 <= B \/ B + 8192 <= baddr L x).
    { intros x Hx. (nd_pre (OTH x Hx) 3%nat; intros N1 S1 _; nd_post). pose proof (baddr_disj L x b N1 S1 SLb) as D. unfold Q_BATCH_BYTES in D. exact D. }
    destruct (list_eq_dec bq_eq_dec T []) as [TNIL|TNE].
    - (* [comment removed for export] *)
      subst T. cbn [tfirst tlast map List.last length Z.of_nat] in TM |- *.
      eapply evtF_cut.
      { eapply (deq_body_spec false B 0 (tfirst L G' 0) (b_size (fst b)) (Z.of_nat (length (b :: G'))) (tlast L (b :: G') 0)
                  (b_size (fst b) + batches_bytes (map fst G')) 0 st1 (Z_to_bv 64 0) st2 tb (Z_to_bv 64 (b_count (fst b))) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)).
        1: exact MI. 1: exact GC. 1: exact BC. 1: exact TM. 1: reflexivity. 9: exact RBb.
        all: clear -GB1 GB2 GB3 GB4 NXN GL SZb SZR SZS LENG BRNG; unfold AIMG_HI, Q_BATCH_BYTES, Q_BATCH in *; lia. }
      cbv beta. intros ms1 (tb' & m1 & -> & MUc & WMc & MI1 & GC1 & BC1 & TM1 & _). clear MI.
      rewrite E1, E2, E3 in GC1. unfold deq_W, AQ_GCACHE in MUc. unfold AQ_GCACHE in GC1.
      (* [comment removed for export] *)
      assert (REB : forall mf, munch [(SPP, SPP + 32); (0xab710, 0xab710 + 32); (B, B + 8)]%Z m mf -> wmono asegs m mf ->
                rw_cells asegs mf B [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (b_size (fst b))); C8 (Z_to_bv 64 (b_count (fst b)))] ->
                chain L mf G' 0 /\ chain L mf [b] 0).
      { intros mf MUf WMf BCf. split.
        - eapply chain_frame; [exact CHR| exact MUf| exact WMf|]. apply Forall_forall. intros x Hx.
          (nd_pre (OTH x ltac:(apply in_app_iff; left; exact Hx)) 3%nat; intros _ _ Gx; nd_post). apply bgeom_num in Gx. specialize (DJB x ltac:(apply in_app_iff; left; exact Hx)).
          unfold AIMG_HI, Q_BATCH_BYTES, AQ_GCACHE in *. cbn. clear -Gx DJB. lia.
        - pose proof EB as EBf. xport EBf MUf WMf ltac:(clear -BRNG BCNT BLEN GB3 GB4; rewrite length_map, qhdrs_length by exact BLEN; unfold AQ_GCACHE, Q_BATCH_BYTES, Q_BATCH in *; lia).
          destruct JB as [jb JBf]. xport JBf MUf WMf ltac:(clear -BRNG GB3 GB4; unfold AQ_GCACHE, Q_BATCH_BYTES, Q_BATCH in *; lia).
          apply (proj2 (chain_cons L _ _ _ _)). split; [| apply chain_nil]. unfold abatch_cells. cbn [tfirst]. fold B.
          split; [exact BCf|]. split; [exact EBf|]. split; [exists jb; exact JBf|]. clear -BCNT BLEN BRNG. tauto. }
      clear BC.
      unfold aqrec_lt. step. if_cases KX; zify_cond KX.          (* [comment removed for export] *)
      + rewrite E3 in KX. rewrite ?Z.mod_small, ?unsigned_lit in KX by (clear -MIN0 SZR SZS SZb; unfold Q_BATCH_BYTES in SZb; lia).
        step. step.                                             (* [comment removed for export] *)
        apply evtF_done. unfold deq_loop_post, aqrec_join.
        rewrite deq_bq_go by exact GO. rewrite E3'. rewrite deq_bq_stop by (clear -KX; lia).
        cbn [app length Z.of_nat Pos.of_succ_nat Pos.to_nat tfirst tlast map List.last]. fold B.
        do 9 eexists. split; [reflexivity|].
        split. { eapply munch_weaken; [| exact MUc]. unfold WL, AQ_GCACHE, Q_BATCH_BYTES. rewrite app_nil_r. cbn [map app]. fold B.
                 solve_sub_fpw ltac:(clear; lia). }
        destruct (REB _ MUc WMc BC1) as [CHR1 CHB].
        split; [exact WMc|]. split; [exact MI1|].
        split; [exact GC1|]. split; [exact CHR1|]. split; [exact TM1|]. split; [exact CHB|].
        split; [reflexivity| clear -KX; lia].
      + rewrite E3 in KX. rewrite ?Z.mod_small, ?unsigned_lit in KX by (clear -MIN0 SZR SZS SZb; unfold Q_BATCH_BYTES in SZb; lia).
        destruct (REB _ MUc WMc BC1) as [CHR1 CHB].
        rewrite E1. replace (0 + 1) with (Z.of_nat (length [b])) by reflexivity.
        change (Z_to_bv 64 B) with (Z_to_bv 64 (tlast L [b] 0)) at 2.
        eapply evtF_mono.
        { eapply (IH G' [b] st1 st2 tb'); [cbn in HD; clear -HD; lia| exact KX| exact MI1| exact GC1| exact CHR1| exact TM1| exact CHB| ..].
          - exact (Forall_rot _ _ _ _ GEO).
          - exact (Forall_rot _ _ _ _ SL).
          - exact (NoDup_rot _ _ _ ND).
          - exact (Forall_inv_tail SZ).
          - clear -SZS SZb; unfold Q_BATCH_BYTES in SZb; lia.
          - revert LEN40; clear; rewrite !length_app; cbn [length]; intros; lia.
          - exact (Forall_rot _ _ _ _ RB). }
        cbv beta. unfold deq_loop_post, aqrec_join. intros ms' (y0 & y1 & y2 & y4 & y5 & y6 & y7 & tb'' & m' & POST).
        rewrite deq_bq_go by exact GO. rewrite E3'. destruct (deq_bq G' (batches_bytes (map fst G')) MIN) as [[tk rs] b2].
        (destruct POST as (-> & ndR1__); nd_pre ndR1__ 9%nat; intros MU' WM' MI' GC' CH' TM' CT' HB2 HB3; nd_post).
        cbn [app] in TM', CT' |- *.
        do 9 eexists. split; [reflexivity|].
        split. { eapply (munch_trans_w _ _ _ _ _ _ MUc MU').
                 - unfold WL, Q_BATCH_BYTES. rewrite app_nil_r. cbn [map app]. fold B. solve_sub_fpw ltac:(clear; lia).
                 - unfold WL. apply sub_fp_incl. intros iv Hiv. apply in_app_iff in Hiv. apply in_app_iff. destruct Hiv as [Hiv|Hiv]; [left; exact Hiv| right].
                   rewrite app_nil_r. rewrite map_app in Hiv. cbn [map] in Hiv |- *. apply in_app_iff in Hiv. destruct Hiv as [Hiv|[Hiv|[]]]; [right; exact Hiv| left; exact Hiv]. }
        split; [eapply wmono_trans; [exact WMc| exact WM']|]. split; [exact MI'|].
        split; [exact GC'|]. split; [exact CH'|]. split; [exact TM'|]. split; [exact CT'|]. split; [exact HB2| exact HB3].
    - (* [comment removed for export] *)
      destruct (exists_last TNE) as [T0 [tl ET]].
      pose proof CT as CT'. rewrite ET in CT'. destruct (proj1 (chain_app L _ _ _ _) CT') as [CT0 CTL]. clear CT CT'. cbn [tfirst] in CT0.
      destruct (proj1 (chain_cons L _ _ _ _) CTL) as [TLCELLS _]. clear CTL.
      (nd_pre TLCELLS 6%nat; intros TLC ETL JTL TCNT TLEN TRNG; nd_post). cbn [fst snd tfirst] in TLC, ETL, JTL, TCNT, TLEN, TRNG.
      assert (INTL : In tl (G' ++ T)) by (rewrite ET; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity).
      (nd_pre (OTH tl INTL) 3%nat; intros NTL STL GTL; nd_post). apply bgeom_num in GTL. (nd_pre GTL 4%nat; intros GT1 GT2 GT3 GT4; nd_post).
      pose proof (DJB tl INTL) as DBT.
      assert (RTL : rng RNG (baddr L tl) Q_BATCH_BYTES) by (eapply (proj1 (Forall_forall _ _) RB); right; exact INTL).
      unfold AIMG_HI, Q_BATCH_BYTES, AQ_GCACHE in GT1, GT2, GT3, GT4.
      fold (baddr L tl) in TLC, ETL, JTL. set (TL := baddr L tl) in *.
      replace (tlast L T 0) with TL by (rewrite ET, tlast_app1; reflexivity).
      assert (OTT : forall x, In x (G' ++ T0) -> bslot x <> bslot tl).
      { intros x Hx. apply (nodup_mid bslot (b :: G' ++ T0) tl [] ); [| apply in_app_iff; left; right; exact Hx].
        cbn [app]. rewrite ET in ND. cbn [app] in ND. rewrite <- app_assoc. exact ND. }
      assert (DJT : forall x, In x (G' ++ T0) -> baddr L x + 8192 <= TL \/ TL + 8192 <= baddr L x).
      { intros x Hx. assert (Hx' : In x (G' ++ T)).
        { rewrite ET. apply in_app_iff in Hx. apply in_app_iff. destruct Hx as [Hx|Hx]; [left; exact Hx| right; apply in_app_iff; left; exact Hx]. }
        (nd_pre (OTH x Hx') 3%nat; intros _ S1 _; nd_post).
        pose proof (baddr_disj L x tl (OTT x Hx) S1 STL) as D. unfold Q_BATCH_BYTES in D. exact D. }
      assert (LENT : 0 < Z.of_nat (length T)) by (rewrite ET; clear; rewrite length_app; cbn [length]; lia).
      eapply evtF_cut.
      { eapply (deq_body_spec true B TL (tfirst L G' 0) (b_size (fst b)) (Z.of_nat (length (b :: G'))) (tlast L (b :: G') 0)
                  (b_size (fst b) + batches_bytes (map fst G')) (Z.of_nat (length T)) st1 (Z_to_bv 64 (tfirst L T 0)) st2 tb
                  (Z_to_bv 64 (b_count (fst b))) (Z_to_bv 64 0) (Z_to_bv 64 (b_size (fst tl))) (Z_to_bv 64 (b_count (fst tl)))).
        1: exact MI. 1: exact GC. 1: exact BC. 1: exact TM.
        1: { split; [exact TLC|]. split; [exact LENT| split; [| split; [| split; [clear -DBT; unfold Q_BATCH_BYTES; lia| unfold Q_BATCH_BYTES; exact RTL]]]].
             - clear -GT1; unfold AIMG_HI; lia.
             - clear -GT2; unfold Q_BATCH_BYTES; lia. }
        9: exact RBb.
        all: clear -GB1 GB2 GB3 GB4 NXN GL SZb SZR SZS LENG BRNG; unfold AIMG_HI, Q_BATCH_BYTES, Q_BATCH in *; lia. }
      cbv beta. intros ms1 (tb' & m1 & -> & MUc & WMc & MI1 & GC1 & BC1 & TM1 & TLC1). clear MI.
      rewrite E1, E2, E3 in GC1. unfold deq_W, AQ_GCACHE in MUc. unfold AQ_GCACHE in GC1.
      (* [comment removed for export] *)
      assert (REB : forall mf, munch [(SPP, SPP + 32); (0xab710, 0xab710 + 32); (B, B + 8); (TL, TL + 8)]%Z m mf -> wmono asegs m mf ->
                rw_cells asegs mf B [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (b_size (fst b))); C8 (Z_to_bv 64 (b_count (fst b)))] ->
                rw_cells asegs mf TL [C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 (b_size (fst tl))); C8 (Z_to_bv 64 (b_count (fst tl)))] ->
                chain L mf G' 0 /\ chain L mf (T ++ [b]) 0).
      { intros mf MUf WMf BCf TLCf. split.
        - eapply chain_frame; [exact CHR| exact MUf| exact WMf|]. apply Forall_forall. intros x Hx.
          (nd_pre (OTH x ltac:(apply in_app_iff; left; exact Hx)) 3%nat; intros Nx Sx Gx; nd_post). apply bgeom_num in Gx. specialize (DJB x ltac:(apply in_app_iff; left; exact Hx)).
          pose proof (DJT x ltac:(apply in_app_iff; left; exact Hx)) as DxT.
          unfold AIMG_HI, Q_BATCH_BYTES, AQ_GCACHE in *. cbn. clear -Gx DJB DxT. lia.
        - pose proof EB as EBf. xport EBf MUf WMf ltac:(clear -BRNG BCNT BLEN GB3 GB4 DBT; rewrite length_map, qhdrs_length by exact BLEN; unfold AQ_GCACHE, Q_BATCH_BYTES, Q_BATCH in *; lia).
          destruct JB as [jb JBf]. xport JBf MUf WMf ltac:(clear -BRNG GB3 GB4 DBT; unfold AQ_GCACHE, Q_BATCH_BYTES, Q_BATCH in *; lia).
          pose proof ETL as ETf. xport ETf MUf WMf ltac:(clear -TRNG TCNT TLEN GT3 GT4 DBT; rewrite length_map, qhdrs_length by exact TLEN; unfold AQ_GCACHE, Q_BATCH_BYTES, Q_BATCH in *; lia).
          destruct JTL as [jt JTf]. xport JTf MUf WMf ltac:(clear -TRNG GT3 GT4 DBT; unfold AQ_GCACHE, Q_BATCH_BYTES, Q_BATCH in *; lia).
          rewrite ET. apply (proj2 (chain_app L _ _ _ _)). split.
          + apply (proj2 (chain_app L _ _ _ _)). cbn [tfirst]. fold TL. fold B. split.
            * eapply chain_frame; [exact CT0| exact MUf| exact WMf|]. apply Forall_forall. intros x Hx.
              assert (HxT : In x (G' ++ T)) by (rewrite ET; apply in_app_iff; right; apply in_app_iff; left; exact Hx).
              (nd_pre (OTH x HxT) 3%nat; intros _ _ Gx; nd_post). apply bgeom_num in Gx.
              specialize (DJB x HxT). specialize (DJT x ltac:(apply in_app_iff; right; exact Hx)).
              unfold AIMG_HI, Q_BATCH_BYTES, AQ_GCACHE in *. cbn. clear -Gx DJB DJT. lia.
            * apply (proj2 (chain_cons L _ _ _ _)). split; [| apply chain_nil]. unfold abatch_cells. cbn [tfirst fst snd]. fold TL. fold B.
              split; [exact TLCf|]. split; [exact ETf|]. split; [exists jt; exact JTf|]. clear -TCNT TLEN TRNG. tauto.
          + apply (proj2 (chain_cons L _ _ _ _)). split; [| apply chain_nil]. unfold abatch_cells. cbn [tfirst]. fold B.
            split; [exact BCf|]. split; [exact EBf|]. split; [exists jb; exact JBf|]. clear -BCNT BLEN BRNG. tauto. }
      clear BC TLC.
      assert (TF : tfirst L (T ++ [b]) 0 = tfirst L T 0) by (apply tfirst_app; exact TNE).
      assert (TLN : Z.of_nat (length (T ++ [b])) = Z.of_nat (length T) + 1) by (clear; rewrite length_app; cbn [length]; lia).
      (* [comment removed for export] *)
      assert (SUB : sub_fp [(SPP, SPP + 32); (0xab710, 0xab710 + 32); (B, B + 8); (TL, TL + 8)]%Z (WL (b :: G') T)).
      { unfold WL, Q_BATCH_BYTES, AQ_GCACHE. apply sub_fp_by_incl'.
        constructor; [apply Exists_exists; eexists; split; [left; reflexivity| cbn; clear; lia]|].
        constructor; [apply Exists_exists; eexists; split; [right; left; reflexivity| cbn; clear; lia]|].
        constructor; [apply Exists_exists; eexists; split; [right; right; apply in_map_iff; exists b; split; [reflexivity| left; reflexivity]| cbn; fold B; clear; lia]|].
        constructor; [apply Exists_exists; eexists; split; [right; right; apply in_map_iff; exists tl; split; [reflexivity| right; exact INTL]| cbn; fold TL; clear; lia]|].
        constructor. }
      unfold aqrec_lt. step. if_cases KX; zify_cond KX.          (* [comment removed for export] *)
      + rewrite E3 in KX. rewrite ?Z.mod_small, ?unsigned_lit in KX by (clear -MIN0 SZR SZS SZb; unfold Q_BATCH_BYTES in SZb; lia).
        step. step.                                             (* [comment removed for export] *)
        apply evtF_done. unfold deq_loop_post, aqrec_join.
        rewrite deq_bq_go by exact GO. rewrite E3'. rewrite deq_bq_stop by (clear -KX; lia).
        rewrite TF, TLN, tlast_app1. fold B.
        cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat tfirst tlast map List.last].
        do 9 eexists. split; [reflexivity|].
        split; [eapply munch_weaken; [exact SUB| exact MUc]|].
        destruct (REB _ MUc WMc BC1 TLC1) as [CHR1 CHB].
        split; [exact WMc|]. split; [exact MI1|].
        split; [exact GC1|]. split; [exact CHR1|]. split; [exact TM1|]. split; [exact CHB|].
        split; [reflexivity| clear -KX; lia].
      + rewrite E3 in KX. rewrite ?Z.mod_small, ?unsigned_lit in KX by (clear -MIN0 SZR SZS SZb; unfold Q_BATCH_BYTES in SZb; lia).
        destruct (REB _ MUc WMc BC1 TLC1) as [CHR1 CHB].
        rewrite E1. rewrite <- TLN. rewrite <- TF in TM1.
        replace (Z_to_bv 64 B) with (Z_to_bv 64 (tlast L (T ++ [b]) 0)) by (rewrite tlast_app1; reflexivity).
        eapply evtF_mono.
        { eapply (IH G' (T ++ [b]) st1 st2 tb'); [cbn in HD; clear -HD; lia| exact KX| exact MI1| exact GC1| exact CHR1| exact TM1| exact CHB| ..].
          - exact (Forall_rot _ _ _ _ GEO).
          - exact (Forall_rot _ _ _ _ SL).
          - exact (NoDup_rot _ _ _ ND).
          - exact (Forall_inv_tail SZ).
          - clear -SZS SZb; unfold Q_BATCH_BYTES in SZb; lia.
          - revert LEN40; clear; rewrite !length_app; cbn [length]; intros; lia.
          - exact (Forall_rot _ _ _ _ RB). }
        cbv beta. unfold deq_loop_post, aqrec_join. intros ms' (y0 & y1 & y2 & y4 & y5 & y6 & y7 & tb'' & m' & POST).
        rewrite deq_bq_go by exact GO. rewrite E3'. destruct (deq_bq G' (batches_bytes (map fst G')) MIN) as [[tk rs] b2].
        (destruct POST as (-> & ndR1__); nd_pre ndR1__ 9%nat; intros MU' WM' MI' GC' CH' TM' CT' HB2 HB3; nd_post).
        rewrite <- app_assoc in TM', CT'. cbn [app] in TM', CT'.
        do 9 eexists. split; [reflexivity|].
        split. { eapply (munch_trans_w _ _ _ _ _ _ MUc MU'); [exact SUB|].
                 unfold WL. apply sub_fp_incl. intros iv Hiv. apply in_app_iff in Hiv. apply in_app_iff. destruct Hiv as [Hiv|Hiv]; [left; exact Hiv| right].
                 rewrite !map_app in Hiv. rewrite map_app. cbn [map] in Hiv |- *. apply in_app_iff in Hiv. rewrite in_app_iff.
                 destruct Hiv as [Hiv|Hiv]; [left; right; exact Hiv|]. apply in_app_iff in Hiv. destruct Hiv as [Hiv|[Hiv|[]]]; [right; exact Hiv| left; left; exact Hiv]. }
        split; [eapply wmono_trans; [exact WMc| exact WM']|]. split; [exact MI'|].
        split; [exact GC'|]. split; [exact CH'|]. split; [exact TM'|]. split; [exact CT'|]. split; [exact HB2| exact HB3].
  Qed.
End Front.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma disj_objs_below : forall L LST TMP Y A n, Forall (bgeom L LST TMP) Y -> A + n <= AIMG_HI ->
  disjoint_from (map (fun x => (baddr L x, baddr L x + Q_BATCH_BYTES)) Y) A n.
Proof.
  intros L LST TMP Y A n HF HA. apply disjoint_from_Forall. apply Forall_map. eapply Forall_impl; [| exact HF].
  intros x (G1 & G2 & _). cbn [fst snd]. right. unfold AIMG_HI, Q_BATCH_BYTES in *. lia.
Qed.

#[using="Type"] Lemma bgeom_baddr : forall L LST TMP x y, baddr L y = baddr L x -> bgeom L LST TMP y -> bgeom L LST TMP x.
Proof. intros L LST TMP x y E H. unfold bgeom in *. rewrite <- E. exact H. Qed.

(* [comment removed for export] *)
Definition WQ (L : alayout) (sp : Z) (X : list bq) : list (Z * Z) :=
  ((sp - 96, sp) :: (AQ_MUTEX, AQ_MUTEX + 4) :: (AQ_GCACHE, AQ_GCACHE + 32) :: map (fun x => (baddr L x, baddr L x + Q_BATCH_BYTES)) X)%Z.

Definition qrec_front__stmt : Prop := qrec_front_stmt.
Section Zd2.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'qrec_front__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'qrec_front__stmt 1).
Variable X : ltac2:(SecDietF.SzSecF.ty 'qrec_front__stmt 2).
Variable bytes : ltac2:(SecDietF.SzSecF.ty 'qrec_front__stmt 3).
Variable min_size : ltac2:(SecDietF.SzSecF.ty 'qrec_front__stmt 4).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'qrec_front__stmt 5).
#[using="Type"] Lemma qrec_front__body : ltac:(let T := type of (fun (h : qrec_front__stmt) => h L RNG X bytes min_size lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (X, (bytes, (min_size, lo)))))) as _.
 intros until m.
  intros ST CEIL LO SP47 MI -> -> MIN0 MX GC CH GEO SL ND SZ BY BY56 LEN40 RIMG RTLS RSTK RB.
  atop_facts. unfold AQUAR_Q, AQ_MUTEX, AQ_GCACHE in *.
  word_range sp SPR.
  pose proof (batches_bytes_lb (map fst X) ltac:(rewrite Forall_map; exact SZ)) as BYLB. rewrite length_map, <- BY in BYLB. unfold Q_BATCH_BYTES in BYLB.
  change (@length (abatch * qbatchc) X) with (@length bq X) in BYLB.
  assert (RT : rng RNG (bv_unsigned sp + -80) 32) by (eapply (rng_sub _ _ _ _ _ RSTK); clear -LO SPR; lia).
  assert (RG : rng RNG 0xab710 32) by (eapply (rng_sub _ _ _ _ _ RIMG); clear; lia).
  assert (RMX : rng RNG 0xab708 4) by (eapply (rng_sub _ _ _ _ _ RIMG); clear; lia).
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (0xab708, 0xab708 + 4); (0xab710, 0xab710 + 32)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  assert (CONT2 : forall (m2 : amem) (rest T : list bq) (bytes2 : Z) (tb' rax t0 t1 t2 xs0 xs1 xs2 xs3 xs4 a4 a5 a6 a7 u3 u4 u5 u6 : word),
    qrec_fun X bytes min_size = (rest, T, bytes2) ->
    mem_inv asegs m2 -> boxed (munch (WQ L (bv_unsigned sp) X) m m2) -> wmono asegs m m2 -> stk asegs m2 lo (bv_unsigned sp + -80) ->
    rw_cells asegs m2 0xab708 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
    rw_cells asegs m2 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m2 (bv_unsigned sp + -80) [C8 (Z_to_bv 64 (Z.of_nat (length T))); C8 (Z_to_bv 64 (tfirst L T 0)); C8 (Z_to_bv 64 (tlast L T 0)); C8 tb'] ->
    rw_cells asegs m2 0xab710 [C8 (Z_to_bv 64 (Z.of_nat (length rest))); C8 (Z_to_bv 64 (tfirst L rest 0)); C8 (Z_to_bv 64 (tlast L rest 0)); C8 (Z_to_bv 64 bytes2)] ->
    chain L m2 rest 0 -> chain L m2 T 0 -> bytes2 = batches_bytes (map fst rest) -> bytes2 <= min_size ->
    Forall (bgeom L 0xab710 (bv_unsigned sp + -80)) (rest ++ T) ->
    evtF asegs RNG (qrec_front_post L X bytes min_size lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 F fc m)
      (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 xs0 xs1 (Z_to_bv 64 0xab670) (Z_to_bv 64 min_size) a2 a3 a4 a5 a6 a7
               xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6) F (Z_to_bv 64 aqrec_join) fc None m2 (seg_rom asegs))).
  { clear MI MU WM ST MX GC CH. intros m2 rest T bytes2 tb' rax x1 y1 y2 xs0 xs1 xs2 xs3 xs4 y4 y5 y6 y7 u3 u4 u5 u6 QF MI MUP WM ST MX FRS TM GC CHR CT HB2 HB3 GEO2.
    pose proof (munch_refl [(0xab708, 0xab708 + 4)]%Z m2) as MU.
    pose proof (wmono_refl asegs m2) as WM2.
    unfold aqrec_join.
    step.                                      (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    zstep. step.                               (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mf _) =>
      assert (CHR' : chain L mf rest 0) by (eapply chain_frame; [exact CHR| exact MU| exact WM2|]; apply Forall_forall; intros x Hx;
        pose proof (proj1 (Forall_forall _ _) GEO2 x ltac:(apply in_app_iff; left; exact Hx)) as (Gx & _); unfold AIMG_HI in Gx; cbn; clear -Gx; lia);
      assert (CT' : chain L mf T 0) by (eapply chain_frame; [exact CT| exact MU| exact WM2|]; apply Forall_forall; intros x Hx;
        pose proof (proj1 (Forall_forall _ _) GEO2 x ltac:(apply in_app_iff; right; exact Hx)) as (Gx & _); unfold AIMG_HI in Gx; cbn; clear -Gx; lia)
    end.
    apply evtF_done. unfold qrec_front_post. rewrite QF. unbox MUP.
    do 19 eexists. split; [reflexivity|].
    split; [eapply (munch_trans_w _ _ _ _ _ _ MUP MU); [intros z Hz; exact Hz| unfold WQ; solve_sub_fpw ltac:(clear; lia)]|].
    split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact TM|]. split; [exact FRS|]. split; [exact MX|].
    split; [exact GC|]. split; [exact CHR'|]. split; [exact CT'|]. split; [exact HB2| exact HB3]. }
  (* [comment removed for export] *)
  assert (CONT1 : forall (m1 : amem) (G T0 : list bq) (tb rax t0 t1 t2 xs0 xs1 xs2 xs3 xs4 a4 a5 a7 u3 u4 u5 u6 : word),
    (if qrec_mergeb (Z.of_nat (length X)) bytes then amerge_fun X else (X, [])) = (G, T0) ->
    bytes - Q_BATCH_BYTES * Z.of_nat (length T0) = batches_bytes (map fst G) ->
    mem_inv asegs m1 -> boxed (munch (WQ L (bv_unsigned sp) X) m m1) -> wmono asegs m m1 -> stk asegs m1 lo (bv_unsigned sp + -80) ->
    rw_cells asegs m1 0xab708 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
    rw_cells asegs m1 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m1 (bv_unsigned sp + -80) [C8 (Z_to_bv 64 (Z.of_nat (length T0))); C8 (Z_to_bv 64 (tfirst L T0 0)); C8 (Z_to_bv 64 (tlast L T0 0)); C8 tb] ->
    rw_cells asegs m1 0xab710 [C8 (Z_to_bv 64 (Z.of_nat (length G))); C8 (Z_to_bv 64 (tfirst L G 0)); C8 (Z_to_bv 64 (tlast L G 0)); C8 (Z_to_bv 64 (batches_bytes (map fst G)))] ->
    chain L m1 G 0 -> chain L m1 T0 0 ->
    Forall (bgeom L 0xab710 (bv_unsigned sp + -80)) (G ++ T0) -> Forall (fun x => 0 <= bslot x) (G ++ T0) -> base.NoDup (map bslot (G ++ T0)) ->
    Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) G -> batches_bytes (map fst G) < 2^56 -> Z.of_nat (length (G ++ T0)) < 2^40 ->
    Forall (fun x => rng RNG (baddr L x) Q_BATCH_BYTES) (G ++ T0) ->
    (forall x, In x (G ++ T0) -> exists y, In y X /\ baddr L y = baddr L x) ->
    evtF asegs RNG (qrec_front_post L X bytes min_size lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 F fc m)
      (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 xs0 xs1 (Z_to_bv 64 0xab670) (Z_to_bv 64 min_size) a2 a3 a4 a5
               (Z_to_bv 64 (Z.of_nat (length G))) a7 xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6) F (Z_to_bv 64 0x35bc4) fc None m1 (seg_rom asegs))).
  { clear MI MU WM ST MX GC CH. intros m1 G T0 tb rax x1 y1 y2 xs0 xs1 xs2 xs3 xs4 y4 y5 y7 u3 u4 u5 u6 QF HBY MI MUP WM ST MX FRS TM GC CHR CT GEO1 SL1 ND1 SZ1 SZS1 LEN1 RB1 INX.
    pose proof (batches_bytes_nonneg G SZ1) as GB0.
    pose proof (tfirst_range L (bv_unsigned sp + -80) G ltac:(apply Forall_app in GEO1 as [G1 _]; exact G1)) as [TF0 _].
    pose proof (tlast_range L (bv_unsigned sp + -80) T0 ltac:(apply Forall_app in GEO1 as [_ G1]; exact G1)) as TL0.
    assert (LENS : 0 <= Z.of_nat (length G) < 2^40 /\ 0 <= Z.of_nat (length T0) < 2^40) by (revert LEN1; clear; rewrite length_app; intros; lia).
    step. step. step.                          (* [comment removed for export] *)
    step. if_cases KL; zify_cond KL.           (* [comment removed for export] *)
    - rewrite ?Z.mod_small, ?unsigned_lit in KL by (clear -MIN0 GB0 SZS1; lia).
      eapply (CONT2 m1 G T0 (batches_bytes (map fst G)) tb); try eassumption.
      + unfold qrec_fun. rewrite QF, HBY, deq_bq_stop by (clear -KL; lia). rewrite app_nil_r. reflexivity.
      + reflexivity.
    - rewrite ?Z.mod_small, ?unsigned_lit in KL by (clear -MIN0 GB0 SZS1; lia).
      step. step.                              (* [comment removed for export] *)
      eapply evtF_cut.
      { eapply deq_loop_spec with (d := length G) (G := G) (T := T0); [..| reflexivity| exact KL| exact MI| exact GC| exact CHR| exact TM| exact CT
          | exact GEO1| exact SL1| exact ND1| exact SZ1| exact SZS1| exact LEN1| exact RB1].
        all: try assumption. all: atop_facts; clear -CEIL LO SP47 SPR MIN0; lia. }
      cbv beta. unfold deq_loop_post. intros ms2 (z0 & z1 & z2 & z4 & z5 & z6 & z7 & tb' & m2 & POST).
      pose proof (deq_bq_split G (batches_bytes (map fst G)) min_size) as SPLIT.
      destruct (deq_bq G (batches_bytes (map fst G)) min_size) as [[tk rs] b2] eqn:DQ.
      (destruct POST as (-> & ndR1__); nd_pre ndR1__ 9%nat; intros MU' WM' MI' GC' CH' TM' CT' HB2 HB3; nd_post). clear MI.
      assert (GEO2 : Forall (bgeom L 0xab710 (bv_unsigned sp + -80)) (rs ++ T0 ++ tk)).
      { apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall _ _) GEO1). rewrite <- SPLIT. rewrite <- app_assoc. apply in_app_iff in Hx. apply in_app_iff.
        destruct Hx as [Hx|Hx]; [right; apply in_app_iff; left; exact Hx|]. apply in_app_iff in Hx. destruct Hx as [Hx|Hx]; [right; apply in_app_iff; right; exact Hx| left; exact Hx]. }
      (* [comment removed for export] *)
      xport MX MU' WM' ltac:(unfold WL, AQ_GCACHE; cbn [app disjoint_from fst snd]; split; [clear -LO CEIL; lia| split; [clear; lia| eapply disj_objs_below; [exact GEO1| unfold AIMG_HI; clear; lia]]]).
      xport FRS MU' WM' ltac:(unfold WL, AQ_GCACHE; cbn [app disjoint_from fst snd]; split; [clear; lia| split; [clear -LO CEIL; lia| eapply disj_objs_above; [exact GEO1| atop_facts; clear -LO CEIL; lia]]]).
      xport ST MU' WM' ltac:(unfold WL, AQ_GCACHE; cbn [app disjoint_from fst snd]; split; [clear; lia| split; [clear -LO CEIL; lia| eapply disj_objs_above; [exact GEO1| atop_facts; clear -LO CEIL; lia]]]).
      unbox MUP.
      eapply (CONT2 m2 rs (T0 ++ tk) b2 tb'); try eassumption.
      + unfold qrec_fun. rewrite QF, HBY, DQ. reflexivity.
      + apply Box. eapply (munch_trans_w _ _ _ _ _ _ MUP MU'); [intros z Hz; exact Hz|].
        unfold WL, WQ, AQ_GCACHE, AQ_MUTEX. cbn [app]. apply sub_fp_by_incl'.
        constructor; [apply Exists_exists; eexists; split; [left; reflexivity| cbn; clear; lia]|].
        constructor; [apply Exists_exists; eexists; split; [right; right; left; reflexivity| cbn; clear; lia]|].
        apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv. (nd_pre Hiv 2%nat; intros x ndR1__; nd_post; destruct ndR1__ as (<- & ndR2__); rename ndR2__ into Hx). (nd_pre (INX x Hx) 3%nat; intros y Hy EY; nd_post).
        apply Exists_exists. eexists. split; [right; right; right; apply in_map_iff; exists y; split; [reflexivity| exact Hy]| cbn; rewrite EY; clear; lia].
      + eapply wmono_trans; [exact WM| exact WM']. }
  (* [comment removed for export] *)
  carve_frame 80%nat ST.
  do 7 step.                                   (* [comment removed for export] *)
  do 4 step.                                   (* [comment removed for export] *)
  zstep. step. zstep. step.                    (* [comment removed for export] *)
  apply (rw_C1x4_to_C4 _ _ 0 1 ltac:(lia) ltac:(lia)) in MX. change (0 + 256 * 1) with 256 in MX.
  amo_step. lits.                              (* [comment removed for export] *)
  do 4 zstep.                                  (* [comment removed for export] *)
  amo_step.                                    (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  zstep. step. if_lit.                         (* [comment removed for export] *)
  apply (rw_C4_to_C1x4 _ _ 1 1 ltac:(lia) ltac:(lia)) in MX.
  step. step. zstep.                           (* [comment removed for export] *)
  setreg 14%Z (Z_to_bv 64 (8192 * Z.of_nat (length X))) ltac:(rewrite ?Z.shiftl_mul_pow2 by (clear; lia); try apply Z_to_bv_eqm; clear -LEN40; Z.div_mod_to_equations; lia).
  step. if_cases KC; zify_cond KC.             (* [comment removed for export] *)
  { exfalso. rewrite ?Z.mod_small, ?unsigned_lit in KC by (clear -BY56 BYLB LEN40; lia). clear -KC BYLB. lia. }
  clear KC.
  (* [comment removed for export] *)
  apply (proj1 (rw_cells_app asegs _ _ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])) in FR.
  destruct FR as [TM FRS].
  lazymatch type of FRS with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + -48) in FRS by (cbn; clear; lia) end.
  (* [comment removed for export] *)
  assert (SL' : Forall (fun x => 0 <= bslot x) (X ++ [])) by (rewrite app_nil_r; exact SL).
  assert (INX0 : forall x, In x (X ++ []) -> exists y, In y X /\ baddr L y = baddr L x) by (intros x Hx; rewrite app_nil_r in Hx; exists x; split; [exact Hx| reflexivity]).
  step. if_cases KM1; zify_cond KM1.           (* [comment removed for export] *)
  - rewrite ?Z.mod_small, ?unsigned_lit in KM1 by (clear -BY56 BYLB LEN40; lia).
    eapply (CONT1 _ X [] (Z_to_bv 64 0)); try eassumption.
    + unfold qrec_mergeb, Q_BATCH_BYTES. destruct (Z.ltb_spec (8192 * Z.of_nat (length X)) bytes) as [Hl|Hl]; [exfalso; clear -KM1 Hl; lia|]. reflexivity.
    + cbn [length]. rewrite <- BY. clear; lia.
    + apply Box. eapply munch_weaken; [| exact MU]. unfold WQ, AQ_MUTEX, AQ_GCACHE. solve_sub_fpw ltac:(clear; lia).
    + rewrite <- BY. exact GC.
    + eapply chain_frame; [exact CH| exact MU| exact WM|]. apply Forall_forall. intros x Hx.
      (pose proof (proj1 (Forall_forall _ _) GEO x Hx) as ndP__; nd_pre ndP__ 4%nat; intros G1 G2 G3 G4; nd_post). unfold AIMG_HI, Q_BATCH_BYTES in *. cbn. clear -G1 G2 G3 CEIL LO. lia.
    + apply chain_nil.
    + rewrite app_nil_r. exact GEO.
    + rewrite app_nil_r. exact ND.
    + rewrite <- BY. exact BY56.
    + rewrite app_nil_r. exact LEN40.
    + rewrite app_nil_r. exact RB.
  - rewrite ?Z.mod_small, ?unsigned_lit in KM1 by (clear -BY56 BYLB LEN40; lia).
    step. step. zstep. zstep.                  (* [comment removed for export] *)
    step. if_cases KM2; zify_cond KM2.         (* [comment removed for export] *)
    + rewrite ?Z.mod_small, ?unsigned_lit in KM2 by (clear -BY56 BYLB LEN40; lia).
      eapply (CONT1 _ X [] (Z_to_bv 64 0)); try eassumption.
      * unfold qrec_mergeb, Q_BATCH_BYTES. destruct (Z.ltb_spec (bytes * 100) (8192 * Z.of_nat (length X) * 200)) as [Hl|Hl]; [exfalso; clear -KM2 Hl; lia|].
        rewrite andb_false_r. reflexivity.
      * cbn [length]. rewrite <- BY. clear; lia.
      * apply Box. eapply munch_weaken; [| exact MU]. unfold WQ, AQ_MUTEX, AQ_GCACHE. solve_sub_fpw ltac:(clear; lia).
      * rewrite <- BY. exact GC.
      * eapply chain_frame; [exact CH| exact MU| exact WM|]. apply Forall_forall. intros x Hx.
        (pose proof (proj1 (Forall_forall _ _) GEO x Hx) as ndP__; nd_pre ndP__ 4%nat; intros G1 G2 G3 G4; nd_post). unfold AIMG_HI, Q_BATCH_BYTES in *. cbn. clear -G1 G2 G3 CEIL LO. lia.
      * apply chain_nil.
      * rewrite app_nil_r. exact GEO.
      * rewrite app_nil_r. exact ND.
      * rewrite <- BY. exact BY56.
      * rewrite app_nil_r. exact LEN40.
      * rewrite app_nil_r. exact RB.
    + rewrite ?Z.mod_small, ?unsigned_lit in KM2 by (clear -BY56 BYLB LEN40; lia).
      (* [comment removed for export] *)
      do 7 zstep.                              (* [comment removed for export] *)
      step.                                    (* [comment removed for export] *)
      destruct X as [|cur R]; [exfalso; cbn [length Z.of_nat] in KM1, KM2; clear -KM1 KM2; lia|].
      eapply evtF_cut.
      { eapply (amerge_spec L RNG 0xab710 (bv_unsigned sp + -80) bytes 0 0 0 lo (cur :: R) []);
          rewrite ?unsigned_lit by (clear -SPR LO CEIL; lia); try eassumption; try reflexivity; try apply chain_nil; try (rewrite app_nil_r; eassumption).
        all: try (clear -CEIL LO SP47 SPR BY56 BYLB LEN40 MIN0; atop_facts; cbn [length]; lia).
        all: try (rewrite <- BY; clear -BY56; lia).
        - eapply chain_frame; [exact CH| exact MU| exact WM|]. apply Forall_forall. intros x Hx.
          (pose proof (proj1 (Forall_forall _ _) GEO x Hx) as ndP__; nd_pre ndP__ 4%nat; intros G1 G2 G3 G4; nd_post). unfold AIMG_HI, Q_BATCH_BYTES in *. cbn. clear -G1 G2 G3 CEIL LO. lia.
        - unfold Q_BATCH_BYTES. clear -LEN40. lia.
        - eapply (rng_sub _ _ _ _ _ RSTK); clear -LO CEIL SPR; lia. }
      cbv beta. unfold amerge_post. cbn [amerge_fun].
      destruct (merge_bq cur R) as [l e] eqn:MB.
      intros ms1 (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m1 & -> & MU' & WM' & MI' & ST' & LS' & CH' & TM' & CT').
      rewrite ?unsigned_lit in MU' by (clear -SPR LO CEIL; lia). rewrite ?unsigned_lit in ST' by (clear -SPR LO CEIL; lia).
      replace (ret_pc (Z_to_bv 64 0x35bb0)) with (Z_to_bv 64 0x35bb0) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      clear MI. rewrite app_nil_r in MU'. cbn [app] in TM', CT'.
      pose proof (merge_bq_baddr_in L R cur) as INX1. rewrite MB in INX1. cbn [fst snd] in INX1.
      assert (GEO1 : Forall (bgeom L 0xab710 (bv_unsigned sp + -80)) (l ++ e)).
      { apply Forall_forall. intros x Hx. (nd_pre (INX1 x Hx) 3%nat; intros y Hy EY; nd_post). eapply bgeom_baddr; [exact EY|]. exact (proj1 (Forall_forall _ _) GEO y Hy). }
      xport MX MU' WM' ltac:(cbn [app disjoint_from fst snd]; split; [clear -LO CEIL; lia| split; [clear; lia| split; [clear -LO CEIL; lia| eapply disj_objs_below; [exact GEO| unfold AIMG_HI; clear; lia]]]]).
      xport FRS MU' WM' ltac:(cbn [app disjoint_from fst snd]; split; [clear; lia| split; [clear -LO CEIL; lia| split; [clear; lia| eapply disj_objs_above; [exact GEO| atop_facts; clear -LO CEIL; lia]]]]).
      pose proof (merge_bq_bytes R cur) as MBY. rewrite MB in MBY. cbn [fst snd] in MBY. rewrite <- BY in MBY.
      replace (bytes - Q_BATCH_BYTES * Z.of_nat (length e)) with (batches_bytes (map fst l)) in LS' by (clear -MBY; lia).
      replace (tfirst L (cur :: R) 0) with (tfirst L l 0) in LS' by (pose proof (merge_bq_first L R cur 0) as E1; rewrite MB in E1; cbn [fst] in E1; rewrite E1; reflexivity).
      do 4 zstep.                              (* [comment removed for export] *)
      step.                                    (* [comment removed for export] *)
      eapply (CONT1 m1 l e); try eassumption.
      * unfold qrec_mergeb, Q_BATCH_BYTES. cbn [amerge_fun].
        destruct (Z.ltb_spec (8192 * Z.of_nat (length (cur :: R))) bytes) as [Hl|Hl]; [| exfalso; clear -KM1 Hl; lia].
        destruct (Z.ltb_spec (bytes * 100) (8192 * Z.of_nat (length (cur :: R)) * 200)) as [Hl2|Hl2]; [| exfalso; clear -KM2 Hl2; lia].
        cbn [andb]. exact MB.
      * clear -MBY; lia.
      * apply Box. eapply (munch_trans_w _ _ _ _ _ _ MU MU'); unfold WQ, AQ_MUTEX, AQ_GCACHE, Q_BATCH_BYTES; cbn [app].
        -- solve_sub_fpw ltac:(clear; lia).
        -- apply sub_fp_by_incl'.
           constructor; [apply Exists_exists; eexists; split; [left; reflexivity| cbn; clear; lia]|].
           constructor; [apply Exists_exists; eexists; split; [right; right; left; reflexivity| cbn; clear; lia]|].
           constructor; [apply Exists_exists; eexists; split; [left; reflexivity| cbn; clear; lia]|].
           apply Forall_forall. intros iv Hiv. apply Exists_exists. exists iv. split; [right; right; right; exact Hiv| clear; lia].
      * eapply wmono_trans; [exact WM| exact WM'].
      * apply Forall_forall. intros x Hx. (nd_pre (INX1 x Hx) 3%nat; intros y Hy EY; nd_post). rewrite <- (baddr_inj L _ _ EY). exact (proj1 (Forall_forall _ _) SL y Hy).
      * refine (proj1 (list_relations.list.NoDup_Permutation_proper _ _ _) ND). pose proof (merge_bq_slots R cur) as P. rewrite MB in P. cbn [fst snd] in P.
        apply Permutation_sym. exact P.
      * pose proof (merge_bq_sizes R cur SZ) as S1. rewrite MB in S1. cbn [fst snd] in S1. apply Forall_app in S1 as [S1 _]. exact S1.
      * clear -MBY BY56. unfold Q_BATCH_BYTES in MBY. lia.
      * pose proof (merge_bq_length R cur) as L1. rewrite MB in L1. cbn [fst snd] in L1. rewrite L1. exact LEN40.
      * apply Forall_forall. intros x Hx. (nd_pre (INX1 x Hx) 3%nat; intros y Hy EY; nd_post). rewrite <- EY. exact (proj1 (Forall_forall _ _) RB y Hy).
Qed.
End Zd2.
#[using="Type"] Theorem qrec_front : ltac:(let t := eval cbv delta [qrec_front__stmt] in qrec_front__stmt in exact t).
Proof. exact qrec_front__body. Qed.

End CANSEC1.
End TwB.
End F_aqrec.
