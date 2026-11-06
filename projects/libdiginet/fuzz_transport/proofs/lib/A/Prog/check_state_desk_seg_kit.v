(* check_state_desk_seg_kit: what the footprint runs (lib/Lib/ExecF.v evtF, StepF's step) of check_state_desk in
   image A share (fuzz_transport.asan e89be137db17, entry 0x8538c = transport_sigma TS_check_state_desk, 171 words;
   listing lib/A/Prog/DgnTransportList.v, the slots of AF_check_state_desk): the image addresses as names, the
   memory, footprint, bound and separation bundles csd_mem / csd_rng / csd_bnd / csd_sep, the prologue csd_pro_F
   (0x8538c .. 0x853a8), and the tactic csd_chk1 for one instrumented check of a 1-byte load.

   The runs, with the model steps of the plain walk lib/Prog/T/check_state_desk.v:
     csd_run1_F (check_state_desk_seg_runs.v)  0x8538c .. the call of bcmp at 0x85540: the frame (sp = sp - 48;
                 ra, s0 .. s4 stored at sp + 40 .. sp + 0), then csd_head_F (check_state_desk_seg_head.v): GOT.desk
                 <= OW.desk, the check of the 4-byte load at p + 40 and n->mac_offset = OW.desk_off, the check of the
                 8-byte load at p + 32 and the personality test, the device and strips bytes when n->personality is
                 not NULL, the check of the 8-byte load at p + 24 (s0 = n->announce, not NULL); then csd_loops_F
                 (check_state_desk_seg_loops.v): the two inlined spec_strz_len loops over OW.desk_body + 15 and + 24
                 (s2 = vn, s3 = nn); then csd_call1_F: a0 = announce, a1 = OW.desk_body + 15, a2 = vn.
     csd_mid_F (check_state_desk_seg_tail.v)  the return 0x85544 (bcmp answered 0) .. the call of bcmp at 0x85574:
                 the check of the 1-byte load at announce + vn and the test version[vn] = 0; then a0 = announce + 10,
                 a1 = OW.desk_body + 24, a2 = nn.
     csd_ret_F (check_state_desk_seg_tail.v)  the return 0x85578 (bcmp answered 0) .. the `ret` at 0x855b4: the
                 check of the 1-byte load at announce + 10 + nn, the test name[nn] = 0, and the epilogue.
   lib/A/Prog/check_state_desk_cgW.v carries the three runs into SRr, cuts the two bcmp calls between them, and
   proves the statement of lib/A/Prog/check_state_desk_cg.v.
   Every instrumented check reads the shadow byte k of the loaded address a at (a >> 3) + 0x7fff8000 and goes on when
   k = 0, or, for a 1-byte load, when a & 7 < k (the handler's `blt` back to the load); csd_mem gives k = 0 for the
   three fields of n (whole granules of the 72 bytes at p, p mod 8 = 0) and for the four granules of personalities[],
   SPEC_C24 and SPEC_PC the code reads, and a k the check accepts for each byte of the heap frame and of the
   announce. Every test that goes to the trap at 0x855b8 compares the values check_state_desk_m compares; the walk
   hands the model's facts to the runs as hypotheses. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA AsanKAProof TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas TCb TImg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require check_state_desk.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module DS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module PW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.check_state_desk.

(* ---- the addresses: the entry and the trampoline are the listing's names ---- *)

Definition CSD_ENTRY : Z := transport_sigma TS_check_state_desk.
Definition CSD_BCMP : Z := transport_sigma TS___interceptor_trampoline_bcmp.
(* The return addresses of the two bcmp calls (0x85540 + 4, 0x85574 + 4). *)
Definition CSD_RET1 : Z := 0x85544.
Definition CSD_RET2 : Z := 0x85578.
(* The records the personality test may name (TImgA.v timg_A: personalities 0xa3ea0 with 24-byte elements,
   SPEC_C24 0xa3da0, SPEC_PC 0xa3dc0), and the two bytes the device and strips tests read in each: the element's
   bytes 16 and 17, the desk's bytes 8 and 9. *)
Definition CSD_PERS0 : Z := TI.ti_personalities timg_A.
Definition CSD_PERS1 : Z := CSD_PERS0 + 24.
Definition CSD_C24 : Z := TI.ti_spec_c24 timg_A.
Definition CSD_PC : Z := TI.ti_spec_pc timg_A.
Definition CSD_P0 : Z := CSD_PERS0 + 16.
Definition CSD_P1 : Z := CSD_PERS1 + 16.
Definition CSD_D0 : Z := CSD_C24 + 8.
Definition CSD_D1 : Z := CSD_PC + 8.

Lemma csd_entry_val : CSD_ENTRY = 0x8538c.
Proof. reflexivity. Qed.

(* The 48-byte frame: s4, s3, s2, s1, s0 and ra at sp - 48 .. sp - 8 (`sd ra,40(sp)` 0x85390 .. `sd s4,0(sp)`
   0x853a4, after `addi sp,sp,-48`). *)
Definition csd_fr (c4 c3 c2 c1 c0 cra : word) : list cell := [C8 c4; C8 c3; C8 c2; C8 c1; C8 c0; C8 cra].

(* ---- the bundles ---- *)

(* What the runs read, at the memory m: the two runtime cells of the shadow base; the world's GOT.desk, OW.desk,
   OW.desk_off, OW.desk_p, OW.desk_body (TWorldA.v TMAP_A rows GOT and OW); the 72 bytes NB of the notice at p and
   the shadow byte 0 of its granules p + 24, p + 32, p + 40; the device and strips bytes of personalities[0], [1],
   SPEC_C24 and SPEC_PC, each granule's shadow byte 0; the heap frame's bytes with a shadow byte the check accepts
   at each of them; the bytes version[vn] and name[nn] of the announce, 0, with a shadow byte the check accepts. *)
Definition csd_mem (m : word -> option byte) (p : Z) (NB Bw : list byte) (fr : TI.tframe) (vn nn : nat) : Prop :=
  bytes_at rsegs m GOT_CELL_K (le8 (wa CELL_K)) /\
  bytes_at rsegs m CELL_K (le8 (wa ASAN_K)) /\
  bytes_at rsegs m (TA_GOT + 208) (TW.sub Bw TW.A_GOT_desk 4) /\
  bytes_at rsegs m (TA_OW + 208) (TW.sub Bw TW.A_OW_desk 4) /\
  bytes_at rsegs m (TA_OW + 232) (TW.sub Bw TW.A_OW_desk_off 4) /\
  bytes_at rsegs m (TA_OW + 240) (TW.sub Bw TW.A_OW_desk_p 8) /\
  bytes_at rsegs m (TA_OW + 248) (TW.sub Bw TW.A_OW_desk_body 8) /\
  length NB = 72%nat /\ bytes_at rsegs m p NB /\
  (forall j, 3 <= j <= 5 -> mrd rsegs m (wa ((p + 8 * j) / 8 + ASAN_K)) = Some (Z_to_bv 8 0)) /\
  bytes_at rsegs m CSD_P0 [Z_to_bv 8 1; Z_to_bv 8 24] /\ bytes_at rsegs m CSD_P1 [Z_to_bv 8 0; Z_to_bv 8 8] /\
  bytes_at rsegs m CSD_D0 [Z_to_bv 8 1; Z_to_bv 8 24] /\ bytes_at rsegs m CSD_D1 [Z_to_bv 8 0; Z_to_bv 8 8] /\
  (forall c, In c [CSD_P0; CSD_P1; CSD_D0; CSD_D1] -> mrd rsegs m (wa (c / 8 + ASAN_K)) = Some (Z_to_bv 8 0)) /\
  bytes_at rsegs m (TI.tf_addr fr) (TI.tf_bytes fr) /\
  (forall x, TI.tf_addr fr <= x < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr)) ->
     exists k : byte, mrd rsegs m (wa (x / 8 + ASAN_K)) = Some k /\ (bv_signed k = 0 \/ x mod 8 < bv_signed k)) /\
  (forall x, x = TW.u_at NB 24 8 + Z.of_nat vn \/ x = TW.u_at NB 24 8 + 10 + Z.of_nat nn ->
     mrd rsegs m (wa x) = Some (Z_to_bv 8 0) /\
     exists k : byte, mrd rsegs m (wa (x / 8 + ASAN_K)) = Some k /\ (bv_signed k = 0 \/ x mod 8 < bv_signed k)).

(* The addresses csd_mem speaks of: a memory that agrees with another one on these keeps csd_mem. *)
Definition csd_addr (p : Z) (NB : list byte) (fr : TI.tframe) (vn nn : nat) (a : Z) : Prop :=
  (GOT_CELL_K <= a < GOT_CELL_K + 8) \/ (CELL_K <= a < CELL_K + 8) \/
  (TA_GOT + 208 <= a < TA_GOT + 212) \/ (TA_OW + 208 <= a < TA_OW + 256) \/
  (p <= a < p + 72) \/
  (exists j, 3 <= j <= 5 /\ a = (p + 8 * j) / 8 + ASAN_K) \/
  (exists c, In c [CSD_P0; CSD_P1; CSD_D0; CSD_D1] /\ (c <= a < c + 2 \/ a = c / 8 + ASAN_K)) \/
  (TI.tf_addr fr <= a < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr))) \/
  (exists x, TI.tf_addr fr <= x < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr)) /\ a = x / 8 + ASAN_K) \/
  (exists x, (x = TW.u_at NB 24 8 + Z.of_nat vn \/ x = TW.u_at NB 24 8 + 10 + Z.of_nat nn) /\
             (a = x \/ a = x / 8 + ASAN_K)).

(* The footprint the runs need: the frame, every multi-byte load's range, and each byte csd_mem speaks of. *)
Definition csd_rng (RNG : ExecF.footprint) (sp p : Z) (NB : list byte) (fr : TI.tframe) (vn nn : nat) : Prop :=
  ExecF.rng RNG (sp - 48) 48 /\ ExecF.rng RNG GOT_CELL_K 8 /\ ExecF.rng RNG CELL_K 8 /\
  ExecF.rng RNG (TA_GOT + 208) 4 /\ ExecF.rng RNG (TA_OW + 208) 48 /\ ExecF.rng RNG p 72 /\
  (forall a, csd_addr p NB fr vn nn a -> ExecF.rng RNG a 1).

(* Every byte csd_mem speaks of lies outside the 48 bytes the prologue writes. *)
Definition csd_sep (sp p : Z) (NB : list byte) (fr : TI.tframe) (vn nn : nat) : Prop :=
  forall a, csd_addr p NB fr vn nn a -> 0 <= a < 2 ^ 64 /\ (a + 1 <= sp - 48 \/ sp <= a).

(* ---- small facts ---- *)

Lemma csd_bytes_ext : forall m m' A bs,
  (forall i, 0 <= i < Z.of_nat (length bs) -> mrd rsegs m' (wa (A + i)) = mrd rsegs m (wa (A + i))) ->
  bytes_at rsegs m A bs -> bytes_at rsegs m' A bs.
Proof.
  intros m m' A bs E (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite E by lia. exact (H i Hi).
Qed.

Lemma csd_mem_ext : forall m m' p NB Bw fr vn nn,
  (forall a, csd_addr p NB fr vn nn a -> mrd rsegs m' (wa a) = mrd rsegs m (wa a)) ->
  csd_mem m p NB Bw fr vn nn -> csd_mem m' p NB Bw fr vn nn.
Proof.
  intros m m' p NB Bw fr vn nn E
    (M1 & M2 & M3 & M4 & M5 & M6 & M7 & ML & M8 & M9 & M10 & M11 & M12 & M13 & M14 & M15 & M16 & M17).
  assert (LS : forall k n, Z.of_nat (length (TW.sub Bw k n)) <= Z.of_nat n)
    by (intros k n; unfold TW.sub; rewrite length_firstn; lia).
  assert (IN : forall c, In c [CSD_P0; CSD_P1; CSD_D0; CSD_D1] -> forall i, 0 <= i < 2 ->
            csd_addr p NB fr vn nn (c + i))
    by (intros c Hc i Hi; do 6 right; left; exists c; split; [exact Hc | left; lia]).
  split; [apply (csd_bytes_ext m m'); [|exact M1]; intros i Hi; apply E; left;
          rewrite length_le8 in Hi; lia|].
  split; [apply (csd_bytes_ext m m'); [|exact M2]; intros i Hi; apply E; right; left;
          rewrite length_le8 in Hi; lia|].
  split; [apply (csd_bytes_ext m m'); [|exact M3]; intros i Hi; apply E; right; right; left;
          pose proof (LS TW.A_GOT_desk 4%nat); lia|].
  split; [apply (csd_bytes_ext m m'); [|exact M4]; intros i Hi; apply E; right; right; right; left;
          pose proof (LS TW.A_OW_desk 4%nat); lia|].
  split; [apply (csd_bytes_ext m m'); [|exact M5]; intros i Hi; apply E; right; right; right; left;
          pose proof (LS TW.A_OW_desk_off 4%nat); lia|].
  split; [apply (csd_bytes_ext m m'); [|exact M6]; intros i Hi; apply E; right; right; right; left;
          pose proof (LS TW.A_OW_desk_p 8%nat); lia|].
  split; [apply (csd_bytes_ext m m'); [|exact M7]; intros i Hi; apply E; right; right; right; left;
          pose proof (LS TW.A_OW_desk_body 8%nat); lia|].
  split; [exact ML|].
  split; [apply (csd_bytes_ext m m'); [|exact M8]; intros i Hi; apply E; do 4 right; left; lia|].
  split.
  { intros j Hj. rewrite E; [exact (M9 j Hj)|]. do 5 right; left. exists j. split; [exact Hj | reflexivity]. }
  split; [apply (csd_bytes_ext m m'); [|exact M10]; intros i Hi; apply (E _ (IN CSD_P0 ltac:(cbn; tauto) i
          ltac:(cbn [length] in Hi; lia)))|].
  split; [apply (csd_bytes_ext m m'); [|exact M11]; intros i Hi; apply (E _ (IN CSD_P1 ltac:(cbn; tauto) i
          ltac:(cbn [length] in Hi; lia)))|].
  split; [apply (csd_bytes_ext m m'); [|exact M12]; intros i Hi; apply (E _ (IN CSD_D0 ltac:(cbn; tauto) i
          ltac:(cbn [length] in Hi; lia)))|].
  split; [apply (csd_bytes_ext m m'); [|exact M13]; intros i Hi; apply (E _ (IN CSD_D1 ltac:(cbn; tauto) i
          ltac:(cbn [length] in Hi; lia)))|].
  split.
  { intros c Hc. rewrite E; [exact (M14 c Hc)|]. do 6 right; left. exists c. split; [exact Hc | right; reflexivity]. }
  split; [apply (csd_bytes_ext m m'); [|exact M15]; intros i Hi; apply E; do 7 right; left; lia|].
  split.
  { intros x Hx. destruct (M16 x Hx) as (k & Hk & Ok). exists k. split; [|exact Ok].
    rewrite E; [exact Hk|]. do 8 right; left. exists x. split; [exact Hx | reflexivity]. }
  intros x Hx. destruct (M17 x Hx) as (Hb & k & Hk & Ok). split.
  - rewrite E; [exact Hb|]. do 9 right. exists x. split; [exact Hx | left; reflexivity].
  - exists k. split; [|exact Ok]. rewrite E; [exact Hk|]. do 9 right. exists x. split; [exact Hx | right; reflexivity].
Qed.

(* The prologue's write keeps csd_mem: every byte it speaks of lies outside [sp - 48, sp). *)
Lemma csd_mem_frame : forall sp m m1 p NB Bw fr vn nn,
  csd_sep sp p NB fr vn nn -> munch [(sp + -48, sp)] m m1 ->
  csd_mem m p NB Bw fr vn nn -> csd_mem m1 p NB Bw fr vn nn.
Proof.
  intros sp m m1 p NB Bw fr vn nn SEP MU MEM. apply (csd_mem_ext m m1); [|exact MEM].
  intros a Ha. destruct (SEP a Ha) as [Hb Hd].
  unfold mrd. rewrite (MU (wa a)); [reflexivity|].
  cbn [outside]. rewrite wa_unsigned by lia. split; [lia | exact I].
Qed.

(* A load of n bytes inside a byte span. *)
Lemma csd_rdn : forall m a bs (k : Z) (n : nat) addr, bytes_at rsegs m a bs -> 0 <= k ->
  (Z.to_nat k + n <= length bs)%nat -> addr = a + k -> ov_read_bytes rsegs m (Z_to_bv 64 addr) n = Some (TW.sub bs k n).
Proof.
  intros m a bs k n addr H Hk Hn ->. change (Z_to_bv 64 (a + k)) with (wa (a + k)).
  exact (bytes_at_read rsegs m a bs k n H Hk Hn).
Qed.

(* A whole byte span, read from its start. *)
Lemma csd_rdall : forall m a bs (n : nat), bytes_at rsegs m a bs -> length bs = n ->
  ov_read_bytes rsegs m (wa a) n = Some bs.
Proof.
  intros m a bs n H L. replace (wa a) with (wa (a + 0)) by (rewrite Z.add_0_r; reflexivity).
  rewrite (bytes_at_read rsegs m a bs 0 n H ltac:(lia)) by (rewrite L; change (Z.to_nat 0) with 0%nat; lia).
  change (Z.to_nat 0) with 0%nat. cbn [skipn]. f_equal. apply firstn_all2. lia.
Qed.

(* One byte of a span. *)
Lemma csd_rd1 : forall m a bs (j : nat) addr, bytes_at rsegs m a bs -> (j < length bs)%nat ->
  addr = a + Z.of_nat j -> ov_read_bytes rsegs m (Z_to_bv 64 addr) 1 = Some [nth j bs (Z_to_bv 8 0)].
Proof. intros m a bs j addr H Hj ->. apply rd1. exact (bytes_nth m a bs j H Hj). Qed.

(* The world's sub lists have their length. *)
Lemma csd_len_sub : forall Bw k n, 0 <= k -> k + Z.of_nat n <= Z.of_nat (length Bw) -> length (TW.sub Bw k n) = n.
Proof. intros Bw k n Hk Hn. apply TWL.length_sub; lia. Qed.

(* ---- the prologue: 0x8538c .. 0x853a8 ---- *)

Lemma csd_pro_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp ->
    ExecF.rng RNG (bv_unsigned sp - 48) 48 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m1,
         ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x853a8) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
         stk rsegs m1 lo (bv_unsigned sp + -48) /\
         rw_cells rsegs m1 (bv_unsigned sp + -48) (csd_fr s4 s3 s2 s1 s0 ra))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CSD_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ST LO RFR.
  rewrite csd_entry_val.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  do 7 step.
  lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => apply evtF_done; exists mm end.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact ST|]. exact FR.
Qed.

(* The arithmetic every run needs: the notice, the heap frame and the announce lie in the lower half, the notice is
   8-aligned, and the world has its W_LEN bytes. *)
Definition csd_bnd (p : Z) (NB Bw : list byte) (fr : TI.tframe) : Prop :=
  0 < p /\ p mod 8 = 0 /\ p + 72 <= 2 ^ 63 /\ length Bw = Z.to_nat TW.W_LEN /\
  0 < TI.tf_addr fr /\ TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr)) <= 2 ^ 63 /\
  0 < TW.u_at NB 24 8 /\ TW.u_at NB 24 8 + 20 <= 2 ^ 63.

(* A test that is not taken: its condition is false. *)
Ltac br_false tac :=
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false; [cbv iota | symmetry; tac]
  end.
(* A test on closed values. *)
Ltac brF b := lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b by (vm_compute; reflexivity); cbv iota
  end.

Ltac csd_prep MEM RNGH BND :=
  destruct MEM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & ML & M8 & M9 & M10 & M11 & M12 & M13 & M14 & M15 & M16 & M17);
  destruct RNGH as (RFR & RGC & RCK & RGD & ROW & RP & RA);
  destruct BND as (BP0 & BP8 & BP63 & LBW & BF0 & BF63 & BA0 & BA63).

(* The instrumented check of a 1-byte load at X, whose address the step before (`add`) leaves in a register (norm
   puts it in the form Z_to_bv 64 X): `srli`, `add` of the shadow base, `lb` of the shadow byte k (MK, its footprint
   RS), `bnez`; when k <> 0 the handler's `andi 7` and `blt` back to the load, taken because X mod 8 < k (SK). BODY
   is the load. *)
Ltac csd_chk1 norm X MK SK RS BODY :=
  step; norm;
  step; let g := fresh "g" in let G := fresh "G" in
  gen_shr (Z_to_bv 64 X) g G; rewrite (unsigned_lit X) in G by lia;
  step; let h := fresh "h" in let H := fresh "H" in gen_addi g h H;
  let RH := fresh "RH" in pose proof (rng_sub' _ _ _ (bv_unsigned h) 1 RS ltac:(lia)) as RH;
  let R := fresh "R" in pose proof (rdw0 _ h _ _ MK ltac:(lia)) as R; step; clear R;
  step; rewrite sxb_eq0;
  lazymatch type of MK with
  | mrd _ _ _ = Some ?k =>
      let C := fresh "C" in destruct SK as [C|C];
      [ rewrite (proj2 (Z.eqb_eq _ _) C); cbn [negb]; cbv iota; apply BODY
      | rewrite (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb]; cbv iota;
        step; rewrite land7, (unsigned_lit X) by lia;
        step; rewrite (lts_low (X mod 8) k ltac:(lia)), (proj2 (Z.ltb_lt _ _) C); cbv iota; apply BODY ]
  end.

