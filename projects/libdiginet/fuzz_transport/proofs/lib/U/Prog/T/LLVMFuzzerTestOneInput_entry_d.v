(* The program points inside the entry of LLVMFuzzerTestOneInput (ubsan, 0x13760 .. the first loop head 0x139dc) that
   the segment lemmas of U/Prog/T/LLVMFuzzerTestOneInput_entry_*.v meet at, and the facts they share.
   Sp = the entry sp - 240 (the frame), m0 = the entry memory. The cursor after the flags byte is FuzzIn o n
   (fuzz_u8_m's c1), the flags byte is flags. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_entry_m.
Import ListNotations.
Open Scope Z_scope.

(* The postcondition of llvm_entry_stmt at Sp. *)
Definition ent_Q (data : Z) (D : list byte) (regs0 : bvmap 5 word) (m0 : word -> option byte) (Sp lo : Z)
    (F : bvmap 5 word) (fc : bv 32) : machine_state -> Prop :=
  fun ms => llvm_out regs0 m0 Sp lo F fc ms \/
    exists (c : fuzz_in) (B' : list byte),
      llvm_head data D regs0 m0 Sp lo 0 c B' F fc ms /\
      forall A, lh_heap_ok A ->
        exists Bw', LLVMFuzzerTestOneInput_loop_m (Z.to_nat OPS_MAX) timg_ubsan B' A D c O = Some (Bw', tt).

(* The frame from the end of the prologue to the frame setup 0x13990: the struct diginet_io at sp + 0x40 (the
   four doublewords of .data.rel.ro 0x21ef8: NULL, io_send, io_recv, io_now), the saved registers at sp + 0x88. *)
Definition ent_frame (regs0 : bvmap 5 word) (j0 j60 : list byte) : list cell :=
  [CB 64 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x1482c); C8 (Z_to_bv 64 0x14b20); C8 (Z_to_bv 64 0x14bbc);
   CB 40 j60] ++ llvm_saved regs0.

(* What every point between the prologue and the frame setup holds of memory, with the world W. *)
Definition ent_mem (regs0 : bvmap 5 word) (m0 : word -> option byte) (Sp lo : Z) (W : list byte)
    (m : word -> option byte) : Prop :=
  exists j0 j60 : list byte,
    stk rsegs m lo Sp /\ mem_inv rsegs m /\ wmem rsegs m W /\
    munch [(lo, Sp + 240); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m0 m /\ wmono rsegs m0 m /\
    rw_cells rsegs m Sp (ent_frame regs0 j0 j60).

(* The facts on Sp and lo every segment uses. *)
Definition ent_num (Sp lo : Z) : Prop :=
  Sp mod 16 = 0 /\ 0 <= lo /\ lo + LH_K <= Sp /\ Sp + LH_FRAME <= 2 ^ 63 /\ W_BASE_UBSAN + W_LEN <= lo.

(* The input buffer at the entry (empty, or a block below the window and off the world). *)
Definition ent_dat (data : Z) (D : list byte) (m0 : word -> option byte) (lo : Z) : Prop :=
  D = [] \/ (0 < data /\ data + Z.of_nat (length D) <= lo /\ off_world data (Z.of_nat (length D)) /\
             bytes_at rsegs m0 data D).

(* 0x137f8, after the flags byte: s0 = the cursor's address, s7 its n, s2 the flags byte; the world as at the
   entry. *)
Definition ent_s7f8 (data : Z) (regs0 : bvmap 5 word) (m0 : word -> option byte) (Sp lo : Z) (B : list byte)
    (o n flags : Z) (F : bvmap 5 word) (fc : bv 32) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (m : word -> option byte),
    ms = MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 (Z_to_bv 64 (data + o)) s1
                 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 flags) s3 s4 s5 s6 (Z_to_bv 64 n) s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x137f8) fc None m (seg_rom rsegs) /\
    ent_mem regs0 m0 Sp lo B m.

(* 0x13854, after memcpy(g_cfg.desk_mac, DESK, 6): s1 = &g_cfg, s9 = &g_fail_next, s3 = flags bit 2; the world
   is the model's B6 (ent_W6). *)
Definition ent_s854 (data : Z) (regs0 : bvmap 5 word) (m0 : word -> option byte) (Sp lo : Z) (B1 : list byte)
    (o n flags : Z) (F : bvmap 5 word) (fc : bv 32) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s10 s11 t3 t4 t5 t6 : word)
         (m : word -> option byte),
    ms = MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 (Z_to_bv 64 (data + o))
                 (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_cfg)) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 flags)
                 (Z_to_bv 64 (Z.land (Z.shiftr flags 2) 1)) s4 s5 s6 (Z_to_bv 64 n) s8
                 (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next)) s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x13854) fc None m (seg_rom rsegs) /\
    ent_mem regs0 m0 Sp lo (ent_W6 flags B1) m.

(* 0x138d4, the config read (the ladder joins here): a0 / a1 = the two bytes of max_body's u16, s5 / s7 the
   cursor c10 = cur o n 14; the world is the model's B14 (ent_W14). *)
Definition ent_s8d4 (data : Z) (D : list byte) (regs0 : bvmap 5 word) (m0 : word -> option byte) (Sp lo : Z)
    (B1 : list byte) (o n flags : Z) (F : bvmap 5 word) (fc : bv 32) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 s0 a2 a3 a4 a5 a6 a7 s4 s6 s8 s10 s11 t3 t4 t5 t6 : word)
         (m : word -> option byte),
    ms = MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 s0
                 (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_cfg)) (Z_to_bv 64 (cbyte D o n 12)) (Z_to_bv 64 (cbyte D o n 13))
                 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 flags)
                 (Z_to_bv 64 (Z.land (Z.shiftr flags 2) 1)) s4 (Z_to_bv 64 (data + fi_off (cur o n 14))) s6
                 (Z_to_bv 64 (fi_n (cur o n 14))) s8
                 (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next)) s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x138d4) fc None m (seg_rom rsegs) /\
    ent_mem regs0 m0 Sp lo (ent_W14 (cbyte D o n) (ent_W6 flags B1)) m.

(* 0x13988, diginet_session_init returned rc in a0: s8 = &M, s10 = &g_s; the world is init's B25 *)
Definition ent_s988 (data : Z) (regs0 : bvmap 5 word) (m0 : word -> option byte) (Sp lo : Z) (o n rc : Z)
    (B25 : list byte) (F : bvmap 5 word) (fc : bv 32) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s11 t3 t4 t5 t6 : word) (m : word -> option byte),
    ms = MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 s0
                 (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_cfg)) (Z_to_bv 64 rc) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4
                 (Z_to_bv 64 (data + fi_off (cur o n 14))) s6 (Z_to_bv 64 (fi_n (cur o n 14)))
                 (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next))
                 (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x13988) fc None m (seg_rom rsegs) /\
    ent_mem regs0 m0 Sp lo B25 m.

(* the struct diginet_io at sp + 0x40 as diginet_session_init's contract asks for it *)
Lemma ent_io_bytes : forall m Sp j0 j60 rest,
  rw_cells rsegs m Sp ([CB 64 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x1482c); C8 (Z_to_bv 64 0x14b20);
                        C8 (Z_to_bv 64 0x14bbc); CB 40 j60] ++ rest) ->
  bytes_at rsegs m (Sp + 64) (put 8 0 ++ put 8 0x1482c ++ put 8 0x14b20 ++ put 8 0x14bbc).
Proof.
  intros m Sp j0 j60 rest [[Hwf Hb] _].
  cbn [app cells_wf cell_wf] in Hwf. destruct Hwf as [Hj0 _].
  cbn [app cells_bytes cbytes] in Hb. rewrite !le8_put in Hb.
  apply (proj1 (bytes_at_app rsegs m Sp j0 _)) in Hb. destruct Hb as [_ Hb].
  rewrite Hj0 in Hb. change (Z.of_nat 64) with 64 in Hb.
  rewrite !app_assoc in Hb. rewrite !app_assoc.
  apply (proj1 (bytes_at_app rsegs m _ _ _)) in Hb. destruct Hb as [Hb _].
  apply (proj1 (bytes_at_app rsegs m _ _ _)) in Hb. destruct Hb as [Hb _].
  exact Hb.
Qed.

(* ---------------------------------------------------------------- shared facts *)

Lemma ent_c1_facts : forall D o n flags,
  fuzz_u8_m D (fuzz_in_m (Z.of_nat (length D))) = (FuzzIn o n, flags) ->
  0 <= o /\ 0 <= n /\ o + n = Z.of_nat (length D) /\ 0 <= flags < 256 /\
  (Z.of_nat (length D) = 0 -> o = 0 /\ n = 0 /\ flags = 0) /\
  (Z.of_nat (length D) <> 0 -> o = 1 /\ n = Z.of_nat (length D) - 1 /\ flags = at8 D 0).
Proof.
  intros D o n flags H. unfold fuzz_u8_m, fuzz_in_m in H. cbn [fi_n fi_off] in H.
  destruct (Z.eqb_spec (Z.of_nat (length D)) 0) as [E|E].
  - injection H as Ho Hn Hf. subst o n flags.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [intros _; lia | intros C; lia].
  - injection H as Ho Hn Hf. subst o n flags.
    pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat 0) D (b8 0))) as R. unfold bv_modulus in R.
    change (2 ^ Z.of_N 8) with 256 in R. unfold at8, bz.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [intros C; lia | intros _; split; [lia | split; [lia | reflexivity]]].
Qed.

(* the length of a CB cell *)
Lemma ent_cb_len : forall m A n j cs, rw_cells rsegs m A (CB n j :: cs) -> length j = n.
Proof. intros m A n j cs [[[Hc _] _] _]. exact Hc. Qed.

(* the exit's frame: the 136 bytes below the saved registers as one cell *)
Lemma ent_merge6 : forall m A x1 x2 x3 x4 x5 x6 post,
  rw_cells rsegs m A (x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: post) ->
  rw_cells rsegs m A (CB (cells_size [x1; x2; x3; x4; x5; x6]) (cells_bytes [x1; x2; x3; x4; x5; x6]) :: post).
Proof.
  intros m A x1 x2 x3 x4 x5 x6 post H.
  exact (rw_cells_merge rsegs m A [] [x1; x2; x3; x4; x5; x6] post H).
Qed.

(* llvm_out from a frame of the prologue's shape *)
Lemma ent_out : forall regs0 m0 Sp lo F fc m j0 j60 v0 v1 v2 v3
    (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  Sp mod 16 = 0 -> lo <= Sp -> Sp + LH_FRAME <= 2 ^ 63 -> mem_inv rsegs m ->
  munch [(lo, Sp + LH_FRAME); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m0 m -> wmono rsegs m0 m ->
  rw_cells rsegs m Sp ([CB 64 j0; C8 v0; C8 v1; C8 v2; C8 v3; CB 40 j60] ++ llvm_saved regs0) ->
  llvm_out regs0 m0 Sp lo F fc
    (MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 LH_OUT) fc None m (seg_rom rsegs)).
Proof.
  intros regs0 m0 Sp lo F fc m j0 j60 v0 v1 v2 v3 ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7
    s8 s9 s10 s11 t3 t4 t5 t6 H16 HLO HSP MI MU WMO FR.
  cbn [app] in FR. apply ent_merge6 in FR. cbn [cells_size csize Nat.add] in FR.
  unfold llvm_out. do 28 eexists. exists m, (cells_bytes [CB 64 j0; C8 v0; C8 v1; C8 v2; C8 v3; CB 40 j60]).
  split; [reflexivity|].
  split; [exact H16|]. split; [exact HLO|]. split; [exact HSP|]. split; [exact MI|].
  split; [exact MU|]. split; [exact WMO|]. split; [exact (ent_cb_len _ _ _ _ _ FR)|]. exact FR.
Qed.

(* the join 0x138d4 from the machine's registers and world, the values given by equations *)
Lemma ent_s8d4_intro : forall data D regs0 m0 Sp lo B1 o n flags F fc ms
    (ra t0 t1 t2 s0 a2 a3 a4 a5 a6 a7 s4 s6 s8 s10 s11 t3 t4 t5 t6 : word) (m : word -> option byte)
    (va0 va1 vs5 vs7 : Z) (W j0 j60 : list byte),
  ms = MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 s0
               (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_cfg)) (Z_to_bv 64 va0) (Z_to_bv 64 va1)
               a2 a3 a4 a5 a6 a7 (Z_to_bv 64 flags)
               (Z_to_bv 64 (Z.land (Z.shiftr flags 2) 1)) s4 (Z_to_bv 64 vs5) s6
               (Z_to_bv 64 vs7) s8
               (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next)) s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x138d4) fc None m (seg_rom rsegs) ->
  va0 = cbyte D o n 12 -> va1 = cbyte D o n 13 -> vs5 = data + fi_off (cur o n 14) -> vs7 = fi_n (cur o n 14) ->
  stk rsegs m lo Sp -> mem_inv rsegs m -> wmem rsegs m W -> W = ent_W14 (cbyte D o n) (ent_W6 flags B1) ->
  munch [(lo, Sp + 240); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m0 m -> wmono rsegs m0 m ->
  rw_cells rsegs m Sp (ent_frame regs0 j0 j60) ->
  ent_s8d4 data D regs0 m0 Sp lo B1 o n flags F fc ms.
Proof.
  intros data D regs0 m0 Sp lo B1 o n flags F fc ms ra t0 t1 t2 s0 a2 a3 a4 a5 a6 a7 s4 s6 s8 s10 s11
    t3 t4 t5 t6 m va0 va1 vs5 vs7 W j0 j60 -> -> -> -> -> ST MI WM -> MU WMO FR.
  unfold ent_s8d4. do 20 eexists. exists m. split; [reflexivity|].
  exists j0, j60. split; [exact ST|]. split; [exact MI|]. split; [exact WM|]. split; [exact MU|].
  split; [exact WMO|]. exact FR.
Qed.

(* ---------------------------------------------------------------- tactics *)

(* a branch whose condition c is b: tac proves c = b *)
Ltac ebr b tac :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b by (symmetry; tac); cbv iota
  end.

(* the current memory of the goal *)
Ltac ent_mem_of := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => mm end.
