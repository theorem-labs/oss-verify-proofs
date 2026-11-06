From Stdlib Require Import String ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcKind.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_CTRL_KIND_NAME : Z := 0x83d98.
Definition REAC_CTRL_KIND_NAME_FRAME : Z := 16.
Definition KIND_NAME : Z := 0x9f580.
Definition QMARK : Z := 0x211e0.

Definition kind_name_addrs : list Z :=
  [0x21220; 0x21240; 0x21260; 0x21280; 0x212a0; 0x212c0; 0x212e0; 0x21300; 0x21320; 0x21340; 0x21360; 0x21380;
   0x213a0; 0x213c0].

Definition kind_name_addr (x : Z) : Z :=
  if x <=? 13 then nth (Z.to_nat x) kind_name_addrs QMARK else QMARK.

Definition kind_name_bytes : list byte :=
  concat (map (fun a => le8 (Z_to_bv 64 a)) kind_name_addrs).

Definition kind_name_strings (m : word -> option byte) : Prop :=
  forall x, 0 <= x -> bytes_at rsegs m (kind_name_addr x) (cstr_bytes (kind_name x)).

Definition reac_ctrl_kind_name_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    bytes_at rsegs m KIND_NAME kind_name_bytes ->
    kind_name_strings m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_CTRL_KIND_NAME_FRAME <= bv_unsigned sp ->
    KIND_NAME + 112 <= bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME ->
    asan_cells m -> shadow_rw m ->
    addressable m KIND_NAME 112 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME, bv_unsigned sp)] x) ->
    evt rsegs
      (fun ms' => exists (a1' a2' a3' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (kind_name_addr (bv_unsigned a0)))
                       a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp) /\
         bytes_at rsegs m' (kind_name_addr (bv_unsigned a0)) (cstr_bytes (kind_name (bv_unsigned a0))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_KIND_NAME) fc None m (seg_rom rsegs)).

Definition reac_ctrl_kind_name_contract_F : Prop :=
  forall (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    bytes_at rsegs m KIND_NAME kind_name_bytes ->
    kind_name_strings m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_CTRL_KIND_NAME_FRAME <= bv_unsigned sp ->
    KIND_NAME + 112 <= bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME ->
    asan_cells m -> shadow_rw m ->
    addressable m KIND_NAME 112 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME, bv_unsigned sp)] x) ->
    rng RNG 0x10000 0x5ee000 ->
    rng RNG (bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME) REAC_CTRL_KIND_NAME_FRAME ->
    rng RNG (shadow_addr KIND_NAME) 14 ->
    evtF rsegs RNG
      (fun ms' => exists (a1' a2' a3' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (kind_name_addr (bv_unsigned a0)))
                       a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp) /\
         bytes_at rsegs m' (kind_name_addr (bv_unsigned a0)) (cstr_bytes (kind_name (bv_unsigned a0))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_KIND_NAME) fc None m (seg_rom rsegs)).

Lemma reac_ctrl_kind_name_contract_of_F : reac_ctrl_kind_name_contract_F -> reac_ctrl_kind_name_contract.
Proof.
  unfold reac_ctrl_kind_name_contract_F, reac_ctrl_kind_name_contract. intros HF.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    HT HS ST HLO HKT HCE HSW HADR HW.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & _ & _).
  apply (evtF_evt rsegs RNG_all). apply HF; try assumption; apply rng_all;
    unfold shadow_addr, KIND_NAME, ASAN_K, REAC_CTRL_KIND_NAME_FRAME in *; lia.
Qed.

(* ---- route (C): the region form (a Theorem Labs lane 09:20Z; form rule a Theorem Labs lane 09:37Z, 09:38Z; R amended 10:33Z) ----
   Image-B twin of lib/A/Prog/reac_ctrl_kind_name_c.v's block (a working branch d68c95046c8).
   R is the set of shadow bytes the run needs PRESENT through its shadow_rw premise (the bytes it reads AND the bytes
   it stores into). For this run R is EMPTY, so each _on statement is the old one with the premise shadow_rw m DROPPED
   (no fun _ => False region). Reads: for a0 <= 13 the run's one instrumented check reads the shadow byte of the table
   entry it loads, (KIND_NAME + 8 * a0) / 8 + ASAN_K, one of the 14 shadow bytes [shadow_addr KIND_NAME,
   shadow_addr KIND_NAME + 14) = [0x8000beb0, 0x8000bebe); that byte comes from the premise addressable m KIND_NAME 112
   (B.Prog.RcAsanRT.rt_shadow_rd; AsanRT.addr_byte), not from shadow_rw: the proofs of reac_ctrl_kind_name_holds_on
   (reac_ctrl_kind_name.v) and reac_ctrl_kind_name_holds_F_on (reac_ctrl_kind_name_F.v) never use the premise.
   Stores: the run stores only its frame [sp - 16, sp), outside the shadow (the premise forall x, ... in_shadow x ->
   outside [...] x): no shadow byte. No post names shadow_rw m', so nothing else changes. The old statements above
   stay byte-identical; each follows from its _on twin in one line. reac_ctrl_kind_name_contract_of_F above keeps its
   own proof; reac_ctrl_kind_name_contract_on_of_F_on is the same proof over the _on twins. *)
Definition reac_ctrl_kind_name_contract_on : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    bytes_at rsegs m KIND_NAME kind_name_bytes ->
    kind_name_strings m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_CTRL_KIND_NAME_FRAME <= bv_unsigned sp ->
    KIND_NAME + 112 <= bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME ->
    asan_cells m ->
    addressable m KIND_NAME 112 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME, bv_unsigned sp)] x) ->
    evt rsegs
      (fun ms' => exists (a1' a2' a3' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (kind_name_addr (bv_unsigned a0)))
                       a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp) /\
         bytes_at rsegs m' (kind_name_addr (bv_unsigned a0)) (cstr_bytes (kind_name (bv_unsigned a0))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_KIND_NAME) fc None m (seg_rom rsegs)).

Lemma reac_ctrl_kind_name_contract_of_on : reac_ctrl_kind_name_contract_on -> reac_ctrl_kind_name_contract.
Proof. intros H; red; intros; apply H; assumption. Qed.

Definition reac_ctrl_kind_name_contract_F_on : Prop :=
  forall (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    bytes_at rsegs m KIND_NAME kind_name_bytes ->
    kind_name_strings m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_CTRL_KIND_NAME_FRAME <= bv_unsigned sp ->
    KIND_NAME + 112 <= bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME ->
    asan_cells m ->
    addressable m KIND_NAME 112 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME, bv_unsigned sp)] x) ->
    rng RNG 0x10000 0x5ee000 ->
    rng RNG (bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME) REAC_CTRL_KIND_NAME_FRAME ->
    rng RNG (shadow_addr KIND_NAME) 14 ->
    evtF rsegs RNG
      (fun ms' => exists (a1' a2' a3' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (kind_name_addr (bv_unsigned a0)))
                       a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp) /\
         bytes_at rsegs m' (kind_name_addr (bv_unsigned a0)) (cstr_bytes (kind_name (bv_unsigned a0))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_KIND_NAME) fc None m (seg_rom rsegs)).

Lemma reac_ctrl_kind_name_contract_F_of_on : reac_ctrl_kind_name_contract_F_on -> reac_ctrl_kind_name_contract_F.
Proof. intros H; red; intros; apply H; assumption. Qed.

Lemma reac_ctrl_kind_name_contract_on_of_F_on : reac_ctrl_kind_name_contract_F_on -> reac_ctrl_kind_name_contract_on.
Proof.
  unfold reac_ctrl_kind_name_contract_F_on, reac_ctrl_kind_name_contract_on. intros HF.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    HT HS ST HLO HKT HCE HADR HW.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & _ & _).
  apply (evtF_evt rsegs RNG_all). apply HF; try assumption; apply rng_all;
    unfold shadow_addr, KIND_NAME, ASAN_K, REAC_CTRL_KIND_NAME_FRAME in *; lia.
Qed.
