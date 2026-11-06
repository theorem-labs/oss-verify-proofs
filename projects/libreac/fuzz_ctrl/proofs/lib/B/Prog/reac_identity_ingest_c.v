From Stdlib Require Import ZArith NArith List Bool.
From Stdlib Require Import Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcIdentModel.
Import ListNotations.
Open Scope Z_scope.

(* reac_identity_ingest in the asan-ubsan image. The code is the asan image's with UBSan checks added (pointer
   overflow of p + i and id + k, a null p, the alignment of id for the u16 stores); each check traps with `unimp` at
   0x88268. The premises are the asan image's: they make every check pass. *)
Definition REAC_IDENTITY_INGEST : Z := 0x87e0c.
Definition REAC_IDENTITY_INGEST_FRAME : Z := 32.

Definition ingest_refused (id p len : Z) : bool := (id =? 0) || (negb (len =? 0) && (p =? 0)).

Definition ingest_ret (id ad p len : Z) (idb pb : list byte) : Z :=
  if ingest_refused id p len then -1 else fst (ING idb ad pb).

Definition reac_identity_ingest_W (sp id : Z) : list ivl :=
  [(sp - REAC_IDENTITY_INGEST_FRAME, sp); (id, id + 38)].

Definition reac_identity_ingest_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo id ad p len : Z) (idb pb : list byte)
    : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (ingest_ret id ad p len idb pb))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch (reac_identity_ingest_W (bv_unsigned sp) id) m m' /\ wmono rsegs m m'
    /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp)
    /\ (ingest_refused id p len = true ->
          munch [(bv_unsigned sp - REAC_IDENTITY_INGEST_FRAME, bv_unsigned sp)] m m')
    /\ (ingest_refused id p len = false -> rw_cells rsegs m' id [CB 38 (snd (ING idb ad pb))]).

Definition reac_identity_ingest_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo id ad p len : Z) (idb pb : list byte),
    a0 = Z_to_bv 64 id -> a1 = Z_to_bv 64 ad -> a2 = Z_to_bv 64 p -> a3 = Z_to_bv 64 len ->
    0 <= id < 2^64 -> 0 <= ad < 65536 -> 0 <= p < 2^64 -> 0 <= len < 2^64 ->
    (id <> 0 -> id mod 2 = 0 /\ rw_cells rsegs m id [CB 38 idb]) ->
    length pb = Z.to_nat len ->
    (0 < len -> p <> 0 -> bytes_at rsegs m p pb) ->
    (id <> 0 -> 0 < len -> p <> 0 -> p + len <= id \/ id + 38 <= p) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_IDENTITY_INGEST_FRAME <= bv_unsigned sp ->
    (id <> 0 -> id + 38 <= bv_unsigned sp - REAC_IDENTITY_INGEST_FRAME \/ bv_unsigned sp <= id) ->
    (0 < len -> p <> 0 -> p + len <= bv_unsigned sp - REAC_IDENTITY_INGEST_FRAME \/ bv_unsigned sp <= p) ->
    asan_cells m -> shadow_rw m ->
    (id <> 0 -> addressable m id 38) ->
    (0 < len -> p <> 0 -> addressable m p len) ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside (reac_identity_ingest_W (bv_unsigned sp) id) x) ->
    evt rsegs
      (reac_identity_ingest_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo id ad p len idb pb)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_IDENTITY_INGEST) fc None m (seg_rom rsegs)).

(* Footprint form (RECIPE.md step 1 (a working note, not in this delivery)): the same run as an ExecF.evtF under a footprint RNG, with one rng
   premise per region the run reads or writes: the 32-byte frame; the GOT cell and the runtime cell that hold the
   shadow offset; when id is not 0, the 38 bytes at id and their shadow bytes; when len > 0 and p is not 0, the len
   bytes at p and their shadow bytes. Shadow spans are byte-exact ((x >> 3) + ASAN_K per checked byte).
   reac_identity_ingest_contract_of_F gives the old statement back with RNG_all. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF.

Definition reac_identity_ingest_contract_F : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo id ad p len : Z) (idb pb : list byte),
    a0 = Z_to_bv 64 id -> a1 = Z_to_bv 64 ad -> a2 = Z_to_bv 64 p -> a3 = Z_to_bv 64 len ->
    0 <= id < 2^64 -> 0 <= ad < 65536 -> 0 <= p < 2^64 -> 0 <= len < 2^64 ->
    (id <> 0 -> id mod 2 = 0 /\ rw_cells rsegs m id [CB 38 idb]) ->
    length pb = Z.to_nat len ->
    (0 < len -> p <> 0 -> bytes_at rsegs m p pb) ->
    (id <> 0 -> 0 < len -> p <> 0 -> p + len <= id \/ id + 38 <= p) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_IDENTITY_INGEST_FRAME <= bv_unsigned sp ->
    (id <> 0 -> id + 38 <= bv_unsigned sp - REAC_IDENTITY_INGEST_FRAME \/ bv_unsigned sp <= id) ->
    (0 < len -> p <> 0 -> p + len <= bv_unsigned sp - REAC_IDENTITY_INGEST_FRAME \/ bv_unsigned sp <= p) ->
    asan_cells m -> shadow_rw m ->
    (id <> 0 -> addressable m id 38) ->
    (0 < len -> p <> 0 -> addressable m p len) ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside (reac_identity_ingest_W (bv_unsigned sp) id) x) ->
    rng RNG (bv_unsigned sp - REAC_IDENTITY_INGEST_FRAME) REAC_IDENTITY_INGEST_FRAME ->
    rng RNG GOT_CELL_K 8 -> rng RNG CELL_K 8 ->
    (id <> 0 -> rng RNG id 38 /\ rng RNG (id / 8 + ASAN_K) ((id + 37) / 8 - id / 8 + 1)) ->
    (0 < len -> p <> 0 -> rng RNG p len /\ rng RNG (p / 8 + ASAN_K) ((p + len - 1) / 8 - p / 8 + 1)) ->
    evtF rsegs RNG
      (reac_identity_ingest_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo id ad p len idb pb)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_IDENTITY_INGEST) fc None m (seg_rom rsegs)).

(* The old statement is the footprint form at ExecF.RNG_all: every rng premise holds of RNG_all, by its bounds
   (the frame is above lo >= 0 and below sp <= 2^64; the two runtime cells are literals; the 38 bytes at id and
   the len bytes at p end at or before APPMEM_END, so their shadow spans end below 2^64). *)
Lemma reac_identity_ingest_contract_of_F :
  reac_identity_ingest_contract_F -> reac_identity_ingest_contract.
Proof.
  intros HF. unfold reac_identity_ingest_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo id ad p len idb pb E0 E1 E2 E3 Hid Had Hp Hlen HS3 Hpl HS4 HD ST HLO HDI HDP HCE HSW HADI HADP HW.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & _ & _).
  unfold REAC_IDENTITY_INGEST_FRAME in *.
  apply (evtF_evt rsegs RNG_all).
  apply HF; try assumption.
  - unfold REAC_IDENTITY_INGEST_FRAME. apply rng_all; lia.
  - apply rng_all; unfold GOT_CELL_K; lia.
  - apply rng_all; unfold CELL_K; lia.
  - intros I0. destruct (HADI I0) as (A0 & A1 & A2 & _). unfold APPMEM_END in A2.
    split; [apply rng_all; lia|].
    apply rng_all; unfold ASAN_K; Z.div_mod_to_equations; lia.
  - intros H1 H2. destruct (HADP H1 H2) as (A0 & A1 & A2 & _). unfold APPMEM_END in A2.
    split; [apply rng_all; lia|].
    apply rng_all; unfold ASAN_K; Z.div_mod_to_equations; lia.
Qed.

(* Route (C), a Theorem Labs lane 11:17Z: the run reads no shadow byte through shadow_rw (its id / p shadow reads come from
   addressable), so the _on forms DROP `shadow_rw m ->`.
   Twin of image A's reac_identity_ingest (a Theorem Labs lane 28e24b8fe6c). The old statements follow by forgetting it. *)
Definition reac_identity_ingest_contract_on : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo id ad p len : Z) (idb pb : list byte),
    a0 = Z_to_bv 64 id -> a1 = Z_to_bv 64 ad -> a2 = Z_to_bv 64 p -> a3 = Z_to_bv 64 len ->
    0 <= id < 2^64 -> 0 <= ad < 65536 -> 0 <= p < 2^64 -> 0 <= len < 2^64 ->
    (id <> 0 -> id mod 2 = 0 /\ rw_cells rsegs m id [CB 38 idb]) ->
    length pb = Z.to_nat len ->
    (0 < len -> p <> 0 -> bytes_at rsegs m p pb) ->
    (id <> 0 -> 0 < len -> p <> 0 -> p + len <= id \/ id + 38 <= p) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_IDENTITY_INGEST_FRAME <= bv_unsigned sp ->
    (id <> 0 -> id + 38 <= bv_unsigned sp - REAC_IDENTITY_INGEST_FRAME \/ bv_unsigned sp <= id) ->
    (0 < len -> p <> 0 -> p + len <= bv_unsigned sp - REAC_IDENTITY_INGEST_FRAME \/ bv_unsigned sp <= p) ->
    asan_cells m ->
    (id <> 0 -> addressable m id 38) ->
    (0 < len -> p <> 0 -> addressable m p len) ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside (reac_identity_ingest_W (bv_unsigned sp) id) x) ->
    evt rsegs
      (reac_identity_ingest_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo id ad p len idb pb)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_IDENTITY_INGEST) fc None m (seg_rom rsegs)).

Lemma reac_identity_ingest_contract_of_on : reac_identity_ingest_contract_on -> reac_identity_ingest_contract.
Proof. intros H. unfold reac_identity_ingest_contract. intros. apply H; assumption. Qed.

Definition reac_identity_ingest_contract_F_on : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo id ad p len : Z) (idb pb : list byte),
    a0 = Z_to_bv 64 id -> a1 = Z_to_bv 64 ad -> a2 = Z_to_bv 64 p -> a3 = Z_to_bv 64 len ->
    0 <= id < 2^64 -> 0 <= ad < 65536 -> 0 <= p < 2^64 -> 0 <= len < 2^64 ->
    (id <> 0 -> id mod 2 = 0 /\ rw_cells rsegs m id [CB 38 idb]) ->
    length pb = Z.to_nat len ->
    (0 < len -> p <> 0 -> bytes_at rsegs m p pb) ->
    (id <> 0 -> 0 < len -> p <> 0 -> p + len <= id \/ id + 38 <= p) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_IDENTITY_INGEST_FRAME <= bv_unsigned sp ->
    (id <> 0 -> id + 38 <= bv_unsigned sp - REAC_IDENTITY_INGEST_FRAME \/ bv_unsigned sp <= id) ->
    (0 < len -> p <> 0 -> p + len <= bv_unsigned sp - REAC_IDENTITY_INGEST_FRAME \/ bv_unsigned sp <= p) ->
    asan_cells m ->
    (id <> 0 -> addressable m id 38) ->
    (0 < len -> p <> 0 -> addressable m p len) ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside (reac_identity_ingest_W (bv_unsigned sp) id) x) ->
    rng RNG (bv_unsigned sp - REAC_IDENTITY_INGEST_FRAME) REAC_IDENTITY_INGEST_FRAME ->
    rng RNG GOT_CELL_K 8 -> rng RNG CELL_K 8 ->
    (id <> 0 -> rng RNG id 38 /\ rng RNG (id / 8 + ASAN_K) ((id + 37) / 8 - id / 8 + 1)) ->
    (0 < len -> p <> 0 -> rng RNG p len /\ rng RNG (p / 8 + ASAN_K) ((p + len - 1) / 8 - p / 8 + 1)) ->
    evtF rsegs RNG
      (reac_identity_ingest_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo id ad p len idb pb)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_IDENTITY_INGEST) fc None m (seg_rom rsegs)).

Lemma reac_identity_ingest_contract_F_of_F_on : reac_identity_ingest_contract_F_on -> reac_identity_ingest_contract_F.
Proof. intros H. unfold reac_identity_ingest_contract_F. intros. apply H; assumption. Qed.

Definition reac_identity_ingest_id_ok_kept : Prop :=
  forall (idb pb : list byte) (ad : Z), length idb = 38%nat -> id_ok idb -> id_ok (snd (ING idb ad pb)).
