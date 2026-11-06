From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
Require Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcPorts RcBox RcSynth RcLay RcFin RcEmit.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_CTRL_BUILD_AS : Z := 0x14690.
Definition REAC_CTRL_BUILD_AS_K : Z := 352.
(* CTRL_FRAMES. The code reads its rows 3 .. 9: the 168 bytes [BA_FR + 72, BA_FR + 240). *)
Definition BA_FR : Z := 0x1f9e8.

(* row(b): word b of the row table RT (0x10670, read-only data): box_block_to_ctrl_frame. *)
Definition ba_row (b : Z) : Z := nth (Z.to_nat b) [3; 5; 6; 7; 8; 4; 9] 0.

(* Row r (3 .. 9) of CTRL_FRAMES (struct.libreac.ctrl_frame R1): type cd ea, block r, template 0, args at 0 len 0,
   record cksum at 0 len 0, cksum 1 for rows 3 and 5, len 1 for rows 3, 4 and 9, gate 1 for rows 4 and 9,
   audio 1 for rows 5 .. 8. *)
Definition ba_fr (r : Z) : list byte :=
  map (Z_to_bv 8)
    ([205; 234; r] ++ repeat 0 17 ++
     [if (r =? 3) || (r =? 5) then 1 else 0; if (r =? 3) || (r =? 4) || (r =? 9) then 1 else 0;
      if (r =? 4) || (r =? 9) then 1 else 0; if (5 <=? r) && (r <=? 8) then 1 else 0]).

Definition ba_tbl : list byte := flat_map ba_fr [3; 4; 5; 6; 7; 8; 9].

(* The function goes on to ctrl_emit_as: o, m non-zero and b a valid block. *)
Definition ba_go (o md b : Z) : bool := negb (o =? 0) && negb (md =? 0) && (b <=? 6).

(* E(b): the width n is valid and, for the identity blocks (b = 5, 6), the model has an identity record. *)
Definition ba_E (n : Z) (mb : list byte) (b : Z) : bool := em_wok n && ((b <=? 4) || negb (em_hid mb =? 0)).

(* X(b): the control block, stamped for b = 0, 1 (rows 3 and 5 have cksum 1). *)
Definition ba_X (md : Z) (mb nb : list byte) (b : Z) : list byte :=
  if b <=? 1 then stamp32 (ly_Z md mb nb b) else ly_Z md mb nb b.

Definition reac_ctrl_build_as_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o md b d s ns : Z)
         (mb nb db sb junk : list byte),
    let S := bv_unsigned sp in
    let Lo := S - REAC_CTRL_BUILD_AS_K in
    let n := bm_uw md (firstn 8 (skipn 16 mb)) in
    let len := 52 + 36 * n in
    let go := ba_go o md b in
    let E := ba_E n mb b in
    let nm := (b = 5 \/ b = 6) /\ has mb <> 0 /\ rname mb <> 0 in
    bv_unsigned a0 = o -> bv_unsigned a1 = md -> bv_unsigned a2 = b -> bv_unsigned a3 = d -> bv_unsigned a4 = s ->
    a7 = Z_to_bv 64 ns -> -2^31 <= ns <= 0 ->
    S mod 16 = 0 -> stk rsegs m Lo S ->
    bytes_at rsegs m (BA_FR + 72) ba_tbl -> ly_dj Lo S (BA_FR + 72) (BA_FR + 240) ->
    length db = 6%nat -> bytes_at rsegs m d db -> ly_dj Lo S d (d + 6) ->
    length sb = 6%nat -> bytes_at rsegs m s sb -> ly_dj Lo S s (s + 6) ->
    (md <> 0 -> md mod 8 = 0 /\ md + 296 <= 2^64 /\ length mb = 296%nat /\ bytes_at rsegs m md mb /\
                ly_dj Lo S md (md + 296)) ->
    (md <> 0 -> nm -> name_ok nb /\ bytes_at rsegs m (rname mb) nb /\
                      ly_dj Lo S (rname mb) (rname mb + Z.of_nat (length nb))) ->
    (o <> 0 -> o + 1492 <= 2^64) ->
    (go && E = true ->
       rw_cells rsegs m o [CB (Z.to_nat len) junk] /\ ly_dj Lo S o (o + len) /\
       ly_dj o (o + len) (BA_FR + 72) (BA_FR + 240) /\ ly_dj o (o + len) md (md + 296) /\
       (nm -> ly_dj o (o + len) (rname mb) (rname mb + Z.of_nat (length nb))) /\
       ly_dj o (o + len) d (d + 6) /\ ly_dj o (o + len) s (s + 6)) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (if go && E then len else 0))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs)
         /\ munch [(Lo, S); (o, o + (if go && E then len else 0))] m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' Lo S
         /\ (go = false -> munch [(S - 80, S)] m m')
         /\ (go && E = true ->
               bytes_at rsegs m' o
                 (em_fr db sb (bv_unsigned a5 mod 65536) (Z_to_bv 8 205) (Z_to_bv 8 234) (ba_X md mb nb b) len)
               /\ em_wok n = true
               /\ (b <= 1 -> blocksum (ba_X md mb nb b) = 0)
               /\ (blocksum (ly_Z md mb nb b) = 0 -> ba_X md mb nb b = ly_Z md mb nb b)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_BUILD_AS) fc None m (seg_rom rsegs)).
