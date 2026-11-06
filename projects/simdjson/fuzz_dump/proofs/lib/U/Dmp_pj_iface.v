(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun SjModel Target Prog.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjTape SjTapeList SjTapeTile.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Pj_loc_defs Pj_os_defs Pj_relro El_os_defs El_ins_iface Dmp_defs.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma ELX : LX_ERRNO = 958484. Proof. reflexivity. Qed.

Lemma mod8_of_mod16 : forall A, A mod 16 = 0 -> A mod 8 = 0.
Proof.
  intros A H. pose proof (Z.div_mod A 16 ltac:(lia)) as E. rewrite H, Z.add_0_r in E. rewrite E.
  replace (16 * (A / 16)) with ((2 * (A / 16)) * 8) by lia. apply Z.mod_mul. lia.
Qed.

Definition DMP_PJ_LEAF : Z := 6400.
Definition pj_need (d : nat) : Z := DMP_PJ_FRAME * (Z.of_nat d + 1) + DMP_PJ_LEAF.
Lemma pj_need_S : forall d, pj_need (S d) = pj_need d + DMP_PJ_FRAME.
Proof. intros d. unfold pj_need. rewrite Nat2Z.inj_succ. lia. Qed.
Lemma pj_need_pos : forall d, DMP_PJ_FRAME + DMP_PJ_LEAF <= pj_need d.
Proof. intros d. unfold pj_need, DMP_PJ_FRAME, DMP_PJ_LEAF. lia. Qed.

Definition pj_W (lo q OS : Z) : list (Z * Z) := [(lo, q); (OS, OS + 288); (EL_TPLOC, EL_TPLOC + 8); (LX_ERRNO, LX_ERRNO + 4)].

Lemma FILLOK_after' : forall f, FILLOK f -> FILLOK (fill_after f).
Proof. intros f H. unfold fill_after. destruct (Z.eqb_spec f 0xffffffff); [right; left; reflexivity| exact H]. Qed.

Lemma el_dcc_of_consts : forall m, pj_consts m -> el_dcc m.
Proof.
  intros m (_ & _ & _ & _ & _ & RN).
  relro_chunk RN m constr:(0xd1630%Z) [C8 (Z_to_bv 64 0x7d594); C8 (Z_to_bv 64 0x3b884); C8 (Z_to_bv 64 8)] H1.
  relro_chunk RN m constr:(0xd4d08%Z) [C8 (Z_to_bv 64 0xa3eac); C8 (Z_to_bv 64 0xa3eb4)] H2.
  relro_chunk RN m constr:(0xd58b8%Z) [C8 (Z_to_bv 64 0x888d0); C8 (Z_to_bv 64 0x88b7c); C8 (Z_to_bv 64 0x88e28); C8 (Z_to_bv 64 0x890b0); C8 (Z_to_bv 64 0x89338)] H3.
  relro_chunk RN m constr:(0xd4ea0%Z) [C8 (Z_to_bv 64 0xa7098); C8 (Z_to_bv 64 0xa70a8); C8 (Z_to_bv 64 0xa70b8)] H4.
  relro_chunk RN m constr:(0xd6f50%Z) [C8 (Z_to_bv 64 0xe8938)] H5.
  relro_chunk RN m constr:(0xd6e90%Z) [C8 (Z_to_bv 64 0xe8bb0)] H6.
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 H6))))).
Qed.
Lemma dmp_dcc_of_consts : forall m, pj_consts m -> dmp_dcc m.
Proof.
  intros m (_ & _ & _ & _ & _ & RN). unfold dmp_dcc, DMP_NPB_SLOT, DMP_NP_BOOL.
  relro_chunk RN m constr:(0xd58b0%Z) [C8 (Z_to_bv 64 0x88638)] H1. exact H1.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition OSX (m : mem) (OS : Z) : Prop :=
  exists (pb : word) (pp ep fill : Z) (dum j148 j284 : list byte),
    rw_cells usegs m OS (os_cellsX OS pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) 0x1002 0 fill dum j148 j284) /\ PUTINV OS pp ep /\ FILLOK fill.

Lemma OSX_of_fresh : forall m OS, OSFRESH m OS -> OSX m OS.
Proof.
  intros m OS (dum & j148 & j284 & H). exists (Z_to_bv 64 0), 0, 0, 0xffffffff, dum, j148, j284.
  rewrite os_cells_X in H. split; [exact H|]. split; [left; split; reflexivity| left; reflexivity].
Qed.

Definition pj_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (lo OS : Z) (canary : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom usegs)
    /\ frm0 fc'
    /\ munch (pj_W lo q OS) m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo q
    /\ OSX m' OS
    /\ rw_cells usegs m' EL_TPLOC [C8 (MallocRep.wz EL_GLOC)]
    /\ (exists errv' : word, rw_cells usegs m' LX_ERRNO [C4 errv'])
    /\ ssp_cells m' canary
    /\ LOCB m'.

Definition pj_stmt (d : nat) : Prop :=
  forall (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (q lo OS DOC TAPE SBUF i j : Z) (tws sbs : list Z) (canary errv : word),

    elem (Tf tws) (Tf sbs) (Z.of_nat (length sbs)) ck_any d i j -> 0 <= i -> j <= Z.of_nat (length tws) -> Z.of_nat (length tws) < 2^32 ->
    Forall (fun c => 0 <= c < 256) sbs -> Z.of_nat (length sbs) < 2^56 ->

    rw_cells usegs m DOC [C8 (Z_to_bv 64 TAPE); C8 (Z_to_bv 64 SBUF)] -> q <= DOC -> (DOC + 16 <= OS \/ OS + 288 <= DOC) -> DOC + 16 < 2 ^ 62 ->
    bytes_at usegs m TAPE (u64s (map (Z_to_bv 64) tws)) -> 0 < TAPE -> TAPE mod 8 = 0 -> TAPE + 8 * Z.of_nat (length tws) <= lo ->
    (TAPE + 8 * Z.of_nat (length tws) <= 0x10000 \/ GLOBALS_TOP <= TAPE) ->
    bytes_at usegs m SBUF (map (Z_to_bv 8) sbs) -> 0 < SBUF -> SBUF + Z.of_nat (length sbs) <= lo ->
    (SBUF + Z.of_nat (length sbs) <= 0x10000 \/ GLOBALS_TOP <= SBUF) ->

    OSX m OS -> q <= OS -> OS + 288 < 2 ^ 62 -> OS mod 8 = 0 -> DOC mod 8 = 0 -> LOCB m -> el_dcc m -> dmp_dcc m -> ssp_cells m canary ->
    rw_cells usegs m EL_TPLOC [C8 (MallocRep.wz EL_GLOC)] -> rw_cells usegs m LX_ERRNO [C4 errv] ->

    stk usegs m lo q -> lo + pj_need d <= q -> GLOBALS_TOP <= lo -> q mod 16 = 0 -> mem_inv usegs m -> frm0 fc ->
    evt usegs (pj_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo OS canary m)
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 (OS + 128)) (Z_to_bv 64 DOC) (Z_to_bv 64 i) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DMP_PJ) fc None m (seg_rom usegs)).

Definition pj_root_stmt : Prop :=
  forall (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (q lo OS DOC TAPE SBUF : Z) (tws sbs : list Z) (canary errv : word),
    tape_wf (Tf tws) (Tf sbs) (Z.of_nat (length sbs)) ck_any (Z.of_nat (length tws)) -> Forall (fun c => 0 <= c < 256) sbs ->
    rw_cells usegs m DOC [C8 (Z_to_bv 64 TAPE); C8 (Z_to_bv 64 SBUF)] -> q <= DOC -> (DOC + 16 <= OS \/ OS + 288 <= DOC) -> DOC + 16 < 2 ^ 62 ->
    bytes_at usegs m TAPE (u64s (map (Z_to_bv 64) tws)) -> 0 < TAPE -> TAPE mod 8 = 0 -> TAPE + 8 * Z.of_nat (length tws) <= lo ->
    (TAPE + 8 * Z.of_nat (length tws) <= 0x10000 \/ GLOBALS_TOP <= TAPE) ->
    bytes_at usegs m SBUF (map (Z_to_bv 8) sbs) -> 0 < SBUF -> SBUF + Z.of_nat (length sbs) <= lo ->
    (SBUF + Z.of_nat (length sbs) <= 0x10000 \/ GLOBALS_TOP <= SBUF) ->
    OSFRESH m OS -> q <= OS -> OS + 288 < 2 ^ 62 -> OS mod 8 = 0 -> DOC mod 8 = 0 -> LOCB m -> el_dcc m -> dmp_dcc m -> ssp_cells m canary ->
    rw_cells usegs m EL_TPLOC [C8 (MallocRep.wz EL_GLOC)] -> rw_cells usegs m LX_ERRNO [C4 errv] ->
    stk usegs m lo q -> lo + pj_need TAPE_MAX_DEPTH <= q -> GLOBALS_TOP <= lo -> q mod 16 = 0 -> mem_inv usegs m -> frm0 fc ->
    evt usegs (pj_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo OS canary m)
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 (OS + 128)) (Z_to_bv 64 DOC) (Z_to_bv 64 1) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DMP_PJ) fc None m (seg_rom usegs)).

Lemma pj_root_of : pj_stmt TAPE_MAX_DEPTH -> pj_root_stmt.
Proof.
  intros PJ. unfold pj_root_stmt. intros until errv. intros WF FAB DOCC QD DJ D62 TB T0 T8 TL TI SB S0 SL SI FR QO O62 O8 D8 LB DCC DCB SSP TPC ERR ST NEED GLO AL MI FRM.
  pose proof (tape_wf_root _ _ _ _ _ WF) as [EL NR]. destruct WF as (_ & SN & _).
  eapply (PJ ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q lo OS DOC TAPE SBUF 1 (Z.of_nat (length tws) - 1) tws sbs canary errv);
    try assumption; try lia.
  apply OSX_of_fresh. exact FR.
Qed.

End WithCeiling0.
