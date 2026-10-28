(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjS1Out SjTape.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import SjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_hkit2 Sj_new Sj_h_dtor Sj_h_alloc Sj_h_setmd Sj_h_deldtor Sj_h_layout Sj_stage2_iface Atp_fzwA Atp_setcapA Atp_hkit3A Atp_pdtorA Atp_activewA Atp_activeA Atp_pidwA Atp_hkit4A Atp_hkit5A Atp_hkit6A Atp_pid1A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition res_cellsA (docp : Z) (r : word) (j20 : list byte) : list cell :=
  if bv_eqb r (Z_to_bv 64 0) then [C8 (Z_to_bv 64 docp); C8 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); CB 4 j20]
  else [CB 16 (repeat z8 16); C4 r; CB 4 j20].

Definition pid_costA (len : Z) : Z := pid_cost6 (Z.max len 32) + S2A_COST len.

Section PidIface.
Variable RT : rt_sig.

Definition pidA_st (Σ : rts RT) (m : mem) (P impl idx oc ia tape sbuf cap : Z) : Prop :=
  fobj RT Σ m P 80
  /\ (exists p1 p17 p57, rw_cells bsegs m P (pid_cells z8 p1 (Z_to_bv 64 impl) z8 p17 (Z_to_bv 64 12) (Z_to_bv 64 tape) (Z_to_bv 64 sbuf) (Z_to_bv 64 cap)
                                                (Z_to_bv 64 4294967295) z8 p57 (Z_to_bv 64 0) (Z_to_bv 64 0)))
  /\ (exists nsi p12 nxt p28 p50 bufv lenv docv,
        rw_cells bsegs m impl (impl16 (Z_to_bv 64 0x169010) nsi p12 (Z_to_bv 64 idx) nxt p28 (Z_to_bv 64 cap) (Z_to_bv 64 1024)
                                      (Z_to_bv 8 0) (Z_to_bv 8 0) p50 (Z_to_bv 64 oc) (Z_to_bv 64 ia) bufv lenv docv)).

Definition pid_post (Σ2 : rts RT) (PMc : Model -> Prop) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (lo RES P : Z) (L : list (Z * Z))
    (impl idx oc ia tape sbuf cap : Z) (cost : Z) (m2 : mem) : config -> Prop :=
  fun c => exists (Σ' : rts RT),
    ASTA RT Σ' PMc (fun ms => exists v m', ret_st ra sp gp (Z_to_bv 64 0x6abde8) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
      /\ rt_after_f RT Σ' (bv_unsigned sp) lo m2 m'
      /\ rt_pres_fp L (rt_frames RT Σ2) (bv_unsigned sp) (pid_X P RES) m2 m'
      /\ (exists (r : word) j20, rw_cells bsegs m' RES (res_cellsA (P + 24) r j20) /\ bv_unsigned r < 64
                                /\ s2a_okres tape sbuf (roundup64 (cap + 3)) (al_sbuf cap) r m')
      /\ sj_lib m' /\ pdone RT Σ' m' P L /\ pidA_st Σ' m' P impl idx oc ia tape sbuf cap) c
    /\ rt_live RT Σ' = rt_live RT Σ2 /\ rt_frames RT Σ' = rt_frames RT Σ2 /\ rt_sp0 RT Σ' = rt_sp0 RT Σ2 /\ rt_credit RT Σ2 - cost <= rt_credit RT Σ'.

Variable LIB : mem -> Prop.

Definition pid_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (P RES BUF : Z) (bs p1 p17 p57 jr : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 RES -> a1 = Z_to_bv 64 P -> a2 = Z_to_bv 64 (P + 24) -> a3 = Z_to_bv 64 BUF -> a4 = Z_to_bv 64 (Z.of_nat (length bs)) ->
  a5 = Z_to_bv 64 0 -> tp = Z_to_bv 64 0x6abde8 ->
  Z.of_nat (length bs) <= 1048512 -> bytes_at bsegs m BUF (padded_bytes (map bv_unsigned bs)) ->
  In (BUF, Z.of_nat (length bs) + 64) (rt_live RT Σ) -> BUF mod 16 = 0 ->
  fobj RT Σ m P 80 -> rw_cells bsegs m P (parser_init p1 p17 p57) ->
  bv_unsigned sp <= RES -> RES + 40 <= USTACK_TOP -> rw_cells bsegs m RES [CB 24 jr] ->
  lposx (rt_live RT Σ) ->
  Z.of_nat (length (rt_live RT Σ)) + 7 <= LIVE_MAX -> (length (rt_frames RT Σ) + PID_FRAMES <= FRAMES_MAX)%nat ->
  pid_costA (Z.of_nat (length bs)) <= rt_credit RT Σ ->
  LIB m -> ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + PID_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> frm0 fc ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_pid m)))
    (fun c => exists (Σ' : rts RT) (impl idx oc ia tape sbuf : Z),
       ASTA RT Σ' PMc (fun ms => exists v m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) ((P, P + 80) :: (RES, RES + 24) :: SJ_W) m m'
         /\ (exists (r : word) j20, rw_cells bsegs m' RES (res_cellsA (P + 24) r j20) /\ bv_unsigned r < 64
                                   /\ s2a_okres tape sbuf (roundup64 (Z.max (Z.of_nat (length bs)) 32 + 3)) (al_sbuf (Z.max (Z.of_nat (length bs)) 32)) r m')
         /\ LIB m' /\ pdone RT Σ' m' P (rt_live RT Σ) /\ pidA_st Σ' m' P impl idx oc ia tape sbuf (Z.max (Z.of_nat (length bs)) 32)) c
       /\ rt_live RT Σ' = (ia, 1024) :: (oc, 8192) :: (idx, sc_idx (Z.max (Z.of_nat (length bs)) 32)) :: (impl, 96)
                            :: (tape, al_tape (Z.max (Z.of_nat (length bs)) 32)) :: (sbuf, al_sbuf (Z.max (Z.of_nat (length bs)) 32)) :: rt_live RT Σ
       /\ (impl mod 16 = 0 /\ idx mod 16 = 0 /\ oc mod 16 = 0 /\ ia mod 16 = 0 /\ tape mod 16 = 0 /\ sbuf mod 16 = 0)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - pid_costA (Z.of_nat (length bs)) <= rt_credit RT Σ').

End PidIface.

Lemma s2a_okres_agree : forall (Q : Z -> Prop) m m' TAPE SBUF tcap scap r,
  agree_on Q m m' -> (forall a, TAPE <= a < TAPE + 8 * tcap -> Q a) -> (forall a, SBUF <= a < SBUF + scap -> Q a) ->
  s2a_okres TAPE SBUF tcap scap r m -> s2a_okres TAPE SBUF tcap scap r m'.
Proof.
  intros Q m m' TAPE SBUF tcap scap r AG HT HS [K|(E & tws & sbs & BT & BS & WF & RNG & LT & LS)]; [left; exact K| right].
  split; [exact E|]. exists tws, sbs. split; [| split; [| auto]].
  - eapply bytes_at_agree; [exact BT|]. eapply agree_sub; [exact AG|]. rewrite u64s_length, length_map. intros a Ha. apply HT. lia.
  - eapply bytes_at_agree; [exact BS|]. eapply agree_sub; [exact AG|]. rewrite length_map. intros a Ha. apply HS. lia.
Qed.
