(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep ZBridge.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import LhPure.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_G_kit Th_mutex Fz_T_lock Fz_env Fz_M_malloc Fz_T_sk Fz_K_hash Fz_K_rep Fz_K_getrn Fz_K_retrieve Fz_K_skw Fz_K_sk Fz_I2_ppis Fz_K_pstw Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Local Ltac zsh := cbv beta; try change (bv_unsigned (Z_to_bv 8 0)) with 0; try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0).

(* [comment removed for export] *)
Lemma ps_w8 : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (l : Z),
  0 <= l < 2 ^ 40 -> mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR (Z_to_bv 64 SITE_ps_malloc) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (l + 16)) (Z_to_bv 64 PS_FILE) (Z_to_bv 64 129) a3 a4 a5 a6 a7
                                  s2 s3 s4 s5 s6 s7 (Z_to_bv 64 l) s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_CRYPTO_malloc) fc None m (seg_rom asegs))
    (MS (mkR (Z_to_bv 64 SITE_ps_strlen) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 l) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 SITE_ps_strlen) fc None m (seg_rom asegs)).
Proof.
  intros until l. intros HL MI. unfold SITE_ps_strlen, SITE_ps_malloc, PS_FILE, e_CRYPTO_malloc.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  do 6 zstep. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ps_w9 : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (l q S : Z),
  0 <= l < 2 ^ 40 -> 0 < q < 2 ^ 47 -> q mod 8 = 0 -> s5 = Z_to_bv 64 S -> mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR (Z_to_bv 64 SITE_ps_memcpy) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (q + 12)) (Z_to_bv 64 S) (Z_to_bv 64 (l + 1)) a3 a4 a5 a6 a7
                                  s2 s3 s4 s5 s6 (Z_to_bv 64 q) (Z_to_bv 64 l) (Z_to_bv 64 (q + 12)) s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_asan_memcpy) fc None m (seg_rom asegs))
    (MS (mkR (Z_to_bv 64 SITE_ps_malloc) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 l) s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 SITE_ps_malloc) fc None m (seg_rom asegs)).
Proof.
  intros until S. intros HL HQ QAL -> MI. unfold SITE_ps_malloc, SITE_ps_memcpy, e_asan_memcpy.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  zstep.                                                                  (* [comment removed for export] *)
  do 5 zstep. apply evt_done. reflexivity.
Qed.
(* [comment removed for export] *)
Definition cnt_of (nm : bool) (ni vi : Z) : Z := if nm then ni else vi.
Definition off_lst (nm : bool) : Z := if nm then 32 else 40.
Definition psd_bump (nm : bool) (pk pl1 pl2 ni vi pq1 pq2 : Z) : list cell :=
  if nm then psd_cells pk pl1 pl2 (ni + 1) vi pq1 pq2 else psd_cells pk pl1 pl2 ni (vi + 1) pq1 pq2.

(* [comment removed for export] *)
Definition ps_w10_post (sp gp tp t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (nm : bool) (RB f ps q pk pl1 pl2 ni vi pq1 pq2 : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_ps_push) (Z_to_bv 64 RB) gp tp t0 t1 t2 sp (Z_to_bv 64 RB) (Z_to_bv 64 (q_of nm pq1 pq2)) (Z_to_bv 64 (q + 12)) (Z_to_bv 64 0) (Z_to_bv 64 0) a4 a5 a6 a7
                 (Z_to_bv 64 f) (Z_to_bv 64 ps) (Z_to_bv 64 (Z.shiftr ps 3 + 2147450880)) (Z_to_bv 64 (ps + off_idx nm)) (Z_to_bv 64 2147450880) (Z_to_bv 64 q)
                 (Z_to_bv 64 (q_of nm pq1 pq2)) (Z_to_bv 64 (Z.shiftr (ps + off_idx nm) 3 + 2147450880)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) t3 t4 t5 t6)
            F (Z_to_bv 64 e_sk_push) fc None m' (seg_rom asegs)
    /\ munch [(q, q + 12); (ps + 24, ps + 32)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' q [C8 (Z_to_bv 64 (q + 12)); C4 (Z_to_bv 64 (cnt_of nm ni vi + 1))]
    /\ rw_cells asegs m' ps (psd_bump nm pk pl1 pl2 ni vi pq1 pq2).

Lemma ps_w10 : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (nm : bool) (RB f ps q pk pl1 pl2 ni vi pq1 pq2 l S : Z) (qj : list byte),
  0 <= RB -> RB + 32 <= 2 ^ 47 ->
  rw_cells asegs m (RB + 8) [C8 (Z_to_bv 64 (off_idx nm))] -> rw_cells asegs m (RB + 16) [C8 (Z_to_bv 64 (nmz nm))] ->
  0 < q -> q mod 8 = 0 -> 0x10007fff8000 <= q -> q + 16 <= 2 ^ 47 -> rw_cells asegs m q [CB 12 qj] -> acc asegs m q 16 ->
  0 < ps -> ps mod 16 = 0 -> 0x10007fff8000 <= ps -> ps + 48 <= 2 ^ 47 -> rw_cells asegs m ps (psd_cells pk pl1 pl2 ni vi pq1 pq2) -> acc asegs m ps 48 ->
  0 <= ni < 2 ^ 20 -> 0 <= vi < 2 ^ 20 -> 0 <= f < 2 ^ 47 -> 0 <= l < 2 ^ 40 ->
  q + 16 <= RB -> ps + 48 <= RB -> (ps + 48 <= q \/ q + 16 <= ps) ->
  mem_inv asegs m ->
  evt asegs (ps_w10_post sp gp tp t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc nm RB f ps q pk pl1 pl2 ni vi pq1 pq2 m)
    (MS (mkR (Z_to_bv 64 SITE_ps_memcpy) (Z_to_bv 64 RB) gp tp t0 t1 t2 sp (Z_to_bv 64 RB) (Z_to_bv 64 (q + 12)) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 f) (Z_to_bv 64 ps) (Z_to_bv 64 (Z.shiftr ps 3 + 2147450880)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) (Z_to_bv 64 q)
             (Z_to_bv 64 l) (Z_to_bv 64 (q + 12)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_ps_memcpy) fc None m (seg_rom asegs)).
Proof.
  intros until qj. intros RB0 RBH OFFC NMC Q0 QAL QHI QH QC QACC PS0 PSAL PSHI PSH PSC PSA NI VI FH LH QRB PSRB PSQ MI.
  unfold SITE_ps_memcpy, psd_cells in *.
  pose proof (munch_refl [(q, q + 12); (ps + 24, ps + 32)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWS : sh_fp [(q, q + 12); (ps + 24, ps + 32)]) by (clear - QHI PSHI; sh_fp_lia).
  assert (PSAL8 : ps mod 8 = 0) by (clear - PSAL; Z.div_mod_to_equations; lia).
  apply (rw_cells_split_CB asegs _ q [] 12 qj [] [8; 4]%nat) in QC; [| reflexivity]; cbn [mk_CB_cells app] in QC.
  zstep. zstep. zstep. zsh. zstep. th_if_lit.
  zstep. zstep.
  zstep.
  destruct nm; cbn [nmz t_of q_of off_idx cnt_of off_lst psd_bump] in *.
  all: zstep; zstep; zstep; zsh; zstep; th_if_lit.
  all: zstep.
  (* [comment removed for export] *)
  all: zstep; zstep; zstep.
  all: match goal with |- context [bv_swrap 32 (bv_unsigned (sx32 (Z_to_bv 64 ?x)) + 1)] => rewrite (t_sx32_small x) by lia; rewrite (unsigned_lit x), (SWR (x + 1)) by lia end.
  all: zstep.
  all: zstep; zstep; zsh; zstep; th_if_lit.
  all: zstep.
  all: zstep; if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by lia; lia|].
  all: zstep.
  all: zstep; th_if_lit.
  1: zstep; zstep.
  2: zstep.
  all: zstep; zstep; zstep; zstep; zsh; zstep; th_if_lit.
  all: zstep; zsh; zstep; th_if_lit.
  all: zstep; zstep; zstep; zstep.
  all: apply evt_done; unfold ps_w10_post, SITE_ps_push, psd_bump, psd_cells; cbn [nmz t_of q_of off_idx cnt_of off_lst].
  all: eexists; split; [reflexivity|].
  all: split; [exact MU|]. all: split; [exact WM|]. all: split; [exact MI|]. all: split; [exact QC| exact PSC].
Qed.

(* [comment removed for export] *)
Definition ps_w11_post (sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (nm : bool) (RB f ps q pl1 pl2 pq1 pq2 : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_ps_insert) (Z_to_bv 64 RB) gp tp t0 t1 t2 sp (Z_to_bv 64 RB) (Z_to_bv 64 (t_of nm pl1 pl2)) (Z_to_bv 64 q) a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 f) (Z_to_bv 64 ps) (Z_to_bv 64 (Z.shiftr ps 3 + 2147450880)) (Z_to_bv 64 (ps + off_idx nm)) (Z_to_bv 64 2147450880) (Z_to_bv 64 q)
                 (Z_to_bv 64 (q_of nm pq1 pq2)) (Z_to_bv 64 (t_of nm pl1 pl2)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) t3 t4 t5 t6)
            F (Z_to_bv 64 0x2003c8) fc None m' (seg_rom asegs)
    /\ munch [(RB + 16, RB + 24)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (RB + 16) [C8 (Z_to_bv 64 (Z.shiftr (ps + off_idx nm) 3 + 2147450880))]
    /\ rw_cells asegs m' (RB + 24) [C8 (Z_to_bv 64 (t_of nm pl1 pl2))].

Lemma ps_w11 : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (nm : bool) (RB f ps q pl1 pl2 pq1 pq2 r : Z),
  0 <= RB -> RB + 32 <= 2 ^ 47 -> 1 <= r < 2 ^ 31 ->
  rw_cells asegs m (RB + 16) [C8 (Z_to_bv 64 (nmz nm))] -> rw_cells asegs m (RB + 24) [C8 (Z_to_bv 64 (t_of nm pl1 pl2))] ->
  0 <= ps -> ps + 48 <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (ps_w11_post sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc nm RB f ps q pl1 pl2 pq1 pq2 m)
    (MS (mkR (Z_to_bv 64 SITE_ps_push) (Z_to_bv 64 RB) gp tp t0 t1 t2 sp (Z_to_bv 64 RB) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 f) (Z_to_bv 64 ps) (Z_to_bv 64 (Z.shiftr ps 3 + 2147450880)) (Z_to_bv 64 (ps + off_idx nm)) (Z_to_bv 64 2147450880) (Z_to_bv 64 q)
             (Z_to_bv 64 (q_of nm pq1 pq2)) (Z_to_bv 64 (Z.shiftr (ps + off_idx nm) 3 + 2147450880)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_ps_push) fc None m (seg_rom asegs)).
Proof.
  intros until r. intros RB0 RBH HR NMC TC PS0 PSH MI. unfold SITE_ps_push in *.
  pose proof (munch_refl [(RB + 16, RB + 24)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (SHR : 0 <= Z.shiftr (ps + off_idx nm) 3 + 2147450880 < 2 ^ 47).
  { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. destruct nm; cbn [off_idx]; Z.div_mod_to_equations; lia. }
  zstep. if_cases K0. all: zify_cond K0.
  1: exfalso; destruct (Z.ltb_spec 0 r); [destruct (Z.ltb_spec r 9223372036854775808); [discriminate| lia] | lia].
  zstep. try lfix.
  zstep. zstep. zstep. zstep.
  apply evt_done. unfold ps_w11_post, SITE_ps_insert. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact NMC| exact TC].
Qed.

(* [comment removed for export] *)
Definition ps_w14a_post (sp gp tp t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (nm : bool) (RB f ps q pk pl1 pl2 pq1 pq2 idx lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a2' a3' : word) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_ps_unlock2) (Z_to_bv 64 RB) gp tp t0 t1 t2 sp (Z_to_bv 64 RB) (Z_to_bv 64 idx) (Z_to_bv 64 0) a2' a3' a4 a5 a6 a7
                 (Z_to_bv 64 f) (Z_to_bv 64 ps) (Z_to_bv 64 (Z.shiftr ps 3 + 2147450880)) (Z_to_bv 64 (ps + off_idx nm)) (Z_to_bv 64 2147450880) (Z_to_bv 64 q)
                 (Z_to_bv 64 (q_of nm pq1 pq2)) (Z_to_bv 64 (t_of nm pl1 pl2)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) t3 t4 t5 t6)
            F (Z_to_bv 64 0x20c3b4) fc None m' (seg_rom asegs)
    /\ munch [(RB - 112, RB); (pk + 4, pk + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo RB /\ rw_cells asegs m' pk (mutex_cells z64 z64).

Lemma ps_w14a : forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (nm : bool) (RB f ps q pk pl1 pl2 ni vi pq1 pq2 idx lo B items : Z),
  0x10007fff8000 <= lo -> lo <= RB - 112 -> RB + 32 <= 2 ^ 47 -> stk asegs m lo RB ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  rw_cells asegs m (t_of nm pl1 pl2) (plh_cells B items) -> acc asegs m (t_of nm pl1 pl2) 104 -> 0 < t_of nm pl1 pl2 -> (t_of nm pl1 pl2) mod 8 = 0 -> t_of nm pl1 pl2 + 104 <= lo ->
  0 < ps -> ps mod 16 = 0 -> 0x10007fff8000 <= ps -> ps + 48 <= lo -> rw_cells asegs m ps (psd_cells pk pl1 pl2 ni vi pq1 pq2) -> acc asegs m ps 48 ->
  0 < pk -> pk mod 16 = 0 -> 0x10007fff8000 <= pk -> pk + 40 <= lo -> rw_cells asegs m pk (mutex_cells z64 (Z_to_bv 64 16)) ->
  0 < q -> q mod 8 = 0 -> 0x10007fff8000 <= q -> q + 16 <= lo -> rw_cells asegs m q [C8 (Z_to_bv 64 (q + 12)); C4 (Z_to_bv 64 idx)] -> acc asegs m q 16 -> 0 <= idx < 2 ^ 31 ->
  (ps + 48 <= pk \/ pk + 40 <= ps) -> (q + 16 <= pk \/ pk + 40 <= q) -> (t_of nm pl1 pl2 + 104 <= pk \/ pk + 40 <= t_of nm pl1 pl2) -> 0 <= f < 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (ps_w14a_post sp gp tp t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc nm RB f ps q pk pl1 pl2 pq1 pq2 idx lo m)
    (MS (mkR (Z_to_bv 64 SITE_ps_insert) (Z_to_bv 64 RB) gp tp t0 t1 t2 sp (Z_to_bv 64 RB) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 f) (Z_to_bv 64 ps) (Z_to_bv 64 (Z.shiftr ps 3 + 2147450880)) (Z_to_bv 64 (ps + off_idx nm)) (Z_to_bv 64 2147450880) (Z_to_bv 64 q)
             (Z_to_bv 64 (q_of nm pq1 pq2)) (Z_to_bv 64 (t_of nm pl1 pl2)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_ps_insert) fc None m (seg_rom asegs)).
Proof.
  intros until items. intros LO0 LO RBH ST UT SHC LHC ACCL L0 LAL LLO PS0 PSAL PSHI PSLO PSC PSA PK0 PKAL PKHI PKLO LKC Q0 QAL QHI QLO QC QACC IDX PSPK QPK LPK FH MI.
  unfold SITE_ps_insert, psd_cells, g_shadow_memory_dynamic_address in *. unfold mutex_cells in LKC.
  pose proof (munch_refl [(RB - 112, RB); (pk + 4, pk + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWS : sh_fp [(RB - 112, RB); (pk + 4, pk + 8)]) by (clear - LO0 LO PKHI; sh_fp_lia).
  assert (HWU : ut_fp [(RB - 112, RB); (pk + 4, pk + 8)]) by (clear - LO0 LO PKHI; ut_fp_lia).
  assert (EU1 : bv_unsigned (Z_to_bv 64 RB) = RB) by (apply unsigned_lit; clear - LO0 LO RBH; lia).
  assert (PSAL8 : ps mod 8 = 0) by (clear - PSAL; Z.div_mod_to_equations; lia). assert (PKAL4 : pk mod 4 = 0) by (clear - PKAL; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  zstep. zstep.
  eapply evt_cut.
  { eapply (lherr_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo (t_of nm pl1 pl2) B items); try reflexivity; rewrite ?EU1; try eassumption; lia. }
  cbv beta. intros ms' PO. hnf in PO. rewrite ?EU1 in PO. revert ms' PO.
  lazymatch type of MU with munch _ _ ?mc => post_call asegs mc end.
  zstep. th_if_lit.
  zstep. zsh. zstep. th_if_lit.
  zstep. zstep.
  (* [comment removed for export] *)
  eapply evt_cut; [eapply (T_unlock_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo); rewrite ?unsigned_lit, ?EU1 by lia; first [eassumption| lia] |].
  cbv beta; intros ms' PO; hnf in PO; repeat (rewrite unsigned_lit in PO by lia); rewrite ?EU1 in PO; unfold mutex_cells in PO; revert ms' PO.
  lazymatch type of MU with munch _ _ ?mc => post_call asegs mc end.
  zstep. zstep. zstep. zstep. zsh. zstep. th_if_lit.
  zstep. rewrite (t_sx32_small idx) by lia.
  zstep.
  apply evt_done. unfold ps_w14a_post, SITE_ps_unlock2, mutex_cells. do 3 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; assumption.
Qed.

(* [comment removed for export] *)
Definition ps_retired_shadow : list cell :=
  [C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11))].
Definition ps_w14b_post (sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (RB f idx S : Z) (hj1 hj2 : list byte) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_ps_unlock2) (Z_to_bv 64 RB) gp tp t0 t1 t2 sp (Z_to_bv 64 RB) (Z_to_bv 64 idx) (Z_to_bv 64 (-11)) a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 f) s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) t3 t4 t5 t6)
            F (Z_to_bv 64 0x20c3f4) fc None m' (seg_rom asegs)
    /\ munch [(f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' f [C8 (Z_to_bv 64 PS_RETIRED); C8 (Z_to_bv 64 PS_DESCR); C8 (Z_to_bv 64 e_property_string); CB 8 hj1; C8 (Z_to_bv 64 S); CB 16 hj2] /\ rw_cells asegs m' (f / 8 + 2147450880) ps_retired_shadow.

Lemma ps_w14b : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (RB f idx S : Z) (hj1 hj2 : list byte),
  0 < f -> f mod 64 = 0 -> 0xbc6000 <= f -> f + 64 <= 2 ^ 47 -> (f + 64 <= 0x7fff8000 \/ 0x10007fff8000 <= f) -> 0 <= idx < 2 ^ 31 ->
  rw_cells asegs m f [C8 (Z_to_bv 64 PS_MAGIC); C8 (Z_to_bv 64 PS_DESCR); C8 (Z_to_bv 64 e_property_string); CB 8 hj1; C8 (Z_to_bv 64 S); CB 16 hj2] -> rw_cells asegs m (f / 8 + 2147450880) ps_shadow -> mem_inv asegs m ->
  evt asegs (ps_w14b_post sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 F fc RB f idx S hj1 hj2 m)
    (MS (mkR (Z_to_bv 64 SITE_ps_unlock2) (Z_to_bv 64 RB) gp tp t0 t1 t2 sp (Z_to_bv 64 RB) (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 f) s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) t3 t4 t5 t6)
        F (Z_to_bv 64 0x20c3b4) fc None m (seg_rom asegs)).
Proof.
  intros until hj2. intros F0 F64 FIMG FH FSH IDX FFC FFS MI. unfold SITE_ps_unlock2, ps_shadow, PS_MAGIC in *.
  pose proof (munch_refl [(f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (SHR : 0x7fff8000 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 8 <= 0x10007fff8000)
    by (pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)); assert (f / 8 + 8 <= 2^44) by (Z.div_mod_to_equations; lia); lia).
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  pose proof (div8_facts f) as Q1.
  zstep. zstep; lfix. zstep; lfix. zstep. zstep. zstep; lfix.
  zstep. if_cases KF; zify_cond KF; [exfalso; rewrite ?unsigned_lit in KF by lia; lia|].
  zstep. do 8 (zstep; lfix).
  unfold ps_w14b_post, SITE_ps_unlock2, PS_RETIRED, ps_retired_shadow. apply evt_done. eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

(* [comment removed for export] *)
Definition ps_w14c_post (rav sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word) (F : bvmap 5 word) (fc : bv 32)
    (idx fl lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 idx) (Z_to_bv 64 fl) a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6)
            F (ret_pc rav) fc None m' (seg_rom asegs)
    /\ munch [(fl, fl + 1)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' fl [C1 (Z_to_bv 8 0)].

Lemma ps_w14c : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word) (f fl lo pd idx : Z) (j : list byte),
  (pd = 0 \/ pd = 16) -> lo <= bv_unsigned sp - 176 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  0 < f -> f + 64 <= lo -> 0 < fl -> fl + 1 <= lo -> 0 <= idx < 2 ^ 31 ->
  stk asegs m lo (bv_unsigned sp + -160 - pd) -> stk asegs m (bv_unsigned sp + -160 - pd) (bv_unsigned sp + -160) ->
  rw_cells asegs m (bv_unsigned sp + -160) (CB 56 j :: ps_ftail s11v s10v s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
  ro_cells asegs m (f + 56) [C8 (Z_to_bv 64 fl)] -> rw_cells asegs m fl [C1 (Z_to_bv 8 1)] -> mem_inv asegs m ->
  evt asegs (ps_w14c_post rav sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v F fc idx fl lo m)
    (MS (mkR (Z_to_bv 64 SITE_ps_unlock2) (Z_to_bv 64 (bv_unsigned sp + -160 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pd)) (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 f) s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) t3 t4 t5 t6)
        F (Z_to_bv 64 0x20c3f4) fc None m (seg_rom asegs)).
Proof.
  intros until j. intros HP HLO HLOS SPH F0 FLO FL0 FLLO IDX ST1 GAP FR FLG FLB MI. unfold SITE_ps_unlock2, ps_ftail in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(fl, fl + 1)] m) as MU; pose proof (wmono_refl asegs m) as WM.
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EUfl : bv_unsigned (Z_to_bv 64 fl) = fl) by (apply unsigned_lit; lia).
  zstep. clear FLG.
  zstep; lfix.
  zstep. zstep.
  do 13 zstep.
  pose proof (stk_merge asegs _ lo (SP + -160 - pd) (SP + -160) ST1 GAP ltac:(lia)) as ST2.
  zstep. release_frame FR ST2 SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold ps_w14c_post. apply evt_done. eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption| assumption].
Qed.
