(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim SjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjTape SjTapeList SjTapeTile.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 RT_iface5 D_defs D_kit D_clx D_libiface D_auxv Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_fzwA Atp_activewA Atp_defsA Pj_lftoi1A Pj_defsA Pj_os_defsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition EL_LFTOI_A : Z := 0xae648.
Definition EL_SMRET_A : Z := 0xb1690.
Definition EL_SPLITRET_A : Z := 0xb18e8.
Definition EL_VEC2_A : Z := 0xb0ffc.
Definition EL_PIDRET_A : Z := 0xb1160.
Definition EL_GATE_A : Z := 0xb1184.
Definition EL_EXIT_A : Z := 0xb1188.
Definition EL_EXIT2_A : Z := 0xb11c4.
Definition EL_EPI_A : Z := 0xb1214.
Definition EL_DISPATCH_A : Z := 0xb1b78.
Definition EL_JTAB_A : Z := 0x23684.
Definition EL_HDR10_A : Z := 0xb1be0.
Definition EL_PAD_A : Z := 0xb15f8.
Definition EL_LRET_A : Z := 0xb1f84.

Definition EL_ARM8_A : Z := 0xb1284.   Definition EL_ARM22_A : Z := 0xb1c80.  Definition EL_ARM23_A : Z := 0xb1c5c.  Definition EL_ARM24_A : Z := 0xb1380.
Definition EL_ARM25_A : Z := 0xb138c.  Definition EL_ARM26_A : Z := 0xb1c68.  Definition EL_ARM28_A : Z := 0xb1354.  Definition EL_ARM29_A : Z := 0xb1368.
Definition EL_ARM30_A : Z := 0xb1e60.  Definition EL_ARM31_A : Z := 0xb1ce0.
Definition el_arm_pcA (a : Z) : Z :=
  if a =? 8 then EL_ARM8_A else if a =? 22 then EL_ARM22_A else if a =? 23 then EL_ARM23_A else if a =? 24 then EL_ARM24_A
  else if a =? 25 then EL_ARM25_A else if a =? 26 then EL_ARM26_A else if a =? 28 then EL_ARM28_A else if a =? 29 then EL_ARM29_A
  else if a =? 30 then EL_ARM30_A else if a =? 31 then EL_ARM31_A else EL_EXIT_A.
Definition el_liveA (a : Z) : bool :=
  (a =? 8) || (a =? 22) || (a =? 23) || (a =? 24) || (a =? 25) || (a =? 26) || (a =? 28) || (a =? 29) || (a =? 30) || (a =? 31).

Definition EL_H8_A : Z := 0xb21d0.
Definition EL_H22_A : Z := 0xb22f4.
Definition EL_H23_A : Z := 0xb2ce8.
Definition EL_H24_A : Z := 0xb2340.
Definition EL_H25_A : Z := 0xb304c.
Definition EL_H26_A : Z := ATP_ELEM_A.
Definition EL_H28_A : Z := 0xb2b74.
Definition EL_H29_A : Z := 0xb2e4c.
Definition EL_H30_A : Z := 0xb3258.
Definition EL_OSCTOR_A : Z := PJ_OS_CTOR_A.
Definition EL_OSDTOR_A : Z := 0xafa98.
Definition EL_DUMP_A : Z := 0xb0b30.
Definition EL_DUMPRET_A : Z := 0xaf1cc.
Definition EL_STRNCASECMP_STUB_A : Z := 0x6bb9c.
Definition EL_CXA_ALLOC_A : Z := 0x10acfc.
Definition EL_CXA_THROW_A : Z := 0x10af00.
Definition EL_BEGIN_CATCH_A : Z := 0x10ad54. Definition EL_END_CATCH_A : Z := 0x10af7c.

Definition EL_UNW_A : Z := 0x6ab290.
Definition EL_EHG_A : Z := 0x6a9978.
Definition EL_TPLOC_A : Z := TPV_A - 48.
Definition EL_GLOC_A : Z := LIBC_A + 56.

Definition EL_LIB_FP : list (Z * Z) := LIB_FP ++ [(EL_UNW_A, EL_UNW_A + 8); (EL_EHG_A, EL_EHG_A + 12); (EL_TPLOC_A, EL_TPLOC_A + 8)].

Definition uw_cellsA (uw : bool) : list cell :=
  if uw then [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  else repeat (C1 (Z_to_bv 8 0)) 8.
Definition el_unwA (m : mem) : Prop := exists uw, rw_cells bsegs m EL_UNW_A (uw_cellsA uw).
Definition el_ehgA (m : mem) : Prop := rw_cells bsegs m EL_EHG_A [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].
Definition el_tplocA (m : mem) : Prop := rw_cells bsegs m EL_TPLOC_A [C8 (Z_to_bv 64 EL_GLOC_A)].
Definition el_xA (m : mem) : Prop := el_ehgA m /\ el_unwA m /\ el_tplocA m.
Definition el_libA (m : mem) : Prop := pj_libA sj_lib m /\ el_xA m.

Definition el_x_rng (x : Z) : Prop := (EL_EHG_A <= x < EL_EHG_A + 12) \/ (EL_UNW_A <= x < EL_UNW_A + 8) \/ (EL_TPLOC_A <= x < EL_TPLOC_A + 8).

Lemma uw_cellsA_size : forall uw, cells_size (uw_cellsA uw) = 8%nat.
Proof. intros [|]; reflexivity. Qed.
Lemma el_xA_agree : forall m m', el_xA m -> agree_on el_x_rng m m' -> el_xA m'.
Proof.
  intros m m' (H1 & (uw & H2) & H3) AG. unfold el_x_rng in AG. split; [| split].
  - eapply rw_cells_agree_nw; [exact H1|]. intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. lia.
  - exists uw. eapply rw_cells_agree_nw; [exact H2|]. intros a Ha. apply AG. rewrite uw_cellsA_size in Ha. lia.
  - eapply rw_cells_agree_nw; [exact H3|]. intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. lia.
Qed.
Lemma el_x_rng_static : forall x, el_x_rng x -> client_static x.
Proof. intros x Hx. unfold el_x_rng, EL_EHG_A, EL_UNW_A, EL_TPLOC_A, TPV_A in Hx. apply client_static_intro; lia. Qed.

Definition el_localsA (j0 : list byte) (sptr slen idx os act : Z) (j64 : list byte) (f : Z) (jres : list byte) (j120 : list byte) (sel fdd fds : Z) (j145 : list byte) : list cell :=
  [CB 24 j0; C8 (Z_to_bv 64 sptr); C8 (Z_to_bv 64 slen); C8 (Z_to_bv 64 idx); C8 (Z_to_bv 64 os); C8 (Z_to_bv 64 act); CB 24 j64; C8 (Z_to_bv 64 f);
   CB 24 jres; CB 4 j120; C4 (Z_to_bv 64 sel); C8 (Z_to_bv 64 fdd); C8 (Z_to_bv 64 fds); C1 (Z_to_bv 8 0); CB 7 j145].
Lemma el_localsA_size : forall j0 sptr slen idx os act j64 f jres j120 sel fdd fds j145,
  cells_size (el_localsA j0 sptr slen idx os act j64 f jres j120 sel fdd fds j145) = 152%nat.
Proof. intros. reflexivity. Qed.

Definition el_shbytesA (vec par elm os : Z) : list Z :=
  [-15; -15; -15; -15; vec; vec; vec; -14; -14; -14; -14; -14; par; par; par; par; par; par; par; par; par; par; -14; -14; -14; -14; elm; elm; -14; -14]
  ++ repeat os 36 ++ repeat (-13) 10.
Definition el_shadowA (vec par elm os : Z) (t : list byte) : list cell := map (fun z => C1 (Z_to_bv 8 z)) (el_shbytesA vec par elm os) ++ [CB 52 t].

Definition el_shadow_armA (t : list byte) : list cell := el_shadowA 0 0 0 (-8) t.
Lemma el_shbytesA_length : forall a b c d, length (el_shbytesA a b c d) = 76%nat.
Proof. intros. reflexivity. Qed.
Lemma el_shadowA_size : forall a b c d t, cells_size (el_shadowA a b c d t) = 128%nat.
Proof. intros. unfold el_shadowA. rewrite cells_size_app. cbn. reflexivity. Qed.

Record lfA : Type := mkLF { lf_usp : Z; lf_S1 : Z; lf_F : Z; lf_lo : Z }.
Record lfA_ok (X : lfA) : Prop := mkLFok {
  lk_S1 : lf_usp X - 144 <= lf_S1 X <= lf_usp X - 128 /\ lf_S1 X mod 32 = 0;
  lk_usp : lf_usp X + 16 <= USTACK_TOP /\ lf_usp X mod 16 = 0;
  lk_lo : 0x7fff7f800000 <= lf_lo X /\ lf_lo X + FUZZ_STACK <= lf_usp X;
  lk_F : 0 < lf_F X /\ lf_F X mod 64 = 0 /\ SEGTOP_A <= lf_F X /\ lf_F X + 512 <= lf_lo X;
  lk_shad : (lf_F X + 512 <= shad (lf_F X) \/ shad (lf_F X) + 64 <= lf_F X) /\ SHB <= shad (lf_F X) /\ shad (lf_F X) + 65 <= lf_lo X }.

Definition lf_envA (X : lfA) (E : aenvA) : Prop :=
  ae_DOC E = lf_F X + 56 /\ ae_fD E = lf_F X /\ ae_kD E = 3%nat /\ ae_lo E = lf_lo X /\ ae_hi E = lf_usp X.

Definition EL_DUMP_STACK_A : Z := 0x8000 + RT_STACK.
Definition EL_THROW_STACK_A : Z := 0x6000 + NORET_DEPTH.
Definition arm_needA (a : Z) : Z :=
  if a =? 26 then ATP_ROOT_STACK_A + 64 else if a =? 31 then EL_DUMP_STACK_A
  else if (a =? 22) || (a =? 23) || (a =? 24) then EL_THROW_STACK_A else 256 + RT_STACK.

Definition EL_DUMP_CW : Z := 24.
Definition EL_DUMP_C0 : Z := 64.
Definition EL_DUMP_CSB : Z := 4.
Definition arm_costA (a n sn L : Z) : Z :=
  if a =? 26 then ATP_ROOT_COST_A L else if a =? 31 then EL_DUMP_C0 + EL_DUMP_CW * n + EL_DUMP_CSB * sn
  else if (a =? 22) || (a =? 23) || (a =? 24) then mcost EXC_SIZE + 16 else 0.
Definition arm_xliveA (a : Z) : Z := if (a =? 26) || (a =? 22) || (a =? 23) || (a =? 24) then 1 else 0.
Definition arm_framesA (a : Z) : nat := if a =? 26 then ATP_ROOT_FRAMES_A else if a =? 31 then 8%nat else 0%nat.

Definition OSDUMPA (m : mem) (OS : Z) : Prop :=
  exists pb pp ep fill dum j148 j284, rw_cells bsegs m OS (os_cellsA OS pb pp ep fill dum j148 j284).
Lemma OSFRESHA_dump : forall m OS, OSFRESHA m OS -> OSDUMPA m OS.
Proof. intros m OS (dum & j148 & j284 & H). exists (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), 0xffffffff, dum, j148, j284. exact H. Qed.
Lemma OSUSEDA_dump : forall m OS, OSUSEDA m OS -> OSDUMPA m OS.
Proof. intros m OS (pb & pp & ep & dum & j148 & j284 & H). exists pb, pp, ep, 0x20, dum, j148, j284. exact H. Qed.
Lemma OSDUMPA_loc : forall m m' OS, OSDUMPA m OS -> agree_on (fun a => OS <= a < OS + 288) m m' -> OSDUMPA m' OS.
Proof.
  intros m m' OS (pb & pp & ep & fill & dum & j148 & j284 & H) AG. exists pb, pp, ep, fill, dum, j148, j284.
  eapply rw_cells_agree_nw; [exact H|]. intros a Ha. apply AG. rewrite os_cellsA_size in Ha. lia.
Qed.

Section Stmts.
Variable RT : rt_sig.
Variable PMc : Model -> Prop.
Notation aevt := (aevt RT PMc).
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition artxA (W : Z -> rts RT -> mem -> Prop) (w : bool) (c : Z) (Σ : rts RT) (m : mem) : Prop :=
  if w then W c Σ m else ART RT Σ m /\ c = rt_credit RT Σ.

Definition lf_st (X : lfA) (pc : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR ra (wz (lf_S1 X)) gp (wz TPV_A) t0 t1 t2 (wz (lf_usp X)) (wz (lf_S1 X)) a0 a1 a2 a3 a4 a5 a6 a7
          (wz (lf_F X)) (wz (shad (lf_F X))) (wz (lf_F X + 32)) (wz (lf_F X + 144)) s6 s7 (wz (lf_F X)) s9 s10 s11 t3 t4 t5 t6)
     F (wz pc) fc None m (seg_rom bsegs).

Definition arm_memA (X : lfA) (E : aenvA) (sel idx : Z) (jr jos t : list byte) (m : mem) : Prop :=
  rw_cells bsegs m (lf_S1 X + 24) [C8 (wz (ae_PTR E)); C8 (wz (zlength (ae_p1 E))); C8 (wz idx); C8 (wz (lf_F X + 144))]
  /\ rw_cells bsegs m (lf_S1 X + 96) [CB 24 jr]
  /\ rw_cells bsegs m (lf_S1 X + 124) [C4 (wz sel)]
  /\ rw_cells bsegs m (lf_F X + 208) [C8 (wz (ae_DOC E)); C8 (wz 1)]
  /\ rw_cells bsegs m (lf_F X + 144) [CB 288 jos]
  /\ rw_cells bsegs m (shad (lf_F X)) (el_shadow_armA t)
  /\ AINV_A E m /\ el_libA m /\ libc_nl m /\ io_ssp m.

Definition arm_WA (X : lfA) : list (Z * Z) :=
  [(lf_S1 X + 96, lf_S1 X + 120); (lf_F X + 144, lf_F X + 432); (shad (lf_F X) + 30, shad (lf_F X) + 66);
   (EL_EHG_A, EL_EHG_A + 12); (EL_TPLOC_A, EL_TPLOC_A + 8)] ++ EL_LIB_FP.

Definition arm_postA (W : Z -> rts RT -> mem -> Prop) (a : Z) (w : bool) (c : Z) (X : lfA) (E : aenvA) (sel idx : Z) (t : list byte)
    (Σ Σ' : rts RT) (m m' : mem) (fc' : bv 32) : Prop :=
  artxA W w c Σ' m' /\ mem_inv bsegs m' /\ stk bsegs m' (lf_lo X) (lf_S1 X) /\ frm0 fc'
  /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
  /\ rt_credit RT Σ - arm_costA a (ae_n E) (ae_sn E) (zlength (ae_p1 E)) <= c
  /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (lf_S1 X) (arm_WA X) m m'
  /\ (exists jr' jos', arm_memA X E sel idx jr' jos' t m')
  /\ (w = true -> (a = 22 \/ a = 23 \/ a = 24)).

Definition arm_cpsA (W : Z -> rts RT -> mem -> Prop) (a : Z) : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (X : lfA) (E : aenvA) (sel idx : Z) (jr jos t : list byte)
         (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  fdfs_only PMc -> mat_stable PMc ->
  lfA_ok X -> aenvA_ok E -> lf_envA X E -> tape_wfS (ae_T E) (ae_S E) (ae_sn E) ck_any (ae_n E) ->
  0 <= sel < 8 -> 0 <= idx < 2^64 ->
  a_live RT Σ E -> rt_frames RT Σ = [(lf_F X, 3%nat)] -> lposA (rt_live RT Σ) ->
  Z.of_nat (length (rt_live RT Σ)) + arm_xliveA a <= LIVE_MAX ->
  arm_costA a (ae_n E) (ae_sn E) (zlength (ae_p1 E)) <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m (lf_lo X) (lf_S1 X) -> lf_lo X + arm_needA a <= lf_S1 X ->
  arm_memA X E sel idx jr jos t m -> frm0 fc ->
  el_xdataA m -> el_auxvA (lf_usp X) m -> lf_usp X <= rt_sp0 RT Σ <= lf_usp X + FUZZ_SP0GAP ->
  (forall (w : bool) (c : Z) (Σ' : rts RT) (m' : mem) (fc' : bv 32) (F' : bvmap 5 word)
          (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s6' s7' s9' s10' s11' t3' t4' t5' t6' : word),
     arm_postA W a w c X E sel idx t Σ Σ' m m' fc' ->
     aevt Σ' K (lf_st X EL_EXIT_A ra' gp t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s6' s7' s9' s10' s11' t3' t4' t5' t6' F' fc' m')) ->
  aevt Σ K (lf_st X (el_arm_pcA a) ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz (lf_F X + 208)) (wz 0) s9 s10 (wz (lf_F X + 56)) t3 t4 t5 t6 F fc m).

Definition lret_postA (W : Z -> rts RT -> mem -> Prop) (a c : Z) (X : lfA) (E : aenvA) (sel idx : Z) (t : list byte)
    (Σ Σ' : rts RT) (m m' : mem) (fc' : bv 32) : Prop :=
  arm_postA W a true c X E sel idx t Σ Σ' m m' fc'.

Definition dump_cpsA : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (X : lfA) (E : aenvA) (OS : Z) (t : list byte)
         (gp t0 t1 t2 a2 a3 a4 a5 a6 a7 s6 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  fdfs_only PMc -> mat_stable PMc ->
  lfA_ok X -> aenvA_ok E -> lf_envA X E -> tape_wfS (ae_T E) (ae_S E) (ae_sn E) ck_any (ae_n E) -> OS = lf_F X + 144 ->
  a_live RT Σ E -> rt_frames RT Σ = [(lf_F X, 3%nat)] ->
  EL_DUMP_C0 - 2 + EL_DUMP_CW * ae_n E + EL_DUMP_CSB * ae_sn E <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m (lf_lo X) (lf_S1 X) -> lf_lo X + EL_DUMP_STACK_A <= lf_S1 X + 96 ->
  AINV_A E m -> el_libA m -> LOCBA m -> libc_nl m -> io_ssp m ->
  OSFRESHA m OS -> bytes_at bsegs m (shad OS) (repeat z8 36) -> frm0 fc ->
  (forall (Σ' : rts RT) (m' : mem) (fc' : bv 32) (F' : bvmap 5 word)
          (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
     ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' (lf_lo X) (lf_S1 X) -> frm0 fc' ->
     rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ - (EL_DUMP_C0 - 2 + EL_DUMP_CW * ae_n E + EL_DUMP_CSB * ae_sn E) <= rt_credit RT Σ' ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (lf_S1 X) ([(OS, OS + 288); (EL_TPLOC_A, EL_TPLOC_A + 8)] ++ EL_LIB_FP) m m' ->
     AINV_A E m' -> el_libA m' -> LOCBA m' -> OSDUMPA m' OS ->
     aevt Σ' K (MS (mkR (wz EL_DUMPRET_A) (wz (lf_S1 X)) gp (wz TPV_A) t0' t1' t2' (wz (lf_usp X)) (wz (lf_S1 X)) a0' a1' a2' a3' a4' a5' a6' a7'
                       (wz (lf_F X)) (wz (shad (lf_F X))) (wz (lf_F X + 32)) (wz (lf_F X + 144)) s6 (wz (lf_F X + 272)) (wz (lf_F X)) s9 s10 s11 t3' t4' t5' t6')
                  F' (wz EL_DUMPRET_A) fc' None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR (wz EL_DUMPRET_A) (wz (lf_S1 X)) gp (wz TPV_A) t0 t1 t2 (wz (lf_usp X)) (wz (lf_S1 X)) (wz (ae_DOC E)) (wz (OS + 128)) a2 a3 a4 a5 a6 a7
                  (wz (lf_F X)) (wz (shad (lf_F X))) (wz (lf_F X + 32)) (wz (lf_F X + 144)) s6 (wz (lf_F X + 272)) (wz (lf_F X)) s9 s10 s11 t3 t4 t5 t6)
             F (wz EL_DUMP_A) fc None m (seg_rom bsegs)).

Definition EL_OSDTOR_STACK_A : Z := 32 + 64 + RT_STACK.
Definition osdtor_cpsA : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (OS q lo fO : Z) (kO : nat)
         (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  fdfs_only PMc -> mat_stable PMc ->
  In (fO, kO) (rt_frames RT Σ) -> fO <= OS -> OS + 288 <= fO + fs_size kO - 8 -> OS mod 16 = 0 ->
  OSDUMPA m OS -> bytes_at bsegs m (shad OS) (repeat z8 36) -> pj_locA m -> libc_nl m -> lockwA m ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo q -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + EL_OSDTOR_STACK_A <= q ->
  q + 16 <= USTACK_TOP -> q mod 16 = 0 ->
  (forall t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     ART RT Σ m' -> mem_inv bsegs m' -> stk bsegs m' lo q -> (exists jos, rw_cells bsegs m' OS [CB 288 jos]) -> pj_locA m' ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(OS, OS + 288)] m m' ->
     aevt Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz OS) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz EL_OSDTOR_A) fc None m (seg_rom bsegs)).

End Stmts.
