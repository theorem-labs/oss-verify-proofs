(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac ImageA Arr Walk Image.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout R_small R_m2s R_thread. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs R_prim_defs R_asan_defs R_prim_kit R_glue_defs R_depot_defs R_sec_defs R_secgbb R_qdorec R_qcbrec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Ltac arith_goal := lazymatch goal with
  | |- @eq Z _ _ => idtac | |- @eq nat _ _ => idtac | |- Z.le _ _ => idtac | |- Z.lt _ _ => idtac | |- Z.ge _ _ => idtac
  | |- Z.gt _ _ => idtac | |- le _ _ => idtac | |- lt _ _ => idtac | |- _ /\ _ => idtac | |- _ \/ _ => idtac | |- ~ _ => idtac
  | |- False => idtac end.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof. intros k x r Hk H. exists (x / k)%Z. rewrite <- H. apply Z.div_mod. lia. Qed.
Local Ltac zlit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Local Ltac zget_mod t :=
  lazymatch type of t with
  | (?x mod ?k = ?r)%Z => let H' := fresh "Hzm" in pose proof t as H'
  | ?A /\ ?B => first [ zget_mod constr:(proj1 t) | zget_mod constr:(proj2 t) ]
  end.
Local Ltac zhide :=
  repeat match goal with
  | H : context [(?x mod ?k)%Z] |- _ => zlit x; zlit k; let v := eval cbv in (x mod k)%Z in change (x mod k)%Z with v in H
  end;
  repeat match goal with
  | H : (?x mod ?k = ?r)%Z |- _ =>
      let q := fresh "zq" in let Hq := fresh "Hzq" in
      destruct (zal_ex k x r (eq_refl : (0 < k)%Z) H) as [q Hq]; change (zal k x r) in H
  | H : context [(?x mod ?k = ?r)%Z] |- _ =>
      lazymatch type of H with (_ mod _ = _)%Z => fail | _ => idtac end;
      (try zget_mod H); change (x mod k = r)%Z with (zal k x r) in H
  end;
  repeat match goal with
  | H : context [(2 ^ ?k)%Z] |- _ => let T := type of H in zify_arith_prop T;
      let v := eval cbv in (2 ^ k)%Z in lazymatch v with Zpos _ => change (2 ^ k)%Z with v in H end
  end.

Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.

Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call asegs m mm MU WM end end.
Open Scope bv_scope.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition secdealloc_entry : Z := 0x5df44.

Lemma qcbs_j1 : forall (P : machine_state -> Prop) ra sp gp tp t0 t1 t2 s0 a0 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (SB M : Z),
  rw_cells asegs m i_spacebeg [C8 (Z_to_bv 64 SB)] -> (M < SB \/ SB + 2^37 <= M)%Z -> (0 <= M < 2^64)%Z -> (0 <= SB)%Z ->
  (SB + 2^37 < 2^64)%Z -> mem_inv asegs m ->
  (forall a1', evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 M) (Z_to_bv 64 SB) a1' a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 INST)
                                   (Z_to_bv 64 (2^37)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 0x5d9e4) fc None m (seg_rom asegs))) ->
  evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 M) a0 (Z_to_bv 64 M) a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 INST) s4 s5 s6 s7 s8
                       s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x5d9a4) fc None m (seg_rom asegs)).
Proof.
  intros until M. intros SBC HM HM0 HSB0 HSB1 MI K.
  unfold i_spacebeg, INST, g_instance in *. change (1508824 + 32)%Z with 1508856%Z in SBC.
  zhide.
  zstep. zstep. zstep. zstep.
  destruct HM as [HM|HM].
  - ifT. apply K.
  - ifF. zstep. zstep. ifT. apply K.
Qed.

Lemma qcbs_j2 : forall (P : machine_state -> Prop) ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (SB p : Z),
  rw_cells asegs m i_spacebeg [C8 (Z_to_bv 64 SB)] -> (p < SB \/ SB + 2^37 <= p)%Z -> (0 <= p < 2^64)%Z -> (0 <= SB)%Z ->
  (SB + 2^37 < 2^64)%Z -> mem_inv asegs m ->
  evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 SB) (Z_to_bv 64 (SB + 2^37)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 p)
                       (Z_to_bv 64 INST) (Z_to_bv 64 (2^37)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x5dae4) fc None m (seg_rom asegs)) ->
  evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 INST) (Z_to_bv 64 (2^37))
                       s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x5d9f0) fc None m (seg_rom asegs)).
Proof.
  intros until p. intros SBC HP HP0 HSB0 HSB1 MI K.
  unfold i_spacebeg, INST, g_instance in *. change (1508824 + 32)%Z with 1508856%Z in SBC.
  zhide.
  zstep. zstep. zstep. zstep.
  destruct HP as [HP|HP].
  - ifF. zstep. exact K.
  - ifT. zstep. ifT. exact K.
Qed.

Lemma qcbs_j3 : forall (P : machine_state -> Prop) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (SB p : Z),
  rw_cells asegs m i_spacebeg [C8 (Z_to_bv 64 SB)] -> (p < SB \/ SB + 2^37 <= p)%Z -> (0 <= p < 2^64)%Z -> (0 <= SB)%Z ->
  (SB + 2^37 < 2^64)%Z -> mem_inv asegs m ->
  (forall s4', evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 SB) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 p) (Z_to_bv 64 INST)
                                   s4' s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 0x5db80) fc None m (seg_rom asegs))) ->
  evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 p) (Z_to_bv 64 INST) (Z_to_bv 64 (2^37))
                       s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x5db14) fc None m (seg_rom asegs)).
Proof.
  intros until p. intros SBC HP HP0 HSB0 HSB1 MI K.
  unfold i_spacebeg, INST, g_instance in *. change (1508824 + 32)%Z with 1508856%Z in SBC.
  zhide.
  zstep. zstep.
  destruct HP as [HP|HP].
  - ifT. apply K.
  - ifF. zstep. zstep. ifT. apply K.
Qed.

Lemma gbb_mem_frame : forall PAB nres n ws MB MSZ SZ IDX W (m m' : mem), gbb_mem PAB nres n ws MB MSZ SZ IDX m ->
  munch W m m' -> wmono asegs m m' -> disjoint_from W img_hull_lo (img_hull_hi - img_hull_lo) ->
  disjoint_from W PAB (8 * Z.of_nat (length ws)) -> disjoint_from W MB 32 -> gbb_mem PAB nres n ws MB MSZ SZ IDX m'.
Proof.
  intros PAB nres n ws MB MSZ SZ IDX W m m' (PG & (CH & NR & MX) & PAD & ARR & HH) MU WM H1 H2 H3.
  unfold img_hull_lo, img_hull_hi in H1. unfold gbb_mem, sec_page, sec_core, sec_pad, shdr in *.
  change i_sec_mutex with 1509504%Z in *. change i_sec_page with 1508888%Z in *. change i_sec_chunks with 1508896%Z in *.
  change i_sec_nres with 1508936%Z in *.
  split; [| split; [split; [| split]| split; [| split]]].
  - apply (rw_cells_transport asegs W m m' _ _ PG MU WM). cbn [cells_size csize Nat.add Z.of_nat]. eapply dep_disj_sub; [exact H1| |]; lia.
  - apply (rw_cells_transport asegs W m m' _ _ CH MU WM). cbn [cells_size csize Nat.add Z.of_nat]. eapply dep_disj_sub; [exact H1| |]; lia.
  - apply (rw_cells_transport asegs W m m' _ _ NR MU WM). cbn [cells_size csize Nat.add Z.of_nat]. eapply dep_disj_sub; [exact H1| |]; lia.
  - apply (rw_cells_transport asegs W m m' _ _ MX MU WM). cbn [cells_size csize Nat.add Z.of_nat]. eapply dep_disj_sub; [exact H1| |]; lia.
  - apply (rw_cells_transport asegs W m m' _ _ PAD MU WM). cbn [cells_size csize Nat.add Z.of_nat length]. eapply dep_disj_sub; [exact H1| |]; lia.
  - apply (u64arr_transport asegs W m m' _ _ ARR MU WM). exact H2.
  - apply (rw_cells_transport asegs W m m' _ _ HH MU WM). exact H3.
Qed.

Lemma qthread_cells_frame2 : forall TCX T W (m m' : mem), thread_cells TCX T m -> munch W m m' -> wmono asegs m m' ->
  disjoint_from W 1520800 8 -> disjoint_from W 6979088 8 -> disjoint_from W 7115552 8 -> disjoint_from W (TCX + 0x98) 8 ->
  thread_cells TCX T m'.
Proof.
  intros TCX T W m m' [(KI & K & TS & T0) TT] MU WM H1 H2 H3 H4.
  unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main in *.
  split; [split; [| split; [| split]]|].
  - apply (rw_cells_transport asegs W m m' _ _ KI MU WM). cbn [cells_size csize Nat.add]. eapply dep_disj_sub; [exact H1| |]; lia.
  - apply (rw_cells_transport asegs W m m' _ _ K MU WM). cbn [cells_size csize Nat.add]. eapply dep_disj_sub; [exact H1| |]; lia.
  - apply (rw_cells_transport asegs W m m' _ _ TS MU WM). exact H2.
  - apply (rw_cells_transport asegs W m m' _ _ T0 MU WM). exact H3.
  - apply (rw_cells_transport asegs W m m' _ _ TT MU WM). exact H4.
Qed.

Definition qcbrec_sec_W (T sp : Z) : list (Z * Z) := [(i_sec_mutex, i_sec_mutex + 4); (T + 2840, T + 2856); (sp - 80, sp)]%Z.

Definition qcbrec_sec_post (rao sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (p : Z) (W : list (Z * Z)) (lo : Z) (P : mem -> Prop) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR rao sp gp tp t0' t1' t2' s0o s1o (Z_to_bv 64 SEC) (Z_to_bv 64 GSTAT) (Z_to_bv 64 p) a3' a4' a5' a6' a7'
                  s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 secdealloc_entry) fc None m' (seg_rom asegs)
    /\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ P m' /\ stk asegs m' lo (bv_unsigned sp).

Definition qcbs_after (PAB nres n0 : Z) (ws : list word) (MB MSZ SZ IDX M n b1 T rf rfd : Z) (m : mem) : Prop :=
  gbb_mem PAB nres n0 ws MB MSZ SZ IDX m
  /\ rw_cells asegs m M [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n)]
  /\ rw_cells asegs m (T + 2840) [C8 (Z_to_bv 64 (rf + 1)); C8 (Z_to_bv 64 (rfd + n))].

Lemma qcbrec_sec_spec : forall ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (ACEIL SB PAB nres n0 : Z) (ws : list word) (MB MSZ SZ IDX M n b1 TCX T rf rfd CBP lo : Z),
  gbb_mem PAB nres n0 ws MB MSZ SZ IDX m ->
  (0 < PAB)%Z -> (PAB + 8 * Z.of_nat (length ws) <= lo)%Z -> hide (PAB + 8 * Z.of_nat (length ws) <= img_hull_lo \/ img_hull_hi <= PAB)%Z ->
  (1 <= n0 <= Z.of_nat (length ws))%Z -> In MB (firstn (Z.to_nat n0) (map bv_unsigned ws)) ->
  Forall (fun ch => ch <= M -> ch <= MB)%Z (firstn (Z.to_nat n0) (map bv_unsigned ws)) ->
  (0 < MB)%Z -> (MB mod 4096 = 0)%Z -> (MB + MSZ <= lo)%Z -> (MB + 4096 <= M)%Z -> (M + 16 <= MB + MSZ)%Z ->
  hide (MB + MSZ <= img_hull_lo \/ img_hull_hi <= MB)%Z -> hide (MB + MSZ <= SB \/ SB + 2^37 <= MB)%Z ->
  (1 <= n < 2^32)%Z -> (0 <= b1 < 256)%Z ->
  rw_cells asegs m M [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n)] ->
  rw_cells asegs m i_spacebeg [C8 (Z_to_bv 64 SB)] -> SB_ok ACEIL SB ->
  thread_cells TCX T m -> tsep ACEIL SB T TCX ->
  hide (PAB + 8 * Z.of_nat (length ws) <= T \/ T + 4096 <= PAB)%Z -> hide (MB + MSZ <= T \/ T + 4096 <= MB)%Z ->
  rw_cells asegs m (T + 2840) [C8 (Z_to_bv 64 rf); C8 (Z_to_bv 64 rfd)] ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 80)%Z -> (ACEIL <= lo)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  mem_inv asegs m ->
  evt asegs (qcbrec_sec_post ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (MB + 4096)
               (qcbrec_sec_W T (bv_unsigned sp)) lo (qcbs_after PAB nres n0 ws MB MSZ SZ IDX M n b1 T rf rfd) m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 CBP) (Z_to_bv 64 M) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 qcbrec_entry) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros GM HPAB HPABl HPABs Hn0 HIN HMAX HMB0 HMBal HMBl HM1 HM2 HMBs HMBSB Hn Hb1 HD SBC HSBo TC TSEP HPABT HMBT
    STS ST HLO HAC HSP MI.
  pose proof HSBo as (HSB1 & HSB2 & HSB3 & HSB4). apply box in HSB2. unfold kHighShadowEnd in *.
  pose proof TSEP as (TOK & HTCX0 & HTCXA & HTCXi & HTSB & HTCXSB & HTX & HTs & HTCXs). destruct TOK as (HT0 & HT4k & HTA & HA47 & HTi).
  apply box in HT4k. apply box in HMBal.
  apply box in HTCXi. apply box in HTSB. apply box in HTCXSB. apply box in HTX. apply box in HTs. apply box in HTCXs. apply box in HTi.
  apply box in HIN. apply box in HMAX.
  unfold hide in HPABs, HMBs, HMBSB, HPABT, HMBT. apply box in HPABs. apply box in HMBs. apply box in HMBSB. apply box in HPABT.
  apply box in HMBT.
  apply box in GM. apply box in TC. apply box in HD. apply box in STS.
  unfold i_spacebeg, INST, g_instance, qcbrec_entry in *. change (1508824 + 32)%Z with 1508856%Z in SBC.
  pose proof (munch_refl (qcbrec_sec_W T (bv_unsigned sp)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MUp.
  unfold qcbrec_sec_W, i_sec_mutex, INST, g_instance in MU. change (1508824 + 680)%Z with 1509504%Z in MU.
  carve_frame 48%nat ST.
  zhide.
  do 7 zstep. do 4 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (gbb_mem_frame _ _ _ _ _ _ _ _ _ m mm (unbox _ GM) MUp WM ltac:(cbn [disjoint_from]; unfold img_hull_lo, img_hull_hi; lia)
                  ltac:(cbn [disjoint_from]; lia) ltac:(cbn [disjoint_from]; lia)) as GMm;
    pose proof (qthread_cells_frame _ _ _ m mm (unbox _ TC) MUp WM ltac:(cbn [disjoint_from]; unfold img_hull_lo, img_hull_hi; lia)
                  ltac:(cbn [disjoint_from]; lia)) as TCm;
    pose proof (rw_cells_transport asegs _ m mm _ _ (unbox _ HD) MUp WM ltac:(cbn [disjoint_from cells_size csize Nat.add Z.of_nat]; lia))
      as HDm;
    pose proof (rw_cells_transport asegs _ m mm _ _ (unbox _ STS) MUp WM ltac:(cbn [disjoint_from cells_size csize Nat.add Z.of_nat]; lia))
      as STSm end.
  clear MUp GM TC HD STS. apply box in TCm. apply box in HDm. apply box in STSm.
  eapply qcbs_j1; [eassumption| pose proof (unbox _ HMBSB); lia| lia| lia| lia| eassumption|]. intros a1'.
  do 3 zstep.
  sp_facts.
  apply box in SBC. lazymatch goal with H : rw_cells asegs _ (bv_unsigned sp + -48) _ |- _ => apply box in H end.
  eapply evt_cut.
  { eapply (gbb_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo PAB nres n0 ws MB MSZ SZ IDX M).
    all: rewrite ?Esp; try eassumption; try (arith_goal; lia); try (unfold kHighShadowEnd; lia). }
  intros ms1 (q0 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & q8 & q9 & q10 & q11 & q12 & q13 & mg & E1 & MU1 & WM1 & MI1 & ST1 & GM1).
  subst ms1. unfold i_sec_mutex, INST, g_instance in MU1. change (1508824 + 680)%Z with 1509504%Z in MU1. rewrite Esp in MU1, ST1.
  clear GMm.
  replace (ret_pc (Z_to_bv 64 383472)) with (Z_to_bv 64 383472) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  lazymatch goal with FRb : boxed (rw_cells asegs _ (bv_unsigned sp + -48) _) |- _ =>
    pose proof (rw_cells_transport asegs _ _ mg _ _ (unbox _ FRb) MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add Z.of_nat]; lia)) as FR1;
    clear FRb end.
  pose proof (rw_cells_transport asegs _ _ mg _ _ (unbox _ SBC) MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add Z.of_nat]; lia)) as SBC1.
  pose proof (qthread_cells_frame2 _ _ _ _ mg (unbox _ TCm) MU1 WM1 ltac:(cbn [disjoint_from]; lia) ltac:(cbn [disjoint_from]; lia)
                ltac:(cbn [disjoint_from]; lia) ltac:(pose proof (unbox _ HTCXi) as H0; unfold img_hull_lo, img_hull_hi in H0; cbn [disjoint_from]; lia)) as TC1.
  pose proof (rw_cells_transport asegs _ _ mg _ _ (unbox _ HDm) MU1 WM1
                ltac:(pose proof (unbox _ HMBs) as H0; unfold img_hull_lo, img_hull_hi in H0; cbn [disjoint_from cells_size csize Nat.add Z.of_nat]; lia))
    as HD1.
  pose proof (rw_cells_transport asegs _ _ mg _ _ (unbox _ STSm) MU1 WM1
                ltac:(pose proof (unbox _ HTi) as H0; unfold img_hull_lo, img_hull_hi in H0; cbn [disjoint_from cells_size csize Nat.add Z.of_nat]; lia))
    as STS1.
  clear SBC TCm HDm STSm.
  lazymatch goal with H : munch _ ?m0 mg |- _ => match goal with H' : munch _ m0 m0 |- _ => fail 1 | _ => idtac end end.
  eapply qcbs_j2; [eassumption| pose proof (unbox _ HMBSB); lia| lia| lia| lia| eassumption|].
  apply (munch_trans _ m _ mg) in MU; [| eapply munch_weaken; [| exact MU1]; intros xx Hx; clear - Hx; cbn [outside] in *; lia].
  apply (wmono_trans asegs m _ mg) in WM; [| exact WM1]. clear MU1 WM1.
  pose proof (munch_refl [(T + 2840, T + 2856); (bv_unsigned sp - 80, bv_unsigned sp)]%Z mg) as MUg.
  pose proof (wmono_refl asegs mg) as WMg. apply box in GM1.

  zstep.
  call (gcts_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ TCX T lo).
  all: rewrite ?Esp in *; try (arith_goal; lia); try eassumption.
  clear TC1.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (munch_refl [(T + 2840, T + 2856)]%Z mm) as MUb; pose proof (wmono_refl asegs mm) as WMb end.
  do 8 zstep.
  apply box in HD1. apply box in SBC1.
  do 2 zstep.
  zstep. ifF.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with MUb' : munch [(_, _)] ?m3 mm, WMb' : wmono _ ?m3 mm |- _ =>
      pose proof (rw_cells_transport asegs _ m3 mm _ _ (unbox _ HD1) MUb' WMb'
                    ltac:(pose proof (unbox _ HMBT); cbn [disjoint_from cells_size csize Nat.add Z.of_nat]; lia)) as HD2;
      pose proof (rw_cells_transport asegs _ m3 mm _ _ (unbox _ SBC1) MUb' WMb'
                    ltac:(pose proof (unbox _ HTi) as H0; unfold img_hull_lo, img_hull_hi in H0;
                          cbn [disjoint_from cells_size csize Nat.add Z.of_nat]; lia)) as SBC2 end end.
  clear HD1 SBC1 MUb WMb.
  rewrite (Z.mod_small n 4294967296) in * by lia.
  eapply qcbs_j3; [eassumption| pose proof (unbox _ HMBSB); lia| lia| lia| lia| eassumption|]. intros s4'.
  do 11 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with H : stk asegs mm _ _ |- _ => match goal with FRx : rw_cells asegs mm (bv_unsigned sp + -48) _ |- _ =>
      release_frame FRx H (bv_unsigned sp) end end end.
  apply evt_done. unfold qcbrec_sec_post, secdealloc_entry.
  do 13 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [| eassumption].
  unfold qcbs_after. split; [| split; [eassumption|]].
  - lazymatch goal with |- gbb_mem _ _ _ _ _ _ _ _ ?mm => match goal with MUg' : munch [(_, _); (_, _)] ?m3 mm, WMg' : wmono _ ?m3 mm |- _ =>
      apply (gbb_mem_frame _ _ _ _ _ _ _ _ _ m3 mm (unbox _ GM1) MUg' WMg') end end.
    + pose proof (unbox _ HTi) as H0. unfold img_hull_lo, img_hull_hi in *. cbn [disjoint_from]. lia.
    + pose proof (unbox _ HPABT) as H0. cbn [disjoint_from]. lia.
    + pose proof (unbox _ HMBT) as H0. cbn [disjoint_from]. lia.
  - replace (rfd + n)%Z with (n + rfd)%Z by lia. eassumption.
Qed.
