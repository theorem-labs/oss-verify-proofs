(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ImageA Arr Walk SysStep ITree StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow R_secalloc_math.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout R_small R_m2s R_thread R_cache_defs R_prim_defs R_glue_defs R_sec_defs F_memset R_setshadow R_poison R_secalloc_ps0 R_mmapordie R_secalloc R_secalloc_p2 R_secalloc_p3 R_secalloc_p4 R_secalloc_B0 R_flushshadow R_secdealloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Ltac clear_big := repeat match goal with
  | H : rw_cells _ _ _ _ |- _ => clear H
  | H : ro_cells _ _ _ _ |- _ => clear H
  | H : bytes_at _ _ _ _ |- _ => clear H
  | H : u8arr _ _ _ _ |- _ => clear H
  | H : u32arr _ _ _ _ |- _ => clear H
  | H : u64arr _ _ _ _ |- _ => clear H
  | H : u8ro _ _ _ _ |- _ => clear H
  | H : stk _ _ _ _ |- _ => clear H
  | H : munch _ _ _ |- _ => clear H
  | H : wmono _ _ _ |- _ => clear H
  | H : mem_inv _ _ |- _ => clear H
  end.

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
      unfold zidle in *; transport_after_call bsegs m mm MU WM end end.
Open Scope bv_scope.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= clear_big; lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Module DJ.
  Import Ltac2.
  Ltac2 prune_reld () : unit :=
    let bad := SF2.bad_heads () in
    let gv := SF2.vars_of [] (Control.goal ()) in
    SF2.prune_with (fun ty => if SF2.plain_arith false ty then SF2.clean bad ty else SF2.meets (SF2.vars_of [] ty) gv).
  Ltac2 prune_reld1 () : unit := Control.enter prune_reld.
End DJ.
Local Ltac dj_prune := ltac2:(DJ.prune_reld1 ()).
Ltac hide_disj := repeat match goal with
  | H : (?A \/ ?B) |- _ => change (hide (A \/ B)) in H
  end.

Ltac lia_p := zify_prune_plain; Zify.zify; xlia zchecker.
Ltac disj_one :=
  first [ lia_p
        | unfold hide in *; sf_unhide; dj_prune; Zify.zify; xlia zchecker
        | match goal with H : hide (_ \/ _) |- _ =>
            let H' := fresh "Hd" in pose proof H as H'; unfold hide in H'; decompose [or] H'; lia_p
          end ].
Ltac my_disj := repeat match goal with |- _ /\ _ => split end; try exact I; disj_one.
Local Ltac tslia ::= first [ exact I | clear_big; my_disj ].

Definition sd_A_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (MB MSZ lo : Z) (W : list (Z * Z)) (K : mem -> Prop) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MSsvc (uod_regs ra sp gp tp t0' t1' t2' MB MSZ a2' a3' a4' a5' a6' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F
                (Z_to_bv 64 sec_munmap_ecall) (Z_to_bv 64 215) fc None m' (seg_rom bsegs)
    /\ munch W m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ uod_frame m' sp ra s0 s1 s2 /\ stk bsegs m' lo (bv_unsigned sp - 48) /\ K m'.

Definition sd_mid (sp rac s0c s1c s2c : word) (MB MSZ SZ TCX T lo : Z) (mu mud : word) (m : mem) : Prop :=
  rw_cells bsegs m (bv_unsigned sp - 32) [C8 s2c; C8 s1c; C8 s0c; C8 rac] /\ stk bsegs m lo (bv_unsigned sp - 32)
  /\ rw_cells bsegs m MB [C8 (Z_to_bv 64 MB); C8 (Z_to_bv 64 MSZ); C8 (Z_to_bv 64 SZ)]
  /\ m2s_cells m /\ rel_cells m /\ thread_cells TCX T m /\ rw_cells bsegs m (T + 2888) [C8 mu; C8 mud].

Definition sd_M_regs (sp gp t0 t1 t2 : word) (MB MSZ : Z) (a4 a5 a6 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) : bvmap 5 word :=
  madv_regs (Z_to_bv 64 0x61860) (Z_to_bv 64 (bv_unsigned sp - 32)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 MB) (Z_to_bv 64 MB)
    (pbeg (shad MB)) (pend (shad (MB + MSZ))) a4 a5 a6 (Z_to_bv 64 MSZ) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

Definition sd_M_post (rac sp gp s0c s1c s2c s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (MB MSZ SZ TCX T lo : Z) (mu mud : word) (W : list (Z * Z)) (K : mem -> Prop) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a4' a5' a6' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MSsvc (sd_M_regs sp gp t0' t1' t2' MB MSZ a4' a5' a6' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F
                (Z_to_bv 64 madv_ecall) (Z_to_bv 64 233) fc None m' (seg_rom bsegs)
    /\ munch W m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ sd_mid sp rac s0c s1c s2c MB MSZ SZ TCX T lo mu mud m' /\ K m'.

Lemma sd_hull_facts : forall MB MSZ lo, (MB mod 4096 = 0)%Z -> (MSZ mod 4096 = 0)%Z -> (65536 < MSZ)%Z -> (0 < MB)%Z -> (MB + MSZ <= lo)%Z ->
  (lo <= 2^47)%Z ->
  (shad (MB + MSZ) = shad MB + MSZ / 8 /\ shad MB <= pbeg (shad MB) /\ pbeg (shad MB) < pend (shad (MB + MSZ))
   /\ pend (shad (MB + MSZ)) <= shad MB + MSZ / 8 /\ 0x7fff8000 <= shad MB /\ shad MB + MSZ / 8 <= 0x10007fff8000)%Z.
Proof.
  intros MB MSZ lo H1 H2 H6 H3 H4 H5.
  assert (P8 : (MB = 8 * (512 * (MB / 4096)))%Z) by (pose proof (Z.div_mod MB 4096 ltac:(lia)); lia).
  assert (M8 : (MSZ = 8 * (512 * (MSZ / 4096)))%Z) by (pose proof (Z.div_mod MSZ 4096 ltac:(lia)); lia).
  set (p := (MB / 4096)%Z) in *. set (q := (MSZ / 4096)%Z) in *.
  assert (D1 : (MB / 8 = 512 * p)%Z) by (rewrite P8; replace (8 * (512 * p))%Z with ((512 * p) * 8)%Z by lia; apply Z.div_mul; lia).
  assert (D2 : (MSZ / 8 = 512 * q)%Z) by (rewrite M8; replace (8 * (512 * q))%Z with ((512 * q) * 8)%Z by lia; apply Z.div_mul; lia).
  assert (D3 : ((MB + MSZ) / 8 = 512 * p + 512 * q)%Z)
    by (rewrite P8, M8; replace (8 * (512 * p) + 8 * (512 * q))%Z with ((512 * p + 512 * q) * 8)%Z by lia; apply Z.div_mul; lia).
  assert (E : (shad (MB + MSZ) = shad MB + MSZ / 8)%Z) by (unfold shad; rewrite D1, D2, D3; lia).
  pose proof (pbeg_facts (shad MB) ltac:(unfold shad, SHB; rewrite D1; lia)) as (B1 & B2).
  pose proof (pend_facts (shad (MB + MSZ)) ltac:(unfold shad, SHB; rewrite D3; lia)) as (E1 & E2).
  rewrite E in *. unfold shad, SHB in *. rewrite D1, D2 in *. clear D1 D2 D3. clearbody p q.
  repeat split; lia.
Qed.

Definition sd_W3a (sp : Z) : list (Z * Z) := [(sp - 64, sp - 32)]%Z.

Lemma sd_p3a : forall (rac s0c s1c s2c t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 sp gp : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (MB MSZ SZ TCX T lo : Z) (mu mud : word),
  (MB mod 4096 = 0 /\ 65536 < MSZ /\ MSZ mod 4096 = 0)%Z ->
  gobj MB MSZ lo -> gobj T 4096 lo -> gobj TCX 0xa0 lo ->
  sd_mid sp rac s0c s1c s2c MB MSZ SZ TCX T lo mu mud m ->
  (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 64)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  mem_inv bsegs m ->
  evt bsegs (sd_M_post rac sp gp s0c s1c s2c s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc MB MSZ SZ TCX T lo mu mud (sd_W3a (bv_unsigned sp))
               (fun _ => True) m)
    (MS (mkR (Z_to_bv 64 0x61854) (Z_to_bv 64 (bv_unsigned sp - 32)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 MB) (Z_to_bv 64 MB)
             a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 MSZ) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x61854) fc None m (seg_rom bsegs)).
Proof.
  intros until mud. intros HMB GM GT GX (FR & ST & HD & M2S & REL & TH & TS) HLOH HLO HSP MI.
  destruct HMB as (HMB1 & HMB2 & HMB3).
  pose proof GM as (GM1 & GM2 & GM3 & GM4). pose proof GT as (GT1 & GT2 & GT3 & GT4). pose proof GX as (GX1 & GX2 & GX3 & GX4).
  pose proof (sd_hull_facts MB MSZ lo HMB1 HMB3 HMB2 GM1 GM2 ltac:(unfold kHighShadowEnd in *; lia)) as (HF1 & HF2 & HF3 & HF4 & HF5 & HF6).
  unfold img_hull_lo, img_hull_hi, kHighShadowEnd in *.
  assert (GM4' : (7208960 <= MB)%Z) by (destruct GM4; lia). clear GM4 GM GT GX.
  pose proof M2S as (M1 & M2 & M3). pose proof REL as (R1 & R2 & R3).
  unfold g_got_pagesize_cached, g_got_sealed, g_PageSizeCached in R1, R2, R3.
  destruct TH as ((KI & KK & TSD & T0) & TT).
  unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main, tpA in KI, KK, TSD, T0.
  pose proof M2S as M2S0. pose proof REL as REL0. clear M2S REL.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 32)) = (bv_unsigned sp - 32)%Z) by (apply unsigned_lit; lia).
  pose proof (munch_refl (sd_W3a (bv_unsigned sp)) m) as MU. unfold sd_W3a in MU.
  pose proof (wmono_refl bsegs m) as WM.
  apply box in HMB1, HMB3.
  hide_disj.
  zhide.
  do 3 zstep.
  call (flush_A_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ MB MSZ lo).
  all: rewrite ?ESP.
  1:{ split; [exact M1| split; [exact M2| exact M3]]. }
  1:{ unfold rel_cells, g_got_pagesize_cached, g_got_sealed, g_PageSizeCached. split; [exact R1| split; [exact R2| exact R3]]. }
  1:{ unfold addr_in_mem, kLowMemEnd, kHighMemEnd, kHighShadowEnd. unfold hide in GM3. lia. }
  1:{ unfold addr_in_mem, kLowMemEnd, kHighMemEnd, kHighShadowEnd. unfold hide in GM3. lia. }
  1:{ lia. }
  1:{ exact HF3. }
  1:{ exact ST. }
  1:{ lia. }
  1:{ unfold kHighShadowEnd. lia. }
  1:{ exact MI. }
  apply evt_done. unfold sd_M_post, sd_M_regs. do 11 eexists.
  split; [reflexivity|].
  split; [exact MU|]. split; [assumption|]. split; [assumption|].
  split; [|exact I].
  unfold sd_mid. rewrite ?ESP in *.
  split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [split; [exact M1| split; [exact M2| exact M3]]|].
  split; [unfold rel_cells, g_got_pagesize_cached, g_got_sealed, g_PageSizeCached; split; [exact R1| split; [exact R2| exact R3]]|].
  split; [|assumption].
  unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main.
  split; [split; [exact KI|split; [exact KK|split; [exact TSD|exact T0]]]|exact TT].
Qed.

Definition sd_W3 (sp MB MSZ T : Z) : list (Z * Z) := [(pbeg (shad MB), pend (shad (MB + MSZ))); (sp - 64, sp); (T + 2888, T + 2904)]%Z.

Lemma sd_p3b : forall (rac s0c s1c s2c t0 t1 t2 a4 a5 a6 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 sp gp : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (MB MSZ SZ TCX T lo : Z) (mu mud : word),
  (MB mod 4096 = 0 /\ 65536 < MSZ /\ MSZ mod 4096 = 0)%Z ->
  gobj MB MSZ lo -> gobj T 4096 lo -> gobj TCX 0xa0 lo -> sapart T 4096 TCX 0xa0 -> sapart MB MSZ T 4096 ->
  sd_mid sp rac s0c s1c s2c MB MSZ SZ TCX T lo mu mud m ->
  (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 64)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  mem_inv bsegs m ->
  evt bsegs (sd_A_post rac sp gp (Z_to_bv 64 tpA) s0c s1c s2c s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc MB MSZ lo (sd_W3 (bv_unsigned sp) MB MSZ T)
               (fun m' => rw_cells bsegs m' (T + 2888) [C8 (Z_to_bv 64 (bv_unsigned mu + 1)); C8 (Z_to_bv 64 (bv_unsigned mud + MSZ))]) m)
    (nret (MSsvc (sd_M_regs sp gp t0 t1 t2 MB MSZ a4 a5 a6 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
                 (Z_to_bv 64 madv_ecall) (Z_to_bv 64 233) fc None m (seg_rom bsegs))
          (mkEffect (Z_to_bv 64 0) [] [(Z_to_bv 64 (pbeg (shad MB)), Z_to_bv 64 (pend (shad (MB + MSZ)) - pbeg (shad MB)))])).
Proof.
  intros until mud. intros HMB GM GT GX ATX AMT (FR & ST & HD & M2S & REL & TH & TS) HLOH HLO HSP MI.
  destruct HMB as (HMB1 & HMB2 & HMB3).
  pose proof GM as (GM1 & GM2 & GM3 & GM4). pose proof GT as (GT1 & GT2 & GT3 & GT4). pose proof GX as (GX1 & GX2 & GX3 & GX4).
  pose proof (sd_hull_facts MB MSZ lo HMB1 HMB3 HMB2 GM1 GM2 ltac:(unfold kHighShadowEnd in *; lia)) as (HF1 & HF2 & HF3 & HF4 & HF5 & HF6).
  unfold sapart, img_hull_lo, img_hull_hi, kHighShadowEnd in *.
  assert (GM4' : (7208960 <= MB)%Z) by (destruct GM4; lia). clear GM4 GM GT GX.
  pose proof M2S as (M1 & M2 & M3). pose proof REL as (R1 & R2 & R3).
  unfold g_got_pagesize_cached, g_got_sealed, g_PageSizeCached in R1, R2, R3.
  destruct TH as ((KI & KK & TSD & T0) & TT).
  unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main, tpA in KI, KK, TSD, T0.
  clear M2S REL.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 32)) = (bv_unsigned sp - 32)%Z) by (apply unsigned_lit; lia).
  pose proof (munch_refl (sd_W3 (bv_unsigned sp) MB MSZ T) m) as MU. unfold sd_W3 in MU.
  pose proof (wmono_refl bsegs m) as WM.
  set (PB := pbeg (shad MB)) in *. set (PE := pend (shad (MB + MSZ))) in *.
  rewrite nret_MSsvc. unfold sd_M_regs, madv_regs. rewrite mkR_set_a0, apply_mem_zeros.
  fold PB PE.
  assert (RO : forall x : word, (PB <= bv_unsigned x < PB + (PE - PB))%Z -> ro_addr bsegs x = false).
  { intros x Hx. apply ro_free_range. unfold img_hull_hi. lia. }

  sys_mem_zeros.
  hide_disj.
  unfold madv_ecall in *.
  replace (Z_to_bv 64 0x98758 + Z_to_bv 64 4 : word) with (Z_to_bv 64 0x9875c : word) by (rewrite lit_add_lit; reflexivity).
  apply box in HMB1, HMB3.
  zhide.

  do 2 zstep.
  zstep.
  call (gcts_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ TCX T lo).
  all: rewrite ?ESP.
  1:{ unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main.
      split; [split; [exact KI|split; [exact KK|split; [exact TSD|exact T0]]]|exact TT]. }
  all: try (unfold hide in *; unfold kHighShadowEnd in *; lia).
  all: try assumption.
  all: try (rewrite ?ESP in *; assumption).
  do 6 zstep.
  zstep. zstep.
  do 7 zstep.
  lazymatch goal with H : stk bsegs _ lo _ |- _ => rename H into STx end.
  rewrite ?ESP in STx.
  release_frame FR STx (bv_unsigned sp).
  try (replace (bv_unsigned sp - 32 + 32)%Z with (bv_unsigned sp) by lia; rewrite Z_to_bv_bv_unsigned).
  zstep.
  call (uod_A_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ MB MSZ lo).
  1-2: lia.
  1-2: reflexivity.
  1:{ assumption. }
  1:{ lia. }
  1:{ lia. }
  1:{ assumption. }
  apply evt_done. unfold sd_A_post. do 13 eexists.
  split; [reflexivity|].
  split; [exact MU|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.
