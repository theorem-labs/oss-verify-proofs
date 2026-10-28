(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac ImageA Arr Walk StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout R_small R_m2s R_thread. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs R_prim_defs R_glue_defs R_sec_defs F_memset R_setshadow R_poison R_secalloc_ps0 R_mmapordie R_secalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

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
Local Ltac zidle_end m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call_fast asegs m mm MU WM end end.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Module DJ.
  Import Ltac2.
  Ltac2 prune_reld () : unit :=
    let bad := SF2.bad_heads () in
    let gv := SF2.vars_of [] (Control.goal ()) in
    SF2.prune_with (fun ty => if SF2.plain_arith false ty then SF2.clean bad ty else SF2.meets (SF2.vars_of [] ty) gv).
  Ltac2 prune_reld1 () : unit := Control.enter prune_reld.
End DJ.
Local Ltac dj_prune := ltac2:(DJ.prune_reld1 ()).
Local Ltac dj_one := first [ Zify.zify; xlia zchecker | sf_unhide; dj_prune; Zify.zify; xlia zchecker | tlia ].
Local Ltac tslia ::= first [ exact I | repeat lazymatch goal with |- _ /\ _ => split end; first [ exact I | dj_one ] ].
Local Ltac lia ::= lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition sa_W2 (sp P SZ T : Z) : list (Z * Z) :=
  [(shad P, shad P + 512); (shad (P + 4096 + SZ), shad (P + sa_msz SZ)); (T + 2872, T + 2888); (P, P + 24);
   (i_sec_mutex, i_sec_mutex + 4); (sp - 64, sp)]%Z.

Lemma land4095_al : forall x, (0 <= x)%Z -> (x mod 4096 = 0)%Z -> Z.land 4095 x = 0%Z.
Proof.
  intros x Hx Hm. rewrite Z.land_comm. change 4095%Z with (Z.ones 12). rewrite Z.land_ones by lia.
  change (2 ^ 12)%Z with 4096%Z. exact Hm.
Qed.

Lemma land_ones64 : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551615 = x.
Proof. intros x Hx. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma land_m8 : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551608 = (x / 8 * 8)%Z.
Proof.
  intros x Hx. change 18446744073709551608%Z with (Z.land (Z.ones 64) (Z.lnot (Z.ones 3))).
  rewrite Z.land_assoc, (Z.land_ones x 64) by lia. rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma sa_shad_facts : forall P SZ lo, (P mod 4096 = 0)%Z -> (0 < SZ /\ SZ mod 8 = 0)%Z -> (SZ + 16384 <= 2^47)%Z ->
  gobj P (sa_msz SZ) lo -> (lo <= 2^47)%Z ->
  (0x7fff8000 <= shad P /\ shad (P + 4096) = shad P + 512 /\ shad (P + 4096 + SZ) = shad P + 512 + SZ / 8
   /\ shad (P + sa_msz SZ) = shad P + sa_msz SZ / 8 /\ 8 * (SZ / 8) = SZ /\ 8 * (sa_msz SZ / 8) = sa_msz SZ
   /\ (sa_msz SZ - 4096 - SZ) / 8 = sa_msz SZ / 8 - 512 - SZ / 8
   /\ shad P + sa_msz SZ / 8 <= 0x10007fff8000
   /\ (P + sa_msz SZ <= 0x7fff7000 \/ 0x10007fff8000 <= P))%Z.
Proof.
  intros P SZ lo HP HSZ HSZ2 GP HLO.
  pose proof (sa_msz_facts SZ ltac:(lia)) as [MS1 MS2].
  destruct GP as (GP1 & GP2 & GP3 & GP4).
  assert (P8 : (P = 8 * (512 * (P / 4096)))%Z) by (pose proof (Z.div_mod P 4096 ltac:(lia)); lia).
  assert (S8 : (SZ = 8 * (SZ / 8))%Z) by (pose proof (Z.div_mod SZ 8 ltac:(lia)); lia).
  assert (M8 : (sa_msz SZ = 8 * (512 * (sa_msz SZ / 4096)))%Z) by (pose proof (Z.div_mod (sa_msz SZ) 4096 ltac:(lia)); lia).
  set (p := (P / 4096)%Z) in *. set (z := (SZ / 8)%Z) in *. set (ms := (sa_msz SZ / 4096)%Z) in *.
  assert (D1 : (P / 8 = 512 * p)%Z) by (rewrite P8; replace (8 * (512 * p))%Z with ((512 * p) * 8)%Z by lia; apply Z.div_mul; lia).
  assert (D2 : ((P + 4096) / 8 = 512 * p + 512)%Z)
    by (rewrite P8; replace (8 * (512 * p) + 4096)%Z with ((512 * p + 512) * 8)%Z by lia; apply Z.div_mul; lia).
  assert (D3 : ((P + 4096 + SZ) / 8 = 512 * p + 512 + z)%Z)
    by (rewrite P8, S8; replace (8 * (512 * p) + 4096 + 8 * z)%Z with ((512 * p + 512 + z) * 8)%Z by lia; apply Z.div_mul; lia).
  assert (D4 : ((P + sa_msz SZ) / 8 = 512 * p + 512 * ms)%Z)
    by (rewrite P8, M8; replace (8 * (512 * p) + 8 * (512 * ms))%Z with ((512 * p + 512 * ms) * 8)%Z by lia; apply Z.div_mul; lia).
  assert (D5 : (sa_msz SZ / 8 = 512 * ms)%Z)
    by (rewrite M8; replace (8 * (512 * ms))%Z with ((512 * ms) * 8)%Z by lia; apply Z.div_mul; lia).
  assert (D6 : ((sa_msz SZ - 4096 - SZ) / 8 = 512 * ms - 512 - z)%Z)
    by (rewrite M8, S8; replace (8 * (512 * ms) - 4096 - 8 * z)%Z with ((512 * ms - 512 - z) * 8)%Z by lia; apply Z.div_mul; lia).
  unfold shad, SHB. rewrite D1, D2, D3, D4, D5, D6. unfold kHighShadowEnd, img_hull_lo, img_hull_hi in *.
  clear D1 D2 D3 D4 D5 D6. clearbody p z ms. Lia.lia.
Qed.

Ltac hide_disj := repeat match goal with
  | H : (?A \/ ?B) |- _ => change (hide (A \/ B)) in H
  end.
Ltac unhide := unfold hide in *.

Section P2.
Variables (sp gp s4 s6 s7 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (P SZ TCX T nres n lo : Z) (mm md : word) (shj1 shj2 : list byte) (Q : machine_state -> Prop).
Hypothesis HSZ : (0 < SZ /\ SZ mod 8 = 0 /\ SZ + 16384 <= 2^47)%Z.
Hypothesis HP : (P mod 4096 = 0)%Z.
Hypothesis GP : gobj P (sa_msz SZ) lo.
Hypothesis GT : gobj T 4096 lo.
Hypothesis GX : gobj TCX 0xa0 lo.
Hypothesis APT : sapart P (sa_msz SZ) T 4096.
Hypothesis APX : sapart P (sa_msz SZ) TCX 0xa0.
Hypothesis ATX : sapart T 4096 TCX 0xa0.
Hypothesis Hn : (0 <= n < 2^20)%Z.
Hypothesis PG : sec_page m.
Hypothesis PS : ps_cells m.
Hypothesis TH : thread_cells TCX T m.
Hypothesis TS : rw_cells asegs m (T + 2872) [C8 mm; C8 md].
Hypothesis HD : rw_cells asegs m P [CB 32 (repeat (Z_to_bv 8 0) 32)].
Hypothesis SH1 : rw_cells asegs m (shad P) [CB 512 shj1].
Hypothesis SH2 : rw_cells asegs m (shad (P + 4096 + SZ)) [CB (Z.to_nat ((sa_msz SZ - 4096 - SZ) / 8)) shj2].
Hypothesis MX : rw_cells asegs m i_sec_mutex [C1 (Z_to_bv 8 0)].
Hypothesis PAD : sec_pad m.
Hypothesis NR : rw_cells asegs m i_sec_nres [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 n)].
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis HLOH : (kHighShadowEnd + 8 <= lo)%Z.
Hypothesis HLO : (lo <= bv_unsigned sp - 64)%Z.
Hypothesis HSP : (bv_unsigned sp <= 2^47)%Z.
Hypothesis MI : mem_inv asegs m.
Hypothesis K : forall (m' : mem) (ra t0 t1 t2 a1 a2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  munch (sa_W2 (bv_unsigned sp) P SZ T) m m' -> wmono asegs m m' -> mem_inv asegs m' ->
  rw_cells asegs m' P [C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 (sa_msz SZ)); C8 (Z_to_bv 64 SZ); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m' (shad P) [CB 512 (repeat (Z_to_bv 8 250) 512)] ->
  rw_cells asegs m' (shad (P + 4096 + SZ))
    [CB (Z.to_nat ((sa_msz SZ - 4096 - SZ) / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat ((sa_msz SZ - 4096 - SZ) / 8)))] ->
  rw_cells asegs m' (T + 2872) [C8 (Z_to_bv 64 (bv_unsigned mm + 1)); C8 (Z_to_bv 64 (bv_unsigned md + sa_msz SZ))] ->
  rw_cells asegs m' i_sec_mutex [C4 (Z_to_bv 64 1)] ->
  stk asegs m' lo (bv_unsigned sp) ->
  evt asegs Q
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 GSTAT) (Z_to_bv 64 SEC) (Z_to_bv 64 (P + 4096)) a1 a2 (Z_to_bv 64 n)
             a4 a5 a6 a7
             (Z_to_bv 64 (sa_msz SZ)) (Z_to_bv 64 SZ) (Z_to_bv 64 P) (Z_to_bv 64 P) (Z_to_bv 64 (P + sa_msz SZ))
             (Z_to_bv 64 (P + 4096 + SZ)) (Z_to_bv 64 7) (Z_to_bv 64 (P + 4096)) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x60250) fc None m' (seg_rom asegs)).

Lemma sa_p2 : forall (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  evt asegs Q
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 GSTAT) (Z_to_bv 64 SEC) (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (sa_msz SZ)) (Z_to_bv 64 SZ) s4 (Z_to_bv 64 8) s6 s7 (Z_to_bv 64 7) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x60154) fc None m (seg_rom asegs)).
Proof using HSZ HP GP GT GX APT APX ATX Hn PG PS TH TS HD SH1 SH2 MX PAD NR ST HLOH HLO HSP MI K.
  intros.
  pose proof (sa_msz_facts SZ ltac:(lia)) as [MS1 MS2].
  pose proof (sa_shad_facts P SZ lo HP ltac:(lia) ltac:(lia) GP ltac:(lia)) as (SR1 & SR2 & SR3 & SR4 & SR5 & SR6 & SR7 & SR8 & SRc).
  rewrite SR7 in SH2. apply (box ((sa_msz SZ - 4096 - SZ) / 8 = sa_msz SZ / 8 - 512 - SZ / 8)%Z) in SR7.
  set (z8 := (SZ / 8)%Z) in *. set (ms8 := (sa_msz SZ / 8)%Z) in *. clearbody z8 ms8.
  pose proof GP as (GP1 & GP2 & GP3 & GP4). pose proof GT as (GT1 & GT2 & GT3 & GT4). pose proof GX as (GX1 & GX2 & GX3 & GX4).
  pose proof APT as APT'. pose proof APX as APX'. pose proof ATX as ATX'.
  clear GP GT GX APT APX ATX.
  unfold sapart, img_hull_lo, img_hull_hi in *.
  unfold sec_page, i_sec_page in PG. change (INST + 0x40)%Z with 1508888%Z in PG.
  change i_sec_mutex with 1509504%Z in *. change i_sec_nres with 1508936%Z in NR.
  change SEC with 1508888%Z. change GSTAT with 1509512%Z.
  unfold kHighShadowEnd in *.
  ps_cells_destr PS.
  destruct TH as ((KI & KK & TSD & T0) & TT).
  unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main, tpA in KI, KK, TSD, T0.
  unfold sec_pad in PAD. change (i_sec_mutex + 1)%Z with 1509505%Z in PAD.
  pose proof (munch_refl (sa_W2 (bv_unsigned sp) P SZ T) m) as MU. unfold sa_W2 in MU. change i_sec_mutex with 1509504%Z in MU.
  pose proof (wmono_refl asegs m) as WM.
  hide_disj.
  zhide.
  zstep. ifF.
  do 4 zstep.
  rewrite land4095_al by lia.
  zstep. ifF.
  do 3 zstep.
  replace (Z.land (4096 + P) 7) with 0%Z by (rewrite land7_ps by lia; lia).
  do 12 zstep.
  change (Z.land (Z.land (Z.b2z (0 <? 1) + -1) 18446744073709551615) (8 + - 0)) with 0%Z.
  rewrite !(land_ones64 (0 + (4096 + P) + 7)) by lia. rewrite !(land_ones64 (0 + (4096 + P) + SZ)) by lia.
  rewrite !land_m8 by lia.
  replace ((0 + (4096 + P) + 7) / 8 * 8)%Z with (P + 4096)%Z by (Z.div_mod_to_equations; lia).
  replace ((0 + (4096 + P) + SZ) / 8 * 8)%Z with (P + 4096 + SZ)%Z by (Z.div_mod_to_equations; lia).
  replace (0 + (4096 + P) + SZ)%Z with (P + 4096 + SZ)%Z by lia.
  replace (0 + (4096 + P))%Z with (P + 4096)%Z by lia.
  replace (sa_msz SZ + P)%Z with (P + sa_msz SZ)%Z by lia.
  replace (P + 4096 + - P)%Z with 4096%Z by lia.
  zstep.
  unfold hide in GP3, GT3, GX3, SRc.
  apply box in SH1.
  call (poison_small_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ P 4096 250 lo shj1).
  1:{ unfold ps_args_ok, kLowMemEnd, kHighMemEnd, kHighShadowEnd. lia. }
  1:{ lia. }
  1:{ left. lia. }
  1:{ exact (unbox _ SH1). }
  1:{ unfold ps_cells, m2s_cells, setshadow_cells, g_got_common_flags, g_can_poison, g_cf_clear_shadow_mmap_threshold,
        g_got_real_memset, g_real_memset, musl_memset_entry, SHB, kHighMemEnd.
      refine (conj _ (conj (conj _ (conj _ _)) (conj (conj _ _) (conj _ _)))); assumption. }
  1:{ exact ST. }
  1:{ lia. }
  1:{ unfold kHighShadowEnd. lia. }
  1:{ exact MI. }
  hide_disj.
  do 3 zstep.
  replace (P + sa_msz SZ + - (P + 4096 + SZ))%Z with (sa_msz SZ - 4096 - SZ)%Z by lia.
  zstep.
  apply unbox in SR7.
  unfold hide in GP3, GT3, GX3, SRc.
  apply box in SH2.
  call (poison_fa_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (P + 4096 + SZ) (sa_msz SZ - 4096 - SZ) lo shj2).
  1:{ destruct (Z.eq_dec (sa_msz SZ - 4096 - SZ) 0) as [E0|E0].
      - left. split; [exact E0|].
        assert (EZ : (SZ mod 4096 = 0)%Z).
        { pose proof (roundup4k_facts SZ ltac:(lia)) as [R1 R2]. unfold sa_msz in E0. replace SZ with (roundup4k SZ) by lia. exact R2. }
        unfold ps0_ok, kLowMemEnd, kHighMemEnd, kHighShadowEnd. split; [Z.div_mod_to_equations; lia|].
        assert (HME : ((P + sa_msz SZ) mod 4096 = 0)%Z) by (Z.div_mod_to_equations; lia).
        destruct GP3 as [L|H]; [left; Z.div_mod_to_equations; lia| right; lia].
      - right. unfold ps_args_ok, kLowMemEnd, kHighMemEnd, kHighShadowEnd. split; [Z.div_mod_to_equations; lia| lia]. }
  1:{ rewrite SR7. exact (unbox _ SH2). }
  1:{ unfold ps_cells, m2s_cells, setshadow_cells, g_got_common_flags, g_can_poison, g_cf_clear_shadow_mmap_threshold,
        g_got_real_memset, g_real_memset, musl_memset_entry, SHB, kHighMemEnd.
      refine (conj _ (conj (conj _ (conj _ _)) (conj (conj _ _) (conj _ _)))); assumption. }
  1:{ assumption. }
  1:{ lia. }
  1:{ unfold kHighShadowEnd. lia. }
  1:{ assumption. }
  hide_disj.
  zstep.
  call (gcts_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ TCX T lo).
  1:{ unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main.
      split; [split; [exact KI|split; [exact KK|split; [exact TSD|exact T0]]]|exact TT]. }
  all: try (unfold kHighShadowEnd in *; lia).
  all: try assumption.
  do 3 zstep.
  replace (Z.land (P + 4096) 7) with 0%Z by (rewrite land7_ps by lia; lia).
  do 2 zstep.
  unfold hide in APT', GT3, GT4, ATX'.
  zstep. zstep.
  hide_disj.
  zstep. ifF.
  do 4 zstep.
  rewrite (land4095_al (P + 4096)) by lia.
  zstep. ifF.
  zstep. ifF.
  zstep. ifF.
  zstep.
  replace (P + 4096 + - 4096)%Z with P by lia.
  unfold hide in APT', GP3, GP4, APX'.
  do 3 zstep.
  hide_disj.
  zstep. ifF.
  do 4 zstep.
  pose proof (lockw_of _ MX PAD) as LW. clear MX PAD. change i_sec_mutex with 1509504%Z in LW.
  assert (AMO : amo_aligned AW (Z_to_bv 64 1509504) = true) by (vm_compute; reflexivity).
  unfold hide in GP4, GT4, GX4.
  amo_step AMO.
  replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by (vm_compute; reflexivity).
  do 4 zstep.
  amo_step AMO; try fix_lit_store.
  hide_disj.
  zstep. ifF.
  zstep. zstep. ifF.
  do 2 zstep.
  replace (n ≫ 20)%Z with 0%Z by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
  zstep. ifF.
  apply (sec_rw_app2 _ P [C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 (sa_msz SZ)); C8 (Z_to_bv 64 SZ)] [CB 8 _]) in HD.
  destruct HD as [HD1 HD2].
  apply (sec_relistZ _ _ _ [C8 (Z_to_bv 64 0)]) in HD2; [| vm_compute; repeat split; reflexivity | vm_compute; reflexivity].
  assert (HDF : rw_cells asegs m1 P [C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 (sa_msz SZ)); C8 (Z_to_bv 64 SZ); C8 (Z_to_bv 64 0)]).
  { apply (sec_rw_app2 _ P [C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 (sa_msz SZ)); C8 (Z_to_bv 64 SZ)] [C8 (Z_to_bv 64 0)]).
    split; [exact HD1| exact HD2]. }
  clear HD1 HD2.
  unfold hide in *.
  apply (K m1); [exact MU| exact WM| exact MI0| exact HDF| exact PC| exact PC0| exact TS| exact LW| exact POST].
Qed.
End P2.
