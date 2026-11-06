(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/RepReallocBcf.v (commit 3cae605a900a, blob b4f8ae8fe1bf) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from cgif_file_fuzzer asan-ubsan ce511d541cda (pin 1c29845fe605), the cf layer at part 3c; module paths changed; 15 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AE3d AFeq AB13.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YE08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB15 AFff.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0v YK13 YK02 YG0b YFfn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.Z Require Import Placement.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import RepReallocD.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require RepMmapcf RepUnmapcf RepMemKcf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Definition tbl_rt_build : ctable := build_table tfibsegs 0x597a0 16%nat TEmpty.
Definition tbl_rt : ctable := Eval vm_compute in tbl_rt_build.
Lemma tbl_rt_eq : tbl_rt = tbl_rt_build.
Proof. vm_cast_no_check (@eq_refl ctable tbl_rt). Qed.
Lemma tbl_rt_ok : table_ok tfibsegs tbl_rt.
Proof. rewrite tbl_rt_eq. unfold tbl_rt_build. apply build_table_ok0. cbv. discriminate. Qed.

Definition rFRt : YP09.region := YP09.mkRegion (Some 2%nat) 0 32 0 0
  [YP09.mkChunk 0 (CVal 8 (SOff 35 0)); YP09.mkChunk 8 (CVal 8 (SOff 36 0)); YP09.mkChunk 16 (CVal 8 (SOff 37 0));
   YP09.mkChunk 24 (CVal 8 (SOff 38 0))].

Definition rVt : YP09.region := YP09.mkRegion (Some 8%nat) 0 24 0 0
  [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0)); YP09.mkChunk 16 (CVal 8 (SOff 34 0))].

Definition rVw : YP09.region := YP09.mkRegion (Some 8%nat) 0 24 0 16 [YP09.mkChunk 16 (CVal 8 (SOff 34 0))].

Definition SS_T : sstate := mkSS 0x597a0 sr_atoms [rFRt; rVt] None (mkFacts [] [] []).
Definition SS_P : sstate := mkSS 0x597c0 sr_atoms [rFRt; rVw] None (mkFacts [] [] []).

Definition mdU_of (md : Model) (a ncap d cap : Z) (mat : list word) : Model :=
let md1 := with_mmap_backing (w64 34) (w64 a) (w64 ncap) (mmap_model (w64 a) (w64 ncap) (with_vm_backing (m_vm_lazy md) mat md)) in
if cap =? 0 then md1 else munmap_model (w64 d) (w64 cap) md1.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Local Ltac num := unfold REALLOC_STK, REALLOC_FRAME, RepMmapcf.MOD_STK, RepUnmapcf.UOD_STK, TFIB_IMG_END, TFIB_IMG_LO,
  TASK_SIZE in *.
Local Ltac regv HS r :=
  lazymatch type of HS with st_ok _ ?E ?ss (restrict ?H ?ms) =>
  rewrite (st_ok_reg_denot H E ss ms r HS);
  let t := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with t end.

Lemma frame_none : forall E rs (m m' : word -> option byte) (x : word),
frame_of E rs m m' -> forallb (fun t => snd t <=? snd (fst t)) (windows rs) = true -> m' x = m x.
Proof.
intros E rs m m' x HF Hb. apply HF. intros Hin. destruct (in_wrange_windows E rs _ Hin) as (b & lo & hi & Ht & Hr).
rewrite forallb_forall in Hb. specialize (Hb _ Ht). cbn [fst snd] in Hb. apply Z.leb_le in Hb. lia.
Qed.
Lemma frame_v : forall E rs (m m' : word -> option byte) v (x : word),
frame_of E rs m m' ->
forallb (fun t => win_eqb t (Some 8%nat, 0, 16) || (snd t <=? snd (fst t))) (windows rs) = true ->
bv_unsigned (ew E 8) = v -> ~ (v <= bv_unsigned x < v + 16) -> m' x = m x.
Proof.
intros E rs m m' v x HF Hb Hv Hx. apply HF. intros Hin. apply Hx.
assert (X : v + 0 <= bv_unsigned x < v + 16) by (eapply in_wrange_single_b; eassumption). lia.
Qed.
Lemma val_mem_tr : forall (H H' : word -> bool) (mem mem' : word -> option byte) c (n : nat) val,
(forall k, (k < n)%nat -> H' (Z_to_bv 64 (c + Z.of_nat k)) = H (Z_to_bv 64 (c + Z.of_nat k)) /\
  mem' (Z_to_bv 64 (c + Z.of_nat k)) = mem (Z_to_bv 64 (c + Z.of_nat k))) ->
val_mem tfibsegs (mrestrict H mem) c n val -> val_mem tfibsegs (mrestrict H' mem') c n val.
Proof.
intros H H' mem mem' c n val HK Hv. apply (val_mem_ext (mrestrict H mem) (mrestrict H' mem') c n val); [|exact Hv].
intros k Hk. destruct (HK k Hk) as [E1 E2]. unfold mbyte. rewrite (mrestrict_same_at H H' mem mem' _ E1 E2). reflexivity.
Qed.
Lemma apresent_eq : forall (H : word -> bool) (m m' : word -> option byte) b,
m' (Z_to_bv 64 b) = m (Z_to_bv 64 b) -> apresent H m b -> apresent H m' b.
Proof. intros H m m' b E [Hh [x Hx]]. split; [exact Hh|]. exists x. rewrite E. exact Hx. Qed.
Lemma writable_tr : forall (m m' : word -> option byte) x,
m' (Z_to_bv 64 x) = m (Z_to_bv 64 x) -> writable_at tfibsegs m x -> writable_at tfibsegs m' x.
Proof. intros m m' x E Hw. unfold writable_at, wview in *. rewrite E. exact Hw. Qed.

Definition msame (m m' : Model) : Prop :=
m_fd m = m_fd m' /\ m_vmmaps m = m_vmmaps m' /\ m_vm_lazy m = m_vm_lazy m' /\ m_io m = m_io m' /\
m_fsys m = m_fsys m' /\ m_proc m = m_proc m' /\ m_lim m = m_lim m' /\ m_time m = m_time m'.
Lemma msame_refl : forall m, msame m m.
Proof. intros m. repeat split; reflexivity. Qed.
Lemma msame_wvb_l : forall m m' X, msame m m' -> msame (with_vm_backing (m_vm_lazy m) X m) m'.
Proof. intros [fd [maps lazy mat] io fs proc lim tm] m' X H. exact H. Qed.
Lemma wvb_msame : forall m m' X, msame m m' -> with_vm_backing (m_vm_lazy m) X m = with_vm_backing (m_vm_lazy m') X m'.
Proof.
intros [fd [maps lazy mat] io fs proc lim tm] [fd' [maps' lazy' mat'] io' fs' proc' lim' tm'] X
  (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
unfold m_vmmaps, m_vm_lazy in E2, E3. cbn in *. subst. reflexivity.
Qed.
Lemma sio_msame : forall m m', msame m m' -> YG0d.same_io m' m.
Proof. intros m m' (E1 & _ & _ & E4 & E5 & E6 & _). unfold YG0d.same_io. repeat split; assumption. Qed.
Lemma amwf_msame : forall m m', msame m m' -> amwf m' -> amwf m.
Proof. intros m m' (_ & E2 & E3 & _) H. exact (amwf_same m' m E2 E3 H). Qed.
Lemma md1_any : forall (md : Model) (mat1 X : list word) (a n : word) (m : Model),
msame m (with_mmap_backing (w64 34) a n (mmap_model a n (with_vm_backing (m_vm_lazy md) mat1 md))) ->
with_vm_backing (m_vm_lazy m) X m = with_mmap_backing (w64 34) a n (mmap_model a n (with_vm_backing (m_vm_lazy md) X md)).
Proof. intros md mat1 X a n m Hs. rewrite (wvb_msame _ _ X Hs). apply md1_collapse. Qed.
Lemma maps_md1 : forall (md : Model) (mat1 : list word) (a n : word) q,
In q (vm_maps (m_vmmaps md)) ->
In q (vm_maps (m_vmmaps (with_mmap_backing (w64 34) a n (mmap_model a n (with_vm_backing (m_vm_lazy md) mat1 md))))).
Proof. intros md mat1 a n q H. rewrite wmb34. right. exact H. Qed.

Lemma tail_fin : forall (W : world tfibsegs) (regsP regsE : bvmap 5 word) (memP : word -> option byte) (mdY : Model)
  (spr v a ncap sz : Z),
let m := mrestrict (w_H W) memP in
bv_unsigned (getr regsP 2) = spr -> getr regsP 8 = w64 v -> getr regsP 9 = w64 ncap -> getr regsP 18 = w64 a ->
(forall r, r = 3 \/ r = 4 \/ 19 <= r <= 27 -> getr regsP (Z_to_bv 5 r) = getr regsE (Z_to_bv 5 r)) ->
getr regsE 2 = w64 (spr + 32) -> YK0s.ret_ok (getr regsE 1) ->
val_mem tfibsegs m spr 8 (bv_unsigned (getr regsE 18)) -> val_mem tfibsegs m (spr + 8) 8 (bv_unsigned (getr regsE 9)) ->
val_mem tfibsegs m (spr + 16) 8 (bv_unsigned (getr regsE 8)) -> val_mem tfibsegs m (spr + 24) 8 (bv_unsigned (getr regsE 1)) ->
(forall x, v <= x < v + 16 -> writable_at tfibsegs m x) -> val_mem tfibsegs m (v + 16) 8 sz ->
0 <= spr -> spr + 32 <= 2 ^ 64 -> 0 <= v -> v + 24 <= 2 ^ 64 -> (v + 24 <= spr \/ spr + 32 <= v) ->
0 <= a < 2 ^ 64 -> 0 <= ncap < 2 ^ 64 -> 0 <= sz < 2 ^ 64 ->
SRr tfibsegs W (mkCfg (mkst regsP (Z_to_bv 64 0x597c0) memP (seg_rom tfibsegs)) mdY)
(fun W' c' => W' = W /\ exists (regs' : bvmap 5 word) (mem' : word -> option byte) (mat : list word),
  c' = mkCfg (mkst regs' (getr regsE 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy mdY) mat mdY) /\
  regs_preserved regsE regs' /\
  val_mem tfibsegs (mrestrict (w_H W) mem') v 8 a /\ val_mem tfibsegs (mrestrict (w_H W) mem') (v + 8) 8 ncap /\
  val_mem tfibsegs (mrestrict (w_H W) mem') (v + 16) 8 sz /\
  (forall x : word, ~ (v <= bv_unsigned x < v + 16) -> mem' x = memP x)).
Proof.
intros W regsP regsE memP mdY spr v a ncap sz. cbv zeta.
intros P2 P8 P9 P18 PCS RE2 Hra VF0 VF1 VF2 VF3 WV VSZ Hs0 Hs1 Hv0 Hv1 Hvs Ha Hn Hs.
pose proof Hwx_tfa as Hwx.
set (ex := [Z_to_bv 64 0; Z_to_bv 64 0; w64 sz; getr regsE 18; getr regsE 9; getr regsE 8; getr regsE 1]).
assert (BV2 : bv_unsigned (ew (Ereg regsP ex) 2) = spr) by (rewrite (ew_Ereg_nat regsP ex 2 2%bv eq_refl); exact P2).
assert (E8 : ew (Ereg regsP ex) 8 = w64 v) by (rewrite (ew_Ereg_nat regsP ex 8 8%bv eq_refl); exact P8).
assert (E9 : ew (Ereg regsP ex) 9 = w64 ncap) by (rewrite (ew_Ereg_nat regsP ex 9 9%bv eq_refl); exact P9).
assert (E18 : ew (Ereg regsP ex) 18 = w64 a) by (rewrite (ew_Ereg_nat regsP ex 18 18%bv eq_refl); exact P18).
set (E := Ereg regsP ex) in *.
assert (BV8 : bv_unsigned (ew E 8) = v) by (rewrite E8; unfold w64; apply unsigned_lit_small; lia).
assert (E34 : ew E 34 = w64 sz) by reflexivity.
assert (E35 : ew E 35 = getr regsE 18) by reflexivity.
assert (E36 : ew E 36 = getr regsE 9) by reflexivity.
assert (E37 : ew E 37 = getr regsE 8) by reflexivity.
assert (E38 : ew E 38 = getr regsE 1) by reflexivity.
assert (CS : forall z, (z = 3 \/ z = 4 \/ 19 <= z <= 27) -> sv_denot E (SOff (Z.to_nat z) 0) = getr regsE (Z_to_bv 5 z)).
{ intros z Hz. rewrite sdo0, <- (PCS z Hz).
  assert (C : z = 3 \/ z = 4 \/ z = 19 \/ z = 20 \/ z = 21 \/ z = 22 \/ z = 23 \/ z = 24 \/ z = 25 \/ z = 26 \/ z = 27) by lia.
  destruct C as [C|[C|[C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]]]; subst z; unfold E; apply ew_Ereg_nat; reflexivity. }
assert (HS : st_ok tfibsegs E SS_P (restrict (w_H W) (mkst regsP (Z_to_bv 64 0x597c0) memP (seg_rom tfibsegs)))).
{ unfold SS_P. rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - fold E. unfold rFRt, rVw. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + reg_intro. rewrite BV2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
      * eapply (chunk_ok_val tfibsegs E _ _ _ _ _ (bv_unsigned (getr regsE 18)));
          [rewrite sdo0, E35; symmetry; apply Z_to_bv_bv_unsigned | exact (u64_range _) | cbn; lia | rewrite Z.add_0_r; exact VF0].
      * eapply (chunk_ok_val tfibsegs E _ _ _ _ _ (bv_unsigned (getr regsE 9)));
          [rewrite sdo0, E36; symmetry; apply Z_to_bv_bv_unsigned | exact (u64_range _) | cbn; lia | exact VF1].
      * eapply (chunk_ok_val tfibsegs E _ _ _ _ _ (bv_unsigned (getr regsE 8)));
          [rewrite sdo0, E37; symmetry; apply Z_to_bv_bv_unsigned | exact (u64_range _) | cbn; lia | exact VF2].
      * eapply (chunk_ok_val tfibsegs E _ _ _ _ _ (bv_unsigned (getr regsE 1)));
          [rewrite sdo0, E38; symmetry; apply Z_to_bv_bv_unsigned | exact (u64_range _) | cbn; lia | exact VF3].
    + reg_intro. rewrite BV8. split; [lia|]. split; [lia|]. split; [intros o Ho; apply WV; lia|].
      apply Forall_cons; [|apply Forall_nil].
      eapply (chunk_ok_val tfibsegs E _ _ _ _ _ sz); [rewrite sdo0, E34; reflexivity | cbn; lia | cbn; lia | exact VSZ].
  - fold E. apply pairwise_disjoint_of_extents. unfold rFRt, rVw, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite BV2, BV8.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [exact I | split; exact I]. }
clearbody E.
srr_run_to_sh tbl_rt_ok HS 0x597dc. clear HFr.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into ms end.
assert (FR : forall x : word, ~ (v <= bv_unsigned x < v + 16) -> ms_mem ms x = memP x).
{ intros x Hx. exact (frame_v E _ _ _ v x HF ltac:(vm_compute; reflexivity) BV8 Hx). }
clear HF.
eapply (SRr_ret_at tfibsegs tbl_rt tbl_rt_ok Hwx W E); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'. split; [reflexivity|].
rreg HS (1%bv : bv 5) Q1.
exists (ms_regs ms), (ms_mem ms), mat'.
split. { rewrite Q1, E38. unfold YK0s.ret_ok in Hra. rewrite Hra. rewrite wvb_collapse. reflexivity. }
split.
{ unfold regs_preserved. intros r Hr.
  rewrite (st_ok_reg_denot (w_H W) E _ ms (Z_to_bv 5 r) HS).
  assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold YO0d.callee_saved in Hr; lia).
  repeat (destruct C as [C|C]; [subst r;
    lazymatch goal with |- sv_denot _ (sr_get ?l ?i) = _ => let t := eval vm_compute in (sr_get l i) in change (sr_get l i) with t end;
    first [ (rewrite sdo0; first [exact E37 | exact E36 | exact E35])
          | (lazymatch goal with |- _ = getr regsE (Z_to_bv 5 ?z) => exact (CS z ltac:(lia)) end)
          | (cbn [sv_denot]; rewrite BV2; transitivity (w64 (spr + 32)); [reflexivity | symmetry; exact RE2]) ] |]).
  subst r.
  lazymatch goal with |- sv_denot _ (sr_get ?l ?i) = _ => let t := eval vm_compute in (sr_get l i) in change (sr_get l i) with t end.
  exact (CS 27 ltac:(lia)). }
split. { first [ (memv HS 1%nat 0%nat; [rewrite BV8; lia | rewrite sdo0, E18; reflexivity | lia])
              | (memv HS 1%nat 1%nat; [rewrite BV8; lia | rewrite sdo0, E18; reflexivity | lia])
              | (memv HS 1%nat 2%nat; [rewrite BV8; lia | rewrite sdo0, E18; reflexivity | lia])
              | (memv HS 0%nat 0%nat; [rewrite BV8; lia | rewrite sdo0, E18; reflexivity | lia])
              | (memv HS 0%nat 1%nat; [rewrite BV8; lia | rewrite sdo0, E18; reflexivity | lia])
              | (memv HS 0%nat 2%nat; [rewrite BV8; lia | rewrite sdo0, E18; reflexivity | lia]) ]. }
split. { first [ (memv HS 1%nat 0%nat; [rewrite BV8; lia | rewrite sdo0, E9; reflexivity | lia])
              | (memv HS 1%nat 1%nat; [rewrite BV8; lia | rewrite sdo0, E9; reflexivity | lia])
              | (memv HS 1%nat 2%nat; [rewrite BV8; lia | rewrite sdo0, E9; reflexivity | lia])
              | (memv HS 0%nat 0%nat; [rewrite BV8; lia | rewrite sdo0, E9; reflexivity | lia])
              | (memv HS 0%nat 1%nat; [rewrite BV8; lia | rewrite sdo0, E9; reflexivity | lia])
              | (memv HS 0%nat 2%nat; [rewrite BV8; lia | rewrite sdo0, E9; reflexivity | lia]) ]. }
split. { first [ (memv HS 1%nat 0%nat; [rewrite BV8; lia | rewrite sdo0, E34; reflexivity | lia])
              | (memv HS 1%nat 1%nat; [rewrite BV8; lia | rewrite sdo0, E34; reflexivity | lia])
              | (memv HS 1%nat 2%nat; [rewrite BV8; lia | rewrite sdo0, E34; reflexivity | lia])
              | (memv HS 0%nat 0%nat; [rewrite BV8; lia | rewrite sdo0, E34; reflexivity | lia])
              | (memv HS 0%nat 1%nat; [rewrite BV8; lia | rewrite sdo0, E34; reflexivity | lia])
              | (memv HS 0%nat 2%nat; [rewrite BV8; lia | rewrite sdo0, E34; reflexivity | lia]) ]. }
exact FR.
Qed.

Lemma realloc_tail : realloc_tail_spec.
Proof.
unfold realloc_tail_spec. intros W regs mem md v nb d cap sz W2 regs1 mem1 a mat1. cbv zeta.
intros HPRE HWLE HA2 HHin HHout Hg Ha0 Ha1 GA1 GA2 GA3 GOLD AMW1 SIO1 RS2 R8 R9 R10 RCS VRA VS0 VS1 VS2 VD VC VS PRES1 FR1 Z1 AP1.
unfold realloc_pre in HPRE. cbv zeta in HPRE.
destruct HPRE as (H10 & H11 & Hra & MW & Hnb0 & Hnb1 & Hsz & Hszc & Hv0 & Hv1 & Hval & HVD & HVC & HVS & HVW &
  DVS & DVP1 & DVP2 & Hd0 & Hdcap & OLD & OLDP & DOS & DOV & HPSP & HPS & HFL & HDPM & HML & NOREF & GAP & GLAZY & GBUD &
  Hal & Hsp & HPRES).
clear H10 H11 MW HVD HVC HVS DVP1 DVP2 HPSP HPS HDPM NOREF GAP GLAZY GBUD HPRES.
pose proof Hwx_tfa as Hwx.
pose proof (u64_range (getr regs 2)) as Usp.
assert (Esp : getr regs 2 = Z_to_bv 64 (bv_unsigned (getr regs 2))) by (symmetry; apply Z_to_bv_bv_unsigned).
set (sp := bv_unsigned (getr regs 2)) in *.
set (ncap := page_round_up_Z nb) in *.
assert (NCb : nb <= ncap <= nb + 4095) by (pose proof (YK02.page_round_up_Z_bounds nb ltac:(lia)) as X; unfold page_size in X; subst ncap; lia).
set (md1 := with_mmap_backing (w64 34) (w64 a) (w64 ncap) (mmap_model (w64 a) (w64 ncap) (with_vm_backing (m_vm_lazy md) mat1 md))) in *.
num.

set (ex := [w64 d; w64 cap; w64 sz; getr regs 18; getr regs 9; getr regs 8; getr regs 1]).
assert (BV2 : bv_unsigned (ew (Ereg regs1 ex) 2) = sp - 32) by (rewrite (ew_Ereg_nat regs1 ex 2 2%bv eq_refl), RS2; lia).
assert (E8 : ew (Ereg regs1 ex) 8 = w64 v) by (rewrite (ew_Ereg_nat regs1 ex 8 8%bv eq_refl); exact R8).
assert (E9 : ew (Ereg regs1 ex) 9 = w64 ncap) by (rewrite (ew_Ereg_nat regs1 ex 9 9%bv eq_refl); exact R9).
assert (E10 : ew (Ereg regs1 ex) 10 = w64 a) by (rewrite (ew_Ereg_nat regs1 ex 10 10%bv eq_refl); exact R10).
assert (ECS : forall z, (z = 3 \/ z = 4 \/ 19 <= z <= 27) -> ew (Ereg regs1 ex) (Z.to_nat z) = getr regs (Z_to_bv 5 z)).
{ intros z Hz. rewrite <- (RCS z Hz).
  assert (C : z = 3 \/ z = 4 \/ z = 19 \/ z = 20 \/ z = 21 \/ z = 22 \/ z = 23 \/ z = 24 \/ z = 25 \/ z = 26 \/ z = 27) by lia.
  destruct C as [C|[C|[C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]]]; subst z; apply ew_Ereg_nat; reflexivity. }
set (E0 := Ereg regs1 ex) in *.
assert (E32 : ew E0 32 = w64 d) by reflexivity.
assert (E33 : ew E0 33 = w64 cap) by reflexivity.
assert (E34 : ew E0 34 = w64 sz) by reflexivity.
assert (E35 : ew E0 35 = getr regs 18) by reflexivity.
assert (E36 : ew E0 36 = getr regs 9) by reflexivity.
assert (E37 : ew E0 37 = getr regs 8) by reflexivity.
assert (E38 : ew E0 38 = getr regs 1) by reflexivity.
assert (BV8 : bv_unsigned (ew E0 8) = v) by (rewrite E8; unfold w64; apply unsigned_lit_small; lia).
assert (HS : st_ok tfibsegs E0 SS_T (restrict (w_H W2) (mkst regs1 (Z_to_bv 64 0x597a0) mem1 (seg_rom tfibsegs)))).
{ unfold SS_T. rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - fold E0. unfold rFRt, rVt. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + reg_intro. rewrite BV2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
      * eapply (chunk_ok_val tfibsegs E0 _ _ _ _ _ (bv_unsigned (getr regs 18)));
          [rewrite sdo0, E35; symmetry; apply Z_to_bv_bv_unsigned | exact (u64_range _) | cbn; lia | rewrite Z.add_0_r; exact VS2].
      * eapply (chunk_ok_val tfibsegs E0 _ _ _ _ _ (bv_unsigned (getr regs 9)));
          [rewrite sdo0, E36; symmetry; apply Z_to_bv_bv_unsigned | exact (u64_range _) | cbn; lia |
           replace (sp - 32 + 8) with (sp - 24) by lia; exact VS1].
      * eapply (chunk_ok_val tfibsegs E0 _ _ _ _ _ (bv_unsigned (getr regs 8)));
          [rewrite sdo0, E37; symmetry; apply Z_to_bv_bv_unsigned | exact (u64_range _) | cbn; lia |
           replace (sp - 32 + 16) with (sp - 16) by lia; exact VS0].
      * eapply (chunk_ok_val tfibsegs E0 _ _ _ _ _ (bv_unsigned (getr regs 1)));
          [rewrite sdo0, E38; symmetry; apply Z_to_bv_bv_unsigned | exact (u64_range _) | cbn; lia |
           replace (sp - 32 + 24) with (sp - 8) by lia; exact VRA].
    + reg_intro. rewrite BV8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      * eapply (chunk_ok_val tfibsegs E0 _ _ _ _ _ d); [rewrite sdo0, E32; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact VD].
      * eapply (chunk_ok_val tfibsegs E0 _ _ _ _ _ cap); [rewrite sdo0, E33; reflexivity | cbn; lia | cbn; lia | exact VC].
      * eapply (chunk_ok_val tfibsegs E0 _ _ _ _ _ sz); [rewrite sdo0, E34; reflexivity | cbn; lia | cbn; lia | exact VS].
  - fold E0. apply pairwise_disjoint_of_extents. unfold rFRt, rVt, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite BV2, BV8.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [exact I | split; exact I]. }
clearbody E0.
change (w64 0x597a0) with (Z_to_bv 64 0x597a0).

srr_run_to_sh tbl_rt_ok HS 0x64a3c.
rename HF into HFA. clear HFr.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msA end.
assert (FRA : forall x : word, ms_mem msA x = mem1 x) by (intros x; exact (frame_none E0 _ _ _ x HFA ltac:(vm_compute; reflexivity))).
clear HFA.
eapply (RepMemKcf.imemcpy_stretch_gen_pres W2 39 E0 _ msA _ a d sz 0x597b0 _ HS).
{ reflexivity. }
{ reflexivity. }
{ vm_compute. reflexivity. }
{ vm_compute. reflexivity. }
{ regv HS (10%bv : bv 5). rewrite sdo0, E10. reflexivity. }
{ regv HS (11%bv : bv 5). rewrite sdo0, E32. reflexivity. }
{ regv HS (12%bv : bv 5). rewrite sdo0, E34. reflexivity. }
{ regv HS (1%bv : bv 5). reflexivity. }
{ lia. }
{ lia. }
{ lia. }
{ lia. }
{ lia. }
{ lia. }
{ intros x Hx. apply (apresent_eq _ mem1); [apply FRA|].
  assert (Ux : bv_unsigned (Z_to_bv 64 x) = x) by (apply unsigned_lit_small; lia).
  split; [apply HHin; rewrite Ux; lia | exists (Z_to_bv 8 0); apply Z1; rewrite Ux; lia]. }
{ intros i Hi. apply (apresent_eq _ mem1); [apply FRA|]. apply AP1; [lia | lia | apply OLDP; lia]. }
{ reflexivity. }
{ lia. }
{ intros r Hr. cbn [ss_mem In] in Hr.
  repeat (destruct Hr as [<-|Hr]; [cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi]; rewrite ?BV2, ?BV8; lia|]). destruct Hr. }
{ intros r x Hr Hx. cbn [ss_mem In] in Hr.
  repeat (destruct Hr as [<-|Hr]; [cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi] in Hx; rewrite ?BV2, ?BV8 in Hx; lia|]). destruct Hr. }
intros regs2 mem2 mat2 HS2 R10' Rkeep Hout Hpres Hin.

set (E1 := havoc E0 39 (map (getr regs2) [11; 12; 13; 14]%bv)) in HS2.
assert (EO : forall n, (n < 39)%nat -> ew E1 n = ew E0 n) by (intros n Hn; apply ew_havoc_old; exact Hn).
clearbody E1.
srr_run_to_sh tbl_rt_ok HS2 0x66b08.
rename HF into HFB. clear HFr.
lazymatch type of HS2 with st_ok _ _ _ (restrict _ ?msx) => rename msx into msB end.
assert (FRB : forall x : word, ms_mem msB x = mem2 x) by (intros x; exact (frame_none E1 _ _ _ x HFB ltac:(vm_compute; reflexivity))).
clear HFB.
assert (RB1 : getr (ms_regs msB) 1 = Z_to_bv 64 0x597c0) by (regv HS2 (1%bv : bv 5); reflexivity).
assert (RB2 : bv_unsigned (getr (ms_regs msB) 2) = sp - 32) by (regv HS2 (2%bv : bv 5); rewrite sdo0, EO by lia; exact BV2).
assert (RB8 : getr (ms_regs msB) 8 = w64 v) by (regv HS2 (8%bv : bv 5); rewrite sdo0, EO by lia; exact E8).
assert (RB9 : getr (ms_regs msB) 9 = w64 ncap) by (regv HS2 (9%bv : bv 5); rewrite sdo0, EO by lia; exact E9).
assert (RB18 : getr (ms_regs msB) 18 = w64 a) by (regv HS2 (18%bv : bv 5); rewrite sdo0, EO by lia; exact E10).
assert (RB10 : getr (ms_regs msB) 10 = w64 d) by (regv HS2 (10%bv : bv 5); rewrite sdo0, EO by lia; exact E32).
assert (RB11 : getr (ms_regs msB) 11 = w64 cap) by (regv HS2 (11%bv : bv 5); rewrite sdo0, EO by lia; exact E33).
assert (RBcs : forall z, (z = 3 \/ z = 4 \/ 19 <= z <= 27) -> getr (ms_regs msB) (Z_to_bv 5 z) = getr regs (Z_to_bv 5 z)).
{ intros z Hz.
  assert (C : z = 3 \/ z = 4 \/ z = 19 \/ z = 20 \/ z = 21 \/ z = 22 \/ z = 23 \/ z = 24 \/ z = 25 \/ z = 26 \/ z = 27) by lia.
  destruct C as [C|[C|[C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]]]; subst z;
  (lazymatch goal with |- getr _ ?rr = _ => regv HS2 rr end); rewrite sdo0, EO by lia;
  (lazymatch goal with |- _ = getr _ (Z_to_bv 5 ?z) => exact (ECS z ltac:(lia)) end). }
assert (MCB : forall x : word, ~ (a <= bv_unsigned x < a + sz) -> ms_mem msB x = mem1 x).
{ intros x Hx. rewrite FRB, (Hout x Hx). apply FRA. }
assert (APB : forall b, apresent (w_H W2) mem1 b -> apresent (w_H W2) (ms_mem msB) b).
{ intros b Hb. apply (apresent_eq _ mem2); [apply FRB|]. apply Hpres. apply (apresent_eq _ mem1); [apply FRA|]. exact Hb. }
pose proof (st_ok_restrict_mkst tfibsegs (w_H W2) E1 _ msB HS2 eq_refl) as Hshape.
lazymatch type of Hshape with _ = mkst _ ?pcv _ _ => replace pcv with (w64 RepUnmapcf.A_UOD) in Hshape by reflexivity end.
rewrite Hshape. clear Hshape.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdB := mdx) end.
assert (HMSB : msame mdB md1) by (unfold mdB; repeat apply msame_wvb_l; apply msame_refl).
clearbody mdB.

assert (KPOST : forall (regs3 : bvmap 5 word) (mem3 : word -> option byte) (mdY : Model),
  regs_preserved (ms_regs msB) regs3 ->
  (forall x : word, ~ (sp - 80 <= bv_unsigned x < sp - 32) -> ~ (d <= bv_unsigned x < d + cap) -> mem3 x = ms_mem msB x) ->
  (forall x : word, d <= bv_unsigned x < d + cap -> mem3 x = None) ->
  (forall b, 0 <= b < 2 ^ 64 -> ~ (d <= b < d + cap) -> apresent (w_H W2) (ms_mem msB) b -> apresent (w_H W2) mem3 b) ->
  (forall matF : list word, exists mat mat2 : list word,
     with_vm_backing (m_vm_lazy mdY) matF mdY =
     with_vm_backing (m_vm_lazy (mdU_of md a ncap d cap mat)) mat2 (mdU_of md a ncap d cap mat)) ->
  YG0d.same_io md mdY -> amwf mdY ->
  SRr tfibsegs W2 (mkCfg (mkst regs3 (Z_to_bv 64 0x597c0) mem3 (seg_rom tfibsegs)) mdY) (realloc_post W regs mem md v nb d cap sz)).
{ intros regs3 mem3 mdY RP3 FRK3 NONE3 AP3 KM SIO3 AMW3.
  assert (P2 : bv_unsigned (getr regs3 2) = sp - 32).
  { rewrite <- RB2. f_equal. exact (RP3 2 ltac:(unfold YO0d.callee_saved; lia)). }
  assert (P8 : getr regs3 8 = w64 v) by (rewrite <- RB8; exact (RP3 8 ltac:(unfold YO0d.callee_saved; lia))).
  assert (P9 : getr regs3 9 = w64 ncap) by (rewrite <- RB9; exact (RP3 9 ltac:(unfold YO0d.callee_saved; lia))).
  assert (P18 : getr regs3 18 = w64 a) by (rewrite <- RB18; exact (RP3 18 ltac:(unfold YO0d.callee_saved; lia))).
  assert (PCS : forall r, r = 3 \/ r = 4 \/ 19 <= r <= 27 -> getr regs3 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr. rewrite (RP3 r ltac:(unfold YO0d.callee_saved; lia)). exact (RBcs r Hr). }
  assert (MC3 : forall x : word, ~ (sp - 80 <= bv_unsigned x < sp - 32) -> ~ (d <= bv_unsigned x < d + cap) ->
     ~ (a <= bv_unsigned x < a + sz) -> mem3 x = mem1 x).
  { intros x H1 H2 H3. rewrite (FRK3 x H1 H2). exact (MCB x H3). }
  assert (VF : forall c (val : Z), sp - 32 <= c -> c + 8 <= sp ->
     val_mem tfibsegs (mrestrict (w_H W2) mem1) c 8 val -> val_mem tfibsegs (mrestrict (w_H W2) mem3) c 8 val).
  { intros c val Hc1 Hc2 Hv. apply (val_mem_tr (w_H W2) (w_H W2) mem1 mem3 c 8 val); [|exact Hv].
    intros k Hk. assert (U : bv_unsigned (Z_to_bv 64 (c + Z.of_nat k)) = c + Z.of_nat k) by (apply unsigned_lit_small; lia).
    split; [reflexivity|]. apply MC3; rewrite U; lia. }
  assert (WV3 : forall x, v <= x < v + 16 -> writable_at tfibsegs (mrestrict (w_H W2) mem3) x).
  { intros x Hx. apply (writable_tr (mrestrict (w_H W) mem)); [|apply HVW; exact Hx].
    assert (U : bv_unsigned (Z_to_bv 64 x) = x) by (apply unsigned_lit_small; lia).
    apply mrestrict_same_at.
    - apply HHout. rewrite U. lia.
    - rewrite MC3 by (rewrite U; lia). apply FR1; rewrite U; lia. }
  assert (VS3 : val_mem tfibsegs (mrestrict (w_H W2) mem3) (v + 16) 8 sz).
  { apply (val_mem_tr (w_H W2) (w_H W2) mem1 mem3 (v + 16) 8 sz); [|exact VS].
    intros k Hk. assert (U : bv_unsigned (Z_to_bv 64 (v + 16 + Z.of_nat k)) = v + 16 + Z.of_nat k) by (apply unsigned_lit_small; lia).
    split; [reflexivity|]. apply MC3; rewrite U; lia. }
  eapply SRr_mono.
  { apply (tail_fin W2 regs3 regs mem3 mdY (sp - 32) v a ncap sz P2 P8 P9 P18 PCS).
    - rewrite Esp. unfold w64. f_equal. lia.
    - exact Hra.
    - apply VF; [lia | lia | exact VS2].
    - apply VF; [lia | lia |]. replace (sp - 32 + 8) with (sp - 24) by lia. exact VS1.
    - apply VF; [lia | lia |]. replace (sp - 32 + 16) with (sp - 16) by lia. exact VS0.
    - apply VF; [lia | lia |]. replace (sp - 32 + 24) with (sp - 8) by lia. exact VRA.
    - exact WV3.
    - exact VS3.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia. }
  intros W' c' _ (-> & regs4 & mem4 & mat4 & -> & RP4 & VA & VN & VSZ4 & FR4).
  destruct (KM mat4) as (matU & mat2U & EQ).
  assert (M4 : forall x : word, ~ (v <= bv_unsigned x < v + 16) -> ~ (sp - 80 <= bv_unsigned x < sp - 32) ->
     ~ (d <= bv_unsigned x < d + cap) -> ~ (a <= bv_unsigned x < a + sz) -> mem4 x = mem1 x).
  { intros x H1 H2 H3 H4. rewrite (FR4 x H1). exact (MC3 x H2 H3 H4). }
  unfold realloc_post. cbv zeta. num.
  try change (page_round_up_Z nb) with ncap. try change (bv_unsigned (getr regs 2)) with sp.
  exists a, regs4, mem4, matU, mat2U.
  split; [exact HWLE|]. split; [exact HA2|]. split; [exact HHin|]. split; [exact HHout|].
  split; [exact Hg|]. split; [exact Ha0|]. split; [exact Ha1|].
  split; [rewrite EQ; unfold mdU_of; reflexivity|].
  split; [exact RP4|].
  split; [exact VA|]. split; [exact VN|]. split; [exact VSZ4|].
  split.
  { intros i Hi. unfold w64.
    assert (Ua : bv_unsigned (Z_to_bv 64 (a + i)) = a + i) by (apply unsigned_lit_small; lia).
    assert (Ud : bv_unsigned (Z_to_bv 64 (d + i)) = d + i) by (apply unsigned_lit_small; lia).
    rewrite (FR4 _ ltac:(rewrite Ua; lia)), (FRK3 _ ltac:(rewrite Ua; lia) ltac:(rewrite Ua; lia)), FRB, (Hin i Hi), FRA.
    apply FR1; rewrite Ud; lia. }
  split.
  { intros i Hi. unfold w64.
    assert (Ua : bv_unsigned (Z_to_bv 64 (a + i)) = a + i) by (apply unsigned_lit_small; lia).
    rewrite (M4 _ ltac:(rewrite Ua; lia) ltac:(rewrite Ua; lia) ltac:(rewrite Ua; lia) ltac:(rewrite Ua; lia)).
    apply Z1. rewrite Ua. lia. }
  split.
  { intros x Hx. rewrite (FR4 x ltac:(lia)). exact (NONE3 x Hx). }
  split.
  { intros x Hs' Ha' Hd' Hv'. rewrite (M4 x Hv' ltac:(lia) Hd' ltac:(lia)). exact (FR1 x Hs' Ha'). }
  split.
  { intros b Hb Hap Hd' Hv'.
    assert (U : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit_small; lia).
    assert (A1 : apresent (w_H W2) mem1 b).
    { destruct (Z_lt_le_dec b (sp - (0x20 + 0x140))) as [L|L]; [|destruct (Z_lt_le_dec b sp) as [L2|L2]].
      - apply AP1; [lia | lia | exact Hap].
      - apply PRES1. lia.
      - apply AP1; [lia | lia | exact Hap]. }
    apply (apresent_eq _ mem3); [apply FR4; rewrite U; exact Hv'|].
    apply AP3; [exact Hb | exact Hd' | apply APB; exact A1]. }
  split.
  { intros b Hb. assert (U : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit_small; lia).
    assert (A1 : apresent (w_H W2) mem1 b) by (split; [apply HHin; rewrite U; lia | exists (Z_to_bv 8 0); apply Z1; rewrite U; lia]).
    apply (apresent_eq _ mem3); [apply FR4; rewrite U; lia|].
    apply AP3; [lia | lia | apply APB; exact A1]. }
  split; cbn [cfg_model].
  - exact (sio_trans _ _ _ SIO3 (sio_wvb _ _ _)).
  - exact (amwf_same mdY _ (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) AMW3). }
destruct (Z.eq_dec cap 0) as [C0|C0].
-
  eapply SRr_bind.
  { apply (RepUnmapcf.unmapordie_nop W2 (ms_regs msB) (ms_mem msB) mdB).
    - right. rewrite RB11, C0. reflexivity.
    - rewrite RB1. apply RepMemKcf.ret_ok_of_mod2; [reflexivity | lia].
    - rewrite RB2. lia.
    - rewrite RB2. num. lia.
    - intros x Hx. rewrite RB2 in Hx. num. apply APB. apply PRES1. lia. }
  intros W' c' _ (-> & regs3 & mem3 & mat3 & -> & RP3 & FR3 & AP3).
  rewrite RB1.
  assert (HMSY : msame (with_vm_backing (m_vm_lazy mdB) mat3 mdB) md1) by (apply msame_wvb_l; exact HMSB).
  apply (KPOST regs3 mem3 _ RP3).
  + intros x H1 _. apply FR3. rewrite RB2. num. lia.
  + intros x Hx. exfalso. lia.
  + intros b _ _ Hb. exact (AP3 b Hb).
  + intros matF. exists matF, matF. unfold mdU_of.
    replace (cap =? 0) with true by (symmetry; apply Z.eqb_eq; exact C0). cbv beta iota.
    rewrite (md1_any md mat1 matF (w64 a) (w64 ncap) _ HMSY). symmetry. apply md1_collapse.
  + exact (sio_trans _ _ _ SIO1 (sio_msame _ _ HMSY)).
  + exact (amwf_msame _ md1 HMSY AMW1).
-
  destruct OLD as [C|(Dpos & DIMG & Dal & Cal & INd)]; [contradiction|].
  assert (PN : page_round_up_Z cap = cap) by (apply RepMmapcf.pru_idem; exact Cal).
  assert (IMGC : forall c (n : nat) val, 0x10000 <= c -> c + Z.of_nat n <= 0x600000 ->
     val_mem tfibsegs (mrestrict (w_H W) mem) c n val -> val_mem tfibsegs (mrestrict (w_H W2) (ms_mem msB)) c n val).
  { intros c n val Hc1 Hc2 Hv. apply (val_mem_tr (w_H W) (w_H W2) mem (ms_mem msB) c n val); [|exact Hv].
    intros k Hk. assert (U : bv_unsigned (Z_to_bv 64 (c + Z.of_nat k)) = c + Z.of_nat k) by (apply unsigned_lit_small; lia).
    split.
    - apply HHout. rewrite U. lia.
    - rewrite MCB by (rewrite U; lia). apply FR1; rewrite U; lia. }
  eapply SRr_bind.
  { apply (RepUnmapcf.unmapordie_unmap W2 (ms_regs msB) (ms_mem msB) mdB d cap); rewrite ?PN.
    - exact RB10.
    - exact RB11.
    - exact Dpos.
    - lia.
    - exact Dal.
    - num. lia.
    - num. lia.
    - apply map_has_In. rewrite (proj1 (proj2 HMSB)). apply maps_md1. exact INd.
    - exact (amwf_msame _ md1 HMSB AMW1).
    - rewrite RB1. apply RepMemKcf.ret_ok_of_mod2; [reflexivity | lia].
    - rewrite RB2. lia.
    - rewrite RB2. num. lia.
    - intros x Hx. rewrite RB2 in Hx. num. apply APB. apply PRES1. lia.
    - rewrite RB2. num. lia.
    - apply IMGC; [lia | lia | exact HFL].
    - apply IMGC; [lia | lia | exact HML]. }
  intros W' c' _ (-> & regs3 & mem3 & mat1u & mat3 & -> & RP3 & FR3 & NONE3 & AP3 & IO3 & AMW3).
  rewrite RB1. rewrite PN in FR3, NONE3, AP3, IO3, AMW3 |- *.
  apply (KPOST regs3 mem3 _ RP3).
  + intros x H1 H2. apply FR3; [rewrite RB2; num; lia | exact H2].
  + exact NONE3.
  + exact AP3.
  + intros matF. exists mat1u, matF. unfold mdU_of.
    replace (cap =? 0) with false by (symmetry; apply Z.eqb_neq; exact C0). cbv beta iota.
    rewrite wvb_collapse. rewrite (md1_any md mat1 mat1u (w64 a) (w64 ncap) mdB HMSB). reflexivity.
  + exact (sio_trans _ _ _ (sio_trans _ _ _ SIO1 (sio_msame _ _ HMSB)) IO3).
  + exact AMW3.
Qed.
End a.
