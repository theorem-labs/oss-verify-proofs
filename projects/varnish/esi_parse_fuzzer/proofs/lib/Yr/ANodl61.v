(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AIcpm9j ARtStmts AMTac ANodeA7 ANodeA6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac hot_qset := lazymatch goal with |- evt _ ?Q _ => lazymatch Q with (fun _ => _) => set (hotQ := Q) | _ => idtac end | |- _ => idtac end.
Ltac hot_qend := lazymatch goal with |- evt _ ?Q _ => first [ is_var Q; subst Q | idtac ] | |- ?Q _ => first [ is_var Q; subst Q; cbv beta | idtac ] | |- _ => idtac end.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac.amstep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac.amz ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma roundup_famap : forall x, 0 <= x < 2^62 -> Z.land (x + 262143) 18446744073709289472 = round_up x 262144.
Proof.
  intros x Hx. change 18446744073709289472 with (2^64 - 2^18). rewrite StrFun.land_align_down by lia.
  unfold round_up. change (2^18) with 262144. replace (x + 262144 - 1) with (x + 262143) by lia.
  pose proof (Z_div_mod_eq_full (x + 262143) 262144). lia.
Qed.
Lemma roundup_famap_cap : forall x, 0 <= x <= 2^29 -> round_up x 262144 <= 2^29.
Proof. intros x Hx. unfold round_up. pose proof (Z_div_mod_eq_full (x + 262144 - 1) 262144). nia. Qed.
Lemma roundup_famap_range : forall x, 0 <= x -> x <= round_up x 262144 < x + 262144 /\ round_up x 262144 mod 262144 = 0.
Proof. intros x Hx. split; [split; [apply round_up_ge | apply round_up_lt] | apply round_up_mod]; lia. Qed.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Notation wz z := (Z_to_bv 64 z) (only parsing).
Definition efas_entry : Z := 0x3a138.
Definition efas_mapret : Z := 0x3a1d8.
Definition efas_name : Z := 0x18d54.      (* [comment removed for export] *)
Definition kFaMap : Z := 262144.

(* [comment removed for export] *)
Definition efas_frame (scr : list byte) (s3 s2 s1 s0 ra : word) : list cell := [CB 8 scr; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition keep (P : Prop) : Prop := P.
Ltac post_call_zx segs m fixup :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  rewrite ?unsigned_lit in MUc by lia;
  try rewrite ?unsigned_lit in PO by lia;
  fixup MUc; try fixup PO;
  lazymatch type of MUc with
  | munch _ m ?m' =>
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).
Tactic Notation "callzx" uconstr(SPEC) tactic3(fixup) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | post_call_zx segs m fixup ]
  end.
Ltac rebundle := repeat (lazymatch goal with
  | |- ro_cells _ _ _ _ => eassumption
  | |- rw_cells _ _ _ _ => eassumption
  | |- bytes_at _ _ _ _ => eassumption
  | |- mapped _ _ _ => eassumption
  | |- thread_cells _ _ _ _ _ => unfold thread_cells
  | |- poison_consts _ => unfold poison_consts
  | |- _ /\ _ => split
  | |- _ => first [eassumption | unfold pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *; plia] end).
Ltac sidec := lazymatch goal with
  | |- evt _ _ _ => idtac
  | |- _ => first [ eassumption | reflexivity | lia
                  | (rewrite unsigned_lit by lia; first [reflexivity | lia | assumption])
                  | (unfold pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *; plia) | (intros; lia) ]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition efas_map_pre_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo R rb num mfa : Z) (Q : machine_state -> Prop),
    let nm := round_up (4 * num) kFaMap in let fe := rb + kFreeArrayOffset + mfa in
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> alloc_ceiling <= lo ->
    a0 = wz 0xb1d58 -> a1 = wz R -> a2 = wz rb -> a3 = wz num ->
    kHighMemBeg <= R -> R + 128 <= alloc_ceiling -> 0 <= rb -> rb + kFreeArrayOffset + 2^29 <= 2^47 ->
    0 <= num <= 2^27 -> 0 <= mfa -> mfa < 4 * num ->
    ro_cells rsegs m 0xb1d90 [C1 (Z_to_bv 8 0)] ->
    rw_cells rsegs m (R + 24) [C8 (wz mfa)] ->
    (forall (m' : word -> option byte) (scr : list byte),
        rw_cells rsegs m' (bv_unsigned sp + -48) (efas_frame scr s3 s2 s1 s0 ra) ->
        munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
        stk rsegs m' lo (bv_unsigned sp + -48) ->
        evt rsegs Q (MS (mkR (wz efas_mapret) (wz (bv_unsigned sp + -48)) gp tp t0 t1 t2 (wz nm) (wz fe)
                            (wz 0xb1d58) (wz fe) (wz (nm - mfa)) (wz efas_name) (wz mfa) (wz kFreeArrayOffset) a6 a7
                            (wz (nm - mfa)) (wz R) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (wz mapcb_entry) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz efas_entry) fc None m (seg_rom rsegs)).

Theorem efas_map_pre_ok : efas_map_pre_stmt.
Proof.
  unfold efas_map_pre_stmt. intros until Q. cbv zeta.
  intros MI ST LOLE CEIL A0 A1 A2 A3 RLO RHI RB0 RBH NUM MFA0 NOFIT PMH MFC K.
  pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  unfold efas_entry, efas_mapret, efas_name, efas_frame, mapcb_entry, kFaMap, kFreeArrayOffset, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all. subst a0 a1 a2 a3.
  pose proof (roundup_famap_range (4 * num) ltac:(lia)) as [NM1 NM2]. pose proof (roundup_famap_cap (4 * num) ltac:(lia)) as NM3.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  carve_frame 48%nat ST.
  do 6 amz. (* [comment removed for export] *)
  amz. amz. amz. (* [comment removed for export] *)
  rewrite (Z.shiftl_mul_pow2 num 2) by lia. change (2 ^ 2) with 4.
  try rewrite (Z.mod_small (num * 4) 18446744073709551616) by lia.
  amz. br_not_taken. (* [comment removed for export] *)
  amz. amz. amz. amz. amz. (* [comment removed for export] *)
  replace (num * 4 + 262143) with (4 * num + 262143) by lia. rewrite (roundup_famap (4 * num)) by lia.
  amz. amz. amz. br_not_taken. (* [comment removed for export] *)
  amz. amz. amz. amz. amz. (* [comment removed for export] *)
  replace (mfa + (rb + 3758096384)) with (rb + 3758096384 + mfa) by lia.
  amz. if_true. (* [comment removed for export] *)
  amz. amz. amz. amz. amz. amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  eapply K; eassumption.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition efas_mapped_stmt : Prop :=
  poison_stmt -> thread_stats_stmt ->
  forall (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (usp lo R nm mfa fe tsd ctx thr : Z) (old scr : list byte) (mm72 mm80 : word)
         (s3v s2v s1v s0v ra0 : word),
    let sz := nm - mfa in
    mem_inv rsegs m -> stk rsegs m lo (usp + -48) -> lo <= usp - 48 - 64 -> alloc_ceiling <= lo -> usp <= 2^47 ->
    kHighMemBeg <= R -> R + 128 <= alloc_ceiling ->
    fe mod 8 = 0 -> kHighMemBeg <= fe -> fe + sz <= 2^47 -> 8 <= sz -> sz mod 8 = 0 -> 0 <= mfa -> nm < 2^62 ->
    poison_consts m -> thread_cells m tp tsd ctx thr -> bv_unsigned tp <= kShadowOffset -> tsd + 8 <= kShadowOffset ->
    (R + 128 <= thr + off_th_stats + 72 \/ thr + off_th_stats + 88 <= R) ->
    rw_cells rsegs m (usp + -48) (efas_frame scr s3v s2v s1v s0v ra0) -> bv_unsigned ra0 mod 2 = 0 ->
    rw_cells rsegs m (R + 24) [C8 (wz mfa)] ->
    rw_cells rsegs m (sh fe) [CB (Z.to_nat (sz / 8)) old] ->
    rw_cells rsegs m (thr + off_th_stats + 72) [C8 mm72; C8 mm80] ->
    evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                 ms' = MS (mkR ra0 (wz usp) gp tp t0' t1' t2' s0v s1v (wz 1) a1' a2' a3' a4' a5' a6' a7'
                              s2v s3v s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra0) fc None m' (seg_rom rsegs)
                 /\ munch [(usp - 48 - 64, usp); (sh fe, sh fe + sz / 8); (thr + off_th_stats + 72, thr + off_th_stats + 88);
                           (R + 24, R + 32)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
                 /\ stk rsegs m' lo usp
                 /\ rw_cells rsegs m' (R + 24) [C8 (wz nm)]
                 /\ bytes_at rsegs m' (sh fe) (repeat (Z_to_bv 8 250) (Z.to_nat (sz / 8)))
                 /\ rw_cells rsegs m' (thr + off_th_stats + 72) [C8 (wz (bv_unsigned mm72 + 1)); C8 (wz (bv_unsigned mm80 + sz))])
        (MS (mkR (wz efas_mapret) (wz (usp + -48)) gp tp t0 t1 t2 (wz nm) (wz fe) (wz fe) a1 a2 a3 a4 a5 a6 a7
                 (wz sz) (wz R) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz efas_mapret) fc None m (seg_rom rsegs)).

Theorem efas_mapped_ok : efas_mapped_stmt.
Proof.
  unfold efas_mapped_stmt. intros PS TS. intros until ra0. cbv zeta.
  intros MI ST LOLE CEIL USP RLO RHI FAL FLO FHI SZ8 SZM MFA0 NMH PC TC TPLO TSDLO DJ FR RA MFC SHC THS.
  pose proof alloc_ceiling_val as CV. unfold efas_mapret, efas_frame, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg, off_th_stats in *. aobj_lin_all. unfold kShadowOffset in TPLO, TSDLO.
  remember (nm - mfa) as sz eqn:HSZ.
  (* [comment removed for export] *)
  set (bq := fe / 8) in *. assert (BQ : fe = 8 * bq) by (subst bq; rewrite (Z_div_mod_eq_full fe 8) at 1; rewrite FAL; lia). clearbody bq.
  set (u8 := sz / 8) in *. assert (U8 : sz = 8 * u8) by (subst u8; rewrite (Z_div_mod_eq_full sz 8) at 1; rewrite SZM; lia). clearbody u8.
  assert (SHB : sh fe = bq + 2147450880) by (unfold sh, kShadowOffset; rewrite BQ, Z.mul_comm, Z.div_mul by lia; lia).
  rewrite SHB in *.
  assert (SHHI : bq + 2147450880 + u8 <= 17594333495296) by lia.
  replace (usp - 48 - 64) with (usp + -48 - 64) by lia.
  replace (thr + 2800 + 72) with (thr + 2872) in * by lia. replace (thr + 2800 + 88) with (thr + 2888) in * by lia.
  pose proof (munch_refl [(usp + -48 - 64, usp); (bq + 2147450880, bq + 2147450880 + u8); (thr + 2872, thr + 2888); (R + 24, R + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof TC as TC0. unfold thread_cells in TC. (first [ dand6 TC as T1 T2 T3 T4 T5 TR | destruct TC as (T1 & T2 & T3 & T4 & T5 & TR) ]). unfold kHighMemBeg in TR. aobj_lin_all.
  (first [ dand8 TR as TR1 TR2 TR3 TR4 TR5 TR6 TR7 TR8 | destruct TR as (TR1 & TR2 & TR3 & TR4 & TR5 & TR6 & TR7 & TR8) ]). aobj_lin_all.
  hot_qset.
  amz. br_not_taken. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. if_false. (* [comment removed for export] *)
  amz. amz. amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  callzx (PS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fe sz 250 lo old) (fun H => rewrite ?SHB in H; replace (sz / 8) with u8 in H by (rewrite U8, Z.mul_comm, Z.div_mul by lia; reflexivity)).
  all: try (rewrite SHB). all: try sidec.
  all: try (unfold pz_in, kHighMemBeg; right; lia).   (* [comment removed for export] *)
  1: { replace (sz / 8) with u8 by (rewrite U8, Z.mul_comm, Z.div_mul by lia; reflexivity). exact SHC. }
  lazymatch goal with H : bytes_at rsegs ?mm (bq + 2147450880) _ |- _ =>
    rename H into SHP; change (keep ltac:(lazymatch type of SHP with ?t => exact t end)) in SHP || idtac;
    pose proof (munch_refl [(usp + -48 - 64, usp); (thr + 2872, thr + 2888); (R + 24, R + 32)] mm) as MU2;
    pose proof (wmono_refl rsegs mm) as WM2 end.
  (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  callz (TS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tsd ctx thr lo).
  all: try sidec.
  all: lazymatch goal with |- evt _ _ _ => idtac | _ => rebundle end.
  unfold off_th_stats.
  amz. amz. amz. amz. amz. amz. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  do 7 amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  all: hot_qend.
  lazymatch goal with H : stk rsegs _ lo _ |- _ => release_frame FR H usp end.
  finish.
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try eassumption.
  unfold keep in SHP. eapply bytes_at_transport; [exact SHP | exact MU2 | cbn [disjoint_from]; rewrite repeat_length; lia].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition efas_fail_stmt : Prop :=
  forall (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (usp lo : Z) (scr : list byte)
         (s3v s2v s1v s0v ra0 : word),
    mem_inv rsegs m -> stk rsegs m lo (usp + -48) -> lo <= usp - 48 -> alloc_ceiling <= lo -> usp <= 2^47 ->
    rw_cells rsegs m (usp + -48) (efas_frame scr s3v s2v s1v s0v ra0) -> bv_unsigned ra0 mod 2 = 0 ->
    evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                 ms' = MS (mkR ra0 (wz usp) gp tp t0' t1' t2' s0v s1v (wz 0) a1' a2' a3' a4' a5' a6' a7'
                              s2v s3v s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra0) fc None m' (seg_rom rsegs)
                 /\ munch [(usp - 48, usp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
                 /\ stk rsegs m' lo usp)
        (MS (mkR (wz efas_mapret) (wz (usp + -48)) gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz efas_mapret) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)

End CEIL.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
