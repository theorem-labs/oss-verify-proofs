(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA RA_seql RA_sjs3 PF_low PF_file PF_pc1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIcp2qs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpkua AIcppc0 AIcp2qw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcptdg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcptdg AIcp1qh.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpkua.AIcpilj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpkua OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcppc0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp2qw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcptdg.AIcp8qs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcptdg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp1qh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN ExW.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Eg3i DA_Cells DA_Ldix.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Storrsf.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac icpt_consts_in H ::= unfold PCM_STACK, pcm_post, tryinit_post in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.word_eq_guarded.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor5a9.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_transport_after_call segs m m' MU WM.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietml6.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietml6.dlia3.
(* [comment removed for export] *)
(* [comment removed for export] *) From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store_sfdx.
(* [comment removed for export] *)
Ltac brf K := if_cases K; zify_cond K.

Definition VP_DEPTH : Z := 5392.      (* [comment removed for export] *)
Definition VP_VF_RET : Z := 0x4ada0.  (* [comment removed for export] *)
Definition FMTD_A : Z := 0x149ba.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition vpicpt_cells (m : word -> option byte) : Prop :=
     asan_inited_cell m
  /\ ro_cells rsegs m 0xa8b60 [C8 (Z_to_bv 64 0x1466e8)]
  /\ ro_cells rsegs m 0x14673c [C1 (Z_to_bv 8 1)]
  /\ ro_cells rsegs m 0xaa900 [C8 (Z_to_bv 64 0xa14d8)]
  /\ ro_cells rsegs m 0xaa908 [C8 (Z_to_bv 64 0x9e3c8)]
  /\ map_cells m.
Lemma fok_vpicpt_cells : fokP vpicpt_cells.
Proof.
  unfold vpicpt_cells, asan_inited_cell. do 5 (apply fokP_and; [apply fok_ro_cells; far_cells|]). apply fok_map_cells.
Qed.
(* [comment removed for export] *)
Definition vpsh_low (A : Z) (m : word -> option byte) : Prop := vpicpt_cells m /\ range_ok m A 4.
Lemma fok_vpsh_low : forall A, fokP (vpsh_low A).
Proof. intros A. apply fokP_and; [apply fok_vpicpt_cells | apply fok_range_ok; lia]. Qed.
Local Ltac fok_lemma P ::= lazymatch P with
  | vpicpt_cells => constr:(fok_vpicpt_cells)
  | vpsh_low ?A => constr:(fok_vpsh_low A)
  | _ => fok_lemma_base P end.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= refok_store_hook m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= refok_all W m m' MU.
Local Ltac icpt_relow W m m' MU ::= refok_all W m m' MU.

Section VPSH.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (lo A VA : Z) (slots : list word).
  #[local] Notation q := (bv_unsigned sp).
  Hypothesis LO : (lo <= q - VP_DEPTH)%Z.
  Hypothesis GT : (alloc_ceiling <= lo)%Z.   (* [comment removed for export] *)
  Hypothesis VLO : (q <= VA)%Z.
  Hypothesis VHI : (VA + 8 * Z.of_nat (length slots) <= 2^63)%Z.
  Hypothesis ARL : (IMG_LO <= A)%Z.
  Hypothesis ART : (A + 4 <= RO_TOP)%Z.

  Definition vp_frames (m1 : word -> option byte) (j8 : list byte) : Prop :=
       rw_cells rsegs m1 (q + -48) [CB 8 j8; C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA); C8 s1; C8 s0; C8 ra]
    /\ rw_cells rsegs m1 (q + -96) [C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA); C8 s2; C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 0x4a230)].

  Definition vp_pre_post (m : word -> option byte) : machine_state -> Prop :=
    fun ms => exists (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (j8 : list byte) (m' : word -> option byte),
      ms = MS (mkR (Z_to_bv 64 VP_VF_RET) (Z_to_bv 64 (q + -96)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 STDOUT_F)
                   (Z_to_bv 64 STDOUT_F) (Z_to_bv 64 A) (Z_to_bv 64 VA) a3 a4 a5 a6 a7
                   (Z_to_bv 64 VA) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x9e3c8) fc None m' (seg_rom rsegs)
      /\ munch [(q - VP_DEPTH, q)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (q + -96)
      /\ vp_frames m' j8
      /\ vpsh_low A m'.

  #[using="ART VHI VLO GT LO Clg"] Lemma vp_pre : forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (m : word -> option byte),
    a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 VA ->
    stk rsegs m lo q -> ro_cells rsegs m A PF_pc1.FMT_D -> bytes_at rsegs m VA (u64s slots) ->
    vpsh_low A m -> mem_inv rsegs m ->
    evt rsegs (vp_pre_post m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VPRINTF_ICPT_ENTRY) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros -> -> ST HF VAA VL MI.
    pose proof VL as ((CI & Gcf & Ccp & Crealp & Crealf & MC) & RNG). unfold asan_inited_cell in CI.
    pose proof alloc_ceiling_val as CV. unfold vp_frames.
    unfold GLOBALS_TOP, RO_TOP, VP_DEPTH, IMG_LO, IMG_HI, VPRINTF_ICPT_ENTRY, VP_VF_RET in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    unfold PF_pc1.FMT_D in HF. pose proof (ro_cells_bound _ _ _ _ HF) as AB. cbn [cells_size csize Nat.add] in AB.
    pose proof (bytes_at_bound _ _ _ _ VAA) as VB. rewrite u64s_length in VB.
    pose proof (munch_refl [(bv_unsigned sp - 5392, bv_unsigned sp)]%Z m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    assert (FB : bytes_at rsegs m A (FMTB_D ++ [Z_to_bv 8 0])) by exact (proj2 HF). unfold FMTB_D in FB. cbn [app] in FB.
    zs. (* [comment removed for export] *)
    carve_frame 48%nat ST.
    do 7 zs.
    (* [comment removed for export] *)
    zs. call_lit tryinit_spec by (idtac;
      lazymatch goal with
      | |- asan_inited_cell _ => unfold asan_inited_cell; eassumption
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
      | |- mem_inv _ _ => eassumption
      | |- _ => rewrite ?unsigned_lit by lia; lia
      end).
    zs. brf K0. { exfalso. try (generalize alloc_ceiling_val); clear -K0. cbv in K0. lia. }
    zs. zs. zs. zs. cbv beta. change (bv_unsigned (Z_to_bv 8 1)) with 1%Z. zs.
    zs. brf K1. { exfalso. try (generalize alloc_ceiling_val); clear -K1. cbv in K1. lia. }
    zs. zs. zs. zs.
    (* [comment removed for export] *)
    zs. call_icpt pcm_fmt_d by (idtac; unfold FMTB_D; cbn [app length Z.of_nat];
      lazymatch goal with
      | |- bytes_at _ _ _ [_;_;_;_] => rewrite ?unsigned_lit by lia; match goal with H : bytes_at rsegs _ A _ |- _ => exact H end
      | |- bytes_at _ _ _ (u64s _) => rewrite ?unsigned_lit by lia; eassumption
      | |- SLOTS_C _ => exact I
      | |- map_cells ?mx => match goal with H : vpsh_low A mx |- _ => exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj1 H)))))) end
      | |- mem_inv _ _ => eassumption
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
      | |- range_ok ?mx _ _ => rewrite ?unsigned_lit by lia; match goal with H : vpsh_low A mx |- _ => exact (proj2 H) end
      | |- @eq _ _ _ => rewrite ?unsigned_lit by lia; reflexivity
      | |- _ => rewrite ?unsigned_lit by lia; unfold PCM_STACK; cbn [length Z.of_nat]; lia
      end || match goal with |- ?G => idtac "PCMSIDE-FAIL:" G end).
    (* [comment removed for export] *)
    zto 0x4ad34%Z.
    lazymatch goal with STq : stk rsegs _ lo _ |- _ => carve_frame 48%nat STq end.
    zto 0x5fce0%Z.
    call_lit tryinit_spec by (idtac;
      lazymatch goal with
      | |- asan_inited_cell _ => unfold asan_inited_cell; eassumption
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
      | |- mem_inv _ _ => eassumption
      | |- _ => rewrite ?unsigned_lit by lia; lia
      end).
    zs. brf K2. { exfalso. try (generalize alloc_ceiling_val); clear -K2. cbv in K2. lia. }
    zs. zs. zs. zs. cbv beta. change (bv_unsigned (Z_to_bv 8 1)) with 1%Z. zs.
    zs. brf K3. { exfalso. try (generalize alloc_ceiling_val); clear -K3. cbv in K3. lia. }
    zto 0x4a268%Z.
    call_icpt pcm_fmt_d by (idtac; unfold FMTB_D; cbn [app length Z.of_nat];
      lazymatch goal with
      | |- bytes_at _ _ _ [_;_;_;_] => rewrite ?unsigned_lit by lia; match goal with H : bytes_at rsegs _ A _ |- _ => exact H end
      | |- bytes_at _ _ _ (u64s _) => rewrite ?unsigned_lit by lia; eassumption
      | |- SLOTS_C _ => exact I
      | |- map_cells ?mx => match goal with H : vpsh_low A mx |- _ => exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj1 H)))))) end
      | |- mem_inv _ _ => eassumption
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
      | |- range_ok ?mx _ _ => rewrite ?unsigned_lit by lia; match goal with H : vpsh_low A mx |- _ => exact (proj2 H) end
      | |- @eq _ _ _ => rewrite ?unsigned_lit by lia; reflexivity
      | |- _ => rewrite ?unsigned_lit by lia; unfold PCM_STACK; cbn [length Z.of_nat]; lia
      end || match goal with |- ?G => idtac "PCMSIDE2-FAIL:" G end).
    zto 0x9e3c8%Z.
    apply evt_done; unfold vp_pre_post; unfold GLOBALS_TOP, RO_TOP, VP_DEPTH, IMG_LO, IMG_HI, VPRINTF_ICPT_ENTRY, VP_VF_RET; idtac.
    hot_eexists_all.
    split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [split; eassumption|]. assumption.
  Qed.

  (* [comment removed for export] *)
  Definition vp_post_post (r : word) (m : word -> option byte) : machine_state -> Prop :=
    fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m (seg_rom rsegs)
      /\ stk rsegs m lo q.

  #[using="LO slots"] Lemma vp_post : forall t0 t1 t2 x8 x9 (r : word) a1 a2 a3 a4 a5 a6 a7 x18 t3 t4 t5 t6 (m : word -> option byte) (j8 : list byte),
    stk rsegs m lo (q + -96) -> mem_inv rsegs m -> vp_frames m j8 ->
    evt rsegs (vp_post_post r m)
      (MS (mkR (Z_to_bv 64 VP_VF_RET) (Z_to_bv 64 (q + -96)) gp tp t0 t1 t2 x8 x9 r a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VP_VF_RET) fc None m (seg_rom rsegs)).
  Proof.
    intros until j8. intros ST MI [FR1 FR2]. unfold vp_post_post, VP_VF_RET, VP_DEPTH in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    do 5 zs. release_frame FR2 ST (bv_unsigned sp + -48)%Z.
    zs.
    do 4 zs. release_frame FR1 ST (bv_unsigned sp).
    zs.
    apply evt_done. hot_eexists_all. split; [reflexivity| exact ST].
  Qed.
End VPSH.
