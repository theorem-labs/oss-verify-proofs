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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA RA_seql RA_sjs3 PF_low PF_file PF_pc1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcp2qs AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpkua AIcppc0 AIcp2qw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcptdg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcptdg AIcp1qh.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp2qs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua.AIcpilj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcppc0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp2qw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcptdg.AIcp8qs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcptdg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp1qh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Eg3i DA_Cells DA_Ldix.
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

Definition FP_DEPTH : Z := 5408.      (* [comment removed for export] *)
Definition FP_VF_RET : Z := 0x4b2dc.  (* [comment removed for export] *)
Definition PCM_CTX : Z := 0x1f2a7.    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition fpicpt_cells (m : word -> option byte) : Prop :=
     asan_inited_cell m
  /\ ro_cells rsegs m 0xa9180 [C8 (Z_to_bv 64 0x146ee8)]
  /\ ro_cells rsegs m 0x146f3c [C1 (Z_to_bv 8 1)]
  /\ ro_cells rsegs m 0xaaf28 [C8 (Z_to_bv 64 0x9ea00)]
  /\ map_cells m.
Lemma fok_fpicpt_cells : fokP fpicpt_cells.
Proof.
  unfold fpicpt_cells, asan_inited_cell. do 4 (apply fokP_and; [apply fok_ro_cells; far_cells|]). apply fok_map_cells.
Qed.
(* [comment removed for export] *)
Definition fpsh_low (A la : Z) (m : word -> option byte) : Prop := fpicpt_cells m /\ range_ok m A la.
Lemma fok_fpsh_low : forall A la, 0 <= la -> fokP (fpsh_low A la).
Proof. intros A la H. apply fokP_and; [apply fok_fpicpt_cells | apply fok_range_ok; lia]. Qed.
Definition fpsh_low_s (A la P ln : Z) (m : word -> option byte) : Prop := fpsh_low A la m /\ range_ok m P ln.
Lemma fok_fpsh_low_s : forall A la P ln, 0 <= la -> 0 <= ln -> fokP (fpsh_low_s A la P ln).
Proof. intros. apply fokP_and; [apply fok_fpsh_low; lia | apply fok_range_ok; lia]. Qed.
Local Ltac fok_lemma P ::= lazymatch P with
  | fpicpt_cells => constr:(fok_fpicpt_cells)
  | fpsh_low ?A ?la => constr:(fok_fpsh_low A la ltac:(lia))
  | fpsh_low_s ?A ?la ?P ?ln => constr:(fok_fpsh_low_s A la P ln ltac:(lia) ltac:(lia))
  | _ => fok_lemma_base P end.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= refok_store_hook m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= refok_all W m m' MU.
Local Ltac icpt_relow W m m' MU ::= refok_all W m m' MU.

(* [comment removed for export] *)
Lemma u64s_6 : forall a2 a3 a4 a5 a6 a7 : word,
  u64s [a2; a3; a4; a5; a6; a7] = le8 a2 ++ le8 a3 ++ le8 a4 ++ le8 a5 ++ le8 a6 ++ le8 a7.
Proof. intros. reflexivity. Qed.

Section FPSH.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (lo A la Fa : Z) (FMT : list cell) (fbytes : list byte).
  #[local] Notation q := (bv_unsigned sp).
  Hypothesis LO : (lo <= q - FP_DEPTH)%Z.
  Hypothesis GT : (alloc_ceiling <= lo)%Z.   (* [comment removed for export] *)
  Hypothesis QHI : (q <= 2^47)%Z.
  Hypothesis ARL : (IMG_LO <= A)%Z.
  Hypothesis ART : (A + la <= RO_TOP)%Z.
  Hypothesis FBY : cells_bytes FMT = fbytes ++ [Z_to_bv 8 0].
  Hypothesis FLA : (Z.of_nat (length fbytes) + 1 = la)%Z.
  Hypothesis FAR : (0 <= Fa < 2^64)%Z.

  (* [comment removed for export] *)
  Definition fp_frame (m1 : word -> option byte) (j8 : list byte) (a2 a3 a4 a5 a6 a7 : word) : Prop :=
    rw_cells rsegs m1 (q + -112)
      [CB 8 j8; C8 (Z_to_bv 64 (q + -48)); C8 (Z_to_bv 64 (q + -48)); C8 (Z_to_bv 64 (q + -48)); C8 s2; C8 s1; C8 s0; C8 ra;
       C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7].

  Definition fp_pre_post (LOWB : (word -> option byte) -> Prop) (a2 a3 a4 a5 a6 a7 : word) (m : word -> option byte) : machine_state -> Prop :=
    fun ms => exists (t0 t1 t2 a4' a5' a6' a7' t3 t4 t5 t6 : word) (j8 : list byte) (m' : word -> option byte),
      ms = MS (mkR (Z_to_bv 64 FP_VF_RET) (Z_to_bv 64 (q + -112)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 Fa)
                   (Z_to_bv 64 Fa) (Z_to_bv 64 A) (Z_to_bv 64 (q + -48)) (Z_to_bv 64 0x9ea00) a4' a5' a6' a7'
                   (Z_to_bv 64 (q + -48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x9ea00) fc None m' (seg_rom rsegs)
      /\ munch [(q - FP_DEPTH, q)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (q + -112)
      /\ fp_frame m' j8 a2 a3 a4 a5 a6 a7
      /\ LOWB m'.

  (* [comment removed for export] *)
  Ltac fp_walk1 :=
    zs; (* [comment removed for export] *)
    lazymatch goal with STq : stk rsegs _ lo _ |- _ => carve_frame 112%nat STq end;
    do 15 zs;
    (* [comment removed for export] *)
    zs; call_lit tryinit_spec by (idtac;
      lazymatch goal with
      | |- asan_inited_cell _ => unfold asan_inited_cell; eassumption
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
      | |- mem_inv _ _ => eassumption
      | |- _ => rewrite ?unsigned_lit by lia; lia
      end);
    zs; (let K0 := fresh "K" in brf K0; [ exfalso; try (generalize alloc_ceiling_val); clear -K0; cbv in K0; lia |]);
    zs; zs;
    (* [comment removed for export] *)
    zs; call_lit tryinit_spec by (idtac;
      lazymatch goal with
      | |- asan_inited_cell _ => unfold asan_inited_cell; eassumption
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
      | |- mem_inv _ _ => eassumption
      | |- _ => rewrite ?unsigned_lit by lia; lia
      end);
    zs; (let K1 := fresh "K" in brf K1; [ exfalso; try (generalize alloc_ceiling_val); clear -K1; cbv in K1; lia |]);
    zs; zs; zs; zs; cbv beta; change (bv_unsigned (Z_to_bv 8 1)) with 1%Z; zs;
    zs; (let K2 := fresh "K" in brf K2; [ exfalso; try (generalize alloc_ceiling_val); clear -K2; cbv in K2; lia |]);
    zs; zs; zs; zs.

  (* [comment removed for export] *)
  Ltac fp_walk2 :=
    zto 0x4b2d8%Z; zs.

  #[using="FLA FBY ART QHI GT LO"] Lemma fp_pre_s : forall (PCM : pcm_stmt_str fbytes) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (m : word -> option byte) (P : Z) (str : list byte),
    a0 = Z_to_bv 64 Fa -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 P ->
    stk rsegs m lo q -> ro_cells rsegs m A FMT ->
    bytes_at rsegs m P (str ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str -> (0 < P)%Z -> (q <= P)%Z ->
    (Z.of_nat (length str) + 1 <= 2^31)%Z ->
    fpsh_low_s A la P (Z.of_nat (length str) + 1) m -> mem_inv rsegs m ->
    evt rsegs (fp_pre_post (fpsh_low_s A la P (Z.of_nat (length str) + 1)) a2 a3 a4 a5 a6 a7 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FPRINTF_ICPT_ENTRY) fc None m (seg_rom rsegs)).
  Proof.
    intros until str. intros -> -> -> ST HF SB NIN P0 QP L31 VL MI.
    pose proof VL as (((CI & Gcf & Ccp & Crealf & MC) & RNG) & RNGS). unfold asan_inited_cell in CI.
    pose proof alloc_ceiling_val as CV. unfold fp_frame.
    unfold GLOBALS_TOP, RO_TOP, FP_DEPTH, IMG_LO, IMG_HI, FPRINTF_ICPT_ENTRY, FP_VF_RET in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (ro_cells_bound _ _ _ _ HF) as AB. rewrite <- (cells_bytes_length FMT (proj1 HF)), FBY, length_app in AB. cbn [length] in AB.
    pose proof (bytes_at_bound _ _ _ _ SB) as PB. rewrite length_app in PB. cbn [length] in PB.
    pose proof (munch_refl [(bv_unsigned sp - 5408, bv_unsigned sp)]%Z m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    assert (FB : bytes_at rsegs m A (fbytes ++ [Z_to_bv 8 0])) by (rewrite <- FBY; exact (proj2 HF)).
    fp_walk1.
    (* [comment removed for export] *)
    lazymatch goal with FRq : rw_cells rsegs ?mx (bv_unsigned sp + -112) _ |- _ =>
      pose proof (proj2 (proj1 (proj2 (proj1 (rw_cells_app rsegs _ _ [_;_;_;_;_;_;_;_] _) FRq)))) as VAB;
      cbn [cells_size csize Nat.add cells_bytes cbytes] in VAB; rewrite app_nil_r in VAB;
      match type of VAB with bytes_at _ _ ?ax _ => replace ax with (bv_unsigned sp + -48)%Z in VAB by (cbn; lia) end
    end.
    zs. call_icpt (PCM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo A (bv_unsigned sp + -48)%Z
                     [Z_to_bv 64 P; a3; a4; a5; a6; a7] P str []) by (idtac;
      lazymatch goal with
      | |- bytes_at _ _ A _ => exact FB || (rewrite ?unsigned_lit by lia; eassumption)
      | |- bytes_at _ _ _ (u64s _) => rewrite u64s_6; exact VAB
      | |- bytes_at _ _ P _ => exact SB || eassumption
      | |- nth_error _ _ = Some _ => reflexivity
      | |- ~ In _ _ => exact NIN
      | |- map_cells ?mx => match goal with H : fpsh_low_s _ _ _ _ mx |- _ => exact (proj2 (proj2 (proj2 (proj2 (proj1 (proj1 H)))))) end
      | |- mem_inv _ _ => eassumption
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
      | |- range_ok ?mx A _ => rewrite FLA; match goal with H : fpsh_low_s _ _ _ _ mx |- _ => exact (proj2 (proj1 H)) end
      | |- range_ok ?mx P _ => match goal with H : fpsh_low_s _ _ _ _ mx |- _ => exact (proj2 H) end
      | |- @eq _ _ _ => rewrite ?unsigned_lit by lia; first [reflexivity | f_equal; lia]
      | |- (_ \/ _)%type => rewrite ?unsigned_lit by lia; right; lia
      | |- _ => rewrite ?unsigned_lit by lia; unfold PCM_STACK; cbn [length Z.of_nat]; lia
      end || match goal with |- ?G => idtac "PCMSIDE-FAIL:" G end).
    fp_walk2.
    apply evt_done; unfold fp_pre_post; unfold GLOBALS_TOP, RO_TOP, FP_DEPTH, IMG_LO, IMG_HI, FPRINTF_ICPT_ENTRY, FP_VF_RET; idtac.
    hot_eexists_all.
    split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [eassumption|]. assumption.
  Qed.

  #[using="FLA FBY ART QHI GT LO"] Lemma fp_pre_u : forall (PCM : pcm_stmt fbytes SLOTS_C) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (m : word -> option byte),
    a0 = Z_to_bv 64 Fa -> a1 = Z_to_bv 64 A ->
    stk rsegs m lo q -> ro_cells rsegs m A FMT ->
    fpsh_low A la m -> mem_inv rsegs m ->
    evt rsegs (fp_pre_post (fpsh_low A la) a2 a3 a4 a5 a6 a7 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FPRINTF_ICPT_ENTRY) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros -> -> ST HF VL MI.
    pose proof VL as ((CI & Gcf & Ccp & Crealf & MC) & RNG). unfold asan_inited_cell in CI.
    pose proof alloc_ceiling_val as CV. unfold fp_frame.
    unfold GLOBALS_TOP, RO_TOP, FP_DEPTH, IMG_LO, IMG_HI, FPRINTF_ICPT_ENTRY, FP_VF_RET in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (ro_cells_bound _ _ _ _ HF) as AB. rewrite <- (cells_bytes_length FMT (proj1 HF)), FBY, length_app in AB. cbn [length] in AB.
    pose proof (munch_refl [(bv_unsigned sp - 5408, bv_unsigned sp)]%Z m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    assert (FB : bytes_at rsegs m A (fbytes ++ [Z_to_bv 8 0])) by (rewrite <- FBY; exact (proj2 HF)).
    fp_walk1.
    lazymatch goal with FRq : rw_cells rsegs ?mx (bv_unsigned sp + -112) _ |- _ =>
      pose proof (proj2 (proj1 (proj2 (proj1 (rw_cells_app rsegs _ _ [_;_;_;_;_;_;_;_] _) FRq)))) as VAB;
      cbn [cells_size csize Nat.add cells_bytes cbytes] in VAB; rewrite app_nil_r in VAB;
      match type of VAB with bytes_at _ _ ?ax _ => replace ax with (bv_unsigned sp + -48)%Z in VAB by (cbn; lia) end
    end.
    zs. call_icpt (PCM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo A (bv_unsigned sp + -48)%Z
                     [a2; a3; a4; a5; a6; a7]) by (idtac;
      lazymatch goal with
      | |- bytes_at _ _ A _ => exact FB || (rewrite ?unsigned_lit by lia; eassumption)
      | |- bytes_at _ _ _ (u64s _) => rewrite u64s_6; exact VAB
      | |- SLOTS_C _ => exact I
      | |- map_cells ?mx => match goal with H : fpsh_low _ _ mx |- _ => exact (proj2 (proj2 (proj2 (proj2 (proj1 H))))) end
      | |- mem_inv _ _ => eassumption
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
      | |- range_ok ?mx A _ => rewrite FLA; match goal with H : fpsh_low _ _ mx |- _ => exact (proj2 H) end
      | |- @eq _ _ _ => rewrite ?unsigned_lit by lia; first [reflexivity | f_equal; lia]
      | |- _ => rewrite ?unsigned_lit by lia; unfold PCM_STACK; cbn [length Z.of_nat]; lia
      end || match goal with |- ?G => idtac "PCMSIDEU-FAIL:" G end).
    fp_walk2.
    apply evt_done; unfold fp_pre_post; unfold GLOBALS_TOP, RO_TOP, FP_DEPTH, IMG_LO, IMG_HI, FPRINTF_ICPT_ENTRY, FP_VF_RET; idtac.
    hot_eexists_all.
    split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [eassumption|]. assumption.
  Qed.

  (* [comment removed for export] *)
  Definition fp_post_post (r : word) (m : word -> option byte) : machine_state -> Prop :=
    fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m (seg_rom rsegs)
      /\ stk rsegs m lo q.

  #[using="LO fbytes"] Lemma fp_post : forall t0 t1 t2 x8 x9 (r : word) a1 a2 a3 a4 a5 a6 a7 x18 t3 t4 t5 t6 (m : word -> option byte) (j8 : list byte) b2 b3 b4 b5 b6 b7,
    stk rsegs m lo (q + -112) -> mem_inv rsegs m -> fp_frame m j8 b2 b3 b4 b5 b6 b7 ->
    evt rsegs (fp_post_post r m)
      (MS (mkR (Z_to_bv 64 FP_VF_RET) (Z_to_bv 64 (q + -112)) gp tp t0 t1 t2 x8 x9 r a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FP_VF_RET) fc None m (seg_rom rsegs)).
  Proof.
    intros until b7. intros ST MI FR. unfold fp_post_post, fp_frame, FP_VF_RET, FP_DEPTH in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    do 5 zs. release_frame FR ST (bv_unsigned sp).
    zs.
    apply evt_done. hot_eexists_all. split; [reflexivity| exact ST].
  Qed.
End FPSH.
