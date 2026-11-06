(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_lits Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Lept_fuzzkit D_iface D_defs D_libiface Gm_iface Gm_kit Gm_leaf Fh_iface Fh_sel_iface Fh_statics Fh_selkit LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma tr_deser : Forall (fun r => Forall (fun f => In [f; r; 0x910a0; D_libiface.RA_TOP] CLIENT_TRACES) DESTROY_FREE_RAS) DESER_DESTROY_RAS.
Proof.
  apply Forall_forall. intros r Hr. apply Forall_forall. intros f Hf.
  unfold DESER_DESTROY_RAS in Hr. unfold DESTROY_FREE_RAS in Hf. cbn [In] in Hr, Hf.
  destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; destruct Hf as [<-|[<-|[]]]; apply ct_mem_In; vm_compute; reflexivity.
Qed.
Definition FUZZ_DESTROY_RAS : list Z := [0x91118; 0x91128; 0x91130].
Lemma tr_destroy : forall r, In r FUZZ_DESTROY_RAS -> Forall (fun f => In [f; r; D_libiface.RA_TOP] CLIENT_TRACES) DESTROY_FREE_RAS.
Proof.
  intros r Hr. apply Forall_forall. intros f Hf. unfold FUZZ_DESTROY_RAS in Hr. unfold DESTROY_FREE_RAS in Hf. cbn [In] in Hr, Hf.
  repeat (destruct Hr as [<-|Hr]; [destruct Hf as [<-|[<-|[]]]; apply ct_mem_In; vm_compute; reflexivity|]). destruct Hr.
Qed.

(* [comment removed for export] *)
Section FzStatics.
Variable RT : rt_sig.
Hypothesis GP : rt_gaps RT.
Lemma sel_names_client : forall a, 0xf0f40 <= a < 0xf0f40 + 800 -> client_static a.
Proof using GP. intros a Ha. apply (gp_globals_client RT GP). exists 0xf0f40, (0xf0f40 + 800). split; [cbn; tauto| exact Ha]. Qed.
Lemma LIB_SEL_agree : forall (P : Z -> Prop) (m m' : mem), LIB_SEL m -> agree_on P m m' -> (forall a, 0xf0f40 <= a < 0xf0f40 + 800 -> P a) -> LIB_SEL m'.
Proof using GP.
  intros P m m' H AG HP. unfold LIB_SEL, LIB_SEL_AT in *.
  apply (rw_cells_agree_nw asegs m m' _ _ H). eapply agree_sub; [exact AG|]. cbv beta. intros x Hx. apply HP. exact Hx.
Qed.
(* [comment removed for export] *)
Lemma LIB_SEL_keep : forall live frames usp (m m' : mem), LIB_SEL m ->
  agree_on (fun a => aclient live frames usp a /\ outside Lept_iface.LIB_FP a) m m' -> LIB_SEL m'.
Proof using GP.
  intros live frames usp m m' H AG. apply (LIB_SEL_agree _ m m' H AG). intros a Ha. split; [right; left; exact (sel_names_client a Ha)|].
  unfold Lept_iface.LIB_FP, g_stderr_handler. cbn [outside]. split; [lia| exact I].
Qed.
End FzStatics.

(* [comment removed for export] *)
Section FzFrame2.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Lemma live_outside_frame2 : forall Σ (m : mem) fr usp slo b k x,
  ART RT Σ m -> In (fr, 2%nat) (rt_frames RT Σ) -> rt_sp0 RT Σ - STACK_WIN <= slo ->
  In (b, k) (rt_live RT Σ) -> b <= x < b + k ->
  outside [(slo, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] x.
Proof using AF.
  intros Σ m fr usp slo b k x HA FIN SLO QIN Hx.
  pose proof (af_live_range RT AF Σ m b k HA QIN) as (_ & R1 & _).
  pose proof (af_frames_range RT AF Σ m fr 2%nat HA FIN) as (_ & _ & _ & FLV). specialize (FLV b k QIN).
  pose proof (af_fshadow_apart RT AF Σ m fr 2%nat HA FIN) as (SA1 & _). specialize (SA1 b k QIN).
  change (fs_size 2) with 256 in *. unfold shad, SHB in SA1.
  cbn [outside]. repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia].
Qed.
End FzFrame2.

(* [comment removed for export] *)
Definition fuzz_case (RT : rt_sig) (al : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d : Z) (bs : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 (Z.of_nat (length bs)) -> tp = Z_to_bv 64 TP_A -> bv_unsigned ra = D_libiface.RA_TOP ->
  0 < d -> Z.of_nat (length bs) < 2^26 -> bytes_at asegs m d bs ->
  ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n /\ d mod 8 = 0) \/ bs = []) ->
  rt_frames RT Σ = [] -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  Z.of_nat (length (rt_live RT Σ)) + D_libiface.FUZZ_LIVE <= LIVE_MAX -> D_libiface.FUZZ_COST <= rt_credit RT Σ ->
  (bv_unsigned s0 < bv_unsigned sp \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0) ->
  D_libiface.LIB_A m -> io_ssp m -> ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + D_libiface.FUZZ_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= rt_sp0 RT Σ ->
  bv_unsigned sp mod 32 = al ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc D_libiface.e_fuzz m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) D_libiface.LIB_FP m m' /\ D_libiface.LIB_A m') c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = [] /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - D_libiface.FUZZ_COST <= rt_credit RT Σ').

(* [comment removed for export] *)
Ltac frame_release_raw RT AF GP MST Σ0 fr k SZ PF AGF PFS usp lo pcafter ivt pft getacl C1 C2 C3 C4 C5 :=
  cps_stop;
  art_now RT AF ivt;
  lazymatch goal with AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ => is_var PFx; agf_munch AGFx MUx pft end;
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
    let FRSc := fresh "FRSc" in
    assert (FRSc : rt_frames RT S = (fr, k) :: rt_frames RT Σ0)
      by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity);
    let S2 := fresh "S2" in let fl := fresh "fl" in let FLC := fresh "FLC" in let FLN := fresh "FLN" in let FL0 := fresh "FL0" in
    let FLHI := fresh "FLHI" in let FLP := fresh "FLP" in let REL := fresh "REL" in
    destruct (af_frame_release RT AF S mm fr k _ A FRSc) as (S2 & fl & FLC & FLN & FL0 & FLHI & FLP & REL);
    change (fs_size k) with SZ in FLP;
    let off := eval vm_compute in (SZ - 8)%Z in replace (fr + SZ - 8)%Z with (fr + off)%Z in FLP by lia;
    repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in FLHI end; unfold STACK_WIN in FLHI;
    (* [comment removed for export] *)
    repeat match goal with
    | IN : In (?b, ?kk) _ |- _ =>
        lazymatch goal with
        | _ : fl < b \/ b + kk <= fl |- _ => fail
        | _ => let FA := fresh "FLA" in
               assert (FA : fl < b \/ b + kk <= fl)
                 by (apply (flag_apart _ _ fl b (b + kk) FLN); let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
                     right; right; left; exists b, kk; split; [solve [in_live_tac] | lia])
        end
    end;
    let SSPs := fresh "SSPs" in
    let D1 := fresh "D1" in let D2 := fresh "D2" in let D3 := fresh "D3" in let D4 := fresh "D4" in let D5 := fresh "D5" in
    pose proof C1 as D1; hide D1; pose proof C2 as D2; hide D2; pose proof C3 as D3; hide D3; pose proof C4 as D4; hide D4;
    lazymatch goal with AGFx : agree_on PF ?m0 mm |- _ => pose proof (LIB_SEL_keep RT GP _ _ _ m0 mm C5 AGFx) as D5; unfold LIB_SEL, LIB_SEL_AT in D5; hide D5 end;
    lazymatch goal with SSPx : io_ssp mm |- _ => pose proof SSPx as SSPs; hide SSPs end;
    walk_to AF MST [(fl, fl + 1)] [pcafter];
    cps_stop;
    lazymatch goal with MUx : munch [(fl, fl + 1)] mm ?m', WMx : wmono asegs mm ?m', FLC' : rw_cells asegs ?m' fl _ |- _ =>
      let ART2 := fresh "ART2" in let FRS2 := fresh "FRS2" in let LV2 := fresh "LV2" in let SP2 := fresh "SP2" in
      let CR2 := fresh "CR2" in let AL2 := fresh "AL2" in let AM2 := fresh "AM2" in let AGS := fresh "AGS" in
      destruct (REL m' MUx WMx FLC') as (ART2 & FRS2 & LV2 & SP2 & CR2 & AL2 & AM2);
      assert (AGS : agree_on client_static mm m')
        by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply MUx; cbn [outside]; split; [| exact I];
            let Hin := fresh "Hin" in intros Hin; apply FLN; replace fl with (bv_unsigned a) by lia; right; left; exact Ha);
      unfold hid in SSPs, D1, D2, D3, D4, D5;
      let SSP2 := fresh "SSP" in
      let E1 := fresh "LSEV" in let E2 := fresh "LALLOC" in let E3 := fresh "LDEALLOC" in let E4 := fresh "LHAND" in let E5 := fresh "LSEL" in
      assert (E1 := rw_cells_agree_nw asegs mm m' _ _ D1 (static_agree RT GP client_static mm m' AGS (fun a Ha => Ha) 0xf0ec0 4 ltac:(cbn; tauto)));
      assert (E2 := rw_cells_agree_nw asegs mm m' _ _ D2 (static_agree RT GP client_static mm m' AGS (fun a Ha => Ha) 0xf0f00 8 ltac:(cbn; tauto)));
      assert (E3 := rw_cells_agree_nw asegs mm m' _ _ D3 (static_agree RT GP client_static mm m' AGS (fun a Ha => Ha) 0xf0f20 8 ltac:(cbn; tauto)));
      assert (E4 := rw_cells_agree_nw asegs mm m' _ _ D4 (static_agree RT GP client_static mm m' AGS (fun a Ha => Ha) 0xf0ee0 8 ltac:(cbn; tauto)));
      assert (E5 := rw_cells_agree_nw asegs mm m' _ _ D5 (static_agree RT GP client_static mm m' AGS (fun a Ha => Ha) 0xf0f40 800 ltac:(cbn; tauto)));
      clear D1 D2 D3 D4 D5;
      assert (SSP2 : io_ssp m') by (exact (io_ssp_agree RT GP client_static S2 mm m' SSPs ART2 AGS (fun a Ha => Ha)));
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; split; [| exact I]; let Hin := fresh "Hin" in intros Hin;
        lazymatch type of Hx with PF ?z =>
          apply (flag_not_client _ _ (rt_live RT Σ0) (rt_frames RT Σ0) fl lo usp FLN ltac:(lia) ltac:(lia));
          [ first [ solve [live_sub_tac] | solve [live_add_tac] ] | solve [frames_sub_tac] | replace fl with z by lia; getacl Hx ] end);
      apply (cps_ASTA_switch RT _ S2 _ _ _ AL2 AM2);
      clear REL SSPs FLC FLN AGS
    end
  end.

