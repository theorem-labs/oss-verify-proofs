(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_poison.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_poison2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_musl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_shgetc_proofs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_scanexp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SFModel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require SoftFloat.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScanProps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScan_nn.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_scan_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Shgetc_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require FmtFp_facts3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Scan_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_shgetc_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_str3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcleaf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcdefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_scommon_lg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_vsscanf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_fmt_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
Module ICPT_sscanf.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_musl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_shgetc_proofs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_scanexp.F_shgetc_proofs3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Scan_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_shgetc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_shgetc_proofs.F_shgetc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_shgetc_proofs.F_shgetc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_scanexp.F_rfile.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_str3.ICPT_str OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcleaf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcdefs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_scommon_lg.ICPT_vfscanf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_scommon_lg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_vsscanf.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_fmt_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope. Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition ASSCANF_ICPT : Z := 0x45ef8.
Definition ASSI_STACK : Z := 11952.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition assi_cells (m : word -> option byte) : Prop :=
  vfsi_cells m /\ ro_cells asegs m 0xa3ce0 [C8 (Z_to_bv 64 0x9ab20)].

Lemma assi_cells_munch : forall W m m', assi_cells m -> munch W m m' ->
  Forall (fun iv => disjoint_from W (fst iv) (snd iv - fst iv)) icpt_cell_ivs ->
  disjoint_from W 0xa3ce0 16 -> assi_cells m'.
Proof.
  intros W m m' [VC RL] MU D1 D2. split; [eapply vfsi_cells_munch; eauto; eapply disjoint_from_sub; [exact D2| lia| lia]|].
  eapply ro_cells_transport; [exact RL| exact MU|]. eapply disjoint_from_sub; [exact D2| cbn; lia| cbn; lia].
Qed.

Definition asscanf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (T PD : Z) (txt : list Z) (r : Z) (res : option Z) (djunk : word) (lo : Z) (canary : word) (m : word -> option byte)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte) (ev' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (PD, PD + 8); (AERRNO, AERRNO + 4)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ frm0 fc'
    /\ (forall k : bv 5, bv_unsigned k <> 10 -> bv_unsigned k <> 14 -> bv_unsigned k <> 15 -> reg_get F' k = reg_get F k)
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' PD [C8 (match res with Some bits => Z_to_bv 64 bits | None => djunk end)]
    /\ bytes_at asegs m' T (map (Z_to_bv 8) txt)
    /\ ssp_cells m' canary
    /\ rw_cells asegs m' AERRNO [C4 ev'].

(* [comment removed for export] *)
Definition asscanf_gen_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (T PD : Z) (txt pre post : list Z) (r : Z) (res : option Z) (djunk : word) (lo : Z) (canary ev : word),
    let usp := bv_unsigned sp in
    mem_inv asegs m -> frm0 fc -> ssp_cells m canary -> rw_cells asegs m AERRNO [C4 ev] ->
    tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 T -> a1 = Z_to_bv 64 A_FMT_LG -> a2 = Z_to_bv 64 PD ->
    bytes_at asegs m T (map (Z_to_bv 8) txt) -> Forall (fun c => 0 <= c < 256) txt ->
    txt = pre ++ 0 :: post -> Forall (fun c => is_numch c = true) pre -> (length pre <= 64)%nat ->
    ((T + zlength txt) mod 8 = 0) -> (zlength txt <= 256) ->
    rw_cells asegs m PD [C8 djunk] ->
    scan_sscanf_lg txt = Some (r, res) ->
    stk asegs m lo usp -> alloc_ceiling <= lo -> lo + ASSI_STACK <= usp -> usp + 8 <= 2^47 ->
    (T + zlength txt <= lo \/ usp <= T) -> (PD + 8 <= lo \/ usp <= PD) ->
    (PD + 8 <= T \/ T + zlength txt <= PD) ->
    (4096 <= T) -> (0x5ff000 <= T) -> (T + 2^41 <= 2^63) -> (KHIGHMEM_BEG <= PD) -> (PD + 8 <= 2^63) ->
    (* [comment removed for export] *)
    MRT m -> assi_cells m -> lowsh_at m ->
    app_range T (zlength txt) -> shadow_ok m T (zlength pre + 1) ->
    app_range PD 8 -> shadow_ok m PD 8 ->
    evt asegs (asscanf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F T PD txt r res djunk lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ASSCANF_T) fc None m (seg_rom asegs)).

Theorem asscanf_gen_ok : asscanf_gen_stmt.
Proof.
  unfold asscanf_gen_stmt. intros until ev. cbv zeta.
  intros MI FRM SSP ERR Htp -> -> -> BY BYT Htxt Hpre Hlen AL L256 PDC HS ST CEIL LO U47 SEPT SEPD SEPTD TLO THI T1 HPDK HPD2.
  intros MR AC LOW ART SOT ARP SOP.
  subst tp. unfold ATP.
  pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE. unfold ASSI_STACK in LO.
  pose proof HPDK as HPDKn. unfold KHIGHMEM_BEG, AIMG_HI in HPDKn.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof (app_range_lt47 _ _ ART) as TB. pose proof (app_range_lt47 _ _ ARP) as PB.
  assert (LT : length (map (Z_to_bv 8) txt) = length txt) by apply length_map. unfold zlength in *.
  assert (Hp : (Z.of_nat (length pre) < Z.of_nat (length txt))%Z) by (subst txt; rewrite length_app; cbn; lia).
  unfold AERRNO, ATP in *. change (6148688 - 164)%Z with 6148524%Z in *.
  pose proof (munch_refl [(lo, bv_unsigned sp); (PD, PD + 8); (6148524, 6148524 + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (WAPP : Forall app_iv [(lo, bv_unsigned sp); (PD, PD + 8); (6148524, 6148524 + 4)]%Z).
  { apply Forall_cons; [apply app_iv_stack; lia|]. apply Forall_cons; [right; cbn; exact HPDK|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
  assert (WMRT : Forall mrt_iv_ok [(lo, bv_unsigned sp); (PD, PD + 8); (6148524, 6148524 + 4)]%Z).
  { apply Forall_cons; [apply mrt_iv_ok_stack; lia|]. apply Forall_cons; [apply mrt_iv_ok_high; exact HPDK|]. apply Forall_cons; [apply mrt_iv_ok_mid; lia| apply Forall_nil]. }
  pose proof AC as [[IC RLV] RL]. pose proof IC as IC'. icpt_split IC'.
  unfold ASSCANF_T, A_FMT_LG.
  zstep.                                  (* [comment removed for export] *)
  carve_frame 112%nat ST.
  apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 15 gs.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(bv_unsigned sp - 112 - 16, bv_unsigned sp - 112)] mm) as MU1 end.
  gs. callsp try_init_ok.
  1:{ lazymatch goal with |- icpt_cells ?mm => eapply icpt_cells_munch; [exact IC| exact MU| unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil] end. }
  1:{ assumption. } 1:{ eassumption. } 1:{ exact CEIL. } 1:{ lia. }
  clear MU1.
  gs. gs. gs.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(bv_unsigned sp - 112 - 16, bv_unsigned sp - 112)] mm) as MU1 end.
  gs. callsp try_init_ok.
  1:{ lazymatch goal with |- icpt_cells ?mm => eapply icpt_cells_munch; [exact IC| exact MU| unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil] end. }
  1:{ assumption. } 1:{ eassumption. } 1:{ exact CEIL. } 1:{ lia. }
  clear MU1.
  gsto 0x45f64%Z.
  (* [comment removed for export] *)
  gs.
  (* [comment removed for export] *)
  lazymatch goal with FRc : rw_cells asegs ?mm (bv_unsigned sp + -112) [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10; ?c11; ?c12; ?c13] |- _ =>
    apply (proj1 (rw_cells_app asegs _ _ [c0; c1; c2; c3; c4; c5; c6; c7] _)) in FRc; destruct FRc as [FRa FRbc]; cbn [cells_size csize Nat.add app] in FRbc;
    apply (proj1 (rw_cells_app asegs _ _ [c8] _)) in FRbc; destruct FRbc as [AQC FRc2]; cbn [cells_size csize Nat.add app] in FRc2;
    replace (bv_unsigned sp + -112 + Z.of_nat 64)%Z with (bv_unsigned sp + -48)%Z in AQC by lia;
    replace (bv_unsigned sp + -112 + Z.of_nat 64 + Z.of_nat 8)%Z with (bv_unsigned sp + -40)%Z in FRc2 by lia
  end.
  name_spq (bv_unsigned sp + -112)%Z.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (MR2 : MRT mm) by (eapply MRT_munch; [exact MR| exact MU| exact WMRT]);
    assert (VC2 : vfsi_cells mm) by (eapply vfsi_cells_munch; [exact (proj1 AC)| exact MU| unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil| cbn; lia]);
    assert (LOW2 : lowsh_at mm) by (eapply lowsh_at_munch; [exact LOW| exact MU| exact WM|];
       apply Forall_cons; [cbn [fst snd]; unfold SH, SHADOW_OFFSET, AIMG_HI; lia|];
       apply Forall_cons; [cbn [fst snd]; unfold SH, SHADOW_OFFSET, AIMG_LO, AIMG_HI, KHIGHMEM_BEG in *; lia|];
       apply Forall_cons; [cbn [fst snd]; unfold SH, SHADOW_OFFSET, AIMG_LO; lia| apply Forall_nil]);
    assert (SOT2 : shadow_ok mm T (Z.of_nat (length pre) + 1)) by (eapply shadow_ok_munch_app; [exact SOT| exact MU| lia| eapply app_range_sub; [exact ART| lia| lia| lia]| exact WAPP]);
    assert (SOP2 : shadow_ok mm PD 8) by (eapply shadow_ok_munch_app; [exact SOP| exact MU| lia| exact ARP| exact WAPP]);
    assert (SSP2 : ssp_cells mm canary) by (destruct SSP as [SS1 SS2]; split; (eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn; unfold got_ssp, ssp_guard; lia]))
  end.
  lazymatch goal with STc : stk asegs _ lo (bv_unsigned sp + -112) |- _ => rename STc into ST1 end.
  pose proof avsscanf_proof as VS. unfold avsscanf_stmt, AVSSCANF in VS.
  eapply evt_cut.
  { eapply VS with (T := T) (PD := PD) (txt := txt) (pre := pre) (post := post) (r := r) (res := res) (djunk := djunk) (lo := lo) (canary := canary);
      clear VS; rewrite ?Hsp; rewrite ?unsigned_lit by lia; unfold AVSS_DEPTH, ATP, AERRNO, A_FMT_LG, zlength.
    all: try reflexivity.
    all: try lia.
    all: try eassumption.
    all: try (replace (bv_unsigned sp + -112 + 64) with (bv_unsigned sp + -48) by lia; eassumption).
    all: try (f_equal; lia).
    all: match goal with |- ?G => idtac "VS-REMAINING" G end. }
  cbv beta. intros ms' P. clear VS.
  unfold avsscanf_post in P. rewrite ?Hsp in P.
  (nelim P 31%nat; intros y5 y6 y7 d1 d2 d3 d4 d5 d6 d7 y28 y29 y30 y31 F' fc' m3 ev' -> MUc WMc MI3 FRM' FOK ST3 PDC3 BY3 SSP3 ERR3 AQ3 Hr).
  unfold AERRNO, ATP in *. change (6148688 - 164)%Z with 6148524%Z in *.
  replace (bv_unsigned sp + -112 + 64)%Z with (bv_unsigned sp + -48)%Z in AQ3 by lia.
  assert (MU3 : munch [(lo, bv_unsigned sp); (PD, PD + 8); (6148524, 6148524 + 4)]%Z m m3).
  { lazymatch type of MUc with munch _ ?mm m3 => lazymatch goal with MUp : munch _ m mm |- _ =>
      eapply munch_trans; [exact MUp| eapply munch_weaken; [| exact MUc]; unfold sub_fp; cbn [outside]; intros; lia] end end. }
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m3 MUc WMc; clear MUc WMc end.
  replace (ret_pc (Z_to_bv 64 286568)) with (Z_to_bv 64 286568 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  subst sp0. clear Hsp MR2 VC2 LOW2 SOT2 SOP2 SSP2.
  assert (LOW3 : lowsh_at m3).
  { eapply lowsh_at_munch; [exact LOW| exact MU3| eassumption|].
    all: try (apply Forall_cons; [cbn [fst snd]; unfold SH, SHADOW_OFFSET, AIMG_HI; lia|];
              apply Forall_cons; [cbn [fst snd]; unfold SH, SHADOW_OFFSET, AIMG_LO, AIMG_HI, KHIGHMEM_BEG in *; lia|];
              apply Forall_cons; [cbn [fst snd]; unfold SH, SHADOW_OFFSET, AIMG_LO; lia| apply Forall_nil]). }
  assert (SOP3 : shadow_ok m3 PD 8) by (eapply shadow_ok_munch_app; [exact SOP| exact MU3| lia| exact ARP| exact WAPP]).
  assert (IC3 : icpt_cells m3) by (eapply icpt_cells_munch; [exact IC| exact MU3| unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil]).
  (* [comment removed for export] *)
  assert (TAIL : forall (x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m4,
    munch [(lo, bv_unsigned sp); (PD, PD + 8); (6148524, 6148524 + 4)]%Z m m4 -> wmono asegs m m4 -> mem_inv asegs m4 ->
    stk asegs m4 lo (bv_unsigned sp + -112) ->
    rw_cells asegs m4 (bv_unsigned sp + -112) [CB 8 (firstn 8 junk); C8 (Z_to_bv 64 (bv_unsigned sp + -48)); C8 (Z_to_bv 64 (bv_unsigned sp + -48)); C8 (Z_to_bv 64 (bv_unsigned sp + -48));
                                              C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m4 (bv_unsigned sp + -48) [C8 (Z_to_bv 64 PD)] ->
    rw_cells asegs m4 (bv_unsigned sp + -40) [C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] ->
    rw_cells asegs m4 PD [C8 match res with Some bits => Z_to_bv 64 bits | None => djunk end] ->
    bytes_at asegs m4 T (map (Z_to_bv 8) txt) -> ssp_cells m4 canary -> rw_cells asegs m4 6148524 [C4 ev'] ->
    evt asegs (asscanf_post ra sp gp (Z_to_bv 64 6148688) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F T PD txt r res djunk lo canary m)
      (MS (mkR x5 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 6148688) x6 x7 x9 (Z_to_bv 64 135776) (Z_to_bv 64 r) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (bv_unsigned sp + -48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F' (Z_to_bv 64 0x45f90) fc' None m4 (seg_rom asegs))).
  { intros until m4. intros MU4 WM4 MI4 ST4 FR4 AQ4 FRc4 PDC4 BY4 SSP4 ERR4.
    do 6 gs.
    release_frame FR4 ST4 (bv_unsigned sp + -48).
    release_frame AQ4 ST4 (bv_unsigned sp + -40).
    release_frame FRc4 ST4 (bv_unsigned sp).
    try (replace (bv_unsigned sp + -112 + 112) with (bv_unsigned sp) by lia); try rewrite (Z_to_bv_bv_unsigned sp).
    apply evt_done. unfold asscanf_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU4|]. split; [exact WM4|]. split; [exact MI4|]. split; [exact FRM'|]. split; [exact FOK|].
    split; [exact ST4|]. split; [exact PDC4|]. split; [exact BY4|]. split; [exact SSP4| exact ERR4]. }
  destruct Hr as [-> | Hr0].
  - (* [comment removed for export] *)
    destruct SSP3 as [SS1 SS2]. unfold got_ssp, ssp_guard in SS1, SS2.
    gs. gs.
    do 6 gs.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(bv_unsigned sp - 112 - 2320, bv_unsigned sp - 112)] mm) as MU1 end.
    gs. callsp scommon_lg_ok; [ exact MI3 | exact IC3 | exact LOW3 | exact ST3 | exact CEIL | unfold ASC_STACK; lia | reflexivity | reflexivity | reflexivity
                             | exact AQ3 | lia | lia | exact ARP | exact SOP3 | ].
    clear MU1.
    gs.
    eapply TAIL; try eassumption.
    all: try (split; assumption).
    all: match goal with |- ?G => idtac "TAIL-REMAINING" G end.
  - (* [comment removed for export] *)
    assert (NOSC : evt asegs (asscanf_post ra sp gp (Z_to_bv 64 6148688) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F T PD txt r res djunk lo canary m)
        (MS (mkR (Z_to_bv 64 286568) (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 6148688) y5 y6 y7 (Z_to_bv 64 135776) (Z_to_bv 64 T) (Z_to_bv 64 r) d1 d2 d3 d4 d5 d6 d7
                 (Z_to_bv 64 (bv_unsigned sp + -48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
            F' (Z_to_bv 64 0x45f90) fc' None m3 (seg_rom asegs)) ->
      evt asegs (asscanf_post ra sp gp (Z_to_bv 64 6148688) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F T PD txt r res djunk lo canary m)
        (MS (mkR (Z_to_bv 64 286568) (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 6148688) y5 y6 y7 (Z_to_bv 64 135776) (Z_to_bv 64 T) (Z_to_bv 64 r) d1 d2 d3 d4 d5 d6 d7
                 (Z_to_bv 64 (bv_unsigned sp + -48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
            F' (Z_to_bv 64 286568) fc' None m3 (seg_rom asegs))).
    { intros KK. destruct Hr0 as [-> | ->]; (gs; exact KK). }
    apply NOSC.
    (* [comment removed for export] *)
    do 6 gs.
    lazymatch goal with FR4 : rw_cells asegs m3 (bv_unsigned sp + -112) _, FRc4 : rw_cells asegs m3 (bv_unsigned sp + -40) _ |- _ =>
      release_frame FR4 ST3 (bv_unsigned sp + -48);
      release_frame AQ3 ST3 (bv_unsigned sp + -40);
      release_frame FRc4 ST3 (bv_unsigned sp) end.
    try (replace (bv_unsigned sp + -112 + 112) with (bv_unsigned sp) by lia); try rewrite (Z_to_bv_bv_unsigned sp).
    apply evt_done. unfold asscanf_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU3|]. split; [eassumption|]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
    split; [exact ST3|]. split; [exact PDC3|]. split; [exact BY3|]. split; [exact SSP3| exact ERR3].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem asscanf_lg_ok : asscanf_lg_stmt.
Proof.
  unfold asscanf_lg_stmt. intros until ev. cbv zeta.
  intros FC MR LOW MI FRM SSP ERR Htp Ha0 Ha1 Ha2 BY BYT Htxt Hpre Hlen AL L256 PDC HS ST CEIL LO U47 SEPT SEPD SEPTD TLO THI T1 HPDK HPD2 ART SOT ARP SOP.
  (nelimp FC 8%nat; intros IC CF RVS RLN RLV RSS RFS _).
  pose proof asscanf_gen_ok as SG. unfold asscanf_gen_stmt in SG. cbv zeta in SG.
  unfold asscanf_lg_post.
  eapply SG; clear SG; try eassumption; try reflexivity.
  all: first [ unfold AFMT_STACK in LO; unfold ASSI_STACK; lia
             | exact (conj (conj IC RFS) RSS)
             | match goal with |- ?G => idtac "ALG-REMAINING" G end ].
Qed.


End CeilWrap.
End ICPT_sscanf.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_defs RT_data CJ_iface AShadow ICPT_iface RT_poison RT_poison2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import ICPT_musl F_shgetc_proofs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_scanexp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_scanexp.F_shgetc_proofs3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import SFModel Arr SysStep Image FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim SoftFloat StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScan.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import FloatScan FloatScanProps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScan_nn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_scan_calls.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_scan_calls Shgetc_lemmas FmtFp_facts3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Scan_iface F_shgetc_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_shgetc_proofs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_shgetc_proofs.F_shgetc_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_shgetc_proofs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_shgetc_proofs.F_shgetc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_scanexp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_scanexp.F_rfile.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_str3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_str3.ICPT_str.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import ICPT_pcleaf ICPT_pcdefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_scommon_lg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_scommon_lg.ICPT_vfscanf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import ICPT_scommon_lg F_vsscanf_b.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import ICPT_fmt_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope. Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ICPT_sscanf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_fmt_glue.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_fmt_glue.ICPT_fmt_iface2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import LiaOn.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.

Section CeilWrap.
Context {ACEIL : Ceil}.

Definition asscanf_gen_stmt_b : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (T PD : Z) (txt pre post : list Z) (r : Z) (res : option Z) (djunk : word) (lo : Z) (canary ev : word),
    let usp := bv_unsigned sp in
    mem_inv asegs m -> frm0 fc -> ssp_cells m canary -> rw_cells asegs m AERRNO [C4 ev] ->
    tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 T -> a1 = Z_to_bv 64 A_FMT_LG -> a2 = Z_to_bv 64 PD ->
    bytes_at asegs m T (map (Z_to_bv 8) txt) -> Forall (fun c => 0 <= c < 256) txt ->
    txt = pre ++ 0 :: post -> Forall (fun c => is_numch c = true) pre -> (length pre <= 64)%nat ->
    ((T + zlength txt) mod 8 = 0) -> (zlength txt <= 256) ->
    rw_cells asegs m PD [C8 djunk] ->
    scan_sscanf_lg txt = Some (r, res) ->
    stk asegs m lo usp -> alloc_ceiling <= lo -> lo + ASSI_STACK <= usp -> usp + 8 <= 2^47 ->
    (T + zlength txt <= lo \/ usp <= T) -> (PD + 8 <= lo \/ usp <= PD) ->
    (PD + 8 <= T \/ T + zlength txt <= PD) ->
    (4096 <= T) -> (0x5ff000 <= T) -> (T + 2^41 <= 2^63) -> (AIMG_HI <= PD /\ sclr PD 8) -> (PD + 8 <= 2^63) ->
    (* [comment removed for export] *)
    MRT m -> assi_cells m -> lowsh_at m ->
    app_range T (zlength txt) -> shadow_ok m T (zlength pre + 1) ->
    app_range PD 8 -> shadow_ok m PD 8 ->
    evt asegs (asscanf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F T PD txt r res djunk lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ASSCANF_T) fc None m (seg_rom asegs)).

Theorem asscanf_gen_ok_b : asscanf_gen_stmt_b.
Proof.
  unfold asscanf_gen_stmt_b. intros until ev. cbv zeta.
  intros MI FRM SSP ERR Htp -> -> -> BY BYT Htxt Hpre Hlen AL L256 PDC HS ST CEIL LO U47 SEPT SEPD SEPTD TLO THI T1 HPDK HPD2.
  intros MR AC LOW ART SOT ARP SOP.
  subst tp. unfold ATP.
  pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE. unfold ASSI_STACK in LO.
  pose proof HPDK as HPDKn. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in HPDKn.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof (app_range_lt47 _ _ ART) as TB. pose proof (app_range_lt47 _ _ ARP) as PB.
  assert (LT : length (map (Z_to_bv 8) txt) = length txt) by apply length_map. unfold zlength in *.
  assert (Hp : (Z.of_nat (length pre) < Z.of_nat (length txt))%Z) by (subst txt; rewrite length_app; cbn; lia).
  unfold AERRNO, ATP in *. change (6148688 - 164)%Z with 6148524%Z in *.
  pose proof (munch_refl [(lo, bv_unsigned sp); (PD, PD + 8); (6148524, 6148524 + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (WAPP : Forall app_iv [(lo, bv_unsigned sp); (PD, PD + 8); (6148524, 6148524 + 4)]%Z).
  { apply Forall_cons; [apply app_iv_stack; lia|]. apply Forall_cons; [destruct HPDKn as [_ [Hl|Hh]]; [left; cbn; lia| right; cbn; unfold KHIGHMEM_BEG; lia]|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
  assert (WMRT : Forall mrt_iv_ok [(lo, bv_unsigned sp); (PD, PD + 8); (6148524, 6148524 + 4)]%Z).
  { apply Forall_cons; [apply mrt_iv_ok_stack; lia|]. apply Forall_cons; [destruct HPDKn as [Hlo [Hl|Hh]]; [apply mrt_iv_ok_mid; lia| apply mrt_iv_ok_high; unfold KHIGHMEM_BEG; lia]|]. apply Forall_cons; [apply mrt_iv_ok_mid; lia| apply Forall_nil]. }
  pose proof AC as [[IC RLV] RL]. pose proof IC as IC'. icpt_split IC'.
  unfold ASSCANF_T, A_FMT_LG.
  zstep.                                  (* [comment removed for export] *)
  carve_frame 112%nat ST.
  apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  sepM. do 15 gs.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(bv_unsigned sp - 112 - 16, bv_unsigned sp - 112)] mm) as MU1 end.
  gs. sepM. callsp try_init_ok.
  1:{ lazymatch goal with |- icpt_cells ?mm => eapply icpt_cells_munch; [exact IC| exact MU| unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; (lia_on CE HPDKn)|]); apply Forall_nil] end. }
  1:{ assumption. } 1:{ eassumption. } 1:{ exact CEIL. } 1:{ lia. }
  clear MU1.
  gs. gs. sepM. gs.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(bv_unsigned sp - 112 - 16, bv_unsigned sp - 112)] mm) as MU1 end.
  gs. sepM. callsp try_init_ok.
  1:{ lazymatch goal with |- icpt_cells ?mm => eapply icpt_cells_munch; [exact IC| exact MU| unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; (lia_on CE HPDKn)|]); apply Forall_nil] end. }
  1:{ assumption. } 1:{ eassumption. } 1:{ exact CEIL. } 1:{ lia. }
  clear MU1.
  sepM. gsto 0x45f64%Z.
  (* [comment removed for export] *)
  gs.
  (* [comment removed for export] *)
  lazymatch goal with FRc : rw_cells asegs ?mm (bv_unsigned sp + -112) [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10; ?c11; ?c12; ?c13] |- _ =>
    apply (proj1 (rw_cells_app asegs _ _ [c0; c1; c2; c3; c4; c5; c6; c7] _)) in FRc; destruct FRc as [FRa FRbc]; cbn [cells_size csize Nat.add app] in FRbc;
    apply (proj1 (rw_cells_app asegs _ _ [c8] _)) in FRbc; destruct FRbc as [AQC FRc2]; cbn [cells_size csize Nat.add app] in FRc2;
    replace (bv_unsigned sp + -112 + Z.of_nat 64)%Z with (bv_unsigned sp + -48)%Z in AQC by lia;
    replace (bv_unsigned sp + -112 + Z.of_nat 64 + Z.of_nat 8)%Z with (bv_unsigned sp + -40)%Z in FRc2 by lia
  end.
  name_spq (bv_unsigned sp + -112)%Z.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (MR2 : MRT mm) by (eapply MRT_munch; [exact MR| exact MU| exact WMRT]);
    assert (VC2 : vfsi_cells mm) by (eapply vfsi_cells_munch; [exact (proj1 AC)| exact MU| unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; (lia_on CE HPDKn)|]); apply Forall_nil| cbn; lia]);
    assert (LOW2 : lowsh_at mm) by (eapply lowsh_at_munch; [exact LOW| exact MU| exact WM|];
       apply Forall_cons; [cbn [fst snd]; unfold SH, SHADOW_OFFSET, AIMG_HI; lia|];
       apply Forall_cons; [cbn [fst snd]; unfold SH, SHADOW_OFFSET, AIMG_LO, AIMG_HI, KHIGHMEM_BEG in *; lia|];
       apply Forall_cons; [cbn [fst snd]; unfold SH, SHADOW_OFFSET, AIMG_LO; lia| apply Forall_nil]);
    assert (SOT2 : shadow_ok mm T (Z.of_nat (length pre) + 1)) by (eapply shadow_ok_munch_app; [exact SOT| exact MU| lia| eapply app_range_sub; [exact ART| lia| lia| lia]| exact WAPP]);
    assert (SOP2 : shadow_ok mm PD 8) by (eapply shadow_ok_munch_app; [exact SOP| exact MU| lia| exact ARP| exact WAPP]);
    assert (SSP2 : ssp_cells mm canary) by (destruct SSP as [SS1 SS2]; split; (eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn; unfold got_ssp, ssp_guard; (lia_on CE HPDKn)]))
  end.
  lazymatch goal with STc : stk asegs _ lo (bv_unsigned sp + -112) |- _ => rename STc into ST1 end.
  pose proof avsscanf_proof as VS. unfold avsscanf_stmt, AVSSCANF in VS.
  eapply evt_cut.
  { eapply VS with (T := T) (PD := PD) (txt := txt) (pre := pre) (post := post) (r := r) (res := res) (djunk := djunk) (lo := lo) (canary := canary);
      clear VS; rewrite ?Hsp; rewrite ?unsigned_lit by lia; unfold AVSS_DEPTH, ATP, AERRNO, A_FMT_LG, zlength.
    all: try reflexivity.
    all: try (cut_to Hlen AL THI L256 CEIL LO U47 SEPT SEPD SEPTD TLO T1 HPD2; (cut_to Hlen AL THI L256 CEIL LO U47 SEPT SEPD SEPTD TLO T1 HPD2; lia)).
    all: try eassumption.
    all: try (replace (bv_unsigned sp + -112 + 64) with (bv_unsigned sp + -48) by lia; eassumption).
    all: try (f_equal; lia).
    all: match goal with |- ?G => idtac "VS-REMAINING" G end. }
  cbv beta. intros ms' P. clear VS.
  unfold avsscanf_post in P. rewrite ?Hsp in P.
  (nelim P 31%nat; intros y5 y6 y7 d1 d2 d3 d4 d5 d6 d7 y28 y29 y30 y31 F' fc' m3 ev' -> MUc WMc MI3 FRM' FOK ST3 PDC3 BY3 SSP3 ERR3 AQ3 Hr).
  unfold AERRNO, ATP in *. change (6148688 - 164)%Z with 6148524%Z in *.
  replace (bv_unsigned sp + -112 + 64)%Z with (bv_unsigned sp + -48)%Z in AQ3 by lia.
  assert (MU3 : munch [(lo, bv_unsigned sp); (PD, PD + 8); (6148524, 6148524 + 4)]%Z m m3).
  { lazymatch type of MUc with munch _ ?mm m3 => lazymatch goal with MUp : munch _ m mm |- _ =>
      eapply munch_trans; [exact MUp| eapply munch_weaken; [| exact MUc]; unfold sub_fp; cbn [outside]; intros; lia] end end. }
  sepM. lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m3 MUc WMc; clear MUc WMc end.
  replace (ret_pc (Z_to_bv 64 286568)) with (Z_to_bv 64 286568 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  subst sp0. clear Hsp MR2 VC2 LOW2 SOT2 SOP2 SSP2.
  assert (LOW3 : lowsh_at m3).
  { eapply lowsh_at_munch; [exact LOW| exact MU3| eassumption|].
    all: try (apply Forall_cons; [cbn [fst snd]; unfold SH, SHADOW_OFFSET, AIMG_HI; lia|];
              apply Forall_cons; [cbn [fst snd]; unfold SH, SHADOW_OFFSET, AIMG_LO, AIMG_HI, KHIGHMEM_BEG in *; lia|];
              apply Forall_cons; [cbn [fst snd]; unfold SH, SHADOW_OFFSET, AIMG_LO; lia| apply Forall_nil]). }
  assert (SOP3 : shadow_ok m3 PD 8) by (eapply shadow_ok_munch_app; [exact SOP| exact MU3| lia| exact ARP| exact WAPP]).
  assert (IC3 : icpt_cells m3) by (eapply icpt_cells_munch; [exact IC| exact MU3| unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; (lia_on CE HPDKn)|]); apply Forall_nil]).
  (* [comment removed for export] *)
  assert (TAIL : forall (x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m4,
    munch [(lo, bv_unsigned sp); (PD, PD + 8); (6148524, 6148524 + 4)]%Z m m4 -> wmono asegs m m4 -> mem_inv asegs m4 ->
    stk asegs m4 lo (bv_unsigned sp + -112) ->
    rw_cells asegs m4 (bv_unsigned sp + -112) [CB 8 (firstn 8 junk); C8 (Z_to_bv 64 (bv_unsigned sp + -48)); C8 (Z_to_bv 64 (bv_unsigned sp + -48)); C8 (Z_to_bv 64 (bv_unsigned sp + -48));
                                              C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m4 (bv_unsigned sp + -48) [C8 (Z_to_bv 64 PD)] ->
    rw_cells asegs m4 (bv_unsigned sp + -40) [C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] ->
    rw_cells asegs m4 PD [C8 match res with Some bits => Z_to_bv 64 bits | None => djunk end] ->
    bytes_at asegs m4 T (map (Z_to_bv 8) txt) -> ssp_cells m4 canary -> rw_cells asegs m4 6148524 [C4 ev'] ->
    evt asegs (asscanf_post ra sp gp (Z_to_bv 64 6148688) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F T PD txt r res djunk lo canary m)
      (MS (mkR x5 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 6148688) x6 x7 x9 (Z_to_bv 64 135776) (Z_to_bv 64 r) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (bv_unsigned sp + -48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F' (Z_to_bv 64 0x45f90) fc' None m4 (seg_rom asegs))).
  { intros until m4. intros MU4 WM4 MI4 ST4 FR4 AQ4 FRc4 PDC4 BY4 SSP4 ERR4.
    do 6 gs.
    release_frame FR4 ST4 (bv_unsigned sp + -48).
    release_frame AQ4 ST4 (bv_unsigned sp + -40).
    release_frame FRc4 ST4 (bv_unsigned sp).
    try (replace (bv_unsigned sp + -112 + 112) with (bv_unsigned sp) by lia); try rewrite (Z_to_bv_bv_unsigned sp).
    apply evt_done. unfold asscanf_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU4|]. split; [exact WM4|]. split; [exact MI4|]. split; [exact FRM'|]. split; [exact FOK|].
    split; [exact ST4|]. split; [exact PDC4|]. split; [exact BY4|]. split; [exact SSP4| exact ERR4]. }
  destruct Hr as [-> | Hr0].
  - (* [comment removed for export] *)
    destruct SSP3 as [SS1 SS2]. unfold got_ssp, ssp_guard in SS1, SS2.
    gs. gs.
    do 6 gs.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(bv_unsigned sp - 112 - 2320, bv_unsigned sp - 112)] mm) as MU1 end.
    gs. sepM. callsp scommon_lg_ok; [ exact MI3 | exact IC3 | exact LOW3 | exact ST3 | exact CEIL | unfold ASC_STACK; lia | reflexivity | reflexivity | reflexivity
                             | exact AQ3 | lia | lia | exact ARP | exact SOP3 | ].
    clear MU1.
    gs.
    eapply TAIL; try eassumption.
    all: try (split; assumption).
    all: match goal with |- ?G => idtac "TAIL-REMAINING" G end.
  - (* [comment removed for export] *)
    assert (NOSC : evt asegs (asscanf_post ra sp gp (Z_to_bv 64 6148688) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F T PD txt r res djunk lo canary m)
        (MS (mkR (Z_to_bv 64 286568) (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 6148688) y5 y6 y7 (Z_to_bv 64 135776) (Z_to_bv 64 T) (Z_to_bv 64 r) d1 d2 d3 d4 d5 d6 d7
                 (Z_to_bv 64 (bv_unsigned sp + -48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
            F' (Z_to_bv 64 0x45f90) fc' None m3 (seg_rom asegs)) ->
      evt asegs (asscanf_post ra sp gp (Z_to_bv 64 6148688) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F T PD txt r res djunk lo canary m)
        (MS (mkR (Z_to_bv 64 286568) (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 6148688) y5 y6 y7 (Z_to_bv 64 135776) (Z_to_bv 64 T) (Z_to_bv 64 r) d1 d2 d3 d4 d5 d6 d7
                 (Z_to_bv 64 (bv_unsigned sp + -48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
            F' (Z_to_bv 64 286568) fc' None m3 (seg_rom asegs))).
    { intros KK. destruct Hr0 as [-> | ->]; (gs; exact KK). }
    apply NOSC.
    (* [comment removed for export] *)
    do 6 gs.
    lazymatch goal with FR4 : rw_cells asegs m3 (bv_unsigned sp + -112) _, FRc4 : rw_cells asegs m3 (bv_unsigned sp + -40) _ |- _ =>
      release_frame FR4 ST3 (bv_unsigned sp + -48);
      release_frame AQ3 ST3 (bv_unsigned sp + -40);
      release_frame FRc4 ST3 (bv_unsigned sp) end.
    try (replace (bv_unsigned sp + -112 + 112) with (bv_unsigned sp) by lia); try rewrite (Z_to_bv_bv_unsigned sp).
    apply evt_done. unfold asscanf_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU3|]. split; [eassumption|]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
    split; [exact ST3|]. split; [exact PDC3|]. split; [exact BY3|]. split; [exact SSP3| exact ERR3].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem asscanf_lg_ok_b : asscanf_lg_stmt_b.
Proof.
  unfold asscanf_lg_stmt_b. intros until ev. cbv zeta.
  intros FC MR LOW MI FRM SSP ERR Htp Ha0 Ha1 Ha2 BY BYT Htxt Hpre Hlen AL L256 PDC HS ST CEIL LO U47 SEPT SEPD SEPTD TLO THI T1 HPDK HPD2 ART SOT ARP SOP.
  (nelimp FC 8%nat; intros IC CF RVS RLN RLV RSS RFS _).
  pose proof asscanf_gen_ok_b as SG. unfold asscanf_gen_stmt_b in SG. cbv zeta in SG.
  unfold asscanf_lg_post.
  eapply SG; clear SG; try eassumption; try reflexivity.
  all: first [ unfold AFMT_STACK in LO; unfold ASSI_STACK; lia
             | exact (conj (conj IC RFS) RSS)
             | match goal with |- ?G => idtac "ALG-REMAINING" G end ].
Qed.

End CeilWrap.
