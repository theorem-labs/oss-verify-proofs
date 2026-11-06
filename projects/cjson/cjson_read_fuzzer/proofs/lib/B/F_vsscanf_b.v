(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_defs RT_data CJ_iface AShadow ICPT_iface RT_poison RT_poison2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.SO_shadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import ICPT_musl F_shgetc_proofs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_scanexp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_scanexp.F_shgetc_proofs3.
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_scan_calls Shgetc_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import Scan_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import F_memset F_memcpy F_memchr F_fmt_fp_lib F_trunctfdf2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_frexpl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_frexpl.F_fmt_fp_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import F_shgetc_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_shgetc_proofs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_shgetc_proofs.F_shgetc_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_shgetc_proofs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_shgetc_proofs.F_shgetc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_scanexp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_scanexp.F_rscan_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_scanexp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_scanexp.F_rfile.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import F_rscan_shape.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import FmtFp_facts3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_rscan_model.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model.F_rscan_facts.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_rscan_model.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_floatscan F_vfscanf_b_c1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg ICPT_pcleaf ICPT_pcdefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_scommon_lg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_scommon_lg.ICPT_vfscanf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import ICPT_scommon_lg.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import LiaOn.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac br K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); try (exfalso; lia).
Tactic Notation "callx" tactic3(tac) := callw tac; try (lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end).

Definition AVSSCANF : Z := 0x9a2a0.
Definition AVSS_DEPTH : Z := 11840.     (* [comment removed for export] *)

Definition avsscanf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (T PD AQ : Z) (txt : list Z) (r : Z) (res : option Z) (djunk : word) (lo : Z) (canary : word) (m : word -> option byte)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte) (ev' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom bsegs)
    /\ munch [(lo, bv_unsigned sp); (PD, PD + 8); (AERRNO, AERRNO + 4)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ frm0 fc'
    /\ (forall k : bv 5, bv_unsigned k <> 10%Z -> bv_unsigned k <> 14%Z -> bv_unsigned k <> 15%Z -> reg_get F' k = reg_get F k)
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' PD [C8 (match res with Some bits => Z_to_bv 64 bits | None => djunk end)]
    /\ bytes_at bsegs m' T (map (Z_to_bv 8) txt)
    /\ ssp_cells m' canary
    /\ rw_cells bsegs m' AERRNO [C4 ev']
    /\ rw_cells bsegs m' AQ [C8 (Z_to_bv 64 PD)]
    /\ (r = 1 \/ r = 0 \/ r = -1)%Z.

(* [comment removed for export] *)
Definition avsscanf_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (T PD : Z) (txt pre post : list Z) (r : Z) (res : option Z) (djunk : word) (lo : Z) (canary ev : word),
    let usp := bv_unsigned sp in let AQ := (usp + 64)%Z in
    mem_inv bsegs m -> frm0 fc -> ssp_cells m canary -> rw_cells bsegs m AERRNO [C4 ev] ->
    tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 T -> a1 = Z_to_bv 64 A_FMT_LG -> a2 = Z_to_bv 64 AQ ->
    bytes_at bsegs m T (map (Z_to_bv 8) txt) -> Forall (fun c => 0 <= c < 256)%Z txt ->
    txt = pre ++ 0%Z :: post -> Forall (fun c => is_numch c = true) pre -> (length pre <= 64)%nat ->
    ((T + zlength txt) mod 8 = 0)%Z -> (zlength txt <= 256)%Z ->
    rw_cells bsegs m AQ [C8 (Z_to_bv 64 PD)] -> rw_cells bsegs m PD [C8 djunk] ->
    scan_sscanf_lg txt = Some (r, res) ->
    stk bsegs m lo usp -> (alloc_ceiling <= lo)%Z -> (lo + AVSS_DEPTH <= usp)%Z -> (usp + 80 <= 2^47)%Z ->
    (T + zlength txt <= lo \/ usp + 72 <= T)%Z -> (PD + 8 <= lo \/ usp + 72 <= PD)%Z ->
    (PD + 8 <= T \/ T + zlength txt <= PD)%Z ->
    (4096 <= T)%Z -> (0x5ff000 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (AIMG_HI <= PD /\ sclr PD 8)%Z -> (PD + 8 <= 2^63)%Z ->
    (* [comment removed for export] *)
    MRT m -> vfsi_cells m -> lowsh_at m ->
    app_range T (zlength txt) -> shadow_ok m T (zlength pre + 1) ->
    app_range PD 8 -> shadow_ok m PD 8 ->
    evt bsegs (avsscanf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F T PD AQ txt r res djunk lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AVSSCANF) fc None m (seg_rom bsegs)).

Theorem avsscanf_proof : avsscanf_stmt.
Proof.
  unfold avsscanf_stmt. intros until ev. cbv zeta.
  intros MI FRM [SSP1 SSP2] ERR Htp -> -> -> BY BYT Htxt Hpre Hlen AL L256 AQC PDC HS ST CEIL LO U47 SEPT SEPD SEPTD TLO THI T1 HPDK HPD2.
  intros MR VC LOW ART SOT ARP SOP.
  pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE. unfold AVSS_DEPTH in LO.
  pose proof HPDK as HPDKn. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in HPDKn.
  unfold AERRNO, ATP in *. change (6146416 - 164)%Z with 6146252%Z in *. unfold got_ssp, ssp_guard in SSP1, SSP2.
  subst tp.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof AINTRIN_STACK_val as AIS.
  assert (LT : length (map (Z_to_bv 8) txt) = length txt) by apply length_map.
  assert (Hp : (0 <= zlength pre < zlength txt)%Z) by (subst txt; unfold zlength; rewrite length_app; cbn; lia).
  unfold zlength in L256, SEPT, SEPTD, AL, Hp, ART, SOT. unfold zlength.
  pose proof (app_range_lt47 _ _ ART) as TB. pose proof (app_range_lt47 _ _ ARP) as PB.
  pose proof (munch_refl [(lo, bv_unsigned sp); (PD, PD + 8); (6146252, 6146252 + 4)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (WAPP : Forall app_iv [(lo, bv_unsigned sp); (PD, PD + 8); (6146252, 6146252 + 4)]%Z).
  { apply Forall_cons; [apply app_iv_stack; lia|]. apply Forall_cons; [destruct HPDKn as [_ [Hl|Hh]]; [left; cbn; lia| right; cbn; unfold KHIGHMEM_BEG; lia]|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
  assert (WMRT : Forall mrt_iv_ok [(lo, bv_unsigned sp); (PD, PD + 8); (6146252, 6146252 + 4)]%Z).
  { apply Forall_cons; [apply mrt_iv_ok_stack; lia|]. apply Forall_cons; [destruct HPDKn as [Hlo [Hl|Hh]]; [apply mrt_iv_ok_mid; lia| apply mrt_iv_ok_high; unfold KHIGHMEM_BEG; lia]|]. apply Forall_cons; [apply mrt_iv_ok_mid; lia| apply Forall_nil]. }
  pose proof (rw_cells_bound _ _ _ _ PDC) as BPD. cbn [cells_size csize Nat.add] in BPD.
  pose proof VC as [IC RLV]. pose proof IC as IC'. icpt_split IC'.
  unfold AVSSCANF, A_FMT_LG.
  (* [comment removed for export] *)
  zs. carve_frame 48%nat ST. rename FR into FRV.
  carve_frame 232%nat ST. rename FR into FILE.
  destruct (stk_split _ _ _ (bv_unsigned sp + -288)%Z _ ST ltac:(lia)) as [ST8 STJ]. clear ST. rename ST8 into ST.
  sepM. do 8 zs.
  zs. zs. zs. zs.
  zs. zs. zs.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (MR1 : MRT mm) by (eapply MRT_munch; [exact MR| exact MU| exact WMRT]);
    assert (SOF : shadow_ok mm (bv_unsigned sp + -280) 232) by ((nelim MR1 3%nat; intros _ SZ _); apply (stack_shadow_zero_shadow_ok _ _ _ SZ); lia)
  end.
  zs. sepM. callx (eapply memset_icpt_callZ with (lo := lo);
    [ exact FILE | assumption | lia | lia | lia | lia
    | exact (MRT_icpt _ MR1) | exact ST | exact CEIL | lia
    | lia | right; unfold highmem_range, KHIGHMEM_BEG, KHIGHMEM_END in *; lia | apply wr_range_ok_high; lia | intros _; exact SOF | lia ]).
  clear MR1 SOF.
  match goal with H : rw_cells _ _ _ [CB (Z.to_nat 232) _] |- _ =>
    change (Z.to_nat 232) with 232%nat in H; rewrite (unsigned_lit 0) in H by lia; change (0 mod 256)%Z with 0%Z in H;
    apply file_cells_zero in H; rename H into FC end.
  (* [comment removed for export] *)
  zs. zs. zs. zs. zs. zs. zs.
  replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 M64) in FC by (apply Z_to_bv_eqm; reflexivity).
  change (repeat (Z_to_bv 8 0) 4) with zero4 in FC.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (FCv : rw_cells bsegs mm (bv_unsigned sp + -336 + 56) (ss_cells T 0 0 w0 T 0 w0 w0))
      by (unfold ss_cells, w0; unfold STRING_READ; replace (bv_unsigned sp + -336 + 56)%Z with (bv_unsigned sp + -280)%Z by lia; exact FC) end.
  clear FC.
  (* [comment removed for export] *)
  zs. zs. zs. zs. zs.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (VC1 : vfsi_cells mm) by (eapply vfsi_cells_munch; [exact VC| exact MU| unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; (lia_on CE HPDKn)|]); apply Forall_nil| cbn; lia]) end.
  name_spq (bv_unsigned sp + -288)%Z.
  eapply vfscanf_icpt_prefix with (lo := lo) (AQ := (bv_unsigned sp + 64)%Z).
  all: lazymatch goal with
       | |- mem_inv _ _ => assumption
       | |- vfsi_cells _ => exact VC1
       | |- stk _ _ _ _ => rewrite Hsp; exact ST
       | |- (alloc_ceiling <= _)%Z => exact CEIL
       | |- (_ + AVFSI_STACK <= _)%Z => rewrite Hsp; unfold AVFSI_STACK; lia
       | |- _ /\ _ => rewrite Hsp; lia
       | |- _ => idtac
       end.
  rewrite ?Hsp. clear VC1.
  intros t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' mv MUv0 WMv0 MIv VC2 STv FRI.
  replace (bv_unsigned sp + -288 + -48)%Z with (bv_unsigned sp + -336)%Z in * by lia.
  (* [comment removed for export] *)
  lazymatch type of MUv0 with munch _ ?mm mv =>
    assert (MU2 : munch [(lo, bv_unsigned sp); (PD, PD + 8); (6146252, 6146252 + 4)]%Z m mv)
      by (eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MUv0]; unfold sub_fp; cbn [outside]; intros; lia]);
    assert (WM2 : wmono bsegs m mv) by (eapply wmono_trans; [exact WM| exact WMv0]);
    transport_after_call bsegs mm mv MUv0 WMv0
  end.
  clear MUv0 WMv0.
  (* [comment removed for export] *)
  destruct (stk_split _ _ _ (bv_unsigned sp + -336 - 11440)%Z _ STv ltac:(lia)) as [STlo SThi]. clear STv.
  assert (MR2 : MRT mv) by (eapply MRT_munch; [exact MR| exact MU2| exact WMRT]).
  assert (SOT2 : shadow_ok mv T (Z.of_nat (length pre) + 1)) by (eapply shadow_ok_munch_app; [exact SOT| exact MU2| lia| eapply app_range_sub; [exact ART| lia| lia| lia]| exact WAPP]).
  assert (AXV : scan_ax mv (bv_unsigned sp + -336) F_vfscanf_b_c1.VF_DEPTH (bv_unsigned sp + -336 + 56) T txt (zlength pre)).
  { unfold scan_ax, F_vfscanf_b_c1.VF_DEPTH, zlength, alloc_ceiling, sp_window_lo, stack_max_size. split; [exact MR2| split; [lia| split; [lia| split; [exact ART| exact SOT2]]]]. }
  replace (Z_to_bv 64 (bv_unsigned sp + -280)) with (Z_to_bv 64 (bv_unsigned sp + -336 + 56) : word) by (f_equal; lia).
  replace (Z_to_bv 64 (bv_unsigned sp + 64)) with (Z_to_bv 64 (bv_unsigned sp + -336 + 400) : word) by (f_equal; lia).
  replace (bv_unsigned sp + 64)%Z with (bv_unsigned sp + -336 + 400)%Z in AQC by lia.
  unfold AVFSCANF_RET, A_REAL_VFSCANF.
  epose proof (F_vfscanf_b_c1.L_VA (Z_to_bv 64 0x45ebc) (bv_unsigned sp + -336)%Z gp _ _ _ (Z_to_bv 64 6277552) s4 s5 s6 s7 s8 s9 s10 s11 F fc mv
                T txt pre post canary PD djunk r res HS Htxt Hpre BYT Hlen ltac:(unfold zlength; lia) ltac:(unfold zlength; lia)
                ltac:(unfold zlength; lia) T1
                ltac:(unfold F_vfscanf_b_c1.VF_DEPTH; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold zlength; lia) FRM
                AXV HPDKn TLO THI) as LV.
  cbv zeta in LV. unfold F_vfscanf_b_c1.vf_post, F_vfscanf_b_c1.Wvf, F_vfscanf_b_c1.VF_DEPTH, F_vfscanf_b_c1.FokR, F_vfscanf_b_c1.resw, F_floatscan_common.RERRNO, F_floatscan_common.RATP, F_vfscanf_b_c1.VFSCANF, F_vfscanf_b_c1.RFMT in LV.
  sepM. callx (eapply LV; [ exact SThi | exact MIv | exact FCv | exact AQC | exact PDC | exact BY | split; [exact SSP1 | exact SSP2] | exact ERR ]).
  clear LV.
  rename PC0 into FJ. rename PC1 into PDR. rename PC2 into BY2. rename PC3 into SSP3. rename PC4 into ERR2. rename PC5 into FOK.
  rename POST into FRM2. rename MI into MI2.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mV end.
  lazymatch goal with H : stk bsegs mV (bv_unsigned sp + -336 - 11440) (bv_unsigned sp + -336) |- _ =>
    pose proof (stk_merge _ _ _ _ _ STlo H ltac:(lia)) as ST2; clear STlo H end.
  replace (bv_unsigned sp + -336 + 400)%Z with (bv_unsigned sp + 64)%Z in AQC by lia.
  (* [comment removed for export] *)
  assert (Hr : (r = 1 \/ r = 0 \/ r = -1)%Z).
  { pose proof (ss_model txt (zlength pre) BYT ltac:(unfold zlength; lia) ltac:(subst txt; apply znth_app_mid)
      ltac:(intros i Hi; subst txt; rewrite znth_app_pre by exact Hi; exact (proj1 (Forall_forall _ _) Hpre _ (znth_In' pre i Hi))) r res HS) as HSM.
    cbv zeta in HSM. destruct HSM as [(_ & -> & _) | (_ & fR & yR & _ & _ & [(_ & -> & _) | (_ & -> & _)])]; lia. }
  assert (VC3 : vfsi_cells mV) by (eapply vfsi_cells_munch; [exact VC| exact MU2| unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; (lia_on CE HPDKn)|]); apply Forall_nil| cbn; lia]).
  assert (LOW3 : lowsh_at mV).
  { eapply lowsh_at_munch; [exact LOW| exact MU2| exact WM2|].
    apply Forall_cons; [cbn [fst snd]; unfold SH, SHADOW_OFFSET, AIMG_HI; (lia_on CE)|].
    apply Forall_cons; [cbn [fst snd]; unfold SH, SHADOW_OFFSET, AIMG_LO, AIMG_HI; lia|].
    apply Forall_cons; [cbn [fst snd]; unfold SH, SHADOW_OFFSET, AIMG_LO; lia| apply Forall_nil]. }
  assert (SOP3 : shadow_ok mV PD 8) by (eapply shadow_ok_munch_app; [exact SOP| exact MU2| lia| exact ARP| exact WAPP]).
  (* [comment removed for export] *)
  pose proof (zbytes_length txt) as LTZ.
  replace (bv_unsigned sp + -336)%Z with (bv_unsigned sp0 + -48)%Z in ST2, FRI |- * by lia.
  replace (Z_to_bv 64 (bv_unsigned sp + -336 + 400) : word) with (Z_to_bv 64 (bv_unsigned sp + 64) : word) by (f_equal; lia).
  unfold A_FMT_LG.
  eapply vfscanf_icpt_epilogue with (sp := sp0) (lo := lo) (AQ := (bv_unsigned sp + 64)%Z) (PD := PD) (r := r).
  all: lazymatch goal with
       | |- (alloc_ceiling <= _)%Z => exact CEIL
       | |- (_ + AVFSI_STACK <= _)%Z => rewrite Hsp; unfold AVFSI_STACK; lia
       | |- (_ <= _ /\ _)%Z => rewrite Hsp; lia
       | |- scommon_lg_stmt => exact scommon_lg_ok
       | |- (_ = 1 \/ _)%Z => exact Hr
       | |- mem_inv _ _ => exact MI2
       | |- vfsi_cells _ => exact VC3
       | |- lowsh_at _ => exact LOW3
       | |- stk _ _ _ _ => exact ST2
       | |- rw_cells _ _ _ _ => first [exact FRI | exact AQC]
       | |- (_ = 1%Z -> _) => intros _; split; [exact ARP | exact SOP3]
       | |- _ => idtac
       end.
  (* [comment removed for export] *)
  intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m3 MU4 WM4 MI3 ST4 AQ4.
  rewrite ?Hsp in *. 
  assert (MU5 : munch [(lo, bv_unsigned sp); (PD, PD + 8); (6146252, 6146252 + 4)]%Z m m3)
    by (eapply munch_trans; [exact MU2| eapply munch_weaken; [| exact MU4]; unfold sub_fp; cbn [outside]; intros; lia]).
  assert (WM5 : wmono bsegs m m3) by (eapply wmono_trans; [exact WM2| exact WM4]).
  destruct SSP3 as [SSP5 SSP6]. unfold got_ssp, ssp_guard in SSP5, SSP6.
  sepM. transport_after_call bsegs mV m3 MU4 WM4. clear MU4 WM4.
  subst sp0. clear Hsp.
  replace (ret_pc (Z_to_bv 64 631568)) with (Z_to_bv 64 631568 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  zs. zs. zs. br K1.
  zs. zs. zs. zs. zs. zs. zs.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m4 _) =>
    lazymatch goal with ST6 : stk bsegs m4 lo (bv_unsigned sp + -288)%Z, STJ6 : stk bsegs m4 (bv_unsigned sp + -288)%Z (bv_unsigned sp + -280)%Z,
                        FRV6 : rw_cells bsegs m4 (bv_unsigned sp + -48)%Z _, FJ6 : rw_cells bsegs m4 (bv_unsigned sp + -336 + 56)%Z _ |- _ =>
      replace (bv_unsigned sp + -336 + 56)%Z with (bv_unsigned sp + -280)%Z in FJ6 by lia;
      pose proof (stk_merge _ _ _ _ _ ST6 STJ6 ltac:(lia)) as ST7; clear ST6 STJ6;
      release_frame FJ6 ST7 (bv_unsigned sp + -48)%Z;
      release_frame FRV6 ST7 (bv_unsigned sp)
    end end.
  apply evt_done. unfold avsscanf_post.
  repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|].
  split; [exact MU5|]. split; [exact WM5|]. split; [assumption|]. split; [assumption|]. split; [exact FOK|].
  split; [assumption|]. split; [exact PDR|]. split; [exact BY2|]. split; [split; [exact SSP5| exact SSP6]|]. split; [exact ERR2|]. split; [exact AQ4| exact Hr].
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac br K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); try (exfalso; lia).
Tactic Notation "callx" tactic3(tac) := callw tac; try (lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end).
