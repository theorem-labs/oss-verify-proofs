(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim Monad Stdio Driver AsanCtrl AsanEmbed ProgA AsanProgDeps.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import Printf_model Printf_mlib Printf_pieces Printf_fmts F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import Shadow ITreeA SysStepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg RtCells Stdio_kit Stdio_kit2 F_syscalls StdioFiles MonadF MonadF2 Strnlen_iface
     F_printf_iface F_fwritex_stdout F_vfprintf F_vfprintf_stdout I_printf_formats I_printf_icpt AProto AMalloc_iface AProg_kit ADriver_iface.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
(* [comment removed for export] *)
Ltac is_zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac lit_frames :=
  repeat match goal with
  | H : context [(bv_unsigned ?sp + ?a - ?b)%Z] |- _ =>
      is_zlit a; is_zlit b; let v := eval vm_compute in (a - b)%Z in replace (bv_unsigned sp + a - b)%Z with (bv_unsigned sp + v)%Z in H by lia
  | |- context [(bv_unsigned ?sp + ?a - ?b)%Z] =>
      is_zlit a; is_zlit b; let v := eval vm_compute in (a - b)%Z in replace (bv_unsigned sp + a - b)%Z with (bv_unsigned sp + v)%Z by lia
  | H : context [(bv_unsigned ?sp + ?a + ?b)%Z] |- _ =>
      is_zlit a; is_zlit b; let v := eval vm_compute in (a + b)%Z in replace (bv_unsigned sp + a + b)%Z with (bv_unsigned sp + v)%Z in H by lia
  | |- context [(bv_unsigned ?sp + ?a + ?b)%Z] =>
      is_zlit a; is_zlit b; let v := eval vm_compute in (a + b)%Z in replace (bv_unsigned sp + a + b)%Z with (bv_unsigned sp + v)%Z by lia
  end.
Ltac fix_ret := lazymatch goal with |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

Section CANSEC1. Context {rc : runConstT}.
Definition AEMIT_DEPTH : Z := 5728.

#[using="Type"] Lemma out_pieces_outsk : forall (St : Type) (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St) ps,
  out_pieces get_so set_so ps = outsk (stdout_fwritex get_so set_so) ps (mret tt).
Proof. intros St get_so set_so ps. induction ps as [|p ps IH]; cbn [out_pieces outsk]; [reflexivity|]. rewrite IH. reflexivity. Qed.

Section Emit.
  Hypothesis HSTRN : strnlen_a_stmt.     (* [comment removed for export] *)
  Notation get_so := aps_so.
  Notation set_so := aset_so.

  Definition emit_printf_postA (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (lo : Z) (canary : word) (m : amem) : unit -> APS -> footprint -> machine_state -> Prop :=
    fun _ st' RNG' ms' => RNG' = RNG /\ exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : amem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ stdout_file m' (get_so st')
      /\ ssp_cells m' canary.

  (* [comment removed for export] *)
  Definition emit_printf_stmtA : Prop :=
    forall RNG (rstk : region) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : APS) (lo : Z) (canary : word) (v : Z),
      stdout_file m (get_so st) ->
      (-2^31 <= v < 2^31) -> bv_unsigned a1 mod 2^32 = v mod 2^32 ->
      stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - AEMIT_DEPTH) -> (KHIGH <= lo) -> (bv_unsigned sp < 2^47) ->
      ssp_cells m canary -> mem_inv bsegs m -> frm0 fc ->
      (* [comment removed for export] *)
      ashenv m -> rclean m rstk -> r_lo rstk <= lo -> bv_unsigned sp <= r_hi rstk -> rodata_sh0 m -> rclean m RBstdout ->
      rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rrng RNG rstk -> rrng RNG RFMT -> rrng RNG RBstdout ->
      implMA RNG (s_emit get_so set_so v) st
             (emit_printf_postA RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m)
             (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 AEMIT_PRINTF) fc None m (seg_rom bsegs)).

  #[using="HSTRN"] Theorem emit_printf_proofA : emit_printf_stmtA.
  Proof.
    unfold emit_printf_stmtA. intros until v. intros SF VR VA1 ST LO KH SPHI SSP MI FRM ENV RCS RSlo RShi ROD RCB RGstk RGimg RRS RRF RRB.
    unfold AEMIT_DEPTH in *. pose proof KH as KH'. unfold KHIGH in KH'.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)]%Z m) as MU.
    pose proof (wmono_refl bsegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU1.
    (* [comment removed for export] *)
    unfold s_emit, stdout_vprintf.
    rewrite (out_pieces_outsk APS get_so set_so (pieces_pct_d v)).
    apply implMA_fold. unfold AEMIT_PRINTF. ienter.
    Local Ltac2 Set LiaHints.tbl := fun () => "02c0?1058660323.101 11392074935.1211159984522.122 1162083372.77  11801586693.10511950417218.12111957068056.83 1221317118.125 12911902344.98 1411653924.98  15688435136.82 16073966649.94 16075753763.73 16075755311.74 16479028504.81 16524822296.84 17776320431.79 17828060772.98 18484529432.98 18693104465.98 18837407391.98 19022441873.98 19042827563.83 19591777079.12220075231868.98 2115336524.81  21250035837.10521542523261.10521700301309.10521724205888.81 22226183811.81 22434196860.10222444666333.11922842247553.12523077509607.82 24385371164.11825878270254.80 26058469174.87 26857600322.12126861890284.94 26863608314.74 26863609846.73 27498241560.83 27723960707.80 28072922155.83 29040911966.98 29451978866.98 29788654622.81 3051486595.80  306449445.121  30927154677.98 31059105597.82 31070687724.83 31161366443.82 31188841880.82 31211773418.98 31282109929.98 31660695966.98 31846929757.12031993076760.98 32687003652.98 32770013518.98 3392500563.98  3464842776.84  34722219088.72 35215434392.83 35551210285.12135909988007.80 36115622446.80 36297512274.98 36344913816.83 3668568768.82  36776907029.98 37457188998.98 38347777338.98 38478403113.81 38478403113.82 38478403113.83 38478403113.84 3867792552.98  39389956526.81 39557300182.98 39769365440.81 39992812893.11940091925679.79 40374333670.71 41055372246.98 42152906053.98 42200251523.81 42350551097.94 42353027887.74 42353028387.73 43061792394.69 43121191467.82 43987951406.80 44484923210.10544519613978.98 44534409240.84 44554761685.98 44977136295.81 45096552682.98 4517862876.98  45788883264.80 46215307841.98 46887021955.79 47367953560.83 47663274663.79 47712440107.83 48059113296.12548135609364.72 48313144512.82 49834049331.80 49870597903.80 50173444969.12550628941955.12350628941955.78 50664164139.83 50972138295.12151234361003.81 51363700191.98 51787079037.10552084281981.1055255412195.101 52640784336.12553508056982.98 53767577772.78 54076858136.84 55899145577.98 55958408871.81 56185096621.83 56185097369.98 56185989799.81 56995406629.12057016229129.98 58108482024.98 58604304415.98 58687490512.72 5896867971.80  59457942168.82 59504824377.11759522377383.80 5957773127.98  59850329652.98 59850344243.12159860780822.10160111391000.84 60334854080.79 61103932905.98 6140963079.105 61811895192.83 61917199023.79 61994440323.81 62670790311.78 63235321903.79 63510117421.12163620907600.12563928885757.10564097026584.81 64656456728.84 65022043122.98 65212743211.80 65346271869.10565783396751.81 66023801651.12167408707478.98 67530936662.81 67530936662.82 67530936662.83 67530936662.84 67965490855.80 7320613356.83  8243131183.74  8243131683.73  8245082169.94  8603416747.82  8904525934.73  8904527458.74  8906966388.94  9668950080.81  00000100200600:00?00@00H00P00V00Z00^00_00`00a00i01101501601701801901:01@01A01B01F01R01^01j01n01o02002102202802<02@02O02P02Q02R02S02[02\02b02c02i02j02k02o03003103903?03G03H03I03J03K03L03M03N03O03W03X03`03d03e03i03j04204604704;04<04@04D04H04L04M04N04O04S04T04X04Y04Z04_04`04a04b04c04g04m05105205305;05<05=05>05?05C05D05E05M05N05R05W05[05_05`05a05b05c05d05j05k06106506A06M06N06S06T06X06`06a06b06c06d06e06i06j07007407507607>07?07@07A07N07[07h08008408508608>08B08C08D08H08L08Q08]08e08m09309909E09F09S09T09X09\09`09d09e09m09n09o0:00:60::0:>0:B0:FSSS2LOS2LOS3HspSS2LO3KH'S2LO3KH'S4SPHIS2LOS2HBSSSS2LO3KH'S2LO3KH'S2LOFSFFFS4SPHISFS2HBS2LO3KH'3HspS2LO3KH'3HspS2LO3KH'3HspS2HBSSSFS4SPHIS2LOS2LOS2LO4SPHI3KH'1HSSSSS2LO3KH'SS4SPHISS4RSloSSS2LOFSS2LO3KH'S4SPHIS2LO3KH'FSSSSSFFS2LO3KH'SS2LO3KH'S2LOSS2LOFS2LO3KH'S2HBFS2VRFS2LOS2LOS2LOS2LOFSFS2HBSS2LOSFS3KH'SSSSS2LOS4SPHIS2LOFFS2LO3KH'FSFSS2HBFSS2LO3KH'SS2LOS3KH'S2KHS2HBSSFSSS4SPHISS4SPHIS2KHS2LO3KH'3HspS2LO3KH'3HspSS3KH'FS2LOS2LO3KH'SSSSSS2LOSS4SPHIS2LOSSS2LO3KH'SSFS2LO4SPHI3KH'S2LO4SPHI3KH'S2LO4SPHI3KH'S2LO3KH'S2HBSFS2LO3KH'S2LOSSS2LOS2LOS3KH'S2LO3KH'3HspS2LO3KH'S2LO3KH'S4RShiS4SPHIS2LO3KH'3HspSS2LO4SPHI3KH'FS2LOS2LOS2LOS2LOSS2LO3KH'FFFS4SPHIS2KHS2KHS2KHS2HB".
carve_frame 80%nat ST.
    do 15 zs.
    (* [comment removed for export] *)
    zs.
    (* [comment removed for export] *)
    assert (AW : appW [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)]%Z) by solve_appW.
    assert (AS : ashsafe [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)]%Z) by solve_ashsafe.
    xport_env ENV MU WM as ENV1. pose proof (rodata_sh0_frame _ _ _ ROD MU WM AW) as ROD1.
    pose proof ENV1 as (Hgot & _ & Hshb & Hini & _ & _ & Hrpf & _ & _ & _ & _ & _ & Hckp & _).
    (* [comment removed for export] *)
    assert (FZ : shadow_bytes m0 (shad (FMT_D - 64)) (shad (FMT_D + 3 + 64)) (fun _ => 0)) by (apply (rodata_sh0_fmt _ FMT_D 3 ROD1); unfold FMT_D; lia).
    assert (RSHF : rng RNG (shad (FMT_D - 64)) (shad (FMT_D + 3 + 64) - shad (FMT_D - 64))).
    { unfold rrng, RFMT in RRF. cbn [r_rlo r_rhi] in RRF. eapply rng_sub'; [exact RRF|]. rewrite !shad_div. unfold FMT_D, ASHOFF. lia. }
    call_sp (vprintf_i_pre_d RNG).
    all: lazymatch goal with
         | |- evtF _ _ _ _ => idtac
         | |- stk _ _ _ _ => exact ST
         | |- rng _ _ _ => first [assumption | eapply rng_sub'; [exact RGstk | lia]]
         | |- _ => first [assumption | reflexivity | lia]
         end.
    lit_frames.
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app bsegs _ _ [_;_;_] _)) in FR. destruct FR as [FR VAC]. cbn [cells_size csize Nat.add app] in VAC.
    replace (bv_unsigned sp + -80 + Z.of_nat 24)%Z with (bv_unsigned sp + -56)%Z in VAC by lia.
    pose proof (rw_cells_bytes_at' _ _ _ _ VAC) as VAA. cbn [cells_bytes cbytes] in VAA.
    change (le8 a1 ++ le8 a2 ++ le8 a3 ++ le8 a4 ++ le8 a5 ++ le8 a6 ++ le8 a7 ++ []) with (u64s [a1; a2; a3; a4; a5; a6; a7]) in VAA.
    (* [comment removed for export] *)
    clear ENV1 ROD1 Hgot Hshb Hini Hrpf Hckp FZ RSHF.
    xport_env ENV MU WM as ENV2. pose proof (rodata_sh0_frame _ _ _ ROD MU WM AW) as ROD2.
    pose proof (rclean_transport _ _ _ _ RCS MU WM AW) as RCS2. pose proof (rclean_transport _ _ _ _ RCB MU WM AW) as RCB2.
    apply evtF_done.
    pose proof (vfprintf_stdout_proof get_so set_so aps_get_set' aps_set_set' fwritex_stdout_proof HSTRN) as VF.
    unfold vfprintf_stdout_stmt in VF. cbv zeta in VF.
    eapply implF_epost_evtF.
    { eapply VF with (A := FMT_D) (VA := (bv_unsigned sp + -56)%Z) (fmt := FMT_pct_d) (slots := [a1; a2; a3; a4; a5; a6; a7]) (args := [PA_i v])
                     (r := pct_d_len v) (lo := lo) (canary := canary) (rstk := rstk) (rfmt := RFMT);
        clear VF; rewrite ?unsigned_lit by lia; unfold VF_FRAME, VF_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength; cbn [length].
      all: try reflexivity. all: try lia.
      - eapply stdout_file_stk; [exact SF | exact MU1 | exact WM | unfold GLOBALS_TOP; lia].
      - apply fmt_bytes_at; [assumption | vm_compute; reflexivity | unfold FMT_D; lia | vm_compute; discriminate].
      - unfold FMT_pct_d. forall_range.
      - exact VAA.
      - cbn [args_ok arg_ok]. split; [|exact I]. split; [lia | exact VA1].
      - apply printf_pieces_pct_d. lia.
      - assumption.
      - split; assumption.
      - assumption.
      - exact FRM.
      - unfold FMT_D. lia.
      - unfold FMT_D, FMT_pct_d. cbn [length]. lia.
      - exact ENV2.
      - exact RCS2.
      - apply rodata_sh0_rclean. exact ROD2.
      - unfold inreg, RFMT, FMT_D, FMT_pct_d. cbn. lia.
      - unfold inreg, RFMT. cbn. lia.
      - exact RCB2.
      - eapply rng_sub'; [exact RGstk | lia].
      - exact RGimg.
      - eapply rng_sub'; [exact RGstk | cbn; lia].
      - exact RRS.
      - exact RRF.
      - exact RRB. }
    cbv beta. intros [[] st'] RNG' ms' [-> P]. clear MU1.
    unfold vfprintf_stdout_post in P. rewrite !unsigned_lit in P by lia.
    destruct P as (y5 & y6 & y7 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SF3 & SSP3).
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call bsegs mm m3 MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret. clear VF. cbn [fst snd] in *.
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (vfprintf_i_post RNG); rewrite ?unsigned_lit by lia; [exact MI3 | exact PC1 | eapply rng_sub'; [exact RGstk | lia]]. }
    cbv beta. intros ms' ->. rewrite !unsigned_lit by lia. lit_frames. fix_ret.
    eapply evtF_cut.
    { eapply (vprintf_i_post RNG); rewrite ?unsigned_lit by lia; [exact MI3 | eassumption | eapply rng_sub'; [exact RGstk | lia]]. }
    cbv beta. intros ms' ->. rewrite !unsigned_lit by lia. lit_frames. fix_ret.
    (* [comment removed for export] *)
    zs. zs. zs.
    (* [comment removed for export] *)
    lazymatch goal with P1 : rw_cells _ ?mm (bv_unsigned sp + -176)%Z _, S : stk _ _ lo _ |- _ => release_frame P1 S (bv_unsigned sp + -128)%Z end.
    lazymatch goal with P0 : rw_cells _ ?mm (bv_unsigned sp + -128)%Z _, S : stk _ _ lo _ |- _ => release_frame P0 S (bv_unsigned sp + -80)%Z end.
    lazymatch goal with FR : rw_cells _ ?mm (bv_unsigned sp + -80)%Z ?hd, VAC : rw_cells _ ?mm (bv_unsigned sp + -56)%Z ?rest |- _ =>
      assert (FALL : rw_cells bsegs mm (bv_unsigned sp + -80) (hd ++ rest));
      [ apply (proj2 (rw_cells_app bsegs _ _ _ _)); split; [exact FR|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact VAC | lia]
      | clear FR VAC ] end.
    cbn [app] in FALL.
    lazymatch goal with S : stk _ _ lo _ |- _ => release_frame FALL S (bv_unsigned sp) end.
    apply evtF_done. unfold emit_printf_postA. split; [reflexivity|]. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
    split; [assumption|]. split; [exact SF3|]. exact SSP3.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Emit.
End CANSEC1.
