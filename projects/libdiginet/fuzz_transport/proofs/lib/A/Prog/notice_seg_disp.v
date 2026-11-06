(* notice_seg_disp: notice's entry, its kind switch and the default arm, from the six arms (notice_seg_lib.v
   nt_path). The walk:
     +0x00 .. +0x20  the frame (sp - 16, ra at sp + 8), a5 = the shadow base through its GOT word, the instrumented
                     check of the 4-byte load at p (decided by the run's shadow entry of the notice's 72 bytes);
     +0x24           `lw a0, 0(a1)`: n->kind, from the region of the notice's first 16 bytes;
     +0x28 .. +0x30  a0 = kind - 1, `bltu 5, a0`: taken exactly for a kind outside 1 .. 6 (nt_br_kind), which runs
                     the epilogue and returns with the world unchanged (notice_m's last case);
     +0x34 .. +0x4c  the jump table at 0x20fcc (a TRANS_RO_RD range, read as the image's by trans_rom_view_rd):
                     the arm of the kind, reached by `jr a0`; each arm is one nt_path. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_data_cg check_state_desk_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import notice_seg_base notice_seg_lib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* A kind outside 1 .. 6 writes nothing. *)
Lemma nt_no_wr : forall Bw n a, (TI.n_kind n < 1 \/ 6 < TI.n_kind n) -> ~ notice_wr Bw n a.
Proof.
  intros Bw n a Hk Hw.
  unfold notice_wr, TC.N_STATE, TC.N_ACKED, TC.N_ACK_LOST, TC.N_DESK, TC.N_DATA, TC.N_FOREIGN in Hw.
  destruct Hw as [(E & _) | [(E & _) | [(E & _) | [(E & _) | [(E & _) | (E & _)]]]]]; lia.
Qed.

(* a0 at the switch: kind - 1. *)
Lemma nt_a0_lit : forall E (NB : list byte) kd c, ew E 33 = Z_to_bv 64 (TW.u_at NB 0 4) -> TW.s32_at NB 0 = kd ->
  c = kd - 1 -> sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff 33 0)) (SLit (-1))) = Z_to_bv 64 c.
Proof.
  intros E NB kd c H33 Hk ->.
  change (sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff 33 0)) (SLit (-1))))
    with (alu64 ALU_ADD (sv_denot E (SExt true 32 (SOff 33 0))) (Z_to_bv 64 (-1))).
  pose proof (TWL.u_at_range NB 0 4) as R. change (8 * Z.of_nat 4) with 32 in R.
  rewrite (nt_sext32 E 33 _ H33 R). change (bv_swrap 32 (TW.u_at NB 0 4)) with (TW.s32_at NB 0). rewrite Hk.
  rewrite nt_add_lit. f_equal; lia.
Qed.

Section disp. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma nt_agree : forall regs NB Bw E, (forall j, (j < 32)%nat -> ew E j = ew (nt_E regs NB Bw) j) ->
  ed E = ed (nt_E regs NB Bw) -> env_agree 32 (Ereg regs (nt_vals NB Bw)) E.
Proof.
  intros regs NB Bw E H1 H2. split.
  - intros j Hj. rewrite (H1 j Hj). unfold nt_E. apply Eimg_low. unfold A_TEXT. lia.
  - rewrite H2. reflexivity.
Qed.


Lemma nt_holds :
  @nt_path fx rc B MT TC.N_DESK NT_DESK -> @nt_path fx rc B MT TC.N_STATE NT_STATE ->
  @nt_path fx rc B MT TC.N_DATA NT_DATA -> @nt_path fx rc B MT TC.N_ACKED NT_ACKED ->
  @nt_path fx rc B MT TC.N_ACK_LOST NT_LOST -> @nt_path fx rc B MT TC.N_FOREIGN NT_FOREIGN ->
  @transport_notice_cg_holds_stmt fx rc B MT.
Proof.
intros PDESK PSTATE PDATA PACKED PLOST PFOREIGN.
unfold transport_notice_cg_holds_stmt.
intros HCELLS HNC LAWS MTL HGX HGE HDESK HLOST HDATA HACK HONL.
unfold transport_notice_cg.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw'
  HJ Hra Hra4 Hgp Htp H11 Hsp16 Hlo Hhi HNT HTF HRO Htw Hm HAP HDT Hev.
pose proof HNT as HNT2.
destruct HNT2 as (P0 & P8 & Hsrc & Hoffw & NB & HNB & HNBL & HK0 & HK4 & HK8 & HK12 & Hpers & Hmac & Hblen
  & HK64 & HK68 & Hrest).
assert (HC : @nt_ctx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB)
  by exact {| c_cells := HCELLS; c_ncells := HNC; c_laws := LAWS; c_mtl := MTL; c_gx := HGX; c_gxe := HGE;
              c_desk := HDESK; c_lost := HLOST; c_data := HDATA; c_acked := HACK; c_online := HONL; c_J := HJ;
              c_ra := Hra; c_ra4 := Hra4; c_gp := Hgp; c_tp := Htp; c_a1 := H11; c_sp16 := Hsp16; c_lo := Hlo;
              c_hi := Hhi; c_nt := HNT; c_tf := HTF; c_ro := HRO; c_tw := Htw; c_m := Hm; c_ap := HAP; c_dt := HDT;
              c_ev := Hev; c_nb := HNB; c_nbl := HNBL; c_kind := HK0; c_state := HK4; c_old := HK8;
              c_reason := HK12; c_counter := HK64; c_retry := HK68 |}.
destruct (nt_basics B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB HC)
  as (HAR & Hwin & Hsp & Hce & Hm16 & Hp4096 & Hp47 & Hp8 & Hoffp & Hrd).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : NOTICE_STK = 8240) by reflexivity.
set (E0 := nt_E regs NB Bw).
assert (HEI0 : img_env VAL A_LIM E0) by (unfold E0, nt_E; apply Eimg_env).
assert (EE : forall j (r : bv 5), Z.of_nat j = bv_unsigned r -> ew E0 j = YK11.getr regs r)
  by (intros j r Hj; unfold E0; apply nt_E_reg; exact Hj).
assert (EXT : forall j, (j < 11)%nat -> ew E0 (32 + j) = nth j (nt_vals NB Bw) (Z_to_bv 64 0))
  by (intros j Hj; unfold E0; apply nt_E_atom; exact Hj).
pose proof (EXT 0%nat ltac:(lia)) as E32. pose proof (EXT 1%nat ltac:(lia)) as E33.
pose proof (EXT 2%nat ltac:(lia)) as E34. pose proof (EXT 3%nat ltac:(lia)) as E35.
pose proof (EXT 4%nat ltac:(lia)) as E36.
cbn [Nat.add nth nt_vals] in E32, E33, E34, E35, E36.
assert (E11 : ew E0 11 = Z_to_bv 64 p) by (rewrite (EE 11%nat 11%bv eq_refl); exact H11).
assert (U11 : bv_unsigned (ew E0 11) = p) by (rewrite E11; apply unsigned_lit_small; lia).
assert (Usp0 : bv_unsigned (ew E0 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
destruct (nt_entry B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB HC) as [HS SHOK].
fold E0 in HS, SHOK.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
pose proof (paj_ret_at (fx := fx) (PL := PL_transport) (PI := PI_transport)) as RET.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_notice)) memc (YK11.seg_rom segs)) mdc) Q)
  end.
(* run 1, +0x00 .. +0x20: the frame, the saves, the shadow base, the instrumented check of the load at p. *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ nt_awr. }
lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
  set (md1 := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md1; clear mt end.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mz) =>
  assert (KA1 : nt_KA W memc (ms_mem mz) (nt_Wn regs)) by
    (apply (nt_KA_run _ _ W memc memc _ _ (nt_KA_refl W memc _) HFr HG);
     intros b wlo whi x Hin Hx; cbv beta; unfold nt_Wn;
     nt_win Hin Hx ltac:(rewrite ?Usp0 in Hx; lia)) end.
clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E1 := EF) in HS, SHOK, HEI end.
assert (E1lo : forall j, (j < 1024)%nat -> ew E1 j = ew E0 j)
  by (intros j Hj; unfold E1; repeat rewrite ew_ewset_other by lia; reflexivity).
assert (U11_1 : bv_unsigned (ew E1 11) = p) by (rewrite E1lo by lia; exact U11).
assert (Usp1 : bv_unsigned (ew E1 2) = spZ regs) by (rewrite E1lo by lia; exact Usp0).
(* the two runtime cells dropped, the notice's first 16 bytes added *)
nt_keep1.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mz) =>
  assert (HNB1 : garr8 segs (mrestrict (w_H W) (ms_mem mz)) p (map DSpec.bz NB)) by
    (apply (nt_garr8_keep W memc _ (nt_Wn regs) p _ KA1 HNB);
     intros a Ha; rewrite length_map, HNBL in Ha; split;
     [lia | unfold nt_Wn, decode_off_win, NTC_SIZE in *; lia]) end.
pose proof (nt_add E1 _ _ nt_reg_p HS ltac:(vm_compute; reflexivity)) as HSq. clear HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq.
specialize (HSq ltac:(cbn [ms_mem restrict];
  apply (nt_preg_ok E1 _ p NB); first
    [ rewrite E1lo by lia; first [exact E11 | exact E33 | exact E34 | exact E35 | exact E36]
    | lia | exact HNB1 | exact HNBL ])).
specialize (HSq ltac:(cbn [all_disjoint]; split; [|exact I];
  unfold extent_disjoint, nt_reg_p, nt_reg_frame;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite Usp1, U11_1;
  unfold decode_off_win in Hoffp; lia)).
rename HSq into HS.
(* run 2, +0x24 .. +0x30: the kind load and `bltu 5, a0`. *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ nt_awr. }
lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
  set (md2 := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md2; clear mt end.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mz) =>
  assert (KA2 : nt_KA W memc (ms_mem mz) (nt_Wn regs)) by
    (apply (nt_KA_run _ _ W memc _ _ _ KA1 HFr HG);
     intros b wlo whi x Hin Hx; cbv beta; unfold nt_Wn;
     nt_win Hin Hx ltac:(rewrite ?Usp1, ?U11_1 in Hx; lia)) end.
clear HF HFr HG KA1.
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E2 := EF) in HS, SHOK, HEI end.
assert (E2lo : forall j, (j < 1024)%nat -> ew E2 j = ew E0 j)
  by (intros j Hj; unfold E2; repeat rewrite ew_ewset_other by lia; apply E1lo; exact Hj).
assert (U11_2 : bv_unsigned (ew E2 11) = p) by (rewrite E2lo by lia; exact U11).
assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite E2lo by lia; exact Usp0).
assert (E32_2 : ew E2 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite E2lo by lia; exact E32).
assert (E33_2 : ew E2 33 = Z_to_bv 64 (TW.u_at NB 0 4)) by (rewrite E2lo by lia; exact E33).
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* a kind outside 1 .. 6: the epilogue, the world unchanged *)
  rewrite (nt_br_kind E2 NB (TI.n_kind n) E33_2 HK0) in Hc.
  apply negb_true_iff, andb_false_iff in Hc.
  assert (HKout : TI.n_kind n < 1 \/ 6 < TI.n_kind n)
    by (destruct Hc as [Hc|Hc]; [left; apply Z.leb_gt in Hc | right; apply Z.leb_gt in Hc]; lia).
  pose proof (nt_m_out timg_A Fr Bw n Bw' HKout Hm) as HBw.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { nt_awr. }
  lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
    set (md3 := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md3; clear mt end.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mz) =>
    assert (KA3 : nt_KA W memc (ms_mem mz) (nt_Wn regs)) by
      (apply (nt_KA_run _ _ W memc _ _ _ KA2 HFr HG);
       intros b wlo whi x Hin Hx; cbv beta; unfold nt_Wn;
       nt_win Hin Hx ltac:(rewrite ?Usp2, ?U11_2 in Hx; lia)) end.
  clear HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict _ ?mz) =>
    set (EF3 := EF) in HS; rename mz into msF end.
  assert (EF3lo : forall j, (j < 1024)%nat -> ew EF3 j = ew E0 j)
    by (intros j Hj; unfold EF3; repeat rewrite ew_ewset_other by lia; apply E2lo; exact Hj).
  nt_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1
    ltac:(cbn [sv_denot]; rewrite EF3lo by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          reflexivity).
  assert (HPF : aregs_preserved regs (ms_regs msF)).
  { apply (aregs_preserved_of_st_ok segs (w_H W) EF3 _ msF regs (nt_vals NB Bw) HS).
    - apply nt_agree; [intros j Hj; rewrite EF3lo by lia; reflexivity | reflexivity].
    - vm_compute. reflexivity. }
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  refine (nt_close B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB
    (ms_regs msF) (ms_mem msF) md3 HC HJ
    (nt_KA_mono W memc _ (nt_Wn regs) (nt_Zs regs Bw n) (fun a Ha => nt_Wn_Zs regs Bw n a Ha) KA3)
    _ HPF RF1 mat').
  rewrite HBw. apply (nt_tw_keep W memc (ms_mem msF) Bw (nt_Wn regs) Htw KA3).
  intros x Hx Hz; pose proof (TMAP_A_hull x Hx) as Hh;
    unfold nt_Wn, TG.G_HARNESS_LO, TG.G_HARNESS_HI in *; lia.
- (* a kind in 1 .. 6: the jump table *)
  rewrite (nt_br_kind E2 NB (TI.n_kind n) E33_2 HK0) in Hc.
  apply negb_false_iff, andb_true_iff in Hc. destruct Hc as [Hc1 Hc2].
  apply Z.leb_le in Hc1. apply Z.leb_le in Hc2.
  assert (KC : TI.n_kind n = 1 \/ TI.n_kind n = 2 \/ TI.n_kind n = 3 \/ TI.n_kind n = 4 \/ TI.n_kind n = 5 \/
    TI.n_kind n = 6) by lia.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mz) =>
    assert (HRO2 : trans_rom_view_rd W (ms_mem mz))
      by (apply (nt_ro_keep W memc _ regs Hce KA2 HRO)) end.
  assert (UT : bv_unsigned (ew E2 (A_OBJ 35)) = 135116).
  { rewrite (HEI (A_OBJ 35) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)). vm_compute. reflexivity. }
  destruct KC as [Ek | [Ek | [Ek | [Ek | [Ek | Ek]]]]].
  + (* kind 1: N_DESK *)
    nt_reg HS (Z_to_bv 5 10) (Z_to_bv 64 0) Q10
      ltac:(apply (nt_a0_lit _ NB (TI.n_kind n) _ E33_2 HK0); lia).
    pose proof (nt_pin E2 _ _ (Z_to_bv 5 10) (SLit 0) HS Q10 ltac:(vm_compute; reflexivity)) as HSq.
    clear HS Q10. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq. rename HSq into HS.
    nt_keep1.
    pose proof (nt_add E2 _ _ nt_reg_tbl HS ltac:(vm_compute; reflexivity)) as HSq. clear HS.
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq.
    specialize (HSq ltac:(cbn [ms_mem restrict]; apply (nt_tbl_ok W _ E2); [exact UT | exact HRO2])).
    specialize (HSq ltac:(cbn [all_disjoint]; split; [|exact I];
      unfold extent_disjoint, nt_reg_tbl;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; lia)).
    rename HSq into HS.
    pose proof (nt_facts_set E2 _ _ nt_facts HS
      ltac:(apply (nt_facts_ok E2 (spZ regs) p); first [exact Usp2 | exact U11_2 | exact E32_2 | lia])) as HSq.
    clear HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq. rename HSq into HS.
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { nt_awr. }
    lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
      set (mdJ := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody mdJ; clear mt end.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mz) =>
      assert (KAJ : nt_KA W memc (ms_mem mz) (nt_Wn regs)) by
        (apply (nt_KA_run _ _ W memc _ _ _ KA2 HFr HG);
         intros b wlo whi x Hin Hx; cbv beta; unfold nt_Wn;
         nt_win Hin Hx ltac:(rewrite ?Usp2, ?U11_2 in Hx; lia)) end.
    clear HF HFr HG.
    lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict _ ?mz) =>
      set (E3 := EF) in HS, SHOK, HEI; rename mz into msJ end.
    assert (E3lo : forall j, (j < 1024)%nat -> ew E3 j = ew E0 j)
      by (intros j Hj; unfold E3; repeat rewrite ew_ewset_other by lia; apply E2lo; exact Hj).
    nt_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (BASE + NT_DESK)) Q10
      ltac:(cbn [sv_denot]; rewrite (HEI 276%nat ltac:(unfold A_TEXT, A_LIM; lia));
            f_equal; vm_compute; reflexivity).
    pose proof (nt_pin E3 _ _ (Z_to_bv 5 10) (SOff A_TEXT NT_DESK) HS
      (eq_trans Q10 (eq_sym (codeptr_val E3 NT_DESK HEI))) ltac:(vm_compute; reflexivity)) as HSq.
    clear HS Q10. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq. rename HSq into HS.
    nt_keep1.
    change (st_ok_pi tfibsegs VAL E3 (nt_ss_jr (SOff A_TEXT NT_DESK)) (restrict (w_H W) msJ)) in HS.
    exact (PDESK STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB E3 msJ mdJ
      HC Ek HS HEI ltac:(intros j Hj; apply E3lo; lia) eq_refl SHOK HJ KAJ).
  + (* kind 2: N_STATE *)
    nt_reg HS (Z_to_bv 5 10) (Z_to_bv 64 1) Q10
      ltac:(apply (nt_a0_lit _ NB (TI.n_kind n) _ E33_2 HK0); lia).
    pose proof (nt_pin E2 _ _ (Z_to_bv 5 10) (SLit 1) HS Q10 ltac:(vm_compute; reflexivity)) as HSq.
    clear HS Q10. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq. rename HSq into HS.
    nt_keep1.
    pose proof (nt_add E2 _ _ nt_reg_tbl HS ltac:(vm_compute; reflexivity)) as HSq. clear HS.
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq.
    specialize (HSq ltac:(cbn [ms_mem restrict]; apply (nt_tbl_ok W _ E2); [exact UT | exact HRO2])).
    specialize (HSq ltac:(cbn [all_disjoint]; split; [|exact I];
      unfold extent_disjoint, nt_reg_tbl;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; lia)).
    rename HSq into HS.
    pose proof (nt_facts_set E2 _ _ nt_facts HS
      ltac:(apply (nt_facts_ok E2 (spZ regs) p); first [exact Usp2 | exact U11_2 | exact E32_2 | lia])) as HSq.
    clear HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq. rename HSq into HS.
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { nt_awr. }
    lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
      set (mdJ := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody mdJ; clear mt end.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mz) =>
      assert (KAJ : nt_KA W memc (ms_mem mz) (nt_Wn regs)) by
        (apply (nt_KA_run _ _ W memc _ _ _ KA2 HFr HG);
         intros b wlo whi x Hin Hx; cbv beta; unfold nt_Wn;
         nt_win Hin Hx ltac:(rewrite ?Usp2, ?U11_2 in Hx; lia)) end.
    clear HF HFr HG.
    lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict _ ?mz) =>
      set (E3 := EF) in HS, SHOK, HEI; rename mz into msJ end.
    assert (E3lo : forall j, (j < 1024)%nat -> ew E3 j = ew E0 j)
      by (intros j Hj; unfold E3; repeat rewrite ew_ewset_other by lia; apply E2lo; exact Hj).
    nt_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (BASE + NT_STATE)) Q10
      ltac:(cbn [sv_denot]; rewrite (HEI 276%nat ltac:(unfold A_TEXT, A_LIM; lia));
            f_equal; vm_compute; reflexivity).
    pose proof (nt_pin E3 _ _ (Z_to_bv 5 10) (SOff A_TEXT NT_STATE) HS
      (eq_trans Q10 (eq_sym (codeptr_val E3 NT_STATE HEI))) ltac:(vm_compute; reflexivity)) as HSq.
    clear HS Q10. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq. rename HSq into HS.
    nt_keep1.
    change (st_ok_pi tfibsegs VAL E3 (nt_ss_jr (SOff A_TEXT NT_STATE)) (restrict (w_H W) msJ)) in HS.
    exact (PSTATE STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB E3 msJ mdJ
      HC Ek HS HEI ltac:(intros j Hj; apply E3lo; lia) eq_refl SHOK HJ KAJ).
  + (* kind 3: N_DATA *)
    nt_reg HS (Z_to_bv 5 10) (Z_to_bv 64 2) Q10
      ltac:(apply (nt_a0_lit _ NB (TI.n_kind n) _ E33_2 HK0); lia).
    pose proof (nt_pin E2 _ _ (Z_to_bv 5 10) (SLit 2) HS Q10 ltac:(vm_compute; reflexivity)) as HSq.
    clear HS Q10. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq. rename HSq into HS.
    nt_keep1.
    pose proof (nt_add E2 _ _ nt_reg_tbl HS ltac:(vm_compute; reflexivity)) as HSq. clear HS.
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq.
    specialize (HSq ltac:(cbn [ms_mem restrict]; apply (nt_tbl_ok W _ E2); [exact UT | exact HRO2])).
    specialize (HSq ltac:(cbn [all_disjoint]; split; [|exact I];
      unfold extent_disjoint, nt_reg_tbl;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; lia)).
    rename HSq into HS.
    pose proof (nt_facts_set E2 _ _ nt_facts HS
      ltac:(apply (nt_facts_ok E2 (spZ regs) p); first [exact Usp2 | exact U11_2 | exact E32_2 | lia])) as HSq.
    clear HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq. rename HSq into HS.
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { nt_awr. }
    lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
      set (mdJ := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody mdJ; clear mt end.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mz) =>
      assert (KAJ : nt_KA W memc (ms_mem mz) (nt_Wn regs)) by
        (apply (nt_KA_run _ _ W memc _ _ _ KA2 HFr HG);
         intros b wlo whi x Hin Hx; cbv beta; unfold nt_Wn;
         nt_win Hin Hx ltac:(rewrite ?Usp2, ?U11_2 in Hx; lia)) end.
    clear HF HFr HG.
    lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict _ ?mz) =>
      set (E3 := EF) in HS, SHOK, HEI; rename mz into msJ end.
    assert (E3lo : forall j, (j < 1024)%nat -> ew E3 j = ew E0 j)
      by (intros j Hj; unfold E3; repeat rewrite ew_ewset_other by lia; apply E2lo; exact Hj).
    nt_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (BASE + NT_DATA)) Q10
      ltac:(cbn [sv_denot]; rewrite (HEI 276%nat ltac:(unfold A_TEXT, A_LIM; lia));
            f_equal; vm_compute; reflexivity).
    pose proof (nt_pin E3 _ _ (Z_to_bv 5 10) (SOff A_TEXT NT_DATA) HS
      (eq_trans Q10 (eq_sym (codeptr_val E3 NT_DATA HEI))) ltac:(vm_compute; reflexivity)) as HSq.
    clear HS Q10. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq. rename HSq into HS.
    nt_keep1.
    change (st_ok_pi tfibsegs VAL E3 (nt_ss_jr (SOff A_TEXT NT_DATA)) (restrict (w_H W) msJ)) in HS.
    exact (PDATA STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB E3 msJ mdJ
      HC Ek HS HEI ltac:(intros j Hj; apply E3lo; lia) eq_refl SHOK HJ KAJ).
  + (* kind 4: N_ACKED *)
    nt_reg HS (Z_to_bv 5 10) (Z_to_bv 64 3) Q10
      ltac:(apply (nt_a0_lit _ NB (TI.n_kind n) _ E33_2 HK0); lia).
    pose proof (nt_pin E2 _ _ (Z_to_bv 5 10) (SLit 3) HS Q10 ltac:(vm_compute; reflexivity)) as HSq.
    clear HS Q10. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq. rename HSq into HS.
    nt_keep1.
    pose proof (nt_add E2 _ _ nt_reg_tbl HS ltac:(vm_compute; reflexivity)) as HSq. clear HS.
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq.
    specialize (HSq ltac:(cbn [ms_mem restrict]; apply (nt_tbl_ok W _ E2); [exact UT | exact HRO2])).
    specialize (HSq ltac:(cbn [all_disjoint]; split; [|exact I];
      unfold extent_disjoint, nt_reg_tbl;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; lia)).
    rename HSq into HS.
    pose proof (nt_facts_set E2 _ _ nt_facts HS
      ltac:(apply (nt_facts_ok E2 (spZ regs) p); first [exact Usp2 | exact U11_2 | exact E32_2 | lia])) as HSq.
    clear HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq. rename HSq into HS.
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { nt_awr. }
    lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
      set (mdJ := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody mdJ; clear mt end.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mz) =>
      assert (KAJ : nt_KA W memc (ms_mem mz) (nt_Wn regs)) by
        (apply (nt_KA_run _ _ W memc _ _ _ KA2 HFr HG);
         intros b wlo whi x Hin Hx; cbv beta; unfold nt_Wn;
         nt_win Hin Hx ltac:(rewrite ?Usp2, ?U11_2 in Hx; lia)) end.
    clear HF HFr HG.
    lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict _ ?mz) =>
      set (E3 := EF) in HS, SHOK, HEI; rename mz into msJ end.
    assert (E3lo : forall j, (j < 1024)%nat -> ew E3 j = ew E0 j)
      by (intros j Hj; unfold E3; repeat rewrite ew_ewset_other by lia; apply E2lo; exact Hj).
    nt_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (BASE + NT_ACKED)) Q10
      ltac:(cbn [sv_denot]; rewrite (HEI 276%nat ltac:(unfold A_TEXT, A_LIM; lia));
            f_equal; vm_compute; reflexivity).
    pose proof (nt_pin E3 _ _ (Z_to_bv 5 10) (SOff A_TEXT NT_ACKED) HS
      (eq_trans Q10 (eq_sym (codeptr_val E3 NT_ACKED HEI))) ltac:(vm_compute; reflexivity)) as HSq.
    clear HS Q10. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq. rename HSq into HS.
    nt_keep1.
    change (st_ok_pi tfibsegs VAL E3 (nt_ss_jr (SOff A_TEXT NT_ACKED)) (restrict (w_H W) msJ)) in HS.
    exact (PACKED STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB E3 msJ mdJ
      HC Ek HS HEI ltac:(intros j Hj; apply E3lo; lia) eq_refl SHOK HJ KAJ).
  + (* kind 5: N_ACK_LOST *)
    nt_reg HS (Z_to_bv 5 10) (Z_to_bv 64 4) Q10
      ltac:(apply (nt_a0_lit _ NB (TI.n_kind n) _ E33_2 HK0); lia).
    pose proof (nt_pin E2 _ _ (Z_to_bv 5 10) (SLit 4) HS Q10 ltac:(vm_compute; reflexivity)) as HSq.
    clear HS Q10. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq. rename HSq into HS.
    nt_keep1.
    pose proof (nt_add E2 _ _ nt_reg_tbl HS ltac:(vm_compute; reflexivity)) as HSq. clear HS.
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq.
    specialize (HSq ltac:(cbn [ms_mem restrict]; apply (nt_tbl_ok W _ E2); [exact UT | exact HRO2])).
    specialize (HSq ltac:(cbn [all_disjoint]; split; [|exact I];
      unfold extent_disjoint, nt_reg_tbl;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; lia)).
    rename HSq into HS.
    pose proof (nt_facts_set E2 _ _ nt_facts HS
      ltac:(apply (nt_facts_ok E2 (spZ regs) p); first [exact Usp2 | exact U11_2 | exact E32_2 | lia])) as HSq.
    clear HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq. rename HSq into HS.
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { nt_awr. }
    lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
      set (mdJ := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody mdJ; clear mt end.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mz) =>
      assert (KAJ : nt_KA W memc (ms_mem mz) (nt_Wn regs)) by
        (apply (nt_KA_run _ _ W memc _ _ _ KA2 HFr HG);
         intros b wlo whi x Hin Hx; cbv beta; unfold nt_Wn;
         nt_win Hin Hx ltac:(rewrite ?Usp2, ?U11_2 in Hx; lia)) end.
    clear HF HFr HG.
    lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict _ ?mz) =>
      set (E3 := EF) in HS, SHOK, HEI; rename mz into msJ end.
    assert (E3lo : forall j, (j < 1024)%nat -> ew E3 j = ew E0 j)
      by (intros j Hj; unfold E3; repeat rewrite ew_ewset_other by lia; apply E2lo; exact Hj).
    nt_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (BASE + NT_LOST)) Q10
      ltac:(cbn [sv_denot]; rewrite (HEI 276%nat ltac:(unfold A_TEXT, A_LIM; lia));
            f_equal; vm_compute; reflexivity).
    pose proof (nt_pin E3 _ _ (Z_to_bv 5 10) (SOff A_TEXT NT_LOST) HS
      (eq_trans Q10 (eq_sym (codeptr_val E3 NT_LOST HEI))) ltac:(vm_compute; reflexivity)) as HSq.
    clear HS Q10. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq. rename HSq into HS.
    nt_keep1.
    change (st_ok_pi tfibsegs VAL E3 (nt_ss_jr (SOff A_TEXT NT_LOST)) (restrict (w_H W) msJ)) in HS.
    exact (PLOST STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB E3 msJ mdJ
      HC Ek HS HEI ltac:(intros j Hj; apply E3lo; lia) eq_refl SHOK HJ KAJ).
  + (* kind 6: N_FOREIGN *)
    nt_reg HS (Z_to_bv 5 10) (Z_to_bv 64 5) Q10
      ltac:(apply (nt_a0_lit _ NB (TI.n_kind n) _ E33_2 HK0); lia).
    pose proof (nt_pin E2 _ _ (Z_to_bv 5 10) (SLit 5) HS Q10 ltac:(vm_compute; reflexivity)) as HSq.
    clear HS Q10. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq. rename HSq into HS.
    nt_keep1.
    pose proof (nt_add E2 _ _ nt_reg_tbl HS ltac:(vm_compute; reflexivity)) as HSq. clear HS.
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq.
    specialize (HSq ltac:(cbn [ms_mem restrict]; apply (nt_tbl_ok W _ E2); [exact UT | exact HRO2])).
    specialize (HSq ltac:(cbn [all_disjoint]; split; [|exact I];
      unfold extent_disjoint, nt_reg_tbl;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; lia)).
    rename HSq into HS.
    pose proof (nt_facts_set E2 _ _ nt_facts HS
      ltac:(apply (nt_facts_ok E2 (spZ regs) p); first [exact Usp2 | exact U11_2 | exact E32_2 | lia])) as HSq.
    clear HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq. rename HSq into HS.
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { nt_awr. }
    lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
      set (mdJ := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody mdJ; clear mt end.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mz) =>
      assert (KAJ : nt_KA W memc (ms_mem mz) (nt_Wn regs)) by
        (apply (nt_KA_run _ _ W memc _ _ _ KA2 HFr HG);
         intros b wlo whi x Hin Hx; cbv beta; unfold nt_Wn;
         nt_win Hin Hx ltac:(rewrite ?Usp2, ?U11_2 in Hx; lia)) end.
    clear HF HFr HG.
    lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict _ ?mz) =>
      set (E3 := EF) in HS, SHOK, HEI; rename mz into msJ end.
    assert (E3lo : forall j, (j < 1024)%nat -> ew E3 j = ew E0 j)
      by (intros j Hj; unfold E3; repeat rewrite ew_ewset_other by lia; apply E2lo; exact Hj).
    nt_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (BASE + NT_FOREIGN)) Q10
      ltac:(cbn [sv_denot]; rewrite (HEI 276%nat ltac:(unfold A_TEXT, A_LIM; lia));
            f_equal; vm_compute; reflexivity).
    pose proof (nt_pin E3 _ _ (Z_to_bv 5 10) (SOff A_TEXT NT_FOREIGN) HS
      (eq_trans Q10 (eq_sym (codeptr_val E3 NT_FOREIGN HEI))) ltac:(vm_compute; reflexivity)) as HSq.
    clear HS Q10. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq. rename HSq into HS.
    nt_keep1.
    change (st_ok_pi tfibsegs VAL E3 (nt_ss_jr (SOff A_TEXT NT_FOREIGN)) (restrict (w_H W) msJ)) in HS.
    exact (PFOREIGN STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB E3 msJ mdJ
      HC Ek HS HEI ltac:(intros j Hj; apply E3lo; lia) eq_refl SHOK HJ KAJ).
Qed.
End disp.
