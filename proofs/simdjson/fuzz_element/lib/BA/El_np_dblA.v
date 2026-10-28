(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image RzCPS FP ZBridge.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim Monad PrintfModel PrintfFormats.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import SoftFloat FmtFp FmtFpDig FmtFpTail FmtFp6 FmtFpNf.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Export FX_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Startup_glue Pj_steps Pj_loc_kit Pj_os_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Printf_mlib F_printf_iface Printf_pieces Printf_sn El_fmt_facts.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout R_m2s I_consts I_qck D_kit D_clx RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_iface3 F_achk Fe_icalls Fe_printf_iface Fe_vsnprintf I_pchead I_vprintfw I_pcfmt6 I_vfsn6 I_vsn6 I_frexpl F_fmt_fp_sn. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_akit Sj_acps Sj_hkit Sj_num_akit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Pj_defsA Pj_os_defsA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import El_snlA El_np_wgiA El_np_wgfA El_os_xsputnLA El_os_padA El_ins_ifaceA El_np_intA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Export El_os_defsA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.

Ltac show_pc := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "pc =" pc end.
Ltac show_reg k :=
  lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 k)) in
    let v := eval cbv beta iota delta [tget] in (tget p R) in
    idtac "x" k "=" v
  end.
Ltac lit_reg e := let v := eval vm_compute in e in replace e with v by (vm_compute; reflexivity).
Ltac lit_words := repeat match goal with |- context [zext 64 ?x] =>
  let v := eval vm_compute in (bv_unsigned (zext 64 x)) in
  replace (zext 64 x) with (Z_to_bv 64 v) by (apply bv_eq; vm_compute; reflexivity) end.

Notation NPD_DEPTH := 10688%Z (only parsing).
Definition FMT_g : list Z := [37; 46; 42; 103; 0]%Z.

Lemma OUTFP_sn_g : forall y txt n, fmt_fp_total [] y 0 6 0 CHR_g = Some (txt, n) -> zlength txt = n -> (0 <= n <= 80)%Z ->
  OUTFP_sn y 0 6 0 CHR_g [] = ITree.Ret (Exc.Ok (n, txt)).
Proof.
  intros y txt n HF HL HN. unfold OUTFP_sn. rewrite (mbind_eq mget _ [] [] []) by reflexivity.
  rewrite HF. unfold SN_CAP. rewrite HL. change (zlength (@nil Z)) with 0%Z.
  replace ((0 <=? n) && (n <=? 80))%Z with true by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
  rewrite (mbind_eq (mput txt) _ [] tt txt) by reflexivity. reflexivity.
Qed.

Lemma printf_model_g : forall y txt n, fmt_fp_total [] y 0 6 0 CHR_g = Some (txt, n) -> zlength txt = n -> (0 <= n <= 80)%Z ->
  printf_model OUT_sn OUTFP_sn FMT_g [PA_i 6; PA_g y] [] = ITree.Ret (Exc.Ok (n, txt)).
Proof.
  intros y txt n HF HL HN.
  unfold printf_model, FMT_g. lazy -[OUTFP_sn OUT_sn mbind mret munr].
  rewrite (mbind_eq (OUT_sn []) _ [] tt []) by (apply OUT_sn_eq; discriminate).
  rewrite (mbind_mbind_eq (OUTFP_sn y 0 6 0 103) _ _ [] n txt) by (apply OUTFP_sn_g; assumption).
  change ((cnt <- (if ((n <? 0) || (PrintfModel.INT_MAX - 0 <? n))%Z then munr else mret (0 + n)%Z) ;; mret cnt) txt = ITree.Ret (Exc.Ok (n, txt))).
  replace ((n <? 0) || (PrintfModel.INT_MAX - 0 <? n))%Z with false
    by (symmetry; apply orb_false_intro; apply Z.ltb_ge; unfold PrintfModel.INT_MAX; lia).
  rewrite mbind_mret. rewrite Z.add_0_l. reflexivity.
Qed.

Section FPC.
Hypothesis RIP : rip_stmt.
Lemma fpcalls_g : forall d, fpcalls_sn_ok FMT_g [PA_i 6; PA_g (f128_of_d d)].
Proof using RIP.
  intros d. unfold fpcalls_sn_ok. intros. lazy -[fpcall_stmt SINK_sn TOPOK_sn OUTFP_sn SN_CAP f128_of_d].
  apply Forall_cons; [| apply Forall_nil]. apply (sn_fpcall _ _ _ _ _ _ _ _ RIP (ifrexpl_proof RIP)); lia.
Qed.
End FPC.

Lemma gchb_zb : forall txt, Forall noxc txt -> Forall gchb (zb txt).
Proof.
  intros txt H. unfold zb. apply Forall_map. eapply Forall_impl; [|exact H].
  intros c [Rc Hc]. unfold gchb. rewrite Z_to_bv_small; [exact Hc|]. unfold bv_modulus. cbn. lia.
Qed.

Definition npd1_post (sp gp tp s10 s11 : word) (F : bvmap 5 word)
    (lo OS fill : Z) (canary ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (nc : Z) (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (ob jf : list byte) (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 0x11946c) (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0 t1 t2 (Z_to_bv 64 fill) (Z_to_bv 64 (OS + 136))
                  (Z_to_bv 64 OS) (Z_to_bv 64 (bv_unsigned sp + -201)) (Z_to_bv 64 (bv_unsigned sp + -201)) (Z_to_bv 64 (bv_unsigned sp + -201 + nc))
                  (Z_to_bv 64 (OS + 136)) (Z_to_bv 64 fill) a6 a7
                  (Z_to_bv 64 OS) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (bv_unsigned sp + -134)) (Z_to_bv 64 (bv_unsigned sp + -134 + nc))
                  (Z_to_bv 64 (bv_unsigned sp + -201)) (Z_to_bv 64 (bv_unsigned sp + -134)) (Z_to_bv 64 0x6a6870) s10 s11 t3 t4 t5 t6)
             Ft (Z_to_bv 64 0xb8714) fc' None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (0x6a7e38, 0x6a7e38 + 8)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10%Z -> bv_unsigned k <> 8%Z -> reg_get Ft k = reg_get F k)
    /\ stk asegs m' lo (bv_unsigned sp + -240)
    /\ ssp_cells m' canary
    /\ rw_cells asegs m' 0x6a7e38 [C8 (Z_to_bv 64 0x6c8130)] /\ LOCBA m'
    /\ (1 <= nc <= 14)%Z /\ length ob = Z.to_nat nc /\ bytes_at asegs m' (bv_unsigned sp + -201) ob
    /\ rw_cells asegs m' (bv_unsigned sp + -240) [CB 144 jf]
    /\ rw_cells asegs m' (bv_unsigned sp + -96) [C8 (reg_get F (Z_to_bv 5 8)); C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition npd_seg1_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo OS fill : Z) (dw : word) (j148 j284 : list byte) (canary : word),
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - NPD_DEPTH)%Z -> (0x6ca000 <= lo)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  tp = Z_to_bv 64 (0x6a7e38 + 48) ->
  rw_cells asegs m (OS + 136) (ios_cellsX OS 0x164678 0x1002 0 fill j148 j284) ->
  (0x6ca000 <= OS)%Z -> (OS + 288 <= lo)%Z ->
  (0 <= fill < 256)%Z -> reg_get F (Z_to_bv 5 10) = dw ->
  rw_cells asegs m 0x6a7e38 [C8 (Z_to_bv 64 0x6c8130)] -> ssp_cells m canary -> frm0 fc ->
  LOCBA m -> el_dccA m -> mem_inv asegs m ->
  (bv_unsigned sp mod 16 = 0)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> np_afacts lo (bv_unsigned sp) m ->
  evt asegs (npd1_post sp gp tp s10 s11 F lo OS fill canary ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 OS) (Z_to_bv 64 (OS + 136)) (Z_to_bv 64 fill) a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EL_NP_D) fc None m (seg_rom asegs)).

Lemma pcok2_g : forall m (d : Z) slots A VA lo r (o : list Z),
  printf_model OUT_sn OUTFP_sn FMT_g [PA_i 6; PA_g (f128_of_d d)] [] = ITree.Ret (Exc.Ok (r, o)) -> (1 <= r)%Z -> zlength o = r -> (r <= 14)%Z ->
  (0 <= VA)%Z -> (VA + 16 < 2^63)%Z -> pctx m -> pfcells6 m ->
  PCOK2_el FMT_g [PA_i 6; PA_g (f128_of_d d)] slots A VA lo m.
Proof.
  intros m d slots A VA lo r o MODEL R1 RL RH V0 V1 PC PF. split.
  - split; [exists [37; 46; 42; 103]%Z; split; [right; reflexivity| reflexivity]|].
    split; [exact V0|]. split; [exact V1|]. split; [exact PC| exact PF].
  - intros r' o' E. rewrite MODEL in E. injection E as <- <-. lia.
Qed.

Section Seg1.
Hypothesis RIP : rip_stmt.

Theorem npd_seg1 : npd_seg1_stmt.
Proof using RIP.
  unfold npd_seg1_stmt. intros until canary. intros ST LO LOLO SPH TP IOS OLO RO RF HDW TPC SSP FRM LB DCC MI SP16 HSH AF0.
  assert (SP16' : ((bv_unsigned sp + -240) mod 16 = 0)%Z) by (clear - SP16; Z.div_mod_to_equations; lia).
  assert (ZONE : forall x, np_zone x -> outside [(lo, bv_unsigned sp); (0x6a7e38, 0x6a7e38 + 8)]%Z x).
  { intros x Hx. unfold np_zone, SHADOW_LO, SHADOW_HI, kHighShadowEnd in *. cbn [outside]. lia. }
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 dw) as RDW. unfold bv_modulus in RDW. cbn in RDW.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(lo, bv_unsigned sp); (0x6a7e38, 0x6a7e38 + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof DCC as DCC'. destruct DCC as (VT & WS & WS2 & NPT & NPV & GNP & GCT).
  destruct LB as (l1 & l2 & l3 & l4 & l5 & l6 & l7 & l8 & l9 & l10 & l11 & l12 & l13 & l14 & l15 & LBC). unfold locb_cellsA, PJ_LOC_LO_A in LBC.
  unfold ios_cellsX in IOS.
  destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.

  assert (RL : ro_cells asegs m 0x146aa [CB 1 [Z_to_bv 8 0]])
    by (apply (ro_cells_image asegs m 0x146aa [Z_to_bv 8 0] MI); [vm_compute; reflexivity | lia | cbn; lia]).
  do 3 lstep.
  carve_frame 240%nat ST.
  do 14 lstep.
  do 3 lstep.
  lstep.
  lit_words.
  do 3 lstep.
  lazymatch type of FR with rw_cells _ _ _ (CB 136 ?x :: _) => set (jq := x) in FR; clearbody jq end.
  retype_at FR 1%nat 1%nat [CB 8 [Z_to_bv 8 37; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]].
  lstep.
  replace (zx32 (Z_to_bv 64 4098)) with (Z_to_bv 64 4098) in * by (apply bv_eq; vm_compute; reflexivity).
  lit_reg (bv_unsigned (Z_to_bv 64 4098) ≪ 52)%Z.
  if_false.
  do 2 lstep.
  lstep.
  if_false.
  do 3 lstep.
  lstep.
  if_true.
  do 6 lstep.
  lstep.
  lit_words.
  lstep.
  lstep.
  if_false.
  do 5 lstep.
  lstep.
  if_false.
  lstep.
  lstep.
  if_true.
  lstep.
  lstep.
  if_true.
  lstep.
  if_true.
  lstep.
  lstep.
  do 2 lstep.
  do 2 lstep.
  lstep.
  if_false.
  lstep.
  lazymatch type of FR with rw_cells _ _ _ (CB 96 ?x :: _) => set (jl := x) in FR; clearbody jl end.
  lazymatch type of FR with rw_cells _ _ _ (_ :: _ :: CB 32 ?x :: _) => set (jn := x) in FR; clearbody jn end.
  retype_at FR 3%nat 5%nat [CB 8 [Z_to_bv 8 37; Z_to_bv 8 46; Z_to_bv 8 42; Z_to_bv 8 103; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]].
  retype_at IOS 3%nat 1%nat [C4 (Z_to_bv 64 6); C4 (Z_to_bv 64 0)].
  lstep.
  replace (sx32 (Z_to_bv 64 6)) with (Z_to_bv 64 6) by (vm_compute; reflexivity).
  retype_at IOS 3%nat 2%nat [C8 (Z_to_bv 64 6)].
  do 5 lstep.
  lstep.

  takeZ FR 2%nat (bv_unsigned sp + -136)%Z FRA.
  takeZ FR 1%nat (bv_unsigned sp + -104)%Z NARC. takeZ FR 1%nat (bv_unsigned sp + -96)%Z FMT8.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (rw_cells_CB_cut3 mm (bv_unsigned sp + -136)%Z 32 jn 2 30 ltac:(lia) ltac:(lia) ltac:(lia) NARC) as (jg & jnar & j0 & GAP & NAR & _) end.
  clear NARC. change (Z.to_nat 2) with 2%nat in GAP. change (Z.to_nat 30) with 30%nat in NAR.
  replace (bv_unsigned sp + -136 + 2)%Z with (bv_unsigned sp + -134)%Z in NAR by lia.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (FMTB : bytes_at asegs mm (bv_unsigned sp + -104) (zb FMT_g)) end.
  { pose proof (rw_cells_bytes_at _ _ _ _ FMT8) as B. cbn [cells_bytes cbytes app] in B.
    pose proof (bytes_at_sub _ _ _ 0 5 B ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as B5. cbv [firstn skipn Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in B5.
    replace (bv_unsigned sp + -104 + 0)%Z with (bv_unsigned sp + -104)%Z in B5 by lia. exact B5. }

  destruct (fmt_fp_total_g6 (bv_unsigned dw)) as (txt & nc & HF & HL & HNC & HG).
  pose proof (printf_model_g _ _ _ HF HL ltac:(lia)) as MODEL.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (np_afacts_munch _ lo (bv_unsigned sp) lo (bv_unsigned sp) m mm AF0 MU WM ltac:(lia) ltac:(lia) ZONE) as (IC1 & STKC1 & ROD1 & RODFP1 & IFX1 & PCTX1 & PF1) end.
  call_sp (snl_proof RIP PCOK2_el (ivsn_proof RIP) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fc _
             (bv_unsigned sp + -134)%Z 30%Z 0x34a18%Z (bv_unsigned sp + -104)%Z 30%nat jnar FMT_g [PA_i 6; PA_g (f128_of_d (bv_unsigned dw))] lo canary nc txt);
    [ reflexivity | reflexivity | reflexivity | reflexivity | exact TP | lia | exact TPC | exact NAR | exact FMTB
    | unfold FMT_g; repeat (apply Forall_cons; [lia|]); apply Forall_nil
    | vm_compute; reflexivity
    | intros m_; cbn [args_ok arg_ok]; split; [split; [lia | rewrite unsigned_lit by lia; reflexivity] | split; [rewrite <- HDW; reflexivity | exact I]]
    | exact MODEL
    | apply (fpcalls_g RIP)
    | rewrite <- (Nat2Z.id (length txt)); change (Z.of_nat (length txt)) with (zlength txt); rewrite HL; lia | lia | lia | exact ST | lia | unfold GLOBALS_TOP; lia | lia
    | split; [exact SSP1 | exact SSP2] | assumption | exact FRM
    | lia | change (zlength FMT_g) with 5%Z; lia | change (zlength FMT_g) with 5%Z; lia | lia | lia
    | lia | exact SP16' | exact HSH | exact IC1
    | intros p n' Hp Hn; apply STKC1; lia
    | apply STKC1; [lia| change (zlength FMT_g) with 5%Z; lia]
    | exact ROD1
    | apply STKC1; [lia| unfold zlength in HL |- *; lia]
    | right; unfold SHADOW_HI, kHighShadowEnd in *; lia
    | exact RODFP1 | exact IFX1
    | intros m' MU' WM'; apply (pcok2_g m' (bv_unsigned dw) _ _ _ lo nc txt); [exact MODEL| lia| exact HL| lia| lia| lia| |];
      [ apply (pctx_munch _ _ m' PCTX1 MU' WM'); intros x Hx; unfold in_PCR in Hx; cbn [outside]; unfold kHighShadowEnd in *; lia
      | destruct PF1 as [PF1a PF1b]; split;
        [ apply (pfcells_munch _ _ m' PF1a MU' WM'); intros x Hx; unfold in_PFR in Hx; cbn [outside]; unfold kHighShadowEnd in *; lia
        | apply (ro_cells_agree asegs _ m' _ _ PF1b); apply (agree_of_munch _ _ m' _ MU'); intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [outside]; unfold kHighShadowEnd in *; lia ] ]
    | ].
  rename PC into FRM1. rename PC0 into FOK. rename PC1 into ST. rename PC2 into SSP. rename PC3 into NARO. rename POST into TPC1. rename MI0 into MI.
  clear SSP1 SSP2 MODEL FMTB. destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
  do 2 lstep.
  rewrite lts_small by lia. replace (29 <? nc)%Z with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb]. try if_true.
  do 4 lstep.
  lit_words. replace (zx32 (Z_to_bv 64 4098)) with (Z_to_bv 64 4098) in * by (apply bv_eq; vm_compute; reflexivity).
  do 5 lstep.
  lit_reg (Z.land (bv_unsigned (Z_to_bv 64 4098)) 176)%Z.
  if_false.
  lstep.
  lstep.
  if_true.
  lstep.
  do 2 lstep.
  bru true.
  do 4 lstep.
  lstep.
  carve_frame 16%nat ST.
  do 9 lstep.
  if_true.
  do 4 lstep.
  release_frame FR0 ST (bv_unsigned sp + -240)%Z.

  apply (rw_cells_split_CB asegs _ _ [CB 8 (firstn 8 jl); C8 (Z_to_bv 64 EL_IMP)] 80 (skipn 16 jl) [C8 (Z_to_bv 64 (bv_unsigned sp + -134))] [8; 8; 7; 57]%nat) in FRA; [|reflexivity].
  cbn [mk_CB_cells app] in FRA. forget_junk FRA.
  takeZ FRA 1%nat (bv_unsigned sp + -232)%Z F0. takeZ FRA 1%nat (bv_unsigned sp + -224)%Z PLOC.
  takeZ FRA 1%nat (bv_unsigned sp + -216)%Z POE. takeZ FRA 1%nat (bv_unsigned sp + -208)%Z POP.
  takeZ FRA 1%nat (bv_unsigned sp + -201)%Z GAP7. takeZ FRA 1%nat (bv_unsigned sp + -144)%Z OBUF. rename FRA into NBP.

  apply (rw_cells_split_CB asegs _ _ [] 30 _ [] [Z.to_nat nc; Z.to_nat (30 - nc)]%nat) in NARO; [|cbn [sum_nat]; lia].
  cbn [mk_CB_cells app] in NARO.
  assert (LZT : length (zb txt) = Z.to_nat nc) by (unfold zb; rewrite length_map; unfold zlength in HL; lia).
  rewrite firstn_app, LZT, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 in NARO by lia.
  destruct (rw_cells_split_n asegs _ _ _ 1 (bv_unsigned sp + -134 + nc)%Z NARO ltac:(cbn [firstn cells_size csize]; lia)) as [SRC NREST]. clear NARO.
  cbn [firstn skipn] in SRC, NREST. forget_junk NREST.
  do 7 lstep.
  lstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ ?fcx _ _ _) =>
  call_sp (wgf_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fcx _ lo
             (bv_unsigned sp + -134)%Z (bv_unsigned sp + -134)%Z (bv_unsigned sp + -134 + nc)%Z (bv_unsigned sp + -201)%Z 57%Z
             (bv_unsigned sp + -216)%Z (bv_unsigned sp + -224)%Z (bv_unsigned sp + -232)%Z (zb txt) _ _ _) end;
    [ exact ST | lia | lia
    | replace (bv_unsigned sp + -134 + nc - (bv_unsigned sp + -134))%Z with nc by lia; exact SRC
    | apply gchb_zb; exact HG
    | lia | lia | lia | exact OBUF | exact POP | exact POE | exact PLOC
    | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia
    | dlia | dlia | dlia | dlia | dlia | dlia
    | do 15 eexists; exact LBC
    | exact DCC' || (split; [exact VT | split; [exact WS | split; [exact WS2 | split; [exact NPT | split; [exact NPV | split; [exact GNP | exact GCT]]]]]])
    | assumption | ].
  rename MI0 into MI. rename PC into ST. rename PC0 into OBUF. rename PC1 into POP. rename PC2 into POE. rename POST into LB.
  destruct LB as (k1 & k2 & k3 & k4 & k5 & k6 & k7 & k8 & k9 & k10 & k11 & k12 & k13 & k14 & k15 & LBC2). unfold locb_cellsA, PJ_LOC_LO_A in LBC2.
  do 2 lstep.
  lstep.
  if_true.
  do 6 lstep.
  lstep.
  lazymatch type of OBUF with rw_cells _ ?mm _ [CB _ ?jb] =>
    assert (LJB : length jb = 57%nat) by (destruct OBUF as [[[LJ _] _] _]; exact LJ);
    pose proof (rw_cells_bytes_at _ _ _ _ OBUF) as OBB; cbn [cells_bytes cbytes app] in OBB; rewrite app_nil_r in OBB;
    pose proof (bytes_at_sub mm _ _ 0 nc OBB ltac:(lia) ltac:(lia) ltac:(rewrite LJB; lia)) as OBS;
    replace (bv_unsigned sp + -201 + 0)%Z with (bv_unsigned sp + -201)%Z in OBS by lia; clear OBB end.

  replace (bv_unsigned sp + -201 + (bv_unsigned sp + -134 - (bv_unsigned sp + -134)))%Z with (bv_unsigned sp + -201)%Z by lia.
  replace (bv_unsigned sp + -201 + (bv_unsigned sp + -134 + nc - (bv_unsigned sp + -134)))%Z with (bv_unsigned sp + -201 + nc)%Z by lia.
  lazymatch type of OBS with context [skipn (Z.to_nat 0) ?l] => change (skipn (Z.to_nat 0) l) with l in OBS end.
  change (Z.to_nat 57) with 57%nat in OBUF.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (rw_cells_glue asegs mm _ _ _ _ SRC NREST ltac:(cbn [cells_size csize]; lia)) as NARB;
    destruct (rw_cells_forget asegs mm _ _ NARB) as [jnar2 NAR2]; clear NARB SRC NREST end.
  cbn [cells_size csize app] in NAR2.
  replace (Z.to_nat nc + (Z.to_nat (30 - nc) + 0))%nat with 30%nat in NAR2
    by (rewrite Nat.add_0_r, <- Z2Nat.inj_add by lia; replace (nc + (30 - nc))%Z with 30%Z by lia; reflexivity).
  glueZ F0 PLOC. glueZ F0 POE. glueZ F0 POP. glueZ F0 GAP7. glueZ F0 OBUF. glueZ F0 NBP. glueZ F0 GAP. glueZ F0 NAR2. glueZ F0 FMT8.
  destruct (rw_cells_forget asegs _ _ _ F0) as [jf JF]. cbn [cells_size csize Nat.add] in JF.
  apply evt_done. unfold npd1_post.
  exists nc. do 14 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; [exact FRM1|].
  split; [intros k Hk H8; rewrite (FOK k Hk); rewrite freg_get_other; [reflexivity| apply (proj2 (Z.eqb_neq _ _)); apply not_eq_sym; exact H8]|].
  split; [exact ST|]. split; [split; [exact SSP1| exact SSP2]|].
  split; [exact TPC1|]. split; [do 15 eexists; exact LBC2|].
  split; [lia|]. split; [| split; [exact OBS| split; [exact JF| exact FR]]].
  rewrite firstn_length_le by (rewrite LJB; lia). lia.
Qed.
End Seg1.

Lemma npd_seg2 : forall (q : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 xs0 xs1 xs2 xs5 xs6 xs7 xs8 xs9 fs8 : word)
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (jf : list byte),
  stk asegs m lo (q + -240) -> (lo <= q + -240)%Z -> (q <= 2^47)%Z -> (0 <= bv_unsigned a0)%Z ->
  rw_cells asegs m (q + -240) [CB 144 jf] ->
  rw_cells asegs m (q + -96) [C8 fs8; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  mem_inv asegs m ->
  evt asegs (fun ms' => ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                (bvmap_set 8 fs8 F) (ret_pc ra) fc None m (seg_rom asegs)
                       /\ stk asegs m lo q)
      (MS (mkR (Z_to_bv 64 0x11946c) (Z_to_bv 64 (q + -240)) gp tp t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7
               xs2 (Z_to_bv 64 0) (Z_to_bv 64 0) xs5 xs6 xs7 xs8 xs9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x11946c) fc None m (seg_rom asegs)).
Proof.
  intros until jf. intros ST LO1 SPH A0 JF FR MI.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as (? & ? & _); lia).
  assert (EQ : bv_unsigned (Z_to_bv 64 (q + -240)) = (q + -240)%Z) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(lo, q)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lstep.
  lstep. if_true.
  lstep. if_true.
  do 15 lstep.
  glueZ JF FR. release_frame JF ST q. apply evt_done. split; [| exact ST].
  all: f_equal; f_equal; apply bv_eq; rewrite ?unsigned_lit by lia; lia.
Qed.

Section Stmt.
Variable RT : rt_sig.
Variable PMc : Model -> Prop.
Definition EL_NPD_STACK_A : Z := 10752 + RT_STACK.

Definition np_d_cpsA : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (OS q lo fO fill : Z) (kO : nat) (pb dw : word) (pp ep : Z) (dum j148 j284 : list byte)
         (ra gp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  fdfs_only PMc -> mat_stable PMc ->
  In (fO, kO) (rt_frames RT Σ) -> (fO <= OS)%Z -> (OS + 288 <= fO + fs_size kO - 8)%Z -> (OS mod 16 = 0)%Z ->
  rw_cells asegs m OS (sb_cellsX pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) dum) -> PUTINV OS pp ep ->
  rw_cells asegs m (OS + 128) [C8 (Z_to_bv 64 0x164650)] -> rw_cells asegs m (OS + 136) (ios_cellsX OS 0x164678 0x1002 0 fill j148 j284) ->
  bytes_at asegs m (shad OS) (repeat z8 36) -> (0 <= fill < 256)%Z -> reg_get F (Z_to_bv 5 10) = dw ->
  el_tploc m -> io_ssp m -> frm0 fc -> LOCBA m ->
  ART RT Σ m -> mem_inv asegs m -> stk asegs m lo q -> (rt_sp0 RT Σ - STACK_WIN <= lo)%Z -> (lo + EL_NPD_STACK_A <= q)%Z ->
  (q + 16 <= USTACK_TOP)%Z -> (q mod 32 = 16)%Z ->
  (Z.of_nat (length (rt_frames RT Σ)) + 1 <= FRAMES_TOT)%Z -> (1 <= rt_credit RT Σ)%Z ->
  (forall (Σ' : rts RT) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (F' : bvmap 5 word) (fc' : bv 32) m' (pb' : word) (pp' ep' : Z) (dum' : list byte),
     ART RT Σ' m' -> mem_inv asegs m' -> stk asegs m' lo q ->
     rw_cells asegs m' OS (sb_cellsX pb' (Z_to_bv 64 pp') (Z_to_bv 64 ep') dum') -> PUTINV OS pp' ep' ->
     rw_cells asegs m' (OS + 128) [C8 (Z_to_bv 64 0x164650)] -> rw_cells asegs m' (OS + 136) (ios_cellsX OS 0x164678 0x1002 0 fill j148 j284) ->
     bytes_at asegs m' (shad OS) (repeat z8 36) -> el_tploc m' -> LOCBA m' -> frm0 fc' ->
     rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ -> (rt_credit RT Σ - 1 <= rt_credit RT Σ')%Z ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(OS + 40, OS + 128); (OS + 160, OS + 168); (0x6a7e38, 0x6a7e38 + 8)]%Z m m' ->
     aevt RT PMc Σ' K (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 TPV_A) t0' t1' t2' s0 s1 (Z_to_bv 64 OS) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F' (ret_pc ra) fc' None m' (seg_rom asegs))) ->
  aevt RT PMc Σ K (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 TPV_A) t0 t1 t2 s0 s1 a0 (Z_to_bv 64 OS) (Z_to_bv 64 (OS + 136)) (Z_to_bv 64 fill) a4 a5 a6 a7
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 EL_NP_D) fc None m (seg_rom asegs)).
End Stmt.

Section Lift.
Local Open Scope Z_scope.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis RC2 : rt_contracts2 RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis RIP : rip_stmt.
Hypothesis AF_IC : forall Σ m, ART RT Σ m -> ictx m.
Hypothesis AF_SHW : forall Σ m p n, ART RT Σ m -> (0 < n)%Z -> rng_class RT Σ p n -> qc_words m p n /\ region_in_mem p n.
Hypothesis DCC : forall Σ m, ART RT Σ m -> el_dccA m.
Hypothesis AF_NP : forall Σ m, ART RT Σ m -> rod_chk m /\ rod_chk_fp m /\ ifx_real m /\ pctx m /\ pfcells6 m.
Local Notation PAD := (padX_okA RT AF RC RC2 PMc FDO MST RIP AF_IC AF_SHW DCC).

Local Ltac ul := unfold EL_NPD_STACK_A, EL_NP_STACK_A, EL_PAD_STACK_A, EL_XSPUTN_DEPTH, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, kHighShadowEnd, SHADOW_LO, SHADOW_HI in *; lia.

Theorem np_d_okA : np_d_cpsA RT PMc.
Proof using AF RC RC2 FDO MST RIP AF_IC AF_SHW DCC AF_NP.
  unfold np_d_cpsA. intros until m. intros FDO' MST' INF FLO FHI AL16 SB PI V128 IOS SHZ RF HDW TPC SSP FRM LB ART0 MI ST LOW LOR SPT Q32 FRB CRB HK.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_frames_range RT AF Σ m fO kO ART0 INF) as (F0 & FTOP & _ & FLIVE).
  pose proof (af_frames_align RT AF Σ m fO kO ART0 INF) as (_ & FSEG).
  remember (fs_size kO) as FSZ eqn:EFSZ.
  assert (LO0 : 0 <= lo) by (destruct ST as (? & ? & _); lia).
  assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; ul).
  destruct SSP as (canary & SSP1 & SSP2).
  destruct (stk_split asegs m lo (lo + 64) q ST ltac:(ul)) as [STlo ST64].
  assert (AFX : np_afacts (lo + 64) q m).
  { destruct (AF_NP Σ m ART0) as (R1 & R2 & R3 & R4 & R5). split; [exact (AF_IC Σ m ART0)|]. split; [| split; [exact R1| split; [exact R2| split; [exact R3| split; [exact R4| exact R5]]]]].
    apply (stk_chkr RT AF AF_SHW Σ m (lo + 64) q ART0 ltac:(ul) ltac:(ul)). }

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut.
  { eapply (npd_seg1 RIP ra (Z_to_bv 64 q) gp (Z_to_bv 64 TPV_A) t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (lo + 64) OS fill dw j148 j284 canary);
      rewrite ?EQ; first [exact ST64| exact IOS| exact RF| exact HDW| exact TPC| split; [exact SSP1| exact SSP2]| exact FRM| exact LB| exact (DCC Σ m ART0)| exact MI| exact AFX| reflexivity| ul| idtac].
    all: clear - Q32; Z.div_mod_to_equations; lia. }
  cbv beta. intros ms1 PO. unfold npd1_post in PO. rewrite !EQ in PO.
  destruct PO as (nc & x5 & x6 & x7 & x16 & x17 & x28 & x29 & x30 & x31 & F1 & fc1 & ob & jf & m1 & -> & MU1 & WM1 & MI1 & FRM1 & FOK1 & ST1 & SSP' & TPC1 & LB1 & NC & LOB & OBS & JF1 & FR1).
  apply evt_done.
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 (lo + 64) ART0 ltac:(ul)); [| exact WM1]. intros a Ha. apply MU1. cbn [outside].
    split; [intros Hr; apply Ha; left; ul|]. split; [| exact I]. intros Hr. apply Ha. right; left. apply client_static_intro. lia. }
  assert (AG1 : forall P : Z -> Prop, (forall x, P x -> (x < lo + 64 \/ q <= x) /\ ~ (0x6a7e38 <= x < 0x6a7e40)) -> agree_on P m m1).
  { intros P HP a Ha. apply MU1. destruct (HP _ Ha) as [H1 H2]. cbn [outside]. split; [lia| split; [lia| exact I]]. }
  assert (OSLO : OS + 288 <= lo) by (clear - FHI FTOP LOW; ul).
  assert (SB1 : rw_cells asegs m1 OS (sb_cellsX pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) dum)).
  { eapply rw_cells_agree_nw; [exact SB|]. apply AG1. intros x Hx. cbn [sb_cellsX cells_size csize Nat.add] in Hx. unfold SEGTOP_A in FSEG. lia. }
  assert (IOS1 : rw_cells asegs m1 (OS + 136) (ios_cellsX OS 0x164678 0x1002 0 fill j148 j284)).
  { eapply rw_cells_agree_nw; [exact IOS|]. apply AG1. intros x Hx. cbn [ios_cellsX cells_size csize Nat.add] in Hx. unfold SEGTOP_A in FSEG. lia. }
  assert (SHZ1 : bytes_at asegs m1 (shad OS) (repeat z8 36)).
  { eapply bytes_at_agree; [exact SHZ|]. apply AG1. intros x Hx. rewrite repeat_length in Hx. unfold shad, SHB in Hx. unfold SEGTOP_A in FSEG. split; [| Z.div_mod_to_equations; lia].
    left. clear - Hx FLO FHI FTOP LOW SP0W F0. unfold STACK_WIN in *. Z.div_mod_to_equations. lia. }
  pose proof IOS1 as IOSc. unfold ios_cellsX in IOSc. takeZ IOSc 4%nat (OS + 160)%Z IOSa. takeZ IOSc 1%nat (OS + 168)%Z WID1. rename IOSc into IOSb.
  assert (V1 : rw_cells asegs m1 (OS + 128) [C8 (Z_to_bv 64 0x164650)]).
  { eapply rw_cells_agree_nw; [exact V128|]. apply AG1. intros x Hx. cbn [cells_size csize Nat.add] in Hx. unfold SEGTOP_A in FSEG. lia. }
  assert (HULL1 : os_hullA m1 OS).
  { split; [| exact SHZ1]. pose proof SB1 as SBc. unfold sb_cellsX in SBc. pose proof IOS1 as IOSc. unfold ios_cellsX in IOSc. pose proof V1 as V1c.
    glueZ SBc V1c. glueZ SBc IOSc. destruct (rw_cells_forget asegs m1 OS _ SBc) as (bo & Hb). exists bo. exact Hb. }
  assert (ST1f : stk asegs m1 lo (q + -240)).
  { apply (stk_merge asegs m1 lo (lo + 64) (q + -240)); [| exact ST1| ul].
    eapply stk_agree_nw; [exact STlo|]. apply AG1. intros x Hx. cbv beta in Hx. clear - Hx SP0W LOW. unfold STACK_WIN in *. lia. }
  eapply (PAD Σ K OS (q + -201)%Z nc nc (q + -240)%Z lo fO fill pp ep kO pb dum ob);
    [exact FDO| exact MST| exact INF| exact FLO| rewrite <- EFSZ; exact FHI| exact AL16
    | exact SB1| exact PI| exact WID1| exact HULL1
    | exact OBS| lia| lia| lia| ul
    | apply (af_acc_stack RT AF Σ m1 _ _ ART1); ul
    | right; left; ul
    | right; ul
    | lia
    | exact ART1| exact MI1| exact ST1f| ul| ul| ul| clear - Q32; Z.div_mod_to_equations; lia
    | exact FRB| exact CRB|].
  intros Σ2 y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 F2 m2 pb' pp' ep' dum' ART2 MI2 ST2 HULL2 SB2 PI2 WID2 LV2 FRS2 SP2 CR2 PRES2.
  rewrite (ret_pc_even 0x11946c) by lia.
  assert (AG2 : forall P : Z -> Prop,
            (forall x, P x -> ((q + -240 <= x < q) \/ (PJ_LOC_LO_A <= x < PJ_LOC_HI_A) \/ (x = 0x6a7e38 \/ 0x6a7e38 < x < 0x6a7e40) \/ (OS <= x < OS + 40) \/ (OS + 128 <= x < OS + 160) \/ (OS + 168 <= x < OS + 288))%Z) ->
            agree_on P m1 m2).
  { intros P HP a Ha. apply PRES2.
    - destruct (HP _ Ha) as [H|[H|[H|[H|[H|H]]]]].
      + left. ul.
      + right; left. apply client_static_intro. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in H. lia.
      + right; left. apply client_static_intro. lia.
      + right; right; right; left. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia].
      + right; right; right; left. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia].
      + right; right; right; left. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia].
    - pose proof (HP _ Ha) as H. clear - H OSLO LOR FSEG FLO. cbn [outside]. unfold PJ_LOC_LO_A, PJ_LOC_HI_A, EL_NPD_STACK_A, RT_STACK, SEGTOP_A in *. split; [lia| split; [lia| exact I]]. }
  assert (JF2 : rw_cells asegs m2 (q + -240) [CB 144 jf]) by (eapply rw_cells_agree_nw; [exact JF1|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia).
  lazymatch type of FR1 with rw_cells _ _ _ ?cs => assert (FR2 : rw_cells asegs m2 (q + -96) cs) by (eapply rw_cells_agree_nw; [exact FR1|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia) end.
  assert (V2 : rw_cells asegs m2 (OS + 128) [C8 (Z_to_bv 64 0x164650)]) by (eapply rw_cells_agree_nw; [exact V1|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia).
  lazymatch type of IOSa with rw_cells _ _ _ ?cs => assert (IOSa2 : rw_cells asegs m2 (OS + 136) cs) by (eapply rw_cells_agree_nw; [exact IOSa|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia) end.
  lazymatch type of IOSb with rw_cells _ _ _ ?cs => assert (IOSb2 : rw_cells asegs m2 (OS + 168) cs) by (eapply rw_cells_agree_nw; [exact IOSb|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia) end.
  assert (TPC2 : el_tploc m2) by (eapply rw_cells_agree_nw; [exact TPC1|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia).
  assert (LB2 : LOCBA m2) by (apply (LOCBA_agree m1 m2 LB1); apply AG2; intros x Hx; lia).
  pose proof IOSa2 as IOS2. glueZ IOS2 WID2. glueZ IOS2 IOSb2. change (rw_cells asegs m2 (OS + 136) (ios_cellsX OS 0x164678 0x1002 0 fill j148 j284)) in IOS2.
  destruct HULL2 as [_ SHZ2].

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut.
  { eapply (npd_seg2 q ra gp (Z_to_bv 64 TPV_A) y0 y1 y2 s0 s1 (Z_to_bv 64 OS) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6
              _ _ _ _ _ _ _ _ _ F2 fc1 m2 lo jf); [exact ST2| ul| ul| rewrite unsigned_lit by ul; ul| exact JF2| exact FR2| exact MI2]. }
  cbv beta. intros ms3 [-> ST3]. apply evt_done.
  assert (SB2x : rw_cells asegs m2 OS (sb_cellsX pb' (Z_to_bv 64 pp') (Z_to_bv 64 ep') dum')) by (unfold sb_cellsX; exact SB2).
  eapply (HK Σ2 y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 _ fc1 m2 pb' pp' ep' dum' ART2 MI2 ST3 SB2x PI2 V2 IOS2 SHZ2 TPC2 LB2 FRM1 LV2 FRS2 SP2);
    [clear - CR2; lia|].
  intros a Ha Ho. cbn [outside] in Ho. destruct Ho as (Ho1 & Ho2 & Ho3 & _).
  rewrite (PRES2 a); [| apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia]| cbn [outside]; split; [exact Ho1| split; [exact Ho2| exact I]]].
  apply MU1. cbn [outside]. split; [| split; [exact Ho3| exact I]]. intros Hr. destruct (aclient_split_c RT AF Σ m q _ ART0 Ha); ul.
Qed.
End Lift.
