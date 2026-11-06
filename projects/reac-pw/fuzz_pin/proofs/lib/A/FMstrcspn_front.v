(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_identity/lib/A/FMstrlen.v at 6ebe35ba632; the strlen
   wrapper's composition (entry phase, musl call, range check, epilogue) becomes the front half of the strcspn
   wrapper's walk: the entry phase up to musl __strchrnul's loops, the loops, and the phase from their exit to
   the range check of the set at 0x42d38. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
Require Import
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AB1v
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AE34
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AF0l
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AF0m
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AF0x
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AB1w
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AE20
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AE2y
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AE39
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AE3a.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import FMcs0 FMstrcspn_front0.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.Rt Require Import WrapRo WrapRoM.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require PPgWrap.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Hypothesis MUSL : CS_MUSL_LOOPS.

(* a symbolic phase that stops because the run reached its stop pc *)
Lemma phaseT : forall (W : world tfibsegs) (md0 : Model) E ss ss' ms stop (Q : world tfibsegs -> config -> Prop),
st_ok tfibsegs E ss (restrict (w_H W) ms) ->
sym_run_toN tfibsegs tbl_cs FUEL stop ss = (ss', RS_running) ->
(forall ms1 mat1, st_ok tfibsegs E ss' (restrict (w_H W) ms1) ->
 frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) ->
 SRr tfibsegs W (mkCfg ms1 (with_vm_backing (m_vm_lazy md0) mat1 md0)) Q) ->
SRr tfibsegs W (mkCfg ms md0) Q.
Proof.
intros W md0 E ss ss' ms stop Q HS Hrun K.
eapply SRr_bind; [exact (cs_phase_to W E stop ss ss' RS_running ms md0 HS Hrun)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & _).
exact (K ms1 mat1 HS1 HF1).
Qed.
(* a symbolic phase that stops on an undecided branch *)
Lemma phaseS : forall (W : world tfibsegs) (md0 : Model) E ss ss' ms stop why (Q : world tfibsegs -> config -> Prop),
st_ok tfibsegs E ss (restrict (w_H W) ms) ->
sym_run_toN tfibsegs tbl_cs FUEL stop ss = (ss', RS_stopped why) ->
(forall ms1 mat1, st_ok tfibsegs E ss' (restrict (w_H W) ms1) ->
 frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) ->
 SRr tfibsegs W (mkCfg ms1 (with_vm_backing (m_vm_lazy md0) mat1 md0)) Q) ->
SRr tfibsegs W (mkCfg ms md0) Q.
Proof.
intros W md0 E ss ss' ms stop why Q HS Hrun K.
eapply SRr_bind; [exact (cs_phase_to W E stop ss ss' (RS_stopped why) ms md0 HS Hrun)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & _).
exact (K ms1 mat1 HS1 HF1).
Qed.
(* one byte load whose value the walk names *)
Lemma lbuR : forall (W : world tfibsegs) (md0 : Model) E ss ms (rd rs : bv 5) (w : Z) (imm : bv 12)
(h v : Z) (t : sv) (K : nat) (Q : world tfibsegs -> config -> Prop),
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_atoms_lt K ss = true ->
clookup tbl_cs (ss_pc ss) = Some w -> decode_any (Z_to_bv 32 w) = Some (Load SZ1 false rd rs imm, 4) ->
bv_eqb rd 0%bv = false ->
v_addi (sv_denot E (sr_get (ss_regs ss) rs)) (bv_signed imm) = Z_to_bv 64 h -> 0 <= h < 2 ^ 64 ->
aview tfibsegs (w_H W) (ms_mem ms) h = Some v -> sv_denot E t = Z_to_bv 64 v ->
(forall ms1 mat1, st_ok tfibsegs E (set_regs_pc ss [(rd, t)] (ss_pc ss + 4)) (restrict (w_H W) ms1) ->
 ms_mem ms1 = ms_mem ms ->
 SRr tfibsegs W (mkCfg ms1 (with_vm_backing (m_vm_lazy md0) mat1 md0)) Q) ->
SRr tfibsegs W (mkCfg ms md0) Q.
Proof.
intros W md0 E ss ms rd rs w imm h v t K Q HS Hrv Hat Hlk Hdec Hrd Hrs Hh Hv Ht Kc.
eapply SRr_bind; [exact (cs_lbu W E ss ms md0 rd rs w imm h v t K HS Hrv Hat Hlk Hdec Hrd Hrs Hh Hv Ht)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HM1).
exact (Kc ms1 mat1 HS1 HM1).
Qed.

Theorem cs_front : forall ly S (W : world tfibsegs) regs mem md x y (str : list byte) (c : byte),
ecall_pre tfibsegs B ly S W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs ->
(forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> getr regs 11 = w64 y ->
PPgWrap.awrap_str tfibsegs W mem regs x str -> PPgWrap.awrap_str tfibsegs W mem regs y [c] ->
aro_unowned tfibsegs B (aview tfibsegs (w_H W) mem) ->
SRr tfibsegs W (cfg_at tfibsegs CS_ENTRY regs mem md)
(fun W' c' => W' = W /\ exists regs1 mem1 md1, c' = cfg_at tfibsegs CS1_ENTRY regs1 mem1 md1 /\
cs_mid B ly S W regs mem md x y (Z.of_nat (PPgWrap.cspn_len [c] str)) regs1 mem1 md1).
Proof.
intros ly S W regs mem md x y str c HPRE Hslo2 Hpres2 G10 G11 HSTR HSET Haro.
pose proof HPRE as (HAR & Hret & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
unfold ESTACK in Hslo2, Hpres2, Hslo, HpresE.
set (sp0 := spZ regs) in *.
assert (Hsp : 2 ^ 44 <= sp0 <= 2 ^ 47) by lia.
assert (HIMG : AF0x.TFIB_IMG_END <= 2 ^ 40) by (vm_compute; discriminate).
assert (Hal16b : (sp0 - CS_WIN) mod 16 = 0)
by (unfold CS_WIN; replace (sp0 - 2256) with (sp0 + (-141) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16).
unfold PPgWrap.awrap_str in HSTR, HSET.
destruct HSTR as (Hx0 & HstrN & Hslen & Hxlen & Hgarr & Hsrc & Hband & Ham & Hrang & Hhull & Htail).
destruct HSET as (Hy0 & HsetN & Hylen1 & Hylen & Hgarr2 & Hsrc2 & Hband2 & Ham2 & Hrang2 & Hhull2 & Htail2).
assert (HL1 : Z.of_nat (length [c]) = 1) by reflexivity.
rewrite HL1 in Hylen1, Hylen, Hband2.
assert (Hcv : 0 < bv_unsigned c < 256).
{ pose proof (u8_range c) as Hc8.
  assert (Hne : bv_unsigned c <> 0).
  { intros H0. apply HsetN. cbn [In]. left. apply bv_eq. rewrite Z_to_bv_unsigned, H0.
    unfold bv_wrap. change (bv_modulus 8) with 256. reflexivity. }
  lia. }
assert (Hcl : forall l : list byte, (PPgWrap.cspn_len [c] l <= length l)%nat).
{ induction l as [|b t IH]; cbn [PPgWrap.cspn_len length]; [lia|]. destruct (existsb _ _); lia. }
assert (Hrk : 0 <= Z.of_nat (PPgWrap.cspn_len [c] str) <= Z.of_nat (length str))
by (pose proof (Hcl str); lia).
assert (Hamr : x + Z.of_nat (length str) + 1 <= 2 ^ 47 - 1)
by (pose proof Ham as Ham'; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham'; lia).
(* the three bands of addresses the walk never writes, with CS_WIN already in numerals *)
assert (LOW : forall a, 0 <= a < 2 ^ 43 -> ~ (sp0 - CS_WIN <= a < sp0)) by (unfold CS_WIN; lia).
assert (Hbandw : forall a, x <= a <= x + Z.of_nat (length str) -> ~ (sp0 - CS_WIN <= a < sp0)).
{ intros a Ha. pose proof (Hband a Ha) as Hq. unfold ESTACK in Hq. unfold CS_WIN. lia. }
assert (Hband2w : forall a, y <= a <= y + 1 -> ~ (sp0 - CS_WIN <= a < sp0)).
{ intros a Ha. pose proof (Hband2 a Ha) as Hq. unfold ESTACK in Hq. unfold CS_WIN. lia. }
assert (TAILW : forall a, x + Z.of_nat (length str) < a < x + Z.of_nat (length str) + 8 ->
~ (sp0 - CS_WIN <= a < sp0)).
{ intros a Ha. pose proof (Hband (x + Z.of_nat (length str)) ltac:(lia)) as Hq.
  unfold ESTACK in Hq. unfold CS_WIN. lia. }
remember (Z.of_nat (PPgWrap.cspn_len [c] str)) as rres eqn:Hrd.
assert (AVy : aview tfibsegs (w_H W) mem y = Some (bv_unsigned c)).
{ pose proof (garr8_av (w_H W) mem y (map (fun b : byte => bv_unsigned b) [c] ++ [0]) 0%nat Hgarr2
    ltac:(cbn [length map app]; lia)) as Hq.
  cbn [map app nth] in Hq. replace (y + Z.of_nat 0) with y in Hq by lia. exact Hq. }
assert (AVy1 : aview tfibsegs (w_H W) mem (y + 1) = Some 0).
{ pose proof (garr8_av (w_H W) mem y (map (fun b : byte => bv_unsigned b) [c] ++ [0]) 1%nat Hgarr2
    ltac:(cbn [length map app]; lia)) as Hq.
  cbn [map app nth] in Hq. replace (y + Z.of_nat 1) with (y + 1) in Hq by lia. exact Hq. }
destruct (guard_word (w_H W) mem) as (g & Hgv & Hgr).
pose proof (mconsts_of_aro B W mem TB Haro) as Hrom.
(* ---------------- the entry state ---------------- *)
set (EE := AE2y.Env regs [g; bv_unsigned c]).
assert (EEreg : forall i (rr : bv 5), Z.of_nat i = bv_unsigned rr -> ew EE i = getr regs rr)
by (intros; apply AE2y.Env_reg; assumption).
assert (EE2 : bv_unsigned (ew EE 2) = sp0) by (rewrite (EEreg 2%nat 2%bv eq_refl); reflexivity).
assert (EE10 : ew EE 10 = Z_to_bv 64 x) by (rewrite (EEreg 10%nat 10%bv eq_refl); exact G10).
assert (EE11 : ew EE 11 = Z_to_bv 64 y) by (rewrite (EEreg 11%nat 11%bv eq_refl); exact G11).
assert (EE32 : ew EE 32 = Z_to_bv 64 g) by (apply (AE2y.Env_x regs _ 0); reflexivity).
assert (EE33 : ew EE 33 = Z_to_bv 64 (bv_unsigned c)) by (apply (AE2y.Env_x regs _ 1); reflexivity).
assert (EE33u : bv_unsigned (ew EE 33) = bv_unsigned c) by (rewrite EE33; apply unsigned_lit_small; lia).
assert (FR : forall E ss (m m1 : word -> option byte), bv_unsigned (ew E 2) = sp0 -> win_chk (ss_mem ss) = true ->
frame_of E (ss_mem ss) m m1 -> forall z : word, ~ (sp0 - CS_WIN <= bv_unsigned z < sp0) -> m1 z = m z).
{ intros E ss m m1 HE2 Hw HF z Hz. apply HF. intros Hin.
  pose proof (in_wrange_single_b E (ss_mem ss) (bv_unsigned z) 2%nat (- CS_WIN) 0 sp0 Hw HE2 Hin) as X. lia. }
assert (HS0 : st_ok tfibsegs EE ssE (restrict (w_H W) (mkst regs (w64 CS_ENTRY) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssE. unfold EE, AE2y.Env.
  apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g; bv_unsigned c])) with EE.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [| apply Forall_cons].
    + unfold stkE. apply (region_ok_stack tfibsegs EE _ 2%nat sp0 (- CS_WIN));
        [exact EE2 | unfold CS_WIN; lia | lia |].
      intros a Ha. apply AF0x.apresent_writable; [unfold CS_WIN in *; lia|].
      apply HpresE. unfold CS_WIN in *. lia.
    + unfold grdR, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      split; [unfold CS_GUARD; lia|]. split; [unfold CS_GUARD; lia|].
      split; [intros o Ho; exfalso; lia|].
      apply Forall_cons; [| apply Forall_nil].
      eapply (chunk_ok_val tfibsegs EE (mrestrict (w_H W) mem) 0 CS_GUARD 8%N (SOff 32 0) g).
      * cbn [sv_denot]. rewrite EE32, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
      * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      * cbn [Z.of_N]. lia.
      * rewrite Z.add_0_l. exact Hgv.
    + exact (rodata_ok B TB cs_rodata ly S (w_H W) mem EE (cs_rodata_chk ly) (proj1 HAR)).
  - apply pairwise_disjoint_of_extents.
    unfold stkE, grdR, cs_rodata, icpt_rodata, ro_region, extent_of_region, CS_WIN, CS_GUARD.
    cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite EE2.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok factsE]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite EE2, EE33u. change (2 ^ 4) with 16. change (2 ^ 0) with 1.
    repeat split; first [exact Hal16 | apply Z.mod_1_r | lia]. }
(* ---------------- phase 1: the prologue, the runtime's init test, musl strcspn's prologue ---------------- *)
unfold cfg_at.
apply (phaseT W md EE ssE e1 _ A_LB1 _ HS0 r_e1). intros ms1 mat1 HS1 HF1.
destruct e1_f as (E1pc & E1rv & E1at & E1r9).
assert (M1 : forall z : word, ~ (sp0 - CS_WIN <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z)
by (intros z Hz; exact (FR EE ssE mem (ms_mem ms1) EE2 wc_ssE HF1 z Hz)).
assert (AV1y : aview tfibsegs (w_H W) (ms_mem ms1) y = Some (bv_unsigned c)).
{ rewrite (aview_same (w_H W) mem (ms_mem ms1) y); [exact AVy|].
  apply M1. rewrite unsigned_lit_small by lia. apply Hband2w. lia. }
apply (lbuR W _ EE e1 ms1 (11%bv : bv 5) (9%bv : bv 5) W_LB1 (0%bv : bv 12) y (bv_unsigned c) (SOff 33 0) 34%nat _
  HS1 E1rv E1at ltac:(rewrite E1pc; exact clk_lb1) dec_lb1 ltac:(vm_compute; reflexivity)
  ltac:(rewrite E1r9; cbn [sv_denot]; rewrite EE11, unsigned_lit_small by lia; rewrite Z.add_0_r, v_addi_lit;
        change (bv_signed (0%bv : bv 12)) with 0; rewrite Z.add_0_r; reflexivity)
  ltac:(lia) AV1y
  ltac:(cbn [sv_denot]; rewrite EE33u; rewrite Z.add_0_r; reflexivity)).
intros ms2 mat2 HS2 MM2. rewrite wvb_collapse. rewrite E1pc in HS2.
apply (phaseT W _ EE s1b e2 _ A_LB2 _ HS2 r_e2). intros ms3 mat3 HS3 HF3.
destruct e2_f as (E2pc & E2rv & E2at & E2r9).
assert (M3 : forall z : word, ~ (sp0 - CS_WIN <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (FR EE s1b (ms_mem ms2) (ms_mem ms3) EE2 wc_s1b HF3 z Hz), MM2. apply M1. exact Hz. }
assert (AV3y1 : aview tfibsegs (w_H W) (ms_mem ms3) (y + 1) = Some 0).
{ rewrite (aview_same (w_H W) mem (ms_mem ms3) (y + 1)); [exact AVy1|].
  apply M3. rewrite unsigned_lit_small by lia. apply Hband2w. lia. }
apply (lbuR W _ EE e2 ms3 (10%bv : bv 5) (9%bv : bv 5) W_LB2 (1%bv : bv 12) (y + 1) 0 (SLit 0) 34%nat _
  HS3 E2rv E2at ltac:(rewrite E2pc; exact clk_lb2) dec_lb2 ltac:(vm_compute; reflexivity)
  ltac:(rewrite E2r9; cbn [sv_denot]; rewrite EE11, unsigned_lit_small by lia; rewrite Z.add_0_r, v_addi_lit;
        change (bv_signed (1%bv : bv 12)) with 1; reflexivity)
  ltac:(lia) AV3y1 ltac:(reflexivity)).
intros ms4 mat4 HS4 MM4. rewrite wvb_collapse. rewrite E2pc in HS4.
apply (phaseS W _ EE s1c e3 _ CS_LOOP _ _ HS4 r_e3). intros ms5 mat5 HS5 HF5.
assert (M5 : forall z : word, ~ (sp0 - CS_WIN <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (FR EE s1c (ms_mem ms4) (ms_mem ms5) EE2 wc_s1c HF5 z Hz), MM4. apply M3. exact Hz. }
assert (HS5d : st_ok tfibsegs EE s1d (restrict (w_H W) ms5)).
{ unfold s1d. apply st_ok_add_cond; [exact HS5|].
  rewrite branch_ne_U. unfold cs_cmask. rewrite U_and_lit by lia.
  rewrite (U_atom EE 33 (bv_unsigned c)) by (first [rewrite EE33; reflexivity | lia]).
  rewrite U_lit by lia.
  replace (Z.land (bv_unsigned c) 255) with (bv_unsigned c)
    by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
  apply negb_true_iff. apply Z.eqb_neq. lia. }
apply (phaseT W _ EE s1d e4 _ CS_LOOP _ HS5d r_e4). intros ms6 mat6 HS6 HF6.
assert (M6 : forall z : word, ~ (sp0 - CS_WIN <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (FR EE s1d (ms_mem ms5) (ms_mem ms6) EE2 wc_s1d HF6 z Hz). apply M5. exact Hz. }
destruct e4_f as (E4pc & E4rv & E4r10 & E4r11 & E4r2 & E4r18 & E4keep).
assert (RD6 : forall rr : bv 5, getr (ms_regs ms6) rr = sv_denot EE (sr_get (ss_regs e4) rr))
by (intros rr; exact (st_ok_reg_denot (w_H W) EE e4 ms6 rr HS6)).
assert (P6 : forall a, sp0 - CS_WIN <= a < sp0 -> apresent (w_H W) (ms_mem ms6) a).
{ intros a Ha. destruct e4_r0_f as (Hb & Hwlo & Hwhi).
  apply (st_ok_window_apresent (w_H W) EE e4 ms6 0%nat e4_r0 a HS6 ltac:(rewrite e4_mem; reflexivity)).
  - rewrite Hb, Hwlo, Hwhi. cbn [base_val]. rewrite EE2. lia.
  - unfold CS_WIN in *. lia. }
assert (CKE : forall off v, has_chunk e4 off v = true ->
YP09.chunk_ok tfibsegs EE (mrestrict (w_H W) (ms_mem ms6)) sp0 (YP09.mkChunk off (CVal 8 v))).
{ intros off v Hc.
  pose proof (chunk_of_st (w_H W) EE e4 ms6 e4_r0 e4_rest off v HS6 e4_mem Hc) as Hok.
  destruct e4_r0_f as (Hb & _ & _). rewrite Hb in Hok. cbn [base_val] in Hok. rewrite EE2 in Hok. exact Hok. }
(* ---------------- phase 2: the loops of musl __strchrnul ---------------- *)
assert (R6x : getr (ms_regs ms6) 10 = w64 x).
{ rewrite (RD6 (10%bv : bv 5)), E4r10. cbn [sv_denot]. rewrite EE10, unsigned_lit_small by lia.
  rewrite Z.add_0_r. reflexivity. }
assert (R6c : getr (ms_regs ms6) 11 = Z_to_bv 64 (bv_unsigned c)).
{ rewrite (RD6 (11%bv : bv 5)), E4r11. unfold cs_cmask. rewrite denot_lit_U, U_and_lit by lia.
  rewrite (U_atom EE 33 (bv_unsigned c)) by (first [rewrite EE33; reflexivity | lia]).
  f_equal. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
assert (RDN : forall j, (j <= length str)%nat ->
rdn tfibsegs (mrestrict (w_H W) (ms_mem ms6)) (Z_to_bv 64 (x + Z.of_nat j)) 1 = Some [nth j (str ++ [NUL]) NUL]).
{ intros j Hj.
  assert (Hjl : (j < length (map (fun b : byte => bv_unsigned b) str ++ [0%Z]))%nat)
    by (rewrite length_app, length_map; cbn [length]; lia).
  destruct (Hgarr j Hjl) as (Hv & Hr).
  apply (proj2 (rdn_mbytes tfibsegs _ 1 (x + Z.of_nat j) _)). split; [reflexivity|].
  intros i Hi. replace i with 0%nat by lia. cbn [nth_error]. rewrite Z.add_0_r.
  rewrite (mb_same (w_H W) mem (ms_mem ms6) (x + Z.of_nat j)).
  2:{ apply M6. rewrite unsigned_lit_small by lia. apply Hbandw. lia. }
  specialize (Hv 0%nat ltac:(lia)). rewrite Z.add_0_r in Hv. rewrite Hv. f_equal.
  rewrite le_byte_small by (change (2 ^ (8 * Z.of_nat 1)) with 256; lia).
  cbn [Nat.mul Z.of_nat Z.mul]. rewrite Z.shiftr_0_r. apply nth_map_app_nul. exact Hj. }
assert (RTAIL : forall a : Z, x + Z.of_nat (length str) < a
< x + Z.of_nat (length str) - (x + Z.of_nat (length str)) mod 8 + 8 ->
rdn tfibsegs (mrestrict (w_H W) (ms_mem ms6)) (Z_to_bv 64 a) 1 <> None).
{ intros a Ha Hnone.
  pose proof (Z.mod_pos_bound (x + Z.of_nat (length str)) 8 ltac:(lia)) as Hm8.
  assert (Hv : aview tfibsegs (w_H W) (ms_mem ms6) a <> None).
  { rewrite (aview_same (w_H W) mem (ms_mem ms6) a); [apply (Htail a); lia|].
    apply M6. rewrite unsigned_lit_small by lia. apply TAILW. lia. }
  apply (proj1 (AF0x.aview_vis (w_H W) (ms_mem ms6) a)) in Hv.
  destruct (mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms6)) a) as [b|] eqn:Eb; [|exact (Hv eq_refl)].
  rewrite rdn1_mbyte, Eb in Hnone. discriminate. }
assert (RMC : forall a : Z, AE3a.tfib_D_const_HIGHS_0x8080808080808080 <= a
< AE3a.tfib_D_const_ONES_0x0101010101010100 + 8 ->
rdn tfibsegs (mrestrict (w_H W) (ms_mem ms6)) (Z_to_bv 64 a) 1
= rdn tfibsegs (fun _ : word => @None byte) (Z_to_bv 64 a) 1).
{ intros a Ha. pose proof mc_bounds as [MB1 MB2].
  unfold AE3a.tfib_D_const_HIGHS_0x8080808080808080, AE3a.tfib_D_const_ONES_0x0101010101010100 in Ha.
  assert (Hin : MC_LO <= a < MC_HI) by lia.
  pose proof (Hrom a Hin) as Hvv.
  rewrite <- (aview_same (w_H W) mem (ms_mem ms6) a) in Hvv
    by (apply M6; rewrite unsigned_lit_small by lia; apply LOW; lia).
  rewrite !rdn1_mbyte. unfold aview in Hvv.
  change (mbyte tfibsegs (fun _ : word => None) a) with (seg_rom tfibsegs (Z_to_bv 64 a)).
  destruct (mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms6)) a) as [b|],
           (seg_rom tfibsegs (Z_to_bv 64 a)) as [b'|]; cbn in Hvv; try discriminate; [|reflexivity].
  injection Hvv as Hvv. do 2 f_equal. apply bv_eq. exact Hvv. }
destruct (MUSL str c (w64 x) (mrestrict (w_H W) (ms_mem ms6)) (seg_rom tfibsegs) (ms_regs ms6)
  HstrN ltac:(lia) ltac:(unfold w64; rewrite unsigned_lit_small by lia; lia)
  ltac:(unfold w64; rewrite unsigned_lit_small by lia; exact RDN)
  ltac:(unfold w64; rewrite unsigned_lit_small by lia; exact RTAIL)
  RMC R6x ltac:(exact R6c)) as (regs7 & Hms & A10 & KEEP).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) EE e4 ms6 HS6 E4rv) as Hshape6.
rewrite E4pc in Hshape6. rewrite Hshape6.
eapply (SRr_msteps tfibsegs AF0x.Hwx_tfa W); [rewrite restrict_mkst_fx; exact Hms|].
intros model' Hsbm _.
rewrite (same_but_materialized_wvb _ model' Hsbm). rewrite wvb_collapse.
set (mem7 := munrestrict (w_H W) (ms_mem ms6) (mrestrict (w_H W) (ms_mem ms6))).
assert (M76 : forall z, mem7 z = ms_mem ms6 z)
by (intros z; unfold mem7; apply munrestrict_mrestrict_same).
assert (M7 : forall z : word, ~ (sp0 - CS_WIN <= bv_unsigned z < sp0) -> mem7 z = mem z)
by (intros z Hz; rewrite M76; apply M6; exact Hz).
assert (P7 : forall a, sp0 - CS_WIN <= a < sp0 -> apresent (w_H W) mem7 a)
by (intros a Ha; apply (apresent_same (w_H W) (ms_mem ms6) mem7 a (M76 _)); apply P6; exact Ha).
set (mdA := with_vm_backing (m_vm_lazy md) (m_vm_materialized model') md).
assert (HARA : AR tfibsegs B ly S W mem7 mdA).
{ apply (al_frame _ _ LAWS ly S W mem md mem7 mdA HAR).
  - intros a Hr Hown. apply aview_same. apply M7. rewrite unsigned_lit_small by lia. intros Hs.
    exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(unfold CS_WIN in *; lia) Hown).
  - intros a Hv. rewrite (AE2y.aview_mod _ mem7 a). rewrite (AE2y.aview_mod _ mem a) in Hv.
    assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
    set (a' := a mod 2 ^ 64) in *.
    destruct (Z_lt_le_dec a' (sp0 - CS_WIN)) as [L1|L1].
    { assert (Hq : mem7 (Z_to_bv 64 a') = mem (Z_to_bv 64 a'))
        by (apply M7; rewrite unsigned_lit_small by lia; lia).
      rewrite (aview_same (w_H W) mem mem7 a' Hq). exact Hv. }
    destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [apply aview_some_of_apresent; apply P7; lia|].
    assert (Hq : mem7 (Z_to_bv 64 a') = mem (Z_to_bv 64 a'))
      by (apply M7; rewrite unsigned_lit_small by lia; lia).
    rewrite (aview_same (w_H W) mem mem7 a' Hq). exact Hv.
  - apply (same_but_materialized_frame md _ (with_vm_backing_same md (m_vm_materialized model'))).
  - apply (same_but_materialized_frame md _ (with_vm_backing_same md (m_vm_materialized model'))).
  - apply (same_but_materialized_frame md _ (with_vm_backing_same md (m_vm_materialized model'))).
  - exact (AE2y.hs_kept_win _ _ _ _ _ _ _ _ M7 HpresE ltac:(unfold CS_WIN; lia) ltac:(lia)). }
(* ---------------- phase 3: the two epilogues, the flags byte and the runtime's internal_strlen -------- *)
set (E3 := AE2y.Env regs7 [g; bv_unsigned c; x; y; sp0]).
assert (E3reg : forall i (rr : bv 5), Z.of_nat i = bv_unsigned rr -> ew E3 i = getr regs7 rr)
by (intros; apply AE2y.Env_reg; assumption).
assert (K7 : forall rr : bv 5, rr <> 10%bv -> rr <> 12%bv -> rr <> 13%bv -> rr <> 14%bv -> rr <> 15%bv ->
rr <> 16%bv -> rr <> 17%bv -> getr regs7 rr = getr (ms_regs ms6) rr) by (intros rr; apply KEEP).
assert (BV5 : forall z, 0 <= z < 32 -> bv_unsigned (Z_to_bv 5 z) = z).
{ intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
  apply Z.mod_small. lia. }
assert (NEQ : forall z (u : bv 5), 0 <= z < 32 -> bv_unsigned u <> z -> Z_to_bv 5 z <> u)
by (intros z u Hz Hu Heq; apply Hu; rewrite <- Heq; apply BV5; exact Hz).
assert (R7sp : getr regs7 2 = w64 (sp0 - CS_WIN)).
{ rewrite (K7 (2%bv : bv 5)) by (intros Hq; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq; discriminate).
  rewrite (RD6 (2%bv : bv 5)), E4r2. cbn [sv_denot]. rewrite EE2. reflexivity. }
assert (R7gd : getr regs7 18 = w64 CS_GUARD).
{ rewrite (K7 (18%bv : bv 5)) by (intros Hq; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq; discriminate).
  rewrite (RD6 (18%bv : bv 5)), E4r18. reflexivity. }
assert (E3_2 : bv_unsigned (ew E3 2) = sp0 - CS_WIN).
{ rewrite (E3reg 2%nat 2%bv eq_refl), R7sp. unfold w64. apply unsigned_lit_small. unfold CS_WIN. lia. }
assert (E3_10 : ew E3 10 = Z_to_bv 64 (x + rres)).
{ rewrite (E3reg 10%nat 10%bv eq_refl), A10. unfold w64. rewrite unsigned_lit_small by lia.
  rewrite <- Hrd. reflexivity. }
assert (E3_32 : ew E3 32 = Z_to_bv 64 g) by (apply (AE2y.Env_x regs7 _ 0); reflexivity).
assert (E3_33 : ew E3 33 = Z_to_bv 64 (bv_unsigned c)) by (apply (AE2y.Env_x regs7 _ 1); reflexivity).
assert (E3_34 : ew E3 34 = Z_to_bv 64 x) by (apply (AE2y.Env_x regs7 _ 2); reflexivity).
assert (E3_35 : ew E3 35 = Z_to_bv 64 y) by (apply (AE2y.Env_x regs7 _ 3); reflexivity).
assert (E3_36 : ew E3 36 = Z_to_bv 64 sp0) by (apply (AE2y.Env_x regs7 _ 4); reflexivity).
assert (E3_33u : bv_unsigned (ew E3 33) = bv_unsigned c) by (rewrite E3_33; apply unsigned_lit_small; lia).
assert (XF : forall off off' (v v' : sv), has_chunk e4 off v = true -> sv_denot E3 v' = sv_denot EE v ->
sp0 - CS_WIN + off' = sp0 + off ->
YP09.chunk_ok tfibsegs E3 (mrestrict (w_H W) mem7) (sp0 - CS_WIN) (YP09.mkChunk off' (CVal 8 v'))).
{ intros off off' v v' Hc Hd Ho.
  exact (chunk_xfer (w_H W) EE E3 (ms_mem ms6) mem7 sp0 (sp0 - CS_WIN) off off' v v' (CKE off v Hc) Hd Ho M76). }
assert (DX : sv_denot E3 (SOff 34 0) = sv_denot EE (SOff 10 0)).
{ cbn [sv_denot]. rewrite E3_34, EE10, !unsigned_lit_small by lia. reflexivity. }
assert (DY : sv_denot E3 (SOff 35 0) = sv_denot EE (SOff 11 0)).
{ cbn [sv_denot]. rewrite E3_35, EE11, !unsigned_lit_small by lia. reflexivity. }
assert (DG : sv_denot E3 (SOff 32 0) = sv_denot EE (SOff 32 0)).
{ cbn [sv_denot]. rewrite E3_32, EE32, !unsigned_lit_small by lia. reflexivity. }
assert (DS : sv_denot E3 (SOff 36 0) = sv_denot EE (SOff 2 0)).
{ cbn [sv_denot]. rewrite E3_36, unsigned_lit_small by lia. rewrite EE2. reflexivity. }
assert (HgvM : val_mem tfibsegs (mrestrict (w_H W) mem7) CS_GUARD 8 g).
{ apply (AF0x.val_mem_ext (mrestrict (w_H W) mem)); [|exact Hgv].
  intros j Hj. apply (mb_same (w_H W) mem mem7). apply M7.
  rewrite unsigned_lit_small by (unfold CS_GUARD; lia). unfold CS_GUARD, CS_WIN. lia. }
assert (HS7 : st_ok tfibsegs E3 ss3 (restrict (w_H W)
  (mkst regs7 (Z_to_bv 64 CS_LOOP_END) mem7 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss3. unfold E3, AE2y.Env.
  apply (entry_st_ok_full tfibsegs);
    change (Ereg regs7 (map (Z_to_bv 64) [g; bv_unsigned c; x; y; sp0])) with E3.
  - unfold sr3. apply regs_ok_pin; [apply regs_ok_Ereg
      | intros Hq; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq; discriminate
      | rewrite R7gd; reflexivity].
  - vm_compute. reflexivity.
  - apply Forall_cons; [| apply Forall_cons].
    + unfold stk3, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E3_2. split; [unfold CS_WIN; lia|]. split; [unfold CS_WIN; lia|].
      split; [intros o Ho; exfalso; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (XF (- CS_WIN + 0) 0 (SOff 10 0) (SOff 34 0)); [vm_compute; reflexivity | exact DX | lia].
      * apply (XF (- CS_WIN + 8) 8 (SLit CS_CN_RA) (SLit CS_CN_RA));
          [vm_compute; reflexivity | reflexivity | lia].
      * apply (XF (- CS_WIN + 48) 48 (SOff 32 0) (SOff 32 0)); [vm_compute; reflexivity | exact DG | lia].
      * apply (XF (- CS_WIN + 56) 56 (SOff 11 0) (SOff 35 0)); [vm_compute; reflexivity | exact DY | lia].
      * apply (XF (- CS_WIN + 64) 64 (SLit 1) (SLit 1)); [vm_compute; reflexivity | reflexivity | lia].
      * apply (XF (- CS_WIN + 72) 72 (SOff 10 0) (SOff 34 0)); [vm_compute; reflexivity | exact DX | lia].
      * apply (XF (- CS_WIN + 80) 80 (SOff 2 0) (SOff 36 0)); [vm_compute; reflexivity | exact DS | lia].
      * apply (XF (- CS_WIN + 88) 88 (SLit CS_RET1) (SLit CS_RET1));
          [vm_compute; reflexivity | reflexivity | lia].
    + unfold grdR, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      split; [unfold CS_GUARD; lia|]. split; [unfold CS_GUARD; lia|].
      split; [intros o Ho; exfalso; lia|].
      apply Forall_cons; [| apply Forall_nil].
      eapply (chunk_ok_val tfibsegs E3 (mrestrict (w_H W) mem7) 0 CS_GUARD 8%N (SOff 32 0) g).
      * cbn [sv_denot]. rewrite E3_32, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
      * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      * cbn [Z.of_N]. lia.
      * rewrite Z.add_0_l. exact HgvM.
    + exact (rodata_ok B TB cs_rodata ly S (w_H W) mem7 E3 (cs_rodata_chk ly) (proj1 HARA)).
  - apply pairwise_disjoint_of_extents.
    unfold stk3, grdR, cs_rodata, icpt_rodata, ro_region, extent_of_region, CS_GUARD.
    cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E3_2.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold CS_WIN. repeat split; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok facts3]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E3_2, E3_33u. change (2 ^ 4) with 16. change (2 ^ 0) with 1.
    repeat split; first [exact Hal16b | apply Z.mod_1_r | unfold CS_WIN; lia]. }
apply (phaseT W _ E3 ss3 e5 _ A_SLB _ HS7 r_e5). intros ms8 mat8 HS8 HF8.
destruct e5_f as (E5pc & E5rv & E5at & E5r12).
assert (M87 : forall z, ms_mem ms8 z = mem7 z) by (apply (frame_all E3 (ss_mem ss3)); [exact we_ss3 | exact HF8]).
assert (AV8y : aview tfibsegs (w_H W) (ms_mem ms8) y = Some (bv_unsigned c)).
{ rewrite (aview_same (w_H W) mem7 (ms_mem ms8) y (M87 _)).
  rewrite (aview_same (w_H W) mem mem7 y); [exact AVy|].
  apply M7. rewrite unsigned_lit_small by lia. apply Hband2w. lia. }
apply (lbuR W _ E3 e5 ms8 (12%bv : bv 5) (12%bv : bv 5) W_SLB (0%bv : bv 12) y (bv_unsigned c) (SOff 33 0) 37%nat _
  HS8 E5rv E5at ltac:(rewrite E5pc; exact clk_slb) dec_slb ltac:(vm_compute; reflexivity)
  ltac:(rewrite E5r12; cbn [sv_denot]; rewrite E3_35, unsigned_lit_small by lia;
        rewrite Z.add_0_r, v_addi_lit; change (bv_signed (0%bv : bv 12)) with 0;
        rewrite Z.add_0_r; reflexivity)
  ltac:(lia) AV8y
  ltac:(cbn [sv_denot]; rewrite E3_33u; rewrite Z.add_0_r; reflexivity)).
intros ms9 mat9 HS9 MM9. rewrite wvb_collapse. rewrite E5pc in HS9.
apply (phaseT W _ E3 s3b e6 _ A_SLB _ HS9 r_e6). intros ms10 mat10 HS10 HF10.
destruct e6_f as (E6pc & E6rv & E6at & E6r12).
assert (M107 : forall z, ms_mem ms10 z = mem7 z).
{ intros z. rewrite (frame_all E3 (ss_mem s3b) (ms_mem ms9) (ms_mem ms10) we_s3b HF10 z), MM9. apply M87. }
assert (AV10y1 : aview tfibsegs (w_H W) (ms_mem ms10) (y + 1) = Some 0).
{ rewrite (aview_same (w_H W) mem7 (ms_mem ms10) (y + 1) (M107 _)).
  rewrite (aview_same (w_H W) mem mem7 (y + 1)); [exact AVy1|].
  apply M7. rewrite unsigned_lit_small by lia. apply Hband2w. lia. }
apply (lbuR W _ E3 e6 ms10 (12%bv : bv 5) (12%bv : bv 5) W_SLB (0%bv : bv 12) (y + 1) 0 (SLit 0) 37%nat _
  HS10 E6rv E6at ltac:(rewrite E6pc; exact clk_slb) dec_slb ltac:(vm_compute; reflexivity)
  ltac:(rewrite E6r12; cbn [sv_denot]; rewrite E3_35, unsigned_lit_small by lia;
        rewrite v_addi_lit; change (bv_signed (0%bv : bv 12)) with 0; rewrite Z.add_0_r; reflexivity)
  ltac:(lia) AV10y1 ltac:(reflexivity)).
intros ms11 mat11 HS11 MM11. rewrite wvb_collapse. rewrite E6pc in HS11.
apply (phaseT W _ E3 s3c e7 _ CS1_ENTRY _ HS11 r_e7). intros ms12 mat12 HS12 HF12.
assert (M127 : forall z, ms_mem ms12 z = mem7 z).
{ intros z. rewrite (frame_all E3 (ss_mem s3c) (ms_mem ms11) (ms_mem ms12) we_s3c HF12 z), MM11. apply M107. }
(* ---------------- the state at 0x42d38 ---------------- *)
destruct e7_f as (E7pc & E7rv & E7r2 & E7r8 & E7r9 & E7r19 & E7r10 & E7r23 & E7r21 & E7keep).
assert (RD12 : forall rr : bv 5, getr (ms_regs ms12) rr = sv_denot E3 (sr_get (ss_regs e7) rr))
by (intros rr; exact (st_ok_reg_denot (w_H W) E3 e7 ms12 rr HS12)).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E3 e7 ms12 HS12 E7rv) as Hshape12.
rewrite E7pc in Hshape12. rewrite Hshape12.
apply SRr_ret. split; [reflexivity|].
exists (ms_regs ms12), (ms_mem ms12), (with_vm_backing (m_vm_lazy md) mat12 md).
split; [reflexivity|].
assert (SBMA : same_but_materialized mdA (with_vm_backing (m_vm_lazy md) mat12 md))
by (unfold mdA; rewrite <- (wvb_collapse (m_vm_lazy md) mat12 (m_vm_materialized model') md);
    apply with_vm_backing_same).
unfold cs_mid.
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]]].
- apply (al_frame _ _ LAWS ly S W mem7 mdA (ms_mem ms12) _ HARA).
  + intros a _ _. apply aview_same. apply M127.
  + intros a Hv. rewrite (aview_same (w_H W) mem7 (ms_mem ms12) a (M127 _)). exact Hv.
  + apply (same_but_materialized_frame _ _ SBMA).
  + apply (same_but_materialized_frame _ _ SBMA).
  + apply (same_but_materialized_frame _ _ SBMA).
  + exact (AE2y.hs_kept_eq _ _ _ M127).
- apply with_vm_backing_same.
- rewrite (RD12 (2%bv : bv 5)), E7r2. cbn [sv_denot]. rewrite E3_2. unfold w64, CS_FRAME, CS_WIN.
  f_equal. lia.
- rewrite (RD12 (8%bv : bv 5)), E7r8. cbn [sv_denot]. rewrite E3_36, unsigned_lit_small by lia.
  rewrite Z.add_0_r. reflexivity.
- rewrite (RD12 (9%bv : bv 5)), E7r9. cbn [sv_denot]. rewrite E3_34, unsigned_lit_small by lia.
  rewrite Z.add_0_r. reflexivity.
- rewrite (RD12 (19%bv : bv 5)), E7r19. cbn [sv_denot]. rewrite E3_35, unsigned_lit_small by lia.
  rewrite Z.add_0_r. reflexivity.
- rewrite (RD12 (10%bv : bv 5)), E7r10. reflexivity.
- rewrite (RD12 (21%bv : bv 5)), E7r21. rewrite denot_lit_U. unfold w64. f_equal.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E3 10 (x + rres) E3_10) by lia.
  rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E3 34 x E3_34) by lia.
  rewrite U_SLit. rewrite (zcanon_id (2 ^ 64 - 1)) by (unfold M64; lia).
  unfold zcanon, M64. rewrite Zplus_mod_idemp_r.
  replace (x + rres + x * (2 ^ 64 - 1)) with (rres + x * 2 ^ 64) by ring.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
- rewrite (RD12 (23%bv : bv 5)), E7r23. reflexivity.
- intros q Hq. cbn [In CS_KEPT] in Hq.
  assert (Hqv : q = 3 \/ q = 4 \/ q = 20 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia.
  assert (Hq32 : 0 <= q < 32) by lia.
  rewrite (RD12 (Z_to_bv 5 q)).
  rewrite forallb_forall in E7keep.
  specialize (E7keep q ltac:(cbn [In CS_KEEPB]; lia)). cbn beta in E7keep.
  unfold reg_is, RGv in E7keep. apply sv_eqb_eq in E7keep. rewrite E7keep.
  cbn [sv_denot]. rewrite (E3reg (Z.to_nat q) (Z_to_bv 5 q) ltac:(rewrite BV5 by lia; lia)).
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite (K7 (Z_to_bv 5 q)) by (apply NEQ; [lia | vm_compute; lia]).
  rewrite forallb_forall in E4keep.
  specialize (E4keep q ltac:(cbn [In CS_KEEPB]; lia)). cbn beta in E4keep.
  unfold reg_is, RGv in E4keep. apply sv_eqb_eq in E4keep.
  rewrite (RD6 (Z_to_bv 5 q)), E4keep. cbn [sv_denot].
  rewrite (EEreg (Z.to_nat q) (Z_to_bv 5 q) ltac:(rewrite BV5 by lia; lia)).
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- intros a Har Hna. rewrite (aview_same (w_H W) mem7 (ms_mem ms12) a (M127 _)).
  apply aview_same. apply M7. rewrite unsigned_lit_small by lia. exact Hna.
- intros a Hp. apply (apresent_same (w_H W) mem7 (ms_mem ms12) a (M127 _)).
  rewrite (AE2y.apresent_mod _ mem7 a). rewrite (AE2y.apresent_mod _ mem a) in Hp.
  assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  set (a' := a mod 2 ^ 64) in *.
  destruct (Z_lt_le_dec a' (sp0 - CS_WIN)) as [L1|L1].
  { assert (Hq : mem7 (Z_to_bv 64 a') = mem (Z_to_bv 64 a'))
      by (apply M7; rewrite unsigned_lit_small by lia; lia).
    exact (apresent_same (w_H W) mem mem7 a' Hq Hp). }
  destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [apply P7; lia|].
  assert (Hq : mem7 (Z_to_bv 64 a') = mem (Z_to_bv 64 a'))
    by (apply M7; rewrite unsigned_lit_small by lia; lia).
  exact (apresent_same (w_H W) mem mem7 a' Hq Hp).
- intros rz off Hin.
  assert (Hb : 0 <= rz < 32 /\ - 80 <= off <= - 8)
    by (cbn [In CS_SAVED] in Hin; repeat (destruct Hin as [Hq|Hin]; [injection Hq as Hq1 Hq2; lia|]);
        destruct Hin).
  destruct Hb as (Hrz & Hoff).
  pose proof e4_saved as Hsv. rewrite forallb_forall in Hsv.
  specialize (Hsv (rz, off) Hin). cbn [fst snd] in Hsv.
  pose proof (CKE off (SOff (Z.to_nat rz) 0) Hsv) as Hok.
  pose proof (val_of_chunk_ok tfibsegs EE (mrestrict (w_H W) (ms_mem ms6)) sp0 off 8%N
    (SOff (Z.to_nat rz) 0) (bv_unsigned (getr regs (Z_to_bv 5 rz))) Hok) as Hvm.
  apply (AF0x.val_mem_ext (mrestrict (w_H W) (ms_mem ms6))).
  { intros j Hj. apply (mb_same (w_H W) (ms_mem ms6) (ms_mem ms12)).
    rewrite M127. apply M76. }
  apply Hvm.
  + cbn [sv_denot]. rewrite (EEreg (Z.to_nat rz) (Z_to_bv 5 rz) ltac:(rewrite BV5 by lia; lia)).
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply u64_range.
  + cbn [Z.of_N]. lia.
Qed.
End g.
