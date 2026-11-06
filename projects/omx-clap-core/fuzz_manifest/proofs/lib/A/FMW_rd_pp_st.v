(* lv2_locate_manifest_readings, segment PP, piece ST (FMW_rd_pp_cuts.v pp_seg_ST): from 0x81f08 (the '<' at p3 found,
   lv2_locate.c:127-129) to the cut C8 (0x81f20, after strchr).  The stretch stores p0 at F+0x38, -p0 at F+0x10 and
   ns = text + S p3 at F+0x28, sets a1 = '>' and calls strchr (ns, '>') (readings_names.dis 203-208).  At the return
   rd_C8 (FMW_rd_cuts.v) holds with strchr's answer: the scan's invariant is kept (the stores and the call write only
   the three scratch slots and strchr's window below F), the three slots hold their values, the callee-saved registers
   are as at 0x81f08.  Technique: FMW_rd_c8.v (rd_C8_holds, c8_segB: the frame window, slot read-back, g3_aj_ro_at) and
   G4's FMW_ex_decl_d3c.v (the same strchr call in expected). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YCbm.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC20 YI00 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMPstat FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_g3kit FMW_rd_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_rd_cuts FMW_rd_ret ACej.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_rd_pp_cuts.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require readings_scan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ---- words ---- *)
Section u. Context {fx : YK11.FPState}.
Lemma st_u64 : forall z, bv_unsigned (w64 z) = z mod 2 ^ 64.
Proof. intros z. unfold w64. rewrite Z_to_bv_unsigned. reflexivity. Qed.
Lemma st_w64_mod : forall z, w64 z = Z_to_bv 64 (z mod 2 ^ 64).
Proof. intros z. rewrite <- (st_u64 z). rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.
End u.

(* ---- the memory this stretch and strchr may write: strchr's window below F and the three scratch slots
   (after FMW_rd_c8.v rd_win / rd_kept, which has slot 0x38 only) ---- *)
Definition st_win (cx : rdcx) (a : Z) : Prop :=
  cx_F cx - STK_RT_STR <= a < cx_F cx \/ cx_F cx + 0x10 <= a < cx_F cx + 0x18 \/
  cx_F cx + 0x28 <= a < cx_F cx + 0x30 \/ cx_F cx + 0x38 <= a < cx_F cx + 0x40.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Definition st_kept (cx : rdcx) (W : world tfibsegs) (m m' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ st_win cx a -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a.

(* FMW_rd_c8.v c8_bounds *)
Lemma st_bounds : forall CTX cx, rd_base B CTX cx ->
  alloc_ceiling + STK_readings <= cx_sp cx /\ cx_sp cx + 16 <= 2 ^ 47 /\ cx_sp cx mod 16 = 0.
Proof.
intros CTX cx (HAN & _ & _ & _ & _ & _ & _ & Htopr & _).
pose proof HAN as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold cx_sp in *. lia.
Qed.

(* FMW_rd_c8.v c8_val_kept *)
Lemma st_val_kept : forall cx W m m' a n v, st_kept cx W m m' -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat n -> ~ st_win cx x) ->
  val_mem tfibsegs (rdW W m) a n v -> val_mem tfibsegs (rdW W m') a n v.
Proof.
intros cx W m m' a n v HK H0 H1 Hw Hv. apply (g3_val_mem_kept W W m m'); [exact Hv|].
intros i Hi. apply HK; [lia|]. apply Hw. lia.
Qed.

(* FMW_rd_c8.v c8_slots_kept, for the slots outside st_win *)
Lemma st_slots_kept : forall CTX cx W m m' sl, rd_base B CTX cx -> st_kept cx W m m' ->
  Forall (fun s => (0 <= fst s /\ fst s + 8 <= 0x10) \/ (0x18 <= fst s /\ fst s + 8 <= 0x28) \/
                   (0x30 <= fst s /\ fst s + 8 <= 0x38) \/ (0x40 <= fst s <= 0x100)) sl ->
  rd_slots_ok cx W m sl -> rd_slots_ok cx W m' sl.
Proof.
intros CTX cx W m m' sl HB HK Hs H. pose proof (st_bounds CTX cx HB) as (Bs1 & Bs2 & _).
pose proof asan_consts as (C1 & _). assert (STK_readings = 16624) by reflexivity.
assert (STK_RT_STR = 8192) by reflexivity.
unfold rd_slots_ok in *. rewrite Forall_forall in Hs, H |- *. intros s Hin.
destruct (H s Hin) as [Hv Hr]. split; [|exact Hr]. specialize (Hs s Hin).
assert (HF : cx_F cx = cx_sp cx - 208) by reflexivity.
apply (st_val_kept cx W m m' _ 8 _ HK); [lia | lia | | exact Hv].
intros x Hx Hw. unfold st_win in Hw. cbn [Z.of_nat Pos.of_succ_nat] in Hx. lia.
Qed.

(* FMW_rd_c8.v c8_loop_kept: rd_loop carries over a run or a runtime call that writes inside st_win only *)
Lemma st_loop_kept : forall CTX cx d ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4,
  rd_base B CTX cx -> rd_loop B cx d ly3 S3 W3 regs3 mem3 md3 ->
  ajournal tfibsegs B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx)
    (cx_md cx) [] ly3 S3 W3 mem4 md4 EV_names ->
  st_kept cx W3 mem3 mem4 ->
  getr regs4 2 = getr regs3 2 -> getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  getr regs4 8 = getr regs3 8 -> getr regs4 9 = getr regs3 9 -> getr regs4 18 = getr regs3 18 ->
  rd_loop B cx d ly3 S3 W3 regs4 mem4 md4.
Proof.
intros CTX cx d ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HB HL HJ4 HK Q2 Q3 Q4 Q8 Q9 Q18.
pose proof (st_bounds CTX cx HB) as (Bs1 & Bs2 & _).
pose proof asan_consts as (C1 & _). assert (STK_readings = 16624) by reflexivity.
assert (STK_RT_STR = 8192) by reflexivity.
assert (HF : cx_F cx = cx_sp cx - 208) by reflexivity.
assert (HKL : g3_low_kept W3 W3 mem3 mem4).
{ intros a Ha. apply HK; [lia|]. unfold st_win. lia. }
destruct HL as ((HJ & Hk & R2 & R3 & R4 & R8 & HSV & K16 & HRO & Ct & Cu & Kt & Ku) & R9 & R18 & HSL & HVrp & HPm & HGl
  & Hrest).
split; [|split; [|split; [|split; [|split; [|split; [|split; [|exact Hrest]]]]]]].
- split; [exact HJ4|]. split; [exact Hk|].
  split; [rewrite Q2; exact R2|]. split; [rewrite Q3; exact R3|]. split; [rewrite Q4; exact R4|].
  split; [rewrite Q8; exact R8|].
  split.
  { unfold rd_saved_ok in *. rewrite Forall_forall in HSV |- *. intros s Hin.
    assert (Hs : 104 <= fst s <= 200).
    { cbv [RD_SAVED In] in Hin. repeat (destruct Hin as [<-|Hin]; [cbn; lia|]). destruct Hin. }
    apply (st_val_kept cx W3 mem3 mem4 _ 8 _ HK); [lia | lia | | exact (HSV s Hin)].
    intros x Hx Hw. unfold st_win in Hw. cbn in Hx. lia. }
  split.
  { intros a Ha. rewrite (HK a); [exact (K16 a Ha) | lia |]. unfold st_win. lia. }
  split; [exact (g3_arodata_kept B W3 W3 mem3 mem4 HRO HKL)|].
  split; [exact (g3_cstr_ok_kept W3 W3 mem3 mem4 _ _ Ct HKL)|].
  split; [exact (g3_cstr_ok_kept W3 W3 mem3 mem4 _ _ Cu HKL)|].
  split; [exact Kt | exact Ku].
- rewrite Q9. exact R9.
- rewrite Q18. exact R18.
- apply (st_slots_kept CTX cx W3 mem3 mem4 _ HB HK); [|exact HSL].
  unfold rd_loc_list. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia.
- apply (st_val_kept cx W3 mem3 mem4 _ 8 _ HK); [lia | lia | | exact HVrp].
  intros x Hx Hw. unfold st_win in Hw. cbn in Hx. lia.
- exact HPm.
- exact (g3_fm_glob_kept W3 W3 mem3 mem4 _ _ _ _ HGl HKL).
Qed.
End k.

(* ---- tactics over the run's state (FMW_rd_c8.v c8_greg / c8_awr / c8_cs) ---- *)
(* getr at a register the state keeps as its entry atom: the entry register *)
Ltac st_greg HS EE :=
  lazymatch goal with |- getr _ ?r = getr _ ?r =>
    let Q := fresh "Q" in rreg HS r Q; rewrite Q; apply EE; reflexivity end.
(* awr_ok for the three scratch slots (the frame at atom 2 = F = journal sp0 - 224) *)
Ltac st_awr U2 :=
  lazymatch goal with |- awr_ok ?sg ?BB ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg BB E rs' stk sp0 fp b0 bc ly own) end;
  repeat first
    [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn; lia|]
    | eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -224);
      [reflexivity | rewrite U2; unfold cx_F; lia | cbn; lia | cbn; lia |] ].
(* a register the call keeps (callee-saved) and the state before it holds as an atom *)
Ltac st_cs HP HS :=
  lazymatch goal with |- getr _ ?r = _ =>
    rewrite (g3_aregs_keep _ _ HP r ltac:(cbv [G3_KEPT In]; repeat (first [left; reflexivity | right])));
    let Q := fresh "Q" in rreg HS r Q; rewrite Q end.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable CTX : list (list Z).
Hypothesis IMG : fm_img_facts tfibsegs B.
Hypothesis STRCHR : astrchr_realizes tfibsegs B PC_strchr.

(* ST, 0x81f08: sd a5,0x38(sp); sd a6,0x10(sp); a0 = a2 + 2 = ns; a1 = '>'; sd a0,0x28(sp); strchr (ns, '>') *)
Theorem pp_st_holds : forall f, rd_seg_C8 B CTX (S f) -> pp_seg_ST B CTX f.
Proof.
intros f SC8 cx i d s11 p1 p2 p3 ly3 S3 W3 regs mem md HB HST.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof g3_wx as Hwx. pose proof g3_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (st_bounds B CTX cx HB) as (Bs1 & Bs2 & Bs3).
assert (FFR : STK_readings = 16624) by reflexivity. assert (FRT : STK_RT_STR = 8192) by reflexivity.
assert (HFe : cx_F cx = cx_sp cx - 208) by reflexivity.
pose proof HB as (HAN & _).
pose proof HAN as (_ & _ & _ & Hgp & Htp & _).
unfold pp_at_ST, pp_head in HST. cbv zeta in HST.
destruct HST as ((HI & HA & Hi & Hh & Hs11 & Hsp & R19 & R24 & R27) & HD & R12 & R15 & R16 & R20 & R21 & R22 & R23
  & R25 & R26).
pose proof (pp_facts_of B CTX cx d ly3 S3 W3 regs mem md HB HI) as
  ((V48 & V50 & V60 & Hu2 & Hu3 & HFc & HF2 & HF16) & R2 & R8 & R9 & R18 & Ct & Cu & Ht4 & Htc & Hu4 & Huc & HWR & HJ).
pose proof HI as ((_ & _ & _ & R3 & R4 & _ & _ & _ & HRO & _) & _).
pose proof HD as (_ & _ & _ & _ & _ & _ & _ & _ & Hp3).
(* the entry state: the registers as atoms, the three scratch slots writable *)
assert (HW : forall a, cx_F cx + 0x10 <= a < cx_F cx + 0x40 -> writable_at tfibsegs (mrestrict (w_H W3) mem) a)
  by (intros a Ha; apply HWR; lia).
pose proof (pp_entry_ST W3 regs mem (cx_F cx) R2 R8 HFc HF2 HF16 HW) as HS.
set (E := Ereg regs []) in *.
assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs q)
  by (intros n q Hn; apply ew_Ereg_nat; exact Hn).
clearbody E.
assert (U2 : bv_unsigned (ew E 2) = cx_F cx)
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (E12 : ew E 12 = w64 (rd_p0 cx i s11 + rd_s10 i s11 p3)) by (rewrite (EE 12%nat 12%bv eq_refl); exact R12).
assert (E15 : ew E 15 = w64 (rd_p0 cx i s11)) by (rewrite (EE 15%nat 15%bv eq_refl); exact R15).
assert (E16 : ew E 16 = w64 (- rd_p0 cx i s11)) by (rewrite (EE 16%nat 16%bv eq_refl); exact R16).
assert (SHOK : sh_ok tfibsegs PP_Bx [] E
  (mrestrict (w_H W3) (ms_mem (mkst regs (Z_to_bv 64 PP_ST) mem (seg_rom tfibsegs))))) by constructor.
change mem with (ms_mem (mkst regs (Z_to_bv 64 PP_ST) mem (seg_rom tfibsegs))) in HJ.
unfold cfg_at. change (w64 PP_ST) with (Z_to_bv 64 PP_ST).
(* the run 0x81f08 .. 0x81f1c: three stores, a0 = ns, a1 = '>', jal strchr *)
aj_run_tok rd_tbl_ok HS HJ SHOK PP_Bspan.
{ st_awr U2. }
(* the memory: unchanged outside the three slots *)
assert (AV : st_kept cx W3 mem (ms_mem ms)).
{ lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?m0) (mrestrict _ ?m1) |- _ =>
    intros a Ha Hn; rewrite (g3_aview_frame Ex rs (w_H W3) m0 m1 HFr a Ha); [reflexivity|];
    let rg := fresh "rg" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
    intros (rg & Hin & Hr); apply Hn; vm_compute in Hin;
    destruct Hin as [<-|[<-|[<-|[]]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite U2 in Hr; unfold st_win; lia end. }
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
assert (HKL : g3_low_kept W3 W3 mem (ms_mem ms)) by (intros a Ha; apply AV; [lia | unfold st_win; lia]).
pose proof (g3_arodata_kept B W3 W3 mem (ms_mem ms) HRO HKL) as HRO1.
pose proof (g3_cstr_ok_kept W3 W3 mem (ms_mem ms) _ _ Ct HKL) as Ct1.
(* the three slots: -p0 at 0x10, ns at 0x28, p0 at 0x38 *)
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
  pose proof (g3_st_ok_region_nth Ex ssx (restrict _ msX) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
  let r1 := eval vm_compute in (nth 1 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
  pose proof (g3_st_ok_region_nth Ex ssx (restrict _ msX) 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1;
  let r2 := eval vm_compute in (nth 2 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
  pose proof (g3_st_ok_region_nth Ex ssx (restrict _ msX) 2 r2 HS ltac:(vm_compute; reflexivity)) as HR2;
  cbn [ms_mem restrict] in HR0, HR1, HR2 end.
assert (V10 : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms)) (cx_F cx + 0x10) 8 ((- rd_p0 cx i s11) mod 2 ^ 64)).
{ apply (g3_field_of_region _ _ 2%nat (cx_F cx) _ _ _ _ _ 0x10 8%N (SOff 16 0) _ HR0 U2).
  - cbn. tauto.
  - rewrite (pp_reg_off E 16%nat _ 0 E16), Z.add_0_r. apply st_w64_mod.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply Z.mod_pos_bound. lia.
  - cbn. lia. }
assert (V28 : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms)) (cx_F cx + 0x28) 8 (cx_t cx + Z.of_nat (S p3))).
{ apply (g3_field_of_region _ _ 2%nat (cx_F cx) _ _ _ _ _ 0x28 8%N (SOff 12 2) _ HR1 U2).
  - cbn. tauto.
  - rewrite (pp_reg_off E 12%nat _ 2 E12). unfold w64; f_equal; unfold rd_p0, rd_s10; lia.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - cbn. lia. }
assert (V38 : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms)) (cx_F cx + 0x38) 8 (rd_p0 cx i s11)).
{ apply (g3_field_of_region _ _ 2%nat (cx_F cx) _ _ _ _ _ 0x38 8%N (SOff 15 0) _ HR2 U2).
  - cbn. tauto.
  - rewrite (pp_reg_off E 15%nat _ 0 E15), Z.add_0_r. reflexivity.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold rd_p0. lia.
  - cbn. lia. }
clear HR0 HR1 HR2.
(* the registers at the call *)
rreg HS (1%bv : bv 5) Q1. rreg HS (2%bv : bv 5) Q2. rreg HS (3%bv : bv 5) Q3. rreg HS (4%bv : bv 5) Q4.
pp_rd HS (10%bv : bv 5) Q10. pp_rd HS (11%bv : bv 5) Q11.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl).
lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?x)] =>
  let v := eval vm_compute in (ss_pc x) in change (ss_pc x) with v end.
(* strchr (ns, '>') on the text's suffix after the '<' *)
eapply SRr_bind.
{ eapply (g3_aj_ro_at B LAWS PC_strchr STK_RT_STR
    (fun v => (v = 0 /\ ~ In 62 (skipn (S p3) (cx_tb cx))) \/
              (exists j, FMH_Rt.first_at (skipn (S p3) (cx_tb cx)) 62 j /\
                         v = cx_t cx + Z.of_nat (S p3) + Z.of_nat j))
    W3 (ms_regs ms) (ms_mem ms) (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx)
    (cx_mem cx) (cx_md cx) [] ly3 S3 _ EV_names (-224) (Z_to_bv 64 0x81f20) HJ).
  - unfold spZ. rewrite Q2, U2. lia.
  - reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - lia.
  - rewrite Q3, (EE 3%nat 3%bv eq_refl), R3. exact Hgp.
  - rewrite Q4, (EE 4%nat 4%bv eq_refl), R4. exact Htp.
  - exact Q1.
  - vm_compute. reflexivity.
  - intros HPK.
    apply (STRCHR ly3 S3 W3 (ms_regs ms) (ms_mem ms) _ (cx_t cx + Z.of_nat (S p3)) 62 (skipn (S p3) (cx_tb cx)) HPK).
    + exact (proj1 (IMG ly3 S3 W3 (ms_mem ms) _ (proj1 HJ) HRO1)).
    + exact (proj1 (proj2 (IMG ly3 S3 W3 (ms_mem ms) _ (proj1 HJ) HRO1))).
    + rewrite Q10, (pp_reg_off E 12%nat _ 2 E12). unfold w64; f_equal; unfold rd_p0, rd_s10; lia.
    + rewrite Q11. reflexivity.
    + lia.
    + exact (pp_cstr_suffix W3 (ms_mem ms) (cx_t cx) (cx_tb cx) (S p3) Ct1 Hp3). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & H10v & Hv & HR & Hfr2 & Hpres2).
change (mkCfg (mkst regs2 (Z_to_bv 64 0x81f20) mem2 (seg_rom tfibsegs)) md2)
  with (cfg_at tfibsegs RD_C8 regs2 mem2 md2).
(* the memory after the call: unchanged outside st_win *)
assert (AV2 : st_kept cx W3 mem mem2).
{ intros a Ha Hn. rewrite (Hfr2 a Ha); [exact (AV a Ha Hn)|]. intros Hw. apply Hn. unfold st_win. left. lia. }
assert (Hsp2 : getr regs2 2 = getr (ms_regs ms) 2) by exact (HP2 2 ltac:(unfold acallee_saved; lia)).
apply (SC8 cx i d s11 p1 p2 p3 v ly3 S3 W3 regs2 mem2 md2 HB).
unfold rd_C8. cbv zeta.
split.
{ apply (st_loop_kept B CTX cx d ly3 S3 W3 regs mem md regs2 mem2 md2 HB HI HJ2 AV2).
  - rewrite Hsp2. st_greg HS EE.
  - st_cs HP2 HS. apply EE. reflexivity.
  - st_cs HP2 HS. apply EE. reflexivity.
  - st_cs HP2 HS. apply EE. reflexivity.
  - st_cs HP2 HS. apply EE. reflexivity.
  - st_cs HP2 HS. apply EE. reflexivity. }
split; [exact HA|]. split; [exact Hi|]. split; [exact HD|].
split.
{ unfold rd_slots_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; split.
  - apply (g3_val_mem_kept W3 W3 (ms_mem ms) mem2); [exact V10|]. intros q Hq. cbn in Hq.
    apply Hfr2; [lia|]. lia.
  - apply Z.mod_pos_bound. lia.
  - apply (g3_val_mem_kept W3 W3 (ms_mem ms) mem2); [exact V28|]. intros q Hq. cbn in Hq.
    apply Hfr2; [lia|]. lia.
  - lia.
  - apply (g3_val_mem_kept W3 W3 (ms_mem ms) mem2); [exact V38|]. intros q Hq. cbn in Hq.
    apply Hfr2; [lia|]. lia.
  - unfold rd_p0. lia. }
split; [st_cs HP2 HS; rewrite (EE 19%nat 19%bv eq_refl); exact R19|].
split; [st_cs HP2 HS; rewrite (EE 20%nat 20%bv eq_refl); exact R20|].
split; [st_cs HP2 HS; rewrite (EE 21%nat 21%bv eq_refl); exact R21|].
split; [st_cs HP2 HS; rewrite (EE 22%nat 22%bv eq_refl); exact R22|].
split; [st_cs HP2 HS; rewrite (EE 23%nat 23%bv eq_refl); exact R23|].
split; [st_cs HP2 HS; rewrite (EE 24%nat 24%bv eq_refl); exact R24|].
split; [st_cs HP2 HS; rewrite (EE 25%nat 25%bv eq_refl); exact R25|].
split; [st_cs HP2 HS; rewrite (EE 26%nat 26%bv eq_refl); exact R26|].
split; [st_cs HP2 HS; rewrite (EE 27%nat 27%bv eq_refl); exact R27|].
split; [exact H10v|].
exact HR.
Qed.
End c.
