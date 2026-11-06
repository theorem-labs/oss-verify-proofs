(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8j.v:49-57;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACan.v:337-344; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:140-147, 156-161;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACes.v:193-195, for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg1.v, with its module paths, module names and numbers changed; 459 of its 550 lines of code are new or changed and 365 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/SbDecSeg1.v, with its module paths, module names and numbers changed; 1841 of its 1900 lines of code are new or changed and 491 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMW_rd_pl.v, with its module paths and module names changed; 919 of its 1019 lines of code are new or changed and 1800 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/B/FMW_rd_lp.v; 261 of its 338 lines of code are new or changed and 942 lines of the source are left out. *)
(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMW_rd_pp_st.v (a working branch e2e59892bef),
   re-walked on B's code (B-readings.lst 0x82150 .. 0x82158 and 0x821ac .. 0x821bc). *)
(* lv2_locate_manifest_readings on fm.asan-ubsan, segment PP, pieces L3E and ST (lib/B/FMW_rd_pp_cuts.v pp_seg_L3E,
   pp_seg_ST).
   L3E 0x82150 (lv2_locate.c:121-125): the name ended with ':' at s8 = text + p2; the guard 0x82150 (beq s8,s0),
   then F+0x48 := -a1 = p2 - p1 (0x82154 neg, 0x82158 sd) and the third loop's head L3 0x8215c with j = 0 (pp_seg_W3).
   ST 0x821ac (lv2_locate.c:127-129): the '<' at a0 = text + p3; the guard 0x821ac (beq a0,s0), s8 := s8 + 2 = ns =
   text + S p3, a1 = '>', a0 = ns, strchr (ns, '>') via the trampoline 0x41340, returning to C8 0x821c0: rd_C8
   (FMW_rd_cuts.v) holds with strchr's answer. B makes no store on this stretch (A stored p0, -p0 and ns here; B
   keeps them in s6, s9 / s10 and s8).
   UBSan guards (trap 0x823b4): 0x82150 (beq s8,s0) and 0x821ac (beq a0,s0) are decided not taken by the token engine
   from the entry fact 4096 <= s8 / a0 <= 2^47 - 16 (class K1: a text position is not -1).
   Technique: A's FMW_rd_pp_st.v (st_win / st_kept / st_loop_kept, the region read-back, g3_aj_ro_at for strchr). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YCbm.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YC20 YI00 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_g3kit FMW_rd_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YCej.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_rd_cuts FMW_rd_ret.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMTrapB.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_rd_pp_cuts.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require readings_scan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ---- the memory this stretch and strchr may write: strchr's window below F and the slot F+0x48 ---- *)
Definition st_win (cx : rdcx) (a : Z) : Prop :=
  cx_F cx - STK_RT_STR <= a < cx_F cx \/ cx_F cx + 0x48 <= a < cx_F cx + 0x50.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Definition st_kept (cx : rdcx) (W : world tfibsegs) (m m' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ st_win cx a -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a.

Lemma st_bounds : forall CTX cx, rd_base B CTX cx ->
  alloc_ceiling + STK_readings <= cx_sp cx /\ cx_sp cx + 16 <= 2 ^ 47 /\ cx_sp cx mod 16 = 0.
Proof.
intros CTX cx (HAN & _ & _ & _ & _ & _ & _ & Htopr & _).
pose proof HAN as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold cx_sp in *. lia.
Qed.

Lemma st_val_kept : forall cx W m m' a n v, st_kept cx W m m' -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat n -> ~ st_win cx x) ->
  val_mem tfibsegs (rdW W m) a n v -> val_mem tfibsegs (rdW W m') a n v.
Proof.
intros cx W m m' a n v HK H0 H1 Hw Hv. apply (g3_val_mem_kept W W m m'); [exact Hv|].
intros i Hi. apply HK; [lia|]. apply Hw. lia.
Qed.

(* the frame slots outside st_win *)
Lemma st_slots_kept : forall CTX cx W m m' sl, rd_base B CTX cx -> st_kept cx W m m' ->
  Forall (fun s => (0 <= fst s /\ fst s + 8 <= 0x48) \/ (0x50 <= fst s <= 0x100)) sl ->
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

(* rd_loop carries over a run or a runtime call that writes inside st_win only (A's st_loop_kept, B's rd_loop) *)
Lemma st_loop_kept : forall CTX cx d ly3 S3 W3 regs mem md regs' mem' md',
  rd_base B CTX cx -> rd_loop B cx d ly3 S3 W3 regs mem md ->
  ajournal tfibsegs B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx)
    (cx_md cx) [] ly3 S3 W3 mem' md' EV_names ->
  st_kept cx W3 mem mem' ->
  (forall r, In r PP_KEPT -> getr regs' r = getr regs r) ->
  getr regs' 8 = w64 RD_M1 -> getr regs' 9 = w64 (Z.of_nat d) -> getr regs' 18 = w64 32 -> getr regs' 19 = w64 5 ->
  getr regs' 20 = w64 RD_MASK1 -> getr regs' 23 = w64 58 ->
  rd_loop B cx d ly3 S3 W3 regs' mem' md'.
Proof.
intros CTX cx d ly3 S3 W3 regs mem md regs' mem' md' HB HL HJ4 HK HR K8 K9 K18 K19 K20 K23.
pose proof (st_bounds CTX cx HB) as (Bs1 & Bs2 & _).
pose proof asan_consts as (C1 & _). assert (STK_readings = 16624) by reflexivity.
assert (STK_RT_STR = 8192) by reflexivity.
assert (HF : cx_F cx = cx_sp cx - 208) by reflexivity.
assert (HKL : g3_low_kept W3 W3 mem mem').
{ intros a Ha. apply HK; [lia|]. unfold st_win. lia. }
assert (K2 : getr regs' 2 = getr regs 2) by (apply HR; cbv [PP_KEPT In]; left; apply bv_eq; reflexivity).
assert (K3 : getr regs' 3 = getr regs 3) by (apply HR; cbv [PP_KEPT In]; right; left; apply bv_eq; reflexivity).
assert (K4 : getr regs' 4 = getr regs 4) by (apply HR; cbv [PP_KEPT In]; right; right; left; apply bv_eq; reflexivity).
assert (K27 : getr regs' 27 = getr regs 27)
  by (apply HR; cbv [PP_KEPT In]; right; right; right; left; apply bv_eq; reflexivity).
destruct HL as ((HJ & Hk & R2 & R3 & R4 & R27 & HSV & K16 & HRO & Ct & Cu & Kt & Ku) & R8 & R9 & R18 & R19 & R20 & R23
  & HSL & HVrp & HPm & HGl & Hrest).
split.
{ split; [change (unpoison [] mem') with mem'; exact HJ4|]. split; [exact Hk|].
  split; [rewrite K2; exact R2|]. split; [rewrite K3; exact R3|]. split; [rewrite K4; exact R4|].
  split; [rewrite K27; exact R27|].
  split.
  { unfold rd_saved_ok in *. rewrite Forall_forall in HSV |- *. intros s Hin.
    assert (Hs : 104 <= fst s <= 200).
    { cbv [RD_SAVED In] in Hin. repeat (destruct Hin as [<-|Hin]; [cbn; lia|]). destruct Hin. }
    apply (st_val_kept cx W3 mem mem' _ 8 _ HK); [lia | lia | | exact (HSV s Hin)].
    intros x Hx Hw. unfold st_win in Hw. cbn in Hx. lia. }
  split.
  { intros a Ha. rewrite (HK a); [exact (K16 a Ha) | lia |]. unfold st_win. lia. }
  split; [exact (g3_arodata_kept B W3 W3 mem mem' HRO HKL)|].
  split; [exact (g3_cstr_ok_kept W3 W3 mem mem' _ _ Ct HKL)|].
  split; [exact (g3_cstr_ok_kept W3 W3 mem mem' _ _ Cu HKL)|].
  split; [exact Kt | exact Ku]. }
split; [exact K8|]. split; [exact K9|]. split; [exact K18|]. split; [exact K19|]. split; [exact K20|].
split; [exact K23|].
split.
{ apply (st_slots_kept CTX cx W3 mem mem' _ HB HK); [|exact HSL].
  unfold rd_loc_list. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia. }
split.
{ apply (st_val_kept cx W3 mem mem' _ 8 _ HK); [lia | lia | | exact HVrp].
  intros x Hx Hw. unfold st_win in Hw. cbn in Hx. lia. }
split; [exact HPm|]. split; [exact (g3_fm_glob_kept W3 W3 mem mem' _ _ _ _ HGl HKL)|].
exact Hrest.
Qed.
End k.

(* ---- tactics over the run's state ---- *)
(* the value a register holds after a run, in terms of the cut's (FMW_rd_lp.v lp_gr) *)
Ltac st_gr HS r0 :=
  let r := constr:(r0 : bv 5) in
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    rewrite (st_ok_restrict_reg segs H E ss ms r HS);
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e end;
  cbn [sv_denot ew ewset extK havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
(* a register after a run: a literal the state pins, or the engine's value over the entry facts (pp_g) *)
Ltac st_g HS :=
  lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
    lazymatch type of HS with st_ok ?segs ?Ev ?ss (restrict ?H ?ms') =>
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in
      lazymatch e with
      | SLit _ =>
          rewrite (st_ok_restrict_reg segs H Ev ss ms' r HS); change (sr_get (ss_regs ss) r) with e;
          cbn [sv_denot]; reflexivity
      | _ => pp_g HS
      end end end.
(* a register the run keeps as its entry atom: the cut's register (EE : ew E n = getr regs q) *)
Ltac st_qq HS EE :=
  lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
    let n := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
    st_gr HS r; exact (EE n r eq_refl) end.
(* a callee-saved register across a runtime call (aregs_preserved HP): the register before the call *)
Ltac st_pres HP :=
  lazymatch goal with |- getr _ ?r = _ =>
    let z := eval vm_compute in (bv_unsigned r) in
    etransitivity; [exact (HP z ltac:(unfold acallee_saved; lia)) |] end.
(* awr_ok for the slot F+0x48 (the frame at atom 2 = F = journal sp0 - 224) (A's st_awr) *)
Ltac st_awr U2 :=
  lazymatch goal with |- awr_ok ?sg ?BB ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg BB E rs' stk sp0 fp b0 bc ly own) end;
  repeat first
    [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn; lia|]
    | eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -224);
      [reflexivity | rewrite U2; unfold cx_F; lia | cbn; lia | cbn; lia |] ].
(* a read-only run: its memory is the cut's (FMW_rd_lp.v lp_mem / lp_mk) *)
Ltac st_mem m0 :=
  lazymatch goal with H : frame_of ?Ex ?rs ?mp (ms_mem ?m1) |- _ =>
    let Hm := fresh "Hmem" in
    assert (Hm : ms_mem m1 = m0) by
      (rewrite (frame_of_read_only Ex rs mp (ms_mem m1) ltac:(vm_compute; reflexivity) H);
       first [reflexivity | assumption]) end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac st_mk HS :=
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl);
  lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?x)] =>
    let v := eval vm_compute in (ss_pc x) in change (ss_pc x) with v end;
  repeat match goal with Hm : ms_mem ?x = _ |- _ => rewrite Hm in * end.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable CTX : list (list Z).
Hypothesis IMG : fm_img_facts tfibsegs B.
Hypothesis STRCHR : astrchr_realizes tfibsegs B PC_strchr.

(* L3E, 0x82150: the guard on s8 = text + p2, F+0x48 := p2 - p1, then L3 at j = 0 *)
Theorem pp_l3e_holds : forall f, pp_seg_W3 B CTX f -> pp_seg_L3E B CTX f.
Proof.
intros f HW3 cx i d s11 p1 p2 ly3 S3 W3 regs mem md HB HP.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof g3_wx as Hwx. pose proof g3_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (st_bounds B CTX cx HB) as (Bs1 & Bs2 & Bs3).
assert (FFR : STK_readings = 16624) by reflexivity. assert (FRT : STK_RT_STR = 8192) by reflexivity.
assert (HFe : cx_F cx = cx_sp cx - 208) by reflexivity.
destruct HP as ((HI & HA & Hi & Hh & Hs11 & Hsp0 & R21) & Ep1 & Ep2 & H58 & R11 & R22 & R24 & R25 & R26).
pose proof (pp_facts_of B CTX cx d ly3 S3 W3 regs mem md HB HI) as
  (HFR & R2 & R27 & HPN & R9 & Ct & Cu & Ht4 & Htc & Hu4 & Huc & HWR & HJ).
pose proof HFR as (V58 & Hu2 & HFc & HF2 & HF16).
assert (Hp2 : (p2 < length (cx_tb cx))%nat) by (apply pp_lt_of_nz; rewrite H58; lia).
assert (HW : forall a, cx_F cx + 0x48 <= a < cx_F cx + 0x50 -> writable_at tfibsegs (mrestrict (w_H W3) mem) a)
  by (intros a Ha; apply HWR; lia).
pose proof (pp_entry_L3E W3 regs mem (cx_F cx) (cx_t cx + Z.of_nat p2) R2 R27 HPN HFc HF2 HF16 HW R24
  ltac:(lia) ltac:(lia)) as HS.
remember (Ereg regs []) as E eqn:HE.
assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs q)
  by (intros n q Hn; rewrite HE; apply ew_Ereg_nat; exact Hn).
clear HE.
assert (U2 : bv_unsigned (ew E 2) = cx_F cx)
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (E9 : ew E 9 = w64 (Z.of_nat d)) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (E11 : ew E 11 = w64 (Z.of_nat p1 - Z.of_nat p2)) by (rewrite (EE 11%nat 11%bv eq_refl); exact R11).
assert (E21 : ew E 21 = w64 (cx_t cx + Z.of_nat i)) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
assert (E22 : ew E 22 = w64 (cx_t cx + Z.of_nat p1)) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (E24 : ew E 24 = w64 (cx_t cx + Z.of_nat p2)) by (rewrite (EE 24%nat 24%bv eq_refl); exact R24).
assert (E25 : ew E 25 = w64 (cx_u cx - 2 - Z.of_nat s11 - (cx_t cx + Z.of_nat i) -
                             (Z.of_nat p2 - Z.of_nat i - Z.of_nat s11)))
  by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
assert (E26 : ew E 26 = w64 (cx_u cx - 2 - rd_p0 cx i s11 - (Z.of_nat p2 - Z.of_nat i - Z.of_nat s11)))
  by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
assert (SHOK : sh_ok tfibsegs PP_Bx [] E
  (mrestrict (w_H W3) (ms_mem (mkst regs (Z_to_bv 64 PP_L3E) mem (seg_rom tfibsegs))))) by constructor.
change mem with (ms_mem (mkst regs (Z_to_bv 64 PP_L3E) mem (seg_rom tfibsegs))) in HJ.
unfold cfg_at. change (w64 PP_L3E) with (Z_to_bv 64 PP_L3E).
(* 0x82150 .. 0x82158: the guard (decided), a0 = -a1, sd a0, 0x48(sp) *)
aj_run_to_tok rd_tbl_ok HS HJ SHOK PP_Bspan PP_L3.
{ st_awr U2. }
(* the memory: unchanged outside F+0x48 .. F+0x50 *)
assert (AV : st_kept cx W3 mem (ms_mem ms)).
{ lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?m0) (mrestrict _ ?m1) |- _ =>
    intros a Ha Hn; rewrite (g3_aview_frame Ex rs (w_H W3) m0 m1 HFr a Ha); [reflexivity|];
    let rg := fresh "rg" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
    intros (rg & Hin & Hr); apply Hn; vm_compute in Hin;
    destruct Hin as [<-|[]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite U2 in Hr; unfold st_win; lia end. }
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* the slot F+0x48 holds p2 - p1 *)
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
  pose proof (g3_st_ok_region_nth Ex ssx (restrict _ msX) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
  cbn [ms_mem restrict] in HR0;
  assert (U2x : bv_unsigned (ew Ex 2) = cx_F cx) by (cbn [ew ewset extK Nat.eqb]; exact U2) end.
assert (V48 : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms)) (cx_F cx + 0x48) 8 (Z.of_nat p2 - Z.of_nat p1)).
{ eapply (g3_field_of_region _ _ 2%nat (cx_F cx) _ _ _ _ _ 0x48 8%N _ _ HR0 U2x).
  - cbn. left. reflexivity.
  - pp_sv.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - cbn. lia. }
clear HR0.
st_mk HS.
apply (HW3 cx i d s11 p1 p2 0%nat ly3 S3 W3 _ _ _ HB).
unfold pp_at_L3, pp_head.
split; [split|].
- apply (st_loop_kept B CTX cx d ly3 S3 W3 regs mem md _ _ _ HB HI HJ AV).
  + let r := fresh "r" in let Hr := fresh "Hr" in
    intros r Hr; cbv [PP_KEPT In] in Hr;
    repeat (destruct Hr as [<- | Hr]; [st_qq HS EE |]); destruct Hr.
  + st_g HS.
  + st_g HS.
  + st_g HS.
  + st_g HS.
  + st_g HS.
  + st_g HS.
- split; [exact HA|]. split; [exact Hi|]. split; [exact Hh|]. split; [exact Hs11|].
  split; [exact Hsp0|]. st_g HS.
- split; [exact Ep1|]. split; [exact Ep2|]. split; [exact H58|]. split; [lia|].
  split.
  { unfold rd_slots_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. split; [exact V48 | lia]. }
  split; [st_g HS|]. split; [st_g HS|].
  unfold pp_cd, pp_s10_L3. split; st_g HS.
Qed.

(* ST, 0x821ac: the guard on a0 = text + p3 (decided), s8 := ns = s8 + 2, a1 = '>', a0 = ns, strchr (ns, '>') *)
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
destruct HST as ((HI & HA & Hi & Hh & Hs11 & Hsp0 & R21) & HD & HS48 & R10 & R22 & R24 & R25 & R26).
pose proof (pp_facts_of B CTX cx d ly3 S3 W3 regs mem md HB HI) as
  (HFR & R2 & R27 & HPN & R9 & Ct & Cu & Ht4 & Htc & Hu4 & Huc & HWR & HJ).
pose proof HFR as (V58 & Hu2 & HFc & HF2 & HF16).
pose proof HI as ((_ & _ & _ & R3 & R4 & _ & _ & _ & HRO & _) & _).
pose proof HD as (_ & _ & _ & _ & _ & _ & _ & H60 & Hp3).
pose proof (pp_entry_ST W3 regs mem (cx_F cx) (cx_t cx + Z.of_nat p3) R2 R27 HPN HFc HF2 HF16 R10
  ltac:(lia) ltac:(lia)) as HS.
remember (Ereg regs []) as E eqn:HE.
assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs q)
  by (intros n q Hn; rewrite HE; apply ew_Ereg_nat; exact Hn).
clear HE.
assert (E9 : ew E 9 = w64 (Z.of_nat d)) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (E21 : ew E 21 = w64 (cx_t cx + Z.of_nat i)) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
assert (E22 : ew E 22 = w64 (cx_t cx + Z.of_nat p1)) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (E24 : ew E 24 = w64 (cx_t cx + Z.of_nat p3 - 1)) by (rewrite (EE 24%nat 24%bv eq_refl); exact R24).
assert (E25 : ew E 25 = w64 (cx_u cx - 2 - Z.of_nat s11 - (cx_t cx + Z.of_nat i) - rd_s10 i s11 p3))
  by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
assert (E26 : ew E 26 = w64 (cx_u cx - 2 - rd_p0 cx i s11 - rd_s10 i s11 p3))
  by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
assert (SHOK : sh_ok tfibsegs PP_Bx [] E
  (mrestrict (w_H W3) (ms_mem (mkst regs (Z_to_bv 64 PP_ST) mem (seg_rom tfibsegs))))) by constructor.
change mem with (ms_mem (mkst regs (Z_to_bv 64 PP_ST) mem (seg_rom tfibsegs))) in HJ.
unfold cfg_at. change (w64 PP_ST) with (Z_to_bv 64 PP_ST).
(* 0x821ac .. 0x821bc: the guard (decided), s8 += 2, a1 = '>', a0 = s8, jal strchr *)
aj_run_tok rd_tbl_ok HS HJ SHOK PP_Bspan.
{ awr_ok_tac. }
st_mem mem. st_mk HS.
pose proof (proj1 HJ) as HAR3.
destruct (IMG ly3 S3 W3 mem _ HAR3 HRO) as (HROM & HROO & _).
(* strchr (ns, '>') on the text's suffix after the '<' *)
eapply SRr_bind.
{ eapply (g3_aj_ro_at B LAWS PC_strchr STK_RT_STR
    (fun v => (v = 0 /\ ~ In 62 (skipn (S p3) (cx_tb cx))) \/
              (exists j, FMH_Rt.first_at (skipn (S p3) (cx_tb cx)) 62 j /\
                         v = cx_t cx + Z.of_nat (S p3) + Z.of_nat j))
    W3 _ _ (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] ly3 S3 _ EV_names (-224) (Z_to_bv 64 RD_C8));
  [ exact HJ
  | unfold spZ; st_gr HS (2%bv : bv 5); rewrite (EE 2%nat 2%bv eq_refl), R2, unsigned_lit_small by (unfold cx_F; lia);
    unfold cx_F; lia
  | reflexivity | lia | unfold ESTACK; lia | lia
  | st_gr HS (3%bv : bv 5); rewrite (EE 3%nat 3%bv eq_refl), R3; exact Hgp
  | st_gr HS (4%bv : bv 5); rewrite (EE 4%nat 4%bv eq_refl), R4; exact Htp
  | st_gr HS (1%bv : bv 5); reflexivity
  | unfold YK0s.ret_ok; vm_compute; reflexivity
  | ].
  intros HPK.
  apply (STRCHR ly3 S3 W3 _ _ _ (cx_t cx + Z.of_nat (S p3)) 62 (skipn (S p3) (cx_tb cx)) HPK HROM HROO);
  [ st_g HS
  | st_gr HS (11%bv : bv 5); reflexivity
  | lia
  | exact (pp_cstr_suffix W3 mem (cx_t cx) (cx_tb cx) (S p3) Ct Hp3) ]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & H10v & Hv & HR & Hfr2 & Hpres2).
change (mkCfg (mkst regs2 (Z_to_bv 64 RD_C8) mem2 (seg_rom tfibsegs)) md2)
  with (cfg_at tfibsegs RD_C8 regs2 mem2 md2).
(* the memory after the call: unchanged outside strchr's window below F *)
assert (AV2 : st_kept cx W3 mem mem2).
{ intros a Ha Hn. apply Hfr2; [exact Ha|]. intros Hw. apply Hn. unfold st_win. left. lia. }
apply (SC8 cx i d s11 p1 p2 p3 v ly3 S3 W3 regs2 mem2 md2 HB).
unfold rd_C8. cbv zeta.
split.
{ apply (st_loop_kept B CTX cx d ly3 S3 W3 regs mem md regs2 mem2 md2 HB HI HJ2 AV2).
  - let r := fresh "r" in let Hr := fresh "Hr" in
    intros r Hr; cbv [PP_KEPT In] in Hr;
    repeat (destruct Hr as [<- | Hr]; [st_pres HP2; st_qq HS EE |]); destruct Hr.
  - st_pres HP2; st_g HS.
  - st_pres HP2; st_g HS.
  - st_pres HP2; st_g HS.
  - st_pres HP2; st_g HS.
  - st_pres HP2; st_g HS.
  - st_pres HP2; st_g HS. }
split; [exact HA|]. split; [exact Hi|]. split; [exact HD|].
split.
{ unfold rd_slots_ok in HS48 |- *. apply Forall_cons_iff in HS48 as [[V48 H48r] _]. cbn [fst snd] in V48, H48r.
  apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. split; [|exact H48r].
  apply (g3_val_mem_kept W3 W3 mem mem2); [exact V48|]. intros q Hq. cbn in Hq.
  apply Hfr2; [lia|]. lia. }
split; [st_pres HP2; st_g HS|].
split; [st_pres HP2; st_g HS|].
split; [st_pres HP2; st_g HS|].
split; [st_pres HP2; st_g HS|].
split; [st_pres HP2; st_g HS|].
split; [exact H10v|].
exact HR.
Qed.
End c.
