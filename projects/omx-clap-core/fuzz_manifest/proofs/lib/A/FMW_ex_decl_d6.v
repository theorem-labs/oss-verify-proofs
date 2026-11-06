(* G4.ExDecl.DeclD6B: dseg_D6 (FMW_ex_decl_base.v:389), expected 0x8150c..0x8152c (fuzz_manifest.c:162-166) on
   fm.asan, after plain (uri + nl2) returned a0 (expected.dis lines 230-232, 238-243, 248-256):
   0x8150c s7 = ld F+0x58 = text; `beqz a0`:
   - a0 = 0 (plain_name false): 0x814c8 a1 = ld F+0x28 = text + close, 0x814e8 s3 = a1 - s7 = close, s1 = 64,
     a5 = 58, a6 = ld F+0x60 = the mask, 0x814dc s3 + 1: EX_L at close + 1 (the declaration does not match);
   - a0 = 1: a2 = ld F+0x18 + 1 = declared + 1, a0 = 1, a1 = 16, `bltu a1, a2`: 16 < declared + 1 -> EX_R with
     a0 = 1 = the scan's answer (dd_res_full); else 0x81528 sd a2 F+0x18 -> EX_T (ex_at_T). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC20 YI16 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v ACeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMPstat FMH_Base FMH_Rt FMH_Fn FMW_lib.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_ex_base FMW_ex_ret FMW_ex_decl_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel expected_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the four frame slots the segment loads (F+0x18 declared, F+0x28 close, F+0x58 text, F+0x60 the mask) as chunks
   holding the extra atoms 32..35 (FMW_ex_ret.v ex_slot_chunks); the write window [F+0x18, F+0x20) is the store
   of declared + 1 at 0x81528 *)
Definition d6_chunks : list (Z * nat) := [(0x18, 0%nat); (0x28, 1%nat); (0x58, 2%nat); (0x60, 3%nat)].
Definition d6_frame : YP09.region := YP09.mkRegion (Some 2%nat) 0 208 0x18 0x20 (ex_slot_chunks d6_chunks).
Definition ss_D6 : sstate := mkSS EX_D6 sr_atoms [d6_frame] None (mkFacts [(2%nat, mkAF (2^46) (2^47) 4)] [] []).

(* ---- walk tactics (after FMW_plain.v fw_reg / pl_mk / pl_g / pl_avw) ---- *)
Ltac d6_reg HS r :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    rewrite (st_ok_restrict_reg segs H E ss ms r HS); change (sr_get (ss_regs ss) r) with e end.
Ltac d6_mk HS := rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl);
  lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?x)] =>
    let v := eval vm_compute in (ss_pc x) in change (ss_pc x) with v end.
Ltac d6_g HS :=
  lazymatch goal with |- getr _ ?r = _ => d6_reg HS r end;
  cbn [sv_denot ew ewset Nat.eqb]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
(* a run's frame: memory kept outside the window [lo, hi); composed with AVw (memory kept since the entry) *)
Ltac d6_avw W mem0 lo hi Usp :=
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) |- _ =>
    let AVn := fresh "AVn" in
    assert (AVn : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
      aview tfibsegs (w_H W) m1 a = aview tfibsegs (w_H W) m0 a)
      by (apply (fw_win tfibsegs _ _ _ _ _ lo hi HFr);
          lazymatch goal with |- Forall _ ?rs => let v := eval vm_compute in rs in change rs with v end;
          repeat apply Forall_cons; try apply Forall_nil;
          cbn [YP09.r_whi YP09.r_wlo YP09.r_base base_val];
          first [left; lia | right; cbn [ew ewset Nat.eqb]; rewrite Usp; lia]);
    lazymatch goal with AV : forall a, _ -> _ -> aview _ _ m0 a = aview _ _ mem0 a |- _ =>
      let AV2 := fresh "AVw" in
      assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
        aview tfibsegs (w_H W) m1 a = aview tfibsegs (w_H W) mem0 a)
        by (intros a Ha Hn; rewrite (AVn a Ha Hn); exact (AV a Ha Hn));
      clear AV AVn; rename AV2 into AVw end end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  repeat match goal with H : context [with_vm_backing (m_vm_lazy (with_vm_backing _ _ _)) _ _] |- _ =>
    rewrite wvb_collapse in H end.
(* the run's writes: the frame region (based at sp = F = entry sp - 208) writes only [F+0x18, F+0x20) *)
Ltac d6_awr Usp :=
  first
    [ lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
        let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end
    | lazymatch goal with |- awr_ok ?sg ?Bv ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
        let rs' := eval vm_compute in rs in change (awr_ok sg Bv E rs' stk sp0 fp b0 bc ly own) end ];
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -208);
    [reflexivity | rewrite Usp; unfold cx_F; lia | cbn; lia | cbn; lia | apply awr_ok_nil].
(* the declared slot's value in the run's last state: the frame region's chunk at 0x18 holds e *)
Ltac d6_slot HS Usp e Hv :=
  lazymatch type of HS with st_ok _ ?Ex ?ss _ =>
    let r := eval vm_compute in (nth_error (ss_mem ss) 0) in
    lazymatch r with Some ?rg =>
      let HR := fresh "HR" in
      pose proof (fw_region_nth tfibsegs _ ss _ 0 rg HS ltac:(vm_compute; reflexivity)) as HR;
      rewrite restrict_mem in HR;
      eapply (fw_field tfibsegs Ex _ 2 _ _ _ _ _ _ 0x18 8 e _ HR Usp);
      [cbn [In]; left; reflexivity | exact Hv | change (8 * Z.of_N 8) with 64; lia | change (Z.of_N 8) with 8; lia]
    end end.

(* s3 = (text + close + 1) + text * (2^64 - 1) at 0x814e8/0x814dc: close + 1 *)
Lemma d6_sub_canon : forall a t, 0 <= a - t < M64 ->
  zcanon (a + zcanon (t * 18446744073709551615)) = a - t.
Proof.
  intros a t Ha. unfold zcanon, M64 in *. change (2 ^ 64) with 18446744073709551616 in *.
  replace (t * 18446744073709551615) with (- t + t * 18446744073709551616) by ring.
  rewrite Z_mod_plus_full, Z.add_mod_idemp_r by lia.
  replace (a + - t) with (a - t) by ring. apply Z.mod_small. exact Ha.
Qed.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis SEG_R : ex_seg_R B.
Hypothesis SEG_T : ex_seg_T B.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Lemma d6_cfg : forall (W : world tfibsegs) pc regs mem md Q,
  SRr tfibsegs W (cfg_at tfibsegs pc regs mem md) Q ->
  SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs)) md) Q.
Proof. intros W pc regs mem md Q H. exact H. Qed.

Definition d6_extra (cx : ecx) (d close : nat) : list word :=
  [Z_to_bv 64 (Z.of_nat d); Z_to_bv 64 (cx_t cx + Z.of_nat close); Z_to_bv 64 (cx_t cx); Z_to_bv 64 EX_MASK1].

Lemma d6_entry : forall cx i d f name nl ns nl2 close ly3 S3 W3 regs3 mem3 md3,
  dat_D6 B cx i d f name nl ns nl2 close ly3 S3 W3 regs3 mem3 md3 ->
  st_ok tfibsegs (Ereg regs3 (d6_extra cx d close)) ss_D6
    (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 EX_D6) mem3 (seg_rom tfibsegs))).
Proof.
  intros cx i d f name nl ns nl2 close ly3 S3 W3 regs3 mem3 md3
    ((HB & HC & HSL & R22 & R18 & R8 & HSC & Hit) & Hdc & Hnl & Hfe & V28 & V8 & R10 & _).
  pose proof (dd_bounds B cx HB) as (HFm & HFlo & HFhi & Ht4 & Htc & Hu4 & Huc).
  pose proof HB as ((HPRE & _) & _).
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct HC as (HJ & Hbl & HGL & Rsp & Rgp & Rtp & R25 & HSV & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  destruct HSL as (S18 & S20 & S30 & S38 & S40 & S48 & S50 & S58 & S60).
  pose proof (expected_m.decl_found _ _ _ _ _ _ _ Hdc) as (D1 & D2 & D3 & D4 & D5).
  pose proof HSC as (Hi & Hd & Hf & Hu & Hr).
  assert (HSTK : STK_expected = 208 + 8224) by reflexivity.
  rewrite restrict_mkst_fx.
  set (E := Ereg regs3 (d6_extra cx d close)).
  assert (Usp : bv_unsigned (ew E 2) = cx_F cx).
  { subst E. rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl), Rsp. apply unsigned_lit_small.
    unfold cx_F, cx_sp in *. lia. }
  assert (E32 : ew E 32 = Z_to_bv 64 (Z.of_nat d)) by (subst E; exact (ew_Ereg_extra regs3 _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (cx_t cx + Z.of_nat close)) by (subst E; exact (ew_Ereg_extra regs3 _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 (cx_t cx)) by (subst E; exact (ew_Ereg_extra regs3 _ 2)).
  assert (E35 : ew E 35 = Z_to_bv 64 EX_MASK1) by (subst E; exact (ew_Ereg_extra regs3 _ 3)).
  unfold ss_D6. apply (entry_st_ok_full tfibsegs); change (Ereg regs3 (d6_extra cx d close)) with E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, d6_frame.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
    split; [unfold cx_F, cx_sp in *; lia|]. split; [unfold cx_F, cx_sp in *; lia|]. split.
    { intros o Ho. apply (apresent_writable tfibsegs). apply Hpres. unfold cx_F, cx_sp in *. lia. }
    apply ex_chunks_ok. unfold d6_chunks.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]];
      cbn [fst snd Nat.add].
    + rewrite E32, unsigned_lit_small by lia. exact S18.
    + rewrite E33, unsigned_lit_small by lia. exact V28.
    + rewrite E34, unsigned_lit_small by lia. exact S58.
    + rewrite E35, unsigned_lit_small by (unfold EX_MASK1; lia). exact S60.
  - cbn. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp. change (2 ^ 4) with 16. split; [|exact I].
    unfold cx_F, cx_sp in *. split; [lia|].
    replace (spZ (cx_regs cx) - 208) with (spZ (cx_regs cx) + (-13) * 16) by lia. rewrite Z_mod_plus_full.
    split; [exact Hal16 | lia].
Qed.

(* ex_com after a step that changes memory only in the declared slot [F+0x18, F+0x20) (after FMW_ex_decl_base.v
   dd_com_kept) *)
Lemma d6_com_kept : forall cx ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4,
  ex_base B cx -> ex_com B cx ly3 S3 W3 regs3 mem3 md3 ->
  ajournal tfibsegs B STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] ly3 S3 W3 mem4 md4 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (cx_F cx + 0x18 <= a < cx_F cx + 0x20) ->
     aview tfibsegs (w_H W3) mem4 a = aview tfibsegs (w_H W3) mem3 a) ->
  getr regs4 2 = getr regs3 2 -> getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  getr regs4 25 = getr regs3 25 ->
  ex_com B cx ly3 S3 W3 regs4 mem4 md4.
Proof.
  intros cx ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 HB HC HJ4 HK Q2 Q3 Q4 Q25.
  pose proof (dd_bounds B cx HB) as (HFm & HFlo & HFhi & _).
  pose proof asan_consts as (C1 & _).
  assert (FS : STK_expected = 8432) by reflexivity.
  destruct HC as (HJ & Hbl & HGL & R2 & R3 & R4 & R25 & HSV & HRO & Ct & Cu & Kt & Ku).
  assert (KL : fw_low tfibsegs (w_H W3) mem3 mem4) by (intros a Ha; apply HK; lia).
  split; [exact HJ4|]. split; [exact Hbl|].
  split; [exact (fw_glob_low tfibsegs W3 mem3 mem4 _ _ _ _ KL HGL)|].
  split; [rewrite Q2; exact R2|]. split; [rewrite Q3; exact R3|]. split; [rewrite Q4; exact R4|].
  split; [rewrite Q25; exact R25|].
  split.
  { unfold ex_saved_ok, EX_SAVED in *.
    repeat match goal with H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H end.
    repeat (apply Forall_cons; [|]); try apply Forall_nil; cbn [fst snd] in *;
      (eapply dd_val_kept; [|eassumption]); intros x Hx; apply HK; change (Z.of_nat 8) with 8 in Hx; lia. }
  split; [exact (fw_rodata_low tfibsegs B _ mem3 mem4 fmw_segs_low KL HRO)|].
  split; [exact (fw_cstr_low tfibsegs W3 mem3 mem4 _ _ KL Ct)|].
  split; [exact (fw_cstr_low tfibsegs W3 mem3 mem4 _ _ KL Cu)|].
  split; [exact Kt | exact Ku].
Qed.

Theorem decl_D6_holds : dseg_D6 B.
Proof.
  intros cx i d f name nl ns nl2 close ly3 S3 W3 regs3 mem3 md3 HLF HD.
  pose proof LAWS as HL. pose proof fmw_segs_low as Hsegs. pose proof fmw_wx as Hwx.
  pose proof (d6_entry cx i d f name nl ns nl2 close ly3 S3 W3 regs3 mem3 md3 HD) as HS.
  destruct HD as ((HB & HC & HSL & R22 & R18 & R8 & HSC & Hit) & Hdc & Hnl & Hfe & V28 & V8 & R10 & R20 & R21 & R24
    & R19 & R9).
  pose proof (dd_bounds B cx HB) as (HFm & HFlo & HFhi & Ht4 & Htc & Hu4 & Huc).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HC as (HJ & Hbl & HGL & Rsp & Rgp & Rtp & R25 & HSV & _).
  pose proof HSC as (Hi & Hd & Hf & Hu & Hr).
  pose proof (expected_m.decl_found _ _ _ _ _ _ _ Hdc) as (D1 & D2 & D3 & D4 & D5).
  assert (HSTK : STK_expected = 208 + 8224) by reflexivity.
  set (E := Ereg regs3 (d6_extra cx d close)) in *.
  assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs3 q)
    by (intros n q Hn'; subst E; apply ew_Ereg_nat; exact Hn').
  assert (E32 : ew E 32 = Z_to_bv 64 (Z.of_nat d)) by (subst E; exact (ew_Ereg_extra regs3 _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (cx_t cx + Z.of_nat close)) by (subst E; exact (ew_Ereg_extra regs3 _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 (cx_t cx)) by (subst E; exact (ew_Ereg_extra regs3 _ 2)).
  assert (E35 : ew E 35 = Z_to_bv 64 EX_MASK1) by (subst E; exact (ew_Ereg_extra regs3 _ 3)).
  assert (Usp : bv_unsigned (ew E 2) = cx_F cx).
  { rewrite (EE 2%nat 2%bv eq_refl), Rsp. apply unsigned_lit_small. unfold cx_F, cx_sp in *. lia. }
  assert (E10 : ew E 10 = Z_to_bv 64 (if MM.plain_name (skipn nl2 (cx_ub cx)) then 1 else 0))
    by (rewrite (EE 10%nat 10%bv eq_refl); exact R10).
  assert (Hpv : 0 <= (if MM.plain_name (skipn nl2 (cx_ub cx)) then 1 else 0) < 2 ^ 64)
    by (destruct (MM.plain_name (skipn nl2 (cx_ub cx))); lia).
  assert (Hm1 : MM.plain_name (skipn nl2 (cx_ub cx)) = true -> MM.matches (cx_tb cx) (cx_ub cx) ns nl2 = true)
    by (intros Hp; apply dm_matches; tauto).
  assert (Hm0 : MM.plain_name (skipn nl2 (cx_ub cx)) = false -> MM.matches (cx_tb cx) (cx_ub cx) ns nl2 = false).
  { intros Hp. destruct (MM.matches (cx_tb cx) (cx_ub cx) ns nl2) eqn:Hm; [|reflexivity].
    apply dm_matches in Hm. destruct Hm as (_ & _ & Hp'). congruence. }
  assert (SHOK : sh_ok tfibsegs EX_Bx [] E
    (mrestrict (w_H W3) (ms_mem (mkst regs3 (Z_to_bv 64 EX_D6) mem3 (seg_rom tfibsegs))))) by constructor.
  assert (AVw : forall a, 0 <= a < 2 ^ 64 -> ~ (cx_F cx + 0x18 <= a < cx_F cx + 0x20) ->
    aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W3) mem3 a) by reflexivity.
  change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 EX_D6) mem3 (seg_rom tfibsegs))) in HJ.
  unfold cfg_at. change (w64 EX_D6) with (Z_to_bv 64 EX_D6).
  (* 0x8150c s7 = ld F+0x58; 0x81510 beqz a0 *)
  aj_run_tok EX_tbl_ok HS HJ SHOK EX_Bspan.
  { d6_awr Usp. }
  d6_avw W3 mem3 (cx_F cx + 0x18) (cx_F cx + 0x20) Usp.
  srr_branch_tok EX_tbl_ok HS SHOK EX_Bspan.
  - (* plain's answer 0: plain_name false, the declaration does not match; 0x814c8 .. 0x814e0 -> EX_L at close + 1 *)
    rewrite branch_eq_U, (U_atom E 10 _ E10 Hpv), U_SLit in Hc. change (zcanon 0) with 0 in Hc.
    destruct (MM.plain_name (skipn nl2 (cx_ub cx))) eqn:Hpn; try rewrite Hpn in Hc; cbn in Hc; [discriminate Hc|].
    clear Hc.
    pose proof (dd_scan_skip cx i d f name nl ns nl2 close HSC Hit Hdc (Hm0 ltac:(first [exact Hpn | reflexivity])))
      as (HSC' & Hlt).
    aj_run_to_tok EX_tbl_ok HS HJ SHOK EX_Bspan EX_L; [d6_awr Usp|].
    d6_avw W3 mem3 (cx_F cx + 0x18) (cx_F cx + 0x20) Usp.
    assert (H18 : sv_denot E (SOff 32 0) = Z_to_bv 64 (Z.of_nat d))
      by (apply fw_sv_U; apply (U_atom E 32 _ E32); lia).
    assert (V18 : val_mem tfibsegs (rdW W3 (ms_mem ms0)) (cx_F cx + 0x18) 8 (Z.of_nat d))
      by (d6_slot HS Usp (SOff 32 0) H18).
    d6_mk HS. apply (d6_cfg _ EX_L).
    apply (HLF (S close) d (pred f) ly3 S3 W3 _ _ _ Hlt).
    split; [exact HB|]. split.
    { apply (d6_com_kept cx ly3 S3 W3 regs3 mem3 md3 _ _ _ HB HC HJ AVw); d6_g HS; apply EE; reflexivity. }
    split.
    { apply (dd_slots_d B cx W3 mem3 _ d d HB HSL); [intros a Ha; apply AVw; lia | exact V18]. }
    split.
    { split; [d6_g HS; rewrite E34; reflexivity|].
      split; [d6_g HS; rewrite (EE 22%nat 22%bv eq_refl); exact R22|].
      split; [d6_g HS; rewrite (EE 18%nat 18%bv eq_refl); exact R18|].
      d6_g HS; rewrite (EE 8%nat 8%bv eq_refl); exact R8. }
    split; [exact HSC'|].
    split.
    { lazymatch goal with |- getr _ ?r = _ => d6_reg HS r end. apply fw_sv_U.
      rewrite U_SAlu, U_SMd, (U_atom_off E 33 (cx_t cx + Z.of_nat close) 1 E33), (U_atom E 34 (cx_t cx) E34), U_SLit
        by lia.
      cbn [zalu_raw zmd_raw]. change (zcanon 18446744073709551615) with 18446744073709551615.
      rewrite d6_sub_canon by (unfold M64; lia). lia. }
    split; [d6_g HS; first [reflexivity | apply bv_eq; vm_compute; reflexivity]|].
    split; [d6_g HS; first [reflexivity | apply bv_eq; vm_compute; reflexivity]|].
    d6_g HS. rewrite E35. reflexivity.
  - (* plain's answer 1: the declaration matches; 0x81514 a2 = declared + 1, a0 = 1, a1 = 16; bltu a1, a2 *)
    rewrite branch_eq_U, (U_atom E 10 _ E10 Hpv), U_SLit in Hc. change (zcanon 0) with 0 in Hc.
    destruct (MM.plain_name (skipn nl2 (cx_ub cx))) eqn:Hpn; try rewrite Hpn in Hc; cbn in Hc; [|discriminate Hc].
    clear Hc.
    pose proof (Hm1 ltac:(first [exact Hpn | reflexivity])) as Hm.
    aj_run_tok EX_tbl_ok HS HJ SHOK EX_Bspan; [d6_awr Usp|].
    d6_avw W3 mem3 (cx_F cx + 0x18) (cx_F cx + 0x20) Usp.
    srr_branch_tok EX_tbl_ok HS SHOK EX_Bspan.
    + (* 16 < declared + 1: EX_R with a0 = 1, the scan's answer *)
      rewrite branch_ltu_U, U_SLit, (U_atom_off E 32 (Z.of_nat d) 1 E32) in Hc by lia.
      change (zcanon 16) with 16 in Hc. apply Z.ltb_lt in Hc.
      aj_run_to_tok EX_tbl_ok HS HJ SHOK EX_Bspan EX_R; [d6_awr Usp|].
      d6_avw W3 mem3 (cx_F cx + 0x18) (cx_F cx + 0x20) Usp.
      d6_mk HS. apply (d6_cfg _ EX_R).
      apply (SEG_R cx ly3 S3 W3 _ _ _ HB).
      * apply (d6_com_kept cx ly3 S3 W3 regs3 mem3 md3 _ _ _ HB HC HJ AVw); d6_g HS; apply EE; reflexivity.
      * d6_g HS. rewrite (dd_res_full cx i d f name nl ns nl2 close HSC Hit Hdc Hm ltac:(lia)). reflexivity.
    + (* declared + 1 <= 16: 0x81528 sd a2 F+0x18; EX_T *)
      rewrite branch_ltu_U, U_SLit, (U_atom_off E 32 (Z.of_nat d) 1 E32) in Hc by lia.
      change (zcanon 16) with 16 in Hc. apply Z.ltb_ge in Hc.
      aj_run_to_tok EX_tbl_ok HS HJ SHOK EX_Bspan EX_T; [d6_awr Usp|].
      d6_avw W3 mem3 (cx_F cx + 0x18) (cx_F cx + 0x20) Usp.
      assert (H18 : sv_denot E (SOff 32 1) = Z_to_bv 64 (Z.of_nat (S d)))
        by (apply fw_sv_U; rewrite (U_atom_off E 32 (Z.of_nat d) 1 E32) by lia; lia).
      assert (V18 : val_mem tfibsegs (rdW W3 (ms_mem ms1)) (cx_F cx + 0x18) 8 (Z.of_nat (S d)))
        by (d6_slot HS Usp (SOff 32 1) H18).
      d6_mk HS. apply (d6_cfg _ EX_T).
      apply (SEG_T cx i d f name nl ns nl2 close ly3 S3 W3 _ _ _ HLF).
      split; [exact HB|]. split.
      { apply (d6_com_kept cx ly3 S3 W3 regs3 mem3 md3 _ _ _ HB HC HJ AVw); d6_g HS; apply EE; reflexivity. }
      split.
      { apply (dd_slots_d B cx W3 mem3 _ d (S d) HB HSL); [intros a Ha; apply AVw; lia | exact V18]. }
      split.
      { split; [d6_g HS; rewrite E34; reflexivity|].
        split; [d6_g HS; rewrite (EE 22%nat 22%bv eq_refl); exact R22|].
        split; [d6_g HS; rewrite (EE 18%nat 18%bv eq_refl); exact R18|].
        d6_g HS; rewrite (EE 8%nat 8%bv eq_refl); exact R8. }
      split; [exact HSC|]. split; [exact Hit|]. split; [lia|]. split; [exact Hdc|]. split; [exact Hm|].
      split; [eapply dd_val_kept; [|exact V8]; intros x Hx; apply AVw; change (Z.of_nat 8) with 8 in Hx; lia|].
      split; [eapply dd_val_kept; [|exact V28]; intros x Hx; apply AVw; change (Z.of_nat 8) with 8 in Hx; lia|].
      split; [d6_g HS; rewrite (EE 20%nat 20%bv eq_refl); exact R20|].
      split; [d6_g HS; rewrite (EE 21%nat 21%bv eq_refl); exact R21|].
      split; [d6_g HS; rewrite (EE 24%nat 24%bv eq_refl); exact R24|].
      split; [d6_g HS; rewrite (EE 19%nat 19%bv eq_refl); exact R19|].
      d6_g HS; rewrite (EE 9%nat 9%bv eq_refl); exact R9.
Qed.
End W.

Print Assumptions decl_D6_holds.
