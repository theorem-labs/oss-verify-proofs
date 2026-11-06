(* G4.ExDecl.DeclD5B: dseg_D5 (FMW_ex_decl_base.v:385), expected 0x814c0..0x8150c (fuzz_manifest.c:162) on fm.asan,
   after strncmp (uri, ns, nl2) answered v (expected.dis lines 229-232, 238-247):
   0x814c0 `beqz a0`:
   - v <> 0 (the namespace differs from the uri's first nl2 bytes): 0x814c4 s7 = ld F+0x58 = text, a1 = ld F+0x28 =
     text + close, 0x814e4 s7 = text, s3 = a1 - s7 = close, s1 = 64, a5 = 58, a6 = ld F+0x60 = the mask, 0x814dc
     s3 + 1: EX_L at close + 1 (the declaration does not match: dd_scan_skip);
   - v = 0: 0x814fc a0 = ld F+0x28 + s10 = uri + nl2 (local), sd a0 F+8, 0x81508 jal plain (A_plain 0x81778,
     ra 0x8150c): a program call, composed with plain_spec (FMH_Fn.v:250) as YCbq.v aj_call does; at the return
     0x8150c = EX_D6 the invariant dat_D6 holds and dseg_D6 finishes. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_ex_decl_d5_kits.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel expected_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the three frame slots the segment loads (F+0x28 close, F+0x58 text, F+0x60 the mask) as chunks holding the extra
   atoms 32..34 (FMW_ex_ret.v ex_slot_chunks); the write window [F+8, F+0x10) is the store of local at 0x81504 *)
Definition d5_chunks : list (Z * nat) := [(0x28, 0%nat); (0x58, 1%nat); (0x60, 2%nat)].
Definition d5_frame : YP09.region := YP09.mkRegion (Some 2%nat) 0 0x68 8 0x10 (ex_slot_chunks d5_chunks).
Definition ss_D5 : sstate := mkSS EX_D5 sr_atoms [d5_frame] None (mkFacts [(2%nat, mkAF (2^46) (2^47) 4)] [] []).

(* ---- walk tactics (after FMW_plain.v fw_reg / pl_mk / pl_g / pl_avw) ---- *)
Ltac d5_reg HS r :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    rewrite (st_ok_restrict_reg segs H E ss ms r HS); change (sr_get (ss_regs ss) r) with e end.
Ltac d5_mk HS := rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl);
  lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?x)] =>
    let v := eval vm_compute in (ss_pc x) in change (ss_pc x) with v end.
Ltac d5_g HS :=
  lazymatch goal with |- getr _ ?r = _ => d5_reg HS r end;
  cbn [sv_denot ew ewset Nat.eqb]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
(* a run's frame: memory kept outside the window [lo, hi) *)
Ltac d5_avw W lo hi Usp AVn :=
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) |- _ =>
    assert (AVn : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
      aview tfibsegs (w_H W) m1 a = aview tfibsegs (w_H W) m0 a)
      by (apply (fw_win tfibsegs _ _ _ _ _ lo hi HFr);
          lazymatch goal with |- Forall _ ?rs => let v := eval vm_compute in rs in change rs with v end;
          repeat apply Forall_cons; try apply Forall_nil;
          cbn [YP09.r_whi YP09.r_wlo YP09.r_base base_val];
          first [left; lia | right; cbn [ew ewset Nat.eqb]; rewrite Usp; lia]) end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  repeat match goal with H : context [with_vm_backing (m_vm_lazy (with_vm_backing _ _ _)) _ _] |- _ =>
    rewrite wvb_collapse in H end.

(* the call's argument local = s10 + ld F+0x28 = (uri - text - ns) + (text + ns + nl2) = uri + nl2 *)
Lemma d5_U_local : forall E t u ns nl2,
  bv_unsigned (ew E 26) = (u - t - Z.of_nat ns) mod 2 ^ 64 -> bv_unsigned (ew E 32) = t + Z.of_nat (ns + nl2) ->
  0 <= u + Z.of_nat nl2 < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SOff 26 0) (SOff 32 0)) = u + Z.of_nat nl2.
Proof.
  intros E t u ns nl2 H26 H32 Hr. rewrite U_SAlu, !U_SOff, H26, H32. cbn [zalu_raw]. unfold zcanon, M64.
  rewrite !Z.add_0_r, Z.mod_mod by lia. rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r.
  replace (u - t - Z.of_nat ns + (t + Z.of_nat (ns + nl2))) with (u + Z.of_nat nl2) by lia.
  apply Z.mod_small. exact Hr.
Qed.

(* s3 = a1 - s7 + 1 = (text + close) - text + 1 (the executor's sub is an add of the product by -1) *)
Lemma d5_U_s3 : forall E t c, bv_unsigned (ew E 32) = t + c -> bv_unsigned (ew E 33) = t -> 0 <= t -> 0 <= c ->
  t + c + 1 < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SOff 32 1) (SMd M_MUL (SOff 33 0) (SLit 18446744073709551615))) = c + 1.
Proof.
  intros E t c H32 H33 Ht Hc Hr. rewrite U_SAlu, U_SMd, !U_SOff, U_SLit, H32, H33.
  cbn [zalu_raw zmd_raw]. unfold zcanon, M64.
  rewrite Z.add_0_r, (Z.mod_small t) by lia. rewrite (Z.mod_small (t + c + 1)) by lia.
  rewrite (Z.mod_small 18446744073709551615) by lia.
  rewrite Zplus_mod_idemp_r.
  replace (t + c + 1 + t * 18446744073709551615) with (c + 1 + t * 2 ^ 64) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

(* the run's write window [F+8, F+0x10) lies in expected's stack: the frame region is based at F = sp0 - 208 *)
Ltac d5_awr Usp :=
  first
    [ lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
        let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end
    | lazymatch goal with |- awr_ok ?sg ?Bv ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
        let rs' := eval vm_compute in rs in change (awr_ok sg Bv E rs' stk sp0 fp b0 bc ly own) end ];
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -208);
  [reflexivity | rewrite Usp; unfold cx_F; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil].
(* a callee-saved register after the call: the callee kept it, the run kept the entry's *)
Ltac d5_pres HP Rc z := exact (eq_trans (HP z ltac:(unfold acallee_saved; lia)) Rc).

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis SD6 : dseg_D6 B.
Hypothesis PLAIN : plain_spec tfibsegs B.
Hypothesis IMG : fm_img_facts tfibsegs B.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Definition d5_extra (cx : ecx) (close : nat) : list word :=
  [Z_to_bv 64 (cx_t cx + Z.of_nat close); Z_to_bv 64 (cx_t cx); Z_to_bv 64 EX_MASK1].

Lemma d5_entry : forall cx d close ly3 S3 W3 regs3 mem3 md3,
  ex_base B cx -> ex_com B cx ly3 S3 W3 regs3 mem3 md3 -> ex_slots cx W3 mem3 d ->
  val_mem tfibsegs (rdW W3 mem3) (cx_F cx + 0x28) 8 (cx_t cx + Z.of_nat close) ->
  (close < length (cx_tb cx))%nat ->
  st_ok tfibsegs (Ereg regs3 (d5_extra cx close)) ss_D5
    (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 EX_D5) mem3 (seg_rom tfibsegs))).
Proof.
  intros cx d close ly3 S3 W3 regs3 mem3 md3 HB HC HSL V28 Hcl.
  pose proof (dd_bounds B cx HB) as (HFm & HFlo & HFhi & Ht4 & Htc & Hu4 & Huc).
  pose proof HB as ((HPRE & _) & _).
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct HC as (HJ & Hbl & HGL & Rsp & Rgp & Rtp & R25 & HSV & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  destruct HSL as (S18 & S20 & S30 & S38 & S40 & S48 & S50 & S58 & S60).
  assert (HSTK : STK_expected = 208 + 8224) by reflexivity.
  rewrite restrict_mkst_fx.
  set (E := Ereg regs3 (d5_extra cx close)).
  assert (Usp : bv_unsigned (ew E 2) = cx_F cx).
  { subst E. rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl), Rsp. apply unsigned_lit_small.
    unfold cx_F, cx_sp in *. lia. }
  assert (E32 : ew E 32 = Z_to_bv 64 (cx_t cx + Z.of_nat close)) by (subst E; exact (ew_Ereg_extra regs3 _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (cx_t cx)) by (subst E; exact (ew_Ereg_extra regs3 _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 EX_MASK1) by (subst E; exact (ew_Ereg_extra regs3 _ 2)).
  unfold ss_D5. apply (entry_st_ok_full tfibsegs); change (Ereg regs3 (d5_extra cx close)) with E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, d5_frame.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
    split; [unfold cx_F, cx_sp in *; lia|]. split; [unfold cx_F, cx_sp in *; lia|]. split.
    { intros o Ho. apply (apresent_writable tfibsegs). apply Hpres. unfold cx_F, cx_sp in *. lia. }
    apply ex_chunks_ok. unfold d5_chunks.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd Nat.add].
    + rewrite E32, unsigned_lit_small by lia. exact V28.
    + rewrite E33, unsigned_lit_small by lia. exact S58.
    + rewrite E34, unsigned_lit_small by (unfold EX_MASK1; lia). exact S60.
  - cbn. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp. change (2 ^ 4) with 16. split; [|exact I].
    unfold cx_F, cx_sp in *. split; [lia|].
    replace (spZ (cx_regs cx) - 208) with (spZ (cx_regs cx) + (-13) * 16) by lia. rewrite Z_mod_plus_full.
    split; [exact Hal16 | lia].
Qed.

(* memory facts across a step that keeps the bytes [a, a + n) (the world may grow) *)
Lemma d5_val_kept : forall (W W' : world tfibsegs) mem mem' a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview tfibsegs (w_H W') mem' x = aview tfibsegs (w_H W) mem x) ->
  val_mem tfibsegs (rdW W mem) a n v -> val_mem tfibsegs (rdW W' mem') a n v.
Proof.
  intros W W' mem mem' a n v HA Hv k Hk. rewrite (mbyte_of_aview tfibsegs (w_H W) (w_H W') mem mem');
    [apply Hv; exact Hk|]. apply HA. lia.
Qed.

Lemma d5_slots_kept : forall cx (W3 W2 : world tfibsegs) mem3 mem2 d,
  ex_slots cx W3 mem3 d ->
  (forall a, cx_F cx + 0x18 <= a < cx_F cx + 0x68 -> aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W3) mem3 a) ->
  ex_slots cx W2 mem2 d.
Proof.
  intros cx W3 W2 mem3 mem2 d (S18 & S20 & S30 & S38 & S40 & S48 & S50 & S58 & S60) HK.
  unfold ex_slots.
  repeat split; (eapply d5_val_kept; [|eassumption]); intros x Hx; apply HK; change (Z.of_nat 8) with 8 in Hx; lia.
Qed.

(* ex_com after the call of plain: the composed journal, the callee's post (blocks, statics), the frame bytes from
   F + 0x18 up (above the callee's sp F), the callee-saved registers; rodata and the strings over the callee's
   journal (G5's FMW_as_ruled.v:141-148, here with the empty footprint) *)
Lemma d5_com_call : forall cx ly3 S3 W3 regs3 mem3 md3 memc mdc ly2 S2 W2 regs2 mem2 md2,
  ex_base B cx -> ex_com B cx ly3 S3 W3 regs3 mem3 md3 -> fw_low tfibsegs (w_H W3) mem3 memc ->
  ajournal tfibsegs B STK_plain (cx_F cx) [] ly3 S3 W3 memc mdc [] ly2 S2 W2 mem2 md2 0 ->
  ajournal tfibsegs B STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] ly2 S2 W2 mem2 md2 0 ->
  ablocks B ly2 S2 = ablocks B ly3 S3 ->
  fm_glob tfibsegs W2 mem2 (cx_live cx) (cx_peak cx) (cx_cnt cx) (cx_fail cx) ->
  (forall a, cx_F cx + 0x18 <= a < cx_F cx + 208 -> aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W3) mem3 a) ->
  getr regs2 2 = getr regs3 2 -> getr regs2 3 = getr regs3 3 -> getr regs2 4 = getr regs3 4 ->
  getr regs2 25 = getr regs3 25 ->
  ex_com B cx ly2 S2 W2 regs2 mem2 md2.
Proof.
  intros cx ly3 S3 W3 regs3 mem3 md3 memc mdc ly2 S2 W2 regs2 mem2 md2 HB HC KL HJc HJ2 Hbl2 HG2 HK Q2 Q3 Q4 Q25.
  destruct HC as (HJ & Hbl & HGL & R2 & R3 & R4 & R25 & HSV & HRO & Ct & Cu & Kt & Ku).
  assert (Hinc : forall x, In x (ablocks B ly3 S3) -> In x (ablocks B ly2 S2)) by (intros x Hx; rewrite Hbl2; exact Hx).
  assert (HFP : forall a, inFP [] a -> in_img tfibsegs a) by (intros a Ha; exfalso; exact (inFP_nil a Ha)).
  pose proof (fw_rodata_low tfibsegs B _ mem3 memc fmw_segs_low KL HRO) as HROc.
  assert (HRO2 : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W2) mem2)).
  { apply (d5k_arodata_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc).
    - intros (r & Hr & _). destruct Hr.
    - intros a _ Ha. exact (inFP_nil a Ha).
    - exact HROc. }
  split; [exact HJ2|]. split; [rewrite Hbl2; exact Hbl|]. split; [exact HG2|].
  split; [rewrite Q2; exact R2|]. split; [rewrite Q3; exact R3|]. split; [rewrite Q4; exact R4|].
  split; [rewrite Q25; exact R25|].
  split.
  { unfold ex_saved_ok, EX_SAVED in *.
    repeat match goal with H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H end.
    repeat (apply Forall_cons; [|]); try apply Forall_nil; cbn [fst snd] in *;
      (eapply d5_val_kept; [|eassumption]); intros x Hx; apply HK; change (Z.of_nat 8) with 8 in Hx; lia. }
  split; [exact HRO2|].
  split; [exact (d5k_cstr_ok_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IMG HJc Hinc HFP HRO2 Kt
                   (fw_cstr_low tfibsegs W3 mem3 memc _ _ KL Ct))|].
  split; [exact (d5k_cstr_ok_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IMG HJc Hinc HFP HRO2 Ku
                   (fw_cstr_low tfibsegs W3 mem3 memc _ _ KL Cu))|].
  split; [exact (d5k_cstr_kept_kept B _ _ _ _ _ _ Hinc Kt) | exact (d5k_cstr_kept_kept B _ _ _ _ _ _ Hinc Ku)].
Qed.

Theorem decl_D5_holds : dseg_D5 B.
Proof.
  intros cx i d f name nl ns nl2 close v ly3 S3 W3 regs3 mem3 md3 HLF HD.
  pose proof LAWS as HL. pose proof fmw_segs_low as Hsegs. pose proof fmw_wx as Hwx.
  destruct HD as ((HB & HC & HSL & R22 & R18 & R8 & HSC & Hit) & Hdc & Hnl & V28 & R10 & Hv & Hveq & R20 & R21 & R24
    & R19 & R9 & R26).
  pose proof (expected_m.decl_found _ _ _ _ _ _ _ Hdc) as (D1 & D2 & D3 & D4 & D5).
  pose proof (d5_entry cx d close ly3 S3 W3 regs3 mem3 md3 HB HC HSL V28 D4) as HS.
  pose proof (dd_bounds B cx HB) as (HFm & HFlo & HFhi & Ht4 & Htc & Hu4 & Huc).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HC as (HJ & Hbl & HGL & Rsp & Rgp & Rtp & R25 & HSV & HRO & Ct & Cu & Kt & Ku).
  assert (HSTK : STK_expected = 208 + 8224) by reflexivity.
  assert (HSP : STK_plain = 8224) by reflexivity.
  set (E := Ereg regs3 (d5_extra cx close)) in *.
  assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs3 q)
    by (intros n q Hn'; subst E; apply ew_Ereg_nat; exact Hn').
  assert (E32 : ew E 32 = Z_to_bv 64 (cx_t cx + Z.of_nat close)) by (subst E; exact (ew_Ereg_extra regs3 _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (cx_t cx)) by (subst E; exact (ew_Ereg_extra regs3 _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 EX_MASK1) by (subst E; exact (ew_Ereg_extra regs3 _ 2)).
  assert (Usp : bv_unsigned (ew E 2) = cx_F cx).
  { rewrite (EE 2%nat 2%bv eq_refl), Rsp. apply unsigned_lit_small. unfold cx_F, cx_sp in *. lia. }
  assert (U10 : U E (SOff 10 0) = v) by (apply U_atom; [rewrite (EE 10%nat 10%bv eq_refl); exact R10 | exact Hv]).
  assert (SHOK : sh_ok tfibsegs EX_Bx [] E
    (mrestrict (w_H W3) (ms_mem (mkst regs3 (Z_to_bv 64 EX_D5) mem3 (seg_rom tfibsegs))))) by constructor.
  change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 EX_D5) mem3 (seg_rom tfibsegs))) in HJ.
  unfold cfg_at. change (w64 EX_D5) with (Z_to_bv 64 EX_D5).
  srr_branch_tok EX_tbl_ok HS SHOK EX_Bspan.
  - (* v = 0: the namespace is the uri's first nl2 bytes; local = uri + nl2 at F+8, the call of plain *)
    rewrite branch_eq_U, U10, U_SLit in Hc. change (zcanon 0) with 0 in Hc. apply Z.eqb_eq in Hc.
    pose proof (proj1 Hveq Hc) as Hfe.
    aj_run_tok EX_tbl_ok HS HJ SHOK EX_Bspan.
    { d5_awr Usp. }
    d5_avw W3 (cx_F cx + 8) (cx_F cx + 0x10) Usp AVw.
    assert (KL : fw_low tfibsegs (w_H W3) mem3 (ms_mem ms)) by (intros a Ha; apply AVw; lia).
    assert (HU : U E (SAlu ALU_ADD (SOff 26 0) (SOff 32 0)) = cx_u cx + Z.of_nat nl2).
    { apply (d5_U_local E (cx_t cx) (cx_u cx) ns nl2).
      - rewrite (EE 26%nat 26%bv eq_refl), R26. unfold w64. rewrite Z_to_bv_unsigned. reflexivity.
      - rewrite E32, unsigned_lit_small by lia. lia.
      - lia. }
    assert (R1c : getr (ms_regs ms) 1 = Z_to_bv 64 529676) by (d5_g HS; reflexivity).
    assert (R2c : getr (ms_regs ms) 2 = getr regs3 2) by (d5_g HS; apply EE; reflexivity).
    assert (R3c : getr (ms_regs ms) 3 = getr regs3 3) by (d5_g HS; apply EE; reflexivity).
    assert (R4c : getr (ms_regs ms) 4 = getr regs3 4) by (d5_g HS; apply EE; reflexivity).
    assert (R8c : getr (ms_regs ms) 8 = getr regs3 8) by (d5_g HS; apply EE; reflexivity).
    assert (R9c : getr (ms_regs ms) 9 = getr regs3 9) by (d5_g HS; apply EE; reflexivity).
    assert (R18c : getr (ms_regs ms) 18 = getr regs3 18) by (d5_g HS; apply EE; reflexivity).
    assert (R19c : getr (ms_regs ms) 19 = getr regs3 19) by (d5_g HS; apply EE; reflexivity).
    assert (R20c : getr (ms_regs ms) 20 = getr regs3 20) by (d5_g HS; apply EE; reflexivity).
    assert (R21c : getr (ms_regs ms) 21 = getr regs3 21) by (d5_g HS; apply EE; reflexivity).
    assert (R22c : getr (ms_regs ms) 22 = getr regs3 22) by (d5_g HS; apply EE; reflexivity).
    assert (R24c : getr (ms_regs ms) 24 = getr regs3 24) by (d5_g HS; apply EE; reflexivity).
    assert (R25c : getr (ms_regs ms) 25 = getr regs3 25) by (d5_g HS; apply EE; reflexivity).
    assert (R10c : getr (ms_regs ms) 10 = w64 (cx_u cx + Z.of_nat nl2))
      by (d5_reg HS (10%bv : bv 5); unfold w64; apply fw_sv_U; exact HU).
    assert (V8 : val_mem tfibsegs (rdW W3 (ms_mem ms)) (cx_F cx + 8) 8 (cx_u cx + Z.of_nat nl2)).
    { pose proof (fw_region_nth tfibsegs _ _ _ 0 _ HS eq_refl) as HR. rewrite restrict_mem in HR.
      apply (fw_field tfibsegs E _ 2%nat (cx_F cx) _ _ _ _ _ 8 8%N (SAlu ALU_ADD (SOff 26 0) (SOff 32 0))
        (cx_u cx + Z.of_nat nl2) HR Usp).
      - cbn. tauto.
      - apply fw_sv_U. exact HU.
      - replace (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) by reflexivity. lia.
      - cbn. lia. }
    assert (Hspc : spZ (ms_regs ms) = cx_F cx).
    { unfold spZ. rewrite R2c, Rsp. unfold w64. apply unsigned_lit_small. lia. }
    pose proof HB as ((HPRE & _) & _ & _ & _ & _ & _ & _ & _ & Hlu & _).
    pose proof HPRE as (_ & _ & _ & Hgp0 & Htp0 & _).
    d5_mk HS.
    eapply SRr_bind.
    { apply (PLAIN ly3 S3 W3 (ms_regs ms) (ms_mem ms) _ [] (cx_u cx + Z.of_nat nl2) (skipn nl2 (cx_ub cx))
        (cx_live cx) (cx_peak cx) (cx_cnt cx) (cx_fail cx)).
      - split.
        + apply (afn_pre_at tfibsegs B STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx)
            (cx_md cx) [] ly3 S3 W3 (ms_mem ms) _ 0 (ms_regs ms) STK_plain (-208) [] HJ).
          * rewrite Hspc. unfold cx_F. lia.
          * reflexivity.
          * lia.
          * lia.
          * lia.
          * rewrite R1c. apply ret_ok_even. rewrite unsigned_lit_small by lia. reflexivity.
          * unfold raZ. rewrite R1c, unsigned_lit_small by lia. lia.
          * rewrite R3c, Rgp. exact Hgp0.
          * rewrite R4c, Rtp. exact Htp0.
          * apply achain_low. unfold s0Z. rewrite R8c, R8. unfold w64. rewrite unsigned_lit_small by lia. lia.
        + exact (fw_rodata_low tfibsegs B _ mem3 (ms_mem ms) fmw_segs_low KL HRO).
      - exact (fw_glob_low tfibsegs W3 mem3 (ms_mem ms) _ _ _ _ KL HGL).
      - exact R10c.
      - apply (fw_cstr_low tfibsegs W3 mem3 (ms_mem ms) _ _ KL). apply (dd_cstr_suffix W3 mem3 (cx_u cx) (cx_ub cx) nl2 Cu).
        lia.
      - rewrite length_skipn. lia. }
    intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJc & HP2 & H10c & Hbl2 & HG2).
    rewrite R1c.
    change (mkCfg (mkst regs2 (Z_to_bv 64 529676) mem2 (seg_rom tfibsegs)) md2)
      with (cfg_at tfibsegs EX_D6 regs2 mem2 md2).
    rewrite Hspc in HJc.
    pose proof (ajournal_sub tfibsegs B HL Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HJc
      ltac:(rewrite HSTK, HSP; unfold cx_F; lia) ltac:(unfold cx_F; lia)
      ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
    cbn [app] in HJ2. change (0 + 0) with 0 in HJ2.
    pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _).
    assert (KF : forall a, cx_F cx <= a < cx_F cx + 208 ->
      aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W3) (ms_mem ms) a)
      by (intros a Ha; apply G1; lia).
    assert (KF3 : forall a, cx_F cx + 0x18 <= a < cx_F cx + 208 ->
      aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W3) mem3 a)
      by (intros a Ha; rewrite KF by lia; apply AVw; lia).
    apply (SD6 cx i d f name nl ns nl2 close ly2 S2 W2 regs2 mem2 md2 HLF).
    split.
    { split; [exact HB|]. split.
      { apply (d5_com_call cx ly3 S3 W3 regs3 mem3 md3 (ms_mem ms) _ ly2 S2 W2 regs2 mem2 md2 HB HC KL HJc HJ2 Hbl2
          HG2 KF3).
        - d5_pres HP2 R2c 2.
        - d5_pres HP2 R3c 3.
        - d5_pres HP2 R4c 4.
        - d5_pres HP2 R25c 25. }
      split; [apply (d5_slots_kept cx W3 W2 mem3 mem2 d HSL); intros a Ha; apply KF3; lia|].
      split; [exact (eq_trans (HP2 22 ltac:(unfold acallee_saved; lia)) (eq_trans R22c R22))|].
      split; [exact (eq_trans (HP2 18 ltac:(unfold acallee_saved; lia)) (eq_trans R18c R18))|].
      split; [exact (eq_trans (HP2 8 ltac:(unfold acallee_saved; lia)) (eq_trans R8c R8))|].
      split; [exact HSC | exact Hit]. }
    split; [exact Hdc|]. split; [exact Hnl|]. split; [exact Hfe|].
    split; [eapply d5_val_kept; [|exact V28]; intros x Hx; apply KF3; change (Z.of_nat 8) with 8 in Hx; lia|].
    split; [eapply d5_val_kept; [|exact V8]; intros x Hx; apply KF; change (Z.of_nat 8) with 8 in Hx; lia|].
    split; [exact H10c|].
    split; [exact (eq_trans (HP2 20 ltac:(unfold acallee_saved; lia)) (eq_trans R20c R20))|].
    split; [exact (eq_trans (HP2 21 ltac:(unfold acallee_saved; lia)) (eq_trans R21c R21))|].
    split; [exact (eq_trans (HP2 24 ltac:(unfold acallee_saved; lia)) (eq_trans R24c R24))|].
    split; [exact (eq_trans (HP2 19 ltac:(unfold acallee_saved; lia)) (eq_trans R19c R19))|].
    exact (eq_trans (HP2 9 ltac:(unfold acallee_saved; lia)) (eq_trans R9c R9)).
  - (* v <> 0: the declaration does not match; back to EX_L at close + 1 *)
    rewrite branch_eq_U, U10, U_SLit in Hc. change (zcanon 0) with 0 in Hc. apply Z.eqb_neq in Hc.
    aj_run_to_tok EX_tbl_ok HS HJ SHOK EX_Bspan EX_L.
    { d5_awr Usp. }
    d5_avw W3 (cx_F cx + 8) (cx_F cx + 0x10) Usp AVw.
    assert (HM : MM.matches (cx_tb cx) (cx_ub cx) ns nl2 = false).
    { destruct (MM.matches (cx_tb cx) (cx_ub cx) ns nl2) eqn:Em; [|reflexivity].
      apply dm_matches in Em as (_ & Efn & _). exfalso. exact (Hc (proj2 Hveq Efn)). }
    destruct (dd_scan_skip cx i d f name nl ns nl2 close HSC Hit Hdc HM) as (HSC' & Hlt).
    d5_mk HS.
    eapply (HLF (S close) d (pred f) ly3 S3 W3 (ms_regs ms) (ms_mem ms) _ Hlt).
    split; [exact HB|]. split.
    { apply (dd_com_kept B cx ly3 S3 W3 regs3 mem3 md3 (ms_regs ms) (ms_mem ms) _ HB HC HJ).
      - intros a Ha H1 H2 H3. apply AVw; [exact Ha | lia].
      - d5_g HS. apply EE. reflexivity.
      - d5_g HS. apply EE. reflexivity.
      - d5_g HS. apply EE. reflexivity.
      - d5_g HS. apply EE. reflexivity. }
    split; [apply (dd_slots_kept B cx W3 mem3 (ms_mem ms) d HB HSL); intros a Ha; apply AVw; lia|].
    split.
    { split; [d5_g HS; rewrite E33; reflexivity|].
      split; [d5_g HS; rewrite (EE 22%nat 22%bv eq_refl); exact R22|].
      split; [d5_g HS; rewrite (EE 18%nat 18%bv eq_refl); exact R18|].
      d5_g HS; rewrite (EE 8%nat 8%bv eq_refl); exact R8. }
    split; [exact HSC'|].
    split.
    { d5_reg HS (19%bv : bv 5). unfold w64. apply fw_sv_U.
      rewrite (d5_U_s3 E (cx_t cx) (Z.of_nat close));
        [lia | rewrite E32; apply unsigned_lit_small; lia | rewrite E33; apply unsigned_lit_small; lia | lia | lia | lia]. }
    split; [d5_g HS; reflexivity|]. split; [d5_g HS; reflexivity|].
    d5_g HS. rewrite E34. reflexivity.
Qed.
End W.

Print Assumptions decl_D5_holds.
