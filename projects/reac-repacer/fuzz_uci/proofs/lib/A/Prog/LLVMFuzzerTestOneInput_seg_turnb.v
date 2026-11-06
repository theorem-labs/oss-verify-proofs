(* LLVMFuzzerTestOneInput_seg_turnb: u_turn_b_ok : u_turn_b_stmt (lib/A/Prog/LLVMFuzzerTestOneInput_segs.v), in the
   form of proofs/libreac/fuzz_decode's LLVMFuzzerTestOneInput_seg_crt1.v c1_B (a run of the Pa engine to a call, the
   callee contract at the call, the run from its return address).

   Three runs of the Pa engine from three seats, each with the registers as atoms (Ereg regs extra):
   - tb_A, +0x130 .. +0x144: one read-only region on sp holding the four bytes of cur (extra atom 32 = cu, from
     u_st_pre's rd32); `lw s4, 8(sp)` gives the sign extension of cu, s5 = p + off, a0 / a1 / a2; the run stops at the
     call of check_no_overread, which tb_call_cno (LLVMFuzzerTestOneInput_seg_turnb_lib.v) takes to tb_st at +0x148;
   - tb_B, +0x148 .. +0x154: no region; the run stops at the call of check_value, which tb_call_cv takes to tb_st at
     +0x158 with a0 the value;
   - tb_C, +0x158 .. +0x16c: one writable region (extra atom 32 = sp1 + 0x1c + 4 i, with the alias fact that names
     s9 + (s7 << 2) by it), so `sw a0, 0(a1)` stores the value there; s7 = i + 1, s8 = len + off; the run stops at
     `bne s7, s10`. Taken (i + 1 <> 5) it runs to +0xa8 and tb_close gives u_st_oh (i + 1); not taken (i = 4) it runs
     over `j` to +0x180 and tb_close gives u_st_exit. *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0s YC5d.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YM05 YE00 YE01 YO09 YImgTop.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YI16.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import AB1v ACfn.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require AE2k.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal
  UciPSyms UciPList UciPAddr UciPPa UciPPaLib UciPImg UciCg.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import LLVMFuzzerTestOneInput_cg
  LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_seg_lib LLVMFuzzerTestOneInput_seg_turnb_lib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ------------------------------------------------------------------ *)
(* 1. The three seats                                                  *)
(* ------------------------------------------------------------------ *)

(* +0x130: the 4-byte cur buffer at sp + 8 (atom 2 = sp1), read only, holding atom 32 = cu. *)
Definition tb_cur_region : YP09.region := YP09.mkRegion (Some 2%nat) 8 12 0 0 [YP09.mkChunk 8 (CVal 4 (SOff 32 0))].
Definition tb_ss_a : sstate := mkSS U_PRE sr_atoms [tb_cur_region] None (mkFacts [] [] []).
(* +0x148: no region. *)
Definition tb_ss_b : sstate := mkSS 0x148 sr_atoms [] None (mkFacts [] [] []).
(* +0x158: the result word at atom 32 = sp1 + 0x1c + 4 i, writable, and s9 + (s7 << 2) named by atom 32. *)
Definition tb_res_region : YP09.region := YP09.mkRegion (Some 32%nat) 0 4 0 4 [].
Definition tb_alias : sv * sv := (SAlu ALU_ADD (SOff 25 0) (SAlu ALU_SLL (SOff 23 0) (SLit 2)), SOff 32 0).
Definition tb_ss_c : sstate :=
  mkSS 0x158 sr_atoms [tb_res_region] None (mkFacts [(32%nat, mkAF (2 ^ 46) (2 ^ 47) 2)] [] [tb_alias]).

Section seat. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation SEGS := (@pa_segs _ uci_listing PI_uci).
Local Abbreviation VAL := (@pa_val _ uci_listing PI_uci).
Local Abbreviation BASE := (@pa_val _ uci_listing PI_uci A_TEXT).

Lemma tb_seat_a : forall (W : world SEGS) (regs : bvmap 5 word) mem sp1 cu,
  spZ regs = sp1 -> 0 <= sp1 -> sp1 + 12 <= 2 ^ 64 -> 0 <= cu < 2 ^ 32 ->
  rd32 (aview SEGS (w_H W) mem) (sp1 + 8) cu ->
  st_ok_pi SEGS VAL (Eimg (PI := PI_uci) (Ereg regs [Z_to_bv 64 cu])) tb_ss_a
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + U_PRE)) mem (seg_rom SEGS))).
Proof.
intros W regs mem sp1 cu Hsp H0 H1 Hcu Hrd.
rewrite restrict_mkst_fx. unfold tb_ss_a.
set (E := Eimg (PI := PI_uci) (Ereg regs [Z_to_bv 64 cu])).
assert (E2 : bv_unsigned (ew E 2) = sp1)
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact Hsp).
assert (E32 : ew E 32 = Z_to_bv 64 cu)
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok, tb_cur_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ sp1 8 4 (SOff 32 0) cu);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
  apply val_mem_of_rd32. exact Hrd.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- exact (conj I (conj I I)).
Qed.

Lemma tb_seat_b : forall (W : world SEGS) (regs : bvmap 5 word) mem,
  st_ok_pi SEGS VAL (Eimg (PI := PI_uci) (Ereg regs [])) tb_ss_b
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x148)) mem (seg_rom SEGS))).
Proof.
intros W regs mem. rewrite restrict_mkst_fx. unfold tb_ss_b. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- exact I.
- exact (conj I (conj I I)).
Qed.

Lemma tb_seat_c : forall (W : world SEGS) (regs : bvmap 5 word) mem sp1 i,
  YK11.getr regs 25 = w64 (sp1 + 0x1c) -> YK11.getr regs 23 = w64 i -> 0 <= i < 5 ->
  2 ^ 46 <= sp1 -> sp1 + 0x1c + 4 * i + 4 <= 2 ^ 47 -> (sp1 + 0x1c + 4 * i) mod 4 = 0 ->
  (forall a, sp1 + 0x1c + 4 * i <= a < sp1 + 0x1c + 4 * i + 4 -> apresent (w_H W) mem a) ->
  st_ok_pi SEGS VAL (Eimg (PI := PI_uci) (Ereg regs [Z_to_bv 64 (sp1 + 0x1c + 4 * i)])) tb_ss_c
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x158)) mem (seg_rom SEGS))).
Proof.
intros W regs mem sp1 i R25 R23 Hi Hlo Hhi H4 Hpres.
rewrite restrict_mkst_fx. unfold tb_ss_c.
set (R := sp1 + 0x1c + 4 * i) in *.
set (E := Eimg (PI := PI_uci) (Ereg regs [Z_to_bv 64 R])).
assert (E25 : ew E 25 = Z_to_bv 64 (sp1 + 0x1c))
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact R25).
assert (E23 : ew E 23 = Z_to_bv 64 i)
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact R23).
assert (E32 : ew E 32 = Z_to_bv 64 R)
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (U32 : bv_unsigned (ew E 32) = R) by (rewrite E32; apply unsigned_lit_small; lia).
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok, tb_res_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U32.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- cbn [facts_ok f_atoms f_conds f_alias atoms_ok conds_ok alias_ok tb_alias].
  split; [|split; [exact I|]].
  + split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U32. change (2 ^ 2) with 4. lia.
  + split; [|exact I]. rewrite !denot_lit_U. f_equal.
    rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
    rewrite U_SLit, (U_atom E 23 i E23), (U_atom E 25 (sp1 + 0x1c) E25), (U_atom E 32 R E32) by lia.
    change (Z.land (zcanon 2) 63) with 2. rewrite Z.shiftl_mul_pow2 by lia.
    rewrite (zcanon_id (i * 2 ^ 2)) by (unfold M64; lia).
    rewrite zcanon_id by (unfold M64, R in *; lia). unfold R in *. lia.
Qed.

(* What the last run of tb_C leaves: the stored word, the kept registers, s7 = i + 1 and s8 = len + off. *)
Lemma tb_fin : forall (W : world (@pa_segs _ uci_listing PI_uci)) E0 ss ms (regs : bvmap 5 word) X R v i len off,
  st_ok_pi (@pa_segs _ uci_listing PI_uci) (@pa_val _ uci_listing PI_uci) E0 ss (restrict (w_H W) ms) ->
  env_agree 32 (Ereg regs X) E0 -> bv_unsigned (ew E0 32) = R ->
  nth_error (ss_mem ss) 0 = Some (YP09.mkRegion (Some 32%nat) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 10 0))]) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0))
    [2; 3; 4; 8; 9; 18; 22; 25; 26; 27]%bv = true ->
  sr_get (ss_regs ss) 23 = SOff 23 1 -> sr_get (ss_regs ss) 24 = SAlu ALU_ADD (SOff 19 0) (SOff 24 0) ->
  YK11.getr regs 10 = w64 v -> YK11.getr regs 23 = w64 i -> YK11.getr regs 19 = w64 len ->
  YK11.getr regs 24 = w64 off -> 0 <= i < 5 -> 0 <= len < 2 ^ 63 -> 0 <= off < 2 ^ 63 ->
  rd32 (aview (@pa_segs _ uci_listing PI_uci) (w_H W) (ms_mem ms)) R v /\
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 22; 25; 26; 27]%bv -> YK11.getr (ms_regs ms) r = YK11.getr regs r) /\
  YK11.getr (ms_regs ms) 23 = w64 (i + 1) /\ YK11.getr (ms_regs ms) 24 = w64 (len + off).
Proof.
intros W E0 ss ms regs X R v i len off HS HAE U32 Hnth Hkeep S23 S24 R10 R23 R19 R24 Hi Hlen Hoff.
assert (EL : forall (nn : nat) (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E0 nn = YK11.getr regs r).
{ intros nn r Hnn. destruct HAE as [HA _]. pose proof (u5_range r) as Hr. rewrite HA by lia.
  apply ew_Ereg_nat. exact Hnn. }
refine (conj _ (conj _ (conj _ _))).
- pose proof (st_ok_pi_region_nth E0 ss (restrict (w_H W) ms) 0 _ HS Hnth) as (_ & _ & _ & Hcs).
  cbn [YP09.r_base YP09.r_chunks base_val ms_mem restrict] in Hcs. rewrite U32 in Hcs.
  apply Forall_inv in Hcs.
  pose proof (tb_store_val _ E0 _ R 0 (SOff 10 0) v Hcs
    ltac:(rewrite (tb_soff_denot E0 10 _ (EL 10%nat 10%bv eq_refl)); exact R10)) as Hval.
  rewrite Z.add_0_r in Hval. exact (tb_rd32_of_val _ _ _ _ _ Hval).
- intros r Hr. exact (regs_kept_of_st_ok_pi E0 ss (restrict (w_H W) ms) regs X _ HS HAE Hkeep r Hr).
- pose proof (st_ok_pi_restrict_reg (w_H W) E0 ss ms 23 HS) as H. rewrite S23 in H. rewrite H.
  rewrite denot_lit_U, (U_atom_off E0 23 i 1) by (first [rewrite (EL 23%nat 23%bv eq_refl); exact R23 | lia]).
  reflexivity.
- pose proof (st_ok_pi_restrict_reg (w_H W) E0 ss ms 24 HS) as H. rewrite S24 in H. rewrite H.
  apply tb_add_denot;
    [rewrite (EL 19%nat 19%bv eq_refl); exact R19 | rewrite (EL 24%nat 24%bv eq_refl); exact R24 | lia | lia].
Qed.
End seat.

(* ------------------------------------------------------------------ *)
(* 2. The runs                                                         *)
(* ------------------------------------------------------------------ *)

(* A register's symbolic value at a state (st_ok_pi, or st_ok at a call). *)
Ltac tb_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?sg ?vl ?Ex ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H Ex ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
  | st_ok ?sg ?Ex ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg sg H Ex ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
  end.
(* The write rights of the runs: read-only regions, or the result word (atom 32) at d from the entry sp. *)
Ltac tb_awr U32 d :=
  lazymatch goal with |- awr_ok ?Ey ?rsx ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rsx in change (awr_ok Ey rs' stk sp0q fp b0 bc lyq ownq) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 32%nat d);
    [reflexivity | rewrite U32; lia | cbn; unfold LLVMF_STK; lia | cbn; lia |] ].
Ltac tb_awr_ro :=
  lazymatch goal with |- awr_ok ?Ey ?rsx ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rsx in change (awr_ok Ey rs' stk sp0q fp b0 bc lyq ownq) end;
  repeat first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|] ].
(* The model after a run, named. *)
Ltac tb_md md2 :=
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md2 := mdx) in *; clearbody md2 end.

Section sg. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.

(* +0x130 .. +0x144 and check_no_overread. *)
Lemma tb_A : forall cx i (W : world segs) c,
  u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx -> 0 <= i < 5 -> u_st_pre B MT XL cx i W c ->
  SRr segs W c (tb_st B MT XL cx i 0x148 (i * U_EV_TURN + PN.CNO_EV) (fun l => PN.uci_cno_cost MT l)
    (fun _ _ _ _ => True)).
Proof.
intros cx i W c HP HB Hi HPRE.
destruct HPRE as (ly' & S' & regs & mem & md & off & len & mm & cu & vs & -> & HC & HM & R8 & R9 & R18 & Hmm & R19
  & R22 & R23 & R24 & R25 & R26 & Hoff & Hlen & Hol & Hcu & Hrd & HR).
pose proof (up_laws _ _ _ _ _ HP) as LAWS.
pose proof HC as (HJ & Hfrs & Hsp & Hgp & Htp & H27 & Hsv & Hperm).
destruct (tb_J_facts B cx ly' S' W mem md _ HJ) as (H16 & Hceil & H47 & Hpres).
destruct (tb_base B MT XL RLO RHI cx HP HB) as (Hn & Hp & _).
pose proof alloc_ceiling_val as Hce.
pose proof (@tb_seat_a (u_fx cx) rc W regs mem (u_sp1 cx) cu Hsp
  ltac:(unfold u_sp1, U_FRAME, LLVMF_STK in *; lia) ltac:(unfold u_sp1, U_FRAME in *; lia) Hcu Hrd) as HS.
set (E0 := Eimg (PI := PI_uci) (Ereg regs [Z_to_bv 64 cu])) in HS.
assert (HEI : img_env (@pa_val _ uci_listing PI_uci) A_LIM E0) by apply Eimg_env.
assert (SHOK : sh_ok (@pa_segs _ uci_listing PI_uci) (SOff 22 0) [] E0 (mrestrict (w_H W) mem)) by constructor.
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 cu]) E0)
  by (split; [intros nn Hnn; unfold E0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EL : forall (nn : nat) (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E0 nn = YK11.getr regs r)
  by (intros nn r Hnn; unfold E0; rewrite Eimg_low by (pose proof (u5_range r); unfold A_TEXT; lia);
      apply ew_Ereg_nat; exact Hnn).
assert (E32 : ew E0 32 = Z_to_bv 64 cu)
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
pose proof (paj_run (fx := u_fx cx) (SK := AE2k.tfib_sink_head) (PI := PI_uci) B LAWS) as RUN.
unfold u_cfg.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr (@pa_segs _ uci_listing PI_uci) Wx
    (mkCfg (@YK11.mkst (u_fx cx) regs (Z_to_bv 64 (@pa_val _ uci_listing PI_uci A_TEXT + U_PRE)) mem
      (seg_rom (@pa_segs _ uci_listing PI_uci))) md) Q) end.
paj_run_tok RUN HS HJ SHOK Bspan; [tb_awr_ro|].
tb_md mdA.
apply frame_of_read_only in HF; [|vm_compute; reflexivity]. rename HF into Hm.
clear HFr HG.
lazymatch type of HS with st_ok _ _ ?ss _ =>
  pose proof (regs_kept_of_st_ok (@pa_segs _ uci_listing PI_uci) E0 ss (restrict (w_H W) ms) regs [Z_to_bv 64 cu]
    [2; 3; 4; 8; 9; 18; 19; 22; 23; 24; 25; 26; 27]%bv HS HAE ltac:(vm_compute; reflexivity)) as KA end.
cbn [ms_regs restrict] in KA.
tb_reg HS (1%bv : bv 5) R1'. tb_reg HS (10%bv : bv 5) R10'. tb_reg HS (11%bv : bv 5) R11'.
tb_reg HS (12%bv : bv 5) R12'. tb_reg HS (20%bv : bv 5) R20'. tb_reg HS (21%bv : bv 5) R21'.
cbn [ms_regs restrict] in R1', R10', R11', R12', R20', R21'.
destruct (tb_sext_denot E0 32 cu E32 Hcu) as (D20 & D12).
assert (DA : sv_denot E0 (SAlu ALU_ADD (SOff 9 0) (SOff 24 0)) = w64 (u_p cx + off)).
{ apply tb_add_denot; [rewrite (EL 9%nat 9%bv eq_refl); exact R9 | rewrite (EL 24%nat 24%bv eq_refl); exact R24
  | lia | lia]. }
assert (R1 : YK11.getr (ms_regs ms) 1 = w64 (UCI_A_LLVMF + 0x148)) by (rewrite R1'; exact (codeptr_val E0 328 HEI)).
rewrite DA in R10', R21'. rewrite D12 in R12'. rewrite D20 in R20'.
rewrite (tb_soff_denot E0 19 _ (EL 19%nat 19%bv eq_refl)), R19 in R11'.
pmkst HS. rewrite Hm in HJ |- *.
apply (tb_call_cno B MT XL RLO RHI cx i W (ms_regs ms) mem _ ly' S' mm off len (tb_cur cu) vs HP HB Hi).
- apply (tb_core_same B cx ly' S' W regs (ms_regs ms) mem md _ _ HC HJ).
  intros r Hr. apply KA. cbn [In] in Hr |- *. intuition.
- exact HM.
- exact R1.
- refine (conj _ (conj _ (conj _ (conj Hmm (conj _ (conj R20' (conj R21' (conj _ (conj _ (conj _ (conj _ _)))))))))));
    rewrite KA by tb_in; assumption.
- exact R10'.
- exact R11'.
- exact R12'.
- exact Hoff.
- exact Hlen.
- exact Hol.
- exact (tb_cur_range cu Hcu).
- exact HR.
Qed.

(* +0x148 .. +0x154 and check_value. *)
Lemma tb_B : forall cx i (W : world segs) c,
  u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx -> 0 <= i < 5 ->
  tb_st B MT XL cx i 0x148 (i * U_EV_TURN + PN.CNO_EV) (fun l => PN.uci_cno_cost MT l) (fun _ _ _ _ => True) W c ->
  SRr segs W c (tb_st B MT XL cx i 0x158 (i * U_EV_TURN + PN.CNO_EV + PV.CV_EV)
    (fun l => PN.uci_cno_cost MT l + PV.uci_cv_cost MT l)
    (fun regs off len cur => YK11.getr regs 10 = w64 (rp_uci_int_m (PRc.zbytes (tb_slice (u_pl cx) off len)) cur))).
Proof.
intros cx i W c HP HB Hi HST.
destruct HST as (ly' & S' & regs & mem & md & mm & off & len & cur & vs & -> & HC & Hle & Hmo & HRg & Ho & Hl & Hol
  & Hcur & HR & _).
cbv beta in Hle, Hmo.
pose proof (up_laws _ _ _ _ _ HP) as LAWS.
pose proof HC as (HJ & _).
pose proof HRg as (R8 & R9 & R18 & Hmm & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26).
pose proof (@tb_seat_b (u_fx cx) rc W regs mem) as HS.
set (E0 := Eimg (PI := PI_uci) (Ereg regs [])) in HS.
assert (HEI : img_env (@pa_val _ uci_listing PI_uci) A_LIM E0) by apply Eimg_env.
assert (SHOK : sh_ok (@pa_segs _ uci_listing PI_uci) (SOff 22 0) [] E0 (mrestrict (w_H W) mem)) by constructor.
assert (HAE : env_agree 32 (Ereg regs []) E0)
  by (split; [intros nn Hnn; unfold E0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EL : forall (nn : nat) (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E0 nn = YK11.getr regs r)
  by (intros nn r Hnn; unfold E0; rewrite Eimg_low by (pose proof (u5_range r); unfold A_TEXT; lia);
      apply ew_Ereg_nat; exact Hnn).
pose proof (paj_run (fx := u_fx cx) (SK := AE2k.tfib_sink_head) (PI := PI_uci) B LAWS) as RUN.
unfold u_cfg.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr (@pa_segs _ uci_listing PI_uci) Wx
    (mkCfg (@YK11.mkst (u_fx cx) regs (Z_to_bv 64 (@pa_val _ uci_listing PI_uci A_TEXT + 0x148)) mem
      (seg_rom (@pa_segs _ uci_listing PI_uci))) md) Q) end.
paj_run_tok RUN HS HJ SHOK Bspan; [tb_awr_ro|].
tb_md mdA.
apply frame_of_read_only in HF; [|vm_compute; reflexivity]. rename HF into Hm.
clear HFr HG.
lazymatch type of HS with st_ok _ _ ?ss _ =>
  pose proof (regs_kept_of_st_ok (@pa_segs _ uci_listing PI_uci) E0 ss (restrict (w_H W) ms) regs []
    [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS HAE ltac:(vm_compute; reflexivity)) as KA end.
cbn [ms_regs restrict] in KA.
tb_reg HS (1%bv : bv 5) R1'. tb_reg HS (10%bv : bv 5) R10'. tb_reg HS (11%bv : bv 5) R11'.
tb_reg HS (12%bv : bv 5) R12'.
cbn [ms_regs restrict] in R1', R10', R11', R12'.
assert (R1 : YK11.getr (ms_regs ms) 1 = w64 (UCI_A_LLVMF + 0x158)) by (rewrite R1'; exact (codeptr_val E0 344 HEI)).
rewrite (tb_soff_denot E0 21 _ (EL 21%nat 21%bv eq_refl)), R21 in R10'.
rewrite (tb_soff_denot E0 19 _ (EL 19%nat 19%bv eq_refl)), R19 in R11'.
rewrite (tb_soff_denot E0 20 _ (EL 20%nat 20%bv eq_refl)), R20 in R12'.
pmkst HS. rewrite Hm in HJ |- *.
apply (tb_call_cv B MT XL RLO RHI cx i W (ms_regs ms) mem _ ly' S' mm off len cur vs HP HB Hi).
- apply (tb_core_same B cx ly' S' W regs (ms_regs ms) mem md _ _ HC HJ).
  intros r Hr. apply KA. cbn [In] in Hr |- *. intuition.
- exact Hle.
- exact Hmo.
- exact R1.
- apply (tb_regs_kept cx regs (ms_regs ms) i mm off len cur HRg).
  intros r Hr. apply KA. cbn [In] in Hr |- *. intuition.
- exact R10'.
- exact R11'.
- exact R12'.
- exact Ho.
- exact Hl.
- exact Hol.
- exact Hcur.
- exact HR.
Qed.

(* +0x158 .. +0x16c: the store of the value, s7 + 1, s8 + len, and `bne s7, s10`. *)
Lemma tb_C : forall cx i (W : world segs) c,
  u_prem B MT XL RLO RHI -> u_base B MT XL RLO RHI cx -> 0 <= i < 5 ->
  tb_st B MT XL cx i 0x158 (i * U_EV_TURN + PN.CNO_EV + PV.CV_EV) (fun l => PN.uci_cno_cost MT l + PV.uci_cv_cost MT l)
    (fun regs off len cur => YK11.getr regs 10 = w64 (rp_uci_int_m (PRc.zbytes (tb_slice (u_pl cx) off len)) cur))
    W c ->
  SRr segs W c (fun W2 c2 => (i < 4 /\ u_st_oh B MT XL cx (i + 1) W2 c2) \/ (i = 4 /\ u_st_exit B MT XL cx W2 c2)).
Proof.
intros cx i W c HP HB Hi HST.
destruct HST as (ly' & S' & regs & mem & md & mm & off & len & cur & vs & -> & HC & Hle & Hmo & HRg & Ho & Hl & Hol
  & Hcur & HR & R10).
cbv beta in Hle, Hmo.
set (v := rp_uci_int_m (PRc.zbytes (tb_slice (u_pl cx) off len)) cur) in R10.
assert (Hv : INT_MIN <= v <= INT_MAX) by (apply rp_uci_int_range; exact Hcur).
pose proof (up_laws _ _ _ _ _ HP) as LAWS.
pose proof HC as (HJ & Hfrs & Hsp & Hgp & Htp & H27 & Hsv & Hperm).
destruct (tb_J_facts B cx ly' S' W mem md _ HJ) as (H16 & Hceil & H47 & Hpres).
destruct (tb_base B MT XL RLO RHI cx HP HB) as (Hn & Hp & _).
pose proof alloc_ceiling_val as Hce.
pose proof HRg as (R8 & R9 & R18 & Hmm & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26).
pose proof (@tb_seat_c (u_fx cx) rc W regs mem (u_sp1 cx) i R25 R23 Hi
  ltac:(unfold u_sp1, U_FRAME, LLVMF_STK in *; lia) ltac:(unfold u_sp1, U_FRAME in *; lia)
  ltac:(unfold u_sp1, U_FRAME in *; lia)
  ltac:(intros a Ha; apply Hpres; unfold u_sp1, U_FRAME, LLVMF_STK in *; lia)) as HS.
set (R := u_sp1 cx + 0x1c + 4 * i) in *.
set (E0 := Eimg (PI := PI_uci) (Ereg regs [Z_to_bv 64 R])) in HS.
assert (HEI : img_env (@pa_val _ uci_listing PI_uci) A_LIM E0) by apply Eimg_env.
assert (SHOK : sh_ok (@pa_segs _ uci_listing PI_uci) (SOff 22 0) [] E0 (mrestrict (w_H W) mem)) by constructor.
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 R]) E0)
  by (split; [intros nn Hnn; unfold E0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EL : forall (nn : nat) (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E0 nn = YK11.getr regs r)
  by (intros nn r Hnn; unfold E0; rewrite Eimg_low by (pose proof (u5_range r); unfold A_TEXT; lia);
      apply ew_Ereg_nat; exact Hnn).
assert (U32 : bv_unsigned (ew E0 32) = R)
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs _ 0);
      apply unsigned_lit_small; unfold R, u_sp1, U_FRAME, LLVMF_STK in *; lia).
assert (E23 : ew E0 23 = Z_to_bv 64 i) by (rewrite (EL 23%nat 23%bv eq_refl); exact R23).
assert (E26 : ew E0 26 = Z_to_bv 64 5) by (rewrite (EL 26%nat 26%bv eq_refl); exact R26).
assert (HRd : R - u_sp0 cx = 4 * i - 116) by (unfold R, u_sp1, U_FRAME; lia).
pose proof (paj_run (fx := u_fx cx) (SK := AE2k.tfib_sink_head) (PI := PI_uci) B LAWS) as RUN.
pose proof (paj_run_to (fx := u_fx cx) (SK := AE2k.tfib_sink_head) (PI := PI_uci) B LAWS) as RUNTO.
pose proof (@paj_branch (u_fx cx) rc uci_listing PI_uci) as BR.
unfold u_cfg.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr (@pa_segs _ uci_listing PI_uci) Wx
    (mkCfg (@YK11.mkst (u_fx cx) regs (Z_to_bv 64 (@pa_val _ uci_listing PI_uci A_TEXT + 0x158)) mem
      (seg_rom (@pa_segs _ uci_listing PI_uci))) md) Q) end.
paj_run_tok RUN HS HJ SHOK Bspan; [tb_awr U32 (R - u_sp0 cx)|].
tb_md mdA.
assert (HM1 : forall x, ~ (R <= bv_unsigned x < R + 4) -> ms_mem ms x = mem x)
  by exact (tb_frame32 E0 _ _ _ R HF ltac:(vm_compute; reflexivity) U32).
clear HF HFr HG.
rename ms into ms1.
assert (KVof : forall m2 : word -> option byte, (forall x, ~ (R <= bv_unsigned x < R + 4) -> m2 x = ms_mem ms1 x) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (R <= a < R + 4) -> aview segs (w_H W) m2 a = aview segs (w_H W) mem a).
{ intros m2 Hm2 a Ha Hna. apply aview_eq_of. unfold mrestrict.
  assert (Hx : ~ (R <= bv_unsigned (Z_to_bv 64 a) < R + 4)) by (rewrite unsigned_lit_small by lia; exact Hna).
  rewrite (Hm2 _ Hx), (HM1 _ Hx). reflexivity. }
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* i + 1 <> 5: the head of turn i + 1 *)
  assert (Hi4 : i < 4).
  { rewrite branch_ne_U, (U_atom_off E0 23 i 1 E23), (U_atom E0 26 5 E26) in Hc by lia.
    apply negb_true_iff, Z.eqb_neq in Hc. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 168; [tb_awr U32 (R - u_sp0 cx)|].
  tb_md mdB.
  assert (HM2 : forall x, ~ (R <= bv_unsigned x < R + 4) -> ms_mem ms x = ms_mem ms1 x)
    by exact (tb_frame32 E0 _ _ _ R HF ltac:(vm_compute; reflexivity) U32).
  clear HF HFr HG.
  destruct (tb_fin W E0 _ ms regs [Z_to_bv 64 R] R v i len off HS HAE U32
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) R10 R23 R19 R24 Hi ltac:(unfold PR.REPLY_MAX in *; lia) ltac:(lia))
    as (Hrd & KA & R23' & R24').
  pmkst HS.
  apply SRr_ret. left. split; [exact Hi4|].
  destruct (tb_close B MT XL RLO RHI cx i W regs mem md ly' S' mm off len cur vs (ms_regs ms) (ms_mem ms) mdB v
    HP HB Hi HC Hle Hmo HRg Ho Hl Hol HR HJ (KVof _ HM2) Hrd Hv KA R23' R24')
    as (HC2 & HM2' & HR2 & S8 & S9 & S18 & Hmm' & S22 & S23 & S24 & S25 & S26 & Hoff2).
  exists ly', S', (ms_regs ms), (ms_mem ms), mdB, (len + off), mm, (vs ++ [v]).
  exact (conj eq_refl (conj HC2 (conj HM2' (conj S8 (conj S9 (conj S18 (conj Hmm' (conj S22 (conj S23 (conj S24
    (conj S25 (conj S26 (conj Hoff2 HR2))))))))))))).
- (* i + 1 = 5: over `j` to +0x180 *)
  assert (Hi4 : i = 4).
  { rewrite branch_ne_U, (U_atom_off E0 23 i 1 E23), (U_atom E0 26 5 E26) in Hc by lia.
    apply negb_false_iff, Z.eqb_eq in Hc. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 384; [tb_awr U32 (R - u_sp0 cx)|].
  tb_md mdB.
  assert (HM2 : forall x, ~ (R <= bv_unsigned x < R + 4) -> ms_mem ms x = ms_mem ms1 x)
    by exact (tb_frame32 E0 _ _ _ R HF ltac:(vm_compute; reflexivity) U32).
  clear HF HFr HG.
  destruct (tb_fin W E0 _ ms regs [Z_to_bv 64 R] R v i len off HS HAE U32
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) R10 R23 R19 R24 Hi ltac:(unfold PR.REPLY_MAX in *; lia) ltac:(lia))
    as (Hrd & KA & R23' & R24').
  pmkst HS.
  apply SRr_ret. right. split; [exact Hi4|].
  destruct (tb_close B MT XL RLO RHI cx i W regs mem md ly' S' mm off len cur vs (ms_regs ms) (ms_mem ms) mdB v
    HP HB Hi HC Hle Hmo HRg Ho Hl Hol HR HJ (KVof _ HM2) Hrd Hv KA R23' R24')
    as (HC2 & HM2' & HR2 & S8 & S9 & S18 & Hmm' & S22 & S23 & S24 & S25 & S26 & Hoff2).
  subst i.
  exists ly', S', (ms_regs ms), (ms_mem ms), mdB, mm, (vs ++ [v]).
  exact (conj eq_refl (conj HC2 (conj HM2' (conj S18 (conj Hmm' HR2))))).
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The segment                                                      *)
(* ------------------------------------------------------------------ *)

Theorem u_turn_b_ok : u_turn_b_stmt B MT XL RLO RHI.
Proof.
intros HP cx i W c Hi HB HPRE.
eapply SRr_bind; [exact (tb_A cx i W c HP HB Hi HPRE)|].
intros W1 c1 _ H1.
eapply SRr_bind; [exact (tb_B cx i W1 c1 HP HB Hi H1)|].
intros W2 c2 _ H2.
exact (tb_C cx i W2 c2 HP HB Hi H2).
Qed.
End sg.
