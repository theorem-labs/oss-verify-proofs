(* check_refusal (fuzz_codec.c:283-291) at image A 0x844dc, 45 instructions, real frame 16, no call, against
   lib/A/Prog/CPgChkC.v's cdc_check_refusal_specX. a0 = q = &k, the 184-byte call record.
   0x844dc addi sp,-16; sd ra,8(sp): the walk's only store, into [sp - 16, sp).
   0x844e4-0x844ec load the shadow offset SB through the .got slot and its cell (the base regions of CPgWalk); the
   walk then drops those two regions and adds the record's region (atom 10 = q, chunks kind / b / rc at 0 / 28 / 72),
   which lies off [sp - 16, sp) by crd_ok, so it needs no fact about where the record is.
   Three 4-byte instrumented checks (q, q + 28, q + 72) are paid by the shadow entry mkSHE 10 0 184 (crd_ok).
   Branches: 0x84508 bne kind,11 / 0x84528 bne b,112: taken -> 0x84548, the return. 0x84544 beqz rc: taken -> the
   abort call at 0x84588, refuted by the premise ~ (kind = 11 /\ b = 0x70 /\ rc = 0); not taken -> the return. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgChkC CPgWalk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Definition A_CHECK_REFUSAL : Z := 0x844dc.
(* the record's three fields the function reads *)
Definition cr_rec : YP09.region := YP09.mkRegion (Some 10%nat) 0 184 0 0
[YP09.mkChunk 0 (CVal 4 (SOff 33 0)); YP09.mkChunk 28 (CVal 4 (SOff 34 0)); YP09.mkChunk 72 (CVal 4 (SOff 35 0))].
Definition cr_xs (kc : kcallZ) : list Z := [kz_kind kc mod 2 ^ 32; kz_b kc; kz_rc kc mod 2 ^ 32].
Definition cr_AF : list (nat * afact) :=
[(10%nat, mkAF 0 (2 ^ 47 - 185) 0); (33%nat, mkAF 0 (2 ^ 32 - 1) 0); (34%nat, mkAF 0 (2 ^ 32 - 1) 0);
 (35%nat, mkAF 0 (2 ^ 32 - 1) 0)].
Definition cr_SH : list shent := [mkSHE 10 0 184].

(* the return path: run to `ret`, then the leaf (memory clause from the save-slot zone, result True) *)
Ltac cr_ret HJ0 KE :=
  cw_run cw_awr_stk; cw_keep cw_kwr_stk;
  cw_leaf ltac:(idtac; cw_kept HJ0 KE ltac:(intros ? []) ltac:(intros ? Hz; left; cbv beta in Hz; lia)) ltac:(exact I).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Theorem check_refusal_A_holds : cdc_check_refusal_specX tfibsegs B MT A_CHECK_REFUSAL.
Proof using MTL TL LAWS ML.
unfold cdc_check_refusal_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q kc HE H10 Hkc Hwf Hcrd Hno.
pose proof HE as (HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwin & Hwhi & Hev & Hlive).
(* the entry journal stays as HJ0 (older); the runs take the newest journal, HJ *)
pose proof HJ as HJ1. rename HJ into HJ0. rename HJ1 into HJ.
unfold T_check_refusal in *.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs 16 HE ltac:(lia))
  as (Hceil & H47 & H46 & _ & Hpres).
pose proof Hwf as (Wk & _ & _ & _ & Wb & _ & _ & _ & Wrc & _).
pose proof Hcrd as (Hq0 & Hq63 & Hqv & Hqra & Hqhull & Hqam & Hqwin).
assert (Hq47 : q + 184 <= 2 ^ 47 - 1).
{ unfold amem_range in Hqam. rewrite C4, C5 in Hqam. destruct Hqam as [Hl | [_ Hh]]; lia. }
pose proof Hkc as (Vkind & _ & _ & _ & Vb & _ & _ & _ & _ & Vrc & _).
set (xs := cr_xs kc).
change (w64 q) with (Z_to_bv 64 q) in H10.
pose proof (Z.mod_pos_bound (kz_kind kc) (2 ^ 32) ltac:(lia)) as Mk.
pose proof (Z.mod_pos_bound (kz_rc kc) (2 ^ 32) ltac:(lia)) as Mr.
assert (X33 : ew (Ereg regs (cw_extra xs)) 33 = Z_to_bv 64 (kz_kind kc mod 2 ^ 32)) by exact (cw_ew_x regs xs 0).
assert (X34 : ew (Ereg regs (cw_extra xs)) 34 = Z_to_bv 64 (kz_b kc)) by exact (cw_ew_x regs xs 1).
assert (X35 : ew (Ereg regs (cw_extra xs)) 35 = Z_to_bv 64 (kz_rc kc mod 2 ^ 32)) by exact (cw_ew_x regs xs 2).
assert (HAF : atoms_ok (Ereg regs (cw_extra xs)) cr_AF).
{ unfold cr_AF. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), H10, X33, X34, X35.
  rewrite !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat split; lia. }
pose proof (cw_entry_base_af B TL LAWS A_CHECK_REFUSAL 16 xs cr_AF STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs 16
  HE ltac:(lia) ltac:(vm_compute; reflexivity) HAF) as HS.
remember (Ereg regs (cw_extra xs)) as E eqn:HEE.
assert (HAE : env_agree 32 (Ereg regs (cw_extra xs)) E) by (subst E; apply env_agree_refl).
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 q) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
assert (E33 : ew E 33 = Z_to_bv 64 (kz_kind kc mod 2 ^ 32)) by (subst E; exact (cw_ew_x regs xs 0)).
assert (E34 : ew E 34 = Z_to_bv 64 (kz_b kc)) by (subst E; exact (cw_ew_x regs xs 1)).
assert (E35 : ew E 35 = Z_to_bv 64 (kz_rc kc mod 2 ^ 32)) by (subst E; exact (cw_ew_x regs xs 2)).
clear HEE.
assert (SHOK : sh_ok tfibsegs CW_Bx cr_SH E (mrestrict (w_H W) memc)).
{ unfold cr_SH. apply Forall_cons; [|apply Forall_nil].
  exact (cw_shent_crd W memc (spZ regs) 16 E 10 q 184 Hcrd E10 E32 ltac:(lia)). }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
  aview tfibsegs (w_H W) memc a = aview tfibsegs (w_H W) memc a) by (intros; reflexivity).
unfold cfg_at. change (w64 A_CHECK_REFUSAL) with (Z_to_bv 64 A_CHECK_REFUSAL).
(* 0x844dc-0x844ec: the save of ra, the shadow offset through the .got slot and its cell *)
cw_run_to cw_awr_stk 0x844f0. cw_keep cw_kwr_stk.
(* the shadow offset is in a2 (SOff 32 0): drop the .got slot and the cell, add the record's region *)
assert (VK : forall o n v, 0 <= o -> o + Z.of_nat n <= 184 ->
  val_mem tfibsegs (mrestrict (w_H W) memc) (q + o) n v -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (q + o) n v).
{ intros o n v Ho Hn Hv. apply (cw_val_mem_kept (w_H W) (w_H W) memc (ms_mem ms)); [|exact Hv].
  intros x Hx. apply KE; [lia | cbv beta; unfold coff_win in Hqwin; lia]. }
lazymatch goal with HS : st_ok _ ?Ev ?ssv ?msv |- _ =>
  let l := eval vm_compute in (ss_mem ssv) in
  let r1 := eval vm_compute in (hd got_region l) in
  assert (HS1 : st_ok tfibsegs Ev (mkSS (ss_pc ssv) (ss_regs ssv) [r1] (ss_resv ssv) (ss_facts ssv)) msv)
  by (apply (st_ok_submem tfibsegs Ev ssv msv [r1] HS); [change (submem [r1] l); submem_to | reflexivity]);
  clear HS end.
lazymatch goal with HS1 : st_ok _ ?Ev ?ssv ?msv |- _ =>
  assert (Hrok : region_ok tfibsegs Ev (ms_mem msv) cr_rec);
  [ unfold region_ok, cr_rec; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
    rewrite E10, unsigned_lit_small by lia;
    split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
    [ apply (chunk_ok_val tfibsegs E _ q 0 4 (SOff 33 0) (kz_kind kc mod 2 ^ 32));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
      apply (VK 0 4%nat); [lia | cbn; lia|]; rewrite Z.add_0_r;
      exact (cw_val_mem_mod (mrestrict (w_H W) memc) q 4%nat (kz_kind kc) Vkind)
    | apply (chunk_ok_val tfibsegs E _ q 28 4 (SOff 34 0) (kz_b kc));
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
      apply (VK 28 4%nat); [lia | cbn; lia|]; exact Vb
    | apply (chunk_ok_val tfibsegs E _ q 72 4 (SOff 35 0) (kz_rc kc mod 2 ^ 32));
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
      apply (VK 72 4%nat); [lia | cbn; lia|];
      exact (cw_val_mem_mod (mrestrict (w_H W) memc) (q + 72) 4%nat (kz_rc kc) Vrc) ]
  | ];
  assert (Hdj : all_disjoint Ev cr_rec (ss_mem ssv));
  [ cbn [ss_mem all_disjoint]; unfold extent_disjoint, cr_rec;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite E10, B2, unsigned_lit_small by lia;
    unfold coff_win in Hqwin; split; [lia | exact I]
  | ];
  pose proof (ast_ok_add_region tfibsegs Ev ssv msv cr_rec HS1 eq_refl Hrok Hdj) as HS;
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS; clear HS1 Hrok Hdj end.
(* 0x844f0 ..: the check of kind's shadow (paid by mkSHE 10 0 184), lw kind, li 11, to bne kind,11 *)
cw_run cw_awr_stk. cw_keep cw_kwr_stk.
(* 0x84508 bne kind,11 *)
cw_branch Hb1.
all: rewrite branch_ne_U, (cw_U_sx32_eqb E 33 _ 11 E33 ltac:(lia) ltac:(lia)) in Hb1.
- (* taken: kind <> 11, to the return at 0x84548 *)
  cr_ret HJ0 KE.
- (* kind = 11: the check of b's shadow, lw b, li 112, to bne b,112 at 0x84528 *)
  apply negb_false_iff, Z.eqb_eq in Hb1.
  assert (Kk : kz_kind kc = 11) by (pose proof (Z.div_mod (kz_kind kc) (2 ^ 32) ltac:(lia)); lia).
  cw_run cw_awr_stk. cw_keep cw_kwr_stk.
  cw_branch Hb2.
  all: rewrite branch_ne_U, (cw_U_sx32_eqb E 34 _ 112 E34 ltac:(lia) ltac:(lia)) in Hb2.
  + (* taken: b <> 0x70 *)
    cr_ret HJ0 KE.
  + (* b = 0x70: the check of rc's shadow, lw rc, to beqz rc at 0x84544 *)
    apply negb_false_iff, Z.eqb_eq in Hb2.
    cw_run cw_awr_stk. cw_keep cw_kwr_stk.
    cw_branch Hb3.
    all: rewrite branch_eq_U, (cw_U_sx32_eqb E 35 _ 0 E35 ltac:(lia) ltac:(lia)) in Hb3.
    * (* taken: rc = 0, the abort call at 0x84588: refuted by the premise *)
      exfalso. apply Z.eqb_eq in Hb3.
      assert (Kr : kz_rc kc = 0) by (pose proof (Z.div_mod (kz_rc kc) (2 ^ 32) ltac:(lia)); lia).
      apply Hno. split; [exact Kk|]. split; [exact Hb2 | exact Kr].
    * (* rc <> 0: the return *)
      cr_ret HJ0 KE.
Qed.
End d.
End b.
