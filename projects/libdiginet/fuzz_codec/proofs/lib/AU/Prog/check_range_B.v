(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the run / keep / branch / leaf tactics, kept_run and same_io_wvb are the text of
   projects/reac-pw/fuzz_qdisc/proofs/lib/A/QPgSlots.v:123-188 (made there from proofs/libreac/fuzz_knock/lib/A/APgStep.v,
   origin/ossv/recipes 6ebe35ba632), the stack-slot write tactics that of QPgCheck.v:52-69, the entry regions those of
   QPgRt.v:61-65 / 193-243, the shadow entry that of proofs/libreac/fuzz_identity/lib/A/Prog/sb_dec.v:354-370
   (origin/ossv/recipes 4b6f0df50aa7), cw_U_sx32_eqb that of proofs/libreac/fuzz_knock/lib/A/APgStep.v:54-68
   (U_sx32_eqb, origin/ossv/recipes 4b6f0df50aa7), cw_join_win that of proofs/reac-pw/fuzz_qdisc/lib/A/QPgLoop0.v:169-196
   (ra_join_win, a working branch b0f706c04a19), cw_bcmp_at that of lib/Reusable/YCbq.v:2262-2310 (aj_bcmp_at) with
   the wrapper's same_but_materialized kept in its post, cw_st_ok_at that of lib/Reusable/YI04.v:342-356 (entry_st_ok_full)
   with the env apart from the registers, renamed with the prefix cw_ and moved to libdiginet/fuzz_codec's ASan
   build (image A); the leaf ends in lib/A/Prog/CPgBase.v's cdc_post, whose memory clause is CodecCJ's tcj_kept. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgWalk.v, with its module paths and module names changed; 221 of its 262 lines of code are new or changed and 592 lines of the source are left out. *)
(* check_range (fuzz_codec.c:293-314) at image B 0x84c84, 47 instructions, real frame 32, the bcmp wrapper at 0x84cd8,
   against lib/AU/Prog/CPgChkU.v's cdcU_check_range_specX. a0 = q = &k, the 184-byte call record.
   The image-A walk (lib/A/Prog/check_range_A.v) at image B's addresses, with one more step: image B checks that q is
   8-aligned (0x84c9c andi a0,a0,7; 0x84ca0 bnez -> the UBSan trap at 0x84d1c); the contract's q mod 8 = 0 is atom 10's
   alignment fact (al2 = 3), so the engine takes the not-taken side.
   0x84c84-0x84c98 save ra, s0, s1, s2 into [sp - 32, sp) and keep q in s0; 0x84ca4-0x84cac load the shadow offset into s1
   through the .got slot and its cell; the walk then drops those two regions and adds the record's region (atom 10 = q,
   chunks rc / want_rc at 72 / 140). Two 4-byte instrumented checks (q + 72, q + 140), paid by the shadow entry
   mkSHE 10 0 184.
   0x84cc8 beqz rc: taken (rc = 0) -> 0x84ce0; not taken -> bcmp(q + 108, q + 76, 32) through the wrapper's contract
   abcmp_realizes (aj_bcmp_at), the state reseated at 0x84cdc (st_ok_after_call), 0x84cdc bnez a0: taken -> the abort
   call at 0x84d14, refuted: rc <> 0 gives out = before (premise), so the 32 bytes agree and a0 = 0.
   0x84cf8 bne rc,want_rc: taken -> the abort call, refuted by rc = want_rc (premise); not taken -> the return. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CPgWalkU CPgWalkStrU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Definition B_CHECK_RANGE : Z := 0x84c84.
Definition B_BCMP : Z := 0x42430.
Definition cg_rec : YP09.region := YP09.mkRegion (Some 10%nat) 0 184 0 0
[YP09.mkChunk 72 (CVal 4 (SOff 33 0)); YP09.mkChunk 140 (CVal 4 (SOff 34 0))].
Definition cg_xs (kc : kcallZ) : list Z := [kz_rc kc mod 2 ^ 32; kz_want_rc kc mod 2 ^ 32].
Definition cg_AF : list (nat * afact) :=
[(10%nat, mkAF 0 (2 ^ 47 - 185) 3); (33%nat, mkAF 0 (2 ^ 32 - 1) 0); (34%nat, mkAF 0 (2 ^ 32 - 1) 0)].
Definition cg_SH : list shent := [mkSHE 10 0 184].
(* `lw` of a 4-byte field s: the sign-extended value *)
Lemma cg_U_sx32 : forall E n s, ew E n = Z_to_bv 64 s -> 0 <= s < 2 ^ 32 ->
U E (SExt true 32 (SOff n 0)) = if s <? 2 ^ 31 then s else s + (2 ^ 64 - 2 ^ 32).
Proof.
intros E n s Hn Hs. rewrite U_SExt. cbv iota beta. rewrite (U_atom E n s Hn) by lia.
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small s) by lia.
unfold zcanon, M64, bv_swrap, bv_wrap.
replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity. replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
destruct (Z.ltb_spec s (2 ^ 31)).
- rewrite (Z.mod_small (s + 2 ^ 31)) by lia. replace (s + 2 ^ 31 - 2 ^ 31) with s by lia. rewrite Z.mod_small by lia. reflexivity.
- replace (s + 2 ^ 31) with ((s - 2 ^ 31) + 1 * 2 ^ 32) by lia. rewrite Z.mod_add by lia.
  rewrite (Z.mod_small (s - 2 ^ 31)) by lia.
  replace (s - 2 ^ 31 - 2 ^ 31) with ((s + (2 ^ 64 - 2 ^ 32)) + (-1) * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
(* two sign-extended 4-byte fields compare as the fields do *)
Lemma cg_U_sx32_eqb2 : forall E n m s t, ew E n = Z_to_bv 64 s -> ew E m = Z_to_bv 64 t ->
0 <= s < 2 ^ 32 -> 0 <= t < 2 ^ 32 ->
(U E (SExt true 32 (SOff n 0)) =? U E (SExt true 32 (SOff m 0))) = (s =? t).
Proof.
intros E n m s t Hn Hm Hs Ht. rewrite (cg_U_sx32 E n s Hn Hs), (cg_U_sx32 E m t Hm Ht).
destruct (Z.eqb_spec s t) as [Hst | Hst].
- subst t. apply Z.eqb_refl.
- apply Z.eqb_neq. destruct (Z.ltb_spec s (2 ^ 31)); destruct (Z.ltb_spec t (2 ^ 31)); lia.
Qed.
(* an int field read modulo 2 ^ 32 *)
Lemma cg_int_mod : forall v w, - 2 ^ 31 <= v < 2 ^ 31 -> - 2 ^ 31 <= w < 2 ^ 31 ->
(v mod 2 ^ 32 = w mod 2 ^ 32 <-> v = w).
Proof.
intros v w Hv Hw. split; [|intros ->; reflexivity]. intros H.
pose proof (Z.div_mod v (2 ^ 32) ltac:(lia)). pose proof (Z.div_mod w (2 ^ 32) ltac:(lia)).
pose proof (Z.mod_pos_bound v (2 ^ 32) ltac:(lia)). pose proof (Z.mod_pos_bound w (2 ^ 32) ltac:(lia)). lia.
Qed.

(* 0x84ce0 ..: the check of want_rc's shadow, lw want_rc, bne rc,want_rc (0x84cf8): taken -> the abort call,
   refuted by rc = want_rc; not taken -> the return *)
Ltac cg_tail HJ0 KE E33 E34 Hwant :=
  cw_run cw_awr_stk; cw_keep cw_kwr_stk;
  let Hb := fresh "Hb" in cw_branch Hb;
  [ rewrite branch_ne_U, (cg_U_sx32_eqb2 _ 33 34 _ _ E33 E34 ltac:(lia) ltac:(lia)) in Hb;
    exfalso; apply negb_true_iff, Z.eqb_neq in Hb; apply Hb; rewrite Hwant; reflexivity
  | cw_run cw_awr_stk; cw_keep cw_kwr_stk;
    cw_leaf ltac:(idtac; cw_kept HJ0 KE ltac:(intros ? []) ltac:(intros ? Hz; left; cbv beta in Hz; lia)) ltac:(exact I) ].
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ABCMP : abcmp_realizes tfibsegs B B_BCMP.
Theorem check_range_B_holds : cdcU_check_range_specX tfibsegs B MT B_CHECK_RANGE.
Proof using MTL TL LAWS ML ABCMP.
unfold cdcU_check_range_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q kc HE H10 Hq8 Hkc Hwf Hcrd Hout Hwant.
pose proof HE as (HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwin & Hwhi & Hev & Hlive).
cw_keep_j0 HJ HJ0.
unfold TB_check_range in *. assert (Hes : ESTACK = 4096) by reflexivity. rewrite Hes in *.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs (32 + 2 * 4096) HE ltac:(lia))
  as (Hceil & H47 & H46 & _ & Hpres).
pose proof Hwf as (Wk & _ & _ & _ & _ & _ & _ & _ & Wrc & Wwrc & _ & _ & _ & _ & Lbef & Lout & _).
pose proof Hcrd as (Hq0 & Hq63 & Hqv & Hqra & Hqhull & Hqam & Hqwin).
assert (Hq47 : q + 184 <= 2 ^ 47 - 1).
{ unfold amem_range in Hqam. rewrite C4, C5 in Hqam. destruct Hqam as [Hl | [_ Hh]]; lia. }
pose proof Hkc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Vrc & Vbef & Vout & Vwrc & _).
set (xs := cg_xs kc).
change (w64 q) with (Z_to_bv 64 q) in H10.
pose proof (Z.mod_pos_bound (kz_rc kc) (2 ^ 32) ltac:(lia)) as Mr.
pose proof (Z.mod_pos_bound (kz_want_rc kc) (2 ^ 32) ltac:(lia)) as Mw.
assert (X33 : ew (Ereg regs (cw_extra xs)) 33 = Z_to_bv 64 (kz_rc kc mod 2 ^ 32)) by exact (cw_ew_x regs xs 0).
assert (X34 : ew (Ereg regs (cw_extra xs)) 34 = Z_to_bv 64 (kz_want_rc kc mod 2 ^ 32)) by exact (cw_ew_x regs xs 1).
assert (HAF : atoms_ok (Ereg regs (cw_extra xs)) cg_AF).
{ unfold cg_AF. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), H10, X33, X34.
  rewrite !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 3) with 8.
  repeat split; lia. }
pose proof (cw_entry_base_af B TL LAWS B_CHECK_RANGE 32 xs cg_AF STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
  (32 + 2 * 4096) HE ltac:(lia) ltac:(vm_compute; reflexivity) HAF) as HS.
remember (Ereg regs (cw_extra xs)) as E eqn:HEE.
assert (HAE : env_agree 32 (Ereg regs (cw_extra xs)) E) by (subst E; apply env_agree_refl).
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 q) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
assert (E33 : ew E 33 = Z_to_bv 64 (kz_rc kc mod 2 ^ 32)) by (subst E; exact X33).
assert (E34 : ew E 34 = Z_to_bv 64 (kz_want_rc kc mod 2 ^ 32)) by (subst E; exact X34).
clear HEE X33 X34.
assert (SHOK : sh_ok tfibsegs CW_Bx cg_SH E (mrestrict (w_H W) memc)).
{ unfold cg_SH. apply Forall_cons; [|apply Forall_nil].
  exact (cw_shent_crd W memc (spZ regs) (32 + 2 * 4096) E 10 q 184 Hcrd E10 E32 ltac:(lia)). }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
  aview tfibsegs (w_H W) memc a = aview tfibsegs (w_H W) memc a) by (intros; reflexivity).
unfold cfg_at. change (w64 B_CHECK_RANGE) with (Z_to_bv 64 B_CHECK_RANGE).
(* 0x84c84-0x84cac: the saves, q into s0, the alignment check of q (not taken), the shadow offset into s1 *)
cw_run_to cw_awr_stk 0x84cb0. cw_keep cw_kwr_stk.
cw_drop_gb.
assert (VK : forall o n v, 0 <= o -> o + Z.of_nat n <= 184 ->
  val_mem tfibsegs (mrestrict (w_H W) memc) (q + o) n v -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (q + o) n v).
{ intros o n v Ho Hn Hv. apply (cw_val_mem_kept (w_H W) (w_H W) memc (ms_mem ms)); [|exact Hv].
  intros x Hx. apply KE; [lia | cbv beta; unfold coff_win in Hqwin; lia]. }
lazymatch goal with HS : st_ok _ ?Ev ?ssv ?msv |- _ =>
  assert (Hrok : region_ok tfibsegs Ev (ms_mem msv) cg_rec);
  [ unfold region_ok, cg_rec; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
    rewrite E10, unsigned_lit_small by lia;
    split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
    [ apply (chunk_ok_val tfibsegs E _ q 72 4 (SOff 33 0) (kz_rc kc mod 2 ^ 32));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
      apply (VK 72 4%nat); [lia | cbn; lia|];
      exact (cw_val_mem_mod (mrestrict (w_H W) memc) (q + 72) 4%nat (kz_rc kc) Vrc)
    | apply (chunk_ok_val tfibsegs E _ q 140 4 (SOff 34 0) (kz_want_rc kc mod 2 ^ 32));
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
      apply (VK 140 4%nat); [lia | cbn; lia|];
      exact (cw_val_mem_mod (mrestrict (w_H W) memc) (q + 140) 4%nat (kz_want_rc kc) Vwrc) ]
  | ];
  assert (Hdj : all_disjoint Ev cg_rec (ss_mem ssv));
  [ cbn [ss_mem all_disjoint]; unfold extent_disjoint, cg_rec;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite E10, B2, unsigned_lit_small by lia;
    unfold coff_win in Hqwin; split; [lia | exact I]
  | ];
  pose proof (ast_ok_add_region tfibsegs Ev ssv msv cg_rec HS eq_refl Hrok Hdj) as HS2;
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2; clear HS Hrok Hdj; rename HS2 into HS end.
(* 0x84cb0 ..: the check of rc's shadow, lw rc into s2, to beqz s2 at 0x84cc8 *)
cw_run cw_awr_stk. cw_keep cw_kwr_stk.
(* 0x84cc8 beqz rc *)
cw_branch Hb1.
all: rewrite branch_eq_U, (cw_U_sx32_eqb E 33 _ 0 E33 ltac:(lia) ltac:(lia)) in Hb1.
- (* taken: rc = 0, to 0x84ce0 *)
  apply Z.eqb_eq in Hb1.
  cg_tail HJ0 KE E33 E34 Hwant.
- (* rc <> 0: bcmp(out, before, 32) *)
  apply Z.eqb_neq in Hb1.
  assert (Krc : kz_rc kc <> 0) by (intros Hz; apply Hb1; rewrite Hz; reflexivity).
  cw_run cw_awr_stk. cw_keep cw_kwr_stk.
  (* 0x84cd8 jal: the bcmp wrapper's contract (aj_bcmp_at), then the state reseated at 0x84cdc *)
  rename HJ into HJ1.
  lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict (w_H W) ?msv) |- _ =>
    rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl); cbn [ss_pc] end.
  rreg HS (1%bv : bv 5) Gra. rreg HS (2%bv : bv 5) Gsp. rreg HS (3%bv : bv 5) Ggp. rreg HS (4%bv : bv 5) Gtp.
  rreg HS (10%bv : bv 5) Ga0. rreg HS (11%bv : bv 5) Ga1. rreg HS (12%bv : bv 5) Ga2.
  rewrite B2 in Gsp. rewrite E10, unsigned_lit_small in Ga0, Ga1 by lia. rewrite E3 in Ggp. rewrite E4 in Gtp.
  pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp0al & _) & _).
  pose proof (cw_crd_kept W memc (ms_mem ms1) (spZ regs) (32 + 2 * 4096) q 184 (spZ regs - 32) (spZ regs) Hcrd KE
    ltac:(lia) ltac:(unfold coff_win in Hqwin; lia)) as Hcrd1.
  pose proof (cw_crd_sub W (ms_mem ms1) (spZ regs) (32 + 2 * 4096) q 184 (q + 108) 32 Hcrd1 ltac:(lia) ltac:(lia) ltac:(lia))
    as (Hx0 & Hxn & Hxv & Hxra & Hxhull & Hxam & Hxwin).
  pose proof (cw_crd_sub W (ms_mem ms1) (spZ regs) (32 + 2 * 4096) q 184 (q + 76) 32 Hcrd1 ltac:(lia) ltac:(lia) ltac:(lia))
    as (Hy0 & Hyn & Hyv & Hyra & Hyhull & Hyam & Hywin).
  (* the 32 bytes of out and of before agree (rc <> 0 gives out = before), at the call's memory *)
  assert (Hbytes : forall i, 0 <= i < 32 ->
    aview tfibsegs (w_H W) (ms_mem ms1) (q + 108 + i) = aview tfibsegs (w_H W) (ms_mem ms1) (q + 76 + i)).
  { intros i Hi. rewrite (KE (q + 108 + i)) by (first [lia | cbv beta; unfold coff_win in Hqwin; lia]).
    rewrite (KE (q + 76 + i)) by (first [lia | cbv beta; unfold coff_win in Hqwin; lia]).
    rewrite (Hout Krc) in Vout.
    destruct (Vout (Z.to_nat i) ltac:(lia)) as [V1 _]. destruct (Vbef (Z.to_nat i) ltac:(lia)) as [V2 _].
    specialize (V1 0%nat ltac:(lia)). specialize (V2 0%nat ltac:(lia)).
    rewrite Z2Nat.id in V1, V2 by lia. change (Z.of_nat 0) with 0 in V1, V2. rewrite Z.add_0_r in V1, V2.
    unfold aview. rewrite V1, V2. reflexivity. }
  set (o := spZ regs - 32 - sp0).
  eapply SRr_bind.
  { eapply (cw_bcmp_at B LAWS B_BCMP ABCMP W (ms_regs ms1) (ms_mem ms1) STK sp0 FP ly S W0 mem0 md0
      own lyc Sc _ k (q + 108) (q + 76) 32 o (Z_to_bv 64 0x84cdc)).
    - exact HJ1.
    - exact Ga0.
    - exact Ga1.
    - exact Ga2.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - unfold spZ. rewrite Gsp, unsigned_lit_small by lia. unfold o. fold (spZ regs). lia.
    - unfold o. pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D1. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
      rewrite Hal16, Z.add_0_r in D1. rewrite Hsp0al, Z.add_0_r in D2.
      replace (spZ regs - 32 - sp0) with ((spZ regs / 16 - 2 - sp0 / 16) * 16) by lia. apply Z_mod_mult.
    - unfold o. lia.
    - rewrite Hes. unfold o. lia.
    - rewrite Ggp. exact Hgp.
    - rewrite Gtp. exact Htp.
    - exact Gra.
    - apply ret_ok_even. vm_compute. reflexivity.
    - intros a Ha. split; [apply Hxv; lia|]. unfold spZ. rewrite Gsp, unsigned_lit_small by lia. fold (spZ regs).
      rewrite Hes. unfold coff_win in Hqwin. lia.
    - intros a Ha. split; [apply Hyv; lia|]. unfold spZ. rewrite Gsp, unsigned_lit_small by lia. fold (spZ regs).
      rewrite Hes. unfold coff_win in Hqwin. lia.
    - intros a Ha. rewrite Hes. unfold o. unfold coff_win in Hqwin. lia.
    - intros a Ha. rewrite Hes. unfold o. unfold coff_win in Hqwin. lia.
    - exact Hxam.
    - exact Hyam.
    - exact Hxra.
    - exact Hxhull.
    - exact Hyra.
    - exact Hyhull. }
  cbv beta. intros W2 c2 Hwle (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hkept & Hpres2 & Hsame).
  rewrite Hes in Hkept.
  lazymatch type of HS with st_ok _ _ ?ssv _ =>
    let K := eval vm_compute in (run_K 0 (SOff 32 0) [] ssv) in
    jafter_call_keep HS K regs2 (mrestrict (w_H W) mem2) HP2 [0; 1]%nat HS2 end.
  match type of HS2 with ?Q -> _ => assert (HQ : Q) end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
    - eapply region_kept_aview; [rewrite E10; apply unsigned_lit_small; lia | | exact Hpres2].
      intros a Ha. apply Hkept; [lia | unfold o; unfold coff_win in Hqwin; lia].
    - eapply region_kept_aview; [exact B2 | | exact Hpres2].
      intros a Ha. apply Hkept; [lia | unfold o; lia]. }
  specialize (HS2 HQ). clear HQ. rewrite <- restrict_mkst_fx in HS2. clear HS. rename HS2 into HS.
  lazymatch type of HS with st_ok _ ?En _ _ => remember En as E' eqn:HE' in HS end.
  assert (E1' : ew E' 1 = getr regs 1) by (rewrite HE', ew_havoc_old by lia; exact E1).
  assert (B2' : bv_unsigned (ew E' 2) = spZ regs) by (rewrite HE', ew_havoc_old by lia; exact B2).
  assert (E10' : ew E' 10 = Z_to_bv 64 q) by (rewrite HE', ew_havoc_old by lia; exact E10).
  assert (E32' : ew E' 32 = Z_to_bv 64 SB) by (rewrite HE', ew_havoc_old by lia; exact E32).
  assert (E33' : ew E' 33 = Z_to_bv 64 (kz_rc kc mod 2 ^ 32)) by (rewrite HE', ew_havoc_old by lia; exact E33).
  assert (E34' : ew E' 34 = Z_to_bv 64 (kz_want_rc kc mod 2 ^ 32)) by (rewrite HE', ew_havoc_old by lia; exact E34).
  assert (HAE' : env_agree 32 (Ereg regs (cw_extra xs)) E') by (rewrite HE'; env_agree_chain HAE).
  assert (KE2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 8224 <= a < spZ regs) ->
    aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memc a).
  { intros a Ha Hz. rewrite (Hkept a Ha ltac:(unfold o; lia)). apply KE; [exact Ha | cbv beta; lia]. }
  rreg HS (10%bv : bv 5) Ga0'.
  assert (Hv39 : ew E' 39 = Z_to_bv 64 (bv_unsigned v)) by (rewrite <- Ga0', Hv; symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (bv_unsigned_in_range 64 v) as Hvr. change (bv_modulus 64) with (2 ^ 64) in Hvr.
  pose proof (cw_crd_kept W memc mem2 (spZ regs) (32 + 2 * 4096) q 184 (spZ regs - 8224) (spZ regs) Hcrd KE2
    ltac:(lia) ltac:(unfold coff_win in Hqwin; lia)) as Hcrd2.
  clear SHOK.
  assert (SHOK : sh_ok tfibsegs CW_Bx cg_SH E' (mrestrict (w_H W) mem2)).
  { unfold cg_SH. apply Forall_cons; [|apply Forall_nil].
    exact (cw_shent_crd W mem2 (spZ regs) (32 + 2 * 4096) E' 10 q 184 Hcrd2 E10' E32' ltac:(lia)). }
  clear E1 B2 E10 E32 E33 E34 E3 E4 HAE KE HJ1 Ga0'.
  rename E1' into E1. rename B2' into B2. rename E10' into E10. rename E32' into E32. rename E33' into E33.
  rename E34' into E34. rename HAE' into HAE. rename KE2 into KE.
  (* 0x84cdc bnez a0 *)
  cw_branch Hb4.
  all: rewrite branch_ne_U, (cw_U_atom0 E' 39 (bv_unsigned v) Hv39 Hvr), U_lit in Hb4 by lia.
  + (* taken: a0 <> 0, the abort call: refuted, the 32 bytes agree *)
    exfalso. apply negb_true_iff, Z.eqb_neq in Hb4. apply Hb4. rewrite (proj2 Hcmp Hbytes). reflexivity.
  + (* a0 = 0: to 0x84ce0 *)
    cg_tail HJ0 KE E33 E34 Hwant.
Qed.
End d.
End b.
