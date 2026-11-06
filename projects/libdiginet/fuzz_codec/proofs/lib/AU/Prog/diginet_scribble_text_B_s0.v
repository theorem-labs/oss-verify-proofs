(* diginet_scribble_text in image B (fuzz_codec.asan-ubsan, 0x86500): the segment S0 of
   diginet_scribble_text_B_inv.v -- from the entry to the loop head 0x86544 with i = j = 0 (sc_seg_S0).

   The code 0x86500 .. 0x86540: sp -= 16; ra at sp + 8 and s0 at sp (the frame); beqz a1 (o >= 1 by cdst_ok: not
   taken, decided by atom 11's range); a3 := a0 = q; a0 := the .got slot 0x9e430, a5 := the shadow offset through it;
   a6 := ~o; beqz a3 (q >= 1 by cstr_rd: not taken, decided by atom 10's range); t5 = a0 = a7 := 0, t0 := q + 1,
   t1 := 46, t2 := 49, t3 := 57. One run, whose only writes are the two saves. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CPgWalkU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import diginet_scribble_text_B_inv.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0l.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Definition ss_AF : list (nat * afact) :=
[(10%nat, mkAF 1 (2 ^ 47 - 2) 0); (11%nat, mkAF 1 (2 ^ 47 - 1) 0); (12%nat, mkAF 0 (2 ^ 32 - 1) 0)].

(* the env's atoms through the layers a run adds *)
Ltac ewpeel := repeat (first [ rewrite ew_havoc_old by nat_side | rewrite ew_ewset_other by nat_side ]).
(* rewrite the goal's register r of the stopped state by its symbolic value *)
Ltac sreg := lazymatch goal with HS : st_ok ?segs ?Ev ?ss (restrict ?H ?msv) |- context [getr (ms_regs ?msv) ?r] =>
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in
  let R := fresh "R" in
  assert (R : getr (ms_regs msv) r = sv_denot Ev e)
    by (refine (eq_trans (st_ok_restrict_reg segs H Ev ss msv r HS) _); reflexivity);
  rewrite R; clear R end.
(* ~o as `xori a6,a1,-1` computes it *)
Lemma ss_not : forall E n o, ew E n = Z_to_bv 64 o -> 0 <= o < 2 ^ 64 ->
  U E (SAlu ALU_XOR (SOff n 0) (SLit (-1))) = 2 ^ 64 - 1 - o.
Proof.
intros E n o Hn Ho. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n o Hn Ho), U_SLit.
change (zcanon (-1)) with 18446744073709551615. rewrite ZBridge.zb_lxor_ones by lia.
apply zcanon_id. unfold M64. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.

Theorem ss0_holds : sc_seg_S0 B.
Proof.
unfold sc_seg_S0. intros g Hpre.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hpre as (HE & H10 & HSTR & H11 & H12 & (Hn & HnL) & HDST & HOJ & HDJ).
destruct (sc_stack B g Hpre) as (Hceil & H47 & H46 & Hal & Hwin & Hsp0 & Hprs).
destruct (sc_text B g Hpre) as (Hq0 & Hql & Hin0 & Hlen0 & HG & HRAq & Hamq & Hoffq).
destruct (sc_out B g Hpre) as (Ho0 & Hon & _ & Hoff & HTD & HTW & HRAo & Hamo & _).
pose proof (sc_amem47 (sg_q g) (sg_len g) ltac:(lia) ltac:(lia) Hamq) as Hq47.
pose proof (sc_amem47 (sg_o g) (sg_n g) ltac:(lia) ltac:(lia) Hamo) as Ho47.
pose proof HE as (HJ0 & Hra & Hra4 & Hgp & Htp & _).
pose proof HJ0 as HJ.
unfold sg_sp in *.
set (regs := sg_regs g) in *.
change (w64 (sg_q g)) with (Z_to_bv 64 (sg_q g)) in H10.
change (w64 (sg_o g)) with (Z_to_bv 64 (sg_o g)) in H11.
change (w64 (sg_n g)) with (Z_to_bv 64 (sg_n g)) in H12.
assert (HAF : atoms_ok (Ereg regs (cw_extra [])) ss_AF).
{ unfold ss_AF. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), H10, (ew_Ereg_nat regs _ 11 11%bv eq_refl), H11,
    (ew_Ereg_nat regs _ 12 12%bv eq_refl), H12.
  rewrite !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat split; lia. }
pose proof (cw_entry_base_af B TL LAWS B_ST 16 [] ss_AF (sg_STK g) (sg_sp0 g) (sg_FP g) (sg_ly g) (sg_S g) (sg_W0 g)
  (sg_mem0 g) (sg_md0 g) (sg_own g) (sg_lyc g) (sg_Sc g) (sg_W g) (sg_memc g) (sg_mdc g) (sg_k g) regs 16
  HE ltac:(lia) ltac:(vm_compute; reflexivity) HAF) as HS.
remember (Ereg regs (cw_extra [])) as E eqn:HEE.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros nn r Hnn; subst E; apply ew_Ereg_nat; exact Hnn).
assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 (sg_q g)) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 (sg_o g)) by (rewrite (EE 11%nat 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 (sg_n g)) by (rewrite (EE 12%nat 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
clear HEE.
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H (sg_W g)) (sg_memc g))) by apply Forall_nil.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
  aview tfibsegs (w_H (sg_W g)) (sg_memc g) a = aview tfibsegs (w_H (sg_W g)) (sg_memc g) a) by (intros; reflexivity).
assert (KP : forall a, apresent (w_H (sg_W g)) (sg_memc g) a -> apresent (w_H (sg_W g)) (sg_memc g) a)
  by (intros; assumption).
unfold cfg_at. change (w64 B_ST) with (Z_to_bv 64 B_ST).
cw_run_to cw_awr_stk PC_H.
lazymatch goal with HG : mem_grows (mrestrict ?H ?m1) (mrestrict ?H ?m2) |- _ =>
  let KQ := fresh "KQ" in
  assert (KQ : forall a, apresent H (sg_memc g) a -> apresent H m2 a)
    by (intros a Ha; eapply apresent_grows; [exact HG | exact (KP a Ha)]);
  clear KP; rename KQ into KP end.
cw_keep cw_kwr_stk.
pose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as RG. cbn [ms_mem restrict] in RG.
lazymatch type of RG with region_ok _ _ _ ?rg => let rg' := eval vm_compute in rg in change rg with rg' in RG end.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  assert (AGv : forall n, (n < 33)%nat -> ew Ev n = ew E n) by (intros nn Hnn; ewpeel; reflexivity) end.
apply SRr_ret. split; [reflexivity|].
exists (ms_regs ms), (ms_mem ms); eexists.
split; [rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply same_io_trans; [apply same_io_refl | apply cw_same_io_wvb]|].
split.
{ (* sc_common *)
  split.
  { unfold sc_kregs. repeat (apply Forall_cons; [cbv beta; sreg; rewrite sv_denot_SOff0; ewpeel;
      apply EE; reflexivity|]). apply Forall_nil. }
  split.
  { sreg. rewrite denot_lit_U.
    lazymatch goal with |- Z_to_bv 64 (U ?Ev _) = _ =>
      rewrite (cw_U_offx Ev 2 (spZ regs) (-16) ltac:(ewpeel; rewrite (EE 2%nat 2%bv eq_refl); unfold spZ;
        symmetry; apply Z_to_bv_bv_unsigned) ltac:(unfold spZ; apply sc_u64)) end.
    unfold w64. rewrite Z.mod_small by lia. f_equal; try lia. }
  split; [sreg; rewrite sv_denot_SOff0; ewpeel; exact E12|].
  split; [sreg; rewrite sv_denot_SOff0; ewpeel; rewrite E32; reflexivity|].
  split.
  { sreg. rewrite denot_lit_U.
    lazymatch goal with |- Z_to_bv 64 (U ?Ev _) = _ =>
      rewrite (ss_not Ev 11 (sg_o g) ltac:(ewpeel; exact E11) ltac:(lia)) end. reflexivity. }
  split.
  { replace (sg_sp g - 8) with (sg_sp g + -8) by lia.
    eapply (field_of_region _ _ 2 _ _ _ _ _ _ (-8) 8%N (SOff 1 0) (raZ regs) RG).
    - try rewrite (AGv 2%nat ltac:(lia)). exact B2.
    - repeat (first [apply in_eq | apply in_cons]).
    - rewrite sv_denot_SOff0; try rewrite (AGv 1%nat ltac:(lia)); rewrite (EE 1%nat 1%bv eq_refl). unfold raZ.
      symmetry. apply Z_to_bv_bv_unsigned.
    - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold raZ. apply sc_u64.
    - lia. }
  split.
  { replace (sg_sp g - 16) with (sg_sp g + -16) by lia.
    eapply (field_of_region _ _ 2 _ _ _ _ _ _ (-16) 8%N (SOff 8 0) (bv_unsigned (getr regs 8)) RG).
    - try rewrite (AGv 2%nat ltac:(lia)). exact B2.
    - repeat (first [apply in_eq | apply in_cons]).
    - rewrite sv_denot_SOff0; try rewrite (AGv 8%nat ltac:(lia)); rewrite (EE 8%nat 8%bv eq_refl). symmetry. apply Z_to_bv_bv_unsigned.
    - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply sc_u64.
    - lia. }
  split.
  { intros a Ha Hz. apply KE; [exact Ha|]. intros Hs. apply Hz. left. exact Hs. }
  exact KP. }
(* P_H at i = j = 0 *)
exists 0, 0, [].
split; [sreg; reflexivity|].
split; [sreg; reflexivity|].
split; [sreg; rewrite sv_denot_SOff0; ewpeel; exact E11|].
split; [sreg; rewrite sv_denot_SOff0; ewpeel; exact E10|].
split; [sreg; cbn [sv_denot]; ewpeel; rewrite E10, unsigned_lit_small by lia; reflexivity|].
split; [sreg; reflexivity|].
split; [sreg; reflexivity|].
split; [sreg; reflexivity|].
split; [sreg; reflexivity|].
split; [lia|].
split; [cbn [Z.to_nat skipn]; exact Hin0|].
split; [unfold sg_len; lia|].
split; [lia|].
split; [reflexivity|].
split; [apply garr8_nil|].
unfold sc_res, scribble_text_spec. rewrite Z.sub_0_r. change (Z.to_nat 0) with 0%nat. cbn [skipn app].
rewrite Z.add_0_l. apply surjective_pairing.
Time Qed.
End h.
End d.
