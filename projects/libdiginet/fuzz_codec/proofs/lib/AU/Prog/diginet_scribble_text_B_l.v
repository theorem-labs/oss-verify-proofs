(* diginet_scribble_text in image B (fuzz_codec.asan-ubsan, 0x86500): the segment L of
   diginet_scribble_text_B_inv.v -- one space of the padding loop at 0x8665c (sc_seg_L).

   The code: 0x8665c bltu a6,a7, the UBSan check of o + j (a6 = ~o, a7 = j < n < 2 ^ 32: not taken, decided by the
   atoms' ranges); the instrumented check of a1 = o + j (paid by the shadow entry of atom 11); a7 := j + 1;
   sb a4,0(a3): ' ' at o + j; a1, a3 one on; bne a2,a7 back to 0x8665c, else j 0x86698.
   The state is built with a3 pinned to atom 11 (a1 = a3 = o + j), a4 to 32 and a5 to the shadow offset (atom 32);
   the byte o + j is the state's one region, writable. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0l.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Ltac ewpeel := repeat (first [ rewrite ew_havoc_old by nat_side | rewrite ew_ewset_other by nat_side ]).
Ltac ewpeel_in H := repeat (first [ rewrite ew_havoc_old in H by nat_side | rewrite ew_ewset_other in H by nat_side ]).
Ltac sreg := lazymatch goal with HS : st_ok ?segs ?Ev ?ss (restrict ?H ?msv) |- context [getr (ms_regs ?msv) ?r] =>
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in
  let R := fresh "R" in
  assert (R : getr (ms_regs msv) r = sv_denot Ev e)
    by (refine (eq_trans (st_ok_restrict_reg segs H Ev ss msv r HS) _); reflexivity);
  rewrite R; clear R end.

(* a register the run did not write: its atom, the boundary's register; a5 is pinned to atom 32 *)
Ltac skeep := sreg; rewrite ?sv_denot_SOff0; ewpeel;
  first [ lazymatch goal with EE : forall n (rr : bv 5), _ -> ew ?Ev n = _ |- _ => apply EE; reflexivity end
        | lazymatch goal with E32 : ew _ 32 = _, R15 : getr _ 15 = w64 SHADOW_OFF |- _ =>
            rewrite E32, R15; reflexivity end
        | lazymatch goal with E10 : ew _ 10 = w64 _ |- _ => exact E10 end ].

(* the run's one write window: the byte o + j of atom 11, which the caller lets the call write *)
Ltac sl_awr := cbn [ss_mem];
  lazymatch goal with
  | TWj : twr_ok _ ?Bv ?STK ?sp0 ?FP ?ly ?S ?lyc ?Sc ?own ?W ?memc ?sp ?q 1, U11 : bv_unsigned (ew _ 11) = ?q |- _ =>
    eapply (cw_awr_ok_cons_twr Bv _ _ _ STK sp0 FP ly S lyc Sc own W memc sp q 1 11%nat);
    [reflexivity | ewpeel; exact U11 | cbn; lia | cbn; lia | exact TWj | apply awr_ok_nil] end.
(* fold a run's growth into KP and its frame into KE (zone: the byte o + j) *)
Ltac sl_keep :=
  lazymatch goal with HG : mem_grows (mrestrict ?H ?m1) (mrestrict ?H ?m2),
                      KP : forall a, apresent ?H ?m0 a -> apresent ?H ?m1 a |- _ =>
    let KQ := fresh "KQ" in
    assert (KQ : forall a, apresent H m0 a -> apresent H m2 a)
      by (intros a Ha; eapply apresent_grows; [exact HG | exact (KP a Ha)]);
    clear KP; rename KQ into KP end;
  cw_keep ltac:(let a := fresh "a" in let rr := fresh "rr" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
    intros a (rr & Hr & Hb); cbv beta;
    lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In rr rs') in Hr end;
    destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; ewpeel_in Hb;
    lazymatch goal with U11 : bv_unsigned (ew _ 11) = _ |- _ => rewrite U11 in Hb end; lia).

Ltac kio := first [ apply same_io_refl | eapply same_io_trans; [| apply cw_same_io_wvb]; kio ].

Definition sl_rout : YP09.region := YP09.mkRegion (Some 11%nat) 0 1 0 1 [].
Definition sl_sr : list sv := sr_set (sr_set (sr_set sr_atoms 13%bv (SOff 11 0)) 14%bv (SLit 32)) 15%bv (SOff 32 0).
Definition sl_G : facts :=
  mkFacts [(32%nat, mkAF SB SB 0); (11%nat, mkAF 1 (2 ^ 47 - 2) 0); (17%nat, mkAF 0 (2 ^ 32 - 2) 0);
           (16%nat, mkAF (2 ^ 63 - 1) (2 ^ 64 - 2) 0)] [] [].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws tfibsegs B.

Theorem sl_holds : sc_seg_L B.
Proof.
unfold sc_seg_L. intros g kk W2 c2 Hpre Hcut.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hcut as (-> & regs2 & mem2 & md2 & -> & HJ & Hio & HC & HPL).
destruct HPL as (r & j & outs & R10 & R17 & R11 & R13 & R14 & Hj & Hk & Hlen & Hout & Hspec).
destruct (sc_out B g Hpre) as (Ho0 & Hon & Hn & Hoff & HTD & HTW & HRAo & Hamo & _).
pose proof (sc_amem47 (sg_o g) (sg_n g) ltac:(lia) ltac:(lia) Hamo) as Ho47.
pose proof HC as (_ & _ & R12 & R15 & R16 & _ & _ & KC & PC).
set (E := Ereg regs2 (cw_extra [])).
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs2 rr)
  by (intros nn rr Hnn; unfold E; apply ew_Ereg_nat; exact Hnn).
assert (E10 : ew E 10 = w64 r) by (rewrite (EE 10%nat 10%bv eq_refl); exact R10).
assert (E11 : ew E 11 = Z_to_bv 64 (sg_o g + j)) by (rewrite (EE 11%nat 11%bv eq_refl); exact R11).
assert (E12 : ew E 12 = Z_to_bv 64 (sg_n g)) by (rewrite (EE 12%nat 12%bv eq_refl); exact R12).
assert (E16 : ew E 16 = Z_to_bv 64 (sg_noto g)) by (rewrite (EE 16%nat 16%bv eq_refl); exact R16).
assert (E17 : ew E 17 = Z_to_bv 64 j) by (rewrite (EE 17%nat 17%bv eq_refl); exact R17).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (apply cw_ew_SB).
assert (U11 : bv_unsigned (ew E 11) = sg_o g + j) by (rewrite E11; apply unsigned_lit_small; lia).
(* the byte o + j: present, its shadow usable *)
assert (Hpj : forall a, sg_o g + j <= a < sg_o g + j + 1 -> apresent (w_H (sg_W g)) mem2 a)
  by (intros a Ha; apply (sc_out_present B g mem2 Hpre PC); lia).
assert (RAj : range_addressable (aview tfibsegs (w_H (sg_W g)) mem2) SHADOW_OFF (sg_o g + j) 1).
{ apply (sc_ra_kept B g mem2 Hpre KC); [lia | lia | |].
  - unfold amem_range in Hamo |- *. rewrite C3, C4, C5 in *. lia.
  - eapply range_addressable_sub; [exact HRAo | lia | lia]. }
assert (HS : st_ok tfibsegs E (mkSS PC_L sl_sr [sl_rout] None sl_G)
  (restrict (w_H (sg_W g)) (mkst regs2 (Z_to_bv 64 PC_L) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. apply entry_st_ok_full; change (Ereg regs2 (cw_extra [])) with E.
  - unfold sl_sr.
    apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | discriminate |] | discriminate |]
      | discriminate |].
    + rewrite sv_denot_SOff0, E11. exact R13.
    + rewrite R14. reflexivity.
    + rewrite sv_denot_SOff0, E32. exact R15.
  - reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold region_ok, sl_rout. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U11. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros a Ha. apply (apresent_writable tfibsegs). apply Hpj. lia.
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - split; [|split; exact I]. unfold sl_G. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E32, U11, E17, E16. unfold sg_noto. rewrite !unsigned_lit_small by (unfold SB; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat split; first [exact I | lia]. }
clearbody E.
assert (SHOK : sh_ok tfibsegs CW_Bx [mkSHE 11 0 1] E (mrestrict (w_H (sg_W g)) mem2)).
{ apply Forall_cons; [|apply Forall_nil].
  apply (cw_shent_ra (sg_W g) mem2 E 11 (sg_o g + j) 1 RAj); [| lia | lia | lia | exact E11 | exact E32].
  unfold amem_range in Hamo |- *. rewrite C3, C4, C5 in *. lia. }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (sg_o g + j <= a < sg_o g + j + 1) ->
  aview tfibsegs (w_H (sg_W g)) mem2 a = aview tfibsegs (w_H (sg_W g)) mem2 a) by (intros; reflexivity).
assert (KP : forall a, apresent (w_H (sg_W g)) mem2 a -> apresent (w_H (sg_W g)) mem2 a) by (intros; assumption).
assert (TWj : twr_ok tfibsegs B (sg_STK g) (sg_sp0 g) (sg_FP g) (sg_ly g) (sg_S g) (sg_lyc g) (sg_Sc g) (sg_own g)
  (sg_W g) (sg_memc g) (sg_sp g) (sg_o g + j) 1) by (intros a Ha; apply HTW; lia).
unfold cfg_at. change (w64 PC_L) with (Z_to_bv 64 PC_L).
cw_run sl_awr.
sl_keep.
(* 0x86680 bne a2,a7: n against j + 1 *)
cw_branch Hb.
all: lazymatch type of Hb with branch_taken _ (sv_denot ?Ev _) _ = _ =>
  rewrite branch_ne_U, (U_atom Ev 12 (sg_n g) ltac:(ewpeel; exact E12) ltac:(lia)),
    (U_atom_off Ev 17 j 1 ltac:(ewpeel; exact E17) ltac:(lia) ltac:(lia)) in Hb end.
all: assert (Hsp : Z.to_nat (sg_n g - j) = S (Z.to_nat (sg_n g - (j + 1)))) by lia.
all: rewrite Hsp in Hspec; cbn [repeat] in Hspec.
all: replace (outs ++ 32 :: repeat 32 (Z.to_nat (sg_n g - (j + 1)))) with
       ((outs ++ [32]) ++ repeat 32 (Z.to_nat (sg_n g - (j + 1)))) in Hspec by (rewrite <- app_assoc; reflexivity).
- (* taken: j + 1 <> n, back to the loop head *)
  apply negb_true_iff, Z.eqb_neq in Hb.
  cw_run_to sl_awr PC_L.
  sl_keep.
  pose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as RG. cbn [ms_mem restrict] in RG.
  lazymatch type of RG with region_ok _ _ _ ?rg => let rg' := eval vm_compute in rg in change rg with rg' in RG end.
  pose proof (field_of_region _ _ 11 (sg_o g + j) _ 0 1 0 1 0 1%N (SLit 32) 32 RG ltac:(ewpeel; exact U11)
    ltac:(apply in_eq) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V32.
  rewrite Z.add_0_r in V32. change (N.to_nat 1) with 1%nat in V32.
  apply SRr_ret. left.
  lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
    apply (sc_cut_close B g PC_L (P_L g kk) regs2 mem2 md2 msv _ Hpre Hio HC HJ);
    [ kio
    | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl)
    | unfold sc_kregs, sc_lregs; cbn [app]; repeat (apply Forall_cons; [cbv beta; skeep|]); apply Forall_nil
    | intros a Ha Hz; apply KE; [exact Ha | lia]
    | exact KP | ] end.
  exists r, (j + 1), (outs ++ [32]).
  split; [skeep|].
  split; [sreg; cbn [sv_denot]; ewpeel; rewrite E17, unsigned_lit_small by lia; reflexivity|].
  split; [sreg; cbn [sv_denot]; ewpeel; rewrite U11; unfold w64; f_equal; lia|].
  split; [sreg; cbn [sv_denot]; ewpeel; rewrite U11; unfold w64; f_equal; lia|].
  split; [sreg; reflexivity|].
  split; [lia|]. split; [lia|]. split; [rewrite length_app; cbn [length]; lia|].
  split; [|exact Hspec].
  apply sc_garr8_snoc; [| rewrite Hlen; exact V32 | lia].
  apply (sc_garr8_kept (mrestrict (w_H (sg_W g)) mem2)); [|exact Hout].
  intros x Hx. apply (mbyte_of_aview tfibsegs). apply KE; lia.
- (* j + 1 = n: to the return *)
  apply negb_false_iff, Z.eqb_eq in Hb.
  cw_run_to sl_awr PC_X.
  sl_keep.
  pose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as RG. cbn [ms_mem restrict] in RG.
  lazymatch type of RG with region_ok _ _ _ ?rg => let rg' := eval vm_compute in rg in change rg with rg' in RG end.
  pose proof (field_of_region _ _ 11 (sg_o g + j) _ 0 1 0 1 0 1%N (SLit 32) 32 RG ltac:(ewpeel; exact U11)
    ltac:(apply in_eq) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V32.
  rewrite Z.add_0_r in V32. change (N.to_nat 1) with 1%nat in V32.
  apply SRr_ret. right.
  lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
    apply (sc_cut_close B g PC_X (P_X g) regs2 mem2 md2 msv _ Hpre Hio HC HJ);
    [ kio
    | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl)
    | unfold sc_kregs, sc_lregs; cbn [app]; repeat (apply Forall_cons; [cbv beta; skeep|]); apply Forall_nil
    | intros a Ha Hz; apply KE; [exact Ha | lia]
    | exact KP | ] end.
  replace (Z.to_nat (sg_n g - (j + 1))) with 0%nat in Hspec by lia. cbn [repeat] in Hspec.
  unfold P_X. rewrite app_nil_r in Hspec. rewrite Hspec. cbn [fst snd].
  split; [skeep|].
  apply sc_garr8_snoc; [| rewrite Hlen; exact V32 | lia].
  apply (sc_garr8_kept (mrestrict (w_H (sg_W g)) mem2)); [|exact Hout].
  intros x Hx. apply (mbyte_of_aview tfibsegs). apply KE; lia.
Time Qed.
End h.
End d.
