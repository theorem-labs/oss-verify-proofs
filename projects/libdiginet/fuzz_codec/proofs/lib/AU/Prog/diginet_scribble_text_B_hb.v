(* diginet_scribble_text in image B (fuzz_codec.asan-ubsan, 0x86500): the segment Hb of
   diginet_scribble_text_B_inv.v -- from 0x865c4, a byte b that is not '.' followed by a digit, to the loop head
   0x86544 (sc_seg_Hb).

   The code: 0x865c4 bltu a6,a7, the UBSan check of o + j (a6 = ~o, a7 = j < n < 2 ^ 32: not taken, decided by the
   atoms' ranges); 0x865c8 slli a4,t4,56; bgez a4: b below 0x80 keeps t4 = b, else t4 := 0x3f; a4 := a1 + a7 = o + j
   (0x865d4, pinned to atom 33 at 0x865d8); the instrumented check of a4 (paid by the shadow entry of atom 33);
   sb t4 at o + j; a4 := 1; 0x865f0 a0 := i + 1, a7 := j + 1, a4 := a0 + a3 = q + i + 1, t5 := (a4 == 0);
   bgeu a4,a0 (the UBSan check of q + i + 1: q + i + 1 < 2 ^ 64, so it does not wrap) back to 0x86544, else the
   trap at 0x866a8 (not reached). The byte o + j is the state's one region, writable. *)
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
            rewrite E32, R15; reflexivity end ].
Ltac kio := first [ apply same_io_refl | eapply same_io_trans; [| apply cw_same_io_wvb]; kio ].
(* the run's one write window: the byte o + j of atom 33, which the caller lets the call write *)
Ltac sb_awr := cbn [ss_mem];
  lazymatch goal with
  | TWj : twr_ok _ ?Bv ?STK ?sp0 ?FP ?ly ?S ?lyc ?Sc ?own ?W ?memc ?sp ?q 1, U33 : bv_unsigned (ew _ 33) = ?q |- _ =>
    eapply (cw_awr_ok_cons_twr Bv _ _ _ STK sp0 FP ly S lyc Sc own W memc sp q 1 33%nat);
    [reflexivity | ewpeel; exact U33 | cbn; lia | cbn; lia | exact TWj | apply awr_ok_nil] end.
(* fold a run's growth into KP and its frame into KE (zone: the byte o + j) *)
Ltac sb_keep :=
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
    lazymatch goal with U33 : bv_unsigned (ew _ 33) = _ |- _ => rewrite U33 in Hb end; lia).

(* `slli a4,t4,56; bgez a4` is the test t4 < 0x80 on a byte *)
Lemma sb_br_sign : forall (E : env) m v, ew E m = Z_to_bv 64 v -> 0 <= v < 256 ->
  branch_taken BC_GE (sv_denot E (SAlu ALU_SLL (SOff m 0) (SLit 56))) (sv_denot E (SLit 0)) = (v <? 128).
Proof.
intros E m v Hm Hv.
assert (HU : U E (SAlu ALU_SLL (SOff m 0) (SLit 56)) = v * 2 ^ 56).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E m v Hm ltac:(lia)), U_SLit.
  change (Z.land (zcanon 56) 63) with 56. rewrite Z.shiftl_mul_pow2 by lia.
  apply zcanon_id. unfold M64. lia. }
rewrite (denot_lit_U E (SAlu ALU_SLL (SOff m 0) (SLit 56))), (denot_lit_U E (SLit 0)), HU, U_SLit.
change (zcanon 0) with 0.
cbn [branch_taken]. unfold bv_lts. rewrite !Z_to_bv_signed.
rewrite (bv_swrap_small 64 0) by (change (bv_half_modulus 64) with (2 ^ 63); lia).
destruct (Z.ltb_spec v 128) as [Hlt | Hge].
- rewrite bv_swrap_small by (change (bv_half_modulus 64) with (2 ^ 63); nia).
  apply negb_true_iff. apply Z.ltb_ge. nia.
- unfold bv_swrap, bv_wrap. change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
  replace ((v * 2 ^ 56 + 2 ^ 63) mod 2 ^ 64) with (v * 2 ^ 56 - 2 ^ 63)
    by (replace (v * 2 ^ 56 + 2 ^ 63) with ((v * 2 ^ 56 - 2 ^ 63) + 1 * 2 ^ 64) by lia;
        rewrite Z.mod_add by lia; rewrite Z.mod_small by nia; lia).
  apply negb_false_iff. apply Z.ltb_lt. nia.
Qed.

Definition sb_rout : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 1 [].
Definition sb_sr : list sv := sr_set sr_atoms 15%bv (SOff 32 0).
Definition sb_G : facts :=
  mkFacts [(32%nat, mkAF SB SB 0); (33%nat, mkAF 1 (2 ^ 47 - 2) 0); (11%nat, mkAF 1 (2 ^ 47 - 2) 0);
           (17%nat, mkAF 0 (2 ^ 32 - 2) 0); (16%nat, mkAF (2 ^ 63 - 1) (2 ^ 64 - 2) 0);
           (10%nat, mkAF 0 (2 ^ 47 - 2) 0); (13%nat, mkAF 1 (2 ^ 47 - 2) 0); (29%nat, mkAF 1 255 0)] [] [].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws tfibsegs B.

Theorem shb_holds : sc_seg_Hb B.
Proof.
unfold sc_seg_Hb. intros g fuel W2 c2 Hpre Hcut.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hcut as (-> & regs2 & mem2 & md2 & -> & HJ & Hio & HC & HPO).
destruct HPO as (i & j & b & outs & R10 & R17 & R11 & R13 & R5 & R6 & R7 & R28 & R29 & Hi & Hbn & Hb0 & Hin1 & Hf &
  Hj & Hlen & Hout & Hspec).
destruct (sc_text B g Hpre) as (Hq0 & Hql & Hin0 & Hlen0 & HG & HRAq & Hamq & Hoffq).
destruct (sc_out B g Hpre) as (Ho0 & Hon & Hn & Hoff & HTD & HTW & HRAo & Hamo & _).
pose proof (sc_amem47 (sg_o g) (sg_n g) ltac:(lia) ltac:(lia) Hamo) as Ho47.
pose proof (sc_amem47 (sg_q g) (sg_len g) ltac:(lia) ltac:(lia) Hamq) as Hq47.
pose proof HC as (_ & _ & R12 & R15 & R16 & _ & _ & KC & PC).
assert (Hil : (Z.to_nat i + 1 < length (sg_tb g))%nat) by (pose proof (sc_in_skipn_lt 0 _ _ Hin1); lia).
unfold sg_len in *.
assert (Hbr : 0 <= b < 256)
  by (rewrite <- Hbn; exact (proj2 (sc_text_val B g mem2 Hpre KC (Z.to_nat i) ltac:(lia)))).
set (E := Ereg regs2 (cw_extra [sg_o g + j])).
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs2 rr)
  by (intros nn rr Hnn; unfold E; apply ew_Ereg_nat; exact Hnn).
assert (E10 : ew E 10 = Z_to_bv 64 i) by (rewrite (EE 10%nat 10%bv eq_refl); exact R10).
assert (E11 : ew E 11 = Z_to_bv 64 (sg_o g)) by (rewrite (EE 11%nat 11%bv eq_refl); exact R11).
assert (E12 : ew E 12 = Z_to_bv 64 (sg_n g)) by (rewrite (EE 12%nat 12%bv eq_refl); exact R12).
assert (E13 : ew E 13 = Z_to_bv 64 (sg_q g)) by (rewrite (EE 13%nat 13%bv eq_refl); exact R13).
assert (E16 : ew E 16 = Z_to_bv 64 (sg_noto g)) by (rewrite (EE 16%nat 16%bv eq_refl); exact R16).
assert (E17 : ew E 17 = Z_to_bv 64 j) by (rewrite (EE 17%nat 17%bv eq_refl); exact R17).
assert (E29 : ew E 29 = Z_to_bv 64 b) by (rewrite (EE 29%nat 29%bv eq_refl); exact R29).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (apply cw_ew_SB).
assert (E33 : ew E 33 = Z_to_bv 64 (sg_o g + j)) by (exact (cw_ew_x regs2 [sg_o g + j] 0)).
assert (U33 : bv_unsigned (ew E 33) = sg_o g + j) by (rewrite E33; apply unsigned_lit_small; lia).
assert (Hpj : forall a, sg_o g + j <= a < sg_o g + j + 1 -> apresent (w_H (sg_W g)) mem2 a)
  by (intros a Ha; apply (sc_out_present B g mem2 Hpre PC); lia).
assert (RAj : range_addressable (aview tfibsegs (w_H (sg_W g)) mem2) SHADOW_OFF (sg_o g + j) 1).
{ apply (sc_ra_kept B g mem2 Hpre KC); [lia | lia | |].
  - unfold amem_range in Hamo |- *. rewrite C3, C4, C5 in *. lia.
  - eapply range_addressable_sub; [exact HRAo | lia | lia]. }
assert (HS : st_ok tfibsegs E (mkSS PC_O sb_sr [sb_rout] None sb_G)
  (restrict (w_H (sg_W g)) (mkst regs2 (Z_to_bv 64 PC_O) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. apply entry_st_ok_full; change (Ereg regs2 (cw_extra [sg_o g + j])) with E.
  - unfold sb_sr. apply regs_ok_pin; [apply regs_ok_Ereg | discriminate |].
    rewrite sv_denot_SOff0, E32. exact R15.
  - reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold region_ok, sb_rout. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U33. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros a Ha. apply (apresent_writable tfibsegs). apply Hpj. lia.
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - split; [|split; exact I]. unfold sb_G. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E32, U33, E11, E17, E16, E10, E13, E29. unfold sg_noto, sg_len in *.
    rewrite !unsigned_lit_small by (unfold SB; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat split; first [exact I | lia]. }
clearbody E.
assert (SHOK : sh_ok tfibsegs CW_Bx [mkSHE 33 0 1] E (mrestrict (w_H (sg_W g)) mem2)).
{ apply Forall_cons; [|apply Forall_nil].
  apply (cw_shent_ra (sg_W g) mem2 E 33 (sg_o g + j) 1 RAj); [| lia | lia | lia | exact E33 | exact E32].
  unfold amem_range in Hamo |- *. rewrite C3, C4, C5 in *. lia. }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (sg_o g + j <= a < sg_o g + j + 1) ->
  aview tfibsegs (w_H (sg_W g)) mem2 a = aview tfibsegs (w_H (sg_W g)) mem2 a) by (intros; reflexivity).
assert (KP : forall a, apresent (w_H (sg_W g)) mem2 a -> apresent (w_H (sg_W g)) mem2 a) by (intros; assumption).
assert (TWj : twr_ok tfibsegs B (sg_STK g) (sg_sp0 g) (sg_FP g) (sg_ly g) (sg_S g) (sg_lyc g) (sg_Sc g) (sg_own g)
  (sg_W g) (sg_memc g) (sg_sp g) (sg_o g + j) 1) by (intros a Ha; apply HTW; lia).
unfold cfg_at. change (w64 PC_O) with (Z_to_bv 64 PC_O).
assert (E5 : ew E 5 = Z_to_bv 64 (sg_q g + 1)) by (rewrite (EE 5%nat 5%bv eq_refl); exact R5).
assert (E6 : ew E 6 = Z_to_bv 64 46) by (rewrite (EE 6%nat 6%bv eq_refl); exact R6).
assert (E7 : ew E 7 = Z_to_bv 64 49) by (rewrite (EE 7%nat 7%bv eq_refl); exact R7).
assert (E28 : ew E 28 = Z_to_bv 64 57) by (rewrite (EE 28%nat 28%bv eq_refl); exact R28).
(* 0x865c4 .. 0x865c8: the check of o + j (decided), slli; stop at bgez *)
cw_run sb_awr. sb_keep.
cw_branch Hs.
all: lazymatch type of Hs with branch_taken _ (sv_denot ?Ev _) _ = _ =>
  rewrite (sb_br_sign Ev 29 b ltac:(ewpeel; exact E29) Hbr) in Hs end.
all: set (v := if b <? 128 then b else 63).
all: assert (Hv : 0 <= v < 256) by (unfold v; destruct (b <? 128); lia).
(* to 0x865d8: a4 = a1 + a7, pinned to atom 33 *)
all: cw_run_to sb_awr 0x865d8; sb_keep.
all: lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict ?Hh ?msv) |- _ =>
  pose proof (ast_ok_set_reg_fp tfibsegs Ev ssv (restrict Hh msv) (14%bv : bv 5) (SOff 33 0) HS eq_refl
    ltac:(cbn [ms_regs restrict]; sreg; rewrite sv_denot_SOff0; ewpeel; rewrite E33; symmetry;
          apply (denot_add2 Ev 11 17 (sg_o g) j); [ewpeel; exact E11 | ewpeel; exact E17 | lia | lia | lia]))
    as YS; clear HS; rename YS into HS; norm_ss HS end.
(* the check of o + j (mkSHE 33 0 1), the store, the advance; stop at bgeu a4,a0 *)
all: cw_run sb_awr; sb_keep.
all: cw_branch Ht.
all: lazymatch type of Ht with branch_taken _ (sv_denot ?Ev _) _ = _ =>
  rewrite branch_geu_U, U_SAlu in Ht; cbn [zalu_raw] in Ht;
  rewrite (U_atom_off Ev 10 i 1 ltac:(ewpeel; exact E10) ltac:(lia) ltac:(lia)),
          (U_atom Ev 13 (sg_q g) ltac:(ewpeel; exact E13) ltac:(lia)) in Ht;
  rewrite zcanon_id in Ht by (unfold M64; lia) end.
all: first [ apply negb_true_iff, Z.ltb_ge in Ht | apply negb_false_iff, Z.ltb_lt in Ht; exfalso; lia ].
all: cw_run_to sb_awr PC_H; sb_keep.
all: pose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as RG; cbn [ms_mem restrict] in RG.
all: lazymatch type of RG with region_ok _ _ _ ?rg => let rg' := eval vm_compute in rg in change rg with rg' in RG end.
all: assert (Vv : val_mem tfibsegs (mrestrict (w_H (sg_W g)) (ms_mem ms)) (sg_o g + j) 1 v).
1, 3: (* the byte stored *)
  first
  [ pose proof (field_of_region _ _ 33 (sg_o g + j) _ 0 1 0 1 0 1%N (SOff 29 0) b RG ltac:(ewpeel; exact U33)
      ltac:(apply in_eq) ltac:(rewrite sv_denot_SOff0; ewpeel; exact E29) ltac:(cbn; lia) ltac:(cbn; lia)) as V0;
    rewrite Z.add_0_r in V0; unfold v; rewrite Hs; exact V0
  | pose proof (field_of_region _ _ 33 (sg_o g + j) _ 0 1 0 1 0 1%N (SLit 63) 63 RG ltac:(ewpeel; exact U33)
      ltac:(apply in_eq) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V0;
    rewrite Z.add_0_r in V0; unfold v; rewrite Hs; exact V0
  | match type of RG with ?T => idtac "DBGRG" T end; fail ].
all: apply SRr_ret.
all: lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
    apply (sc_cut_close B g PC_H (P_H g fuel) regs2 mem2 md2 msv _ Hpre Hio HC HJ);
    [ kio
    | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl)
    | unfold sc_kregs, sc_lregs; cbn [app]; repeat (apply Forall_cons; [cbv beta; skeep|]); apply Forall_nil
    | intros a Ha Hz; apply KE; [exact Ha | lia]
    | exact KP | ] end.
all: exists (i + 1), (j + 1), (outs ++ [v]).
all: split; [sreg; cbn [sv_denot]; ewpeel; rewrite E10, unsigned_lit_small by (unfold sg_len in *; lia); reflexivity|].
all: split; [sreg; cbn [sv_denot]; ewpeel; rewrite E17, unsigned_lit_small by lia; reflexivity|].
all: split; [sreg; rewrite sv_denot_SOff0; ewpeel; exact E11|].
all: split; [sreg; rewrite sv_denot_SOff0; ewpeel; exact E13|].
all: split; [sreg; rewrite sv_denot_SOff0; ewpeel; exact E5|].
all: split; [sreg; first [reflexivity | rewrite sv_denot_SOff0; ewpeel; exact E6]|].
all: split; [sreg; first [reflexivity | rewrite sv_denot_SOff0; ewpeel; exact E7]|].
all: split; [sreg; first [reflexivity | rewrite sv_denot_SOff0; ewpeel; exact E28]|].
all: split; [sreg; reflexivity|].
all: split; [lia|].
all: split; [rewrite Z2Nat.inj_add by lia; exact Hin1|].
all: split; [unfold sg_len; exact Hf|].
all: split; [lia|].
all: split; [rewrite length_app; cbn [length]; lia|].
all: split;
  [ apply sc_garr8_snoc;
    [ apply (sc_garr8_kept (mrestrict (w_H (sg_W g)) mem2)); [|exact Hout];
      intros x Hx; apply (mbyte_of_aview tfibsegs); apply KE; lia
    | rewrite Hlen; exact Vv | exact Hv ] |].
all: rewrite Z2Nat.inj_add by lia; exact Hspec.
Time Qed.
End h.
End d.
