(* Part a of one pass of owed_counter_text's first loop in image B (owed_counter_text_B_l1_base.v), from the loop
   head 0x845d4: the check of t[i] (paid by its usable mark, s4 = q + i), lbu a0,1(s6); beq a0,s8 (a dot):
   - a dot with n = 0, or after a digit whose dot is set: the call of owed_seg7 with ' ' (0x84628 .. 0x84630);
   - a dot after a digit whose dot is clear: the UBSan checks of n - 1 (0x845fc, 0x84608), the check of dot[n - 1],
     dot[n - 1] := 1 (0x846bc .. 0x846cc), s6, s4 one on and the UBSan check of s6 (0x846a8 .. 0x846b4), back to the
     head;
   - 0: the text's end 0x84728;
   - any other byte: the call of owed_seg7 with the byte.
   The run writes dot[n - 1] only. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_text codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CPgWalkU CPgWalkKeptU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkFrameU CPgWalkCallU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import owed_counter_text_B_inv owed_counter_text_B_s0_a.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import owed_counter_text_B_s0 owed_counter_text_B_l1_base.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import owed_counter_text_B_l1_e.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0l.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YO0b YO0c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* blez s3 (bge zero,s3) on 0 <= n <= 8 *)
Lemma oca_bge0 : forall E k n, ew E k = Z_to_bv 64 n -> 0 <= n <= 8 ->
  branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E (SOff k 0)) = (n <=? 0).
Proof.
intros E k n Hk Hn. rewrite YO0c.branch_ge.
change (bv_unsigned (sv_denot E (SLit 0))) with (U E (SLit 0)). change (bv_unsigned (sv_denot E (SOff k 0))) with (U E (SOff k 0)).
rewrite U_lit, (U_atom E k n Hk) by lia. rewrite !YO0b.s64_small by lia.
destruct (Z.leb_spec n 0); destruct (Z.ltb_spec 0 n); cbn; try reflexivity; lia.
Qed.
Ltac awr_ro := cbn [ss_mem]; repeat first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|] ].
Ltac kwr_ro := let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a (r & Hr & Hb); cbv beta;
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; exfalso; lia | ]); destruct Hr.

Ltac hE34 := lazymatch goal with H : ew _ 34 = Z_to_bv 64 _ |- _ => rewrite H end.
Ltac hE34_in Hb := lazymatch goal with H : ew _ 34 = Z_to_bv 64 _ |- _ => rewrite H in Hb end.
Ltac hEfa := lazymatch goal with H : forall c p, frame_addr ?l c p = frame_addr _ c p |- context [frame_addr ?l _ _] =>
  rewrite H end.
Ltac hFa := lazymatch goal with H : frame_addr _ 1 _ = _ |- _ => rewrite H end.
(* the write window of dot[n - 1] (atom 34, F + 60 + 4 n) is the walk's own frame *)
Ltac awr_dp :=
  cbn [ss_mem];
  lazymatch goal with |- awr_ok ?Ev ?rs _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply awr_ok_cons_gen;
    [ reflexivity | ewpeel; hE34; apply unsigned_lit_small; lia
    | let a := fresh "a" in let Ha := fresh "Ha" in
      intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; exists 1; eexists; split; [left; reflexivity|];
      left; unfold in_zr; cbn [fst snd]; hEfa; change (fs_frame_bytes 1) with 128; hFa; lia
    | ] ].
Ltac kwr_dp :=
  let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a (r & Hr & Hb); cbv beta;
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  repeat (destruct Hr as [<- | Hr];
          [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; ewpeel_in Hb;
            first [ exfalso; lia | hE34_in Hb; rewrite unsigned_lit_small in Hb by lia; lia ] | ]);
  destruct Hr.

Ltac oc_kregs_tac := unfold oc_kregs; repeat split; rv0; rewrite ?sv_denot_SOff0; ewpeel;
  first [ lazymatch goal with EW : forall k r, _ -> ew _ k = getr ?rr r |- _ = getr ?rr _ => apply EW; reflexivity end
        | lazymatch goal with E32 : ew _ 32 = Z_to_bv 64 SB, R23 : getr ?rr 23 = w64 SB |- _ = getr ?rr 23 =>
            rewrite E32, R23; reflexivity end
        | lazymatch goal with R24 : getr ?rr 24 = w64 46 |- _ = getr ?rr 24 => rewrite R24; reflexivity end ].
Ltac reg_atom E := rv0; rewrite ?sv_denot_SOff0; ewpeel; exact E.
Ltac reg_off E v c := rv0; rewrite denot_lit_U, (U_atom_off _ _ v c) by (first [ewpeel; exact E | lia]); unfold w64; f_equal; lia.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables RLO RHI GLYPHA : Z.
Variable ROSTRS : list (Z * Z).
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.

Theorem oc_part_a_holds : oc_part_a B MT RLO RHI GLYPHA ROSTRS.
Proof.
unfold oc_part_a. intros g pos fuel W2 c2 Hpre Hnow Hc.
destruct Hc as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HK & HP & Hni & Hio & Hmo & HC & HL).
destruct HL as (i & n & s & dot & R19 & R20 & R22 & Hi & Hfuel & Hnz & Hct1 & Hl1 & Harr & Hsj & Hdj).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (ocl_stack B g Hpre) as (Hceil & H47 & H46 & Hal & Hsp1 & Hsp1a & Hwin & Hsp0).
destruct (ocl_frame B LAWS g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (Hfr & Efa & Efl & HF0 & HFc & HF64 & HFapp & HFp).
pose proof HC as (R8 & R2 & R9 & R3 & R4 & R23 & R26 & R18 & R21 & R24 & R27 & _).
pose proof Hpre as (_ & _ & (Hq0 & _ & Hin0 & (_ & Hqn & _ & _ & _ & Hqam & _)) & _).
pose proof (Hnow pos ly2 S2 W2 mem2 md2 HJ HK HP Hni) as ((Htb & Htra) & _).
pose proof Hl1 as ((Hn0 & Hdl & Hdz) & Hd01 & Hsl & Hs128).
assert (Hil : i < og_len g) by (unfold og_len; exact (ocl_tb_len (og_tb g) i Hi Hin0 Hnz)).
unfold og_len in Hil, Hqn, Hqam.
assert (Hq47 : og_q g + Z.of_nat (length (og_tb g)) <= 2 ^ 47 - 1)
  by (unfold amem_range in Hqam; rewrite ?C3, ?C4, ?C5 in Hqam; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hqam; lia).
set (ch := nth (Z.to_nat i) (og_tb g) 0).
pose proof (Htb (Z.to_nat i) ltac:(lia)) as (Vch & Hch8). fold ch in Vch, Hch8.
rewrite Z2Nat.id in Vch by lia.
set (F := og_F g pos) in *.
assert (HFa : frame_addr (og_lyc g) 1 pos = F) by reflexivity.
assert (HF8 : F = 8 * (F / 8)).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. pose proof (Z.div_mod F 8 ltac:(lia)) as D8.
  pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M8. lia. }
pose proof alloc_ceiling_val as Hac.
set (dv := nth (Z.to_nat (n - 1)) dot 0).
assert (Hdv : 0 <= dv <= 1).
{ destruct (Z_lt_le_dec 0 n) as [Hn | Hn].
  - apply (nth_Forall (fun x => 0 <= x <= 1)); [exact Hd01 | lia].
  - unfold dv. replace (Z.to_nat (n - 1)) with 0%nat by lia. destruct dot as [|d0 dt']; [cbn; lia|].
    inversion Hd01; subst; cbn; lia. }
set (xs := [ch; F + 60 + 4 * n; dv]).
remember (Ereg regs2 (cw_extra xs)) as E eqn:HEE.
assert (EW : forall (k : nat) (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs2 r)
  by (intros k r Hk; subst E; exact (ew_Ereg_nat regs2 _ k r Hk)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
assert (E33 : ew E 33 = Z_to_bv 64 ch) by (subst E; exact (cw_ew_x regs2 xs 0)).
assert (E34 : ew E 34 = Z_to_bv 64 (F + 60 + 4 * n)) by (subst E; exact (cw_ew_x regs2 xs 1)).
assert (E35 : ew E 35 = Z_to_bv 64 dv) by (subst E; exact (cw_ew_x regs2 xs 2)).
assert (E19 : ew E 19 = w64 n) by (rewrite (EW 19%nat 19%bv eq_refl); exact R19).
assert (E20 : ew E 20 = w64 (og_q g + i)) by (rewrite (EW 20%nat 20%bv eq_refl); exact R20).
assert (E22 : ew E 22 = w64 (og_q g + i - 1)) by (rewrite (EW 22%nat 22%bv eq_refl); exact R22).
assert (E21 : ew E 21 = w64 (F + 64)) by (rewrite (EW 21%nat 21%bv eq_refl); exact R21).
assert (E27 : ew E 27 = w64 (onot (F + 64))) by (rewrite (EW 27%nat 27%bv eq_refl); exact R27).
assert (U22 : bv_unsigned (ew E 22) = og_q g + i - 1) by (rewrite E22; unfold w64; apply unsigned_lit_small; lia).
assert (YS : st_ok tfibsegs E
  (mkSS PC_L1 sr_atoms [YP09.mkRegion (Some 22%nat) 1 2 1 1 [YP09.mkChunk 1 (CVal 1 (SOff 33 0))]] None
     (mkFacts [(32%nat, mkAF SB SB 0); (19%nat, mkAF 0 8 0); (20%nat, mkAF 1 (2 ^ 47 - 2) 0);
               (22%nat, mkAF 0 (2 ^ 47 - 3) 0); (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 (2 ^ 47 - 8) 0);
               (35%nat, mkAF 0 1 0)] [] []))
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 PC_L1) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U22. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val tfibsegs _ _ (og_q g + i - 1) 1 1 (SOff 33 0) ch);
    [rewrite sv_denot_SOff0; exact E33 | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia |].
    replace (og_q g + i - 1 + 1) with (og_q g + i) by lia. exact Vch.
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E32, E19, E20, E22, E33, E34, E35. unfold w64. rewrite !unsigned_lit_small by (unfold SB; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat split; first [exact I | lia]. }
pose proof (ast_ok_set_reg_fp tfibsegs E _ _ (23%bv : bv 5) (SOff 32 0) YS eq_refl
  ltac:(cbn [ms_regs restrict mkst]; rewrite sv_denot_SOff0, E32, R23; reflexivity)) as HS.
clear YS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
pose proof (ast_ok_set_reg_fp tfibsegs E _ _ (24%bv : bv 5) (SLit 46) HS eq_refl
  ltac:(cbn [ms_regs restrict mkst]; rewrite R24; reflexivity)) as YS.
clear HS. rename YS into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
assert (SHOK : sh_ok tfibsegs CW_Bx [mkSHE 20 0 1] E (mrestrict (w_H W2) mem2)).
{ apply Forall_cons; [|apply Forall_nil].
  apply (cw_shent_ra W2 mem2 E 20 (og_q g + i) 1); [| | lia | lia | lia | exact E20 | exact E32].
  - eapply range_addressable_sub; [exact Htra | lia | unfold og_len; lia].
  - unfold amem_range. rewrite ?C3, ?C4, ?C5. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *.
    unfold amem_range in Hqam. rewrite ?C3, ?C4, ?C5 in Hqam. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hqam. lia. }
cw_keep_j0 HJ HJ0.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a)
  by (intros; reflexivity).
assert (KP : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem2 a) by (intros; assumption).
unfold cfg_at. change (w64 PC_L1) with (Z_to_bv 64 PC_L1).
cw_run_to awr_ro B_OSEG7. ctk_keep kwr_ro.
(* beq a0,s8 (0x845e8): t[i] is a dot *)
cw_branch Hc1.
all: rewrite branch_eq_U, (U_atom _ 33 ch) in Hc1 by (first [ewpeel; exact E33 | lia]); rewrite U_lit in Hc1 by lia.
- (* a dot: blez s3 *)
  apply Z.eqb_eq in Hc1.
  cw_run_to awr_ro B_OSEG7. ctk_keep kwr_ro.
  cw_branch Hc2.
  all: rewrite (oca_bge0 _ 19 n) in Hc2 by (first [ewpeel; exact E19 | lia]).
  + (* n <= 0: the dot draws as ' ' *)
    apply Z.leb_le in Hc2.
    cw_run_to awr_ro B_OSEG7. ctk_keep kwr_ro.
    apply SRr_ret. cbv beta. right; left.
    lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
      apply (ocl_cut_close B MT LAWS g pos B_OSEG7 (P_C g pos fuel) ly2 S2 regs2 mem2 md2 W2 msv _ Hpre HJ0 HK HP Hni Hio Hmo HC HJ);
      [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl) | oc_kregs_tac
      | intros a Ha _; apply KE; [exact Ha | tauto] | exact KP | exact Hsj | exact Hdj | ] end.
    intros Ksj Kdj.
    exists i, n, ch, s, dot.
    split; [rv0; reflexivity|]. split; [rv0; unfold oc_c; rewrite Hc1; reflexivity|].
    split; [reg_atom E19|]. split; [reg_atom E20|]. split; [reg_atom E22|].
    split; [rv0; unfold w64; apply (oc_den_sh _ 20 (og_q g + i)); [ewpeel; exact E20 | ewpeel; exact E32 | lia]|].
    split; [exact Hi|]. split; [exact Hfuel|]. split; [reflexivity|]. split; [rewrite Hc1; discriminate|]. split; [exact Hnz|].
    split; [exact Hct1|]. split; [intros (_ & Hn' & _); lia|]. split; [exact Hl1|].
    split; [|split; [exact Ksj | exact Kdj]].
    apply (ocl_arrays_kept g pos W2 W2 mem2 _ n s dot); [intros a Ha; apply KE; [lia | tauto] | lia | exact Harr].
  + (* n > 0: the UBSan checks of n - 1 *)
    apply Z.leb_gt in Hc2.
    cw_run_to awr_ro 0x84610. ctk_keep kwr_ro.
    (* bltu s11,a1 (0x84608): ~(F + 64) against 4 n - 4 *)
    cw_branch Hc4.
    all: rewrite branch_ltu_U, (U_atom _ 27 (onot (F + 64))), (cw_U_m4 _ 19 n) in Hc4
           by (first [ewpeel; first [exact E27 | exact E19] | unfold onot; lia | lia]).
    * exfalso. apply Z.ltb_lt in Hc4. unfold onot in Hc4. lia.
    * cw_run_to awr_ro 0x84610. ctk_keep kwr_ro.
      (* a1 = F + 60 + 4 n, the address of dot[n - 1]: pinned to atom 34; the text byte's region dropped *)
      lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict ?Hh ?msv) |- _ =>
        pose proof (ast_ok_set_reg_fp tfibsegs Ev ssv (restrict Hh msv) (11%bv : bv 5) (SOff 34 0) HS eq_refl
          ltac:(cbn [ms_regs restrict]; rv0; rewrite sv_denot_SOff0; ewpeel; rewrite E34; symmetry;
                replace (F + 60 + 4 * n) with ((F + 64) - 4 + 4 * n) by lia;
                apply (cw_den_dot Ev 21 19 (F + 64) n); [ewpeel; exact E21 | ewpeel; exact E19 | lia | lia | lia]))
          as YS end.
      clear HS. rename YS into HS. norm_ss HS.
      lazymatch goal with HS : st_ok _ ?Ex ?ssx ?msx |- _ =>
        pose proof (st_ok_submem tfibsegs Ex ssx msx [] HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity))
          as YS end.
      clear HS. rename YS into HS. norm_ss HS.
      pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        _ & _ & _ & _ & _ & _ & _ & Hsh).
      lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
        assert (Hsh1 : garr8 tfibsegs (mrestrict (w_H W2) (ms_mem msv)) (SB + F / 8) OC_FRAME_SHADOW)
          by (apply (ocl_garr8_kept (w_H W2) (w_H W2) mem2 (ms_mem msv)); [|exact Hsh];
              intros x Hx; apply KE; [unfold SB in *; cbn [length OC_FRAME_SHADOW] in Hx; lia | tauto]);
        assert (Vdp : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem msv)) (F + 60 + 4 * n) 4 dv)
          by (apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 (ms_mem msv)); [intros x Hx; apply KE; [lia | tauto]|];
              replace (F + 60 + 4 * n) with (F + 64 + 4 * (n - 1)) by lia; exact (proj1 Harr (n - 1) ltac:(lia)));
        assert (Hdp_ok : region_ok tfibsegs Ev (mrestrict (w_H W2) (ms_mem msv))
            (YP09.mkRegion (Some 34%nat) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 35 0))]))
          by (unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
              ewpeel; rewrite E34, unsigned_lit_small by lia;
              split; [lia|]; split; [lia|]; split;
              [ intros o Ho; apply (YCbq.apresent_writable tfibsegs); apply KP; apply HFp; lia
              | apply Forall_cons; [|apply Forall_nil];
                apply (chunk_ok_val tfibsegs Ev _ (F + 60 + 4 * n) 0 4 (SOff 35 0) dv);
                [ rewrite sv_denot_SOff0; ewpeel; exact E35 | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vdp ] ]);
        pose proof (ast_ok_add_region tfibsegs Ev ssv (restrict (w_H W2) msv)
          (YP09.mkRegion (Some 34%nat) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 35 0))]) HS eq_refl Hdp_ok I) as YS;
        clear HS; rename YS into HS; norm_ss HS;
        assert (SHOK2 : sh_ok tfibsegs CW_Bx [mkSHE 20 0 1; mkSHE 34 0 4] Ev (mrestrict (w_H W2) (ms_mem msv)))
          by (unfold sh_ok in SHOK |- *; apply Forall_cons; [exact (Forall_inv SHOK)|];
              apply Forall_cons; [|apply Forall_nil];
              apply (cw_shent_ra W2 (ms_mem msv) Ev 34 (F + 60 + 4 * n) 4);
              [ replace (F + 60 + 4 * n) with (F + (60 + 4 * n)) by lia;
                apply ocl_ra_var; [rewrite HF8, Z.mul_comm; apply Z_mod_mult | lia | right; lia | exact Hsh1]
              | unfold amem_range, in_app, kLowShadowBeg, ASAN_CEIL in *; rewrite ?C3, ?C4, ?C5 in *;
                unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia
              | lia | lia | lia | ewpeel; exact E34 | ewpeel; exact E32 ]);
        clear SHOK; rename SHOK2 into SHOK;
        assert (KE' : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 60 + 4 * n <= a < F + 64 + 4 * n) ->
          aview tfibsegs (w_H W2) (ms_mem msv) a = aview tfibsegs (w_H W2) mem2 a)
          by (intros a Ha _; apply KE; [exact Ha | tauto]) end.
      clear KE. rename KE' into KE.
      cw_run_to awr_dp B_OSEG7. ctk_keep kwr_dp.
      (* beqz a3 (0x84624): dot[n - 1] *)
      cw_branch Hc5.
      all: rewrite branch_eq_U, (U_atom _ 35 dv) in Hc5 by (first [ewpeel; exact E35 | lia]); rewrite U_lit in Hc5 by lia.
      -- (* clear: dot[n - 1] := 1 and the next byte *)
         apply Z.eqb_eq in Hc5.
         cw_run_to awr_dp PC_L1. ctk_keep kwr_dp.
         lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
           let ix := oc_ridx HS 34%nat in
           pose proof (st_ok_region_nth Ev ssv (restrict (w_H W2) msv) ix _ HS eq_refl) as HR end.
         cbn [ms_mem restrict] in HR.
         lazymatch type of HR with region_ok _ _ _ ?rg => let rg' := eval vm_compute in rg in change rg with rg' in HR end.
         pose proof (field_of_region _ _ 34 (F + 60 + 4 * n) _ _ _ _ _ 0 4%N (SLit 1) 1 HR
           ltac:(ewpeel; rewrite E34; apply unsigned_lit_small; lia) ltac:(oc_in) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew.
         rewrite Z.add_0_r in Vnew. change (N.to_nat 4) with 4%nat in Vnew.
         assert (Hct1' : ct1_owe (skipn (Z.to_nat (i + 1)) (og_tb g)) n s (upd_at dot (n - 1) 1) =
                         ct1_owe (og_tb g) 0 [] (repeat 0 8)).
         { rewrite <- Hct1, (skipn_cons_nth (og_tb g) (Z.to_nat i) 0) by lia. fold ch. rewrite Hc1.
           replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. symmetry. apply ocl_ct1_dotset; [lia | exact Hc5]. }
         apply SRr_ret. cbv beta. left.
    lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
      apply (ocl_cut_close B MT LAWS g pos PC_L1 (P_L1 g pos fuel) ly2 S2 regs2 mem2 md2 W2 msv _ Hpre HJ0 HK HP Hni Hio Hmo HC HJ);
      [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl) | oc_kregs_tac
      | intros a Ha Hz; apply KE; [exact Ha | intros Hd; apply Hz; unfold oc_zv; lia] | exact KP | exact Hsj | exact Hdj | ] end.
    intros Ksj Kdj.
         exists (i + 1), n, s, (upd_at dot (n - 1) 1).
         split; [reg_atom E19|]. split; [reg_off E20 (og_q g + i) 1|]. split; [reg_off E22 (og_q g + i - 1) 1|].
         split; [lia|]. split; [unfold og_len in *; lia|].
         split; [replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia;
                 rewrite (ocl_firstn_S (og_tb g) (Z.to_nat i)) by lia; apply Forall_app; split;
                 [exact Hnz | constructor; [fold ch; rewrite Hc1; discriminate | constructor]]|].
         split; [exact Hct1'|].
         split; [split; [exact (ct_inv_dot n dot (conj Hn0 (conj Hdl Hdz)) ltac:(lia))|];
                 split; [apply ocl_Forall_upd_at; [exact Hd01 | lia]|]; split; [exact Hsl | exact Hs128]|].
         split; [|split; [exact Ksj | exact Kdj]].
         apply (ocl_arrays_word g pos W2 mem2 _ n s dot 1); [lia | exact Hdl | | exact Vnew | exact Harr].
         intros a Ha Hz. apply KE; [lia | exact Hz].
      -- (* set: the dot draws as ' ' *)
         apply Z.eqb_neq in Hc5.
         cw_run_to awr_dp B_OSEG7. ctk_keep kwr_dp.
         lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
           let ix := oc_ridx HS 34%nat in
           pose proof (st_ok_region_nth Ev ssv (restrict (w_H W2) msv) ix _ HS eq_refl) as HR end.
         cbn [ms_mem restrict] in HR.
         lazymatch type of HR with region_ok _ _ _ ?rg => let rg' := eval vm_compute in rg in change rg with rg' in HR end.
         pose proof (field_of_region _ _ 34 (F + 60 + 4 * n) _ _ _ _ _ 0 4%N (SOff 35 0) dv HR
           ltac:(ewpeel; rewrite E34; apply unsigned_lit_small; lia) ltac:(oc_in)
           ltac:(rewrite sv_denot_SOff0; ewpeel; exact E35) ltac:(cbn; lia) ltac:(cbn; lia)) as Vold.
         rewrite Z.add_0_r in Vold. change (N.to_nat 4) with 4%nat in Vold.
         apply SRr_ret. cbv beta. right; left.
    lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
      apply (ocl_cut_close B MT LAWS g pos B_OSEG7 (P_C g pos fuel) ly2 S2 regs2 mem2 md2 W2 msv _ Hpre HJ0 HK HP Hni Hio Hmo HC HJ);
      [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl) | oc_kregs_tac
      | intros a Ha Hz; apply KE; [exact Ha | intros Hd; apply Hz; unfold oc_zv; lia] | exact KP | exact Hsj | exact Hdj | ] end.
    intros Ksj Kdj.
         exists i, n, ch, s, dot.
    split; [rv0; reflexivity|]. split; [rv0; unfold oc_c; rewrite Hc1; reflexivity|].
    split; [reg_atom E19|]. split; [reg_atom E20|]. split; [reg_atom E22|].
    split; [rv0; unfold w64; apply (oc_den_sh _ 20 (og_q g + i)); [ewpeel; exact E20 | ewpeel; exact E32 | lia]|].
    split; [exact Hi|]. split; [exact Hfuel|]. split; [reflexivity|]. split; [rewrite Hc1; discriminate|]. split; [exact Hnz|].
    split; [exact Hct1|]. split; [intros (_ & _ & Hd0); exact (Hc5 Hd0)|]. split; [exact Hl1|].
    split; [|split; [exact Ksj | exact Kdj]].
         assert (Hu : upd_at dot (n - 1) dv = dot) by (unfold dv; apply upd_same; lia).
         rewrite <- Hu.
         apply (ocl_arrays_word g pos W2 mem2 _ n s dot dv); [lia | exact Hdl | | exact Vold | exact Harr].
         intros a Ha Hz. apply KE; [lia | exact Hz].
- (* not a dot: beqz a0 *)
  apply Z.eqb_neq in Hc1.
  cw_run_to awr_ro PC_E. ctk_keep kwr_ro.
  cw_branch Hc2.
  all: rewrite branch_eq_U, (U_atom _ 33 ch) in Hc2 by (first [ewpeel; exact E33 | lia]); rewrite U_lit in Hc2 by lia.
  + (* 0: the text's end *)
    apply Z.eqb_eq in Hc2.
    cw_run_to awr_ro PC_E. ctk_keep kwr_ro.
    apply SRr_ret. cbv beta. right; right.
    lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
      apply (ocl_cut_close B MT LAWS g pos PC_E (P_E g pos) ly2 S2 regs2 mem2 md2 W2 msv _ Hpre HJ0 HK HP Hni Hio Hmo HC HJ);
      [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl) | oc_kregs_tac
      | intros a Ha _; apply KE; [exact Ha | tauto] | exact KP | exact Hsj | exact Hdj | ] end.
    intros Ksj Kdj.
    exists n, s, dot.
    split; [reg_atom E19|].
    split; [unfold owed_counter_text_spec; rewrite <- Hct1, (skipn_cons_nth (og_tb g) (Z.to_nat i) 0) by lia;
            fold ch; rewrite Hc2; reflexivity|].
    split; [exact Hl1|]. split; [|split; [exact Ksj | exact Kdj]].
    apply (ocl_arrays_kept g pos W2 W2 mem2 _ n s dot); [intros a Ha; apply KE; [lia | tauto] | lia | exact Harr].
  + (* another byte: the call *)
    apply Z.eqb_neq in Hc2.
    cw_run_to awr_ro B_OSEG7. ctk_keep kwr_ro.
    apply SRr_ret. cbv beta. right; left.
    lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
      apply (ocl_cut_close B MT LAWS g pos B_OSEG7 (P_C g pos fuel) ly2 S2 regs2 mem2 md2 W2 msv _ Hpre HJ0 HK HP Hni Hio Hmo HC HJ);
      [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl) | oc_kregs_tac
      | intros a Ha _; apply KE; [exact Ha | tauto] | exact KP | exact Hsj | exact Hdj | ] end.
    intros Ksj Kdj.
    exists i, n, ch, s, dot.
    split; [rv0; reflexivity|]. split; [rv0; rewrite sv_denot_SOff0; ewpeel; rewrite E33; unfold oc_c; rewrite (proj2 (Z.eqb_neq ch 46) Hc1); reflexivity|].
    split; [reg_atom E19|]. split; [reg_atom E20|]. split; [reg_atom E22|].
    split; [rv0; unfold w64; apply (oc_den_sh _ 20 (og_q g + i)); [ewpeel; exact E20 | ewpeel; exact E32 | lia]|].
    split; [exact Hi|]. split; [exact Hfuel|]. split; [reflexivity|]. split; [exact Hc2|]. split; [exact Hnz|].
    split; [exact Hct1|]. split; [intros (Hx & _); exact (Hc1 Hx)|]. split; [exact Hl1|].
    split; [|split; [exact Ksj | exact Kdj]].
    apply (ocl_arrays_kept g pos W2 W2 mem2 _ n s dot); [intros a Ha; apply KE; [lia | tauto] | lia | exact Harr].
Qed.
End d.
