(* diginet_scribble_text in image A (fuzz_codec.asan, 0x85cc4): the segment S0 of diginet_scribble_text_A_inv.v --
   the entry 0x85cc4 to the loop head 0x85d1c or the padding 0x85de0 (sc_seg_S0).

   The code: sp -= 16, ra at sp + 8, s0 at sp; o = 0 (to 0x85dd0) and q = 0 (to 0x85dd8) are not taken (the
   contract gives 0 < o and 0 < q); a3 := the 8-byte cell at 0x9db10, a4 := its contents, the shadow offset; the
   instrumented check of q at 0x85cec; t1 := q[0]; s0 := 0, a5 := 0; t1 = 0 (to 0x85de0), n = 0 (to 0x85de0), else
   a6 := q + 1, a7 := 46, t0 := 8 and the loop head. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0m.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YCeo.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YC85.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgChkC CPgWalk.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import diginet_scribble_text_A_inv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the text's first byte, in atom 33 *)
Definition s0_xs (g : sc_ctx) : list Z := [nth 0 (sg_tb g) 0].
(* q, o and n, as the branches at 0x85cd0, 0x85cd4 and 0x85d04 read them *)
Definition s0_AF (g : sc_ctx) : list (nat * afact) :=
[(10%nat, mkAF 1 (2 ^ 47 - 1) 0); (11%nat, mkAF 1 (2 ^ 47 - 1) 0); (12%nat, mkAF 0 4294967295 0);
 (33%nat, mkAF 0 255 0)].
(* the text's first byte, a one-byte region at q *)
Definition s0_rtx : YP09.region := YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].

Ltac ewpeel := repeat (first [ rewrite ew_havoc_old by nat_side | rewrite ew_ewset_other by nat_side ]).
Ltac sreg := lazymatch goal with HS : st_ok ?segs ?Ev ?ss (restrict ?H ?msv) |- context [getr (ms_regs ?msv) ?r] =>
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in
  let R := fresh "R" in
  assert (R : getr (ms_regs msv) r = sv_denot Ev e)
    by (refine (eq_trans (st_ok_restrict_reg segs H Ev ss msv r HS) _); reflexivity);
  rewrite R; clear R end.
Ltac skeep := sreg; rewrite sv_denot_SOff0; ewpeel;
  lazymatch goal with EE : forall n (rr : bv 5), _ -> ew ?Ev n = _ |- _ => apply EE; reflexivity end.
(* a register the walk set to a literal *)
Ltac slit := sreg; reflexivity.
(* a register that still holds an atom of the entry *)
Ltac sval H := sreg; rewrite sv_denot_SOff0; ewpeel; exact H.
(* the model's input and output across the runs of this segment *)
(* the two saves of the prologue, read off the frame's region at the current state *)
Ltac s0_save gg :=
lazymatch goal with HSv : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
  let HRg := fresh "HRg" in
  pose proof (st_ok_region_nth Ev ssv (restrict (w_H (sg_W gg)) msv) 1%nat _ HSv eq_refl) as HRg;
  assert (Vs0 : val_mem tfibsegs (mrestrict (w_H (sg_W gg)) (ms_mem msv)) (spZ (sg_regs gg) - 16) 8
                  (bv_unsigned (getr (sg_regs gg) 8)));
  [ replace (spZ (sg_regs gg) - 16) with (spZ (sg_regs gg) + -16) by lia;
    apply (field_of_region Ev _ 2%nat (spZ (sg_regs gg)) [YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))] (-16) 0 (-16) 0 (-16) 8 (SOff 8 0));
    [ exact HRg | ewpeel; lazymatch goal with B2v : bv_unsigned (ew _ 2) = _ |- _ => exact B2v end | cbn [YP09.r_chunks In]; first [left; reflexivity | right; left; reflexivity]
    | cbn [sv_denot]; ewpeel;
      lazymatch goal with EEv : forall n (rr : bv 5), _ -> ew _ n = _ |- _ => rewrite (EEv 8%nat 8%bv eq_refl) end;
      rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (8 * Z.of_N 8) with 64; apply sc_u64 | cbn; lia ] | ];
  assert (Vra : val_mem tfibsegs (mrestrict (w_H (sg_W gg)) (ms_mem msv)) (spZ (sg_regs gg) - 8) 8
                  (raZ (sg_regs gg)));
  [ replace (spZ (sg_regs gg) - 8) with (spZ (sg_regs gg) + -8) by lia;
    apply (field_of_region Ev _ 2%nat (spZ (sg_regs gg)) [YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))] (-16) 0 (-16) 0 (-8) 8 (SOff 1 0));
    [ exact HRg | ewpeel; lazymatch goal with B2v : bv_unsigned (ew _ 2) = _ |- _ => exact B2v end | cbn [YP09.r_chunks In]; first [left; reflexivity | right; left; reflexivity]
    | cbn [sv_denot]; ewpeel;
      lazymatch goal with E1v : ew _ 1 = getr _ 1 |- _ => rewrite E1v end;
      rewrite Z.add_0_r; unfold raZ; reflexivity
    | change (8 * Z.of_N 8) with 64; apply sc_u64 | cbn; lia ] | ]
end.
Ltac s0_cfg := lazymatch goal with HSv : st_ok _ _ _ (restrict _ _) |- _ =>
  norm_ss HSv; unfold cfg_at, w64; cbv [PC_P PC_H];
  let Hms := fresh "Hms" in
  pose proof (st_ok_restrict_mkst tfibsegs _ _ _ _ HSv eq_refl) as Hms; cbn [ss_pc] in Hms;
  rewrite <- Hms; reflexivity end.
Ltac s0_common gg :=
  split; [ unfold sc_kregs; repeat (apply Forall_cons; [cbv beta; skeep|]); apply Forall_nil
  | split; [ unfold sg_sp; sreg; rewrite denot_lit_U; unfold w64; f_equal;
             lazymatch goal with |- U ?Ev _ = _ =>
               rewrite (cw_U_offx Ev 2 (spZ (sg_regs gg)) (-16)
                 ltac:(ewpeel; lazymatch goal with EEv : forall n (rr : bv 5), _ -> ew _ n = _ |- _ =>
                 rewrite (EEv 2%nat 2%bv eq_refl) end; unfold spZ; symmetry;
                 apply Z_to_bv_bv_unsigned) ltac:(unfold spZ; apply sc_u64)) end;
             rewrite Z.mod_small by lia; f_equal; lia
  | split; [ unfold sg_sp; assumption
  | split; [ unfold sg_sp; assumption
  | split; [ intros aa Haa Hzz;
             lazymatch goal with KEv : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
               apply KEv; [exact Haa | unfold sc_zone, sg_sp, T_scribble_text, ESTACK in Hzz; lia] end
           | lazymatch goal with KPv : forall a, apresent _ _ a -> apresent _ _ a |- _ => exact KPv end
           ]]]]].
Ltac s0_io := let rec kio := first [assumption | apply same_io_refl
  | eapply same_io_trans; [| apply cw_same_io_wvb]; kio
  | eapply same_io_trans; [| apply same_io_materialized; eassumption]; kio] in kio.

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
pose proof Hpre as (HE & H10 & HSTR & H11 & H12 & (Hn32 & Hnl) & HDST & HOJ & HDJ).
pose proof HE as (HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwin & Hwhi & Hev & Hlive).
cw_keep_j0 HJ HJ0.
destruct (sc_stack B g Hpre) as (Hceil & H47 & H46 & Hal & Hwin2 & Hsp0 & Hprs).
destruct (sc_text B g Hpre) as (Hq0 & Hql & Hin0 & Hlen0 & HGT & HRAq & Hamq & Hoffq).
destruct (sc_out B g Hpre) as (Ho0 & Hon & Hn & Hoff & HTD & HTW & HRAo & Hhull & Hamo & _).
pose proof (sc_amem47 (sg_q g) (sg_len g) ltac:(lia) ltac:(lia) Hamq) as Hq47.
pose proof (sc_amem47 (sg_o g) (sg_n g) ltac:(lia) ltac:(lia) Hamo) as Ho47.
unfold sg_sp, sg_len in *. unfold T_scribble_text, ESTACK in *.
pose proof HSTR as (_ & _ & _ & Hcrd). pose proof Hcrd as (_ & _ & _ & _ & _ & _ & Hcw).
unfold coff_win, T_scribble_text, ESTACK in Hcw.
destruct (HGT 0%nat ltac:(lia)) as (Hb0v & Hb0r).
set (b0 := nth 0 (sg_tb g) 0) in *.
(* ---- the entry state ---- *)
assert (X33 : ew (Ereg (sg_regs g) (cw_extra (s0_xs g))) 33 = Z_to_bv 64 b0)
  by exact (cw_ew_x (sg_regs g) (s0_xs g) 0).
assert (HAF : atoms_ok (Ereg (sg_regs g) (cw_extra (s0_xs g))) (s0_AF g)).
{ unfold s0_AF. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite (ew_Ereg_nat (sg_regs g) _ 10 10%bv eq_refl), (ew_Ereg_nat (sg_regs g) _ 11 11%bv eq_refl),
          (ew_Ereg_nat (sg_regs g) _ 12 12%bv eq_refl), X33, H10, H11, H12.
  unfold w64. rewrite !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat split; lia. }
pose proof (cw_entry_base_af B TL LAWS A_ST 16 (s0_xs g) (s0_AF g) (sg_STK g) (sg_sp0 g) (sg_FP g) (sg_ly g)
  (sg_S g) (sg_W0 g) (sg_mem0 g) (sg_md0 g) (sg_own g) (sg_lyc g) (sg_Sc g) (sg_W g) (sg_memc g) (sg_mdc g)
  (sg_k g) (sg_regs g) (16 + 4096) HE ltac:(lia) ltac:(vm_compute; reflexivity) HAF) as HS.
remember (Ereg (sg_regs g) (cw_extra (s0_xs g))) as E eqn:HEE.
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr (sg_regs g) rr)
  by (intros nn rr Hnn; subst E; apply ew_Ereg_nat; exact Hnn).
assert (HAE : env_agree 32 (Ereg (sg_regs g) (cw_extra (s0_xs g))) E) by (subst E; apply env_agree_refl).
assert (E1 : ew E 1 = getr (sg_regs g) 1) by (apply EE; reflexivity).
assert (B2 : bv_unsigned (ew E 2) = spZ (sg_regs g)) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 (sg_q g)) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 (sg_o g)) by (rewrite (EE 11%nat 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 (sg_n g)) by (rewrite (EE 12%nat 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
assert (E33 : ew E 33 = Z_to_bv 64 b0) by (subst E; exact X33).
clear HEE X33.
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H (sg_W g)) (sg_memc g))) by apply Forall_nil.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (sg_regs g) - 16 <= a < spZ (sg_regs g)) ->
  aview tfibsegs (w_H (sg_W g)) (sg_memc g) a = aview tfibsegs (w_H (sg_W g)) (sg_memc g) a)
  by (intros; reflexivity).
assert (KP : forall a, apresent (w_H (sg_W g)) (sg_memc g) a -> apresent (w_H (sg_W g)) (sg_memc g) a)
  by (intros; assumption).
unfold cfg_at. change (w64 A_ST) with (Z_to_bv 64 A_ST).
(* ---- 0x85cc4-0x85ce0: the saves, the two tests, the shadow offset ---- *)
cw_run_to cw_awr_stk 0x85ce4.
lazymatch goal with HG : mem_grows (mrestrict ?H ?m1) (mrestrict ?H ?m2) |- _ =>
  let KQ := fresh "KQ" in
  assert (KQ : forall a, apresent H (sg_memc g) a -> apresent H m2 a)
    by (intros a Ha; eapply apresent_grows; [exact HG | exact (KP a Ha)]);
  clear KP; rename KQ into KP end.
cw_keep cw_kwr_stk.
cw_drop_gb.
(* ---- the text's first byte ---- *)
lazymatch goal with HSv : st_ok _ ?Ev ?ssv ?msv |- _ =>
  pose proof (ast_ok_add_region tfibsegs Ev ssv msv s0_rtx HSv eq_refl
    ltac:(unfold region_ok, s0_rtx;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
          rewrite E10, unsigned_lit_small by lia;
          split; [lia|]; split; [lia|]; split; [intros oo Hoo; lia|];
          apply Forall_cons; [|apply Forall_nil];
          apply (chunk_ok_val tfibsegs Ev _ (sg_q g) 0 1 (SOff 33 0) b0);
          [ cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | cbn; lia | cbn; lia |];
          rewrite Z.add_0_r;
          apply (sc_val_mem_kept (mrestrict (w_H (sg_W g)) (sg_memc g)));
          [ intros x Hx; apply (mbyte_of_aview tfibsegs); apply KE;
            [lia | intros Hzz; apply (Hoffq x ltac:(cbn in Hx; lia)); unfold sc_zone, sg_sp, T_scribble_text, ESTACK; left; lia]
          | pose proof (proj1 (sc_text_val B g (sg_memc g) Hpre ltac:(intros a Ha Hz; reflexivity) 0%nat ltac:(lia))) as Hv0;
            change (Z.of_nat 0) with 0 in Hv0; rewrite Z.add_0_r in Hv0; exact Hv0 ])
    ltac:(unfold s0_rtx;
          lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
            let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
          cbn [all_disjoint]; unfold extent_disjoint;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          ewpeel; rewrite E10, B2, unsigned_lit_small by lia; split; [lia | exact I])) as HS3;
  clear HSv; rename HS3 into HS; norm_ss HS end.
(* ---- 0x85ce4-0x85cfc: the check of q, t1 := q[0], s0 := 0, a5 := 0 ---- *)
cw_run_ob cw_awr_stk
  ltac:(idtac; rewrite (cw_U_atom0 _ 10 (sg_q g) ltac:(ewpeel; exact E10) ltac:(lia));
        apply (sc_obl_of (sg_W g) _ _ _ _ (sg_q g) (Z.of_nat (length (sg_tb g))));
        [ apply (sc_ra_kept B g _ Hpre);
          first [ intros aa Haa Hzz; apply KE;
                  [exact Haa | unfold sc_zone, sg_sp, T_scribble_text, ESTACK in Hzz; lia]
                | exact Hamq | exact HRAq | lia ]
        | ewpeel; exact E32 | lia | lia ]).
lazymatch goal with HG : mem_grows (mrestrict ?H ?m1) (mrestrict ?H ?m2) |- _ =>
  let KQ := fresh "KQ" in
  assert (KQ : forall a, apresent H (sg_memc g) a -> apresent H m2 a)
    by (intros a Ha; eapply apresent_grows; [exact HG | exact (KP a Ha)]);
  clear KP; rename KQ into KP end.
cw_keep cw_kwr_stk.
cw_branch Hb0.

all: rewrite branch_eq_U in Hb0;
     lazymatch type of Hb0 with context [U ?Ev (SOff 33 0)] =>
       rewrite (cw_U_atom0 Ev 33 b0 ltac:(ewpeel; exact E33) ltac:(lia)) in Hb0 end;
     rewrite U_SLit in Hb0; hc_prop Hb0; replace (zcanon 0) with 0 in Hb0 by reflexivity.
- (* the first text byte is 0: the padding, with no output byte written *)
  cw_run_to cw_awr_stk PC_P.
  lazymatch goal with HG : mem_grows (mrestrict ?H ?m1) (mrestrict ?H ?m2) |- _ =>
    let KQ := fresh "KQ" in
    assert (KQ : forall a, apresent H (sg_memc g) a -> apresent H m2 a)
      by (intros a Ha; eapply apresent_grows; [exact HG | exact (KP a Ha)]);
    clear KP; rename KQ into KP end.
  cw_keep cw_kwr_stk.
  apply SRr_ret. right.
  lazymatch goal with HSv : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
    split; [reflexivity|]; exists (ms_regs msv), (ms_mem msv); eexists end.
  split; [s0_cfg|].
  split; [eassumption|]. split; [s0_io|].
  split.
  { s0_save g. s0_common g. }
  exists 0, 0, []. cbn [length].
  split; [slit|]. split; [slit|]. split; [sval E11|]. split; [sval E12|].
  split; [lia|]. split; [lia|]. split; [reflexivity|].
  split; [intros jj Hjj; cbn in Hjj; lia|].
  assert (Htb : sg_tb g = b0 :: skipn 1 (sg_tb g))
    by (change b0 with (nth 0 (sg_tb g) 0);
        rewrite <- (sc_skipn_cons (sg_tb g) 0 0 ltac:(lia)); symmetry; apply skipn_O).
  unfold sc_res, scribble_text_spec. rewrite Htb at 1. rewrite Hb0, sc_lib_zero.
  cbn [app]. replace (Z.to_nat (sg_n g - 0)) with (Z.to_nat (sg_n g)) by lia. reflexivity.
- (* the first text byte is not 0: the test of n *)
  cw_run cw_awr_stk.
  lazymatch goal with HG : mem_grows (mrestrict ?H ?m1) (mrestrict ?H ?m2) |- _ =>
    let KQ := fresh "KQ" in
    assert (KQ : forall a, apresent H (sg_memc g) a -> apresent H m2 a)
      by (intros a Ha; eapply apresent_grows; [exact HG | exact (KP a Ha)]);
    clear KP; rename KQ into KP end.
  cw_keep cw_kwr_stk.
  cw_branch Hb1.
  all: rewrite branch_eq_U in Hb1;
       lazymatch type of Hb1 with context [U ?Ev (SOff 12 0)] =>
         rewrite (cw_U_atom0 Ev 12 (sg_n g) ltac:(ewpeel; exact E12) ltac:(lia)) in Hb1 end;
       rewrite U_SLit in Hb1; hc_prop Hb1; replace (zcanon 0) with 0 in Hb1 by reflexivity.
  + (* n = 0: the padding, with nothing to write *)
    cw_run_to cw_awr_stk PC_P.
    lazymatch goal with HG : mem_grows (mrestrict ?H ?m1) (mrestrict ?H ?m2) |- _ =>
        let KQ := fresh "KQ" in
        assert (KQ : forall a, apresent H (sg_memc g) a -> apresent H m2 a)
            by (intros a Ha; eapply apresent_grows; [exact HG | exact (KP a Ha)]);
        clear KP; rename KQ into KP end.
    cw_keep cw_kwr_stk.
    apply SRr_ret. right.
    lazymatch goal with HSv : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
      split; [reflexivity|]; exists (ms_regs msv), (ms_mem msv); eexists end.
    split; [s0_cfg|].
    split; [eassumption|]. split; [s0_io|].
    split.
    { s0_save g. s0_common g. }
    exists 0, 0, []. cbn [length].
    split; [slit|]. split; [slit|]. split; [sval E11|]. split; [sval E12|].
    split; [lia|]. split; [lia|]. split; [reflexivity|].
    split; [intros jj Hjj; cbn in Hjj; lia|].
    unfold sc_res, scribble_text_spec. rewrite Hb1. cbn [Z.to_nat]. rewrite sc_lib_0.
    cbn [app repeat]. reflexivity.
  + (* the loop head, with i = j = 0 *)
    cw_run_to cw_awr_stk PC_H.
    lazymatch goal with HG : mem_grows (mrestrict ?H ?m1) (mrestrict ?H ?m2) |- _ =>
      let KQ := fresh "KQ" in
      assert (KQ : forall a, apresent H (sg_memc g) a -> apresent H m2 a)
        by (intros a Ha; eapply apresent_grows; [exact HG | exact (KP a Ha)]);
      clear KP; rename KQ into KP end.
    cw_keep cw_kwr_stk.
    apply SRr_ret. left.
    lazymatch goal with HSv : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
      split; [reflexivity|]; exists (ms_regs msv), (ms_mem msv); eexists end.
    split; [s0_cfg|].
    split; [eassumption|]. split; [s0_io|].
    split.
    { s0_save g. s0_common g. }
    exists 0, 0, b0, []. cbn [length].
    split; [slit|]. split; [slit|]. split; [sval E33|].
    split.
    { split; [sval E10|]. split; [sval E11|]. split; [sval E12|].
      split; [sval E32|].
      split; [sreg; rewrite denot_lit_U; unfold w64; f_equal;
              lazymatch goal with |- U ?Ev _ = _ =>
                rewrite (cw_U_offx Ev 10 (sg_q g) 1 ltac:(ewpeel; exact E10) ltac:(lia)) end;
              rewrite Z.mod_small by lia; reflexivity|].
      split; slit. }
    split; [lia|]. split; [cbn [Z.to_nat]; reflexivity|]. split; [exact Hb0|].
    split; [cbn [Z.to_nat]; rewrite Nat.add_0_l;
            apply (sc_in0_S (sg_tb g) 0); [rewrite skipn_O; exact Hin0 | exact Hb0]|].
    split; [unfold sg_len; lia|].
    split; [lia|]. split; [reflexivity|].
    split; [intros jj Hjj; cbn in Hjj; lia|].
    cbn [Z.to_nat]. rewrite skipn_O. replace (sg_n g - 0) with (sg_n g) by lia.
    unfold sc_res, scribble_text_spec. cbn [app]. rewrite Z.add_0_l.
    apply surjective_pairing.
Time Qed.
End h.
End d.
