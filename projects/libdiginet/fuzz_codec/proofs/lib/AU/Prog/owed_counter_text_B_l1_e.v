(* Part e of owed_counter_text's first loop in image B (owed_counter_text_B_l1_base.v): from the text's end 0x84728,
   dt = 40(s1), the check of dt (paid by its usable mark), *dt := 0 (0x84748), a3 = a4 = 0, a5 = 8, a6 = ~sg (48(s1)),
   a7 = 7, t0 = 8 - n, t1 = 1, to the loop-2 head 0x84764. The run writes dt only. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0l.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YO0b YO0c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Ltac ewpeel := repeat (first [ rewrite ew_havoc_old by nat_side | rewrite ew_ewset_other by nat_side ]).
Ltac ewpeel_in H := repeat (first [ rewrite ew_havoc_old in H by nat_side | rewrite ew_ewset_other in H by nat_side ]).
Ltac hE33 := lazymatch goal with H : ew _ 33 = Z_to_bv 64 _ |- _ => rewrite H end.
Ltac hE33_in Hb := lazymatch goal with H : ew _ 33 = Z_to_bv 64 _ |- _ => rewrite H in Hb end.
Ltac kio := first [ apply same_io_refl | eapply same_io_trans; [| apply cw_same_io_wvb]; kio ].
Ltac ctk_keep kwr :=
  lazymatch goal with HG : mem_grows (mrestrict ?H ?m1) (mrestrict ?H ?m2),
                      KP : forall a, apresent ?H ?m0 a -> apresent ?H ?m1 a |- _ =>
    let KQ := fresh "KQ" in
    assert (KQ : forall a, apresent H m0 a -> apresent H m2 a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; eapply apresent_grows; [exact HG | exact (KP a Ha)]);
    clear KP; rename KQ into KP end;
  cw_keep kwr.
(* the write window of the run: dt (atom 33), a byte of the write set *)
Ltac awr_e :=
  cbn [ss_mem];
  lazymatch goal with |- awr_ok ?Ev ?rs _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply awr_ok_cons_gen;
    [ reflexivity | ewpeel; hE33; apply unsigned_lit_small; lia
    | let a := fresh "a" in let Ha := fresh "Ha" in
      intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha;
      lazymatch goal with Hp : oc_pre _ ?g, HJx : ajournal _ _ _ _ _ _ _ _ _ _ ((1, ?ps) :: _) ?l2 ?s2 ?w2 ?m2 ?d2 _,
        HPx : Permutation (ablocks _ ?l2 ?s2) _, Lx : AR_laws _ ?Bv |- _ =>
        apply (ocl_awr_wr Bv Lx g ps l2 s2 w2 m2 d2 a Hp HJx HPx); unfold oc_wr; right; lia end
    | ] ].
Ltac kwr_e :=
  let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a (r & Hr & Hb); cbv beta;
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  repeat (destruct Hr as [<- | Hr];
          [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; ewpeel_in Hb;
            first [ exfalso; lia
                  | hE33_in Hb; rewrite unsigned_lit_small in Hb by lia; lia ] | ]);
  destruct Hr.
Lemma oc_vm1_of_aview : forall H (m : word -> option byte) a v,
  aview tfibsegs H m a = Some v -> val_mem tfibsegs (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv j Hj. replace j with 0%nat by lia. cbn [Z.of_nat]. rewrite Z.add_0_r.
destruct (aview_byte tfibsegs H m a v Hv) as (b & Hb & -> & Hr). rewrite Hb. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
repeat rewrite (Z.mod_small (bv_unsigned b) 256 Hr). reflexivity.
Qed.
(* the shadow byte address of x (srli by 3, add the shadow offset in atom 32) *)
Lemma oc_den_sh : forall E m x, ew E m = Z_to_bv 64 x -> ew E 32 = Z_to_bv 64 SB -> 0 <= x < 2 ^ 47 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff m 0) (SLit 3)) (SOff 32 0)) = Z_to_bv 64 (SB + x / 8).
Proof.
intros E m x Hm H32 Hx. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite U_SLit, (U_atom E m x Hm ltac:(lia)), (U_atom E 32 SB H32 ltac:(unfold SB; lia)).
change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (Hx8 : 0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
rewrite (zcanon_id (x / 8)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64, SB; lia). lia.
Qed.
(* blt on two values below 2 ^ 63 *)
Lemma oc_blt_small : forall E a b x y, U E a = x -> U E b = y -> 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (x <? y).
Proof.
intros E a b x y Ha Hb Hx Hy. rewrite YO0c.branch_lt.
change (bv_unsigned (sv_denot E a)) with (U E a). change (bv_unsigned (sv_denot E b)) with (U E b).
rewrite Ha, Hb, !YO0b.s64_small by lia. reflexivity.
Qed.
Lemma oc_land7 : forall x, 0 <= x -> Z.land x 7 = x mod 8.
Proof. intros x Hx. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Ltac rv0 := lazymatch goal with HS : st_ok ?segs ?Ev ?ss (restrict ?H ?msv) |- context [getr (ms_regs ?msv) ?r] =>
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in
  let R := fresh "R" in
  assert (R : getr (ms_regs msv) r = sv_denot Ev e)
    by (refine (eq_trans (st_ok_restrict_reg segs H Ev ss msv r HS) _); reflexivity);
  rewrite R; clear R end.

(* the loop-2 head reached: the cut, from the run's kept memory (only dt changed, now 0) *)
Ltac close_e :=
  lazymatch goal with
  | HS : st_ok _ ?Ev ?ssv (restrict _ ?msv), HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?msv) ?md3 _,
    KE : forall a, _ -> ~ _ -> aview _ _ (ms_mem ?msv) a = _, KP : forall a, _ -> apresent _ (ms_mem ?msv) a,
    Hpre : oc_pre ?Bv ?g, HJ0 : ajournal _ _ _ _ _ _ _ _ _ _ _ ?l2 ?s2 ?w2 ?m2 ?d2 _, HP : Permutation _ _,
    HK : tcj_kept _ _ _ _ _ _ _ _ ?m2 _ _, HC : oc_common ?g ?ps ?r2 ?m2 ?w2, Lx : AR_laws _ ?Bv |- _ =>
  apply SRr_ret; cbv beta;
  assert (KE2 : forall a, 0 <= a < 2 ^ 64 -> ~ (oc_zv g ps a \/ oc_wr g a) ->
    aview tfibsegs (w_H w2) (ms_mem msv) a = aview tfibsegs (w_H w2) m2 a)
    by (let a := fresh "a" in let Ha := fresh "Ha" in let Hz := fresh "Hz" in
        intros a Ha Hz; apply KE; [exact Ha | intros Hd; apply Hz; right; unfold oc_wr; right; exact Hd]);
  destruct (ocl_keep_w Bv Lx g ps l2 s2 r2 m2 d2 w2 (ms_mem msv) Hpre HJ0 HP HK HC KE2 KP) as (HK3 & HC3);
  clear KE2;
  exists l2, s2, (ms_regs msv), (ms_mem msv), md3;
  split; [unfold cfg_at, w64; rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl) at 1; reflexivity|];
  split; [exact HJx|]; split; [exact HK3|]; split; [exact HP|];
  split; [assumption|]; split; [eapply same_io_trans; [eassumption | kio]|]; split; [assumption|];
  split; [apply (oc_common_regs g ps r2 (ms_regs msv) (ms_mem msv) w2); [|exact HC3];
          repeat split; rv0; rewrite ?sv_denot_SOff0; ewpeel;
          first [ lazymatch goal with EW : forall i r, _ -> ew _ i = getr ?rr r |- _ = getr ?rr ?r0 => apply EW; reflexivity end
                | lazymatch goal with E32 : ew _ 32 = Z_to_bv 64 SB, R23 : getr _ 23 = w64 SB |- _ =>
                    rewrite E32, R23; reflexivity end ]|]
  end.

(* the loop-2 head's facts: digit 0, seg as at entry, dt = 0 *)
Ltac p_l2_e :=
  lazymatch goal with
  | HS : st_ok _ ?Ev ?ssv (restrict _ ?msv), KE : forall a, _ -> ~ _ -> aview _ _ (ms_mem ?msv) a = _,
    Hpre : oc_pre ?Bv ?g, HJ0 : ajournal _ _ _ _ _ _ _ _ _ _ ((1, ?ps) :: _) ?l2 ?s2 ?w2 ?m2 ?d2 _, HP : Permutation _ _,
    Lx : AR_laws _ ?Bv, Hspec : owed_counter_text_spec _ = ct2 ?n ?s ?dot, Hl1 : oc_l1 ?n ?s ?dot,
    Harr : oc_arrays ?g ?ps ?w2 ?m2 ?n ?s ?dot, Hsj : garr8 _ _ (og_sg ?g) (og_sj ?g) |- _ =>
  exists 0, n, 0, s, dot, [];
  split; [rv0; reflexivity|]; split; [rv0; reflexivity|]; split; [rv0; reflexivity|];
  split; [rv0; unfold w64; apply (oc_D_not Ev 34 (og_sg g)); [ewpeel; assumption | lia]|];
  split; [rv0; reflexivity|];
  split; [rv0; rewrite denot_lit_U, (cw_U8n Ev 19 n) by (first [ewpeel; assumption | lia]); reflexivity|];
  split; [rv0; reflexivity|];
  split; [rv0; rewrite sv_denot_SOff0; ewpeel; assumption|];
  split; [rv0; rewrite denot_lit_U, U_and_lit by lia;
          rewrite (U_atom Ev 33 (og_dt g)) by (first [ewpeel; assumption | lia]); rewrite oc_land7 by lia; reflexivity|];
  split; [rv0; rewrite sv_denot_SOff0; ewpeel; assumption|];
  split; [reflexivity|]; split; [lia|];
  split; [rewrite Hspec; reflexivity|]; split; [exact Hl1|]; split; [reflexivity|]; split; [apply Forall_nil|];
  split; [lia|];
  split;
  [ apply (ocl_arrays_kept g ps w2 w2 m2 (ms_mem msv) n s dot); [|pose proof Hl1 as ((? & _) & _); lia | exact Harr];
    let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply KE; [lia|];
    let Hd := fresh "Hd" in intros Hd;
    exact (proj1 (ocl_wr_off Bv Lx g ps l2 s2 w2 m2 d2 a Hpre HJ0 HP ltac:(unfold oc_wr; right; exact Hd)) Ha)
  |];
  split;
  [ change ([] ++ skipn (Z.to_nat 0) (og_sj g)) with (og_sj g); apply (ocl_garr8_kept (w_H w2) (w_H w2) m2 (ms_mem msv)); [|exact Hsj];
    let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    let Lq := fresh "Lq" in let Hq1 := fresh "Hq1" in
    pose proof Hpre as (_ & _ & _ & _ & _ & _ & Lq & _ & _ & _ & Hq1 & _);
    rewrite ?Lq in Ha; change (Z.of_nat 8) with 8 in Ha; apply KE; [lia | lia]
  |];
  let i := oc_ridx HS 33%nat in
  let HR := fresh "HR" in
  pose proof (st_ok_region_nth _ _ _ i _ HS eq_refl) as HR; cbn [ms_mem restrict] in HR;
  lazymatch type of HR with region_ok _ _ _ ?rg => let rg' := eval vm_compute in rg in change rg with rg' in HR end;
  let V := fresh "V" in
  pose proof (field_of_region _ _ 33 (og_dt g) _ _ _ _ _ 0 1%N (SLit 0) 0 HR
    ltac:(ewpeel; lazymatch goal with E : ew _ 33 = Z_to_bv 64 (og_dt g) |- _ => rewrite E end; apply unsigned_lit_small; lia)
    ltac:(oc_in) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V;
  rewrite Z.add_0_r in V; exact V
  end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables RLO RHI GLYPHA : Z.
Variable ROSTRS : list (Z * Z).
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.

Theorem oc_part_e_holds : oc_part_e B MT RLO RHI GLYPHA ROSTRS.
Proof.
unfold oc_part_e. intros g pos W2 c2 Hpre Hnow Hc.
destruct Hc as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HK & HP & Hni & Hio & Hmo & HC & HL).
destruct HL as (n & s & dot & R19 & Hspec & Hl1 & Harr & Hsj & Hdj).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (ocl_stack B g Hpre) as (Hceil & H47 & H46 & Hal & Hsp1 & Hsp1a & Hwin & Hsp0).
destruct (ocl_frame B LAWS g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (Hfr & Efa & Efl & HF0 & HFc & HF64 & HFapp & HFp).
pose proof HC as (R8 & R2 & R9 & R3 & R4 & R23 & R26 & R18 & R21 & R24 & R27 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & V40 & V48 & _ & _ & _ & _).
pose proof Hpre as (_ & _ & _ & _ & Hsg & _ & Lsj & _ & Hdt & _).
pose proof (Hnow pos ly2 S2 W2 mem2 md2 HJ HK HP Hni) as (_ & Hsgra & Hdtra & _).
pose proof Hl1 as ((Hn0 & Hdl & Hdz) & Hd01 & Hsl & Hs128).
assert (Hdtb : 0 < og_dt g /\ og_dt g + 1 <= 2 ^ 63 /\ amem_range (og_dt g) 1)
  by (destruct Hdt as [((Hx0 & Hx1 & _ & _ & _ & _ & Ham & _) & _) | (Hx0 & Hx1 & _ & _ & _ & _ & _ & Ham & _)];
      (split; [|split]; assumption)).
destruct Hdtb as (Hdt0 & Hdt63 & Hdtam).
assert (Hdt47 : og_dt g + 2 <= 2 ^ 47) by (pose proof Hdtam as Ham; unfold amem_range in Ham; rewrite ?C3, ?C4, ?C5 in Ham;
  unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham; lia).
pose proof Hsg as (Hsg0 & Hsg63 & _).
assert (Hdtw : ~ (og_sp g - TB_owed_counter_text <= og_dt g < og_sp g))
  by (apply (oc_wr_win B g Hpre); unfold oc_wr; right; lia).
unfold TB_owed_counter_text, ESTACK in *.
destruct (Hdtra (og_dt g) ltac:(lia)) as (kd & Hkd & Hkok). unfold shadow_of_addr in Hkd. rewrite <- SB_SHADOW_OFF in Hkd.
assert (Hkd7 : 0 <= kd < 8) by (destruct Hkok as [-> | (? & ?)]; [lia | pose proof (Z.mod_pos_bound (og_dt g) 8 ltac:(lia)); lia]).
assert (Hdt8 : 0 <= og_dt g / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
set (xs := [og_dt g; og_sg g; SB + og_dt g / 8; kd]).
remember (Ereg regs2 (cw_extra xs)) as E eqn:HEE.
assert (EW : forall (i : nat) (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs2 r)
  by (intros i r Hi; subst E; exact (ew_Ereg_nat regs2 _ i r Hi)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
assert (E33 : ew E 33 = Z_to_bv 64 (og_dt g)) by (subst E; exact (cw_ew_x regs2 xs 0)).
assert (E34 : ew E 34 = Z_to_bv 64 (og_sg g)) by (subst E; exact (cw_ew_x regs2 xs 1)).
assert (E35 : ew E 35 = Z_to_bv 64 (SB + og_dt g / 8)) by (subst E; exact (cw_ew_x regs2 xs 2)).
assert (E36 : ew E 36 = Z_to_bv 64 kd) by (subst E; exact (cw_ew_x regs2 xs 3)).
assert (U35 : bv_unsigned (ew E 35) = SB + og_dt g / 8) by (rewrite E35; apply unsigned_lit_small; unfold SB; lia).
assert (E9 : ew E 9 = w64 (og_sp1 g)) by (rewrite (EW 9%nat 9%bv eq_refl); exact R9).
assert (E19 : ew E 19 = w64 n) by (rewrite (EW 19%nat 19%bv eq_refl); exact R19).
assert (U9 : bv_unsigned (ew E 9) = og_sp1 g) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = og_dt g) by (rewrite E33; apply unsigned_lit_small; lia).
assert (YS : st_ok tfibsegs E
  (mkSS PC_E sr_atoms
     [YP09.mkRegion (Some 9%nat) 40 56 40 40 [YP09.mkChunk 40 (CVal 8 (SOff 33 0)); YP09.mkChunk 48 (CVal 8 (SOff 34 0))];
      YP09.mkRegion (Some 33%nat) 0 1 0 1 []; YP09.mkRegion (Some 35%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 36 0))]] None
     (mkFacts [(32%nat, mkAF SB SB 0); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (19%nat, mkAF 0 8 0);
               (33%nat, mkAF 1 (2 ^ 47 - 2) 0); (35%nat, mkAF SB (SB + 2 ^ 44 - 1) 0); (36%nat, mkAF 0 7 0)] [] []))
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 PC_E) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val tfibsegs _ _ (og_sp1 g) 40 8 (SOff 33 0) (og_dt g));
        [rewrite sv_denot_SOff0; exact E33 | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact V40].
      * apply (chunk_ok_val tfibsegs _ _ (og_sp1 g) 48 8 (SOff 34 0) (og_sg g));
        [rewrite sv_denot_SOff0; exact E34 | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact V48].
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U33. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. replace (og_dt g + o) with (og_dt g) by lia. apply (apresent_writable tfibsegs).
      apply (ocl_present B LAWS g pos ly2 S2 W2 mem2 md2 (og_dt g) Hpre HJ HP HK). unfold oc_wr; right; lia.
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U35. unfold SB. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs _ _ (SB + og_dt g / 8) 0 1 (SOff 36 0) kd);
      [rewrite sv_denot_SOff0; exact E36 | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (oc_vm1_of_aview _ _ _ _ Hkd).
  - assert (Hdtapp : og_dt g + 1 <= SB - 1 \/ SB + 2 ^ 44 <= og_dt g)
      by (pose proof Hdtam as Ham; unfold amem_range in Ham; rewrite ?C3, ?C4, ?C5 in Ham;
          unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham; unfold SB; lia).
    apply pairwise_disjoint_of_extents. unfold extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U9, U33, U35. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold SB in *. repeat split; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E32, U9, E19, E33, E35, E36. unfold w64. rewrite !unsigned_lit_small by (unfold SB; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 5) with 32. unfold SB. repeat split; first [exact I | exact Hsp1a | lia]. }
pose proof (ast_ok_set_reg_fp tfibsegs E _ _ (23%bv : bv 5) (SOff 32 0) YS eq_refl
  ltac:(cbn [ms_regs restrict mkst]; rewrite sv_denot_SOff0, E32, R23; reflexivity)) as HS.
clear YS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
assert (SHOK : sh_ok tfibsegs CW_Bx [mkSHE 33 0 1] E (mrestrict (w_H W2) mem2)).
{ apply Forall_cons; [|apply Forall_nil].
  apply (cw_shent_ra W2 mem2 E 33 (og_dt g) 1); [exact Hdtra | exact Hdtam | lia | lia | lia | exact E33 | exact E32]. }
cw_keep_j0 HJ HJ0.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (og_dt g <= a < og_dt g + 1) ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
assert (KP : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem2 a) by (intros; assumption).
unfold cfg_at. change (w64 PC_E) with (Z_to_bv 64 PC_E).
cw_run_to awr_e 0x84734. ctk_keep kwr_e.
(* a1 = the shadow byte address of dt: atom 35, the base of the shadow byte's region *)
lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict ?Hh ?msv) |- _ =>
  pose proof (ast_ok_set_reg_fp tfibsegs Ev ssv (restrict Hh msv) (11%bv : bv 5) (SOff 35 0) HS eq_refl
    ltac:(cbn [ms_regs restrict]; rv0; rewrite sv_denot_SOff0; ewpeel; rewrite E35; symmetry;
          apply (oc_den_sh Ev 33 (og_dt g)); [ewpeel; exact E33 | ewpeel; exact E32 | lia])) as YS end.
clear HS. rename YS into HS. norm_ss HS.
cw_run_to awr_e PC_L2. ctk_keep kwr_e.
(* bnez a3 (0x8473c): the shadow byte of dt *)
cw_branch Hb1.
- (* not 0: the slow path's blt a2,a3 (0x84944), a2 = dt mod 8 *)
  lazymatch type of Hb1 with branch_taken _ (sv_denot ?Ev _) _ = _ =>
    rewrite branch_ne_U, (U_atom Ev 36 kd ltac:(ewpeel; exact E36) ltac:(lia)), U_lit in Hb1 by lia end.
  apply negb_true_iff, Z.eqb_neq in Hb1.
  cw_run_to awr_e PC_L2. ctk_keep kwr_e.
  cw_branch Hb2.
  all: lazymatch type of Hb2 with branch_taken _ (sv_denot ?Ev _) _ = _ =>
    rewrite (oc_blt_small Ev _ _ (og_dt g mod 8) kd) in Hb2;
    [ | rewrite U_and_lit, (U_atom Ev 33 (og_dt g) ltac:(ewpeel; exact E33) ltac:(lia)) by lia; apply oc_land7; lia
      | apply (U_atom Ev 36 kd ltac:(ewpeel; exact E36) ltac:(lia))
      | pose proof (Z.mod_pos_bound (og_dt g) 8 ltac:(lia)); lia | lia ] end.
  + cw_run_to awr_e PC_L2. ctk_keep kwr_e. close_e. p_l2_e.
  + exfalso. apply Z.ltb_ge in Hb2. destruct Hkok as [Hk0 | (Hk1 & _)]; lia.
- lazymatch type of Hb1 with branch_taken _ (sv_denot ?Ev _) _ = _ =>
    rewrite branch_ne_U, (U_atom Ev 36 kd ltac:(ewpeel; exact E36) ltac:(lia)), U_lit in Hb1 by lia end.
  cw_run_to awr_e PC_L2. ctk_keep kwr_e. close_e. p_l2_e.
Qed.
End d.
