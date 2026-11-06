(* LLVMFuzzerTestOneInput_segX_up_loop: the scan loop L5 of the image-B up segment of LLVMFuzzerTestOneInput,
   +0x918 .. +0x958, and the call of reac_upstream_decode #3 it falls into (+0x95c .. +0x968).

   The loop reads every byte of the upstream buffer (s7, length s8) back after the two refusing calls and ORs
   `byte != 0xa5` into a1; +0x958 aborts unless a1 = 0. Each byte read is ASan-checked in line (+0x91c .. +0x92c,
   slow path +0x94c .. +0x954) and UBSan-checked for the wrap of s7 + i (+0x918, `bltu s9, a2` with s9 = ~s7).

   One iteration is one Pa run (lib/B/Prog/DecodeBPaLib.v) from a seat at +0x918 whose env has i in a2 and the
   byte's address s7 + i as the extra atom 33 (the alias (s7 + a2) = atom 33 lets the engine see the address the
   loop computes as that atom), the byte as a one-byte region holding 0xa5, and the shadow base s2 as the run's Bx
   with the byte covered by one shadow entry; the ASan check and its slow path are the engine's token machinery
   (lib/Reusable/YCbn.v tok_load / tok_branch_pi). The loop itself is an induction on the bytes left, the shape of
   a Theorem Labs lane's GrantBuildSweepWalk.v:229 pb_bs_loop (a working branch). *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04 YG0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBList DecodeBAddr DecodeBPa DecodeBImg DecodeBPaLib.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_segX_up_a LLVMFuzzerTestOneInput_segX_up_b LLVMFuzzerTestOneInput_segX_up_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN1y.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* YM03.v:182-189 redefines lia / nia globally (context pruning and retries); this file uses the originals
   (YM03.v:179-180). *)
Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
Local Ltac Lia.nia ::= Zify.zify; xnia zchecker.

(* ~u as a 64-bit word. *)
Lemma up_lnot_mod : forall u, 0 <= u < 18446744073709551616 ->
  Z.lnot u mod 18446744073709551616 = 18446744073709551615 - u.
Proof.
intros u Hu. pose proof (Z.add_lnot_diag u) as H.
replace (Z.lnot u) with (-1 - u) by lia.
rewrite <- (Z.mod_add (-1 - u) 1 18446744073709551616) by discriminate.
rewrite Z.mod_small by lia. lia.
Qed.

(* The seat of one iteration. *)
Definition up_lextra (a : Z) : list word := [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 a].
Definition up_lreg : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 165))].
Definition UP_BLK_HI : Z := 0x7fffff800000.
Definition up_lfacts : facts :=
  mkFacts [(18%nat, mkAF 2147450880 2147450880 0); (33%nat, mkAF 4096 UP_BLK_HI 0)] []
    [(SAlu ALU_ADD (SOff 23 0) (SOff 12 0), SOff 33 0)].
Definition ss_loop : sstate := mkSS 0x918 sr_atoms [up_lreg] None up_lfacts.
Definition LBx : sv := SOff 18 0.
Definition up_LSH : list shent := [mkSHE 33 0 1].
(* The registers one iteration leaves alone (s2 .. s11, sp, gp, tp, s0, s1). *)
Definition up_keepL : list (bv 5) :=
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv].

(* Agreement below 32 survives the fresh atoms a run adds above it. *)
Ltac up_agree_ext :=
  lazymatch goal with
  | |- env_agree ?K ?X (ewset ?Y ?n ?w) =>
    apply (env_agree_trans K X Y (ewset Y n w)); [up_agree_ext | eapply env_agree_le; [|apply env_agree_ewset]; lia]
  | |- _ => assumption
  end.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Abbreviation SEGS := (@pa_segs _ decodeb_listing PI_decodeb).
#[local] Abbreviation VAL := (@pa_val _ decodeb_listing PI_decodeb).
#[local] Abbreviation BASE := (@pa_val _ decodeb_listing PI_decodeb A_TEXT).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Let RUN := @paj_run fx rc dec_B_sink_head decodeb_listing PL_decodeb PI_decodeb B LAWS.
Let RUNTO := @paj_run_to fx rc dec_B_sink_head decodeb_listing PL_decodeb PI_decodeb B LAWS.
Let BR := @paj_branch fx rc decodeb_listing PI_decodeb.

Definition EL (regs : bvmap 5 word) (a : Z) : env := Eimg (Ereg regs (up_lextra a)).

Lemma EL_agree : forall regs a, env_agree 32 (Ereg regs (up_lextra a)) (EL regs a).
Proof.
intros regs a. split; [intros n Hn; unfold EL; first [apply Eimg_low | symmetry; apply Eimg_low]; unfold A_TEXT; lia
  | reflexivity].
Qed.

Lemma EL_reg : forall regs a (r : bv 5) (n : nat), Z.of_nat n = bv_unsigned r -> ew (EL regs a) n = getr regs r.
Proof.
intros regs a r n Hn. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
unfold EL. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ n r Hn).
Qed.

Lemma EL_33 : forall regs a, ew (EL regs a) 33 = Z_to_bv 64 a.
Proof. intros regs a. unfold EL. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1). Qed.

Lemma EL_U_reg : forall regs a (r : bv 5) (n : nat) v, Z.of_nat n = bv_unsigned r ->
  getr regs r = w64 v -> 0 <= v < 18446744073709551616 -> U (EL regs a) (SOff n 0) = v.
Proof.
intros regs a r n v Hn Hr Hv. rewrite U_SOff, (EL_reg regs a r n Hn), Hr, Z.add_0_r. unfold w64.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
rewrite Z.mod_small by exact Hv. apply zcanon_id. change M64 with 18446744073709551616. exact Hv.
Qed.

Lemma EL_U_33 : forall regs a, 0 <= a < 18446744073709551616 -> U (EL regs a) (SOff 33 0) = a.
Proof.
intros regs a Ha. rewrite U_SOff, EL_33, Z.add_0_r, Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with 18446744073709551616. rewrite Z.mod_small by exact Ha.
apply zcanon_id. change M64 with 18446744073709551616. exact Ha.
Qed.

(* A byte the view shows as 0xa5 is the one-byte value 165. *)
Lemma up_val1 : forall (W : world SEGS) mem a,
  aview SEGS (w_H W) mem a = Some 165 -> val_mem SEGS (mrestrict (w_H W) mem) a 1 165.
Proof.
intros W mem a H k Hk. assert (k = 0%nat) by lia. subst k. rewrite Z.add_0_r.
unfold aview in H. destruct (mbyte SEGS (mrestrict (w_H W) mem) a) as [b|]; cbn in H; [|discriminate].
injection H as H. f_equal. apply bv_eq. rewrite H. vm_compute. reflexivity.
Qed.

Lemma up_lseat : forall regs (W : world SEGS) mem md ly S upb m i,
  AR SEGS B ly S W mem md -> In (upb, m) (ablocks B ly S) -> 0 <= i < req_size m ->
  getr regs 18 = w64 SHADOW_OFF -> getr regs 23 = w64 upb -> getr regs 12 = w64 i ->
  aview SEGS (w_H W) mem (upb + i) = Some 165 ->
  st_ok_pi SEGS VAL (EL regs (upb + i)) ss_loop
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x918)) mem (seg_rom SEGS))) /\
  sh_ok SEGS LBx up_LSH (EL regs (upb + i)) (mrestrict (w_H W) mem).
Proof.
intros regs W mem md ly S upb m i HAR Hin Hi H18 H23 H12 Hbyte.
destruct (al_blocks _ _ LAWS ly S W mem md upb m HAR Hin) as (_ & H4096 & Hc & Happ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Ha : 0 <= upb + i < 18446744073709551616) by lia.
set (E := EL regs (upb + i)).
assert (U33 : U E (SOff 33 0) = upb + i) by exact (EL_U_33 regs (upb + i) Ha).
assert (U18 : U E (SOff 18 0) = SHADOW_OFF)
  by (exact (EL_U_reg regs (upb + i) 18%bv 18 SHADOW_OFF eq_refl H18 ltac:(unfold SHADOW_OFF; lia))).
assert (U23 : U E (SOff 23 0) = upb) by (exact (EL_U_reg regs (upb + i) 23%bv 23 upb eq_refl H23 ltac:(lia))).
assert (U12 : U E (SOff 12 0) = i) by (exact (EL_U_reg regs (upb + i) 12%bv 12 i eq_refl H12 ltac:(lia))).
rewrite restrict_mkst_fx. split.
- apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + constructor; [|constructor]. unfold region_ok, up_lreg.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    assert (B33 : bv_unsigned (ew E 33) = upb + i)
      by (subst E; rewrite EL_33, Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616;
          apply Z.mod_small; exact Ha).
    rewrite B33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (upb + i) 0 1 (SLit 165) 165); [reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia |].
    rewrite Z.add_0_r. exact (up_val1 W mem (upb + i) Hbyte).
  + cbn [pairwise_disjoint all_disjoint]. split; exact I.
  + split; [|split].
    * cbn [f_atoms atoms_ok up_lfacts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      assert (B18 : bv_unsigned (ew E 18) = SHADOW_OFF)
        by (subst E; rewrite (EL_reg regs (upb + i) 18%bv 18 eq_refl), H18; reflexivity).
      assert (B33 : bv_unsigned (ew E 33) = upb + i)
        by (subst E; rewrite EL_33, Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616;
            apply Z.mod_small; exact Ha).
      rewrite B18, B33. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF, UP_BLK_HI.
      repeat split; try exact I; lia.
    * exact I.
    * cbn [f_alias alias_ok up_lfacts]. split; [|exact I].
      apply U_inj. rewrite U_SAlu, U23, U12, U33. cbn [zalu_raw]. apply zcanon_id.
      change M64 with 18446744073709551616. lia.
- constructor; [|constructor]. split.
  + cbn [she_m she_lo she_hi]. rewrite U33, Z.add_0_r. change (1 - 0) with 1.
    apply (obl_of_block SEGS B LAWS ly S W mem md E LBx (upb + i) 1 upb m HAR Hin U18); lia.
  + unfold app_apart, LBx. cbn [she_m she_lo she_hi]. rewrite U33, U18. intros a Ha'.
    change (Z.min 0 1) with 0 in Ha'. change (Z.max 0 1) with 1 in Ha'.
    unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. unfold SHADOW_OFF. lia.
Qed.
(* A register read through an env that agrees with the entry registers below 32. *)
Lemma up_U_agree : forall regs extra E' (n : nat) (r : bv 5) v z,
  env_agree 32 (Ereg regs extra) E' -> Z.of_nat n = bv_unsigned r -> getr regs r = w64 v ->
  0 <= v < 18446744073709551616 -> U E' (SOff n z) = zcanon (v + z).
Proof.
intros regs extra E' n r v z HA Hn Hr Hv.
pose proof (bv_unsigned_in_range 5 r) as Hb. change (bv_modulus 5) with 32 in Hb.
rewrite U_SOff, (proj1 HA n ltac:(lia)), (ew_Ereg_nat regs extra n r Hn), Hr. unfold w64.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
rewrite Z.mod_small by exact Hv. reflexivity.
Qed.


Lemma up_den_agree : forall regs extra E' (n : nat) (r : bv 5),
  env_agree 32 (Ereg regs extra) E' -> Z.of_nat n = bv_unsigned r -> (n < 32)%nat ->
  sv_denot E' (SOff n 0) = getr regs r.
Proof.
intros regs extra E' n r HA Hn Hl. cbn [sv_denot].
rewrite (proj1 HA n Hl), (ew_Ereg_nat regs extra n r Hn), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

Ltac in_tac := repeat (first [left; reflexivity | right]).

(* The agreement of the env a symbolic state HS is stated in with the iteration's entry registers. *)
Ltac up_agree_of HS regs a H :=
  pose proof (EL_agree regs a) as HAE0;
  lazymatch type of HS with
  | st_ok_pi _ _ ?E _ _ => assert (H : env_agree 32 (Ereg regs (up_lextra a)) E) by up_agree_ext
  | st_ok _ ?E _ _ => assert (H : env_agree 32 (Ereg regs (up_lextra a)) E) by up_agree_ext
  end; clear HAE0.

(* +0x918 .. +0x968: the loop over the bytes left, then the third reac_upstream_decode call. *)
Lemma up_loop : forall (W : world SEGS) STK sp0 FP ly0 S0 W0 mem0 md0 own ly S k (regs0 : bvmap 5 word) mem upb m
    (Q : world SEGS -> config -> Prop),
  In (upb, m) (ablocks B ly S) -> 1 <= m <= 1440 ->
  (forall j, 0 <= j < m -> aview SEGS (w_H W) mem (upb + j) = Some 165) ->
  getr regs0 18 = w64 SHADOW_OFF -> getr regs0 23 = w64 upb -> getr regs0 24 = w64 m ->
  getr regs0 25 = w64 (Z.lnot upb) ->
  (forall regsT mdT,
     getr regsT 10 = getr regs0 27 -> getr regsT 11 = getr regs0 22 -> getr regsT 12 = getr regs0 23 ->
     getr regsT 1 = Z_to_bv 64 (BASE + 0x96c) ->
     (forall x, In x up_keepL -> getr regsT x = getr regs0 x) ->
     @ajournal rc dec_B_sink_head SEGS B STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem mdT k ->
     SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (decodeb_sigma DB_reac_upstream_decode)) mem (seg_rom SEGS)) mdT) Q) ->
  forall n i regs md, n = Z.to_nat (m - i) -> 0 <= i < m ->
  @ajournal rc dec_B_sink_head SEGS B STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem md k ->
  getr regs 11 = w64 0 -> getr regs 12 = w64 i ->
  (forall x, In x up_keepL -> getr regs x = getr regs0 x) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x918)) mem (seg_rom SEGS)) md) Q.
Proof.
intros W STK sp0 FP ly0 S0 W0 mem0 md0 own ly S k regs0 mem upb m Q Hin Hm Hfill R18 R23 R24 R25 HK n.
induction n as [n IH] using lt_wf_ind.
intros i regs md Hn Hi HJ H11 H12 Hkeep.
pose proof (proj1 HJ) as HAR.
destruct (al_blocks _ _ LAWS ly S W mem md upb m HAR Hin) as (_ & H4096 & Hbc & _).
pose proof (req_size_pos m ltac:(lia)) as [_ Hrq].
pose proof asan_consts as (C1 & _).
assert (G18 : getr regs 18 = w64 SHADOW_OFF) by (rewrite (Hkeep 18%bv ltac:(in_tac)); exact R18).
assert (G23 : getr regs 23 = w64 upb) by (rewrite (Hkeep 23%bv ltac:(in_tac)); exact R23).
assert (G24 : getr regs 24 = w64 m) by (rewrite (Hkeep 24%bv ltac:(in_tac)); exact R24).
assert (G25 : getr regs 25 = w64 (18446744073709551615 - upb)).
{ rewrite (Hkeep 25%bv ltac:(in_tac)), R25. apply bv_eq. unfold w64. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with 18446744073709551616. rewrite up_lnot_mod by lia.
  rewrite (Z.mod_small (18446744073709551615 - upb)) by lia. reflexivity. }
destruct (up_lseat regs W mem md ly S upb m i HAR Hin ltac:(lia) G18 G23 H12 (Hfill i Hi)) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (EL regs (upb + i))) by (unfold EL; apply Eimg_env).
pose proof (EL_agree regs (upb + i)) as HA0.
assert (U25 : U (EL regs (upb + i)) (SOff 25 0) = 18446744073709551615 - upb)
  by (rewrite (up_U_agree regs _ _ 25 25%bv _ 0 HA0 eq_refl G25 ltac:(lia)), Z.add_0_r; apply zcanon_id; change M64 with 18446744073709551616; lia).
assert (U12 : U (EL regs (upb + i)) (SOff 12 0) = i)
  by (rewrite (up_U_agree regs _ _ 12 12%bv _ 0 HA0 eq_refl H12 ltac:(lia)), Z.add_0_r; apply zcanon_id; change M64 with 18446744073709551616; lia).
psrr_branch_tok RUN BR HS SHOK UPspan; rename Hc into Hb0.
{ exfalso. rewrite branch_ltu_U, U25, U12 in Hb0. apply Z.ltb_lt in Hb0. lia. }
paj_run_tok RUN HS HJ SHOK UPspan; [awr_ro|]. up_memeq HF.
up_agree_of HS regs (upb + i) HA1.
psrr_branch_tok RUN BR HS SHOK UPspan; rename Hc into Hb1.
- (* bytes left: back to +0x918 with i + 1 *)
  rewrite branch_ne_U in Hb1.
  rewrite (up_U_agree regs _ _ 24 24%bv m 0 HA1 eq_refl G24 ltac:(lia)),
          (up_U_agree regs _ _ 12 12%bv i 1 HA1 eq_refl H12 ltac:(lia)) in Hb1.
  rewrite Z.add_0_r, !zcanon_id in Hb1 by (change M64 with 18446744073709551616; lia).
  apply negb_true_iff, Z.eqb_neq in Hb1.
  paj_run_to_tok RUNTO HS HJ SHOK UPspan 0x918; [awr_ro|]. up_memeq HF.
  up_agree_of HS regs (upb + i) HA2.
  lazymatch goal with Hmem : ms_mem _ = _ |- _ => rewrite Hmem in HJ end.
  pmkst HS.
  lazymatch goal with Hmem : ms_mem _ = _ |- _ => rewrite Hmem end.
  eapply (IH (Z.to_nat (m - (i + 1))) ltac:(lia) (i + 1) _ _ eq_refl ltac:(lia) HJ).
  + up_rege HS (11%bv : bv 5) (SAlu ALU_OR (SOff 11 0) (SLit 0)).
    apply up_w64_of_U; [|lia]. rewrite U_SAlu, (up_U_agree regs _ _ 11 11%bv 0 0 HA2 eq_refl H11 ltac:(lia)), U_SLit.
    reflexivity.
  + up_rege HS (12%bv : bv 5) (SOff 12 1).
    apply up_w64_of_U; [|lia]. rewrite (up_U_agree regs _ _ 12 12%bv i 1 HA2 eq_refl H12 ltac:(lia)).
    apply zcanon_id. change M64 with 18446744073709551616. lia.
  + intros x Hx. rewrite <- (Hkeep x Hx).
    lazymatch type of HS with st_ok_pi _ _ ?E ?ss (restrict ?H ?msx) =>
      exact (regs_kept_of_st_ok_pi E ss (restrict H msx) regs (up_lextra (upb + i)) up_keepL HS HA2
               ltac:(vm_compute; reflexivity) x Hx) end.
- (* the last byte: a1 = 0, so +0x958 does not abort; then reac_upstream_decode #3 *)
  rewrite branch_ne_U in Hb1.
  rewrite (up_U_agree regs _ _ 24 24%bv m 0 HA1 eq_refl G24 ltac:(lia)),
          (up_U_agree regs _ _ 12 12%bv i 1 HA1 eq_refl H12 ltac:(lia)) in Hb1.
  paj_run_tok RUN HS HJ SHOK UPspan; [awr_ro|]. up_memeq HF.
  up_agree_of HS regs (upb + i) HA2.
  psrr_branch_tok RUN BR HS SHOK UPspan; rename Hc into Hb2.
  { exfalso. rewrite branch_ne_U, U_SAlu, (up_U_agree regs _ _ 11 11%bv 0 0 HA2 eq_refl H11 ltac:(lia)), !U_SLit in Hb2.
    cbn in Hb2. discriminate. }
  paj_run_tok RUN HS HJ SHOK UPspan; [awr_ro|].
  up_agree_of HS regs (upb + i) HA3.
  up_land HF HS HJ.
  apply HK.
  + up_rege HS (10%bv : bv 5) (SOff 27 0).
    rewrite <- (Hkeep 27%bv ltac:(in_tac)). exact (up_den_agree regs _ _ 27 27%bv HA3 eq_refl ltac:(lia)).
  + up_rege HS (11%bv : bv 5) (SOff 22 0).
    rewrite <- (Hkeep 22%bv ltac:(in_tac)). exact (up_den_agree regs _ _ 22 22%bv HA3 eq_refl ltac:(lia)).
  + up_rege HS (12%bv : bv 5) (SOff 23 0).
    rewrite <- (Hkeep 23%bv ltac:(in_tac)). exact (up_den_agree regs _ _ 23 23%bv HA3 eq_refl ltac:(lia)).
  + up_rege HS (1%bv : bv 5) (SOff 240 2412).
    lazymatch type of HS with st_ok _ ?E _ _ =>
      lazymatch goal with Hx : img_env _ _ E |- _ => exact (codeptr_val E 2412 Hx) end end.
  + intros x Hx. rewrite <- (Hkeep x Hx).
    lazymatch type of HS with st_ok ?sg ?E ?ss (restrict ?H ?msx) =>
      exact (regs_kept_of_st_ok sg E ss (restrict H msx) regs (up_lextra (upb + i)) up_keepL HS HA3
               ltac:(vm_compute; reflexivity) x Hx) end.
  + exact HJ.
Qed.
End g.
