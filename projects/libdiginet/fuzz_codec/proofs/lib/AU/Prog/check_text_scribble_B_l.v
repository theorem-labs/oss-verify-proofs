(* Segment L of check_text_scribble's walk in image B (fuzz_codec.asan-ubsan 0x83dbc): bs_seg_L of
   check_text_scribble_B_inv.v, one output byte of the inlined owed_scribble_text from the loop head 0x83ed4.
   The state at the head (check_text_scribble_B_lst.v bsl_state) holds the text byte x = q[i] (atom 34), for a dot also
   y = q[i + 1] (atom 36), and want[o] (atom 35) as a writable byte when o < n. Three cases, split before the run:
   - x = 0 or o = n: the run stops at 0x83eec beqz x (taken for x = 0) and at 0x83ef0 bgeu a1,s3 (taken for o >= n),
     each taken side goes to the exit 0x83fb8; both not taken contradicts the case.
   - x <> 0, x <> 46, o < n: bgeu not taken, 0x83ef4 bne x,46 taken, 0x83f54 bgez (x << 56): x < 128 stores x, else
     the store of '?' (63); want[o] := the byte, back to the head with o + 1, i + 1.
   - x = 46, o < n: bne not taken, 0x83f20 bltu 8,((y - 49) & 255): taken (y not a digit) stores x = 46 through the
     plain path; not taken (y a digit) stores y - 26 and takes two bytes.
   The UBSan checks of the loop (0x83efc q + i + 1, 0x83f24 / 0x83f4c want + o, 0x83f80 q + i and the jump at
   0x83f84) are decided by the run from the atoms' facts (a2, a3 at least 2 ^ 64 - 2 ^ 47, a1 at most 8, s10 at most
   2 ^ 47 - 2); the instrumented checks of q + i, q + i + 1 and want[o] by the shadow entries. want[o]'s write window
   passes the token run's check only with a fact apart from the shadow band, so the store cases are run once for a
   frame in the low zone and once for one in the high zone. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CPgWalkU CPgWalkKeptU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkFrameU check_text_scribble_B_inv.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_base check_text_scribble_B_lst.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the branch conditions the runs leave ---------------------------------------------------------------------- *)
Lemma bsl_c_eq : forall Ev k x c, ew Ev k = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot Ev (SOff k 0)) (sv_denot Ev (SLit c)) = (x =? c).
Proof. intros Ev k x c Hk Hx Hc. rewrite branch_eq_U, (U_atom Ev k x Hk Hx), (U_lit Ev c Hc). reflexivity. Qed.
Lemma bsl_c_ne : forall Ev k x c, ew Ev k = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot Ev (SOff k 0)) (sv_denot Ev (SLit c)) = negb (x =? c).
Proof. intros Ev k x c Hk Hx Hc. rewrite branch_ne_U, (U_atom Ev k x Hk Hx), (U_lit Ev c Hc). reflexivity. Qed.
Lemma bsl_c_geu : forall Ev a b va vb, ew Ev a = Z_to_bv 64 va -> ew Ev b = Z_to_bv 64 vb ->
  0 <= va < 2 ^ 64 -> 0 <= vb < 2 ^ 64 ->
  branch_taken BC_GEU (sv_denot Ev (SOff a 0)) (sv_denot Ev (SOff b 0)) = negb (va <? vb).
Proof.
intros Ev a b va vb Ha Hb Hva Hvb. rewrite branch_geu_U, (U_atom Ev a va Ha Hva), (U_atom Ev b vb Hb Hvb). reflexivity.
Qed.
(* 0x83f18-0x83f20: (y - 49) & 255 above 8 is y not a digit *)
Lemma bsl_c_digit : forall Ev y, ew Ev 36 = Z_to_bv 64 y -> 0 <= y < 256 ->
  branch_taken BC_LTU (sv_denot Ev (SLit 8)) (sv_denot Ev (SAlu ALU_AND (SOff 36 (-49)) (SLit 255))) =
  negb ((49 <=? y) && (y <=? 57)).
Proof.
intros Ev y Hy Hr. rewrite branch_ltu_U, (U_lit Ev 8 ltac:(lia)), (U_and_lit Ev _ 255 ltac:(lia)).
rewrite U_SOff, Hy, unsigned_lit_small by lia.
change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite zcanon_wrap. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64).
destruct (Z.ltb_spec y 49) as [Hl | Hl].
- rewrite <- (Z.mod_add (y + -49) 1 (2 ^ 64)) by lia. rewrite (Z.mod_small (y + -49 + 1 * 2 ^ 64)) by lia.
  replace (y + -49 + 1 * 2 ^ 64) with ((y + 207) + (2 ^ 56 - 1) * 2 ^ 8) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
  replace (49 <=? y) with false by (symmetry; apply Z.leb_gt; lia). cbn [andb negb]. apply Z.ltb_lt. lia.
- rewrite (Z.mod_small (y + -49) (2 ^ 64)) by lia. rewrite (Z.mod_small (y + -49) (2 ^ 8)) by lia.
  replace (49 <=? y) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
  destruct (Z.leb_spec y 57); cbn [negb]; [apply Z.ltb_ge | apply Z.ltb_lt]; lia.
Qed.
(* 0x83f50-0x83f54: bgez (x << 56) is x < 128 *)
Lemma bsl_c_ge56 : forall Ev x, ew Ev 34 = Z_to_bv 64 x -> 0 <= x < 256 ->
  branch_taken BC_GE (sv_denot Ev (SAlu ALU_SLL (SOff 34 0) (SLit 56))) (sv_denot Ev (SLit 0)) = (x <? 128).
Proof.
intros Ev x Hx Hr. rewrite YO0c.branch_ge.
change (bv_unsigned (sv_denot Ev (SAlu ALU_SLL (SOff 34 0) (SLit 56)))) with (U Ev (SAlu ALU_SLL (SOff 34 0) (SLit 56))).
change (bv_unsigned (sv_denot Ev (SLit 0))) with (U Ev (SLit 0)).
rewrite U_SAlu, (U_atom Ev 34 x Hx ltac:(lia)), (U_lit Ev 56 ltac:(lia)), (U_lit Ev 0 ltac:(lia)).
cbn [zalu_raw]. change (Z.land 56 63) with 56. rewrite Z.shiftl_mul_pow2 by lia.
rewrite zcanon_id by (unfold M64; lia). unfold YO0b.s64.
replace (0 <? 2 ^ 63) with true by reflexivity.
destruct (Z.ltb_spec x 128) as [Hl | Hl].
- replace (x * 2 ^ 56 <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (x * 2 ^ 56 <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
- replace (x * 2 ^ 56 <? 2 ^ 63) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (x * 2 ^ 56 - 2 ^ 64 <? 0) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
(* the byte a store left in a region's chunk *)
Lemma bsl_byte_of : forall Ev e v, U Ev e = v -> 0 <= v < 256 -> bv_unsigned (sv_denot Ev e) mod 2 ^ (8 * Z.of_N 1) = v.
Proof.
intros Ev e v Hu Hv. change (bv_unsigned (sv_denot Ev e)) with (U Ev e). rewrite Hu.
change (2 ^ (8 * Z.of_N 1)) with 256. apply Z.mod_small. exact Hv.
Qed.

(* ---- the runs' write windows ------------------------------------------------------------------------------------ *)
(* the text is read-only, want[o] is a byte of the walk's own frame *)
Ltac bsl_awr :=
  cw_awrA;
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 35%nat);
    [ reflexivity | ewpeel; lazymatch goal with U35 : bv_unsigned (ew _ 35) = _ |- _ => exact U35 end
    | let a := fresh "a" in let Ha := fresh "Ha" in
      intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; exists 0; eexists;
      split; [left; reflexivity|]; left; unfold in_zr, frame_rng; cbn [fst snd];
      lazymatch goal with Efa : forall c p, frame_addr ?l c p = frame_addr _ c p |- _ => rewrite Efa end;
      change (fs_frame_bytes 0) with 64; unfold bs_F in *; lia
    | ] ].
(* the zone of the runs' writes: want[o] *)
Ltac bsl_kwr :=
  let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a (r & Hr & Hb); cbv beta;
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  repeat (destruct Hr as [<- | Hr];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; ewpeel_in Hb;
      first [ lia | lazymatch goal with U35 : bv_unsigned (ew _ 35) = _ |- _ => rewrite U35 in Hb end; lia ] | ]);
  destruct Hr.
(* a register as an atom of the start plus c *)
Ltac bsl_off Ek := rv; ewpeel; rewrite Ek; unfold w64; rewrite unsigned_lit_small by lia; reflexivity.
(* the byte the run stored into want[o] *)
Ltac bsl_vn Vn :=
  lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict ?Hh ?msv), U35 : bv_unsigned (ew _ 35) = ?b |- _ =>
    let HR := fresh "HR" in
    pose proof (st_ok_region_nth Ev ssv (restrict Hh msv) 1 _ HS eq_refl) as HR;
    cbn [ms_mem restrict] in HR;
    pose proof (field_of_region_any _ _ 35 b _ 0 1 0 1 0 1%N _ HR ltac:(ewpeel; exact U35) ltac:(left; reflexivity)
      ltac:(cbn; lia)) as Vn;
    clear HR; change (N.to_nat 1) with 1%nat in Vn; rewrite Z.add_0_r in Vn end.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.

(* a byte of an object of the call state is not a fresh byte *)
Lemma bsl_apart : forall lyc Sc q n a, cobj_ok B lyc Sc q n -> cw_fresh B lyc Sc a -> forall j, q <= j < q + n -> j <> a.
Proof.
intros lyc Sc q n a Hc (_ & _ & Hfb & Hff) j Hj Heq. subst a.
destruct Hc as [(bb & m & Hin & H1 & H2) | (cid & p & Hin & H1 & H2)].
- exact (Hfb bb m (j - bb) Hin ltac:(lia) ltac:(lia)).
- apply (proj1 (Hff cid p Hin)). unfold in_zr, frame_rng. cbn [fst snd]. lia.
Qed.

Theorem bs_l_holds : bs_seg_L B MT.
Proof.
unfold bs_seg_L. intros g pos fuel W2 c2 Hpre Hnow Hc.
destruct Hc as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HK & HP & Hni & Hio & Hmo & HC & HL).
destruct HL as (i & o & w & R11 & R26 & R12 & R13 & R14 & R15 & R20 & Hi & Ho & Hfuel & Hnz & Hwl & Hw1 & Hw2 & Hwg).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_val as Hac.
destruct (bs_stack B g Hpre) as (Hceil & H47 & H46 & Hal & Hsp1 & Hsp1a & Hwin & Hsp0).
destruct (bs_frame B LAWS g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (Hfr & Efa & Efl & HF0 & HFc & HF64 & HFapp & HFp).
pose proof HC as (R8 & R2 & R9 & R3 & R4 & R18 & R24 & R22 & R23 & R25 & R19 & R21 & _).
pose proof Hpre as (_ & _ & (Hq0 & _ & Hin0 & (_ & Hqn & _ & _ & _ & Ham & _)) & Hoq & _ & _ & _ & _ & _ & _ & Hn & _).
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsh).
specialize (Hnow pos ly2 S2 W2 mem2 md2 HJ HK HP Hni) as ((Htb & Htra) & _ & _).
assert (Hil : (Z.to_nat i < length (bs_tb g))%nat) by exact (bs_tb_len (bs_tb g) (Z.to_nat i) Hin0 Hnz).
set (x := nth (Z.to_nat i) (bs_tb g) 0).
destruct (Htb (Z.to_nat i) Hil) as (Vx & Hx8). fold x in Vx, Hx8. rewrite Z2Nat.id in Vx by lia.
assert (Hlen : bs_q g + bs_len g <= 2 ^ 47 - 1) by (unfold bs_len, amem_range, kLowMemEnd, kHighMemEnd in *; lia).
assert (Ham1 : forall k, 0 <= k -> i + k <= bs_len g -> amem_range (bs_q g + i) k)
  by (intros k Hk0 Hk; unfold bs_len, amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg in *; lia).
assert (Hra1 : forall k, 0 <= k -> i + k <= bs_len g ->
  range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (bs_q g + i) k)
  by (intros k Hk0 Hk a Ha; apply Htra; lia).
assert (Hwant : o < bs_n g -> forall k, 0 <= k -> i + k <= bs_len g ->
  range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (bs_F g pos + 32 + o) 1 /\
  amem_range (bs_F g pos + 32 + o) 1 /\ apresent (w_H W2) mem2 (bs_F g pos + 32 + o) /\
  (forall a, bs_q g + i <= a < bs_q g + i + k -> a <> bs_F g pos + 32 + o)).
{ intros Hon k Hk0 Hk. split; [|split; [|split]].
  - rewrite <- Z.add_assoc. apply (bs_ra_want (w_H W2) mem2 (bs_F g pos) (32 + o) 1); [| lia | lia | lia | exact Hsh].
    pose proof (Z.div_mod (bs_F g pos) 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
    replace (64 * (bs_F g pos / 64)) with ((8 * (bs_F g pos / 64)) * 8) by lia. apply Z.mod_mul. lia.
  - unfold in_app, amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg, kLowShadowBeg, ASAN_CEIL in *. lia.
  - apply HFp. lia.
  - intros a Ha. apply (bsl_apart (bs_lyc g) (bs_Sc g) (bs_q g) (bs_len g) (bs_F g pos + 32 + o) Hoq);
      [| unfold bs_len in *; lia].
    exact (bs_fresh B LAWS g pos ly2 S2 W2 mem2 md2 (bs_F g pos + 32 + o) Hpre HJ HP ltac:(unfold bs_zv; lia)). }
assert (KP : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem2 a) by (intros; assumption).
cw_keep_j0 HJ HJ0.
unfold cfg_at. change (w64 PC_L) with (Z_to_bv 64 PC_L).
unfold in_app in HFapp.
assert (Hsw : (x = 0 \/ o = bs_n g) \/ (x <> 0 /\ o < bs_n g)) by lia.
destruct Hsw as [HA | (Hx0 & Hon)].
- (* the loop's exit: the byte is 0, or every slot is filled *)
  destruct (bsl_state regs2 W2 mem2 (bs_q g) i o (bs_n g) (bs_F g pos) x 0 false false 0 255 0 0 4096 (2 ^ 47 - 24)
    R23 R14 R15 R21 R26 R22 R11 R19 R13 R12
    ltac:(lia) Hi ltac:(unfold bs_len in *; lia) Ho (proj2 Hn) HF0 ltac:(lia) ltac:(lia) ltac:(lia) Hx8 ltac:(lia)
    ltac:(lia) Vx ltac:(intros Hf; discriminate Hf) (Hra1 1 ltac:(lia) ltac:(unfold bs_len in *; lia))
    (Ham1 1 ltac:(lia) ltac:(unfold bs_len in *; lia)) ltac:(intros Hf; discriminate Hf)) as (HS & SHOK).
  remember (Ereg regs2 (cw_extra (bsl_xs (bs_q g) i x (bs_F g pos) o 0))) as E eqn:HEE.
  assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs2 r)
    by (intros nn r Hnn; subst E; apply ew_Ereg_nat; exact Hnn).
  assert (E34 : ew E 34 = Z_to_bv 64 x) by (subst E; exact (cw_ew_x regs2 (bsl_xs (bs_q g) i x (bs_F g pos) o 0) 1)).
  assert (E11 : ew E 11 = w64 o) by (rewrite (EE 11%nat 11%bv eq_refl); exact R11).
  assert (E19 : ew E 19 = w64 (bs_n g)) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
  assert (E26 : ew E 26 = w64 i) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
  assert (E12 : ew E 12 = w64 (bnot (bs_F g pos + 32))) by (rewrite (EE 12%nat 12%bv eq_refl); exact R12).
  assert (E20 : ew E 20 = w64 (bs_ch g)) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
  assert (E23 : ew E 32 = getr regs2 23) by (subst E; rewrite cw_ew_SB; exact (eq_sym R23)).
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a)
    by (intros; reflexivity).
  cw_run_to bsl_awr 0x83fb8. ctk_keep cw_kwr_ro.
  cw_branch Hc1.
  all: lazymatch type of Hc1 with context [sv_denot ?Ev _] =>
    rewrite (bsl_c_eq Ev 34 x 0 ltac:(ewpeel; exact E34) ltac:(lia) ltac:(lia)) in Hc1 end.
  + (* x = 0 *)
    apply Z.eqb_eq in Hc1.
    destruct (bs_rest_exit0 g i o w Hi Ho Hil ltac:(fold x; exact Hc1) Hw1 Hw2) as (He1 & He2).
    cw_run_to bsl_awr 0x83fb8. ctk_keep cw_kwr_ro.
    apply SRr_ret. cbv beta. right.
    lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- context [mkCfg _ ?md3] =>
      apply (bs_cut_close B MT LAWS g pos PC_E (P_E g pos) ly2 S2 regs2 mem2 md2 W2 msv md3 Hpre HJ0 HK HP Hni Hio
        Hmo HC HJ);
      [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl)
      | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin
      | bs_rfin | bs_rfin
      | intros a Ha _; apply KE; [exact Ha | tauto] | exact KP | ] end.
    exists i, o, w.
    split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|].
    split; [exact Hi|]. split; [exact Ho|]. split; [exact Hwl|]. split; [exact He1|]. split; [exact He2|].
    apply (bs_garr8_kept (w_H W2) (w_H W2) mem2 _); [|exact Hwg].
    intros a Ha. apply KE; [lia | tauto].
  + apply Z.eqb_neq in Hc1.
    cw_run_to bsl_awr 0x83fb8. ctk_keep cw_kwr_ro.
    cw_branch Hc2.
    all: lazymatch type of Hc2 with context [sv_denot ?Ev _] =>
      rewrite (bsl_c_geu Ev 11 19 o (bs_n g) ltac:(ewpeel; exact E11) ltac:(ewpeel; exact E19) ltac:(lia) ltac:(lia))
        in Hc2 end.
    * (* o = n *)
      assert (Hon : o = bs_n g) by (destruct (Z.ltb_spec o (bs_n g)); [discriminate Hc2 | lia]).
      destruct (bs_rest_full g i o w Hon Hw1 Hw2) as (He1 & He2).
      cw_run_to bsl_awr 0x83fb8. ctk_keep cw_kwr_ro.
      apply SRr_ret. cbv beta. right.
      lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- context [mkCfg _ ?md3] =>
        apply (bs_cut_close B MT LAWS g pos PC_E (P_E g pos) ly2 S2 regs2 mem2 md2 W2 msv md3 Hpre HJ0 HK HP Hni Hio
          Hmo HC HJ);
        [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl)
        | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin
        | bs_rfin | bs_rfin
        | intros a Ha _; apply KE; [exact Ha | tauto] | exact KP | ] end.
      exists i, o, w.
      split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|].
      split; [exact Hi|]. split; [exact Ho|]. split; [exact Hwl|]. split; [exact He1|]. split; [exact He2|].
      apply (bs_garr8_kept (w_H W2) (w_H W2) mem2 _); [|exact Hwg].
      intros a Ha. apply KE; [lia | tauto].
    * (* x <> 0 and o < n: not this case *)
      exfalso. destruct (Z.ltb_spec o (bs_n g)); [|discriminate Hc2]. lia.
- destruct (Z.eq_dec x 46) as [Hx46 | Hx46].
  + (* a dot: the byte after it *)
    assert (Hil1 : (S (Z.to_nat i) < length (bs_tb g))%nat)
      by exact (bs_tb_len (bs_tb g) (S (Z.to_nat i)) Hin0 (bs_firstn_S (bs_tb g) (Z.to_nat i) Hil Hnz ltac:(fold x; lia))).
    set (y := nth (S (Z.to_nat i)) (bs_tb g) 0).
    destruct (Htb (S (Z.to_nat i)) Hil1) as (Vy & Hy8). fold y in Vy, Hy8.
    replace (bs_q g + Z.of_nat (S (Z.to_nat i))) with (bs_q g + i + 1) in Vy by lia.
    destruct HFapp as (_ & [Hz | Hz]).
    * (* the frame in the low zone *)
      destruct (bsl_state regs2 W2 mem2 (bs_q g) i o (bs_n g) (bs_F g pos) x y true true 46 46 0 255 4096 (kLowShadowBeg - 24)
        R23 R14 R15 R21 R26 R22 R11 R19 R13 R12
        ltac:(lia) Hi ltac:(unfold bs_len in *; lia) ltac:(lia) (proj2 Hn) HF0 ltac:(lia) ltac:(lia) ltac:(lia) Hx8
        ltac:(lia) Hy8 Vx ltac:(intros _; exact Vy) (Hra1 2 ltac:(lia) ltac:(unfold bs_len in *; lia))
        (Ham1 2 ltac:(lia) ltac:(unfold bs_len in *; lia))
        ltac:(intros _; split; [exact Hon | exact (Hwant Hon 2 ltac:(lia) ltac:(unfold bs_len in *; lia))]))
        as (HS & SHOK).
      remember (Ereg regs2 (cw_extra (bsl_xs (bs_q g) i x (bs_F g pos) o y))) as E eqn:HEE.
      assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs2 r)
        by (intros nn r Hnn; subst E; apply ew_Ereg_nat; exact Hnn).
      assert (E34 : ew E 34 = Z_to_bv 64 x) by (subst E; exact (cw_ew_x regs2 (bsl_xs (bs_q g) i x (bs_F g pos) o y) 1)).
      assert (E35 : ew E 35 = Z_to_bv 64 (bs_F g pos + 32 + o))
        by (subst E; exact (cw_ew_x regs2 (bsl_xs (bs_q g) i x (bs_F g pos) o y) 2)).
      assert (U35 : bv_unsigned (ew E 35) = bs_F g pos + 32 + o) by (rewrite E35; apply unsigned_lit_small; lia).
      assert (E36 : ew E 36 = Z_to_bv 64 y) by (subst E; exact (cw_ew_x regs2 (bsl_xs (bs_q g) i x (bs_F g pos) o y) 3)).
      assert (E11 : ew E 11 = w64 o) by (rewrite (EE 11%nat 11%bv eq_refl); exact R11).
      assert (E19 : ew E 19 = w64 (bs_n g)) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
      assert (E26 : ew E 26 = w64 i) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
      assert (E12 : ew E 12 = w64 (bnot (bs_F g pos + 32))) by (rewrite (EE 12%nat 12%bv eq_refl); exact R12).
      assert (E13 : ew E 13 = w64 (bnot (bs_q g))) by (rewrite (EE 13%nat 13%bv eq_refl); exact R13).
      assert (E20 : ew E 20 = w64 (bs_ch g)) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
      assert (E23 : ew E 32 = getr regs2 23) by (subst E; rewrite cw_ew_SB; exact (eq_sym R23)).
      assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (a = bs_F g pos + 32 + o) ->
        aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
      cw_run_to bsl_awr 0x83ee8. ctk_keep bsl_kwr.
      cw_run_to bsl_awr 0x83ed4. ctk_keep bsl_kwr.
      cw_branch Hc1.
      all: lazymatch type of Hc1 with context [sv_denot ?Ev _] =>
        rewrite (bsl_c_geu Ev 11 19 o (bs_n g) ltac:(ewpeel; exact E11) ltac:(ewpeel; exact E19) ltac:(lia) ltac:(lia))
          in Hc1 end.
      { exfalso. destruct (Z.ltb_spec o (bs_n g)); [discriminate Hc1 | lia]. }
      cw_run_to bsl_awr 0x83ed4. ctk_keep bsl_kwr.
      cw_branch Hc2.
      all: lazymatch type of Hc2 with context [sv_denot ?Ev _] =>
        rewrite (bsl_c_ne Ev 34 x 46 ltac:(ewpeel; exact E34) ltac:(lia) ltac:(lia)) in Hc2 end.
      { exfalso. apply negb_true_iff, Z.eqb_neq in Hc2. exact (Hc2 Hx46). }
      cw_run_to bsl_awr 0x83ed4. ctk_keep bsl_kwr.
      cw_branch Hc3.
      all: lazymatch type of Hc3 with context [sv_denot ?Ev _] =>
        rewrite (bsl_c_digit Ev y ltac:(ewpeel; exact E36) Hy8) in Hc3 end.
      -- (* y is not a digit: the dot itself *)
        assert (Hnd : ~ (49 <= y <= 57))
          by (intros (Hy1 & Hy2); rewrite (proj2 (Z.leb_le _ _) Hy1), (proj2 (Z.leb_le _ _) Hy2) in Hc3; discriminate Hc3).
        assert (Hv : (if x <? 128 then x else 63) = x) by (rewrite (proj2 (Z.ltb_lt x 128) ltac:(lia)); reflexivity).
        cw_run_to bsl_awr 0x83ed4. ctk_keep bsl_kwr.
        bsl_vn Vn.
        lazymatch type of Vn with context [bv_unsigned (sv_denot ?Ev ?e) mod _] =>
          rewrite (bsl_byte_of Ev e (x) ltac:(apply (U_atom Ev 34 x); [ewpeel; exact E34 | lia]) ltac:(lia)) in Vn end.
        pose proof (bs_rest_plain g i o w Hi ltac:(lia) Hil ltac:(fold x; lia) ltac:(fold x y; lia) Hw1 Hw2) as Hrr.
        cbv zeta in Hrr. destruct Hrr as (Hr1 & Hr2). fold x in Hr1. rewrite Hv in Hr1.
        apply SRr_ret. cbv beta. left.
        lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- context [mkCfg _ ?md3] =>
          apply (bs_cut_close B MT LAWS g pos PC_L (P_L g pos fuel) ly2 S2 regs2 mem2 md2 W2 msv md3 Hpre HJ0 HK HP Hni
            Hio Hmo HC HJ);
          [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl)
          | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin
          | bs_rfin | bs_rfin
          | intros a Ha Hzv; apply KE; [exact Ha | intros Ha'; apply Hzv; unfold bs_zv; lia] | exact KP | ] end.
        exists (i + 1), (o + 1), (w ++ [x]).
        split; [bsl_off E11|]. split; [bsl_off E26|].
        split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|].
        split; [lia|]. split; [lia|]. split; [lia|].
        split; [replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia; exact (bs_firstn_S (bs_tb g) (Z.to_nat i) Hil Hnz ltac:(fold x; lia))|].
        split; [rewrite length_app; cbn [length]; lia|].
        split; [exact Hr1|]. split; [exact Hr2|].
        apply (bs_want_snoc (w_H W2) mem2 _ (bs_F g pos) w (x) Hwg).
        ++ intros a Ha. apply KE; lia.
        ++ replace (bs_F g pos + 32 + Z.of_nat (length w)) with (bs_F g pos + 32 + o) by lia. exact Vn.
        ++ lia.
      -- (* y is a digit: y - 26, two bytes *)
        assert (Hdg : 49 <= y <= 57)
          by (destruct (Z.leb_spec 49 y); destruct (Z.leb_spec y 57); cbn [andb negb] in Hc3; try discriminate Hc3; lia).
        cw_run_to bsl_awr 0x83ed4. ctk_keep bsl_kwr.
        bsl_vn Vn.
        lazymatch type of Vn with context [bv_unsigned (sv_denot ?Ev ?e) mod _] =>
          rewrite (bsl_byte_of Ev e (y - 26) ltac:(rewrite (U_atom_off Ev 36 y (-26) ltac:(ewpeel; exact E36) ltac:(lia) ltac:(lia)); lia) ltac:(lia)) in Vn end.
        pose proof (bs_rest_digit g i o w Hi ltac:(lia) Hil ltac:(fold x; lia) ltac:(fold y; lia) Hw1 Hw2) as (Hr1 & Hr2).
        fold y in Hr1.
        apply SRr_ret. cbv beta. left.
        lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- context [mkCfg _ ?md3] =>
          apply (bs_cut_close B MT LAWS g pos PC_L (P_L g pos fuel) ly2 S2 regs2 mem2 md2 W2 msv md3 Hpre HJ0 HK HP Hni
            Hio Hmo HC HJ);
          [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl)
          | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin
          | bs_rfin | bs_rfin
          | intros a Ha Hzv; apply KE; [exact Ha | intros Ha'; apply Hzv; unfold bs_zv; lia] | exact KP | ] end.
        exists (i + 2), (o + 1), (w ++ [y - 26]).
        split; [bsl_off E11|]. split; [bsl_off E26|].
        split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|].
        split; [lia|]. split; [lia|]. split; [lia|].
        split; [replace (Z.to_nat (i + 2)) with (S (S (Z.to_nat i))) by lia; apply (bs_firstn_S (bs_tb g) (S (Z.to_nat i)) Hil1); [exact (bs_firstn_S (bs_tb g) (Z.to_nat i) Hil Hnz ltac:(fold x; lia)) | fold y; lia]|].
        split; [rewrite length_app; cbn [length]; lia|].
        split; [exact Hr1|]. split; [exact Hr2|].
        apply (bs_want_snoc (w_H W2) mem2 _ (bs_F g pos) w (y - 26) Hwg).
        ++ intros a Ha. apply KE; lia.
        ++ replace (bs_F g pos + 32 + Z.of_nat (length w)) with (bs_F g pos + 32 + o) by lia. exact Vn.
        ++ lia.
    * (* the frame in the high zone *)
      destruct (bsl_state regs2 W2 mem2 (bs_q g) i o (bs_n g) (bs_F g pos) x y true true 46 46 0 255 (kHighMemBeg + 32) (2 ^ 47 - 24)
        R23 R14 R15 R21 R26 R22 R11 R19 R13 R12
        ltac:(lia) Hi ltac:(unfold bs_len in *; lia) ltac:(lia) (proj2 Hn) HF0 ltac:(lia) ltac:(lia) ltac:(lia) Hx8
        ltac:(lia) Hy8 Vx ltac:(intros _; exact Vy) (Hra1 2 ltac:(lia) ltac:(unfold bs_len in *; lia))
        (Ham1 2 ltac:(lia) ltac:(unfold bs_len in *; lia))
        ltac:(intros _; split; [exact Hon | exact (Hwant Hon 2 ltac:(lia) ltac:(unfold bs_len in *; lia))]))
        as (HS & SHOK).
      remember (Ereg regs2 (cw_extra (bsl_xs (bs_q g) i x (bs_F g pos) o y))) as E eqn:HEE.
      assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs2 r)
        by (intros nn r Hnn; subst E; apply ew_Ereg_nat; exact Hnn).
      assert (E34 : ew E 34 = Z_to_bv 64 x) by (subst E; exact (cw_ew_x regs2 (bsl_xs (bs_q g) i x (bs_F g pos) o y) 1)).
      assert (E35 : ew E 35 = Z_to_bv 64 (bs_F g pos + 32 + o))
        by (subst E; exact (cw_ew_x regs2 (bsl_xs (bs_q g) i x (bs_F g pos) o y) 2)).
      assert (U35 : bv_unsigned (ew E 35) = bs_F g pos + 32 + o) by (rewrite E35; apply unsigned_lit_small; lia).
      assert (E36 : ew E 36 = Z_to_bv 64 y) by (subst E; exact (cw_ew_x regs2 (bsl_xs (bs_q g) i x (bs_F g pos) o y) 3)).
      assert (E11 : ew E 11 = w64 o) by (rewrite (EE 11%nat 11%bv eq_refl); exact R11).
      assert (E19 : ew E 19 = w64 (bs_n g)) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
      assert (E26 : ew E 26 = w64 i) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
      assert (E12 : ew E 12 = w64 (bnot (bs_F g pos + 32))) by (rewrite (EE 12%nat 12%bv eq_refl); exact R12).
      assert (E13 : ew E 13 = w64 (bnot (bs_q g))) by (rewrite (EE 13%nat 13%bv eq_refl); exact R13).
      assert (E20 : ew E 20 = w64 (bs_ch g)) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
      assert (E23 : ew E 32 = getr regs2 23) by (subst E; rewrite cw_ew_SB; exact (eq_sym R23)).
      assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (a = bs_F g pos + 32 + o) ->
        aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
      cw_run_to bsl_awr 0x83ee8. ctk_keep bsl_kwr.
      cw_run_to bsl_awr 0x83ed4. ctk_keep bsl_kwr.
      cw_branch Hc1.
      all: lazymatch type of Hc1 with context [sv_denot ?Ev _] =>
        rewrite (bsl_c_geu Ev 11 19 o (bs_n g) ltac:(ewpeel; exact E11) ltac:(ewpeel; exact E19) ltac:(lia) ltac:(lia))
          in Hc1 end.
      { exfalso. destruct (Z.ltb_spec o (bs_n g)); [discriminate Hc1 | lia]. }
      cw_run_to bsl_awr 0x83ed4. ctk_keep bsl_kwr.
      cw_branch Hc2.
      all: lazymatch type of Hc2 with context [sv_denot ?Ev _] =>
        rewrite (bsl_c_ne Ev 34 x 46 ltac:(ewpeel; exact E34) ltac:(lia) ltac:(lia)) in Hc2 end.
      { exfalso. apply negb_true_iff, Z.eqb_neq in Hc2. exact (Hc2 Hx46). }
      cw_run_to bsl_awr 0x83ed4. ctk_keep bsl_kwr.
      cw_branch Hc3.
      all: lazymatch type of Hc3 with context [sv_denot ?Ev _] =>
        rewrite (bsl_c_digit Ev y ltac:(ewpeel; exact E36) Hy8) in Hc3 end.
      -- (* y is not a digit: the dot itself *)
        assert (Hnd : ~ (49 <= y <= 57))
          by (intros (Hy1 & Hy2); rewrite (proj2 (Z.leb_le _ _) Hy1), (proj2 (Z.leb_le _ _) Hy2) in Hc3; discriminate Hc3).
        assert (Hv : (if x <? 128 then x else 63) = x) by (rewrite (proj2 (Z.ltb_lt x 128) ltac:(lia)); reflexivity).
        cw_run_to bsl_awr 0x83ed4. ctk_keep bsl_kwr.
        bsl_vn Vn.
        lazymatch type of Vn with context [bv_unsigned (sv_denot ?Ev ?e) mod _] =>
          rewrite (bsl_byte_of Ev e (x) ltac:(apply (U_atom Ev 34 x); [ewpeel; exact E34 | lia]) ltac:(lia)) in Vn end.
        pose proof (bs_rest_plain g i o w Hi ltac:(lia) Hil ltac:(fold x; lia) ltac:(fold x y; lia) Hw1 Hw2) as Hrr.
        cbv zeta in Hrr. destruct Hrr as (Hr1 & Hr2). fold x in Hr1. rewrite Hv in Hr1.
        apply SRr_ret. cbv beta. left.
        lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- context [mkCfg _ ?md3] =>
          apply (bs_cut_close B MT LAWS g pos PC_L (P_L g pos fuel) ly2 S2 regs2 mem2 md2 W2 msv md3 Hpre HJ0 HK HP Hni
            Hio Hmo HC HJ);
          [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl)
          | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin
          | bs_rfin | bs_rfin
          | intros a Ha Hzv; apply KE; [exact Ha | intros Ha'; apply Hzv; unfold bs_zv; lia] | exact KP | ] end.
        exists (i + 1), (o + 1), (w ++ [x]).
        split; [bsl_off E11|]. split; [bsl_off E26|].
        split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|].
        split; [lia|]. split; [lia|]. split; [lia|].
        split; [replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia; exact (bs_firstn_S (bs_tb g) (Z.to_nat i) Hil Hnz ltac:(fold x; lia))|].
        split; [rewrite length_app; cbn [length]; lia|].
        split; [exact Hr1|]. split; [exact Hr2|].
        apply (bs_want_snoc (w_H W2) mem2 _ (bs_F g pos) w (x) Hwg).
        ++ intros a Ha. apply KE; lia.
        ++ replace (bs_F g pos + 32 + Z.of_nat (length w)) with (bs_F g pos + 32 + o) by lia. exact Vn.
        ++ lia.
      -- (* y is a digit: y - 26, two bytes *)
        assert (Hdg : 49 <= y <= 57)
          by (destruct (Z.leb_spec 49 y); destruct (Z.leb_spec y 57); cbn [andb negb] in Hc3; try discriminate Hc3; lia).
        cw_run_to bsl_awr 0x83ed4. ctk_keep bsl_kwr.
        bsl_vn Vn.
        lazymatch type of Vn with context [bv_unsigned (sv_denot ?Ev ?e) mod _] =>
          rewrite (bsl_byte_of Ev e (y - 26) ltac:(rewrite (U_atom_off Ev 36 y (-26) ltac:(ewpeel; exact E36) ltac:(lia) ltac:(lia)); lia) ltac:(lia)) in Vn end.
        pose proof (bs_rest_digit g i o w Hi ltac:(lia) Hil ltac:(fold x; lia) ltac:(fold y; lia) Hw1 Hw2) as (Hr1 & Hr2).
        fold y in Hr1.
        apply SRr_ret. cbv beta. left.
        lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- context [mkCfg _ ?md3] =>
          apply (bs_cut_close B MT LAWS g pos PC_L (P_L g pos fuel) ly2 S2 regs2 mem2 md2 W2 msv md3 Hpre HJ0 HK HP Hni
            Hio Hmo HC HJ);
          [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl)
          | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin
          | bs_rfin | bs_rfin
          | intros a Ha Hzv; apply KE; [exact Ha | intros Ha'; apply Hzv; unfold bs_zv; lia] | exact KP | ] end.
        exists (i + 2), (o + 1), (w ++ [y - 26]).
        split; [bsl_off E11|]. split; [bsl_off E26|].
        split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|].
        split; [lia|]. split; [lia|]. split; [lia|].
        split; [replace (Z.to_nat (i + 2)) with (S (S (Z.to_nat i))) by lia; apply (bs_firstn_S (bs_tb g) (S (Z.to_nat i)) Hil1); [exact (bs_firstn_S (bs_tb g) (Z.to_nat i) Hil Hnz ltac:(fold x; lia)) | fold y; lia]|].
        split; [rewrite length_app; cbn [length]; lia|].
        split; [exact Hr1|]. split; [exact Hr2|].
        apply (bs_want_snoc (w_H W2) mem2 _ (bs_F g pos) w (y - 26) Hwg).
        ++ intros a Ha. apply KE; lia.
        ++ replace (bs_F g pos + 32 + Z.of_nat (length w)) with (bs_F g pos + 32 + o) by lia. exact Vn.
        ++ lia.
  + (* any other byte *)
    destruct HFapp as (_ & [Hz | Hz]).
    * (* the frame in the low zone *)
      destruct (bsl_state regs2 W2 mem2 (bs_q g) i o (bs_n g) (bs_F g pos) x 0 false true 1 255 0 0 4096 (kLowShadowBeg - 24)
        R23 R14 R15 R21 R26 R22 R11 R19 R13 R12
        ltac:(lia) Hi ltac:(unfold bs_len in *; lia) ltac:(lia) (proj2 Hn) HF0 ltac:(lia) ltac:(lia) ltac:(lia) Hx8
        ltac:(lia) ltac:(lia) Vx ltac:(intros Hf; discriminate Hf) (Hra1 1 ltac:(lia) ltac:(unfold bs_len in *; lia))
        (Ham1 1 ltac:(lia) ltac:(unfold bs_len in *; lia))
        ltac:(intros _; split; [exact Hon | exact (Hwant Hon 1 ltac:(lia) ltac:(unfold bs_len in *; lia))]))
        as (HS & SHOK).
      remember (Ereg regs2 (cw_extra (bsl_xs (bs_q g) i x (bs_F g pos) o 0))) as E eqn:HEE.
      assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs2 r)
        by (intros nn r Hnn; subst E; apply ew_Ereg_nat; exact Hnn).
      assert (E34 : ew E 34 = Z_to_bv 64 x) by (subst E; exact (cw_ew_x regs2 (bsl_xs (bs_q g) i x (bs_F g pos) o 0) 1)).
      assert (E35 : ew E 35 = Z_to_bv 64 (bs_F g pos + 32 + o))
        by (subst E; exact (cw_ew_x regs2 (bsl_xs (bs_q g) i x (bs_F g pos) o 0) 2)).
      assert (U35 : bv_unsigned (ew E 35) = bs_F g pos + 32 + o) by (rewrite E35; apply unsigned_lit_small; lia).
      assert (E36 : ew E 36 = Z_to_bv 64 0) by (subst E; exact (cw_ew_x regs2 (bsl_xs (bs_q g) i x (bs_F g pos) o 0) 3)).
      assert (E11 : ew E 11 = w64 o) by (rewrite (EE 11%nat 11%bv eq_refl); exact R11).
      assert (E19 : ew E 19 = w64 (bs_n g)) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
      assert (E26 : ew E 26 = w64 i) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
      assert (E12 : ew E 12 = w64 (bnot (bs_F g pos + 32))) by (rewrite (EE 12%nat 12%bv eq_refl); exact R12).
      assert (E13 : ew E 13 = w64 (bnot (bs_q g))) by (rewrite (EE 13%nat 13%bv eq_refl); exact R13).
      assert (E20 : ew E 20 = w64 (bs_ch g)) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
      assert (E23 : ew E 32 = getr regs2 23) by (subst E; rewrite cw_ew_SB; exact (eq_sym R23)).
      assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (a = bs_F g pos + 32 + o) ->
        aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
      cw_run_to bsl_awr 0x83ee8. ctk_keep bsl_kwr.
      cw_run_to bsl_awr 0x83ed4. ctk_keep bsl_kwr.
      cw_branch Hc1.
      all: lazymatch type of Hc1 with context [sv_denot ?Ev _] =>
        rewrite (bsl_c_geu Ev 11 19 o (bs_n g) ltac:(ewpeel; exact E11) ltac:(ewpeel; exact E19) ltac:(lia) ltac:(lia))
          in Hc1 end.
      { exfalso. destruct (Z.ltb_spec o (bs_n g)); [discriminate Hc1 | lia]. }
      cw_run_to bsl_awr 0x83ed4. ctk_keep bsl_kwr.
      cw_branch Hc2.
      all: lazymatch type of Hc2 with context [sv_denot ?Ev _] =>
        rewrite (bsl_c_ne Ev 34 x 46 ltac:(ewpeel; exact E34) ltac:(lia) ltac:(lia)) in Hc2 end.
      2: { exfalso. apply negb_false_iff, Z.eqb_eq in Hc2. exact (Hx46 Hc2). }
      apply negb_true_iff, Z.eqb_neq in Hc2.
      cw_run_to bsl_awr 0x83ed4. ctk_keep bsl_kwr.
      cw_branch Hc3.
      all: lazymatch type of Hc3 with context [sv_denot ?Ev _] =>
        rewrite (bsl_c_ge56 Ev x ltac:(ewpeel; exact E34) Hx8) in Hc3 end.
      -- (* x < 128: the byte itself *)
        apply Z.ltb_lt in Hc3.
        assert (Hv : (if x <? 128 then x else 63) = x) by (rewrite (proj2 (Z.ltb_lt x 128) Hc3); reflexivity).
        cw_run_to bsl_awr 0x83ed4. ctk_keep bsl_kwr.
        bsl_vn Vn.
        lazymatch type of Vn with context [bv_unsigned (sv_denot ?Ev ?e) mod _] =>
          rewrite (bsl_byte_of Ev e (x) ltac:(apply (U_atom Ev 34 x); [ewpeel; exact E34 | lia]) ltac:(lia)) in Vn end.
        pose proof (bs_rest_plain g i o w Hi ltac:(lia) Hil ltac:(fold x; lia) ltac:(fold x; lia) Hw1 Hw2) as Hrr.
        cbv zeta in Hrr. destruct Hrr as (Hr1 & Hr2). fold x in Hr1. rewrite Hv in Hr1.
        apply SRr_ret. cbv beta. left.
        lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- context [mkCfg _ ?md3] =>
          apply (bs_cut_close B MT LAWS g pos PC_L (P_L g pos fuel) ly2 S2 regs2 mem2 md2 W2 msv md3 Hpre HJ0 HK HP Hni
            Hio Hmo HC HJ);
          [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl)
          | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin
          | bs_rfin | bs_rfin
          | intros a Ha Hzv; apply KE; [exact Ha | intros Ha'; apply Hzv; unfold bs_zv; lia] | exact KP | ] end.
        exists (i + 1), (o + 1), (w ++ [x]).
        split; [bsl_off E11|]. split; [bsl_off E26|].
        split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|].
        split; [lia|]. split; [lia|]. split; [lia|].
        split; [replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia; exact (bs_firstn_S (bs_tb g) (Z.to_nat i) Hil Hnz ltac:(fold x; lia))|].
        split; [rewrite length_app; cbn [length]; lia|].
        split; [exact Hr1|]. split; [exact Hr2|].
        apply (bs_want_snoc (w_H W2) mem2 _ (bs_F g pos) w (x) Hwg).
        ++ intros a Ha. apply KE; lia.
        ++ replace (bs_F g pos + 32 + Z.of_nat (length w)) with (bs_F g pos + 32 + o) by lia. exact Vn.
        ++ lia.
      -- (* x >= 128: '?' *)
        apply Z.ltb_ge in Hc3.
        assert (Hv : (if x <? 128 then x else 63) = 63) by (rewrite (proj2 (Z.ltb_ge x 128) Hc3); reflexivity).
        cw_run_to bsl_awr 0x83ed4. ctk_keep bsl_kwr.
        bsl_vn Vn.
        lazymatch type of Vn with context [bv_unsigned (sv_denot ?Ev ?e) mod _] =>
          rewrite (bsl_byte_of Ev e (63) ltac:(apply (U_lit Ev 63); lia) ltac:(lia)) in Vn end.
        pose proof (bs_rest_plain g i o w Hi ltac:(lia) Hil ltac:(fold x; lia) ltac:(fold x; lia) Hw1 Hw2) as Hrr.
        cbv zeta in Hrr. destruct Hrr as (Hr1 & Hr2). fold x in Hr1. rewrite Hv in Hr1.
        apply SRr_ret. cbv beta. left.
        lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- context [mkCfg _ ?md3] =>
          apply (bs_cut_close B MT LAWS g pos PC_L (P_L g pos fuel) ly2 S2 regs2 mem2 md2 W2 msv md3 Hpre HJ0 HK HP Hni
            Hio Hmo HC HJ);
          [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl)
          | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin
          | bs_rfin | bs_rfin
          | intros a Ha Hzv; apply KE; [exact Ha | intros Ha'; apply Hzv; unfold bs_zv; lia] | exact KP | ] end.
        exists (i + 1), (o + 1), (w ++ [63]).
        split; [bsl_off E11|]. split; [bsl_off E26|].
        split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|].
        split; [lia|]. split; [lia|]. split; [lia|].
        split; [replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia; exact (bs_firstn_S (bs_tb g) (Z.to_nat i) Hil Hnz ltac:(fold x; lia))|].
        split; [rewrite length_app; cbn [length]; lia|].
        split; [exact Hr1|]. split; [exact Hr2|].
        apply (bs_want_snoc (w_H W2) mem2 _ (bs_F g pos) w (63) Hwg).
        ++ intros a Ha. apply KE; lia.
        ++ replace (bs_F g pos + 32 + Z.of_nat (length w)) with (bs_F g pos + 32 + o) by lia. exact Vn.
        ++ lia.
    * (* the frame in the high zone *)
      destruct (bsl_state regs2 W2 mem2 (bs_q g) i o (bs_n g) (bs_F g pos) x 0 false true 1 255 0 0 (kHighMemBeg + 32) (2 ^ 47 - 24)
        R23 R14 R15 R21 R26 R22 R11 R19 R13 R12
        ltac:(lia) Hi ltac:(unfold bs_len in *; lia) ltac:(lia) (proj2 Hn) HF0 ltac:(lia) ltac:(lia) ltac:(lia) Hx8
        ltac:(lia) ltac:(lia) Vx ltac:(intros Hf; discriminate Hf) (Hra1 1 ltac:(lia) ltac:(unfold bs_len in *; lia))
        (Ham1 1 ltac:(lia) ltac:(unfold bs_len in *; lia))
        ltac:(intros _; split; [exact Hon | exact (Hwant Hon 1 ltac:(lia) ltac:(unfold bs_len in *; lia))]))
        as (HS & SHOK).
      remember (Ereg regs2 (cw_extra (bsl_xs (bs_q g) i x (bs_F g pos) o 0))) as E eqn:HEE.
      assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs2 r)
        by (intros nn r Hnn; subst E; apply ew_Ereg_nat; exact Hnn).
      assert (E34 : ew E 34 = Z_to_bv 64 x) by (subst E; exact (cw_ew_x regs2 (bsl_xs (bs_q g) i x (bs_F g pos) o 0) 1)).
      assert (E35 : ew E 35 = Z_to_bv 64 (bs_F g pos + 32 + o))
        by (subst E; exact (cw_ew_x regs2 (bsl_xs (bs_q g) i x (bs_F g pos) o 0) 2)).
      assert (U35 : bv_unsigned (ew E 35) = bs_F g pos + 32 + o) by (rewrite E35; apply unsigned_lit_small; lia).
      assert (E36 : ew E 36 = Z_to_bv 64 0) by (subst E; exact (cw_ew_x regs2 (bsl_xs (bs_q g) i x (bs_F g pos) o 0) 3)).
      assert (E11 : ew E 11 = w64 o) by (rewrite (EE 11%nat 11%bv eq_refl); exact R11).
      assert (E19 : ew E 19 = w64 (bs_n g)) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
      assert (E26 : ew E 26 = w64 i) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
      assert (E12 : ew E 12 = w64 (bnot (bs_F g pos + 32))) by (rewrite (EE 12%nat 12%bv eq_refl); exact R12).
      assert (E13 : ew E 13 = w64 (bnot (bs_q g))) by (rewrite (EE 13%nat 13%bv eq_refl); exact R13).
      assert (E20 : ew E 20 = w64 (bs_ch g)) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
      assert (E23 : ew E 32 = getr regs2 23) by (subst E; rewrite cw_ew_SB; exact (eq_sym R23)).
      assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (a = bs_F g pos + 32 + o) ->
        aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
      cw_run_to bsl_awr 0x83ee8. ctk_keep bsl_kwr.
      cw_run_to bsl_awr 0x83ed4. ctk_keep bsl_kwr.
      cw_branch Hc1.
      all: lazymatch type of Hc1 with context [sv_denot ?Ev _] =>
        rewrite (bsl_c_geu Ev 11 19 o (bs_n g) ltac:(ewpeel; exact E11) ltac:(ewpeel; exact E19) ltac:(lia) ltac:(lia))
          in Hc1 end.
      { exfalso. destruct (Z.ltb_spec o (bs_n g)); [discriminate Hc1 | lia]. }
      cw_run_to bsl_awr 0x83ed4. ctk_keep bsl_kwr.
      cw_branch Hc2.
      all: lazymatch type of Hc2 with context [sv_denot ?Ev _] =>
        rewrite (bsl_c_ne Ev 34 x 46 ltac:(ewpeel; exact E34) ltac:(lia) ltac:(lia)) in Hc2 end.
      2: { exfalso. apply negb_false_iff, Z.eqb_eq in Hc2. exact (Hx46 Hc2). }
      apply negb_true_iff, Z.eqb_neq in Hc2.
      cw_run_to bsl_awr 0x83ed4. ctk_keep bsl_kwr.
      cw_branch Hc3.
      all: lazymatch type of Hc3 with context [sv_denot ?Ev _] =>
        rewrite (bsl_c_ge56 Ev x ltac:(ewpeel; exact E34) Hx8) in Hc3 end.
      -- (* x < 128: the byte itself *)
        apply Z.ltb_lt in Hc3.
        assert (Hv : (if x <? 128 then x else 63) = x) by (rewrite (proj2 (Z.ltb_lt x 128) Hc3); reflexivity).
        cw_run_to bsl_awr 0x83ed4. ctk_keep bsl_kwr.
        bsl_vn Vn.
        lazymatch type of Vn with context [bv_unsigned (sv_denot ?Ev ?e) mod _] =>
          rewrite (bsl_byte_of Ev e (x) ltac:(apply (U_atom Ev 34 x); [ewpeel; exact E34 | lia]) ltac:(lia)) in Vn end.
        pose proof (bs_rest_plain g i o w Hi ltac:(lia) Hil ltac:(fold x; lia) ltac:(fold x; lia) Hw1 Hw2) as Hrr.
        cbv zeta in Hrr. destruct Hrr as (Hr1 & Hr2). fold x in Hr1. rewrite Hv in Hr1.
        apply SRr_ret. cbv beta. left.
        lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- context [mkCfg _ ?md3] =>
          apply (bs_cut_close B MT LAWS g pos PC_L (P_L g pos fuel) ly2 S2 regs2 mem2 md2 W2 msv md3 Hpre HJ0 HK HP Hni
            Hio Hmo HC HJ);
          [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl)
          | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin
          | bs_rfin | bs_rfin
          | intros a Ha Hzv; apply KE; [exact Ha | intros Ha'; apply Hzv; unfold bs_zv; lia] | exact KP | ] end.
        exists (i + 1), (o + 1), (w ++ [x]).
        split; [bsl_off E11|]. split; [bsl_off E26|].
        split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|].
        split; [lia|]. split; [lia|]. split; [lia|].
        split; [replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia; exact (bs_firstn_S (bs_tb g) (Z.to_nat i) Hil Hnz ltac:(fold x; lia))|].
        split; [rewrite length_app; cbn [length]; lia|].
        split; [exact Hr1|]. split; [exact Hr2|].
        apply (bs_want_snoc (w_H W2) mem2 _ (bs_F g pos) w (x) Hwg).
        ++ intros a Ha. apply KE; lia.
        ++ replace (bs_F g pos + 32 + Z.of_nat (length w)) with (bs_F g pos + 32 + o) by lia. exact Vn.
        ++ lia.
      -- (* x >= 128: '?' *)
        apply Z.ltb_ge in Hc3.
        assert (Hv : (if x <? 128 then x else 63) = 63) by (rewrite (proj2 (Z.ltb_ge x 128) Hc3); reflexivity).
        cw_run_to bsl_awr 0x83ed4. ctk_keep bsl_kwr.
        bsl_vn Vn.
        lazymatch type of Vn with context [bv_unsigned (sv_denot ?Ev ?e) mod _] =>
          rewrite (bsl_byte_of Ev e (63) ltac:(apply (U_lit Ev 63); lia) ltac:(lia)) in Vn end.
        pose proof (bs_rest_plain g i o w Hi ltac:(lia) Hil ltac:(fold x; lia) ltac:(fold x; lia) Hw1 Hw2) as Hrr.
        cbv zeta in Hrr. destruct Hrr as (Hr1 & Hr2). fold x in Hr1. rewrite Hv in Hr1.
        apply SRr_ret. cbv beta. left.
        lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- context [mkCfg _ ?md3] =>
          apply (bs_cut_close B MT LAWS g pos PC_L (P_L g pos fuel) ly2 S2 regs2 mem2 md2 W2 msv md3 Hpre HJ0 HK HP Hni
            Hio Hmo HC HJ);
          [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl)
          | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin
          | bs_rfin | bs_rfin
          | intros a Ha Hzv; apply KE; [exact Ha | intros Ha'; apply Hzv; unfold bs_zv; lia] | exact KP | ] end.
        exists (i + 1), (o + 1), (w ++ [63]).
        split; [bsl_off E11|]. split; [bsl_off E26|].
        split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|].
        split; [lia|]. split; [lia|]. split; [lia|].
        split; [replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia; exact (bs_firstn_S (bs_tb g) (Z.to_nat i) Hil Hnz ltac:(fold x; lia))|].
        split; [rewrite length_app; cbn [length]; lia|].
        split; [exact Hr1|]. split; [exact Hr2|].
        apply (bs_want_snoc (w_H W2) mem2 _ (bs_F g pos) w (63) Hwg).
        ++ intros a Ha. apply KE; lia.
        ++ replace (bs_F g pos + 32 + Z.of_nat (length w)) with (bs_F g pos + 32 + o) by lia. exact Vn.
        ++ lia.
Qed.
End s.
