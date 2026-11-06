(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACh9.v:86-90
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203, 332-335, 358-363, 460-463 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:1593-1596, 1605-1615 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:2082-2086 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan build
   (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:393-396. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_catalogue_defect.v, with its module paths and module names changed; 379 of its 457 lines of code are new or changed and 577 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn YA0o YCbm YA0q YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_rival_kind_of_c.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Lemma rk_vm_mod32 : forall segs (m : word -> option byte) a v,
val_mem segs m a 4 v -> val_mem segs m a 4 (v mod 2 ^ 32).
Proof.
intros segs m a v H k Hk. rewrite (H k Hk). unfold YO0f.le_byte. change (8 * Z.of_nat 4) with 32.
rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma rk_U_sx_u : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
U E (SExt true 32 (SOff n 0)) = if v <? 2147483648 then v else v + 18446744069414584320.
Proof.
intros E n v Hn Hv. rewrite U_SExt, (U_atom E n v Hn) by lia. cbv beta iota.
unfold zcanon, M64, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (Z.of_N 32) with 32. change (2 ^ 32) with 4294967296. change (Z.div 4294967296 2) with 2147483648.
change (2 ^ 64) with 18446744073709551616.
rewrite (Z.mod_small v 4294967296) by lia.
destruct (Z.ltb_spec v 2147483648) as [Hl|Hl].
- rewrite (Z.mod_small (v + 2147483648) 4294967296) by lia.
  rewrite Z.mod_small by lia. lia.
- rewrite <- (Z.mod_unique (v + 2147483648) 4294967296 1 (v + 2147483648 - 4294967296)) by lia.
  rewrite <- (Z.mod_unique (v + 2147483648 - 4294967296 - 2147483648) 18446744073709551616 (-1) (v + 18446744069414584320)) by lia.
  reflexivity.
Qed.
Lemma rk_U_sx_s : forall E n v, ew E n = Z_to_bv 64 (v mod 2 ^ 32) -> -2 ^ 31 <= v < 2 ^ 31 ->
U E (SExt true 32 (SOff n 0)) = if v <? 0 then v + 18446744073709551616 else v.
Proof.
intros E n v Hn Hv. rewrite (rk_U_sx_u E n (v mod 2 ^ 32) Hn) by (apply Z.mod_pos_bound; lia).
destruct (Z.ltb_spec v 0) as [Hl|Hl].
- rewrite <- (Z.mod_unique v (2 ^ 32) (-1) (v + 4294967296)) by lia.
  destruct (Z.ltb_spec (v + 4294967296) 2147483648); lia.
- rewrite Z.mod_small by lia. destruct (Z.ltb_spec v 2147483648); lia.
Qed.
Lemma rk_U_off_m1 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 8 ->
U E (SOff n (-1)) = if v =? 0 then 18446744073709551615 else v - 1.
Proof.
intros E n v Hn Hv. rewrite U_SOff, Hn, unsigned_lit_small by lia. unfold zcanon, M64.
destruct (Z.eqb_spec v 0) as [->|Hl].
- reflexivity.
- apply Z.mod_small. lia.
Qed.
Lemma rk_agree_ewset : forall E0 E n v, (32 <= n)%nat -> env_agree 32 E0 E -> env_agree 32 E0 (ewset E n v).
Proof.
intros E0 E n v Hn [HA HD]. split; [intros i Hi; rewrite ew_ewset_other by lia; apply HA; exact Hi | exact HD].
Qed.
Ltac rk_upd_mem Usp WS :=
repeat match goal with
| H : frame_of _ _ (mrestrict _ _) _ |- _ => clear H
| H : mem_grows _ _ |- _ => clear H
end;
lazymatch goal with
| HF : frame_of ?Ex ?rs ?m1 ?m2, HM : forall x : word, ~ (?lo <= bv_unsigned x < ?hi) -> ?m1 x = ?m0 x |- _ =>
  let HM' := fresh "HM" in
  assert (HM' : forall x : word, ~ (lo <= bv_unsigned x < hi) -> m2 x = m0 x);
  [ let x := fresh "x" in let Hx := fresh "Hx" in
    intros x Hx; rewrite (HF x); [exact (HM x Hx)|];
    let rs' := eval vm_compute in rs in change rs with rs';
    let rg := fresh "rg" in let Hrg := fresh "Hrg" in let Hin := fresh "Hin" in
    intros (rg & Hrg & Hin); cbn [In] in Hrg;
    repeat match type of Hrg with _ \/ _ => destruct Hrg as [Hrg | Hrg] end;
    first [ contradiction Hrg
          | subst rg; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hin;
            cbn [ew ewset Nat.eqb] in Hin; rewrite ?ew_ewset_other in Hin by lia; rewrite ?Usp in Hin;
            rewrite WS in Hx; lia ]
  | clear HM HF; rename HM' into HM ]
end.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
#[local] Notation VAL := (@pa_val _ disco_listing PI).
Definition SB_RK : Z := 0x7fff8000.
Definition RBx : sv := SOff 36 0.
Definition RBx0 : sv := SLit SB_RK.
Definition RBspan : Z * Z := (SB_RK, SB_RK + 2 ^ 44 - 1).
Definition rk_regions : smem :=
[ stack_region 16; got_regionP; bcell_regionP 36;
YP09.mkRegion (Some 10%nat) 8 24 0 0 [YP09.mkChunk 8 (CVal 4 (SOff 32 0)); YP09.mkChunk 12 (CVal 1 (SOff 33 0));
YP09.mkChunk 16 (CVal 1 (SOff 34 0)); YP09.mkChunk 20 (CVal 4 (SOff 35 0))] ].
Definition rk_facts : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4088 (140737479966720 - 24) 3);
(32%nat, mkAF 0 4294967295 0); (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 4294967295 0);
(36%nat, mkAF SB_RK SB_RK 0) ] [] [].
Definition ss_rk : sstate := mkSS AF_reac_rival_kind_of sr_atoms rk_regions None rk_facts.
Definition rk_SH : list shent := [ mkSHE 10 8 24 ].
Definition ss_rk0 : sstate :=
mkSS AF_reac_rival_kind_of sr_atoms [stack_region 16] None
(mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 0 0 0)] [] []).
Definition rk_extra (r d s c : Z) : list word := map (Z_to_bv 64) [r mod 2 ^ 32; d; s; c; SB_RK].
Definition ERK (regs : bvmap 5 word) (r d s c : Z) : env := Eimg (Ereg regs (rk_extra r d s c)).
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Definition REAC_RIVAL_KIND_OF_STK : Z := 16 + ESTACK.
Definition treac_rival_kind_of_post (fq : YK11.FPState) (regs : bvmap 5 word) ly S (W : world SEGS) mem md
  (e r d s c : Z) : world SEGS -> config -> Prop :=
  apost_base (fx := fq) SEGS B REAC_RIVAL_KIND_OF_STK [] regs ly S W mem md 0
    (fun ly' S' W' regs' mem' md' =>
       getr regs' 10 = w64 (if e =? 0 then 0 else reac_rival_kind_model d r s c) /\
       Permutation (ablocks B ly' S') (ablocks B ly S) /\ W' = W /\
       (forall a : word, ~ (spZ regs - REAC_RIVAL_KIND_OF_STK <= bv_unsigned a < spZ regs) -> mem' a = mem a)).
Definition treac_rival_kind_of_spec : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (e r d s c : Z),
  afn_pre SEGS B REAC_RIVAL_KIND_OF_STK ly S W regs mem md ch ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  getr regs 10 = w64 e -> 0 <= e < 2 ^ 64 -> e mod 8 = 0 ->
  (e <> 0 ->
     e + 24 <= 2 ^ 63 /\ in_app (e + 8) 16 /\ off_img (e + 8) 16 /\
     range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (e + 8) 16 /\
     (forall a, e + 8 <= a < e + 24 -> apresent (w_H W) mem a) /\
     -2 ^ 31 <= r < 2 ^ 31 /\ 0 <= d < 2 ^ 8 /\ 0 <= s < 2 ^ 8 /\ 0 <= c < 2 ^ 32 /\
     val_mem SEGS (mrestrict (w_H W) mem) (e + 8) 4 r /\
     val_mem SEGS (mrestrict (w_H W) mem) (e + 12) 1 d /\
     val_mem SEGS (mrestrict (w_H W) mem) (e + 16) 1 s /\
     val_mem SEGS (mrestrict (w_H W) mem) (e + 20) 4 c) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_rival_kind_of) regs mem md)
    (treac_rival_kind_of_post fq regs ly S W mem md e r d s c).
Section w. Context {fx : YK11.FPState}.
Let HBgot := pal_got_shadow B TL.
Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_disco) (PI := PI).
Lemma rk_entry : forall ly S W (regs : bvmap 5 word) mem md ch (e r d s c : Z),
afn_pre SEGS B REAC_RIVAL_KIND_OF_STK ly S W regs mem md ch ->
getr regs 10 = w64 e -> e mod 8 = 0 -> in_app (e + 8) 16 -> off_img (e + 8) 16 ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (e + 8) 16 ->
-2 ^ 31 <= r < 2 ^ 31 -> 0 <= d < 2 ^ 8 -> 0 <= s < 2 ^ 8 -> 0 <= c < 2 ^ 32 ->
val_mem SEGS (mrestrict (w_H W) mem) (e + 8) 4 r ->
val_mem SEGS (mrestrict (w_H W) mem) (e + 12) 1 d ->
val_mem SEGS (mrestrict (w_H W) mem) (e + 16) 1 s ->
val_mem SEGS (mrestrict (w_H W) mem) (e + 20) 4 c ->
st_ok_pi SEGS VAL (ERK regs r d s c) ss_rk
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_rival_kind_of)) mem (seg_rom SEGS)))
/\ sh_ok SEGS RBx rk_SH (ERK regs r d s c) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch e r d s c HPRE H10 He8 Happ Hoff Hsh Rr Rd Rs Rc Vr Vd Vs Vc.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_RIVAL_KIND_OF_STK = 4112) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 66 ltac:(unfold disco_nobj; lia)) as HcellR.
pose proof (pa_obj_img 1 ltac:(unfold disco_nobj; lia)) as HgotR.
pose proof (pal_got_cell B TL) as HgcD.
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HcellR, HgotR.
assert (HeR : 4088 <= e <= 140737479966720 - 24).
{ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. lia. }
pose proof (rk_vm_mod32 SEGS _ _ _ Vr) as Vru.
assert (Rru : 0 <= r mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
set (ru := r mod 2 ^ 32) in Vru, Rru.
rewrite restrict_mkst_fx.
set (E := ERK regs r d s c).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (rk_extra r d s c)) n)
by (intros n Hn; subst E; unfold ERK; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 e) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 ru) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 d) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 s) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 c) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 SB_RK) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (Eg : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; unfold ERK; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Ec : ew E (A_OBJ 66) = Z_to_bv 64 (VAL (A_OBJ 66))) by (subst E; unfold ERK; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_rk. apply pa_entry_st_ok_full.
  + exact (regs_ok_Eimg_Ereg regs (rk_extra r d s c)).
  + vm_compute. reflexivity.
  + unfold rk_regions, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eg) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 66) 0) (VAL (A_OBJ 66)));
      [cbn [sv_denot]; rewrite Ec, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VB (A_OBJ 66) (VAL (A_OBJ 66)) Ec) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 66)) 0 8 RBx SB_RK);
      [cbn [sv_denot RBx]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB_RK; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * rewrite (VB 10%nat e E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
      -- apply (chunk_ok_val SEGS E _ e 8 4 _ ru); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vru].
      -- apply (chunk_ok_val SEGS E _ e 12 1 _ d); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vd].
      -- apply (chunk_ok_val SEGS E _ e 16 1 _ s); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vs].
      -- apply (chunk_ok_val SEGS E _ e 20 4 _ c); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vc].
  + apply pairwise_disjoint_of_extents. unfold rk_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 10%nat e E10) by lia.
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eg) by lia. rewrite (VB (A_OBJ 66) (VAL (A_OBJ 66)) Ec) by lia.
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hoff. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
    revert Hoff Happ HeR HgotR HcellR HgcD Hslo Hceil Hstk0 Hshi H47 C1 WS. clear. intros.
    repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [rk_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E32, E33, E34, E35, E36, !unsigned_lit_small by (unfold SB_RK; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hal16 Hslo Hceil Hstk0 Hshi H47 C1 WS HeR He8 Rru Rd Rs Rc. clear. unfold SB_RK. intros.
    repeat split; lia.
- unfold sh_ok, rk_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E RBx 10 (e + 8) 16 e 8 24 Hsh).
  + unfold U, RBx. cbn [sv_denot]. rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold SB_RK; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
Qed.
Lemma rk_entry0 : forall ly S W (regs : bvmap 5 word) mem md ch,
afn_pre SEGS B REAC_RIVAL_KIND_OF_STK ly S W regs mem md ch -> getr regs 10 = w64 0 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) ss_rk0
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_rival_kind_of)) mem (seg_rom SEGS)))
/\ sh_ok SEGS RBx0 [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch HPRE H10. split; [|constructor].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_RIVAL_KIND_OF_STK = 4112) by reflexivity.
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs [])) 2) = spZ regs)
by (rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (U10 : bv_unsigned (ew (Eimg (Ereg regs [])) 10) = 0)
by (rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), H10; reflexivity).
rewrite restrict_mkst_fx. unfold ss_rk0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
- split; exact I.
- split; [|split; exact I].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp, U10.
  change (2 ^ 4) with 16. rewrite Z.pow_0_r, Z.mod_1_r.
  split; [split; [lia|]; split; [exact Hal16 | lia]|]. split; [lia | exact I].
Qed.
Lemma rk_walk0 : forall ly S W (regs : bvmap 5 word) mem md ch (r d s c : Z),
afn_pre SEGS B REAC_RIVAL_KIND_OF_STK ly S W regs mem md ch -> getr regs 10 = w64 0 ->
SRr SEGS W (cfg_at SEGS (BASE + AF_reac_rival_kind_of) regs mem md)
(treac_rival_kind_of_post fx regs ly S W mem md 0 r d s c).
Proof.
intros ly S W regs mem md ch r d s c HPRE H10.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
destruct (rk_entry0 ly S W regs mem md ch HPRE H10) as [HS SHOK].
pose proof (ajournal_init SEGS B REAC_RIVAL_KIND_OF_STK [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 0) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (WS : REAC_RIVAL_KIND_OF_STK = 4112) by reflexivity.
assert (HM : forall x : word, ~ (spZ regs - REAC_RIVAL_KIND_OF_STK <= bv_unsigned x < spZ regs) -> mem x = mem x)
by (intros; reflexivity).
clear HE.
unfold cfg_at. change (w64 (BASE + AF_reac_rival_kind_of)) with (Z_to_bv 64 (BASE + AF_reac_rival_kind_of)).
let leaf0 := idtac;
lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
let R10 := fresh "R10" in let R1 := fresh "R1" in
prreg HS (10%bv : bv 5) R10; prreg HS (1%bv : bv 5) R1;
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
let mat' := fresh "mat" in intros mat';
unfold treac_rival_kind_of_post; apply apost_base_same_fx;
exists ly, S, (ms_regs msc), (ms_mem msc); eexists;
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|];
split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [] HS);
  [repeat (apply rk_agree_ewset; [lia|]); exact HAE | vm_compute; reflexivity]|];
split; [rewrite R10; rewrite ?E10; reflexivity | split; [apply Permutation_refl | split; [reflexivity | exact HM]]]
end in
let bcontra := idtac;
lazymatch goal with Hc : branch_taken _ _ _ = false |- _ =>
  rewrite branch_eq_U, (U_atom _ 10 0 E10), U_lit in Hc by lia; apply Z.eqb_neq in Hc; lia end in
let rec go0 := idtac;
lazymatch goal with HS : st_ok_pi _ _ _ ?ss0 _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
paj_run_tok RUN HS HJ SHOK RBspan;
[first [apply awr_ok_nil | awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp] |];
rk_upd_mem Usp WS;
lazymatch goal with
| HS' : st_ok_pi _ _ _ ?ss _, SHOK' : sh_ok _ _ _ _ _ |- _ =>
let K := eval vm_compute in (run_K A_LIM RBx0 (@nil shent) ss) in
let why := lazymatch paj_tables RUN with (?tpi, ?tw) =>
  psym_why_tok tpi tw K RBx0 RBspan (@nil shent) (start K RBx0 RBspan (@nil shent) ss) end in
lazymatch why with
| SR_jalr _ => leaf0
| SR_branch _ _ _ => psrr_branch_tok RUN BR HS' SHOK' RBspan;
  [first [exfalso; bcontra | go0] | first [exfalso; bcontra | go0]]
| _ => let pc := eval vm_compute in (ss_pc ss) in fail 100 "STUCK0" pc why
end
end end in
go0.
Qed.
Lemma rk_walk1 : forall ly S W (regs : bvmap 5 word) mem md ch (e r d s c : Z),
afn_pre SEGS B REAC_RIVAL_KIND_OF_STK ly S W regs mem md ch ->
getr regs 10 = w64 e -> e mod 8 = 0 -> e <> 0 -> in_app (e + 8) 16 -> off_img (e + 8) 16 ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (e + 8) 16 ->
-2 ^ 31 <= r < 2 ^ 31 -> 0 <= d < 2 ^ 8 -> 0 <= s < 2 ^ 8 -> 0 <= c < 2 ^ 32 ->
val_mem SEGS (mrestrict (w_H W) mem) (e + 8) 4 r ->
val_mem SEGS (mrestrict (w_H W) mem) (e + 12) 1 d ->
val_mem SEGS (mrestrict (w_H W) mem) (e + 16) 1 s ->
val_mem SEGS (mrestrict (w_H W) mem) (e + 20) 4 c ->
SRr SEGS W (cfg_at SEGS (BASE + AF_reac_rival_kind_of) regs mem md)
(treac_rival_kind_of_post fx regs ly S W mem md e r d s c).
Proof.
intros ly S W regs mem md ch e r d s c HPRE H10 He8 Hne Happ Hoff Hsh Rr Rd Rs Rc Vr Vd Vs Vc.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
destruct (rk_entry ly S W regs mem md ch e r d s c HPRE H10 He8 Happ Hoff Hsh Rr Rd Rs Rc Vr Vd Vs Vc) as [HS SHOK].
pose proof (ajournal_init SEGS B REAC_RIVAL_KIND_OF_STK [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
remember (ERK regs r d s c) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold ERK; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (rk_extra r d s c)) n)
by (intros n Hn; subst E; unfold ERK; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 (r mod 2 ^ 32)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 d) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 s) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 c) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (rk_extra r d s c)) E)
by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (WS : REAC_RIVAL_KIND_OF_STK = 4112) by reflexivity.
assert (HM : forall x : word, ~ (spZ regs - REAC_RIVAL_KIND_OF_STK <= bv_unsigned x < spZ regs) -> mem x = mem x)
by (intros; reflexivity).
clear HE EL.
unfold cfg_at. change (w64 (BASE + AF_reac_rival_kind_of)) with (Z_to_bv 64 (BASE + AF_reac_rival_kind_of)).
let bnorm := idtac;
repeat match goal with
| H : branch_taken _ _ _ = _ |- _ =>
  first [rewrite branch_eq_U in H | rewrite branch_ne_U in H | rewrite branch_ltu_U in H | rewrite branch_geu_U in H];
  repeat match type of H with
  | context [U ?Ex (SExt true 32 (SOff 32 0))] =>
    let X := fresh "X" in assert (X : ew Ex 32 = Z_to_bv 64 (r mod 2 ^ 32)) by (rewrite ?ew_ewset_other by lia; exact E32);
    rewrite (rk_U_sx_s Ex 32 r X Rr) in H; clear X
  | context [U ?Ex (SExt true 32 (SOff 35 0))] =>
    let X := fresh "X" in assert (X : ew Ex 35 = Z_to_bv 64 c) by (rewrite ?ew_ewset_other by lia; exact E35);
    rewrite (rk_U_sx_u Ex 35 c X Rc) in H; clear X
  | context [U ?Ex (SOff 34 (-1))] =>
    let X := fresh "X" in assert (X : ew Ex 34 = Z_to_bv 64 s) by (rewrite ?ew_ewset_other by lia; exact E34);
    rewrite (rk_U_off_m1 Ex 34 s X Rs) in H; clear X
  | context [U ?Ex (SOff 33 0)] =>
    let X := fresh "X" in assert (X : ew Ex 33 = Z_to_bv 64 d) by (rewrite ?ew_ewset_other by lia; exact E33);
    rewrite (U_atom Ex 33 d X) in H by lia; clear X
  | context [U ?Ex (SOff 34 0)] =>
    let X := fresh "X" in assert (X : ew Ex 34 = Z_to_bv 64 s) by (rewrite ?ew_ewset_other by lia; exact E34);
    rewrite (U_atom Ex 34 s X) in H by lia; clear X
  | context [U ?Ex (SLit ?k)] => rewrite (U_lit Ex k) in H by lia
  end
end in
let zbool := idtac;
repeat match goal with
| H : negb _ = true |- _ => apply (proj1 (Bool.negb_true_iff _)) in H
| H : negb _ = false |- _ => apply (proj1 (Bool.negb_false_iff _)) in H
| H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
| H : (_ && _)%bool = false |- _ => apply andb_false_iff in H; destruct H
| H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
| H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
| H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
| H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
| H : (_ <=? _) = true |- _ => apply Z.leb_le in H
| H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
end in
let rk_close := idtac;
rewrite (proj2 (Z.eqb_neq e 0) Hne); unfold reac_rival_kind_model;
repeat match goal with
| H : (_ =? _) = _ |- _ => revert H
| H : (_ <? _) = _ |- _ => revert H
| H : negb _ = _ |- _ => revert H
end;
clear - Rr Rd Rs Rc; intros;
repeat match goal with H : context [if ?b then _ else _] |- _ =>
  lazymatch b with true => fail | false => fail | _ => destruct b eqn:? end end;
cbv beta iota in *;
repeat match goal with |- context [if ?b then _ else _] =>
  lazymatch b with true => fail | false => fail | _ => destruct b eqn:?; cbv beta iota end end;
zbool; lia in
let leaf_ret := idtac;
lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
let R10 := fresh "R10" in let R1 := fresh "R1" in
prreg HS (10%bv : bv 5) R10; prreg HS (1%bv : bv 5) R1;
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
let mat' := fresh "mat" in intros mat';
unfold treac_rival_kind_of_post; apply apost_base_same_fx;
exists ly, S, (ms_regs msc), (ms_mem msc); eexists;
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|];
split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (rk_extra r d s c) HS);
  [repeat (apply rk_agree_ewset; [lia|]); exact HAE | vm_compute; reflexivity]|];
split; [rewrite R10; unfold w64; f_equal; bnorm; rk_close
  | split; [apply Permutation_refl | split; [reflexivity | exact HM]]]
end in
let rec go := idtac;
lazymatch goal with HS : st_ok_pi _ _ _ ?ss0 _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
paj_run_tok RUN HS HJ SHOK RBspan;
[first [apply awr_ok_nil | awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp] |];
rk_upd_mem Usp WS;
lazymatch goal with
| HS' : st_ok_pi _ _ _ ?ss _, SHOK' : sh_ok _ _ _ _ _ |- _ =>
let K := eval vm_compute in (run_K A_LIM RBx rk_SH ss) in
let why := lazymatch paj_tables RUN with (?tpi, ?tw) => psym_why_tok tpi tw K RBx RBspan rk_SH (start K RBx RBspan rk_SH ss) end in
lazymatch why with
| SR_jalr _ => leaf_ret
| SR_branch _ _ _ => psrr_branch_tok RUN BR HS' SHOK' RBspan; [go | go]
| _ => let pc := eval vm_compute in (ss_pc ss) in fail 100 "STUCK" pc why
end
end end in
go.
Qed.
End w.
Theorem pb_reac_rival_kind_of : treac_rival_kind_of_spec.
Proof.
unfold treac_rival_kind_of_spec.
intros fq ly S W regs mem md ch e r d s c HPRE _ H10 _ He8 Hpre.
destruct (Z.eq_dec e 0) as [He0 | Hne].
- subst e. exact (@rk_walk0 fq ly S W regs mem md ch r d s c HPRE H10).
- destruct (Hpre Hne) as (_ & Happ & Hoff & Hsh & _ & Rr & Rd & Rs & Rc & Vr & Vd & Vs & Vc).
  exact (@rk_walk1 fq ly S W regs mem md ch e r d s c HPRE H10 He8 Hne Happ Hoff Hsh Rr Rd Rs Rc Vr Vd Vs Vc).
Qed.
End h.
End f.
End d.
