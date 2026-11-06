(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryUnset), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntryUnset.v, with its module paths and module names changed; 1094 of its 1196 lines of code are new or changed and 703 lines of the source are left out. *)
(* The walk of fuzz_boxreg's LLVMFuzzerTestOneInput, phase HEAD (slots 0x801ec .. the four case pcs) on the ASan
   build: from the head of the operation loop J either to the exit cut X (no input byte left) or, through the read
   of the operation byte, the shadow stores of mac and prev, the copy of the registry into the frame's `prev` and
   the dispatch on op & 3, to the case cut T op3.
   The cuts are lib/A/Prog/BoxLxDefs.v's; the phase lemma is `gb_head`. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import
PaTable PaSym PaRun PaShadow PaStep PaJournal BoxSyms BoxList BoxPa BoxPaLib BoxBase YC85.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import YC1g YC1h YC4b BoxFrame ReacBoxregInit.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxLxDefs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require ReacBoxregSetName.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The shadow base the walk's tokens are read against, and the band of shadow cells they may read: the whole low
   shadow. A run that writes into the frame's shadow takes the empty band instead. *)
Definition SB_H : Z := 0x7fff8000.
Definition Bx_H : sv := SOff 18 0.
Definition Bspan_H : Z * Z := (SB_H, SB_H + 2 ^ 44 - 1).
Definition Bspan_0 : Z * Z := (0, 0).

(* The frame's 52 shadow bytes as one chunk each. *)
Fixpoint shc_from (i : Z) (l : list Z) : list YP09.chunk :=
  match l with [] => [] | v :: t => YP09.mkChunk i (CVal 1 (SLit v)) :: shc_from (i + 1) t end.
Definition shc (l : list Z) : list YP09.chunk := shc_from 0 l.

(* The regions of the walk: the spill slots at s1 (atom 9), the frame's shadow at s8 (atom 24), the shadow byte of
   r->n (atom 36, the word slot 0x60 holds), r->n itself (atom 20 = r) and the input byte at the cursor (atom 32). *)
Definition R_sl (wlo whi : Z) (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some 9%nat) 16 152 wlo whi cs.
Definition sl_J : list YP09.chunk :=
  [YP09.mkChunk 96 (CVal 8 (SOff 36 0)); YP09.mkChunk 120 (CVal 8 (SOff 37 0));
   YP09.mkChunk 136 (CVal 8 (SOff 32 0)); YP09.mkChunk 144 (CVal 8 (SOff 33 0))].
Definition R_fsh (sh : list Z) (wlo whi : Z) : YP09.region := YP09.mkRegion (Some 24%nat) 0 64 wlo whi (shc sh).
Definition R_rsh : YP09.region := YP09.mkRegion (Some 36%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
(* the two spill slots the dispatch writes: n_before (0x48) and i (0x68) *)
Definition R_s48 : YP09.region := YP09.mkRegion (Some 9%nat) 72 80 72 80 [].
Definition R_s68 : YP09.region := YP09.mkRegion (Some 9%nat) 104 112 104 112 [].
Definition R_n : YP09.region := YP09.mkRegion (Some 20%nat) 280 284 0 0 [YP09.mkChunk 280 (CVal 4 (SOff 35 0))].
Definition R_in : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))].
Definition F_J : facts := mkFacts
  [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (18%nat, mkAF SB_H SB_H 0); (20%nat, mkAF 4096 140737479966720 4);
   (24%nat, mkAF (SB_H + 512) (SB_H + 2 ^ 44) 0); (32%nat, mkAF 0 (2 ^ 47 - 1) 0); (33%nat, mkAF 0 (2 ^ 26) 0);
   (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 5 0); (36%nat, mkAF (SB_H + 512) (SB_H + 2 ^ 44) 0);
   (37%nat, mkAF 4096 (2 ^ 47) 0)] [] [].
Definition F_5 : facts := mkFacts
  [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (18%nat, mkAF SB_H SB_H 0); (20%nat, mkAF 4096 140737479966720 4);
   (22%nat, mkAF 0 255 0); (24%nat, mkAF (SB_H + 512) (SB_H + 2 ^ 44) 0); (26%nat, mkAF 0 5 0)] [] [].

Local Ltac zbool :=
repeat match goal with
| H : negb _ = true |- _ => apply (proj1 (Bool.negb_true_iff _)) in H
| H : negb _ = false |- _ => apply (proj1 (Bool.negb_false_iff _)) in H
| H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
| H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
| H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
| H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
| H : (_ <=? _) = true |- _ => apply Z.leb_le in H
| H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
end.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg box_listing}.
#[local] Notation SEGS := (@pa_segs _ box_listing PI).
#[local] Notation VAL := (@pa_val _ box_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ box_listing PI).
#[local] Notation BASE := (@pa_val _ box_listing PI A_TEXT).

Lemma hd_sub_mod16 : forall a b, a mod 32 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof.
intros a b Ha Hb. apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide in Hb; [|lia]. apply Z.mod_divide; [lia|].
destruct Ha as [x Hx]. destruct Hb as [y Hy]. exists (2 * x - y). lia.
Qed.
Lemma hd_ewR : forall (regs : bvmap 5 word) extra n (r : bv 5),
  Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs extra)) n = getr regs r.
Proof.
intros regs extra n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma hd_den0 : forall E n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma hd_den_off : forall E n v x, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n x) = Z_to_bv 64 (v + x).
Proof.
intros E n v x F Hv. rewrite denot_lit_U, U_SOff, F, unsigned_lit_small by exact Hv.
unfold zcanon, M64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.
(* A word, a byte and an array read back from a memory that kept the bytes they lie on. *)
Lemma hd_rdword_keep : forall (W : world SEGS) (m m' : word -> option byte) a v,
  (forall x, a <= x < a + 8 -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  rdword (aview SEGS (w_H W) m) a = Some v -> rdword (aview SEGS (w_H W) m') a = Some v.
Proof. intros W m m' a v Hk Hr. rewrite <- Hr. apply rdword_ext. intros i Hi. apply Hk. lia. Qed.
Lemma hd_garr8_keep : forall (W : world SEGS) (m m' : word -> option byte) a l,
  (forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  garr8 SEGS (mrestrict (w_H W) m) a l -> garr8 SEGS (mrestrict (w_H W) m') a l.
Proof.
intros W m m' a l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hb]. split; [|exact Hb].
intros u Hu. assert (u = 0)%nat by lia. subst u.
pose proof (Hv 0%nat ltac:(lia)) as Hv0. cbn [Z.of_nat] in Hv0 |- *. rewrite Z.add_0_r in Hv0 |- *.
rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) m m' (a + Z.of_nat j) (Hk (a + Z.of_nat j) ltac:(lia))). exact Hv0.
Qed.
Lemma hd_val_mem1 : forall (W : world SEGS) (m : word -> option byte) a v,
  aview SEGS (w_H W) m a = Some v -> val_mem SEGS (mrestrict (w_H W) m) a 1 v /\ 0 <= v < 256.
Proof.
intros W m a v Hv. destruct (aview_byte SEGS (w_H W) m a v Hv) as (b & Hb & -> & Hr).
split; [|exact Hr]. intros kk Hk. assert (kk = 0)%nat by lia. subst kk. cbn [Z.of_nat].
rewrite Z.add_0_r, Hb. f_equal. apply bv_eq. rewrite le_byte_small by (cbn [Z.of_nat]; lia).
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite Z.shiftr_div_pow2 by lia. cbn [Z.of_nat Z.mul]. rewrite Z.div_1_r. symmetry. apply Z.mod_small. exact Hr.
Qed.
(* The frame's shadow bytes, one chunk each. *)
Lemma hd_shc_from_ok : forall (W : world SEGS) (m : word -> option byte) (E : env) base sh i,
  (forall j, (j < length sh)%nat -> aview SEGS (w_H W) m (base + (i + Z.of_nat j)) = Some (nth j sh 0)) ->
  Forall (YP09.chunk_ok SEGS E (mrestrict (w_H W) m) base) (shc_from i sh).
Proof.
intros W m E base sh. induction sh as [|v t IH]; intros i H; cbn [shc_from]; [constructor|].
constructor.
- pose proof (H 0%nat ltac:(cbn [length]; lia)) as H0. cbn [nth] in H0. rewrite Z.add_0_r in H0.
  destruct (hd_val_mem1 W m (base + i) v H0) as [Hm Hr].
  apply (chunk_ok_val SEGS E _ base i 1 (SLit v) v).
  + rewrite denot_lit_U, U_SLit. unfold zcanon, M64. rewrite Z.mod_small by lia. reflexivity.
  + cbn [Z.of_N]. change (8 * 1) with 8. lia.
  + cbn [Z.of_N]. lia.
  + cbn [N.to_nat]. exact Hm.
- apply IH. intros j Hj. pose proof (H (S j) ltac:(cbn [length]; lia)) as Hs. cbn [nth] in Hs.
  replace (base + (i + 1 + Z.of_nat j)) with (base + (i + Z.of_nat (S j))) by lia. exact Hs.
Qed.
Lemma hd_shc_ok : forall (W : world SEGS) (m : word -> option byte) (E : env) base sh,
  (forall j, (j < length sh)%nat -> aview SEGS (w_H W) m (base + Z.of_nat j) = Some (nth j sh 0)) ->
  Forall (YP09.chunk_ok SEGS E (mrestrict (w_H W) m) base) (shc sh).
Proof.
intros W m E base sh H. unfold shc. apply hd_shc_from_ok. intros j Hj.
replace (base + (0 + Z.of_nat j)) with (base + Z.of_nat j) by lia. exact (H j Hj).
Qed.
Lemma hd_zcanon_in : forall z, 0 <= z < 2 ^ 64 -> zcanon z = z.
Proof. intros z Hz. unfold zcanon, M64. apply Z.mod_small. exact Hz. Qed.
Lemma hd_U_off_val : forall E n v x, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + x < 2 ^ 64 ->
  U E (SOff n x) = v + x.
Proof. intros E n v x F Hv Hx. rewrite U_SOff, F, unsigned_lit_small by exact Hv. apply hd_zcanon_in. exact Hx. Qed.
Lemma hd_U_lit_val : forall E z, 0 <= z < 2 ^ 64 -> U E (SLit z) = z.
Proof. intros E z Hz. rewrite U_SLit. apply hd_zcanon_in. exact Hz. Qed.
Lemma hd_keep_outside : forall E rs (m m' : word -> option byte) (H : word -> bool) a,
  frame_of E rs m m' -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
  aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs m m' H a HF Ha Hn. unfold aview, YP09.mbyte, mrestrict.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. exact Hn.
Qed.
(* One byte of a region whose chunk is a literal. *)
Lemma hd_sh_byte : forall (W : world SEGS) (m : word -> option byte) E n b cs lo hi wlo whi off v,
  YP09.region_ok SEGS E (mrestrict (w_H W) m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk off (CVal 1 (SLit v))) cs -> 0 <= v < 256 ->
  aview SEGS (w_H W) m (b + off) = Some v.
Proof.
intros W m E n b cs lo hi wlo whi off v Hr Hb Hin Hv.
apply (aview_of_val_mem1 SEGS (w_H W) m); [|exact Hv].
exact (field_of_region E _ n b cs lo hi wlo whi off 1%N (SLit v) v Hr Hb Hin
  ltac:(rewrite denot_lit_U, U_SLit; unfold zcanon, M64; rewrite Z.mod_small by lia; reflexivity)
  ltac:(cbn [Z.of_N]; change (8 * 1) with 8; lia) ltac:(cbn [Z.of_N]; lia)).
Qed.
(* The values of a branch's two sides as numbers, and the value of a register of the symbolic state. *)
Ltac hd_uval H :=
  repeat match type of H with
  | context [U ?Ex (SOff ?n ?x)] =>
      match goal with F : ew Ex n = Z_to_bv 64 ?v |- _ => rewrite (hd_U_off_val Ex n v x F) in H by lia end
  | context [U ?Ex (SLit ?z)] => rewrite (hd_U_lit_val Ex z) in H by lia
  end.
Ltac hd_bnum H :=
  first [rewrite branch_ne_U in H | rewrite branch_eq_U in H | rewrite branch_ltu_U in H | rewrite branch_geu_U in H];
  hd_uval H; zbool.
Ltac hd_bfact := match goal with H : branch_taken _ (sv_denot _ _) (sv_denot _ _) = _ |- _ => hd_bnum H end.
Ltac hd_regval HS :=
  cbn [ms_regs mkst];
  lazymatch goal with |- getr _ ?rr = w64 ?v =>
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ss (restrict ?H ?ms) =>
    let R := fresh "R" in pose proof (st_ok_pi_restrict_reg H Ex ss ms rr HS) as R;
    let e := eval vm_compute in (sr_get (ss_regs ss) rr) in change (sr_get (ss_regs ss) rr) with e in R;
    cbn [ms_regs restrict mkst] in R; rewrite R; clear R;
    lazymatch e with
    | SOff ?n 0 =>
        match goal with F : ew Ex n = Z_to_bv 64 ?u |- _ =>
          rewrite (hd_den0 Ex n u F); unfold w64; first [reflexivity | f_equal; lia] end
    | SOff ?n ?x =>
        match goal with F : ew Ex n = Z_to_bv 64 ?u |- _ =>
          rewrite (hd_den_off Ex n u x F) by lia; unfold w64; f_equal; lia end
    | SLit ?z => cbn [sv_denot]; unfold w64; f_equal; lia
    end end end.
(* The bytes a run kept: every run of this walk opens at most one write window [lo, hi). *)
Ltac hd_mk_keep HFx W lo hi K :=
  lazymatch type of HFx with frame_of ?Ex ?rsB ?m1 ?m2 =>
    assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
      aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m1 a);
    [ let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
      intros a Ha Hn; apply (hd_keep_outside Ex _ _ _ (w_H W) a HFx Ha);
      let rs' := eval vm_compute in rsB in change rsB with rs';
      let rg := fresh "rg" in let Hrg := fresh "Hrg" in let Hb := fresh "Hb" in
      intros (rg & Hrg & Hb); cbn [In] in Hrg;
      repeat (destruct Hrg as [<- | Hrg];
        [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
         repeat match goal with Uh : bv_unsigned (ew Ex _) = _ |- _ => rewrite Uh in Hb end; lia |]);
      destruct Hrg
    | ] end.
Ltac hd_mk_keep2 HFx W lo1 hi1 lo2 hi2 K :=
  lazymatch type of HFx with frame_of ?Ex ?rsB ?m1 ?m2 =>
    assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (lo1 <= a < hi1) -> ~ (lo2 <= a < hi2) ->
      aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m1 a);
    [ let a := fresh "a" in let Ha := fresh "Ha" in
      let Hn1 := fresh "Hn" in let Hn2 := fresh "Hn" in
      intros a Ha Hn1 Hn2; apply (hd_keep_outside Ex _ _ _ (w_H W) a HFx Ha);
      let rs' := eval vm_compute in rsB in change rsB with rs';
      let rg := fresh "rg" in let Hrg := fresh "Hrg" in let Hb := fresh "Hb" in
      intros (rg & Hrg & Hb); cbn [In] in Hrg;
      repeat (destruct Hrg as [<- | Hrg];
        [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
         repeat match goal with Uh : bv_unsigned (ew Ex _) = _ |- _ => rewrite Uh in Hb end; lia |]);
      destruct Hrg
    | ] end.
(* After a run that took shadow tokens: the facts on the atoms below the token base hold in the new environment. *)
Ltac hd_restate OLD :=
  lazymatch type of OLD with forall q, (q < ?K)%nat -> ew ?En q = ew ?Eo q =>
  repeat match goal with
  | F : ew Eo ?n = Z_to_bv 64 ?v |- _ =>
      lazymatch goal with
      | _ : ew En n = Z_to_bv 64 v |- _ => fail
      | _ => let F' := fresh "FF" in assert (F' : ew En n = Z_to_bv 64 v) by (rewrite OLD by (cbv; lia); exact F)
      end
  end end.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA BS___asan_memcpy).
Hypothesis MTL : ameter_laws MT.
Variable POST : bcx -> world SEGS -> config -> Prop.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* The geometry every state of the phase runs in. *)
Lemma hd_geo : forall (cx : bcx) fp ly3 S3 W3 (mem : word -> option byte) md3 k,
  gb_base B MT cx ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 mem md3 k ->
  frames S3 = [(GB_CID, fp)] ->
  spZ (c_regs cx) mod 16 = 0 /\ alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 /\
  spZ (c_regs cx) - 288 <= c_sp1 cx <= spZ (c_regs cx) - 256 /\ c_sp1 cx mod 32 = 0 /\
  frame_addr ly3 GB_CID fp = gF cx fp /\ flag_addr ly3 GB_CID fp = gFL cx fp /\
  4096 <= gF cx fp /\ gF cx fp + 512 <= alloc_ceiling /\ in_app (gF cx fp) 512 /\
  gF cx fp mod 64 = 0 /\ gSH cx fp = SHADOW_OFF + gF cx fp / 8.
Proof.
intros cx fp ly3 S3 W3 mem md3 k HB HJ HFR.
pose proof asan_consts as (Hac & _).
pose proof HB as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & _).
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof HJ as (HAR3 & Hly3 & _).
assert (Hfin : In (GB_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR0 Hly3) as (_ & Efa & _).
assert (EgF : frame_addr ly3 GB_CID fp = gF cx fp) by (unfold gF; apply Efa).
assert (ElyF : ly_F ly3 = ly_F (c_ly cx)).
{ pose proof (Efa GB_CID fp) as Ef. unfold frame_addr in Ef. lia. }
assert (Hfb : fs_frame_bytes GB_CID = 512) by (vm_compute; reflexivity).
pose proof (frames_bounds _ _ LAWS _ _ _ _ _ GB_CID fp HAR3 Hfin) as (HF0 & HFc & HFia).
destruct (frame_al64 SEGS B ly3 S3 W3 mem md3 GB_CID fp HAR3 Hfin) as (H64 & _ & _).
rewrite EgF in HF0, HFc, HFia, H64. rewrite Hfb in HFc, HFia.
assert (Hx : 0 <= spZ (c_regs cx) + -256) by (unfold GB_STK in *; lia).
pose proof (Z.div_mod (spZ (c_regs cx) + -256) 32 ltac:(lia)) as Hdm.
pose proof (Z.mod_pos_bound (spZ (c_regs cx) + -256) 32 ltac:(lia)) as Hmp.
assert (A1 : alloc_ceiling + 32768 <= spZ (c_regs cx)) by (unfold GB_STK in *; lia).
assert (A2 : spZ (c_regs cx) <= 2 ^ 47) by lia.
assert (A3 : spZ (c_regs cx) - 288 <= c_sp1 cx) by (rewrite Hsp1; lia).
assert (A4 : c_sp1 cx <= spZ (c_regs cx) - 256) by (rewrite Hsp1; lia).
assert (A5 : c_sp1 cx mod 32 = 0) by (rewrite Hsp1, Z.mul_comm, Z_mod_mult; reflexivity).
assert (A6 : flag_addr ly3 GB_CID fp = gFL cx fp)
  by (unfold gFL, flag_addr; rewrite ElyF; reflexivity).
assert (A7 : gSH cx fp = SHADOW_OFF + gF cx fp / 8) by (unfold gSH, shadow_of_addr; reflexivity).
repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

Theorem gb_head : forall i,
  (forall op3, 0 <= op3 < 4 -> gb_from B MT POST (GI_T B MT op3 i)) ->
  gb_from B MT POST (GI_X B MT) ->
  gb_from B MT POST (GI_J B MT i).
Proof.
intros i HT HX cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HI.
destruct HI as (r & bs & pos & HBODY & Hi & Hk & Hacc & HBLK & HREG & HINV & R20 & R21 & R25 & HSR & HCUR).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfregs & Hfcsr & HGR & HSV & HSH & Hshlen & HFL & HSF & HIN).
pose proof HGR as (G2 & G8 & G9 & G3 & G4 & G18 & G24).
pose proof HSF as (SF18 & SF28 & SF70 & SF78 & SF80).
pose proof HSR as (SR10 & SR20 & SR38 & SR40 & SR50 & SR60).
pose proof HCUR as (Hpos & SC88 & SC90).
pose proof HREG as (Hrin & Hbslen & Hbsb).
pose proof HINV as ((Hlen288 & HB1 & _) & _). unfold Boxreg.boxreg_B1 in HB1.
assert (Hms : restrict (w_H W3) ms3 =
  mkst (ms_regs ms3) (Z_to_bv 64 (BASE + GP_J)) (mrestrict (w_H W3) (ms_mem ms3)) (seg_rom SEGS)).
{ destruct ms3 as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
  cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem]
    in Hpc, Hresv, Hsvc, Hrom, Hfregs, Hfcsr. subst. reflexivity. }
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBok.
pose proof (pa_base_lo (PL := PL_box) (PI := PI)) as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (hd_geo cx fp ly3 S3 W3 (ms_mem ms3) md3 k HB HJ HFR)
  as (Hal16 & Hsp & Hsp1 & Hsp32 & EgF & EgFL & HF0 & HFc & HFia & HF64 & ESH).
pose proof HB as ((HAR0 & Hra0 & Hra4 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0) & Hr10 & Hr11 & Hinp & Hgarr0 & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & JK1 & JK2 & _ & JK4 & _ & HPRES & _).
assert (Hfin : In (GB_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
assert (Hrin3 : In (r, REG_SIZE) (ablocks B ly3 S3)) by exact Hrin.
destruct (al_blocks _ _ LAWS _ _ _ _ _ r REG_SIZE HAR Hrin3) as (Hr16 & Hr4096 & Hrceil & Hria & Hrpres & _).
change (req_size REG_SIZE) with 288 in Hrceil, Hria, Hrpres.
(* the input block *)
assert (Hinlo : c_n cx = 0 \/ (0 < c_n cx /\ In (c_p cx, c_n cx) (ablocks B ly3 S3) /\
                               0 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling)).
{ destruct Hinp as [(Hn0 & _) | (Hn & Hin)]; [left; exact Hn0 | right].
  assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3))
    by (unfold gblk1 in HBLK; rewrite HBLK; apply in_or_app; left; exact Hin).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin3) as (_ & Hp4096 & Hpceil & _).
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq]. split; [lia|]. split; [exact Hin3|]. lia. }
assert (Hplo : 0 <= c_p cx + pos <= 2 ^ 47 - 1).
{ destruct Hinp as [(Hn0 & Hp0) | (Hn & _)]; unfold c_n in *.
  - rewrite Hp0. unfold GB_EMPTY. lia.
  - destruct Hinlo as [Hn0 | (_ & _ & Hp1 & Hp2)]; lia. }
assert (Hac8 : alloc_ceiling / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
assert (HSHlo : SB_H + 512 <= gSH cx fp <= SB_H + 2 ^ 44).
{ assert (D1 : 4096 / 8 <= gF cx fp / 8) by (apply Z.div_le_mono; lia).
  assert (D2 : gF cx fp / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
  change (4096 / 8) with 512 in D1. rewrite ESH. unfold SHADOW_OFF, SB_H. lia. }
assert (HRSlo : SB_H + 512 <= shadow_of_addr SHADOW_OFF (r + 280) <= SB_H + 2 ^ 44).
{ assert (D1 : 4096 / 8 <= (r + 280) / 8) by (apply Z.div_le_mono; lia).
  assert (D2 : (r + 280) / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
  change (4096 / 8) with 512 in D1. unfold shadow_of_addr, SHADOW_OFF, SB_H. lia. }
(* the byte of the input at the cursor (0 when the cursor is at the end) *)
set (hop := nth (Z.to_nat pos) (map (fun b : byte => bv_unsigned b) (c_pl cx)) 0).
assert (Hhop : 0 <= hop < 256).
{ unfold hop. destruct (Nat.lt_ge_cases (Z.to_nat pos) (length (map (fun b : byte => bv_unsigned b) (c_pl cx)))) as [Hl|Hl].
  - rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by exact Hl. rewrite map_nth.
    pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat pos) (c_pl cx) (Z_to_bv 8 0))) as HR.
    change (bv_modulus 8) with 256 in HR. lia.
  - rewrite nth_overflow by exact Hl. lia. }
set (ext := map (Z_to_bv 64) [c_p cx + pos; c_n cx - pos; hop; Boxreg.bx_n bs;
                              shadow_of_addr SHADOW_OFF (r + 280); gF cx fp + GO_PREV]).
set (E := Eimg (Ereg (ms_regs ms3) ext)).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EE : forall q (rg : bv 5), Z.of_nat q = bv_unsigned rg -> ew E q = getr (ms_regs ms3) rg)
  by (intros q rg Hq; unfold E; apply hd_ewR; exact Hq).
assert (EX : forall q, (q < 6)%nat -> ew E (32 + q)%nat = nth q ext (Z_to_bv 64 0)).
{ intros q Hq. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (F2 : ew E 2 = Z_to_bv 64 (c_sp1 cx)) by (rewrite (EE 2%nat 2%bv eq_refl); exact G2).
assert (F3 : ew E 3 = Z_to_bv 64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl), G3; exact Hgp0).
assert (F4 : ew E 4 = Z_to_bv 64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl), G4; exact Htp0).
assert (F8 : ew E 8 = Z_to_bv 64 (spZ (c_regs cx))) by (rewrite (EE 8%nat 8%bv eq_refl); exact G8).
assert (F9 : ew E 9 = Z_to_bv 64 (c_sp1 cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact G9).
assert (F18 : ew E 18 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 18%nat 18%bv eq_refl); exact G18).
assert (F20 : ew E 20 = Z_to_bv 64 r) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (F21 : ew E 21 = Z_to_bv 64 i) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
assert (F24 : ew E 24 = Z_to_bv 64 (gSH cx fp)) by (rewrite (EE 24%nat 24%bv eq_refl); exact G24).
assert (F25 : ew E 25 = Z_to_bv 64 (Boxreg.bx_fabric bs)) by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
assert (F32 : ew E 32 = Z_to_bv 64 (c_p cx + pos)) by (exact (EX 0%nat ltac:(lia))).
assert (F33 : ew E 33 = Z_to_bv 64 (c_n cx - pos)) by (exact (EX 1%nat ltac:(lia))).
assert (F34 : ew E 34 = Z_to_bv 64 hop) by (exact (EX 2%nat ltac:(lia))).
assert (F35 : ew E 35 = Z_to_bv 64 (Boxreg.bx_n bs)) by (exact (EX 3%nat ltac:(lia))).
assert (F36 : ew E 36 = Z_to_bv 64 (shadow_of_addr SHADOW_OFF (r + 280))) by (exact (EX 4%nat ltac:(lia))).
assert (F37 : ew E 37 = Z_to_bv 64 (gF cx fp + GO_PREV)) by (exact (EX 5%nat ltac:(lia))).
assert (HSB : SB_H = 2147450880) by reflexivity.
assert (ESB : SHADOW_OFF = 2147450880) by (vm_compute; reflexivity).
assert (HGP : GO_PREV = 64) by reflexivity.
assert (Hnlt : 0 <= c_n cx < 2 ^ 26) by (destruct Hinp as [(Hn0 & _) | (Hn & _)]; lia).
(* ---- the state at J as the engine's symbolic state ---- *)
assert (Hfb : fs_frame_bytes GB_CID = 512) by (vm_compute; reflexivity).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite F9; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = r) by (rewrite F20; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = gSH cx fp)
  by (rewrite F24; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = shadow_of_addr SHADOW_OFF (r + 280))
  by (rewrite F36; apply unsigned_lit_small; lia).
(* the frame, the registry and their shadows lie apart *)
assert (SEPrF : r + 288 <= gF cx fp \/ gF cx fp + 512 <= r).
{ pose proof (sep_block_frame _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 r REG_SIZE GB_CID fp HAR Hrin3 Hfin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EgF, Hfb in Hd.
  change (req_size REG_SIZE) with 288 in Hd. exact Hd. }
assert (SEPsh : shadow_of_addr SHADOW_OFF (r + 280) + 1 <= gSH cx fp \/
                gSH cx fp + 64 <= shadow_of_addr SHADOW_OFF (r + 280)).
{ unfold shadow_of_addr. rewrite ESH. destruct SEPrF as [Hd | Hd].
  - left. assert ((r + 280) / 8 <= (gF cx fp - 8) / 8) by (apply Z.div_le_mono; lia).
    assert ((gF cx fp - 8) / 8 = gF cx fp / 8 - 1)
      by (replace (gF cx fp - 8) with (gF cx fp + (-1) * 8) by lia; rewrite Z.div_add by lia; lia). lia.
  - right. assert ((gF cx fp + 512) / 8 <= (r + 280) / 8) by (apply Z.div_le_mono; lia).
    assert ((gF cx fp + 512) / 8 = gF cx fp / 8 + 64)
      by (replace (gF cx fp + 512) with (gF cx fp + 64 * 8) by lia; rewrite Z.div_add by lia; lia). lia. }
assert (SEPfa : forall a, gSH cx fp <= a < gSH cx fp + 64 -> ~ (r <= a < r + 288)).
{ intros a Ha Hr'. apply (fshadow_not_app (gF cx fp) 64 r 288 a); [lia | lia | exact Hria | | exact Hr'].
  rewrite ESH in Ha. unfold SHADOW_OFF in Ha. exact Ha. }
assert (SEPra : forall a, shadow_of_addr SHADOW_OFF (r + 280) <= a < shadow_of_addr SHADOW_OFF (r + 280) + 1 ->
                ~ (r <= a < r + 288)).
{ intros a Ha Hr'. apply (fshadow_not_app (r + 280) 1 r 288 a); [lia | lia | exact Hria | | exact Hr'].
  unfold shadow_of_addr, SHADOW_OFF in Ha. exact Ha. }
(* the chunks of the regions *)
assert (CH8 : forall base off n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
   rdword (aview SEGS (w_H W3) (ms_mem ms3)) (base + off) = Some v ->
   YP09.chunk_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) base (YP09.mkChunk off (CVal 8 (SOff n 0)))).
{ intros base off n v Hn Hv Hr'. apply (chunk_ok_val SEGS E _ base off 8 (SOff n 0) v).
  - apply hd_den0. exact Hn.
  - cbn [Z.of_N]. change (8 * 8) with 64. exact Hv.
  - cbn [Z.of_N]. lia.
  - cbn [N.to_nat]. apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact Hr'. }
assert (CH1 : forall base off v, aview SEGS (w_H W3) (ms_mem ms3) (base + off) = Some v ->
   YP09.chunk_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) base (YP09.mkChunk off (CVal 1 (SLit v)))).
{ intros base off v Hv. destruct (hd_val_mem1 W3 (ms_mem ms3) (base + off) v Hv) as [Hm Hr'].
  apply (chunk_ok_val SEGS E _ base off 1 (SLit v) v).
  - rewrite denot_lit_U, U_SLit. unfold zcanon, M64. rewrite Z.mod_small by lia. reflexivity.
  - cbn [Z.of_N]. change (8 * 1) with 8. lia.
  - cbn [Z.of_N]. lia.
  - cbn [N.to_nat]. exact Hm. }
assert (HS : st_ok_pi SEGS VAL E (mkSS GP_J sr_atoms [R_sl 136 152 sl_J; R_fsh GSH_J 0 0; R_rsh; R_n] None F_J)
  (restrict (w_H W3) ms3)).
{ rewrite Hms. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold R_sl, R_fsh, R_rsh, R_n, YP09.region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [unfold M64; lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply HPRES; unfold GB_STK; lia|].
      unfold sl_J. repeat apply Forall_cons; try apply Forall_nil.
      * apply (CH8 _ _ 36%nat (shadow_of_addr SHADOW_OFF (r + 280)) F36 ltac:(lia) SR60).
      * apply (CH8 _ _ 37%nat (gF cx fp + GO_PREV) F37 ltac:(lia) SF78).
      * apply (CH8 _ _ 32%nat (c_p cx + pos) F32 ltac:(lia) SC88).
      * apply (CH8 _ _ 33%nat (c_n cx - pos) F33 ltac:(lia) SC90).
    + rewrite U24.
      split; [lia|]. split; [unfold M64; lia|]. split; [intros o Ho; lia|].
      apply hd_shc_ok. exact HSH.
    + rewrite U36.
      split; [lia|]. split; [unfold M64; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil]. apply CH1. rewrite Z.add_0_r.
      destruct (al_shadow _ _ LAWS _ _ _ _ _ r REG_SIZE HAR Hrin3) as [Hbsh _].
      change (req_size REG_SIZE) with 288 in Hbsh.
      destruct Hbsh as (_ & _ & Hbsh).
      specialize (Hbsh 35 ltac:(change ((288 + 7) / 8) with 36; lia)).
      replace (if 35 <? 288 / 8 then 0 else 288 mod 8) with 0 in Hbsh by (vm_compute; reflexivity).
      replace (shadow_of_addr SHADOW_OFF (r + 280)) with (shadow_of_addr SHADOW_OFF r + 35); [exact Hbsh|].
      unfold shadow_of_addr. replace (r + 280) with (r + 35 * 8) by lia. rewrite Z.div_add by lia. lia.
    + rewrite U20. split; [lia|]. split; [unfold M64; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ r 280 4 (SOff 35 0) (Boxreg.bx_n bs)).
      * apply hd_den0. exact F35.
      * cbn [Z.of_N]. change (8 * 4) with 32. lia.
      * cbn [Z.of_N]. lia.
      * cbn [N.to_nat]. rewrite (ReacBoxregSetName.sn_bx_n bs Hlen288 HB1).
        apply ReacBoxregSetName.sn_val_mem. exact Hbsb.
  - apply pairwise_disjoint_of_extents.
    unfold R_sl, R_fsh, R_rsh, R_n, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U9, U24, U36, U20.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat match goal with |- _ /\ _ => split end;
    first [ lia
          | (destruct SEPsh as [Hd | Hd]; lia)
          | (destruct (Z_le_gt_dec (gSH cx fp + 64) (r + 280)) as [Hd | Hd]; [lia|];
             destruct (Z_le_gt_dec (r + 284) (gSH cx fp)) as [Hd2 | Hd2]; [lia|];
             exfalso; apply (SEPfa (Z.max (gSH cx fp) (r + 280))); lia)
          | (destruct (Z_le_gt_dec (shadow_of_addr SHADOW_OFF (r + 280) + 1) (r + 280)) as [Hd | Hd]; [lia|];
             destruct (Z_le_gt_dec (r + 284) (shadow_of_addr SHADOW_OFF (r + 280))) as [Hd2 | Hd2]; [lia|];
             exfalso; apply (SEPra (Z.max (shadow_of_addr SHADOW_OFF (r + 280)) (r + 280))); lia) ].
  - split; [|split; exact I].
    cbn [F_J f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite F9, F18, F20, F24, F32, F33, F34, F35, F36, F37.
    rewrite !unsigned_lit_small by lia.
    change (2 ^ 5) with 32. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end;
    first [exact I | exact Hsp32 | exact Hr16 | reflexivity | lia]. }
assert (SHOK : sh_ok SEGS Bx_H [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
(* ---- 0x801ec: the bytes left are tested ---- *)
paj_run_tok RUN HS HJ SHOK Bspan_H;
[ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end;
  repeat first [ apply awr_ok_nil
               | apply awr_ok_cons_ro; [cbn; lia|]
               | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
                 [reflexivity | rewrite U9; lia | cbn; unfold GB_STK; lia | cbn; lia |] ]
| ].
psrr_branch_tok RUN BR HS SHOK Bspan_H.
{ (* no byte left: the loop is done, the exit cut X *)
  hd_bfact.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan_H GP_X;
  [ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end;
    repeat first [ apply awr_ok_nil
                 | apply awr_ok_cons_ro; [cbn; lia|]
                 | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
                   [reflexivity | rewrite U9; lia | cbn; unfold GB_STK; lia | cbn; lia |] ]
  | ].
  lazymatch goal with
  | H1 : frame_of _ _ (ms_mem ms3) (ms_mem ?m1), H2 : frame_of _ _ (ms_mem ?m1) (ms_mem ?m2) |- _ =>
    hd_mk_keep H1 W3 (c_sp1 cx + 136) (c_sp1 cx + 152) K1;
    hd_mk_keep H2 W3 (c_sp1 cx + 136) (c_sp1 cx + 152) K2;
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 136 <= a < c_sp1 cx + 152) ->
      aview SEGS (w_H W3) (ms_mem m2) a = aview SEGS (w_H W3) (ms_mem ms3) a)
      by (intros a Ha Hn; rewrite (K2 a Ha Hn); exact (K1 a Ha Hn))
  end.
  pmkst HS.
  eapply HX; [exact HB | exact HJ | exact HFR | exact HMO |].
  unfold GI_X. exists r.
  pose proof (mo_malloc_nonneg _ MTL 48 ltac:(lia)) as Hmn48.
  pose proof (mo_free_nonneg _ MTL) as Hmf.
  assert (HAmono : GB_A MT i <= GB_A MT 64).
  { unfold GB_A. assert (i * (mo_malloc MT 48 + mo_free MT) <= 64 * (mo_malloc MT 48 + mo_free MT))
      by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
  split; [|split; [lia | split; [lia | split; [exact HBLK | split; [exact Hrin3 |]]]]].
  - unfold gb_body. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [unfold gregs; split; [hd_regval HS|]; split; [hd_regval HS|]; split; [hd_regval HS|];
            split; [rewrite Hgp0; hd_regval HS|]; split; [rewrite Htp0; hd_regval HS|];
            split; [hd_regval HS | hd_regval HS] |].
    unfold gsaved, gshadow, gslots_fr, gslot. cbn [ms_mem mkst].
    split.
    { destruct HSV as (Sra & Ssv). split.
      - apply (hd_rdword_keep W3 (ms_mem ms3)); [intros x Hx; apply KEEP; lia | exact Sra].
      - intros j Hj. apply (hd_rdword_keep W3 (ms_mem ms3)); [intros x Hx; apply KEEP; lia | exact (Ssv j Hj)]. }
    split.
    { intros j Hj. pose proof Hj as Hj'. rewrite Hshlen in Hj'. unfold GB_NSH in Hj'.
      rewrite KEEP; [exact (HSH j Hj) | lia | lia]. }
    split; [exact Hshlen|].
    split; [apply (hd_rdword_keep W3 (ms_mem ms3)); [intros x Hx; rewrite Hfb in Hx; apply KEEP; lia | exact HFL]|].
    split.
    { destruct HSF as (K18 & K28 & K70 & K78 & K80). unfold gslot in K18, K28, K70, K78, K80.
      split; [apply (hd_rdword_keep W3 (ms_mem ms3)); [intros x Hx; apply KEEP; lia | exact K18]|].
      split; [apply (hd_rdword_keep W3 (ms_mem ms3)); [intros x Hx; apply KEEP; lia | exact K28]|].
      split; [apply (hd_rdword_keep W3 (ms_mem ms3)); [intros x Hx; apply KEEP; lia | exact K70]|].
      split; [apply (hd_rdword_keep W3 (ms_mem ms3)); [intros x Hx; apply KEEP; lia | exact K78]|].
      apply (hd_rdword_keep W3 (ms_mem ms3)); [intros x Hx; apply KEEP; lia | exact K80]. }
    apply (hd_garr8_keep W3 (ms_mem ms3)); [|exact HIN].
    intros x Hx. rewrite length_map in Hx. apply KEEP; unfold c_n in *; lia.
  - hd_regval HS. }
(* ---- a byte is left: it is read as the operation ---- *)
hd_bfact.
assert (Hposn : 0 <= pos < c_n cx) by lia.
assert (Hn0 : 0 < c_n cx) by lia.
assert (Hreq : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
destruct Hinp as [(Hz & _) | (Hnr & Hin)]; [lia|].
assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3))
  by (unfold gblk1 in HBLK; rewrite HBLK; apply in_or_app; left; exact Hin).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin3) as (_ & Hp4096 & Hpceil & Hpia & _).
rewrite Hreq in Hpceil, Hpia.
(* the input block lies apart from the registry, the frame and their shadows *)
assert (SEPin : c_p cx + c_n cx <= r \/ r + 288 <= c_p cx).
{ destruct (in_split _ _ Hin) as (l1 & l2 & Hsplit).
  assert (Hdec : ablocks B ly3 S3 = l1 ++ (c_p cx, c_n cx) :: l2 ++ (r, REG_SIZE) :: []).
  { unfold gblk1 in HBLK. rewrite HBLK, Hsplit, <- app_assoc. reflexivity. }
  pose proof (sep_blocks_pos _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 _ _ _ _ _ HAR Hdec) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
  change (req_size REG_SIZE) with 288 in Hd. rewrite Hreq in Hd. exact Hd. }
assert (SEPinF : c_p cx + c_n cx <= gF cx fp \/ gF cx fp + 512 <= c_p cx).
{ pose proof (sep_block_frame _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 (c_p cx) (c_n cx) GB_CID fp HAR Hin3 Hfin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EgF, Hfb, Hreq in Hd. exact Hd. }
assert (SEPinS : forall a, gSH cx fp <= a < gSH cx fp + 64 -> ~ (c_p cx <= a < c_p cx + c_n cx)).
{ intros a Ha Hr'. apply (fshadow_not_app (gF cx fp) 64 (c_p cx) (c_n cx) a); [lia | lia | exact Hpia | | exact Hr'].
  rewrite ESH in Ha. unfold SHADOW_OFF in Ha. exact Ha. }
assert (SEPinR : forall a, shadow_of_addr SHADOW_OFF (r + 280) <= a < shadow_of_addr SHADOW_OFF (r + 280) + 1 ->
                 ~ (c_p cx <= a < c_p cx + c_n cx)).
{ intros a Ha Hr'. apply (fshadow_not_app (r + 280) 1 (c_p cx) (c_n cx) a); [lia | lia | exact Hpia | | exact Hr'].
  unfold shadow_of_addr, SHADOW_OFF in Ha. exact Ha. }
assert (U32 : bv_unsigned (ew E 32) = c_p cx + pos) by (rewrite F32; apply unsigned_lit_small; lia).
(* the input byte at the cursor, as a region of the state the first run left *)
assert (HINv : aview SEGS (w_H W3) (ms_mem ms3) (c_p cx + pos) = Some hop).
{ destruct (HIN (Z.to_nat pos) ltac:(rewrite length_map; unfold c_n in *; lia)) as [Hv _].
  rewrite Z2Nat.id in Hv by lia.
  exact (aview_of_val_mem1 SEGS (w_H W3) (ms_mem ms3) _ _ Hv ltac:(lia)). }
lazymatch goal with H1 : frame_of _ _ (ms_mem ms3) (ms_mem ?m1) |- _ =>
  hd_mk_keep H1 W3 (c_sp1 cx + 136) (c_sp1 cx + 152) K1 end.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx ?msx =>
  assert (HRin : YP09.region_ok SEGS E (ms_mem msx) R_in);
  [ cbn [restrict ms_mem]; unfold R_in, YP09.region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
    rewrite U32; split; [lia|]; split; [unfold M64; lia|]; split; [intros o Ho; lia|];
    apply Forall_cons; [|apply Forall_nil];
    apply (chunk_ok_val SEGS E _ (c_p cx + pos) 0 1 (SOff 34 0) hop);
    [ apply hd_den0; exact F34
    | cbn [Z.of_N]; change (8 * 1) with 8; lia
    | cbn [Z.of_N]; lia
    | cbn [N.to_nat]; rewrite Z.add_0_r;
      exact (proj1 (hd_val_mem1 W3 _ (c_p cx + pos) hop
               ltac:(rewrite (K1 (c_p cx + pos) ltac:(lia) ltac:(lia)); exact HINv))) ]
  | ];
  pose proof (st_ok_pi_add_region E ssx msx R_in HS eq_refl HRin
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
            let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
          cbn [all_disjoint]; unfold extent_disjoint, R_in, R_sl, R_fsh, R_rsh, R_n;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite U32, U9, U24, U36, U20;
          repeat match goal with |- _ /\ _ => split end;
          first [ exact I | lia
                | (destruct (Z_le_gt_dec (gSH cx fp + 64) (c_p cx + pos)) as [Hd | Hd]; [lia|];
                   destruct (Z_le_gt_dec (c_p cx + pos + 1) (gSH cx fp)) as [Hd2 | Hd2]; [lia|];
                   exfalso; apply (SEPinS (c_p cx + pos)); lia)
                | (destruct (Z_le_gt_dec (shadow_of_addr SHADOW_OFF (r + 280) + 1) (c_p cx + pos)) as [Hd | Hd]; [lia|];
                   destruct (Z_le_gt_dec (c_p cx + pos + 1) (shadow_of_addr SHADOW_OFF (r + 280))) as [Hd2 | Hd2]; [lia|];
                   exfalso; apply (SEPinR (c_p cx + pos)); lia)
                | (destruct SEPin as [Hd | Hd]; lia) ])) as HS2;
  clear HS; rename HS2 into HS end.
(* ---- 0x801f4 .. 0x80220: the shadow test of the input byte (0x80214 -> 0x80d20 -> 0x80f9c refuted by the
   input block's shadow), the byte is read and the cursor moves on ---- *)
paj_run_tok RUN HS HJ SHOK Bspan_H;
[ unfold Bx_H; rewrite (U_atom E 18 SHADOW_OFF F18 ltac:(lia)), (U_atom E 32 (c_p cx + pos) F32 ltac:(lia));
  rewrite <- (aview_rd_of SEGS);
  eapply (range_addressable_of_block _ _ LAWS ly3 S3 W3 _ _ (c_p cx) (c_n cx) (c_p cx + pos) 1 (proj1 HJ) Hin3);
  [lia | rewrite Hreq; lia]
| lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end;
  repeat first [ apply awr_ok_nil
               | apply awr_ok_cons_ro; [cbn; lia|]
               | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
                 [reflexivity | rewrite U9; lia | cbn; unfold GB_STK; lia | cbn; lia |] ]
| ].
(* the two shadow tokens extend the environment *)
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  assert (OLD1 : forall q, (q < 512)%nat -> ew Ex q = ew E q)
    by (intros q Hq; rewrite !ew_ewset_other by lia; reflexivity);
  assert (N2 : ew Ex 2 = Z_to_bv 64 (c_sp1 cx)) by (rewrite (OLD1 2%nat ltac:(lia)); exact F2);
  assert (N3 : ew Ex 3 = Z_to_bv 64 (as_gp B)) by (rewrite (OLD1 3%nat ltac:(lia)); exact F3);
  assert (N4 : ew Ex 4 = Z_to_bv 64 (as_tp B)) by (rewrite (OLD1 4%nat ltac:(lia)); exact F4);
  assert (N20 : ew Ex 20 = Z_to_bv 64 r) by (rewrite (OLD1 20%nat ltac:(lia)); exact F20);
  assert (G32 : ew Ex 32 = Z_to_bv 64 (c_p cx + pos)) by (rewrite (OLD1 32%nat ltac:(lia)); exact F32);
  assert (G33 : ew Ex 33 = Z_to_bv 64 (c_n cx - pos)) by (rewrite (OLD1 33%nat ltac:(lia)); exact F33);
  assert (G37 : ew Ex 37 = Z_to_bv 64 (gF cx fp + GO_PREV))
    by (rewrite (OLD1 37%nat ltac:(lia)); exact F37);
  hd_restate OLD1;
  assert (V9 : bv_unsigned (ew Ex 9) = c_sp1 cx) by (rewrite (OLD1 9%nat ltac:(lia)); exact U9);
  assert (V20 : bv_unsigned (ew Ex 20) = r) by (rewrite (OLD1 20%nat ltac:(lia)); exact U20);
  assert (V24 : bv_unsigned (ew Ex 24) = gSH cx fp) by (rewrite (OLD1 24%nat ltac:(lia)); exact U24);
  assert (V32 : bv_unsigned (ew Ex 32) = c_p cx + pos) by (rewrite (OLD1 32%nat ltac:(lia)); exact U32);
  assert (V36 : bv_unsigned (ew Ex 36) = shadow_of_addr SHADOW_OFF (r + 280))
    by (rewrite (OLD1 36%nat ltac:(lia)); exact U36)
end.
(* the shadow bytes of mac and prev may now be written *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  pose proof (st_ok_pi_region_nth Ex ssx msx 2%nat _ HS eq_refl) as RFSH;
  lazymatch type of RFSH with YP09.region_ok _ _ _ ?rg =>
    assert (WRs : forall o, 4 <= o < 44 -> writable_at SEGS (ms_mem msx) (base_val Ex (YP09.r_base rg) + o));
    [ intros o Ho; cbn [YP09.r_base base_val restrict ms_mem]; rewrite V24;
      apply (apresent_writable SEGS);
      destruct (al_frames _ _ LAWS ly3 S3 W3 _ _ GB_CID fp (proj1 HJ) Hfin) as (_ & _ & _ & Hsh);
      specialize (Hsh o ltac:(rewrite Hfb; change (512 / 8) with 64; lia));
      replace (gSH cx fp + o) with (shadow_addr (frame_addr ly3 GB_CID fp) + o);
      [exact (proj1 Hsh) | rewrite EgF; unfold shadow_addr; rewrite ESH; reflexivity]
    | ];
    pose proof (region_ok_rewindow SEGS Ex (ms_mem msx) rg 4 44 RFSH WRs) as RFSH';
    pose proof (ast_ok_pi_set_region Ex ssx msx 2%nat rg (set_window rg 4 44) HS eq_refl eq_refl
      ltac:(vm_compute; reflexivity) RFSH') as HS2;
    clear HS RFSH RFSH' WRs; rename HS2 into HS
  end end.
(* ---- 0x80220 .. 0x802d0: mac's shadow byte, the shadow test of r->n (0x8022c -> 0x80d2c -> 0x80fa0 refuted by
   the registry block's shadow), r->n, prev's 36 shadow bytes and the call of __asan_memcpy ---- *)
paj_run_tok RUN HS HJ SHOK Bspan_0;
[ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end;
  repeat first [ apply awr_ok_nil
               | apply awr_ok_cons_ro; [cbn; lia|]
               | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
                 [reflexivity | rewrite V9; lia | cbn; unfold GB_STK; lia | cbn; lia |]
               | apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 24%nat (gSH cx fp));
                 [reflexivity | exact V24
                 | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha;
                   right; right; right; exists GB_CID, fp; split; [left; reflexivity|];
                   right; unfold in_zr; cbn [fst snd]; rewrite EgF; unfold shadow_addr; rewrite <- ESH;
                   rewrite Hfb; change (512 / 8) with 64; lia
                 |] ]
| ].
(* what the three runs kept of the state at J *)
lazymatch goal with
| HA : frame_of _ _ (ms_mem ms3) (ms_mem ?m1), HBq : frame_of _ _ (ms_mem ?m1) (ms_mem ?m2),
  HCq : frame_of _ _ (ms_mem ?m2) (ms_mem ?m3) |- _ =>
  hd_mk_keep HA W3 (c_sp1 cx + 136) (c_sp1 cx + 152) KA;
  hd_mk_keep HBq W3 (c_sp1 cx + 136) (c_sp1 cx + 152) KB;
  hd_mk_keep2 HCq W3 (c_sp1 cx + 136) (c_sp1 cx + 152) (gSH cx fp + 4) (gSH cx fp + 44) KC;
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 136 <= a < c_sp1 cx + 152) ->
    ~ (gSH cx fp + 4 <= a < gSH cx fp + 44) ->
    aview SEGS (w_H W3) (ms_mem m3) a = aview SEGS (w_H W3) (ms_mem ms3) a)
    by (intros a Ha H1 H2; rewrite (KC a Ha H1 H2), (KB a Ha H1); exact (KA a Ha H1))
end.
(* the frame's shadow after the stores, and the cursor slots *)
assert (HGr : forall j, 0 <= nth j GSH_it 0 < 256).
{ intros j. destruct (Nat.lt_ge_cases j 52) as [Hl | Hl].
  - do 52 (destruct j as [|j]; [unfold GSH_it; cbn [length app repeat nth]; lia|]). lia.
  - rewrite nth_overflow; [lia | unfold GSH_it; cbn [length app repeat]; lia]. }
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msr) =>
  pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msr) 1%nat _ HS eq_refl) as RSL2;
  pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msr) 2%nat _ HS eq_refl) as RSH2;
  cbn [restrict ms_mem] in RSL2, RSH2;
  assert (GSHit : forall j, (j < 52)%nat ->
    aview SEGS (w_H W3) (ms_mem msr) (gSH cx fp + Z.of_nat j) = Some (nth j GSH_it 0));
  [ intros j Hj;
    do 52 (destruct j as [|j];
      [ eapply (hd_sh_byte W3 (ms_mem msr) Ex 24%nat (gSH cx fp));
        [ exact RSH2 | exact V24 | vm_compute; repeat first [exact (or_introl eq_refl) | apply or_intror]
        | apply HGr ] | ]);
    lia
  | ];
  assert (SL88 : rdword (aview SEGS (w_H W3) (ms_mem msr)) (c_sp1 cx + 136) = Some (c_p cx + pos + 1));
  [ apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem msr)); [|lia];
    exact (field_of_region Ex _ 9%nat (c_sp1 cx) _ _ _ _ _ 136 8%N (SOff 32 1) (c_p cx + pos + 1)
             RSL2 V9 ltac:(vm_compute; repeat first [exact (or_introl eq_refl) | apply or_intror])
             (hd_den_off Ex 32 (c_p cx + pos) 1 G32 ltac:(lia))
             ltac:(cbn [Z.of_N]; change (8 * 8) with 64; lia) ltac:(cbn [Z.of_N]; lia))
  | ];
  assert (SL90 : rdword (aview SEGS (w_H W3) (ms_mem msr)) (c_sp1 cx + 144) = Some (c_n cx - pos - 1));
  [ apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem msr)); [|lia];
    exact (field_of_region Ex _ 9%nat (c_sp1 cx) _ _ _ _ _ 144 8%N (SOff 33 (-1)) (c_n cx - pos - 1)
             RSL2 V9 ltac:(vm_compute; repeat first [exact (or_introl eq_refl) | apply or_intror])
             (hd_den_off Ex 33 (c_n cx - pos) (-1) G33 ltac:(lia))
             ltac:(cbn [Z.of_N]; change (8 * 8) with 64; lia) ltac:(cbn [Z.of_N]; lia))
  | ]
end.
(* ---- 0x802d0: __asan_memcpy (F + 0x40, r, 0x120) ---- *)
assert (HES : ESTACK = 4096) by reflexivity.
assert (HGO : GO_PREV = 64) by reflexivity.
assert (HZ : forall j, (8 <= j < 44)%nat -> nth j GSH_it 0 = 0).
{ intros j Hj. unfold GSH_it. rewrite app_nth2 by (cbn [length]; lia). cbn [length].
  rewrite app_nth1 by (rewrite repeat_length; lia).
  destruct (nth_in_or_default (j - 8) (repeat 0 36) 0) as [Hinz | Hdz];
    [exact (repeat_spec _ _ _ Hinz) | exact Hdz]. }
assert (ESH8 : shadow_of_addr SHADOW_OFF (gF cx fp + GO_PREV) = gSH cx fp + 8).
{ unfold shadow_of_addr. rewrite ESH, HGO.
  replace (gF cx fp + 64) with (gF cx fp + 8 * 8) by lia. rewrite Z.div_add by lia. lia. }
assert (HF8 : (gF cx fp + GO_PREV) mod 8 = 0).
{ apply Z.mod_divide; [lia|]. pose proof HF64 as HF64'. apply Z.mod_divide in HF64'; [|lia].
  destruct HF64' as [q Hq]. exists (8 * q + 8). rewrite HGO. lia. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22.
prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
  assert (QSP : spZ rg = spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx)))
    by (unfold spZ at 1; rewrite Q2, F2, unsigned_lit_small by lia; lia);
  eapply SRr_bind;
  [ eapply (aj_intrin_at SEGS B LAWS Hsegs OCpy (SIGMA BS___asan_memcpy) AMEMCPY W3 rg mm
      GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 mdq k
      (gF cx fp + GO_PREV) r 288 (c_sp1 cx - spZ (c_regs cx)) _ HJ);
    [ rewrite Q10, F37; reflexivity
    | rewrite Q11, F20; reflexivity
    | rewrite Q12; reflexivity
    | lia
    | lia
    | lia
    | exact QSP
    | apply hd_sub_mod16; [exact Hsp32 | exact Hal16]
    | lia
    | rewrite HES; unfold GB_STK; lia
    | rewrite Q3, F3; reflexivity
    | rewrite Q4, F4; reflexivity
    | reflexivity
    | rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]
    | intros a Ha; split;
      [ right; right; right; exists GB_CID, fp; split; [left; reflexivity|];
        left; unfold in_zr; cbn [fst snd]; rewrite EgF, Hfb; lia
      | rewrite HES; lia ]
    | apply (amem_range_sub_app (gF cx fp) 512 (gF cx fp + GO_PREV) 288);
      [exact HFia | lia | lia | lia | lia]
    | eapply zero_shadow_range;
      [ exact HF8 | reflexivity
      | intros ii Hii; change (288 / 8) with 36 in Hii; rewrite ESH8;
        replace (gSH cx fp + 8 + ii) with (gSH cx fp + Z.of_nat (Z.to_nat (8 + ii))) by lia;
        rewrite (GSHit (Z.to_nat (8 + ii)) ltac:(lia)); rewrite HZ by lia; reflexivity ]
    | intros _; apply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W3 _ _ GB_CID fp
        (gF cx fp + GO_PREV) 288 (proj1 HJ) Hfin); [rewrite EgF; lia | rewrite EgF, Hfb; lia | lia]
    | split; [lia|]; split; [lia|];
      split;
      [ intros a Ha; split;
        [ apply (aview_some_of_apresent SEGS);
          destruct (al_blocks _ _ LAWS ly3 S3 W3 _ _ r REG_SIZE (proj1 HJ) Hrin3) as (_ & _ & _ & _ & Hpr & _);
          change (req_size REG_SIZE) with 288 in Hpr; exact (proj1 (Hpr a Ha))
        | rewrite QSP, HES; lia ] |];
      split; [destruct SEPrF as [Hd | Hd]; [right | left]; lia |];
      split;
      [ apply (amem_range_of_block _ _ LAWS ly3 S3 W3 _ _ r REG_SIZE r 288 (proj1 HJ) Hrin3);
        [lia | change (req_size REG_SIZE) with 288; lia] |];
      split;
      [ apply (range_addressable_of_block _ _ LAWS ly3 S3 W3 _ _ r REG_SIZE r 288 (proj1 HJ) Hrin3);
        [lia | change (req_size REG_SIZE) with 288; lia]
      | intros _; apply (shadow_hull_vis_of_block _ _ LAWS ly3 S3 W3 _ _ r REG_SIZE r 288 (proj1 HJ) Hrin3);
        [lia | change (req_size REG_SIZE) with 288; lia | lia] ] ]
  | ] end.
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HPR2 & Ha0 & HCPY & HKC & _).
rewrite Q1.
assert (PP : forall (rr : bv 5) (z : Z), Z_to_bv 5 z = rr -> acallee_saved z ->
  getr regs2 rr = getr (ms_regs ms1) rr).
{ intros rr z Hz Hcs. rewrite <- Hz. apply HPR2. exact Hcs. }
pose proof (PP 2%bv 2 eq_refl ltac:(unfold acallee_saved; lia)) as PP2.
pose proof (PP 3%bv 3 eq_refl ltac:(unfold acallee_saved; lia)) as PP3.
pose proof (PP 4%bv 4 eq_refl ltac:(unfold acallee_saved; lia)) as PP4.
pose proof (PP 8%bv 8 eq_refl ltac:(unfold acallee_saved; lia)) as PP8.
pose proof (PP 9%bv 9 eq_refl ltac:(unfold acallee_saved; lia)) as PP9.
pose proof (PP 18%bv 18 eq_refl ltac:(unfold acallee_saved; lia)) as PP18.
pose proof (PP 20%bv 20 eq_refl ltac:(unfold acallee_saved; lia)) as PP20.
pose proof (PP 21%bv 21 eq_refl ltac:(unfold acallee_saved; lia)) as PP21.
pose proof (PP 22%bv 22 eq_refl ltac:(unfold acallee_saved; lia)) as PP22.
pose proof (PP 24%bv 24 eq_refl ltac:(unfold acallee_saved; lia)) as PP24.
pose proof (PP 25%bv 25 eq_refl ltac:(unfold acallee_saved; lia)) as PP25.
pose proof (PP 26%bv 26 eq_refl ltac:(unfold acallee_saved; lia)) as PP26.
set (E5 := Eimg (Ereg regs2 ([] : list word))).
assert (HEI5 : img_env VAL A_LIM E5) by (unfold E5; apply Eimg_env).
assert (P2 : ew E5 2 = Z_to_bv 64 (c_sp1 cx)).
{ transitivity (getr regs2 (2%bv : bv 5)); [unfold E5; apply hd_ewR; reflexivity|].
  transitivity (getr (ms_regs ms1) (2%bv : bv 5)); [exact PP2|].
  transitivity (ew E 2); [exact Q2 | exact F2]. }
assert (P3 : ew E5 3 = Z_to_bv 64 (as_gp B)).
{ transitivity (getr regs2 (3%bv : bv 5)); [unfold E5; apply hd_ewR; reflexivity|].
  transitivity (getr (ms_regs ms1) (3%bv : bv 5)); [exact PP3|].
  transitivity (ew E 3); [exact Q3 | exact F3]. }
assert (P4 : ew E5 4 = Z_to_bv 64 (as_tp B)).
{ transitivity (getr regs2 (4%bv : bv 5)); [unfold E5; apply hd_ewR; reflexivity|].
  transitivity (getr (ms_regs ms1) (4%bv : bv 5)); [exact PP4|].
  transitivity (ew E 4); [exact Q4 | exact F4]. }
assert (P8 : ew E5 8 = Z_to_bv 64 (spZ (c_regs cx))).
{ transitivity (getr regs2 (8%bv : bv 5)); [unfold E5; apply hd_ewR; reflexivity|].
  transitivity (getr (ms_regs ms1) (8%bv : bv 5)); [exact PP8|].
  transitivity (ew E 8); [exact Q8 | exact F8]. }
assert (P9 : ew E5 9 = Z_to_bv 64 (c_sp1 cx)).
{ transitivity (getr regs2 (9%bv : bv 5)); [unfold E5; apply hd_ewR; reflexivity|].
  transitivity (getr (ms_regs ms1) (9%bv : bv 5)); [exact PP9|].
  transitivity (ew E 9); [exact Q9 | exact F9]. }
assert (P18 : ew E5 18 = Z_to_bv 64 (SHADOW_OFF)).
{ transitivity (getr regs2 (18%bv : bv 5)); [unfold E5; apply hd_ewR; reflexivity|].
  transitivity (getr (ms_regs ms1) (18%bv : bv 5)); [exact PP18|].
  transitivity (ew E 18); [exact Q18 | exact F18]. }
assert (P20 : ew E5 20 = Z_to_bv 64 (r)).
{ transitivity (getr regs2 (20%bv : bv 5)); [unfold E5; apply hd_ewR; reflexivity|].
  transitivity (getr (ms_regs ms1) (20%bv : bv 5)); [exact PP20|].
  transitivity (ew E 20); [exact Q20 | exact F20]. }
assert (P21 : ew E5 21 = Z_to_bv 64 (i)).
{ transitivity (getr regs2 (21%bv : bv 5)); [unfold E5; apply hd_ewR; reflexivity|].
  transitivity (getr (ms_regs ms1) (21%bv : bv 5)); [exact PP21|].
  transitivity (ew E 21); [exact Q21 | exact F21]. }
assert (P22 : ew E5 22 = Z_to_bv 64 (hop)).
{ transitivity (getr regs2 (22%bv : bv 5)); [unfold E5; apply hd_ewR; reflexivity|].
  transitivity (getr (ms_regs ms1) (22%bv : bv 5)); [exact PP22|].
  transitivity (ew E 34); [exact Q22 | exact F34]. }
assert (P24 : ew E5 24 = Z_to_bv 64 (gSH cx fp)).
{ transitivity (getr regs2 (24%bv : bv 5)); [unfold E5; apply hd_ewR; reflexivity|].
  transitivity (getr (ms_regs ms1) (24%bv : bv 5)); [exact PP24|].
  transitivity (ew E 24); [exact Q24 | exact F24]. }
assert (P25 : ew E5 25 = Z_to_bv 64 (Boxreg.bx_fabric bs)).
{ transitivity (getr regs2 (25%bv : bv 5)); [unfold E5; apply hd_ewR; reflexivity|].
  transitivity (getr (ms_regs ms1) (25%bv : bv 5)); [exact PP25|].
  transitivity (ew E 25); [exact Q25 | exact F25]. }
assert (P26 : ew E5 26 = Z_to_bv 64 (Boxreg.bx_n bs)).
{ transitivity (getr regs2 (26%bv : bv 5)); [unfold E5; apply hd_ewR; reflexivity|].
  transitivity (getr (ms_regs ms1) (26%bv : bv 5)); [exact PP26|].
  transitivity (ew E 35); [exact Q26 | exact F35]. }
assert (U9b : bv_unsigned (ew E5 9) = c_sp1 cx) by (rewrite P9; apply unsigned_lit_small; lia).
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRESb & _).
assert (HS5 : st_ok_pi SEGS VAL E5 (mkSS 0x388 sr_atoms [R_s48; R_s68] None F_5)
  (restrict (w_H W3) (mkst regs2 (Z_to_bv 64 (BASE + 904)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - assert (RW5 : forall o, 72 <= o < 112 -> writable_at SEGS (mrestrict (w_H W3) mem2) (c_sp1 cx + o))
      by (intros o Ho; apply (apresent_writable SEGS); apply HPRESb; unfold GB_STK; lia).
    repeat apply Forall_cons; try apply Forall_nil; unfold R_s48, R_s68, YP09.region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
      rewrite U9b;
      (split; [lia|]); (split; [unfold M64; lia|]);
      (split; [intros o Ho; apply RW5; lia|]); apply Forall_nil.
  - apply pairwise_disjoint_of_extents.
    unfold R_s48, R_s68, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U9b. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
  - split; [|split; exact I].
    cbn [F_5 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite P9, P18, P20, P22, P24, P26.
    rewrite !unsigned_lit_small by lia.
    change (2 ^ 5) with 32. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end;
    first [exact I | exact Hsp32 | exact Hr16 | reflexivity | lia]. }
assert (SHOK5 : sh_ok SEGS Bx_H [] E5 (mrestrict (w_H W3) mem2)) by constructor.
assert (SEPff : forall a, gSH cx fp <= a < gSH cx fp + 64 -> ~ (gF cx fp <= a < gF cx fp + 512)).
{ intros a Ha Hcf. apply (fshadow_not_app (gF cx fp) 64 (gF cx fp) 512 a); [lia | lia | exact HFia | | exact Hcf].
  rewrite ESH in Ha. unfold SHADOW_OFF in Ha. exact Ha. }
assert (HL52 : length GSH_it = 52%nat) by (vm_compute; reflexivity).
assert (HL : Z.land hop 3 = hop mod 4)
  by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; reflexivity).
assert (HLb : 0 <= Z.land hop 3 < 4)
  by (rewrite HL; pose proof (Z.mod_pos_bound hop 4 ltac:(lia)); lia).
(* ---- the landing: from a state at a case pc with the dispatch's facts, the cut T ---- *)
assert (LAND : forall (op3 : Z) (msF : machine_state) (mdF : Model),
  0 <= op3 < 4 -> Z.land hop 3 = op3 ->
  ms_pc_val msF = w64 (BASE + GP_T op3) -> ms_resv msF = None -> ms_svc_pending msF = None ->
  ms_rom msF = seg_rom SEGS -> ms_fregs msF = fp_regs -> ms_fcsr msF = fp_csr ->
  gregs cx fp msF ->
  getr (ms_regs msF) 20 = w64 r -> getr (ms_regs msF) 22 = w64 hop ->
  getr (ms_regs msF) 25 = w64 (Boxreg.bx_fabric bs) -> getr (ms_regs msF) 26 = w64 (Boxreg.bx_n bs) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 72 <= a < c_sp1 cx + 80) ->
     ~ (c_sp1 cx + 104 <= a < c_sp1 cx + 112) ->
     aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) mem2 a) ->
  rdword (aview SEGS (w_H W3) (ms_mem msF)) (c_sp1 cx + 104) = Some i ->
  (op3 <= 1 -> rdword (aview SEGS (w_H W3) (ms_mem msF)) (c_sp1 cx + 72) = Some (Boxreg.bx_n bs)) ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 (ms_mem msF) mdF k ->
  SRr SEGS W3 (mkCfg msF mdF) (POST cx)).
{ intros op3 msF mdF Hop3r Hop3e Hpc5 Hrv5 Hsv5 Hrom5 Hfr5 Hfc5 HGR5 R20' R22' R25' R26' K5 SI SN HJF.
  assert (KFr : forall a, 0 <= a < 2 ^ 64 ->
    ~ (gF cx fp + GO_PREV <= a < gF cx fp + GO_PREV + 288) -> ~ (c_sp1 cx - 4096 <= a < c_sp1 cx) ->
    ~ (c_sp1 cx + 72 <= a < c_sp1 cx + 80) -> ~ (c_sp1 cx + 104 <= a < c_sp1 cx + 112) ->
    aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms1) a).
  { intros a Ha D1 D2 D3 D4. rewrite (K5 a Ha D3 D4). rewrite HES in HKC.
    apply (HKC a Ha D1). intros Hcw. apply D2. lia. }
  assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 136 <= a < c_sp1 cx + 152) ->
    ~ (gSH cx fp + 4 <= a < gSH cx fp + 44) ->
    ~ (gF cx fp + GO_PREV <= a < gF cx fp + GO_PREV + 288) -> ~ (c_sp1 cx - 4096 <= a < c_sp1 cx) ->
    ~ (c_sp1 cx + 72 <= a < c_sp1 cx + 80) -> ~ (c_sp1 cx + 104 <= a < c_sp1 cx + 112) ->
    aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha D0 Dsh D1 D2 D3 D4. rewrite (KFr a Ha D1 D2 D3 D4). exact (KEEP a Ha D0 Dsh). }
  assert (Kstk : forall a, c_sp1 cx + 16 <= a < c_sp1 cx + 136 ->
    ~ (c_sp1 cx + 72 <= a < c_sp1 cx + 80) -> ~ (c_sp1 cx + 104 <= a < c_sp1 cx + 112) ->
    aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a)
    by (intros a Ha D3 D4; apply KF; lia).
  assert (Ksv : forall a, spZ (c_regs cx) - 104 <= a < spZ (c_regs cx) ->
    aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a)
    by (intros a Ha; apply KF; lia).
  assert (Kfl : forall a, gF cx fp + 504 <= a < gF cx fp + 512 ->
    aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha. apply KF; [lia | lia | intros Hcx; apply (SEPff a); lia | lia | lia | lia | lia]. }
  assert (Ksh : forall a, gSH cx fp <= a < gSH cx fp + 52 ->
    aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms1) a).
  { intros a Ha. apply KFr; [lia | intros Hcx; apply (SEPff a); lia | lia | lia | lia]. }
  assert (Kcur : forall a, c_sp1 cx + 136 <= a < c_sp1 cx + 152 ->
    aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms1) a)
    by (intros a Ha; apply KFr; lia).
  assert (Kr : forall a, r <= a < r + 288 ->
    aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha. apply KF;
    [lia | lia | intros Hcx; apply (SEPfa a); lia | destruct SEPrF as [Hd | Hd]; lia | lia | lia | lia]. }
  assert (Kin : forall a, c_p cx <= a < c_p cx + c_n cx ->
    aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha. apply KF;
    [lia | lia | intros Hcx; apply (SEPinS a); lia | destruct SEPinF as [Hd | Hd]; lia | lia | lia | lia]. }
  eapply (HT op3 Hop3r); [exact HB | exact HJF | exact HFR | exact HMO |].
  unfold GI_T. exists r, bs, (pos + 1), hop.
  split.
  { unfold gb_body.
    split; [exact Hpc5|]. split; [exact Hrv5|]. split; [exact Hsv5|].
    split; [exact Hrom5|]. split; [exact Hfr5|]. split; [exact Hfc5|].
    split; [exact HGR5|].
    split.
    { destruct HSV as (Sra & Ssv). split.
      - apply (hd_rdword_keep W3 (ms_mem ms3)); [intros x Hx; apply Ksv; lia | exact Sra].
      - intros j Hj. apply (hd_rdword_keep W3 (ms_mem ms3)); [intros x Hx; apply Ksv; lia | exact (Ssv j Hj)]. }
    split.
    { intros j Hj. rewrite HL52 in Hj. rewrite Ksh by lia. exact (GSHit j Hj). }
    split; [exact HL52|].
    split.
    { apply (hd_rdword_keep W3 (ms_mem ms3)); [intros x Hx; rewrite Hfb in Hx; apply Kfl; lia | exact HFL]. }
    split.
    { destruct HSF as (K18 & K28 & K70 & K78 & K80). unfold gslot in K18, K28, K70, K78, K80 |- *.
      split; [apply (hd_rdword_keep W3 (ms_mem ms3)); [intros x Hx; apply Kstk; lia | exact K18]|].
      split; [apply (hd_rdword_keep W3 (ms_mem ms3)); [intros x Hx; apply Kstk; lia | exact K28]|].
      split; [apply (hd_rdword_keep W3 (ms_mem ms3)); [intros x Hx; apply Kstk; lia | exact K70]|].
      split; [apply (hd_rdword_keep W3 (ms_mem ms3)); [intros x Hx; apply Kstk; lia | exact K78]|].
      apply (hd_rdword_keep W3 (ms_mem ms3)); [intros x Hx; apply Kstk; lia | exact K80]. }
    apply (hd_garr8_keep W3 (ms_mem ms3)); [|exact HIN].
    intros x Hx. rewrite length_map in Hx. apply Kin. unfold c_n in *. lia. }
  split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact HBLK|].
  split.
  { split; [exact Hrin|]. split; [exact Hbslen|].
    intros ii Hii. change REG_SIZE with 288 in Hii. rewrite Kr by lia.
    exact (Hbsb ii ltac:(change REG_SIZE with 288; lia)). }
  split.
  { intros ii Hii. change REG_SIZE with 288 in Hii.
    rewrite (K5 (gF cx fp + GO_PREV + ii) ltac:(lia) ltac:(lia) ltac:(lia)).
    rewrite (HCPY ii ltac:(lia)).
    rewrite (KEEP (r + ii) ltac:(lia) ltac:(lia) ltac:(intros Hcx; apply (SEPfa (r + ii)); lia)).
    exact (Hbsb ii ltac:(change REG_SIZE with 288; lia)). }
  split; [exact HINV|].
  split; [lia|].
  split; [exact Hop3e|].
  split; [exact R20'|]. split; [exact R22'|]. split; [exact R25'|]. split; [exact R26'|].
  split.
  { destruct HSR as (M10 & M20 & M38 & M40 & M50 & M60). unfold gslot in M10, M20, M38, M40, M50, M60 |- *.
    split; [apply (hd_rdword_keep W3 (ms_mem ms3)); [intros x Hx; apply Kstk; lia | exact M10]|].
    split; [apply (hd_rdword_keep W3 (ms_mem ms3)); [intros x Hx; apply Kstk; lia | exact M20]|].
    split; [apply (hd_rdword_keep W3 (ms_mem ms3)); [intros x Hx; apply Kstk; lia | exact M38]|].
    split; [apply (hd_rdword_keep W3 (ms_mem ms3)); [intros x Hx; apply Kstk; lia | exact M40]|].
    split; [apply (hd_rdword_keep W3 (ms_mem ms3)); [intros x Hx; apply Kstk; lia | exact M50]|].
    apply (hd_rdword_keep W3 (ms_mem ms3)); [intros x Hx; apply Kstk; lia | exact M60]. }
  split.
  { split; [lia|]. unfold gslot. split.
    - replace (c_p cx + (pos + 1)) with (c_p cx + pos + 1) by lia.
      apply (hd_rdword_keep W3 (ms_mem ms1)); [intros x Hx; apply Kcur; lia | exact SL88].
    - replace (c_n cx - (pos + 1)) with (c_n cx - pos - 1) by lia.
      apply (hd_rdword_keep W3 (ms_mem ms1)); [intros x Hx; apply Kcur; lia | exact SL90]. }
  split; [exact SI | exact SN]. }
(* ---- 0x802d4 .. the four case pcs: the dispatch on op & 3 ---- *)
paj_run_tok RUN HS5 HJ2 SHOK5 Bspan_0;
  [ lazymatch goal with |- awr_ok ?E0 ?rsq ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rsq in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end;
    repeat first [ apply awr_ok_nil
                 | apply awr_ok_cons_ro; [cbn; lia|]
                 | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
                   [reflexivity | rewrite U9b; lia | cbn; unfold GB_STK; lia | cbn; lia |] ]
  | ].
assert (U22b : U E5 (SOff 22 0) = hop) by (apply (U_atom E5 22 hop P22); lia).
assert (UAND : U E5 (SAlu ALU_AND (SOff 22 0) (SLit 3)) = Z.land hop 3).
{ rewrite U_SAlu, U22b, (hd_U_lit_val E5 3 ltac:(lia)). cbn [zalu_raw]. apply hd_zcanon_in. lia. }
assert (BLT : branch_taken BC_LT (sv_denot E5 (SLit 1)) (sv_denot E5 (SAlu ALU_AND (SOff 22 0) (SLit 3)))
  = (1 <? Z.land hop 3)).
{ rewrite denot_lit_U, denot_lit_U, UAND, (hd_U_lit_val E5 1 ltac:(lia)).
  cbn [branch_taken]. apply Boxreg.lts_lit; lia. }
assert (BNE : forall z, 0 <= z < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E5 (SAlu ALU_AND (SOff 22 0) (SLit 3))) (sv_denot E5 (SLit z))
  = negb (Z.land hop 3 =? z)).
{ intros z Hz. rewrite branch_ne_U, UAND, (hd_U_lit_val E5 z Hz). reflexivity. }
psrr_branch_tok RUN BR HS5 SHOK5 Bspan_0.
{ (* 1 < op & 3: the cases 2 and 3 *)
  match goal with H : branch_taken BC_LT _ _ = _ |- _ => rewrite BLT in H; apply Z.ltb_lt in H; rename H into HLT end.
  paj_run_tok RUN HS5 HJ2 SHOK5 Bspan_0;
  [ lazymatch goal with |- awr_ok ?E0 ?rsq ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rsq in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end;
    repeat first [ apply awr_ok_nil
                 | apply awr_ok_cons_ro; [cbn; lia|]
                 | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
                   [reflexivity | rewrite U9b; lia | cbn; unfold GB_STK; lia | cbn; lia |] ]
  | ].
  psrr_branch_tok RUN BR HS5 SHOK5 Bspan_0.
  { (* op & 3 <> 2: the case 3 *)
    match goal with H : branch_taken BC_NE _ _ = _ |- _ =>
      rewrite (BNE 2 ltac:(lia)) in H; apply negb_true_iff, Z.eqb_neq in H; rename H into HNE end.
    paj_run_to_tok RUNTO HS5 HJ2 SHOK5 Bspan_0 1200;
  [ lazymatch goal with |- awr_ok ?E0 ?rsq ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rsq in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end;
    repeat first [ apply awr_ok_nil
                 | apply awr_ok_cons_ro; [cbn; lia|]
                 | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
                   [reflexivity | rewrite U9b; lia | cbn; unfold GB_STK; lia | cbn; lia |] ]
  | ].
    lazymatch goal with
    | A1 : frame_of _ _ mem2 ?x1, A2 : frame_of _ _ ?x1 ?x2, A3 : frame_of _ _ ?x2 ?x3 |- _ =>
      hd_mk_keep2 A1 W3 (c_sp1 cx + 72) (c_sp1 cx + 80) (c_sp1 cx + 104) (c_sp1 cx + 112) KX1;
      hd_mk_keep2 A2 W3 (c_sp1 cx + 72) (c_sp1 cx + 80) (c_sp1 cx + 104) (c_sp1 cx + 112) KX2;
      hd_mk_keep2 A3 W3 (c_sp1 cx + 72) (c_sp1 cx + 80) (c_sp1 cx + 104) (c_sp1 cx + 112) KX3;
      assert (K5 : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 72 <= a < c_sp1 cx + 80) ->
        ~ (c_sp1 cx + 104 <= a < c_sp1 cx + 112) ->
        aview SEGS (w_H W3) x3 a = aview SEGS (w_H W3) mem2 a)
        by (intros a Ha D3 D4; rewrite (KX3 a Ha D3 D4), (KX2 a Ha D3 D4); exact (KX1 a Ha D3 D4))
    end.
    lazymatch type of HS5 with st_ok_pi _ _ ?Ey ?ssy (restrict _ ?msy) =>
      pose proof (st_ok_pi_region_nth Ey ssy (restrict (w_H W3) msy) 1%nat _ HS5 eq_refl) as RG68;
      cbn [restrict ms_mem] in RG68;
      assert (SI : rdword (aview SEGS (w_H W3) (ms_mem msy)) (c_sp1 cx + 104) = Some i);
      [ apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem msy)); [|lia];
        exact (field_of_region Ey _ 9%nat (c_sp1 cx) _ _ _ _ _ 104 8%N (SOff 21 0) i RG68 U9b
                 ltac:(vm_compute; repeat first [exact (or_introl eq_refl) | apply or_intror])
                 (hd_den0 Ey 21 i P21) ltac:(cbn [Z.of_N]; change (8 * 8) with 64; lia)
                 ltac:(cbn [Z.of_N]; lia))
      | ] end.
    pmkst HS5.
    eapply (LAND 3); [lia | lia | reflexivity | reflexivity | reflexivity | reflexivity
    | reflexivity | reflexivity
    | unfold gregs; split; [hd_regval HS5|]; split; [hd_regval HS5|]; split; [hd_regval HS5|];
      split; [rewrite Hgp0; hd_regval HS5|]; split; [rewrite Htp0; hd_regval HS5|];
      split; [hd_regval HS5 | hd_regval HS5]
    | hd_regval HS5 | hd_regval HS5 | hd_regval HS5 | hd_regval HS5
    | exact K5 | exact SI
    | intros Hle; lia
    | exact HJ2 ].
  }
  { (* op & 3 = 2: the case 2 *)
    match goal with H : branch_taken BC_NE _ _ = _ |- _ =>
      rewrite (BNE 2 ltac:(lia)) in H; apply negb_false_iff, Z.eqb_eq in H; rename H into HNE end.
    paj_run_to_tok RUNTO HS5 HJ2 SHOK5 Bspan_0 1032;
  [ lazymatch goal with |- awr_ok ?E0 ?rsq ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rsq in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end;
    repeat first [ apply awr_ok_nil
                 | apply awr_ok_cons_ro; [cbn; lia|]
                 | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
                   [reflexivity | rewrite U9b; lia | cbn; unfold GB_STK; lia | cbn; lia |] ]
  | ].
    lazymatch goal with
    | A1 : frame_of _ _ mem2 ?x1, A2 : frame_of _ _ ?x1 ?x2, A3 : frame_of _ _ ?x2 ?x3 |- _ =>
      hd_mk_keep2 A1 W3 (c_sp1 cx + 72) (c_sp1 cx + 80) (c_sp1 cx + 104) (c_sp1 cx + 112) KX1;
      hd_mk_keep2 A2 W3 (c_sp1 cx + 72) (c_sp1 cx + 80) (c_sp1 cx + 104) (c_sp1 cx + 112) KX2;
      hd_mk_keep2 A3 W3 (c_sp1 cx + 72) (c_sp1 cx + 80) (c_sp1 cx + 104) (c_sp1 cx + 112) KX3;
      assert (K5 : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 72 <= a < c_sp1 cx + 80) ->
        ~ (c_sp1 cx + 104 <= a < c_sp1 cx + 112) ->
        aview SEGS (w_H W3) x3 a = aview SEGS (w_H W3) mem2 a)
        by (intros a Ha D3 D4; rewrite (KX3 a Ha D3 D4), (KX2 a Ha D3 D4); exact (KX1 a Ha D3 D4))
    end.
    lazymatch type of HS5 with st_ok_pi _ _ ?Ey ?ssy (restrict _ ?msy) =>
      pose proof (st_ok_pi_region_nth Ey ssy (restrict (w_H W3) msy) 1%nat _ HS5 eq_refl) as RG68;
      cbn [restrict ms_mem] in RG68;
      assert (SI : rdword (aview SEGS (w_H W3) (ms_mem msy)) (c_sp1 cx + 104) = Some i);
      [ apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem msy)); [|lia];
        exact (field_of_region Ey _ 9%nat (c_sp1 cx) _ _ _ _ _ 104 8%N (SOff 21 0) i RG68 U9b
                 ltac:(vm_compute; repeat first [exact (or_introl eq_refl) | apply or_intror])
                 (hd_den0 Ey 21 i P21) ltac:(cbn [Z.of_N]; change (8 * 8) with 64; lia)
                 ltac:(cbn [Z.of_N]; lia))
      | ] end.
    pmkst HS5.
    eapply (LAND 2); [lia | lia | reflexivity | reflexivity | reflexivity | reflexivity
    | reflexivity | reflexivity
    | unfold gregs; split; [hd_regval HS5|]; split; [hd_regval HS5|]; split; [hd_regval HS5|];
      split; [rewrite Hgp0; hd_regval HS5|]; split; [rewrite Htp0; hd_regval HS5|];
      split; [hd_regval HS5 | hd_regval HS5]
    | hd_regval HS5 | hd_regval HS5 | hd_regval HS5 | hd_regval HS5
    | exact K5 | exact SI
    | intros Hle; lia
    | exact HJ2 ].
  } }
{ (* op & 3 <= 1: the cases 0 and 1 *)
  match goal with H : branch_taken BC_LT _ _ = _ |- _ => rewrite BLT in H; apply Z.ltb_ge in H; rename H into HLT end.
  paj_run_tok RUN HS5 HJ2 SHOK5 Bspan_0;
  [ lazymatch goal with |- awr_ok ?E0 ?rsq ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rsq in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end;
    repeat first [ apply awr_ok_nil
                 | apply awr_ok_cons_ro; [cbn; lia|]
                 | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
                   [reflexivity | rewrite U9b; lia | cbn; unfold GB_STK; lia | cbn; lia |] ]
  | ].
  psrr_branch_tok RUN BR HS5 SHOK5 Bspan_0.
  { (* op & 3 <> 0: the case 1 *)
    match goal with H : branch_taken BC_NE _ _ = _ |- _ =>
      rewrite (BNE 0 ltac:(lia)) in H; apply negb_true_iff, Z.eqb_neq in H; rename H into HNE end.
    paj_run_to_tok RUNTO HS5 HJ2 SHOK5 Bspan_0 1116;
  [ lazymatch goal with |- awr_ok ?E0 ?rsq ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rsq in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end;
    repeat first [ apply awr_ok_nil
                 | apply awr_ok_cons_ro; [cbn; lia|]
                 | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
                   [reflexivity | rewrite U9b; lia | cbn; unfold GB_STK; lia | cbn; lia |] ]
  | ].
    lazymatch goal with
    | A1 : frame_of _ _ mem2 ?x1, A2 : frame_of _ _ ?x1 ?x2, A3 : frame_of _ _ ?x2 ?x3 |- _ =>
      hd_mk_keep2 A1 W3 (c_sp1 cx + 72) (c_sp1 cx + 80) (c_sp1 cx + 104) (c_sp1 cx + 112) KX1;
      hd_mk_keep2 A2 W3 (c_sp1 cx + 72) (c_sp1 cx + 80) (c_sp1 cx + 104) (c_sp1 cx + 112) KX2;
      hd_mk_keep2 A3 W3 (c_sp1 cx + 72) (c_sp1 cx + 80) (c_sp1 cx + 104) (c_sp1 cx + 112) KX3;
      assert (K5 : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 72 <= a < c_sp1 cx + 80) ->
        ~ (c_sp1 cx + 104 <= a < c_sp1 cx + 112) ->
        aview SEGS (w_H W3) x3 a = aview SEGS (w_H W3) mem2 a)
        by (intros a Ha D3 D4; rewrite (KX3 a Ha D3 D4), (KX2 a Ha D3 D4); exact (KX1 a Ha D3 D4))
    end.
    lazymatch type of HS5 with st_ok_pi _ _ ?Ey ?ssy (restrict _ ?msy) =>
      pose proof (st_ok_pi_region_nth Ey ssy (restrict (w_H W3) msy) 1%nat _ HS5 eq_refl) as RG68;
      cbn [restrict ms_mem] in RG68;
      assert (SI : rdword (aview SEGS (w_H W3) (ms_mem msy)) (c_sp1 cx + 104) = Some i);
      [ apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem msy)); [|lia];
        exact (field_of_region Ey _ 9%nat (c_sp1 cx) _ _ _ _ _ 104 8%N (SOff 21 0) i RG68 U9b
                 ltac:(vm_compute; repeat first [exact (or_introl eq_refl) | apply or_intror])
                 (hd_den0 Ey 21 i P21) ltac:(cbn [Z.of_N]; change (8 * 8) with 64; lia)
                 ltac:(cbn [Z.of_N]; lia))
      | ] end.
    lazymatch type of HS5 with st_ok_pi _ _ ?Ey ?ssy (restrict _ ?msy) =>
      pose proof (st_ok_pi_region_nth Ey ssy (restrict (w_H W3) msy) 0%nat _ HS5 eq_refl) as RG48;
      cbn [restrict ms_mem] in RG48;
      assert (SN : rdword (aview SEGS (w_H W3) (ms_mem msy)) (c_sp1 cx + 72) = Some (Boxreg.bx_n bs));
      [ apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem msy)); [|lia];
        exact (field_of_region Ey _ 9%nat (c_sp1 cx) _ _ _ _ _ 72 8%N (SOff 26 0) (Boxreg.bx_n bs) RG48 U9b
                 ltac:(vm_compute; repeat first [exact (or_introl eq_refl) | apply or_intror])
                 (hd_den0 Ey 26 (Boxreg.bx_n bs) P26) ltac:(cbn [Z.of_N]; change (8 * 8) with 64; lia)
                 ltac:(cbn [Z.of_N]; lia))
      | ] end.
    pmkst HS5.
    eapply (LAND 1); [lia | lia | reflexivity | reflexivity | reflexivity | reflexivity
    | reflexivity | reflexivity
    | unfold gregs; split; [hd_regval HS5|]; split; [hd_regval HS5|]; split; [hd_regval HS5|];
      split; [rewrite Hgp0; hd_regval HS5|]; split; [rewrite Htp0; hd_regval HS5|];
      split; [hd_regval HS5 | hd_regval HS5]
    | hd_regval HS5 | hd_regval HS5 | hd_regval HS5 | hd_regval HS5
    | exact K5 | exact SI
    | intros _; exact SN
    | exact HJ2 ].
  }
  { (* op & 3 = 0: the case 0 *)
    match goal with H : branch_taken BC_NE _ _ = _ |- _ =>
      rewrite (BNE 0 ltac:(lia)) in H; apply negb_false_iff, Z.eqb_eq in H; rename H into HNE end.
    paj_run_to_tok RUNTO HS5 HJ2 SHOK5 Bspan_0 928;
  [ lazymatch goal with |- awr_ok ?E0 ?rsq ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rsq in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end;
    repeat first [ apply awr_ok_nil
                 | apply awr_ok_cons_ro; [cbn; lia|]
                 | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
                   [reflexivity | rewrite U9b; lia | cbn; unfold GB_STK; lia | cbn; lia |] ]
  | ].
    lazymatch goal with
    | A1 : frame_of _ _ mem2 ?x1, A2 : frame_of _ _ ?x1 ?x2, A3 : frame_of _ _ ?x2 ?x3 |- _ =>
      hd_mk_keep2 A1 W3 (c_sp1 cx + 72) (c_sp1 cx + 80) (c_sp1 cx + 104) (c_sp1 cx + 112) KX1;
      hd_mk_keep2 A2 W3 (c_sp1 cx + 72) (c_sp1 cx + 80) (c_sp1 cx + 104) (c_sp1 cx + 112) KX2;
      hd_mk_keep2 A3 W3 (c_sp1 cx + 72) (c_sp1 cx + 80) (c_sp1 cx + 104) (c_sp1 cx + 112) KX3;
      assert (K5 : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 72 <= a < c_sp1 cx + 80) ->
        ~ (c_sp1 cx + 104 <= a < c_sp1 cx + 112) ->
        aview SEGS (w_H W3) x3 a = aview SEGS (w_H W3) mem2 a)
        by (intros a Ha D3 D4; rewrite (KX3 a Ha D3 D4), (KX2 a Ha D3 D4); exact (KX1 a Ha D3 D4))
    end.
    lazymatch type of HS5 with st_ok_pi _ _ ?Ey ?ssy (restrict _ ?msy) =>
      pose proof (st_ok_pi_region_nth Ey ssy (restrict (w_H W3) msy) 1%nat _ HS5 eq_refl) as RG68;
      cbn [restrict ms_mem] in RG68;
      assert (SI : rdword (aview SEGS (w_H W3) (ms_mem msy)) (c_sp1 cx + 104) = Some i);
      [ apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem msy)); [|lia];
        exact (field_of_region Ey _ 9%nat (c_sp1 cx) _ _ _ _ _ 104 8%N (SOff 21 0) i RG68 U9b
                 ltac:(vm_compute; repeat first [exact (or_introl eq_refl) | apply or_intror])
                 (hd_den0 Ey 21 i P21) ltac:(cbn [Z.of_N]; change (8 * 8) with 64; lia)
                 ltac:(cbn [Z.of_N]; lia))
      | ] end.
    lazymatch type of HS5 with st_ok_pi _ _ ?Ey ?ssy (restrict _ ?msy) =>
      pose proof (st_ok_pi_region_nth Ey ssy (restrict (w_H W3) msy) 0%nat _ HS5 eq_refl) as RG48;
      cbn [restrict ms_mem] in RG48;
      assert (SN : rdword (aview SEGS (w_H W3) (ms_mem msy)) (c_sp1 cx + 72) = Some (Boxreg.bx_n bs));
      [ apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem msy)); [|lia];
        exact (field_of_region Ey _ 9%nat (c_sp1 cx) _ _ _ _ _ 72 8%N (SOff 26 0) (Boxreg.bx_n bs) RG48 U9b
                 ltac:(vm_compute; repeat first [exact (or_introl eq_refl) | apply or_intror])
                 (hd_den0 Ey 26 (Boxreg.bx_n bs) P26) ltac:(cbn [Z.of_N]; change (8 * 8) with 64; lia)
                 ltac:(cbn [Z.of_N]; lia))
      | ] end.
    pmkst HS5.
    eapply (LAND 0); [lia | lia | reflexivity | reflexivity | reflexivity | reflexivity
    | reflexivity | reflexivity
    | unfold gregs; split; [hd_regval HS5|]; split; [hd_regval HS5|]; split; [hd_regval HS5|];
      split; [rewrite Hgp0; hd_regval HS5|]; split; [rewrite Htp0; hd_regval HS5|];
      split; [hd_regval HS5 | hd_regval HS5]
    | hd_regval HS5 | hd_regval HS5 | hd_regval HS5 | hd_regval HS5
    | exact K5 | exact SI
    | intros _; exact SN
    | exact HJ2 ].
  } }
Qed.
End c.
End b.
End a.
