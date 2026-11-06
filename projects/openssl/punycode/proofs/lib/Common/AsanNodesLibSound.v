(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Znumtheory.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg AgentLib
  AsanAcct AsanAcctShape SpinAlg Hoare.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound
  AsanPlanSoundSums AsanNodesLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module LBNS.
Import AX2. Import AX2S. Import AP. Import APS. Import APSX. Import LBN.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Specs.
Variable SEGS : list Segment.

Definition W (z : Z) : word := Z_to_bv 64 z.
Definition rd_ok (M : word -> option byte) (a n : Z) : Prop := forall i, 0 <= i < n -> M (W (a + i)) <> None.
Definition wr_ok (M : word -> option byte) (a n : Z) : Prop :=
  forall x (m : nat), a <= x -> x + Z.of_nat m <= a + n -> store_ok SEGS M (W x) m = true.
Definition cell (M : word -> option byte) (a : Z) (n : nat) (v : word) : Prop :=
  rdn SEGS M (W a) n = Some (word_to_le_bytes n v).
Definition img_ok (M : word -> option byte) (lo hi : Z) : Prop := forall i, lo <= i < hi -> M (W i) = None.
Definition inr (x : word) (a n : Z) : Prop := a <= bv_unsigned x < a + n.

Definition KSdec : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
(* [comment removed for export] *)
Definition dec_FP_x (fr sp out q mx : Z) (x : word) : Prop :=
  inr x (sp - fr) fr \/ inr x out (4 * mx) \/ inr x q 4.

Definition decode_contract_x (fr : Z) (strict : bool) (entry imgend : Z) : Prop :=
  if strict then
  forall regs M (ret : word) sp p n out q mx,
    getr regs 1%bv = ret -> v_jalr ret 0 = ret ->
    getr regs 2%bv = W sp -> getr regs 10%bv = W p -> getr regs 11%bv = W n ->
    getr regs 12%bv = W out -> getr regs 13%bv = W q ->
    0 <= n < 2 ^ 31 -> 0 <= p -> p + n < 2 ^ 63 -> rd_ok M p n ->
    0 <= mx <= 512 -> cell M q 4 (W mx) ->
    imgend <= sp - fr -> sp < 2 ^ 63 -> wr_ok M (sp - fr) fr ->
    imgend <= out -> out + 4 * mx < 2 ^ 63 -> wr_ok M out (4 * mx) ->
    imgend <= q -> q + 4 < 2 ^ 63 -> wr_ok M q 4 ->
    (out + 4 * mx <= sp - fr \/ sp <= out) -> (q + 4 <= sp - fr \/ sp <= q) ->
    (n = 0 \/ 0 < p) -> out mod 4 = 0 -> q mod 4 = 0 ->
    exists regs' M',
      msteps SEGS (mkst regs (W entry) M (seg_rom SEGS)) (mkst regs' ret M' (seg_rom SEGS))
      /\ (forall r : bv 5, ~ In (ridx r) KSdec -> getr regs' r = getr regs r)
      /\ (forall x, ~ dec_FP_x fr sp out q mx x -> M' x = M x) /\ mem_grows M M'
  else
  forall regs M (ret : word) sp p n out q mx,
    getr regs 1%bv = ret -> v_jalr ret 0 = ret ->
    getr regs 2%bv = W sp -> getr regs 10%bv = W p -> getr regs 11%bv = W n ->
    getr regs 12%bv = W out -> getr regs 13%bv = W q ->
    0 <= n < 2 ^ 31 -> 0 <= p -> p + n < 2 ^ 63 -> rd_ok M p n ->
    0 <= mx <= 512 -> cell M q 4 (W mx) ->
    imgend <= sp - fr -> sp < 2 ^ 63 -> wr_ok M (sp - fr) fr ->
    imgend <= out -> out + 4 * mx < 2 ^ 63 -> wr_ok M out (4 * mx) ->
    imgend <= q -> q + 4 < 2 ^ 63 -> wr_ok M q 4 ->
    (out + 4 * mx <= sp - fr \/ sp <= out) -> (q + 4 <= sp - fr \/ sp <= q) ->
    exists regs' M',
      msteps SEGS (mkst regs (W entry) M (seg_rom SEGS)) (mkst regs' ret M' (seg_rom SEGS))
      /\ (forall r : bv 5, ~ In (ridx r) KSdec -> getr regs' r = getr regs r)
      /\ (forall x, ~ dec_FP_x fr sp out q mx x -> M' x = M x) /\ mem_grows M M'.
(* [comment removed for export] *)
Definition dec_FP (sp out q mx : Z) (x : word) : Prop := dec_FP_x 144 sp out q mx x.
Definition decode_contract (entry imgend : Z) : Prop := decode_contract_x 144 false entry imgend.

Definition a2u_FP_x (D S out : Z) (x : word) : Prop :=
  inr x (S - D) (D - 2216) \/ inr x (S - 2200) 16 \/ inr x (S - 2160) 2048 \/ inr x out 16.

Definition a2uloop_contract_x (D : Z) (strict : bool) (entry exit imgend : Z) (rodata : list (Z * Z)) : Prop :=
  if strict then
  forall regs M S b len N out sb (eb : word),
    getr regs 2%bv = W (S - 2240) -> getr regs 8%bv = W S -> getr regs 19%bv = W b ->
    cell M (S - 2216) 8 (W 0) -> cell M (S - 2216 + 8) 8 (W out) -> cell M (S - 2216 + 16) 8 (W 0) ->
    cell M (S - 2216 + 24) 8 (W 0) -> cell M (S - 2216 + 32) 8 (W 16) -> cell M (S - 2216 + 40) 8 (W sb) ->
    cell M (S - 2216 + 48) 1 eb -> (bv_unsigned eb mod 2 ^ 8) mod 2 = 0 -> 0 < sb < 2 ^ 64 ->
    0 <= len < 2 ^ 31 -> len < N -> 0 < b -> b + N < 2 ^ 63 -> rd_ok M b N ->
    M (W (b + len)) = Some (Z_to_bv 8 0) -> (b + len) / 8 * 8 + 8 <= b + N ->
    Forall (fun r => img_ok M (fst r) (snd r)) rodata ->
    imgend <= S - D -> S < 2 ^ 63 ->
    wr_ok M (S - D) (D - 2216) -> wr_ok M (S - 2200) 16 -> wr_ok M (S - 2160) 2048 ->
    imgend <= out -> out + 16 < 2 ^ 63 -> wr_ok M out 16 ->
    (out + 16 <= S - D \/ S <= out) -> (b + N <= S - D \/ S <= b) -> (b + N <= out \/ out + 16 <= b) ->
    S mod 8 = 0 ->
    exists regs' M',
      msteps SEGS (mkst regs (W entry) M (seg_rom SEGS)) (mkst regs' (W exit) M' (seg_rom SEGS))
      /\ getr regs' 2%bv = getr regs 2%bv /\ getr regs' 3%bv = getr regs 3%bv
      /\ getr regs' 4%bv = getr regs 4%bv /\ getr regs' 8%bv = getr regs 8%bv
      /\ (forall x, ~ a2u_FP_x D S out x -> M' x = M x) /\ mem_grows M M'
  else
  forall regs M S b len N out sb (eb : word),
    getr regs 2%bv = W (S - 2240) -> getr regs 8%bv = W S -> getr regs 19%bv = W b ->
    cell M (S - 2216) 8 (W 0) -> cell M (S - 2216 + 8) 8 (W out) -> cell M (S - 2216 + 16) 8 (W 0) ->
    cell M (S - 2216 + 24) 8 (W 0) -> cell M (S - 2216 + 32) 8 (W 16) -> cell M (S - 2216 + 40) 8 (W sb) ->
    cell M (S - 2216 + 48) 1 eb -> (bv_unsigned eb mod 2 ^ 8) mod 2 = 0 -> 0 < sb < 2 ^ 64 ->
    0 <= len < 2 ^ 31 -> len < N -> 0 < b -> b + N < 2 ^ 63 -> rd_ok M b N ->
    M (W (b + len)) = Some (Z_to_bv 8 0) -> (b + len) / 8 * 8 + 8 <= b + N ->
    Forall (fun r => img_ok M (fst r) (snd r)) rodata ->
    imgend <= S - D -> S < 2 ^ 63 ->
    wr_ok M (S - D) (D - 2216) -> wr_ok M (S - 2200) 16 -> wr_ok M (S - 2160) 2048 ->
    imgend <= out -> out + 16 < 2 ^ 63 -> wr_ok M out 16 ->
    (out + 16 <= S - D \/ S <= out) -> (b + N <= S - D \/ S <= b) -> (b + N <= out \/ out + 16 <= b) ->
    exists regs' M',
      msteps SEGS (mkst regs (W entry) M (seg_rom SEGS)) (mkst regs' (W exit) M' (seg_rom SEGS))
      /\ getr regs' 2%bv = getr regs 2%bv /\ getr regs' 3%bv = getr regs 3%bv
      /\ getr regs' 4%bv = getr regs 4%bv /\ getr regs' 8%bv = getr regs 8%bv
      /\ (forall x, ~ a2u_FP_x D S out x -> M' x = M x) /\ mem_grows M M'.
Definition a2u_FP (S out : Z) (x : word) : Prop := a2u_FP_x 2384 S out x.
Definition a2uloop_contract (entry exit imgend : Z) (rodata : list (Z * Z)) : Prop := a2uloop_contract_x 2384 false entry exit imgend rodata.

(* [comment removed for export] *)
Lemma decode_contract_x_use : forall fr strict entry imgend, decode_contract_x fr strict entry imgend ->
  forall regs M (ret : word) sp p n out q mx,
    getr regs 1%bv = ret -> v_jalr ret 0 = ret ->
    getr regs 2%bv = W sp -> getr regs 10%bv = W p -> getr regs 11%bv = W n ->
    getr regs 12%bv = W out -> getr regs 13%bv = W q ->
    0 <= n < 2 ^ 31 -> 0 <= p -> p + n < 2 ^ 63 -> rd_ok M p n ->
    0 <= mx <= 512 -> cell M q 4 (W mx) ->
    imgend <= sp - fr -> sp < 2 ^ 63 -> wr_ok M (sp - fr) fr ->
    imgend <= out -> out + 4 * mx < 2 ^ 63 -> wr_ok M out (4 * mx) ->
    imgend <= q -> q + 4 < 2 ^ 63 -> wr_ok M q 4 ->
    (out + 4 * mx <= sp - fr \/ sp <= out) -> (q + 4 <= sp - fr \/ sp <= q) ->
    (strict = true -> (n = 0 \/ 0 < p) /\ out mod 4 = 0 /\ q mod 4 = 0) ->
    exists regs' M',
      msteps SEGS (mkst regs (W entry) M (seg_rom SEGS)) (mkst regs' ret M' (seg_rom SEGS))
      /\ (forall r : bv 5, ~ In (ridx r) KSdec -> getr regs' r = getr regs r)
      /\ (forall x, ~ dec_FP_x fr sp out q mx x -> M' x = M x) /\ mem_grows M M'.
Proof.
  intros fr strict entry imgend H. unfold decode_contract_x in H. destruct strict; intros; [|eapply H; eassumption].
  match goal with X : true = true -> _ |- _ => destruct (X eq_refl) as (X1 & X2 & X3) end.
  eapply H; eassumption.
Qed.

Lemma a2uloop_contract_x_use : forall D strict entry exit imgend rodata, a2uloop_contract_x D strict entry exit imgend rodata ->
  forall regs M S b len N out sb (eb : word),
    getr regs 2%bv = W (S - 2240) -> getr regs 8%bv = W S -> getr regs 19%bv = W b ->
    cell M (S - 2216) 8 (W 0) -> cell M (S - 2216 + 8) 8 (W out) -> cell M (S - 2216 + 16) 8 (W 0) ->
    cell M (S - 2216 + 24) 8 (W 0) -> cell M (S - 2216 + 32) 8 (W 16) -> cell M (S - 2216 + 40) 8 (W sb) ->
    cell M (S - 2216 + 48) 1 eb -> (bv_unsigned eb mod 2 ^ 8) mod 2 = 0 -> 0 < sb < 2 ^ 64 ->
    0 <= len < 2 ^ 31 -> len < N -> 0 < b -> b + N < 2 ^ 63 -> rd_ok M b N ->
    M (W (b + len)) = Some (Z_to_bv 8 0) -> (b + len) / 8 * 8 + 8 <= b + N ->
    Forall (fun r => img_ok M (fst r) (snd r)) rodata ->
    imgend <= S - D -> S < 2 ^ 63 ->
    wr_ok M (S - D) (D - 2216) -> wr_ok M (S - 2200) 16 -> wr_ok M (S - 2160) 2048 ->
    imgend <= out -> out + 16 < 2 ^ 63 -> wr_ok M out 16 ->
    (out + 16 <= S - D \/ S <= out) -> (b + N <= S - D \/ S <= b) -> (b + N <= out \/ out + 16 <= b) ->
    (strict = true -> S mod 8 = 0) ->
    exists regs' M',
      msteps SEGS (mkst regs (W entry) M (seg_rom SEGS)) (mkst regs' (W exit) M' (seg_rom SEGS))
      /\ getr regs' 2%bv = getr regs 2%bv /\ getr regs' 3%bv = getr regs 3%bv
      /\ getr regs' 4%bv = getr regs 4%bv /\ getr regs' 8%bv = getr regs 8%bv
      /\ (forall x, ~ a2u_FP_x D S out x -> M' x = M x) /\ mem_grows M M'.
Proof.
  intros D strict entry exit imgend rodata H. unfold a2uloop_contract_x in H. destruct strict; intros; [|eapply H; eassumption].
  match goal with X : true = true -> _ |- _ => specialize (X eq_refl) end.
  eapply H; eassumption.
Qed.
End Specs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u_W : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (W z) = z.
Proof. intros z Hz. unfold W. apply u64_lit. exact Hz. Qed.

Lemma u_Zbv_mod : forall z, bv_unsigned (Z_to_bv 64 z) = z mod 2 ^ 64.
Proof. intros z. rewrite Z_to_bv_unsigned. unfold bv_wrap. reflexivity. Qed.

(* [comment removed for export] *)
Lemma start_eq : forall E e b o off n,
  split_lit e = (b, o) ->
  0 <= estart E (SA b (o + off)) -> estart E (SA b (o + off)) + n <= 2 ^ 64 -> 0 < n -> off <= 0 ->
  - off <= bv_unsigned (edenot E e) ->
  estart E (SA b (o + off)) = bv_unsigned (edenot E e) + off.
Proof.
  intros E e b o off n Hsp H0 Hn Hpos Hoff Ha.
  assert (Ee : bv_unsigned (edenot E e) = (bv_unsigned (edenot E b) + o) mod 2 ^ 64).
  { rewrite (w_split_lit_denot E e b o Hsp). apply u_Zbv_mod. }
  rewrite Ee in *. clear Ee.
  unfold estart in *. cbn [a_base a_off] in *.
  remember (bv_unsigned (edenot E b) + o) as z eqn:Hzd.
  replace (bv_unsigned (edenot E b) + (o + off)) with (z + off) in * by lia.
  pose proof (Z.mod_pos_bound z (2 ^ 64) ltac:(lia)) as Hm.
  destruct (Z_lt_le_dec z (2 ^ 64)) as [Hlt|Hge].
  - rewrite Z.mod_small by lia. lia.
  - exfalso.
    assert (Hz2 : z - 2 ^ 64 < 2 ^ 64) by lia.
    assert (Em : z mod 2 ^ 64 = z - 2 ^ 64).
    { replace z with ((z - 2 ^ 64) + 1 * 2 ^ 64) at 1 by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    lia.
Qed.

Section Sound.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_okP A.
Hypothesis HULL_le : img_lo A <= img_hi A.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable ISP : Z.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a.
Hypothesis NX0_spw : AP.expr_vars_lt nx0 e_spw = true.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Variable FS0 : Fs.Fs.
Variable T : libtab.
Hypothesis IMGEND_pos : 0 <= lt_imgend T.

#[local] Notation cfg := (cfg_of SEGS) (only parsing).
#[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH ISP FS0) (only parsing).
#[local] Notation MR := (Mr A argH) (only parsing).

(* [comment removed for export] *)
Lemma wview_off_hull : forall (M : word -> option byte) (x : word),
  in_hull A (bv_unsigned x) = false -> wview SEGS M x <> None -> M x <> None.
Proof.
  intros M x Hh Hw HN. apply Hw. unfold wview. rewrite HN, (SEGS_in_hull x Hh). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ovl_ok_sound : forall E M k e n,
  know_ok SEGS E M k -> ovl_ok A k e n = true -> 0 < elenZ E n ->
  let a := bv_unsigned (edenot E e) in
  rd_ok M a (elenZ E n) /\ a + elenZ E n <= 2 ^ 64
  /\ (forall m, Z.of_nat m <= elenZ E n -> store_ok SEGS M (W a) m = true)
  /\ (a + elenZ E n <= img_lo A \/ img_hi A <= a)
  /\ estart E (SA (fst (split_lit e)) (snd (split_lit e))) = a.
Proof.
  intros E M k e n HK H Hpos a. unfold ovl_ok in H. destruct (split_lit e) as [b o] eqn:Hsp. cbn [fst snd].
  apply andb_prop in H as [Hw Hoff].
  destruct (kwritable_x_sound SEGS E M k k b o n HK HK Hw) as (Wst & Wlo & Whi).
  unfold off_image_x in Hoff.
  pose proof (ranges_apart_x_sound SEGS E M k b o n (ELit 0) (img_lo A) (ELit (img_hi A - img_lo A)) HK Hoff) as Hap.
  destruct HULL_ok as (H0 & _ & _ & Hhi). unfold KHI in Hhi.
  assert (Es : estart E (SA (ELit 0) (img_lo A)) = img_lo A).
  { unfold estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia. lia. }
  assert (El : elenZ E (ELit (img_hi A - img_lo A)) = img_hi A - img_lo A).
  { unfold elenZ. cbn [edenot]. apply u64_lit. lia. }
  rewrite Es, El in Hap.
  assert (Ea : estart E (SA b o) = a).
  { replace o with (o + 0) by lia. unfold a. rewrite (start_eq E e b o 0 (elenZ E n) Hsp); try lia.
    - replace (o + 0) with o by lia. exact Wlo.
    - replace (o + 0) with o by lia. exact Whi.
    - pose proof (u64_range (edenot E e)). lia. }
  rewrite Ea in *.
  assert (Hst : forall m, Z.of_nat m <= elenZ E n -> store_ok SEGS M (W a) m = true) by (intros m Hm; apply Wst; exact Hm).
  split; [|split; [lia | split; [exact Hst | split; [lia | reflexivity]]]].
  intros i Hi.
  assert (Hu : bv_unsigned (W (a + i)) = a + i) by (apply u_W; lia).
  apply wview_off_hull.
  - rewrite Hu. unfold in_hull. destruct (Z.leb_spec (img_lo A) (a + i)); destruct (Z.ltb_spec (a + i) (img_hi A)); cbn; try reflexivity. lia.
  - apply (store_ok_all SEGS M (Z.to_nat (elenZ E n)) (W a)).
    + rewrite u_W by lia. lia.
    + apply Hst. lia.
    + rewrite Hu, u_W by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma stk_ok_sound : forall E M k e off n,
  know_ok SEGS E M k -> stk_ok T k e off n = true -> 0 < n < 2 ^ 63 -> off <= 0 ->
  let a := bv_unsigned (edenot E e) in
  wr_ok SEGS M (a + off) n /\ lt_imgend T <= a + off /\ a + off + n < 2 ^ 63
  /\ estart E (SA (fst (split_lit e)) (snd (split_lit e) + off)) = a + off.
Proof.
  intros E M k e off n HK H Hn Hoff a. unfold stk_ok in H. destruct (split_lit e) as [b o] eqn:Hsp.
  apply andb_prop in H as [Hw Hin]. cbn [fst snd].
  assert (El : elenZ E (ELit n) = n) by (unfold elenZ; cbn [edenot]; apply u64_lit; lia).
  destruct (kwritable_x_sound SEGS E M k k b (o + off) (ELit n) HK HK Hw) as (Wst & Wlo & Whi). rewrite El in *.
  unfold addr_in in Hin.
  destruct (xlo k e) as [l|] eqn:Hl; [|discriminate]. destruct (xhi k e) as [h|] eqn:Hh; [|discriminate].
  apply andb_prop in Hin as [Hl1 Hh1]. apply Z.leb_le in Hl1. apply Z.leb_le in Hh1.
  pose proof (xlo_sound SEGS E M k e l HK Hl) as Bl. pose proof (xhi_sound SEGS E M k e h HK Hh) as Bh. fold a in Bl, Bh.
  assert (Es : estart E (SA b (o + off)) = a + off).
  { unfold a. apply (start_eq E e b o off n Hsp); fold a; lia. }
  rewrite Es in *.
  split; [|split; [lia | split; [lia | reflexivity]]].
  intros x m Hx Hxm.
  apply (store_ok_sub SEGS M (Z_to_bv 64 (a + off)) (Z.to_nat n) (W x) m).
  - rewrite u64_lit by lia. lia.
  - apply Wst. lia.
  - rewrite u64_lit by lia. rewrite u_W by lia. lia.
  - rewrite u64_lit by lia. rewrite u_W by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma hav_sound : forall E (M M' : word -> option byte) k e off n,
  know_ok SEGS E M k -> 0 < n < 2 ^ 63 ->
  estart E (SA (fst (split_lit e)) (snd (split_lit e) + off)) = bv_unsigned (edenot E e) + off ->
  (forall x : word, ~ inr x (bv_unsigned (edenot E e) + off) n -> M' x = M x) -> mem_grows M M' ->
  know_ok SEGS E M' (hav k e off n).
Proof.
  intros E M M' k e off n HK Hn Es Hout Hg. unfold hav. destruct (split_lit e) as [b o] eqn:Hsp. cbn [fst snd] in Es.
  apply (w_know_ok_havoc SEGS E M M' k b (o + off) (ELit n) HK); [|exact Hg].
  intros x Hx. apply Hout. unfold inr. rewrite Es in Hx.
  assert (El : elenZ E (ELit n) = n) by (unfold elenZ; cbn [edenot]; apply u64_lit; lia).
  rewrite El in Hx. lia.
Qed.

(* [comment removed for export] *)
Definition mixm (P : word -> bool) (M M' : word -> option byte) : word -> option byte := fun x => if P x then M' x else M x.
Definition inrb (a n : Z) (x : word) : bool := Z.leb a (bv_unsigned x) && Z.ltb (bv_unsigned x) (a + n).
Lemma inrb_inr : forall a n x, inrb a n x = true <-> inr x a n.
Proof. intros a n x. unfold inrb, inr. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. Qed.
Lemma mixm_grows : forall P M M', mem_grows M M' -> mem_grows M (mixm P M M').
Proof. intros P M M' Hg x Hx. unfold mixm. destruct (P x); [apply Hg|]; exact Hx. Qed.
Lemma mixm_grows2 : forall P Q M M', mem_grows M M' -> (forall x, P x = true -> Q x = true) -> mem_grows (mixm P M M') (mixm Q M M').
Proof.
  intros P Q M M' Hg HPQ x Hx. unfold mixm in *. destruct (P x) eqn:HP.
  - rewrite (HPQ x HP). exact Hx.
  - destruct (Q x); [apply Hg|]; exact Hx.
Qed.

(* [comment removed for export] *)
Lemma lookup_cell : forall E M k e off w v hs,
  know_ok SEGS E M k -> (1 <= w <= 8)%nat ->
  know_lookup SEGS k (fst (split_lit e)) (snd (split_lit e) + off) w false [] [] = LHit v [] hs ->
  estart E (SA (fst (split_lit e)) (snd (split_lit e) + off)) = bv_unsigned (edenot E e) + off ->
  0 <= bv_unsigned (edenot E e) + off -> bv_unsigned (edenot E e) + off + Z.of_nat w <= 2 ^ 64 ->
  cell SEGS M (bv_unsigned (edenot E e) + off) w (edenot E v).
Proof.
  intros E M k e off w v hs HK Hw HL Es H0 H1.
  destruct (lookup_piece SEGS E M k _ _ w v hs HK Hw HL) as (bs & Hrd & Hlen & Hv).
  - unfold flat. rewrite Es. lia.
  - unfold cell, W. rewrite Es in Hrd. rewrite Hv. exact Hrd.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma W_u : forall w : word, W (bv_unsigned w) = w.
Proof. intros w. unfold W. apply Z_to_bv_bv_unsigned. Qed.

Lemma W_mod : forall z, W (z mod two64) = Z_to_bv 64 z.
Proof.
  intros z. unfold W, two64. apply bv_eq. rewrite !u_Zbv_mod. apply Z.mod_mod. lia.
Qed.

Hypothesis DEC : decode_contract_x SEGS (lt_dframe T) (lt_strict T) (lt_dec T) (lt_imgend T).

Theorem node_decode_sound : node1_stmt SEGS A nx0 LIMIT SINV argH ISP FS0 always (fun cs => node_decode SEGS A nx0 T cs).
Proof.
  intros cs cs' E R FULL model TT HC _ Hn Hk. cbv beta in Hn.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := MR E cs model FULL) in *.
  unfold node_decode in Hn.
  destruct (negb (Z.eqb (pc cs) (lt_dec T)) || Z.eqb (lt_dec T) 0)%bool eqn:Hpc0; [discriminate|].
  apply orb_false_iff in Hpc0 as [Hpc _]. apply negb_false_iff in Hpc. apply Z.eqb_eq in Hpc.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (split_lit (reg cs 13)) as [qb qo] eqn:Hspq.
  destruct (kreadZ SEGS (kn cs) qb qo 4) as [mx|] eqn:Hmx; [|discriminate].
  destruct (xlo (kn cs) (reg cs 11)) as [nlo|] eqn:Hnlo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 11)) as [nhi|] eqn:Hnhi; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [phi|] eqn:Hphi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  apply andb_prop in Hc as [Hc C]. apply andb_prop in Hc as [Hc C1]. apply andb_prop in Hc as [Hc C2].
  apply andb_prop in Hc as [Hc C3]. apply andb_prop in Hc as [Hc C4]. apply andb_prop in Hc as [Hc Cst]. apply andb_prop in Hc as [Hc Cfr].
  apply andb_prop in Hc as [Hc C5]. apply andb_prop in Cfr as [Cfr Cfr2]. apply Z.ltb_lt in Cfr. apply Z.ltb_lt in Cfr2. set (fr := lt_dframe T) in *.
  apply andb_prop in Hc as [Hc C6]. apply andb_prop in Hc as [Hc C7]. apply andb_prop in Hc as [Hc C8].
  apply andb_prop in Hc as [C0 C9].
  (* [comment removed for export] *)
  apply Z.leb_le in C0. apply Z.leb_le in C9. apply Z.leb_le in C8. apply Z.ltb_lt in C7. apply Z.ltb_lt in C6.
  destruct (ret_lit_sound SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model ret HC Hret) as (R1 & Hrok & Hretr).
  pose proof (w_reg_sound SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model 2 HC ltac:(lia)) as R2.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model 10 HC ltac:(lia)) as R10.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model 11 HC ltac:(lia)) as R11.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model 12 HC ltac:(lia)) as R12.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model 13 HC ltac:(lia)) as R13.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Bnlo.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Bnhi.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hphi) as Bphi.
  set (sp := bv_unsigned (edenot E (reg cs 2))) in *. set (p := bv_unsigned (edenot E (reg cs 10))) in *.
  set (n := bv_unsigned (edenot E (reg cs 11))) in *. set (out := bv_unsigned (edenot E (reg cs 12))) in *.
  set (q := bv_unsigned (edenot E (reg cs 13))) in *.
  pose proof (u64_range (edenot E (reg cs 10))) as Hpr. fold p in Hpr.
  destruct (stk_ok_sound E M (kn cs) (reg cs 2) (- fr) fr HKN C4 ltac:(lia) ltac:(lia)) as (Wsp & Isp & Hsp63 & Esp). fold sp in Wsp, Isp, Hsp63, Esp.
  destruct (stk_ok_sound E M (kn cs) (reg cs 12) 0 (4 * mx) HKN C3 ltac:(lia) ltac:(lia)) as (Wout & Iout & Hout63 & Eout). fold out in Wout, Iout, Hout63, Eout.
  destruct (stk_ok_sound E M (kn cs) (reg cs 13) 0 4 HKN C2 ltac:(lia) ltac:(lia)) as (Wq & Iq & Hq63 & Eq). fold q in Wq, Iq, Hq63, Eq.
  rewrite Z.add_0_r in Wout, Iout, Hout63, Wq, Iq, Hq63.
  pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HKN C1) as Lo. cbn [xt_den] in Lo. fold sp out in Lo.
  pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HKN C) as Lq. cbn [xt_den] in Lq. fold sp q in Lq.
  (* [comment removed for export] *)
  assert (Hcell : cell SEGS M q 4 (W mx)).
  { unfold kreadZ in Hmx.
    destruct (know_lookup SEGS (kn cs) qb qo 4 false [] []) as [v scs hs|scs hs|] eqn:HL; try discriminate.
    destruct v as [z| | | | | | |]; try discriminate. destruct scs; [|discriminate]. injection Hmx as <-.
    rewrite W_mod.
    pose proof (lookup_cell E M (kn cs) (reg cs 13) 0 4 (ELit z) hs HKN ltac:(lia)) as X.
    rewrite Hspq in X. cbn [fst snd] in X. rewrite Z.add_0_r in X. specialize (X HL).
    rewrite Hspq in Eq. cbn [fst snd] in Eq. rewrite Z.add_0_r in Eq. fold q in X.
    rewrite Z.add_0_r in X. apply X; [rewrite Eq; lia | lia | lia]. }
  (* [comment removed for export] *)
  assert (Hrd : rd_ok M p n).
  { apply orb_prop in C5 as [Hz|Hr].
    - apply Z.eqb_eq in Hz. intros i Hi. lia.
    - apply andb_prop in Hr as [H1 Hov]. apply Z.leb_le in H1.
      destruct (ovl_ok_sound E M (kn cs) (reg cs 10) (reg cs 11) HKN Hov ltac:(unfold elenZ; fold n; lia)) as (X & _). exact X. }
  (* [comment removed for export] *)
  assert (Hstrict : lt_strict T = true -> (n = 0 \/ 0 < p) /\ out mod 4 = 0 /\ q mod 4 = 0).
  { intros Hs. rewrite Hs in Cst. cbn [negb orb] in Cst.
    apply andb_prop in Cst as [Cst Aq]. apply andb_prop in Cst as [Cnp Ao]. apply Z.leb_le in Ao. apply Z.leb_le in Aq.
    assert (D4 : forall a x, 2 <= a -> (2 ^ a | x) -> x mod 4 = 0).
    { intros a x Ha Hd. apply Z.mod_divide; [lia|]. eapply Z.divide_trans; [|exact Hd].
      exists (2 ^ (a - 2)). change 4 with (2 ^ 2). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    split; [|split].
    - apply orb_prop in Cnp as [Hz|Hp1]; [left; apply Z.eqb_eq in Hz; lia | right].
      destruct (xlo (kn cs) (reg cs 10)) as [plo|] eqn:Hplo; [|discriminate]. apply Z.leb_le in Hp1.
      pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hplo) as Bplo. fold p in Bplo. lia.
    - destruct (ealign_sound SEGS E M (kn cs) (reg cs 12) HKN) as [_ Hdiv]. fold out in Hdiv. exact (D4 _ _ Ao Hdiv).
    - destruct (ealign_sound SEGS E M (kn cs) (reg cs 13) HKN) as [_ Hdiv]. fold q in Hdiv. exact (D4 _ _ Aq Hdiv). }
  (* [comment removed for export] *)
  destruct (decode_contract_x_use SEGS _ _ _ _ DEC R M (Z_to_bv 64 ret) sp p n out q mx R1 Hrok
              ltac:(unfold sp; rewrite W_u; exact R2) ltac:(unfold p; rewrite W_u; exact R10)
              ltac:(unfold n; rewrite W_u; exact R11) ltac:(unfold out; rewrite W_u; exact R12)
              ltac:(unfold q; rewrite W_u; exact R13)
              ltac:(lia) ltac:(lia) ltac:(lia) Hrd ltac:(lia) Hcell
              ltac:(lia) ltac:(lia) Wsp ltac:(lia) ltac:(lia) Wout ltac:(lia) ltac:(lia) Wq
              ltac:(right; lia) ltac:(right; lia) Hstrict)
    as (regs' & M' & Hms & Hkept & Hfr & Hg).
  eapply (call_node_sound SEGS A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SINV argH ISP argH_high NX0_spw argH_agree SINV_frame SINV_agree FS0
            cs cs' E R FULL model TT ret None _ regs' M' HC Hn).
  - rewrite Hpc. exact Hms.
  - intros r Hr0 Hncs. apply Hkept. intros Hin. apply Hncs.
    unfold KSdec in Hin. unfold caller_saved. cbn [In] in *. intuition.
  - exact I.
  - (* [comment removed for export] *)
    set (P1 := inrb (sp - fr) fr). set (P2 := fun x => (P1 x || inrb out (4 * mx) x)%bool).
    set (M1 := mixm P1 M M'). set (M2 := mixm P2 M M').
    assert (K1 : know_ok SEGS E M1 (hav (kn cs) (reg cs 2) (- fr) fr)).
    { apply (hav_sound E M M1 (kn cs) (reg cs 2) (- fr) fr HKN ltac:(lia) Esp); [|apply mixm_grows; exact Hg].
      intros x Hx. fold sp in Hx. unfold M1, mixm, P1. destruct (inrb (sp - fr) fr x) eqn:Hb; [|reflexivity].
      exfalso. apply Hx. replace (sp + - fr) with (sp - fr) by lia. apply inrb_inr. exact Hb. }
    assert (K2 : know_ok SEGS E M2 (hav (hav (kn cs) (reg cs 2) (- fr) fr) (reg cs 12) 0 (4 * mx))).
    { apply (hav_sound E M1 M2 _ (reg cs 12) 0 (4 * mx) K1 ltac:(lia) Eout).
      - intros x Hx. fold out in Hx. rewrite Z.add_0_r in Hx. unfold M2, M1, mixm, P2.
        destruct (P1 x); [reflexivity|]. cbn [orb].
        destruct (inrb out (4 * mx) x) eqn:Hb; [|reflexivity]. exfalso. apply Hx. apply inrb_inr. exact Hb.
      - apply mixm_grows2; [exact Hg|]. intros x Hx. unfold P2. rewrite Hx. reflexivity. }
    apply (hav_sound E M2 M' _ (reg cs 13) 0 4 K2 ltac:(lia) Eq).
    + intros x Hx. fold q in Hx. rewrite Z.add_0_r in Hx. unfold M2, mixm, P2, P1.
      destruct (inrb (sp - fr) fr x || inrb out (4 * mx) x)%bool eqn:Hb; [reflexivity|].
      apply orb_false_iff in Hb as [Hb1 Hb2]. apply Hfr. intros [F|[F|F]].
      * apply inrb_inr in F. congruence.
      * apply inrb_inr in F. congruence.
      * exact (Hx F).
    + intros x Hx. unfold M2, mixm in Hx. destruct (P2 x); [exact Hx | apply Hg; exact Hx].
  - exact Hk.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem node_unkintro_sound : forall args,
  node1_stmt SEGS A nx0 LIMIT SINV argH ISP FS0 always (fun cs => node_unkintro A cs args).
Proof.
  intros args cs cs' E R FULL model TT HC _ Hn Hk. cbv beta in Hn. unfold node_unkintro in Hn.
  destruct args as [|e [|[n| | | | | | |] [|? ?]]]; try discriminate.
  destruct (split_lit e) as [b o] eqn:Hsp.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. injection Hn as <-.
  apply andb_prop in Hc as [Hc Hoff]. apply andb_prop in Hc as [Hc Hw]. apply andb_prop in Hc as [Hc _].
  apply andb_prop in Hc as [Hn0 Hn1]. apply Z.ltb_lt in Hn0. apply Z.leb_le in Hn1.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  assert (El : elenZ E (ELit n) = n) by (unfold elenZ; cbn [edenot]; apply u64_lit; lia).
  assert (Hov : ovl_ok A (kn cs) e (ELit n) = true).
  { unfold ovl_ok. rewrite Hsp. rewrite Hw, Hoff. reflexivity. }
  destruct (ovl_ok_sound E _ (kn cs) e (ELit n) HK Hov ltac:(rewrite El; lia)) as (Hrd & Hhi & _ & _ & Es).
  rewrite Hsp in Es. cbn [fst snd] in Es. rewrite El in *.
  refine (Hk E R FULL model (conj (env_agree_refl nx0 E) (env_agree_refl _ E)) _ eq_refl).
  unfold add_kn. apply (cs_ok_set_kn SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model _ HC).
  constructor; [|exact HK]. cbn [kentry_ok]. rewrite El.
  pose proof (u64_range (edenot E e)) as Hr.
  split; [unfold flat; rewrite Es; lia|].
  intros i Hi. rewrite Es. apply Hrd. exact Hi.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mod2_of_mod_pow : forall x k, 1 <= k -> (x mod 2 ^ k) mod 2 = x mod 2.
Proof.
  intros x k Hk. symmetry. apply Zmod_div_mod; try lia.
  exists (2 ^ (k - 1)). replace k with ((k - 1) + 1) at 1 by lia. rewrite Z.pow_add_r by lia. lia.
Qed.

Lemma land_even_l : forall x y, x mod 2 = 0 -> Z.land x y mod 2 = 0.
Proof.
  intros x y Hx. rewrite Zmod_odd in *. rewrite <- Z.bit0_odd in *. rewrite Z.land_spec.
  destruct (Z.testbit x 0); [discriminate|]. reflexivity.
Qed.
Lemma land_even_r : forall x y, y mod 2 = 0 -> Z.land x y mod 2 = 0.
Proof. intros x y Hy. rewrite Z.land_comm. apply land_even_l. exact Hy. Qed.

Lemma even_expr_sound : forall E e, even_expr e = true -> bv_unsigned (edenot E e) mod 2 = 0.
Proof.
  intros E e. induction e as [z|v|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k i n];
    cbn [even_expr]; intros H; try discriminate.
  - cbn [edenot]. rewrite u_Zbv_mod, (mod2_of_mod_pow z 64) by lia.
    rewrite Zmod_odd. rewrite <- Z.negb_even, H. reflexivity.
  - destruct op; try discriminate. cbn [edenot]. rewrite u_and64.
    apply orb_prop in H as [H|H]; [apply land_even_l; exact (IHa H) | apply land_even_r; exact (IHb H)].
  - destruct sx; [discriminate|]. destruct lo; [|discriminate]. destruct n as [|n]; [discriminate|].
    cbn [edenot]. unfold ext_val, ext_Z. rewrite u_Zbv_mod, (mod2_of_mod_pow _ 64) by lia.
    change (8 * Z.of_nat 0) with 0. rewrite Z.pow_0_r, Z.div_1_r.
    rewrite (mod2_of_mod_pow _ (8 * Z.of_nat (S n))) by lia. exact (IHa H).
Qed.

(* [comment removed for export] *)
Definition ext_regs (E : env) (nx : nat) (hv : list nat) (R' : bvmap 5 word) : env :=
  Env (fun n => if (Nat.leb nx n && Nat.ltb n (nx + length hv))%bool
                then getr R' (Z_to_bv 5 (Z.of_nat (nth (n - nx) hv 0%nat)))
                else ev E n) (eb E).

Lemma ext_regs_agree : forall E nx hv R', env_agree nx E (ext_regs E nx hv R').
Proof.
  intros E nx hv R'. split; [|reflexivity]. intros n Hn. cbn [ext_regs ev].
  destruct (Nat.leb_spec nx n); [lia|]. reflexivity.
Qed.

Lemma ext_regs_var : forall E nx hv R' j, (j < length hv)%nat ->
  ev (ext_regs E nx hv R') (nx + j) = getr R' (Z_to_bv 5 (Z.of_nat (nth j hv 0%nat))).
Proof.
  intros E nx hv R' j Hj. cbn [ext_regs ev].
  replace (Nat.leb nx (nx + j) && Nat.ltb (nx + j) (nx + length hv))%bool with true.
  2:{ symmetry. apply andb_true_intro. split; [apply Nat.leb_le; lia | apply Nat.ltb_lt; lia]. }
  f_equal. f_equal. f_equal. f_equal. lia.
Qed.

Lemma regs_after_region : forall E sr R R' nx hv,
  regs_ok E sr R -> AP.sr_vars_lt nx sr = true -> List.NoDup hv ->
  (forall r : bv 5, r <> 0%bv -> ~ In (ridx r) hv -> getr R' r = getr R r) ->
  regs_ok (ext_regs E nx hv R') (sr_fresh sr hv nx) R'.
Proof.
  intros E sr R R' nx hv HR Hsv Hnd Hkept.
  pose proof (ext_regs_agree E nx hv R') as Hag.
  assert (OLD : forall i, (i < 32)%nat -> edenot (ext_regs E nx hv R') (nth i sr (ELit 0)) = edenot E (nth i sr (ELit 0))).
  { intros i Hi. symmetry. apply (edenot_agree' nx); [exact Hag|]. apply nth_sr_vars_lt'; assumption. }
  apply regs_ok_pointwise. intros r Hr0.
  pose proof (ridx_range r) as Hrr.
  destruct (in_dec Nat.eq_dec (ridx r) hv) as [Hin|Hnin].
  - destruct (In_nth hv (ridx r) 0%nat Hin) as (j & Hj & Hnth).
    rewrite <- Hnth at 1. rewrite nth_sr_fresh_in by (exact Hnd || exact Hj).
    cbn [edenot]. rewrite ext_regs_var by exact Hj. rewrite Hnth. rewrite <- (reg_of_ridx r _ eq_refl). reflexivity.
  - rewrite nth_sr_fresh_out by exact Hnin. rewrite OLD by exact Hrr.
    rewrite (Hkept r Hr0 Hnin). pose proof (HR r) as X. unfold sr_get in X.
    destruct (bv_eqb r 0) eqn:Hb; [exfalso; apply Hr0; apply bv_eq; unfold bv_eqb in Hb; apply Z.eqb_eq in Hb; exact Hb|].
    exact X.
Qed.

Lemma loop_havoc_nodup : List.NoDup loop_havoc.
Proof.
  unfold loop_havoc.
  repeat (apply List.NoDup_cons; [cbn; intros H; repeat (destruct H as [H|H]; [lia|]); exact H|]). apply List.NoDup_nil.
Qed.

(* [comment removed for export] *)
Lemma loop_kept_cases : forall r : bv 5, r <> 0%bv -> ~ In (ridx r) loop_havoc ->
  r = 2%bv \/ r = 3%bv \/ r = 4%bv \/ r = 8%bv.
Proof.
  intros r Hr0 Hn. pose proof (ridx_range r) as Hrr. pose proof (reg_of_ridx r (ridx r) eq_refl) as Er.
  remember (ridx r) as n eqn:Hnd. clear Hnd.
  do 32 (destruct n as [|n];
         [first [ solve [exfalso; apply Hr0; rewrite Er; apply bv_eq; reflexivity]
                | solve [exfalso; apply Hn; unfold loop_havoc; cbn [In]; tauto]
                | solve [rewrite Er; left; apply bv_eq; reflexivity]
                | solve [rewrite Er; right; left; apply bv_eq; reflexivity]
                | solve [rewrite Er; right; right; left; apply bv_eq; reflexivity]
                | solve [rewrite Er; right; right; right; apply bv_eq; reflexivity] ] |]).
  lia.
Qed.

(* [comment removed for export] *)
Lemma u_eaddz : forall E e z, bv_unsigned (edenot E (eaddz e z)) = (bv_unsigned (edenot E e) + z) mod 2 ^ 64.
Proof.
  intros E e z. unfold eaddz. rewrite mkAlu_denot, u_add64, edenot_lit, u_Zbv_mod.
  rewrite Zplus_mod_idemp_r. reflexivity.
Qed.
Lemma u_eadd : forall E a b, bv_unsigned (edenot E (eadd a b)) = (bv_unsigned (edenot E a) + bv_unsigned (edenot E b)) mod 2 ^ 64.
Proof. intros E a b. unfold eadd. rewrite mkAlu_denot, u_add64. reflexivity. Qed.
Lemma u_esub : forall E a b, bv_unsigned (edenot E (esub a b)) = (bv_unsigned (edenot E a) - bv_unsigned (edenot E b)) mod 2 ^ 64.
Proof. intros E a b. unfold esub. rewrite mkAlu_denot, u_sub64. reflexivity. Qed.

Lemma str_window_sound : forall E M k b len N,
  know_ok SEGS E M k -> str_window k b len = Some N ->
  estart E (SA (fst (split_lit b)) (snd (split_lit b))) = bv_unsigned (edenot E b) ->
  bv_unsigned (edenot E len) < 2 ^ 31 -> 1 <= bv_unsigned (edenot E b) ->
  bv_unsigned (edenot E b) + bv_unsigned (edenot E N) < 2 ^ 63 ->
  bv_unsigned (edenot E len) < bv_unsigned (edenot E N)
  /\ (bv_unsigned (edenot E b) + bv_unsigned (edenot E len)) / 8 * 8 + 8 <= bv_unsigned (edenot E b) + bv_unsigned (edenot E N).
Proof.
  intros E M k b len N HK H Eb Hl Hb1 HbN. unfold str_window in H. destruct (split_lit b) as [bb bo] eqn:Hsp. cbn [fst snd] in Eb.
  match type of H with match ?f with _ => _ end = _ => destruct f as [K|] eqn:Hf; [|discriminate] end.
  destruct K as [| | | | | |[wb wk] wl| | |]; try discriminate. injection H as <-.
  apply find_some in Hf as [Hin Hp]. apply andb_prop in Hp as [Hxi Hal]. apply Z.leb_le in Hal.
  pose proof (proj1 (Forall_forall _ _) HK _ Hin) as HKK. cbn [kentry_ok] in HKK. destruct HKK as [(F1 & F2 & F3 & F4) _].
  destruct (xinside_sound SEGS E M k bb bo (eaddz len 1) wb wk wl HK Hxi) as [I1 I2].
  rewrite Eb in I1, I2.
  pose proof (u64_range (edenot E len)) as Rl.
  assert (El1 : elenZ E (eaddz len 1) = bv_unsigned (edenot E len) + 1).
  { unfold elenZ. rewrite u_eaddz. apply Z.mod_small. lia. }
  rewrite El1 in I2.
  destruct (ealign_sound SEGS E M k (eadd (eaddz wb wk) wl) HK) as [_ Hdiv].
  assert (H8 : (8 | bv_unsigned (edenot E (eadd (eaddz wb wk) wl)))).
  { eapply Z.divide_trans; [|exact Hdiv]. exists (2 ^ (ealign k (eadd (eaddz wb wk) wl) - 3)).
    change 8 with (2 ^ 3). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  unfold estart in F1, F2, F4, I1, I2. cbn [a_base a_off] in F1, F2, F4, I1, I2. unfold elenZ in F3, F4, I2.
  set (ws := bv_unsigned (edenot E wb) + wk) in *. set (wlz := bv_unsigned (edenot E wl)) in *.
  set (bz := bv_unsigned (edenot E b)) in *. set (lz := bv_unsigned (edenot E len)) in *.
  assert (Ew : bv_unsigned (edenot E (eadd (eaddz wb wk) wl)) = (ws + wlz) mod 2 ^ 64).
  { rewrite u_eadd, u_eaddz. fold wlz. rewrite Zplus_mod_idemp_l. reflexivity. }
  rewrite u_esub, Ew in *. fold bz in HbN |- *.
  destruct (Z.eq_dec (ws + wlz) (2 ^ 64)) as [Heq|Hne].
  - exfalso. rewrite Heq, Z.mod_same in HbN by lia.
    assert (Em : (0 - bz) mod 2 ^ 64 = 2 ^ 64 - bz).
    { replace (0 - bz) with ((2 ^ 64 - bz) + (-1) * 2 ^ 64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small.
      pose proof (u64_range (edenot E b)). fold bz in H. lia. }
    rewrite Em in HbN. lia.
  - rewrite (Z.mod_small (ws + wlz)) in * by lia.
    rewrite (Z.mod_small (ws + wlz - bz)) in * by lia.
    split; [lia|].
    destruct H8 as [c Hc]. rewrite Hc in *.
    assert (Hq : (bz + lz) / 8 < c) by (apply Z.div_lt_upper_bound; lia).
    lia.
Qed.

(* [comment removed for export] *)
Lemma ovl_ok_start : forall E M k e n,
  know_ok SEGS E M k -> ovl_ok A k e n = true -> 1 <= bv_unsigned (edenot E e) ->
  estart E (SA (fst (split_lit e)) (snd (split_lit e))) = bv_unsigned (edenot E e).
Proof.
  intros E M k e n HK H H1. unfold ovl_ok in H. destruct (split_lit e) as [b o] eqn:Hsp. cbn [fst snd].
  apply andb_prop in H as [Hw _].
  destruct (kwritable_x_sound SEGS E M k k b o n HK HK Hw) as (_ & Wlo & Whi).
  pose proof (u64_range (edenot E n)) as Rn. unfold elenZ in Whi.
  assert (Ee : bv_unsigned (edenot E e) = (bv_unsigned (edenot E b) + o) mod 2 ^ 64).
  { rewrite (w_split_lit_denot E e b o Hsp). apply u_Zbv_mod. }
  unfold estart in *. cbn [a_base a_off] in *. rewrite Ee in *.
  destruct (Z.eq_dec (bv_unsigned (edenot E b) + o) (2 ^ 64)) as [Heq|Hne].
  - exfalso. rewrite Heq, Z.mod_same in H1 by lia. lia.
  - rewrite Z.mod_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cell8_sound : forall E M k e off v,
  know_ok SEGS E M k -> cell8 SEGS k e off = Some v ->
  bv_unsigned (edenot E (fst (split_lit e))) + snd (split_lit e) = bv_unsigned (edenot E e) ->
  0 <= bv_unsigned (edenot E e) + off -> bv_unsigned (edenot E e) + off + 8 <= 2 ^ 64 ->
  cell SEGS M (bv_unsigned (edenot E e) + off) 8 (edenot E v).
Proof.
  intros E M k e off v HK H Hs H0 H1. unfold cell8 in H. destruct (split_lit e) as [b o] eqn:Hsp. cbn [fst snd] in Hs.
  unfold kread8e in H.
  destruct (know_lookup SEGS k b (o + off) 8 false [] []) as [v' scs hs|scs hs|] eqn:HL; try discriminate.
  destruct scs; [|discriminate]. injection H as ->.
  pose proof (lookup_cell E M k e off 8 v hs HK ltac:(lia)) as X. rewrite Hsp in X. cbn [fst snd] in X.
  apply X; [exact HL | unfold estart; cbn [a_base a_off]; lia | lia | lia].
Qed.

Lemma cell8_is_sound : forall E M k e off z,
  know_ok SEGS E M k -> cell8_is SEGS k e off z = true ->
  bv_unsigned (edenot E (fst (split_lit e))) + snd (split_lit e) = bv_unsigned (edenot E e) ->
  0 <= bv_unsigned (edenot E e) + off -> bv_unsigned (edenot E e) + off + 8 <= 2 ^ 64 ->
  cell SEGS M (bv_unsigned (edenot E e) + off) 8 (W z).
Proof.
  intros E M k e off z HK H Hs H0 H1. unfold cell8_is in H.
  destruct (cell8 SEGS k e off) as [v|] eqn:Hc; [|discriminate].
  destruct v as [v0| | | | | | |]; try discriminate. apply Z.eqb_eq in H. subst z.
  rewrite W_mod. exact (cell8_sound E M k e off (ELit v0) HK Hc Hs H0 H1).
Qed.

Hypothesis LOOP : a2uloop_contract_x SEGS (lt_ldepth T) (lt_strict T) (lt_loop T) (lt_loop_exit T) (lt_imgend T) (lt_rodata T).

Theorem node_a2uloop_sound : forall args,
  node1_stmt SEGS A nx0 LIMIT SINV argH ISP FS0 always (fun cs => node_a2uloop SEGS A nx0 T cs args).
Proof.
  intros args cs cs' E R FULL model TT HC _ Hn Hk. cbv beta in Hn.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := MR E cs model FULL) in *.
  unfold node_a2uloop in Hn.
  destruct args as [|len [|? ?]]; try discriminate.
  destruct (negb (Z.eqb (pc cs) (lt_loop T)) || Z.eqb (lt_loop T) 0)%bool eqn:Hpc0; [discriminate|].
  apply orb_false_iff in Hpc0 as [Hpc _]. apply negb_false_iff in Hpc. apply Z.eqb_eq in Hpc.
  destruct (split_lit (reg cs 8)) as [Sb So] eqn:HspS.
  destruct (split_lit (reg cs 19)) as [bb bo] eqn:Hspb.
  destruct (split_lit (eadd (reg cs 19) len)) as [nb no] eqn:Hspn.
  destruct (cell8 SEGS (kn cs) (reg cs 8) (-2216 + 8)) as [oute|] eqn:Hc8; [|discriminate].
  destruct (cell8 SEGS (kn cs) (reg cs 8) (-2216 + 40)) as [sbe|] eqn:Hc40; [|discriminate].
  destruct (cell1 SEGS (kn cs) Sb (So - 2216 + 48)) as [fl|] eqn:Hfl; [|discriminate].
  destruct (kreadZ SEGS (kn cs) nb no 1) as [[| |]|] eqn:Hnul; try discriminate.
  destruct (str_window (kn cs) (reg cs 19) len) as [N|] eqn:HN; [|discriminate].
  destruct (xlo (kn cs) len) as [llo|] eqn:Hllo; [|discriminate].
  destruct (xhi (kn cs) len) as [lhi|] eqn:Hlhi; [|discriminate].
  destruct (split_lit oute) as [ob oo] eqn:Hspo.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hkv; [|discriminate] end.
  injection Hn as <-.
  apply andb_prop in Hc as [Hc Hfresh]. apply andb_prop in Hc as [Hc C21]. apply andb_prop in Hc as [Hc C20].
  apply andb_prop in Hc as [Hc C19]. apply andb_prop in Hc as [Hc C18]. apply andb_prop in Hc as [Hc C17].
  apply andb_prop in Hc as [Hc C16]. apply andb_prop in Hc as [Hc C15]. apply andb_prop in Hc as [Hc C14].
  apply andb_prop in Hc as [Hc CS]. apply andb_prop in Hc as [Hc CD]. apply andb_prop in CD as [CD CD2]. apply Z.ltb_lt in CD. apply Z.ltb_lt in CD2. set (D := lt_ldepth T) in *.
  apply andb_prop in Hc as [Hc C13]. apply andb_prop in Hc as [Hc C12b]. apply andb_prop in Hc as [Hc C12].
  apply andb_prop in Hc as [Hc C11]. apply andb_prop in Hc as [Hc C10]. apply andb_prop in Hc as [Hc C9].
  apply andb_prop in Hc as [Hc C8]. apply andb_prop in Hc as [Hc C7]. apply andb_prop in Hc as [Hc C6].
  apply andb_prop in Hc as [Hc C5]. apply andb_prop in Hc as [Hc C4]. apply andb_prop in Hc as [Hc C3].
  apply andb_prop in Hc as [C1 C2].
  apply Z.leb_le in C8. apply Z.ltb_lt in C9.
  (* [comment removed for export] *)
  pose proof (w_reg_sound SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model 2 HC ltac:(lia)) as R2.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model 8 HC ltac:(lia)) as R8.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model 19 HC ltac:(lia)) as R19.
  set (S := bv_unsigned (edenot E (reg cs 8))) in *.
  set (bz := bv_unsigned (edenot E (reg cs 19))) in *.
  set (lz := bv_unsigned (edenot E len)) in *.
  set (Nz := bv_unsigned (edenot E N)) in *.
  set (out := bv_unsigned (edenot E oute)) in *.
  set (sbz := bv_unsigned (edenot E sbe)) in *.
  (* [comment removed for export] *)
  destruct (stk_ok_sound E M (kn cs) (reg cs 8) (- D) (D - 2216) HKN C14 ltac:(lia) ltac:(lia)) as (W1 & I1 & J1 & E1). fold S in W1, I1, J1, E1.
  destruct (stk_ok_sound E M (kn cs) (reg cs 8) (-2200) 16 HKN C15 ltac:(lia) ltac:(lia)) as (W2 & _ & _ & E2). fold S in W2, E2.
  destruct (stk_ok_sound E M (kn cs) (reg cs 8) (-2160) 2048 HKN C16 ltac:(lia) ltac:(lia)) as (W3 & _ & _ & E3). fold S in W3, E3.
  destruct (stk_ok_sound E M (kn cs) oute 0 16 HKN C18 ltac:(lia) ltac:(lia)) as (W4 & I4 & J4 & E4). fold out in W4, I4, J4, E4.
  rewrite Z.add_0_r in W4, I4, J4.
  assert (HS0 : bv_unsigned (edenot E (fst (split_lit (reg cs 8)))) + snd (split_lit (reg cs 8)) = S).
  { unfold estart in E1. cbn [a_base a_off] in E1. lia. }
  assert (HS63 : S < 2 ^ 63).
  { unfold addr_in in C17. destruct (xlo (kn cs) (reg cs 8)); [|discriminate].
    destruct (xhi (kn cs) (reg cs 8)) as [h|] eqn:Hh; [|discriminate].
    apply andb_prop in C17 as [_ X]. apply Z.leb_le in X.
    pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hh) as Bh. fold S in Bh. lia. }
  (* [comment removed for export] *)
  assert (Hsp : getr R 2%bv = W (S - 2240)).
  { replace (2%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 2)) by (apply bv_eq; reflexivity). rewrite R2.
    apply expr_eqb_eq in C1. rewrite C1. apply bv_eq. unfold W. rewrite u_eaddz, u_Zbv_mod. fold S. reflexivity. }
  (* [comment removed for export] *)
  pose proof (cell8_is_sound E M (kn cs) (reg cs 8) (-2216) 0 HKN C2 HS0 ltac:(fold S; lia) ltac:(fold S; lia)) as P0. fold S in P0.
  pose proof (cell8_sound E M (kn cs) (reg cs 8) (-2216 + 8) oute HKN Hc8 HS0 ltac:(fold S; lia) ltac:(fold S; lia)) as P8. fold S in P8.
  pose proof (cell8_is_sound E M (kn cs) (reg cs 8) (-2216 + 16) 0 HKN C3 HS0 ltac:(fold S; lia) ltac:(fold S; lia)) as P16. fold S in P16.
  pose proof (cell8_is_sound E M (kn cs) (reg cs 8) (-2216 + 24) 0 HKN C4 HS0 ltac:(fold S; lia) ltac:(fold S; lia)) as P24. fold S in P24.
  pose proof (cell8_is_sound E M (kn cs) (reg cs 8) (-2216 + 32) 16 HKN C5 HS0 ltac:(fold S; lia) ltac:(fold S; lia)) as P32. fold S in P32.
  pose proof (cell8_sound E M (kn cs) (reg cs 8) (-2216 + 40) sbe HKN Hc40 HS0 ltac:(fold S; lia) ltac:(fold S; lia)) as P40. fold S in P40.
  assert (P48 : cell SEGS M (S - 2216 + 48) 1 (edenot E fl)).
  { unfold cell1 in Hfl.
    destruct (know_lookup SEGS (kn cs) Sb (So - 2216 + 48) 1 false [] []) as [v' scs hs|scs hs|] eqn:HL; try discriminate.
    destruct scs; [|discriminate]. injection Hfl as ->.
    pose proof (lookup_cell E M (kn cs) (reg cs 8) (-2216 + 48) 1 fl hs HKN ltac:(lia)) as X.
    rewrite HspS in X, HS0. cbn [fst snd] in X, HS0.
    replace (So + (-2216 + 48)) with (So - 2216 + 48) in X by lia. fold S in X.
    replace (S - 2216 + 48) with (S + (-2216 + 48)) by lia.
    apply X; [exact HL | unfold estart; cbn [a_base a_off]; lia | lia | lia]. }
  assert (Heven : (bv_unsigned (edenot E fl) mod 2 ^ 8) mod 2 = 0).
  { rewrite (mod2_of_mod_pow _ 8) by lia. apply even_expr_sound. exact C6. }
  assert (Hsb : 0 < sbz < 2 ^ 64).
  { destruct (xlo (kn cs) sbe) as [l|] eqn:Hl; [|discriminate]. apply Z.leb_le in C7.
    pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hl) as Bl. pose proof (u64_range (edenot E sbe)) as Rs. fold sbz in Bl, Rs. lia. }
  (* [comment removed for export] *)
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hllo) as Bllo. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hlhi) as Blhi.
  fold lz in Bllo, Blhi.
  assert (Hb1 : 1 <= bz /\ bz + Nz < 2 ^ 63).
  { destruct (xlo (kn cs) (reg cs 19)) as [l|] eqn:Hl; [|discriminate].
    destruct (xhi (kn cs) (reg cs 19)) as [h|] eqn:Hh; [|discriminate].
    destruct (xhi (kn cs) N) as [hn|] eqn:Hhn; [|discriminate].
    apply andb_prop in C12 as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
    pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hl). pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hh).
    pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hhn). fold bz in H, H0. fold Nz in H1. lia. }
  destruct Hb1 as [Hb1 HbN].
  pose proof (ovl_ok_start E M (kn cs) (reg cs 19) N HKN C11 ltac:(fold bz; lia)) as Eb. fold bz in Eb.
  destruct (str_window_sound E M (kn cs) (reg cs 19) len N HKN HN Eb ltac:(fold lz; lia) ltac:(fold bz; lia) ltac:(fold bz Nz; lia)) as [HlN Hslack].
  fold bz lz Nz in HlN, Hslack.
  destruct (ovl_ok_sound E M (kn cs) (reg cs 19) N HKN C11 ltac:(unfold elenZ; fold Nz; lia)) as (Hrd & _ & _ & _ & _).
  unfold elenZ in Hrd. fold bz Nz in Hrd.
  assert (Hnulb : M (W (bz + lz)) = Some (Z_to_bv 8 0)).
  { destruct (w_flat_x_sound SEGS E M (kn cs) nb no (ELit 1) HKN C12b) as (F0 & F1 & _).
    cbn [edenot] in F1. rewrite u64_lit in F1 by lia.
    destruct (kreadZ1_byte SEGS E M (kn cs) nb no 0 HKN Hnul ltac:(unfold flat; lia)) as [Hr _].
    assert (En : estart E (SA nb no) = bz + lz).
    { pose proof (start_eq E (eadd (reg cs 19) len) nb no 0 1 Hspn) as X. rewrite Z.add_0_r in X.
      rewrite X by (try lia; pose proof (u64_range (edenot E (eadd (reg cs 19) len))); lia).
      rewrite u_eadd. fold bz lz. rewrite Z.mod_small by lia. lia. }
    rewrite En in Hr. fold (W (bz + lz)) in Hr. cbn [rdn] in Hr.
    destruct (M (W (bz + lz))) as [x|] eqn:Hm.
    - injection Hr as ->. reflexivity.
    - exfalso. exact (Hrd lz ltac:(lia) Hm). }
  (* [comment removed for export] *)
  assert (Hro : Forall (fun r => img_ok M (fst r) (snd r)) (lt_rodata T)).
  { apply Forall_forall. intros r Hin. rewrite forallb_forall in C13. specialize (C13 r Hin).
    intros i Hi. exact (img_cov_sound SEGS E M (kn cs) _ _ HKN C13 i Hi). }
  (* [comment removed for export] *)
  pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HKN C19) as Lo. cbn [xt_den] in Lo. fold S out in Lo.
  pose proof (ranges_apart_x_sound SEGS E M (kn cs) bb bo N Sb (So - D) (ELit D) HKN C20) as Ap1.
  pose proof (ranges_apart_x_sound SEGS E M (kn cs) bb bo N ob oo (ELit 16) HKN C21) as Ap2.
  rewrite Hspb in Eb. cbn [fst snd] in Eb. rewrite Eb in Ap1, Ap2.
  assert (El1 : elenZ E (ELit D) = D) by (unfold elenZ; cbn [edenot]; apply u64_lit; lia).
  assert (El2 : elenZ E (ELit 16) = 16) by (unfold elenZ; cbn [edenot]; apply u64_lit; lia).
  rewrite El1 in Ap1. rewrite El2 in Ap2. unfold elenZ in Ap1, Ap2. fold Nz in Ap1, Ap2.
  assert (Ef : estart E (SA Sb (So - D)) = S - D).
  { rewrite HspS in HS0. cbn [fst snd] in HS0. unfold estart. cbn [a_base a_off]. lia. }
  rewrite Ef in Ap1.
  rewrite Hspo in E4. cbn [fst snd] in E4. rewrite Z.add_0_r in E4. rewrite E4 in Ap2. rewrite Z.add_0_r in Ap2.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (Hstrict8 : lt_strict T = true -> S mod 8 = 0).
  { intros Hs. rewrite Hs in CS. cbn [negb orb] in CS. apply Z.leb_le in CS.
    destruct (ealign_sound SEGS E M (kn cs) (reg cs 8) HKN) as [_ Hdiv]. fold S in Hdiv.
    apply Z.mod_divide; [lia|]. eapply Z.divide_trans; [|exact Hdiv].
    exists (2 ^ (ealign (kn cs) (reg cs 8) - 3)). change 8 with (2 ^ 3). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  destruct (a2uloop_contract_x_use SEGS _ _ _ _ _ _ LOOP R M S bz lz Nz out sbz (edenot E fl) Hsp
              ltac:(replace (8%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 8)) by (apply bv_eq; reflexivity); rewrite R8; unfold S; symmetry; apply W_u)
              ltac:(replace (19%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 19)) by (apply bv_eq; reflexivity); rewrite R19; unfold bz; symmetry; apply W_u)
              ltac:(replace (S - 2216) with (S + -2216) by lia; exact P0)
              ltac:(replace (S - 2216 + 8) with (S + (-2216 + 8)) by lia; unfold out; rewrite W_u; exact P8)
              ltac:(replace (S - 2216 + 16) with (S + (-2216 + 16)) by lia; exact P16)
              ltac:(replace (S - 2216 + 24) with (S + (-2216 + 24)) by lia; exact P24)
              ltac:(replace (S - 2216 + 32) with (S + (-2216 + 32)) by lia; exact P32)
              ltac:(replace (S - 2216 + 40) with (S + (-2216 + 40)) by lia; unfold sbz; rewrite W_u; exact P40)
              P48 Heven Hsb ltac:(lia) HlN ltac:(lia) HbN Hrd Hnulb Hslack Hro
              ltac:(lia) HS63
              ltac:(replace (S - D) with (S + - D) by lia; exact W1)
              ltac:(replace (S - 2200) with (S + -2200) by lia; exact W2)
              ltac:(replace (S - 2160) with (S + -2160) by lia; exact W3)
              ltac:(lia) ltac:(lia) W4 ltac:(right; lia) ltac:(lia) ltac:(lia) Hstrict8)
    as (regs' & M' & Hms & K2 & K3 & K4 & K8 & Hfr & Hg).
  (* [comment removed for export] *)
  destruct (w_fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (E' := ext_regs E (nxt cs) loop_havoc regs').
  pose proof (ext_regs_agree E (nxt cs) loop_havoc regs') as Hag. fold E' in Hag.
  eapply (call_core SEGS A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SINV argH ISP argH_high NX0_spw argH_agree SINV_frame SINV_agree FS0
            cs E E' R FULL model TT (lt_loop_exit T) _ _ _ regs' M' HC Hfresh Hag).
  - rewrite Hpc. exact Hms.
  - apply (regs_after_region E _ R regs' (nxt cs) loop_havoc (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC) Fsr loop_havoc_nodup).
    intros r Hr0 Hnin. destruct (loop_kept_cases r Hr0 Hnin) as [ -> | [ -> | [ -> | -> ] ] ]; assumption.
  - apply (know_ok_agree' SEGS (nxt cs) E E' M' _ Hag Hkv).
    set (P1 := inrb (S - D) (D - 2216)). set (P2 := fun x => (P1 x || inrb (S - 2200) 16 x)%bool).
    set (P3 := fun x => (P2 x || inrb (S - 2160) 2048 x)%bool).
    set (M1 := mixm P1 M M'). set (M2 := mixm P2 M M'). set (M3 := mixm P3 M M').
    assert (G1 : know_ok SEGS E M1 (hav (kn cs) (reg cs 8) (- D) (D - 2216))).
    { apply (hav_sound E M M1 (kn cs) (reg cs 8) (- D) (D - 2216) HKN ltac:(lia) E1); [|apply mixm_grows; exact Hg].
      intros x Hx. fold S in Hx. unfold M1, mixm, P1. destruct (inrb (S - D) (D - 2216) x) eqn:Hb; [|reflexivity].
      exfalso. apply Hx. replace (S + - D) with (S - D) by lia. apply inrb_inr. exact Hb. }
    assert (G2 : know_ok SEGS E M2 (hav (hav (kn cs) (reg cs 8) (- D) (D - 2216)) (reg cs 8) (-2200) 16)).
    { apply (hav_sound E M1 M2 _ (reg cs 8) (-2200) 16 G1 ltac:(lia) E2).
      - intros x Hx. fold S in Hx. unfold M2, M1, mixm, P2. destruct (P1 x); [reflexivity|]. cbn [orb].
        destruct (inrb (S - 2200) 16 x) eqn:Hb; [|reflexivity]. exfalso. apply Hx.
        replace (S + -2200) with (S - 2200) by lia. apply inrb_inr. exact Hb.
      - apply mixm_grows2; [exact Hg|]. intros x Hx. unfold P2. rewrite Hx. reflexivity. }
    assert (G3 : know_ok SEGS E M3 (hav (hav (hav (kn cs) (reg cs 8) (- D) (D - 2216)) (reg cs 8) (-2200) 16) (reg cs 8) (-2160) 2048)).
    { apply (hav_sound E M2 M3 _ (reg cs 8) (-2160) 2048 G2 ltac:(lia) E3).
      - intros x Hx. fold S in Hx. unfold M3, M2, mixm, P3. destruct (P2 x); [reflexivity|]. cbn [orb].
        destruct (inrb (S - 2160) 2048 x) eqn:Hb; [|reflexivity]. exfalso. apply Hx.
        replace (S + -2160) with (S - 2160) by lia. apply inrb_inr. exact Hb.
      - apply mixm_grows2; [exact Hg|]. intros x Hx. unfold P3. rewrite Hx. reflexivity. }
    assert (E4' : estart E (SA (fst (split_lit oute)) (snd (split_lit oute) + 0)) = bv_unsigned (edenot E oute) + 0).
    { rewrite Hspo. cbn [fst snd]. rewrite !Z.add_0_r. rewrite E4. unfold out. lia. }
    apply (hav_sound E M3 M' _ oute 0 16 G3 ltac:(lia) E4').
    + intros x Hx. fold out in Hx. rewrite Z.add_0_r in Hx. unfold M3, mixm, P3, P2, P1.
      destruct (inrb (S - D) (D - 2216) x || inrb (S - 2200) 16 x || inrb (S - 2160) 2048 x)%bool eqn:Hb; [reflexivity|].
      apply orb_false_iff in Hb as [Hb Hb3]. apply orb_false_iff in Hb as [Hb1' Hb2].
      apply Hfr. intros [F|[F|[F|F]]].
      * apply inrb_inr in F. congruence.
      * apply inrb_inr in F. congruence.
      * apply inrb_inr in F. congruence.
      * exact (Hx F).
    + intros x Hx. unfold M3, mixm in Hx. destruct (P3 x); [exact Hx | apply Hg; exact Hx].
  - intros R' FULL' model' HC' Hfs. apply (Hk E' R' FULL' model'); [| exact HC' | exact Hfs].
    split; [eapply w_env_agree_le; [exact Hag | exact Fle] | exact Hag].
Qed.

(* [comment removed for export] *)
Theorem ext_sound : ext_stmt SEGS A nx0 LIMIT (LBN.xn SEGS A nx0 T) SINV argH ISP FS0.
Proof.
  intros id args. unfold LBN.xn.
  do 40 (destruct id as [|id]; [intros cs cs' E R FULL model TT _ _ Hn; discriminate|]).
  destruct id as [|id]; [exact node_decode_sound|].
  destruct id as [|id]; [exact (node_a2uloop_sound args)|].
  destruct id as [|id]; [exact (node_unkintro_sound args)|].
  intros cs cs' E R FULL model TT _ _ Hn. discriminate.
Qed.

End Sound.

End LBNS.
