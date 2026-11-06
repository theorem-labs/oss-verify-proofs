(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Ub0PlanKit AsanPlanCore
     Ub0_code_221b0_23098 BigBranchUb0 BigLinkBase BigLinkGlue BigLinkInlBaseU BigLinkDqU BigLinkDivBaseU L5Defs L5Kn
     L5Core L5Words.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigModel BigFactsBase BigFactsOps.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegHost_L5CmpU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.

Module L5CMPU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Module PAii := LibSegZ_cmuAii. Module PAid := LibSegZ_cmuAid. Module PAdi := LibSegZ_cmuAdi. Module PAdd := LibSegZ_cmuAdd.
Module PN := LibSegZ_cmuN. Module PP := LibSegZ_cmuP. Module PE := LibSegZ_cmuE. Module PI := LibSegZ_cmuI. Module PJ := LibSegZ_cmuJ.
Module PN2 := LibSegZ_cmuN2. Module PP2 := LibSegZ_cmuP2. Module PZ := LibSegZ_cmuZ.
Section SCFG_1.
Context {SCFG_P : ScfgP}.


Definition CMP : Z := 0x2211c.
Definition SZBR : Z := 0x221b0. Definition SZBR2 : Z := 0x221c0. Definition MINUS : Z := 0x221b4. Definition PLUS : Z := 0x221c4.
Definition EQSET : Z := 0x221d0. Definition LHEAD : Z := 0x221d8. Definition WBR : Z := 0x221fc. Definition WNEXT : Z := 0x22200.
Definition WBR2 : Z := 0x22224. Definition MINUS2 : Z := 0x22228. Definition PLUS2 : Z := 0x22238. Definition RET : Z := 0x22264.
Definition MAXW : Z := 18446744073709551615.
Definition CMP_SCRATCH : Z := 80.
End SCFG_1.


Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Section SCFG_2.
Context {SCFG_P : ScfgP}.

Definition cfg {fx : FPState} (R : bvmap 5 word) (pc : Z) (M : word -> option byte) (model : Model) : config :=
  mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) model.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cmp_kept : list nat := [1; 2; 3; 4; 5; 6; 7; 8; 9; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.
Definition apart (x lx y ly : Z) : Prop := x + lx <= y \/ y + ly <= x.

Definition cmp_obj (M : word -> option byte) (o : Z) (b : L5.bigobj) : Prop :=
  L5.big_at RSEGS M o b /\ Z.testbit (L5.bo_fb b) 1 = false /\ (1 <= L5.bo_len b)%nat /\ Z.of_nat (L5.bo_len b) <= 300 /\
  o mod 8 = 0 /\ 4096 <= o /\ o + 32 <= 2 ^ 47 /\
  4096 <= L5.bo_data o b /\ L5.bo_data o b + 8 * Z.of_nat (L5.bo_len b) <= 2 ^ 47 /\
  L5.defined M (L5.bo_data o b) (8 * Z.of_nat (L5.bo_len b)).
(* [comment removed for export] *)
Definition cmp_stack (M : word -> option byte) (sp xo yo : Z) (bx by_ : L5.bigobj) : Prop :=
  sp mod 16 = 0 /\ 1048656 <= sp <= 140737488355328 /\ L5.writable RSEGS M (sp - 80) 80 /\
  apart (sp - 80) 80 xo 32 /\ apart (sp - 80) 80 yo 32 /\
  apart (sp - 80) 80 (L5.bo_data xo bx) (8 * Z.of_nat (L5.bo_len bx)) /\ apart (sp - 80) 80 (L5.bo_data yo by_) (8 * Z.of_nat (L5.bo_len by_)).

(* [comment removed for export] *)
Definition res_sized (c : Z) (nx ny : nat) : Prop := (c = 0 \/ c = 1 \/ c = MAXW) /\ ((nx < ny)%nat -> c = MAXW) /\ ((ny < nx)%nat -> c = 1).
Definition cmp_val (wx wy : list Z) : Z :=
  if BigFactsBase.val wx <? BigFactsBase.val wy then MAXW else if BigFactsBase.val wy <? BigFactsBase.val wx then 1 else 0.
Lemma cmp_val_cases wx wy : cmp_val wx wy = 0 \/ cmp_val wx wy = 1 \/ cmp_val wx wy = MAXW.
Proof. unfold cmp_val. destruct (_ <? _); [|destruct (_ <? _)]; tauto. Qed.
Lemma cmp_val_lt wx wy : cmp_val wx wy = MAXW <-> BigFactsBase.val wx < BigFactsBase.val wy.
Proof. unfold cmp_val, MAXW. destruct (Z.ltb_spec (BigFactsBase.val wx) (BigFactsBase.val wy)); [|destruct (Z.ltb_spec (BigFactsBase.val wy) (BigFactsBase.val wx))]; split; intros; lia. Qed.
Lemma cmp_val_gt wx wy : cmp_val wx wy = 1 <-> BigFactsBase.val wy < BigFactsBase.val wx.
Proof. unfold cmp_val, MAXW. destruct (Z.ltb_spec (BigFactsBase.val wx) (BigFactsBase.val wy)); [|destruct (Z.ltb_spec (BigFactsBase.val wy) (BigFactsBase.val wx))]; split; intros; lia. Qed.
Lemma cmp_val_eq wx wy : cmp_val wx wy = 0 <-> BigFactsBase.val wx = BigFactsBase.val wy.
Proof. unfold cmp_val, MAXW. destruct (Z.ltb_spec (BigFactsBase.val wx) (BigFactsBase.val wy)); [|destruct (Z.ltb_spec (BigFactsBase.val wy) (BigFactsBase.val wx))]; split; intros; lia. Qed.

Definition cmp_post (M M' : word -> option byte) (R R' : bvmap 5 word) (sp : Z) (nx ny : nat) (wx wy : list Z) : Prop :=
  (forall i, In i cmp_kept -> getr R' (reg i) = getr R (reg i)) /\ regs_preserved R R'
  /\ (exists c, getr R' (reg 10) = Z_to_bv 64 c /\ res_sized c nx ny /\ (nx = ny -> c = cmp_val wx wy))
  /\ (forall a : word, ~ (sp - 80 <= bv_unsigned a < sp) -> M' a = M a) /\ mem_grows M M'.

Definition cmp_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (sp xo yo r : Z) (bx by_ : L5.bigobj)
         (wx wy : list Z),
    m_halted model = None -> m_vm_lazy model = [] ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 10%bv = Z_to_bv 64 xo -> getr R 11%bv = Z_to_bv 64 yo -> getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    cmp_obj M xo bx -> cmp_obj M yo by_ -> cmp_stack M sp xo yo bx by_ -> L5C.obj_limbs RSEGS M bx wx -> L5C.obj_limbs RSEGS M by_ wy ->
    (forall (fx' : FPState) R' M', cmp_post M M' R R' sp (L5.bo_len bx) (L5.bo_len by_) wx wy -> srealizes RSEGS SCFG (cfg (fx:=fx') R' r M' model) K) ->
    srealizes RSEGS SCFG (cfg (fx:=fx) R CMP M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma obj_limbs_data M o b ws : L5.big_at RSEGS M o b -> L5C.obj_limbs RSEGS M b ws ->
  L5.limbs_at RSEGS M (L5.bo_data o b) ws /\ length ws = L5.bo_len b /\ L5W.words_ok ws.
Proof.
  intros B (Ln & F & S). split; [|split; [exact Ln|exact F]]. unfold L5.big_at in B.
  destruct b as [fb n [v0 v1|cap q]]; cbn [L5.bo_st L5.bo_len L5.bo_data L5.bo_fb] in *.
  - destruct B as (_ & _ & _ & _ & U16 & U24 & Hn & _). subst ws.
    destruct n as [|[|[|n]]]; [apply (L5C.limbs_at_nil RSEGS)| | |exfalso; lia]; cbn [firstn]; intros i Hi; cbn [length] in Hi.
    + destruct i; [|exfalso; lia]. cbn [nth]. replace (o + 16 + 8 * Z.of_nat 0) with (o + 16) by lia. exact U16.
    + destruct i as [|[|i]]; [| |exfalso; lia]; cbn [nth].
      replace (o + 16 + 8 * Z.of_nat 0) with (o + 16) by lia. exact U16.
      replace (o + 16 + 8 * Z.of_nat 1) with (o + 24) by lia. exact U24.
  - exact S.
Qed.

Lemma rl9 : (9%bv : bv 5) = reg 9. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl13 : (13%bv : bv 5) = reg 13. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl10 : (10%bv : bv 5) = reg 10. Proof. apply bv_eq. reflexivity. Qed.
Lemma rl19 : (19%bv : bv 5) = reg 19. Proof. apply bv_eq. reflexivity. Qed.
Lemma br_22078 fx R M : msteps RSEGS (st fx R 0x221b0 M) (st fx R (if branch_taken BC_GEU (getr R (reg 9)) (getr R (reg 13)) then 0x221c0 else 0x221b4) M).
Proof. rewrite <- rl9, <- rl13. apply (@BDQU.br_site fx M R 0x221b0 0x221c0 (0x221b0%bv : word) _ BC_GEU 9 13 _ eq_refl F_221b0 eq_refl D_221b0). reflexivity. Qed.
Lemma br_22088 fx R M : msteps RSEGS (st fx R 0x221c0 M) (st fx R (if branch_taken BC_GEU (getr R (reg 13)) (getr R (reg 9)) then 0x221d0 else 0x221c4) M).
Proof. rewrite <- rl9, <- rl13. apply (@BDQU.br_site fx M R 0x221c0 0x221d0 (0x221c0%bv : word) _ BC_GEU 13 9 _ eq_refl F_221c0 eq_refl D_221c0). reflexivity. Qed.
Lemma br_220c4 fx R M : msteps RSEGS (st fx R 0x221fc M) (st fx R (if branch_taken BC_LTU (getr R (reg 10)) (getr R (reg 19)) then 0x22238 else 0x22200) M).
Proof. rewrite <- rl10, <- rl19. apply (@BDQU.br_site fx M R 0x221fc 0x22238 (0x221fc%bv : word) _ BC_LTU 10 19 _ eq_refl F_221fc eq_refl D_221fc). reflexivity. Qed.
Lemma br_220ec fx R M : msteps RSEGS (st fx R 0x22224 M) (st fx R (if branch_taken BC_GEU (getr R (reg 19)) (getr R (reg 10)) then 0x221d8 else 0x22228) M).
Proof. rewrite <- rl10, <- rl19. apply (@BDQU.br_site fx M R 0x22224 0x221d8 (0x22224%bv : word) _ BC_GEU 19 10 _ eq_refl F_22224 eq_refl D_22224). reflexivity. Qed.
Lemma ret_2212c fx R M r : getr R (reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 -> msteps RSEGS (st fx R 0x22264 M) (st fx R r M).
Proof. intros H1 Hr He. apply (BDU.ret_to fx R M 0x22264 W_22264 r F_22264 eq_refl D_22264 H1 Hr He). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition U (R : bvmap 5 word) (k : nat) : Z := bv_unsigned (getr R (reg k)).
Definition VAL (R0 R : bvmap 5 word) (sp xo yo nx ny xd yd fbx fby k xk yk : Z) (i : nat) : word :=
  match i with
  | 2%nat => Z_to_bv 64 sp
  | 33%nat => Z_to_bv 64 xo | 34%nat => Z_to_bv 64 yo | 35%nat => Z_to_bv 64 nx | 36%nat => Z_to_bv 64 ny
  | 37%nat => Z_to_bv 64 xd | 38%nat => Z_to_bv 64 yd | 39%nat => Z_to_bv 64 fbx | 40%nat => Z_to_bv 64 fby | 41%nat => Z_to_bv 64 k
  | 42%nat => getr R (reg 1)
  | 43%nat => getr R0 (reg 1) | 44%nat => getr R0 (reg 8) | 45%nat => getr R0 (reg 9) | 46%nat => getr R0 (reg 18) | 47%nat => getr R0 (reg 19)
  | 48%nat => Z_to_bv 64 xk | 49%nat => Z_to_bv 64 yk
  | _ => getr R (reg i)
  end.
Definition VZ (R0 R : bvmap 5 word) (sp xo yo nx ny xd yd fbx fby k xk yk : Z) (i : nat) : Z :=
  match i with
  | 2%nat => sp
  | 33%nat => xo | 34%nat => yo | 35%nat => nx | 36%nat => ny | 37%nat => xd | 38%nat => yd | 39%nat => fbx | 40%nat => fby | 41%nat => k
  | 42%nat => U R 1 | 43%nat => U R0 1 | 44%nat => U R0 8 | 45%nat => U R0 9 | 46%nat => U R0 18 | 47%nat => U R0 19
  | 48%nat => xk | 49%nat => yk
  | _ => U R i
  end.
Lemma VAL_VZ R0 R sp xo yo nx ny xd yd fbx fby k xk yk :
  0 <= sp < 2 ^ 64 -> 0 <= xo < 2 ^ 64 -> 0 <= yo < 2 ^ 64 -> 0 <= nx < 2 ^ 64 -> 0 <= ny < 2 ^ 64 -> 0 <= xd < 2 ^ 64 -> 0 <= yd < 2 ^ 64 ->
  0 <= fbx < 256 -> 0 <= fby < 256 -> - 1 <= k < 2 ^ 63 -> 0 <= xk < 2 ^ 64 -> 0 <= yk < 2 ^ 64 ->
  forall i, bv_unsigned (ev (Env (VAL R0 R sp xo yo nx ny xd yd fbx fby k xk yk) (fun _ => [])) i) = (VZ R0 R sp xo yo nx ny xd yd fbx fby k xk yk i) mod 2 ^ 64.
Proof.
  intros until i. cbn [ev]. unfold VAL, VZ, U.
  assert (LIT: forall z, -1 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z mod 2 ^ 64).
  { intros z Hz. rewrite Z_to_bv_unsigned. reflexivity. }
  assert (REG: forall RR j, bv_unsigned (getr RR (reg j)) = bv_unsigned (getr RR (reg j)) mod 2 ^ 64).
  { intros. symmetry. apply Z.mod_small. apply (BL.bvu_range _). }
  repeat (lazymatch goal with
          | |- bv_unsigned (match i with _ => _ end) = _ => destruct i as [|i]
          | _ => fail end; try (apply LIT; lia); try apply REG).
  all: try (apply LIT; lia); try apply REG.
Qed.
(* [comment removed for export] *)
Lemma VAL_VZ' R0 R sp xo yo nx ny xd yd fbx fby k xk yk :
  0 <= sp < 2 ^ 64 -> 0 <= xo < 2 ^ 64 -> 0 <= yo < 2 ^ 64 -> 0 <= nx < 2 ^ 64 -> 0 <= ny < 2 ^ 64 -> 0 <= xd < 2 ^ 64 -> 0 <= yd < 2 ^ 64 ->
  0 <= fbx < 256 -> 0 <= fby < 256 -> 0 <= k < 2 ^ 63 -> 0 <= xk < 2 ^ 64 -> 0 <= yk < 2 ^ 64 ->
  forall i, bv_unsigned (ev (Env (VAL R0 R sp xo yo nx ny xd yd fbx fby k xk yk) (fun _ => [])) i) = VZ R0 R sp xo yo nx ny xd yd fbx fby k xk yk i.
Proof.
  intros until i. rewrite VAL_VZ by lia. apply Z.mod_small. unfold VZ, U.
  repeat (lazymatch goal with
          | |- 0 <= match i with _ => _ end < _ => destruct i as [|i]
          | _ => fail end; try lia; try apply (BL.bvu_range _)).
  all: try lia; try apply (BL.bvu_range _).
Qed.

(* [comment removed for export] *)
Definition saved (M : word -> option byte) (sp : Z) (R0 : bvmap 5 word) : Prop :=
  L5.u64_at RSEGS M (sp - 8) (U R0 1) /\ L5.u64_at RSEGS M (sp - 16) (U R0 8) /\ L5.u64_at RSEGS M (sp - 24) (U R0 9) /\
  L5.u64_at RSEGS M (sp - 32) (U R0 18) /\ L5.u64_at RSEGS M (sp - 40) (U R0 19).
Definition views (M : word -> option byte) (sp xd yd : Z) : Prop := L5.u64_at RSEGS M (sp - 56) xd /\ L5.u64_at RSEGS M (sp - 72) yd.
Definition spok (sp : Z) : Prop := sp mod 16 = 0 /\ 1048656 <= sp <= 140737488355328.
Lemma rdn_exteq (M M' : word -> option byte) : (forall x : word, M' x = M x) -> forall n a, rdn RSEGS M' a n = rdn RSEGS M a n.
Proof. intros MM. induction n as [|n IH]; intros a. reflexivity. cbn [rdn]. rewrite MM, IH. reflexivity. Qed.
Lemma u64_keep M M' a v : (forall x : word, M' x = M x) -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M' a v.
Proof. intros MM Hu. unfold L5.u64_at in *. rewrite <- Hu. apply rdn_exteq. exact MM. Qed.
Lemma saved_keep M M' sp R0 : (forall x : word, M' x = M x) -> saved M sp R0 -> saved M' sp R0.
Proof. intros MM (S1 & S2 & S3 & S4 & S5). repeat split; eapply u64_keep; eauto. Qed.
Lemma views_keep M M' sp xd yd : (forall x : word, M' x = M x) -> views M sp xd yd -> views M' sp xd yd.
Proof. intros MM [V1 V2]. split; eapply u64_keep; eauto. Qed.
Lemma u8_keep M M' a v : (forall x : word, M' x = M x) -> L5.u8_at RSEGS M a v -> L5.u8_at RSEGS M' a v.
Proof. intros MM Hu. unfold L5.u8_at in *. rewrite <- Hu. apply rdn_exteq. exact MM. Qed.
Lemma defined_keep M M' a n : (forall x : word, M' x = M x) -> L5.defined M a n -> L5.defined M' a n.
Proof. intros MM D i Hi. rewrite MM. apply D. exact Hi. Qed.

(* [comment removed for export] *)
Definition xflags (M : word -> option byte) (sp xo fbx : Z) : Prop :=
  L5.u8_at RSEGS M xo fbx /\ 0 <= fbx < 256 /\ Z.testbit fbx 1 = false /\ 4096 <= xo /\ xo + 32 <= 2 ^ 47 /\ apart (sp - 80) 80 xo 32.
Lemma xflags_keep M M' sp xo fbx : (forall x : word, M' x = M x) -> xflags M sp xo fbx -> xflags M' sp xo fbx.
Proof. intros MM (F1 & F2). split. eapply u8_keep; eauto. exact F2. Qed.

(* [comment removed for export] *)
Definition at_ret (R0 R' : bvmap 5 word) (sp c : Z) : Prop :=
  getr R' (reg 1) = getr R0 (reg 1) /\ getr R' (reg 2) = Z_to_bv 64 sp /\ getr R' (reg 8) = getr R0 (reg 8) /\ getr R' (reg 9) = getr R0 (reg 9) /\
  getr R' (reg 18) = getr R0 (reg 18) /\ getr R' (reg 19) = getr R0 (reg 19) /\ getr R' (reg 10) = Z_to_bv 64 c.
(* [comment removed for export] *)
Definition cmp_pass : list nat := [3; 4; 5; 6; 7; 15; 16; 17; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KSA : list nat := Eval vm_compute in (BG.kept_list 48 PAii.regs0 PAii.regs_out0).
Lemma KSAii_ok : BG.kept_ok 48 PAii.regs0 PAii.regs_out0 KSA = true. Proof. vm_compute. reflexivity. Qed.
Lemma KSAid_ok : BG.kept_ok 48 PAid.regs0 PAid.regs_out0 KSA = true. Proof. vm_compute. reflexivity. Qed.
Lemma KSAdi_ok : BG.kept_ok 48 PAdi.regs0 PAdi.regs_out0 KSA = true. Proof. vm_compute. reflexivity. Qed.
Lemma KSAdd_ok : BG.kept_ok 48 PAdd.regs0 PAdd.regs_out0 KSA = true. Proof. vm_compute. reflexivity. Qed.

Definition at_szbr (R : bvmap 5 word) (sp xo nx ny : Z) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 80) /\ getr R (reg 8) = Z_to_bv 64 xo /\ getr R (reg 9) = Z_to_bv 64 nx /\
  getr R (reg 11) = Z_to_bv 64 0 /\ getr R (reg 13) = Z_to_bv 64 ny.

Local Ltac intro_obj OX Hd :=
  let B := fresh in
  destruct OX as (B & ?Xs1 & ?Xl1 & ?Xl2 & ?Xa8 & ?Xlo & ?Xhi & ?Xdlo & ?Xdhi & Hd);
  unfold L5.big_at in B; cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_data] in *.

Lemma cmA_conc fx R M (sp xo yo : Z) (bx by_ : L5.bigobj) :
  cmp_obj M xo bx -> cmp_obj M yo by_ -> cmp_stack M sp xo yo bx by_ ->
  getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 10) = Z_to_bv 64 xo -> getr R (reg 11) = Z_to_bv 64 yo ->
  exists fx' R' M', msteps RSEGS (st fx R CMP M) (st fx' R' SZBR M')
    /\ (forall x, In x KSA -> getr R' (reg x) = getr R (reg x))
    /\ at_szbr R' sp xo (Z.of_nat (L5.bo_len bx)) (Z.of_nat (L5.bo_len by_))
    /\ saved M' sp R /\ views M' sp (L5.bo_data xo bx) (L5.bo_data yo by_)
    /\ (forall a : word, ~ (sp - 80 <= bv_unsigned a < sp) -> M' a = M a) /\ mem_grows M M'.
Proof.
  intros OX OY (S16 & Ssp & SW & Sa1 & Sa2 & Sa3 & Sa4) H2 H10 H11. unfold apart in *.
  destruct bx as [fbx nx [xv0 xv1 | xcap xq]]; destruct by_ as [fby ny [yv0 yv1 | ycap yq]];
    intro_obj OX Xd; intro_obj OY Yd;
    destruct H as (X0 & Xfb & X8 & Xb0 & X16 & X24 & XR); destruct H0 as (Y0 & Yfb & Y8 & Yb0 & Y16 & Y24 & YR).
  - set (Vf := VAL R R sp xo yo (Z.of_nat nx) (Z.of_nat ny) (xo + 16) (yo + 16) fbx fby 0 0 0). set (E := Env Vf (fun _ => [])).
    assert (ZA : forall i, bv_unsigned (ev E i) = VZ R R sp xo yo (Z.of_nat nx) (Z.of_nat ny) (xo + 16) (yo + 16) fbx fby 0 0 0 i) by (apply VAL_VZ'; lia). unfold VZ, U in ZA.
    assert (HR: regs_ok E PAii.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PAii.regs0 nth]. repeat split; L5K.slot ZA. }
    assert (HK: know_ok RSEGS E M PAii.kn0). { unfold know_ok, PAii.kn0. L5K.kn_all ZA. }
    destruct (PAii.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & k & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
    apply L5K.nth_error_single in Hnth. subst ps. change PAii.NX0 with 48%nat in Hag.
    exists fx', R', M'. split. exact Hms.
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PAii.regs0 PAii.regs_out0 48 KSA KSAii_ok HR Hag Hregs j Hj). }
    split. { unfold at_szbr. repeat split; rewrite (BG.out_reg PAii.regs_out0 E' R' _ Hregs) by lia; cbn [nth PAii.regs_out0]; L5K.wordE' ZA Hag. }
    change (SR.ps_cells PAii.ps0) with PAii.cells0 in Hcells. unfold PAii.cells0 in Hcells.
    split. { unfold saved, U. repeat split.
      all: rewrite <- Z.add_opp_r; eapply L5K.u64_of_KWord8; [apply Hcells; cbn; tauto | L5K.evalE' ZA Hag | L5K.evalE' ZA Hag]. }
    split. { unfold views. split.
      all: rewrite <- Z.add_opp_r; eapply L5K.u64_of_KWord8; [apply Hcells; cbn; tauto | L5K.evalE' ZA Hag | L5K.evalE' ZA Hag]. }
    split. { intros x Hx. apply Hfr. unfold PAii.F0. L5K.outsideF ZA Hag. } exact Hgr.
  - set (Vf := VAL R R sp xo yo (Z.of_nat nx) (Z.of_nat ny) (xo + 16) yq fbx fby 0 0 0). set (E := Env Vf (fun _ => [])).
    assert (ZA : forall i, bv_unsigned (ev E i) = VZ R R sp xo yo (Z.of_nat nx) (Z.of_nat ny) (xo + 16) yq fbx fby 0 0 0 i) by (apply VAL_VZ'; lia). unfold VZ, U in ZA.
    assert (HR: regs_ok E PAid.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PAid.regs0 nth]. repeat split; L5K.slot ZA. }
    assert (HK: know_ok RSEGS E M PAid.kn0). { unfold know_ok, PAid.kn0. L5K.kn_all ZA. }
    destruct (PAid.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & k & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
    apply L5K.nth_error_single in Hnth. subst ps. change PAid.NX0 with 48%nat in Hag.
    exists fx', R', M'. split. exact Hms.
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PAid.regs0 PAid.regs_out0 48 KSA KSAid_ok HR Hag Hregs j Hj). }
    split. { unfold at_szbr. repeat split; rewrite (BG.out_reg PAid.regs_out0 E' R' _ Hregs) by lia; cbn [nth PAid.regs_out0]; L5K.wordE' ZA Hag. }
    change (SR.ps_cells PAid.ps0) with PAid.cells0 in Hcells. unfold PAid.cells0 in Hcells.
    split. { unfold saved, U. repeat split.
      all: rewrite <- Z.add_opp_r; eapply L5K.u64_of_KWord8; [apply Hcells; cbn; tauto | L5K.evalE' ZA Hag | L5K.evalE' ZA Hag]. }
    split. { unfold views. split.
      all: rewrite <- Z.add_opp_r; eapply L5K.u64_of_KWord8; [apply Hcells; cbn; tauto | L5K.evalE' ZA Hag | L5K.evalE' ZA Hag]. }
    split. { intros x Hx. apply Hfr. unfold PAid.F0. L5K.outsideF ZA Hag. } exact Hgr.
  - set (Vf := VAL R R sp xo yo (Z.of_nat nx) (Z.of_nat ny) xq (yo + 16) fbx fby 0 0 0). set (E := Env Vf (fun _ => [])).
    assert (ZA : forall i, bv_unsigned (ev E i) = VZ R R sp xo yo (Z.of_nat nx) (Z.of_nat ny) xq (yo + 16) fbx fby 0 0 0 i) by (apply VAL_VZ'; lia). unfold VZ, U in ZA.
    assert (HR: regs_ok E PAdi.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PAdi.regs0 nth]. repeat split; L5K.slot ZA. }
    assert (HK: know_ok RSEGS E M PAdi.kn0). { unfold know_ok, PAdi.kn0. L5K.kn_all ZA. }
    destruct (PAdi.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & k & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
    apply L5K.nth_error_single in Hnth. subst ps. change PAdi.NX0 with 48%nat in Hag.
    exists fx', R', M'. split. exact Hms.
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PAdi.regs0 PAdi.regs_out0 48 KSA KSAdi_ok HR Hag Hregs j Hj). }
    split. { unfold at_szbr. repeat split; rewrite (BG.out_reg PAdi.regs_out0 E' R' _ Hregs) by lia; cbn [nth PAdi.regs_out0]; L5K.wordE' ZA Hag. }
    change (SR.ps_cells PAdi.ps0) with PAdi.cells0 in Hcells. unfold PAdi.cells0 in Hcells.
    split. { unfold saved, U. repeat split.
      all: rewrite <- Z.add_opp_r; eapply L5K.u64_of_KWord8; [apply Hcells; cbn; tauto | L5K.evalE' ZA Hag | L5K.evalE' ZA Hag]. }
    split. { unfold views. split.
      all: rewrite <- Z.add_opp_r; eapply L5K.u64_of_KWord8; [apply Hcells; cbn; tauto | L5K.evalE' ZA Hag | L5K.evalE' ZA Hag]. }
    split. { intros x Hx. apply Hfr. unfold PAdi.F0. L5K.outsideF ZA Hag. } exact Hgr.
  - set (Vf := VAL R R sp xo yo (Z.of_nat nx) (Z.of_nat ny) xq yq fbx fby 0 0 0). set (E := Env Vf (fun _ => [])).
    assert (ZA : forall i, bv_unsigned (ev E i) = VZ R R sp xo yo (Z.of_nat nx) (Z.of_nat ny) xq yq fbx fby 0 0 0 i) by (apply VAL_VZ'; lia). unfold VZ, U in ZA.
    assert (HR: regs_ok E PAdd.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PAdd.regs0 nth]. repeat split; L5K.slot ZA. }
    assert (HK: know_ok RSEGS E M PAdd.kn0). { unfold know_ok, PAdd.kn0. L5K.kn_all ZA. }
    destruct (PAdd.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & k & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
    apply L5K.nth_error_single in Hnth. subst ps. change PAdd.NX0 with 48%nat in Hag.
    exists fx', R', M'. split. exact Hms.
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PAdd.regs0 PAdd.regs_out0 48 KSA KSAdd_ok HR Hag Hregs j Hj). }
    split. { unfold at_szbr. repeat split; rewrite (BG.out_reg PAdd.regs_out0 E' R' _ Hregs) by lia; cbn [nth PAdd.regs_out0]; L5K.wordE' ZA Hag. }
    change (SR.ps_cells PAdd.ps0) with PAdd.cells0 in Hcells. unfold PAdd.cells0 in Hcells.
    split. { unfold saved, U. repeat split.
      all: rewrite <- Z.add_opp_r; eapply L5K.u64_of_KWord8; [apply Hcells; cbn; tauto | L5K.evalE' ZA Hag | L5K.evalE' ZA Hag]. }
    split. { unfold views. split.
      all: rewrite <- Z.add_opp_r; eapply L5K.u64_of_KWord8; [apply Hcells; cbn; tauto | L5K.evalE' ZA Hag | L5K.evalE' ZA Hag]. }
    split. { intros x Hx. apply Hfr. unfold PAdd.F0. L5K.outsideF ZA Hag. } exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KSN : list nat := Eval vm_compute in (BG.kept_list 48 PN.regs0 PN.regs_out0).
Lemma KSN_ok : BG.kept_ok 48 PN.regs0 PN.regs_out0 KSN = true. Proof. vm_compute. reflexivity. Qed.
Definition KSP : list nat := Eval vm_compute in (BG.kept_list 48 PP.regs0 PP.regs_out0).
Lemma KSP_ok : BG.kept_ok 48 PP.regs0 PP.regs_out0 KSP = true. Proof. vm_compute. reflexivity. Qed.
Definition KSE : list nat := Eval vm_compute in (BG.kept_list 48 PE.regs0 PE.regs_out0).
Lemma KSE_ok : BG.kept_ok 48 PE.regs0 PE.regs_out0 KSE = true. Proof. vm_compute. reflexivity. Qed.
Definition KSI : list nat := Eval vm_compute in (BG.kept_list 56 PI.regs0 PI.regs_out0).
Lemma KSI_ok : BG.kept_ok 56 PI.regs0 PI.regs_out0 KSI = true. Proof. vm_compute. reflexivity. Qed.
Definition KSJ : list nat := Eval vm_compute in (BG.kept_list 56 PJ.regs0 PJ.regs_out0).
Lemma KSJ_ok : BG.kept_ok 56 PJ.regs0 PJ.regs_out0 KSJ = true. Proof. vm_compute. reflexivity. Qed.
Definition KSN2 : list nat := Eval vm_compute in (BG.kept_list 48 PN2.regs0 PN2.regs_out0).
Lemma KSN2_ok : BG.kept_ok 48 PN2.regs0 PN2.regs_out0 KSN2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KSP2 : list nat := Eval vm_compute in (BG.kept_list 48 PP2.regs0 PP2.regs_out0).
Lemma KSP2_ok : BG.kept_ok 48 PP2.regs0 PP2.regs_out0 KSP2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KSZ : list nat := Eval vm_compute in (BG.kept_list 48 PZ.regs0 PZ.regs_out0).
Lemma KSZ_ok : BG.kept_ok 48 PZ.regs0 PZ.regs_out0 KSZ = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Local Ltac restored OUT E' R' Hregs Hag :=
  unfold at_ret; repeat split;
  rewrite (BG.out_reg OUT E' R' _ Hregs) by lia; cbn [nth OUT edenot]; first [reflexivity | rewrite <- (proj1 Hag) by lia; reflexivity].

(* [comment removed for export] *)
Lemma cmN_conc fx R0 R M (sp xo : Z) :
  spok sp -> L5.writable RSEGS M (sp - 80) 80 -> saved M sp R0 -> 0 <= xo < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (sp - 80) -> getr R (reg 8) = Z_to_bv 64 xo -> getr R (reg 11) = Z_to_bv 64 0 ->
  exists fx' R' M', msteps RSEGS (st fx R MINUS M) (st fx' R' RET M')
    /\ (forall x, In x KSN -> getr R' (reg x) = getr R (reg x)) /\ at_ret R0 R' sp MAXW /\ (forall a : word, M' a = M a) /\ mem_grows M M'.
Proof.
  intros [S16 Ssp] SW SV Hxo H2 H8 H11. pose proof SV as (V1 & V2 & V3 & V4 & V5). unfold U in *.
  set (Vf := VAL R0 R sp xo 0 0 0 0 0 0 0 0 0 0). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall i, bv_unsigned (ev E i) = VZ R0 R sp xo 0 0 0 0 0 0 0 0 0 0 i) by (apply VAL_VZ'; lia). unfold VZ, U in ZA.
  assert (HR: regs_ok E PN.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PN.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PN.kn0). { unfold know_ok, PN.kn0. L5K.kn_all ZA. }
  destruct (PN.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & k & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PN.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PN.regs0 PN.regs_out0 48 KSN KSN_ok HR Hag Hregs j Hj). }
  split. { restored PN.regs_out0 E' R' Hregs Hag. }
  split. { intros a. apply Hfr. apply L5K.outside_nil_e. } exact Hgr.
Qed.

(* [comment removed for export] *)
Lemma cmP_conc fx R0 R M (sp xo : Z) :
  spok sp -> L5.writable RSEGS M (sp - 80) 80 -> saved M sp R0 -> 0 <= xo < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (sp - 80) -> getr R (reg 8) = Z_to_bv 64 xo -> getr R (reg 11) = Z_to_bv 64 0 ->
  exists fx' R' M', msteps RSEGS (st fx R PLUS M) (st fx' R' RET M')
    /\ (forall x, In x KSP -> getr R' (reg x) = getr R (reg x)) /\ at_ret R0 R' sp 1 /\ (forall a : word, M' a = M a) /\ mem_grows M M'.
Proof.
  intros [S16 Ssp] SW SV Hxo H2 H8 H11. pose proof SV as (V1 & V2 & V3 & V4 & V5). unfold U in *.
  set (Vf := VAL R0 R sp xo 0 0 0 0 0 0 0 0 0 0). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall i, bv_unsigned (ev E i) = VZ R0 R sp xo 0 0 0 0 0 0 0 0 0 0 i) by (apply VAL_VZ'; lia). unfold VZ, U in ZA.
  assert (HR: regs_ok E PP.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PP.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PP.kn0). { unfold know_ok, PP.kn0. L5K.kn_all ZA. }
  destruct (PP.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & k & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PP.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PP.regs0 PP.regs_out0 48 KSP KSP_ok HR Hag Hregs j Hj). }
  split. { restored PP.regs_out0 E' R' Hregs Hag. }
  split. { intros a. apply Hfr. apply L5K.outside_nil_e. } exact Hgr.
Qed.

(* [comment removed for export] *)
Definition at_head (R : bvmap 5 word) (sp xo : Z) (k : nat) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 80) /\ getr R (reg 8) = Z_to_bv 64 xo /\
  getr R (reg 9) = Z_to_bv 64 (Z.of_nat k - 1) /\ getr R (reg 18) = Z_to_bv 64 MAXW.
Lemma m1_word : Z_to_bv 64 (-1) = Z_to_bv 64 MAXW. Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma cmE_conc fx (R0 R : bvmap 5 word) M (sp xo : Z) (n : nat) :
  0 <= sp - 80 -> sp < 2 ^ 64 -> 0 <= xo < 2 ^ 64 -> (1 <= n)%nat -> Z.of_nat n <= 300 ->
  getr R (reg 2) = Z_to_bv 64 (sp - 80) -> getr R (reg 8) = Z_to_bv 64 xo -> getr R (reg 9) = Z_to_bv 64 (Z.of_nat n) ->
  exists fx' R' M', msteps RSEGS (st fx R EQSET M) (st fx' R' LHEAD M')
    /\ (forall x, In x KSE -> getr R' (reg x) = getr R (reg x)) /\ at_head R' sp xo n /\ (forall a : word, M' a = M a) /\ mem_grows M M'.
Proof.
  intros Hs1 Hs2 Hxo Hn1 Hn2 H2 H8 H9.
  set (Vf := VAL R0 R sp xo 0 (Z.of_nat n) 0 0 0 0 0 0 0 0). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall i, bv_unsigned (ev E i) = VZ R0 R sp xo 0 (Z.of_nat n) 0 0 0 0 0 0 0 0 i) by (apply VAL_VZ'; lia). unfold VZ, U in ZA.
  assert (HR: regs_ok E PE.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PE.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PE.kn0). { unfold know_ok, PE.kn0. L5K.kn_all ZA. }
  destruct (PE.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & k & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PE.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PE.regs0 PE.regs_out0 48 KSE KSE_ok HR Hag Hregs j Hj). }
  split. { unfold at_head, MAXW. repeat split; rewrite (BG.out_reg PE.regs_out0 E' R' _ Hregs) by lia; cbn [nth PE.regs_out0]; L5K.wordE' ZA Hag. }
  split. { intros a. apply Hfr. apply L5K.outside_nil_e. } exact Hgr.
Qed.

(* [comment removed for export] *)
Definition loopctx (M : word -> option byte) (sp : Z) (R0 : bvmap 5 word) (xd yd : Z) (n : nat) : Prop :=
  spok sp /\ L5.writable RSEGS M (sp - 80) 80 /\ saved M sp R0 /\ views M sp xd yd /\
  4096 <= xd /\ xd + 8 * Z.of_nat n <= 2 ^ 47 /\ 4096 <= yd /\ yd + 8 * Z.of_nat n <= 2 ^ 47 /\ xd mod 8 = 0 /\ yd mod 8 = 0 /\
  L5.defined M xd (8 * Z.of_nat n) /\ L5.defined M yd (8 * Z.of_nat n) /\
  apart (sp - 80) 80 xd (8 * Z.of_nat n) /\ apart (sp - 80) 80 yd (8 * Z.of_nat n) /\ (1 <= n)%nat /\ Z.of_nat n <= 300.
Lemma loopctx_keep M M' sp R0 xd yd n : (forall x : word, M' x = M x) -> mem_grows M M' -> loopctx M sp R0 xd yd n -> loopctx M' sp R0 xd yd n.
Proof.
  intros MM G (C1 & C2 & C3 & C4 & C5 & C6 & C5' & C6' & C7 & C8 & C9 & C10 & C11).
  split. exact C1. split. eapply L5.writable_grows; eauto. split. eapply saved_keep; eauto. split. eapply views_keep; eauto.
  split. exact C5. split. exact C6. split. exact C5'. split. exact C6'. split. exact C7. split. exact C8. split. eapply defined_keep; eauto. split. eapply defined_keep; eauto. exact C11.
Qed.
Local Ltac intro_ctx C :=
  destruct C as ([S16 Ssp] & SW & (V1 & V2 & V3 & V4 & V5) & [W1 W2] & Bx & Bx' & By & By' & Ax & Ay & Dx & Dy & P1 & P2 & Hn1 & Hn2); unfold apart, U in *.

(* [comment removed for export] *)
Lemma cmI_conc fx R0 R M (sp xo xd yd : Z) (n k : nat) (xk yk : Z) :
  loopctx M sp R0 xd yd n -> at_head R sp xo k -> (1 <= k <= n)%nat -> 0 <= xo < 2 ^ 64 ->
  L5.u64_at RSEGS M (xd + 8 * (Z.of_nat k - 1)) xk -> L5.u64_at RSEGS M (yd + 8 * (Z.of_nat k - 1)) yk -> 0 <= xk < 2 ^ 64 -> 0 <= yk < 2 ^ 64 ->
  exists fx' R' M', msteps RSEGS (st fx R LHEAD M) (st fx' R' WBR M')
    /\ (forall x, In x KSI -> getr R' (reg x) = getr R (reg x))
    /\ getr R' (reg 9) = Z_to_bv 64 (Z.of_nat k - 1)
    /\ (getr R' (reg 19) = Z_to_bv 64 xk /\ getr R' (reg 10) = Z_to_bv 64 yk)
    /\ (forall a : word, M' a = M a) /\ mem_grows M M'.
Proof.
  intros C (A2 & A8 & A9 & A18) Hk Hxo Ux Uy Rx Ry. intro_ctx C.
  set (Vf := VAL R0 R sp xo 0 (Z.of_nat n) 0 xd yd 0 0 (Z.of_nat k) xk yk). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall i, bv_unsigned (ev E i) = VZ R0 R sp xo 0 (Z.of_nat n) 0 xd yd 0 0 (Z.of_nat k) xk yk i) by (apply VAL_VZ'; lia). unfold VZ, U in ZA.
  assert (HR: regs_ok E PI.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PI.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PI.kn0). { unfold know_ok, PI.kn0. L5K.kn_all ZA. }
  destruct (PI.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PI.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PI.regs0 PI.regs_out0 56 KSI KSI_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PI.regs_out0 E' R' 9 Hregs) by lia; cbn [nth PI.regs_out0]; L5K.wordE' ZA Hag. }
  split. { split. rewrite (BG.out_reg PI.regs_out0 E' R' 19 Hregs) by lia; cbn [nth PI.regs_out0]; L5K.wordE' ZA Hag.
           rewrite (BG.out_reg PI.regs_out0 E' R' 10 Hregs) by lia; cbn [nth PI.regs_out0]; L5K.wordE' ZA Hag. }
  split. { intros a. apply Hfr. apply L5K.outside_nil_e. } exact Hgr.
Qed.

(* [comment removed for export] *)
Lemma cmJ_conc fx R0 R M (sp xo xd yd : Z) (n k : nat) (xk yk : Z) :
  loopctx M sp R0 xd yd n -> at_head R sp xo k -> (1 <= k <= n)%nat -> 0 <= xo < 2 ^ 64 ->
  L5.u64_at RSEGS M (xd + 8 * (Z.of_nat k - 1)) xk -> L5.u64_at RSEGS M (yd + 8 * (Z.of_nat k - 1)) yk -> 0 <= xk < 2 ^ 64 -> 0 <= yk < 2 ^ 64 ->
  exists fx' R' M', msteps RSEGS (st fx R WNEXT M) (st fx' R' WBR2 M')
    /\ (forall x, In x KSJ -> getr R' (reg x) = getr R (reg x))
    /\ getr R' (reg 9) = Z_to_bv 64 (Z.of_nat (k - 1) - 1)
    /\ (getr R' (reg 19) = Z_to_bv 64 xk /\ getr R' (reg 10) = Z_to_bv 64 yk)
    /\ (forall a : word, M' a = M a) /\ mem_grows M M'.
Proof.
  intros C (A2 & A8 & A9 & A18) Hk Hxo Ux Uy Rx Ry. intro_ctx C.
  set (Vf := VAL R0 R sp xo 0 (Z.of_nat n) 0 xd yd 0 0 (Z.of_nat k) xk yk). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall i, bv_unsigned (ev E i) = VZ R0 R sp xo 0 (Z.of_nat n) 0 xd yd 0 0 (Z.of_nat k) xk yk i) by (apply VAL_VZ'; lia). unfold VZ, U in ZA.
  assert (HR: regs_ok E PJ.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PJ.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PJ.kn0). { unfold know_ok, PJ.kn0. L5K.kn_all ZA. }
  destruct (PJ.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PJ.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PJ.regs0 PJ.regs_out0 56 KSJ KSJ_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PJ.regs_out0 E' R' 9 Hregs) by lia; cbn [nth PJ.regs_out0].
           destruct (Nat.eq_dec k 1) as [->|NE].
           - change (Z.of_nat (1 - 1) - 1) with (-1). rewrite m1_word. unfold MAXW. L5K.wordE' ZA Hag.
           - replace (Z.of_nat (k - 1) - 1) with (Z.of_nat k - 2) by lia. L5K.wordE' ZA Hag. }
  split. { split. rewrite (BG.out_reg PJ.regs_out0 E' R' 19 Hregs) by lia; cbn [nth PJ.regs_out0]; L5K.wordE' ZA Hag.
           rewrite (BG.out_reg PJ.regs_out0 E' R' 10 Hregs) by lia; cbn [nth PJ.regs_out0]; L5K.wordE' ZA Hag. }
  split. { intros a. apply Hfr. apply L5K.outside_nil_e. } exact Hgr.
Qed.

(* [comment removed for export] *)
Lemma cmN2_conc fx R0 R M (sp xo fbx : Z) :
  spok sp -> L5.writable RSEGS M (sp - 80) 80 -> saved M sp R0 -> xflags M sp xo fbx ->
  getr R (reg 2) = Z_to_bv 64 (sp - 80) -> getr R (reg 8) = Z_to_bv 64 xo ->
  exists fx' R' M', msteps RSEGS (st fx R MINUS2 M) (st fx' R' RET M')
    /\ (forall x, In x KSN2 -> getr R' (reg x) = getr R (reg x)) /\ at_ret R0 R' sp MAXW /\ (forall a : word, M' a = M a) /\ mem_grows M M'.
Proof.
  intros [S16 Ssp] SW SV XF H2 H8. pose proof SV as (V1 & V2 & V3 & V4 & V5). destruct XF as (F1 & F2 & F3 & F4 & F5 & F6). unfold apart, U in *.
  set (Vf := VAL R0 R sp xo 0 0 0 0 0 fbx 0 0 0 0). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall i, bv_unsigned (ev E i) = VZ R0 R sp xo 0 0 0 0 0 fbx 0 0 0 0 i) by (apply VAL_VZ'; lia). unfold VZ, U in ZA.
  assert (HR: regs_ok E PN2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PN2.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PN2.kn0). { unfold know_ok, PN2.kn0. L5K.kn_all ZA. }
  destruct (PN2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & k & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PN2.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PN2.regs0 PN2.regs_out0 48 KSN2 KSN2_ok HR Hag Hregs j Hj). }
  split. { restored PN2.regs_out0 E' R' Hregs Hag. }
  split. { intros a. apply Hfr. apply L5K.outside_nil_e. } exact Hgr.
Qed.

Lemma cmP2_conc fx R0 R M (sp xo fbx : Z) :
  spok sp -> L5.writable RSEGS M (sp - 80) 80 -> saved M sp R0 -> xflags M sp xo fbx ->
  getr R (reg 2) = Z_to_bv 64 (sp - 80) -> getr R (reg 8) = Z_to_bv 64 xo ->
  exists fx' R' M', msteps RSEGS (st fx R PLUS2 M) (st fx' R' RET M')
    /\ (forall x, In x KSP2 -> getr R' (reg x) = getr R (reg x)) /\ at_ret R0 R' sp 1 /\ (forall a : word, M' a = M a) /\ mem_grows M M'.
Proof.
  intros [S16 Ssp] SW SV XF H2 H8. pose proof SV as (V1 & V2 & V3 & V4 & V5). destruct XF as (F1 & F2 & F3 & F4 & F5 & F6). unfold apart, U in *.
  set (Vf := VAL R0 R sp xo 0 0 0 0 0 fbx 0 0 0 0). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall i, bv_unsigned (ev E i) = VZ R0 R sp xo 0 0 0 0 0 fbx 0 0 0 0 i) by (apply VAL_VZ'; lia). unfold VZ, U in ZA.
  assert (HR: regs_ok E PP2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PP2.regs0 nth]. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PP2.kn0). { unfold know_ok, PP2.kn0. L5K.kn_all ZA. }
  destruct (PP2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & k & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PP2.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PP2.regs0 PP2.regs_out0 48 KSP2 KSP2_ok HR Hag Hregs j Hj). }
  split. { restored PP2.regs_out0 E' R' Hregs Hag. }
  split. { intros a. apply Hfr. apply L5K.outside_nil_e. } exact Hgr.
Qed.

(* [comment removed for export] *)
Lemma cmZ_conc fx R0 R M (sp xo fbx : Z) :
  spok sp -> L5.writable RSEGS M (sp - 80) 80 -> saved M sp R0 -> xflags M sp xo fbx ->
  getr R (reg 2) = Z_to_bv 64 (sp - 80) -> getr R (reg 8) = Z_to_bv 64 xo ->
  getr R (reg 9) = Z_to_bv 64 MAXW -> getr R (reg 18) = Z_to_bv 64 MAXW ->
  exists fx' R' M', msteps RSEGS (st fx R LHEAD M) (st fx' R' RET M')
    /\ (forall x, In x KSZ -> getr R' (reg x) = getr R (reg x)) /\ at_ret R0 R' sp 0 /\ (forall a : word, M' a = M a) /\ mem_grows M M'.
Proof.
  intros [S16 Ssp] SW SV XF H2 H8 H9 H18. pose proof SV as (V1 & V2 & V3 & V4 & V5). destruct XF as (F1 & F2 & F3 & F4 & F5 & F6). unfold apart, U in *.
  set (Vf := VAL R0 R sp xo 0 0 0 0 0 fbx 0 0 0 0). set (E := Env Vf (fun _ => [])).
  assert (ZA : forall i, bv_unsigned (ev E i) = VZ R0 R sp xo 0 0 0 0 0 fbx 0 0 0 0 i) by (apply VAL_VZ'; lia). unfold VZ, U in ZA.
  assert (HR: regs_ok E PZ.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PZ.regs0 nth]. unfold MAXW in *. repeat split; L5K.slot ZA. }
  assert (HK: know_ok RSEGS E M PZ.kn0). { unfold know_ok, PZ.kn0. L5K.kn_all ZA. }
  destruct (PZ.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & k & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply L5K.nth_error_single in Hnth. subst ps. change PZ.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PZ.regs0 PZ.regs_out0 48 KSZ KSZ_ok HR Hag Hregs j Hj). }
  split. { restored PZ.regs_out0 E' R' Hregs Hag. }
  split. { intros a. apply Hfr. apply L5K.outside_nil_e. } exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition enc (z : Z) : Z := if z <? 0 then MAXW else z.
Lemma compare_loop_cases k wx wy :
  BigModel.compare_loop k wx wy = 0 \/ BigModel.compare_loop k wx wy = 1 \/ BigModel.compare_loop k wx wy = -1.
Proof. induction k as [|k IH]; cbn [BigModel.compare_loop]. tauto. destruct (_ <? _). tauto. destruct (_ <? _); tauto. Qed.
Lemma enc_cases k wx wy : let c := enc (BigModel.compare_loop k wx wy) in c = 0 \/ c = 1 \/ c = MAXW.
Proof. unfold enc. destruct (compare_loop_cases k wx wy) as [->|[->| ->]]; cbn; tauto. Qed.

Local Ltac kin K i := rewrite (K i) by (apply L5K.in_b; vm_compute; reflexivity).

Lemma wloop (k : nat) : forall fx R0 R M (sp xo xd yd fbx : Z) (n : nat) (wx wy : list Z),
  loopctx M sp R0 xd yd n -> xflags M sp xo fbx -> at_head R sp xo k -> (k <= n)%nat -> 0 <= xo < 2 ^ 64 ->
  L5.limbs_at RSEGS M xd wx -> L5.limbs_at RSEGS M yd wy -> length wx = n -> length wy = n -> L5W.words_ok wx -> L5W.words_ok wy ->
  exists fx' R' M', msteps RSEGS (st fx R LHEAD M) (st fx' R' RET M')
    /\ (forall x, In x cmp_pass -> getr R' (reg x) = getr R (reg x))
    /\ at_ret R0 R' sp (enc (BigModel.compare_loop k wx wy))
    /\ (forall a : word, M' a = M a) /\ mem_grows M M'.
Proof.
  induction k as [|k IH]; intros fx R0 R M sp xo xd yd fbx n wx wy C XF AT Hkn Hxo Lx Ly Nx Ny Wx Wy.
  - (* [comment removed for export] *)
    destruct AT as (A2 & A8 & A9 & A18). pose proof C as (SP & SW & SV & _).
    change (Z.of_nat 0 - 1) with (-1) in A9. rewrite m1_word in A9.
    destruct (cmZ_conc fx R0 R M sp xo fbx SP SW SV XF A2 A8 A9 A18) as (fx1 & R1 & M1 & MS1 & K1 & RET1 & MM1 & G1).
    exists fx1, R1, M1. split. exact MS1. split. { intros x Hx. apply K1. apply (L5K.incl_b cmp_pass KSZ ltac:(vm_compute; reflexivity)). exact Hx. }
    split. { exact RET1. } split. exact MM1. exact G1.
  - pose proof AT as (A2 & A8 & A9 & A18). pose proof C as (_ & _ & _ & _ & Bxlo & Bxhi & Bylo & Byhi & _).
    set (xk := L5W.nth_w wx k). set (yk := L5W.nth_w wy k).
    assert (Rxk : 0 <= xk < 2 ^ 64) by (apply L5W.words_ok_nth; exact Wx). assert (Ryk : 0 <= yk < 2 ^ 64) by (apply L5W.words_ok_nth; exact Wy).
    assert (Ux : L5.u64_at RSEGS M (xd + 8 * (Z.of_nat (S k) - 1)) xk).
    { replace (xd + 8 * (Z.of_nat (S k) - 1)) with (xd + 8 * Z.of_nat k) by lia. apply Lx. lia. }
    assert (Uy : L5.u64_at RSEGS M (yd + 8 * (Z.of_nat (S k) - 1)) yk).
    { replace (yd + 8 * (Z.of_nat (S k) - 1)) with (yd + 8 * Z.of_nat k) by lia. apply Ly. lia. }
    destruct (cmI_conc fx R0 R M sp xo xd yd n (S k) xk yk C AT ltac:(lia) Hxo Ux Uy Rxk Ryk) as (fx1 & R1 & M1 & MS1 & K1 & B9 & (B19 & B10) & MM1 & G1).
    pose proof (br_220c4 fx1 R1 M1) as MB1. rewrite B10, B19 in MB1.
    cbn [BigModel.compare_loop]. change (BigModel.nth_w wx k) with xk. change (BigModel.nth_w wy k) with yk.
    assert (K1' : forall x, In x cmp_pass -> getr R1 (reg x) = getr R (reg x)).
    { intros x Hx. apply K1. apply (L5K.incl_b cmp_pass KSI ltac:(vm_compute; reflexivity)). exact Hx. }
    assert (C1: loopctx M1 sp R0 xd yd n) by (eapply loopctx_keep; eauto). assert (XF1: xflags M1 sp xo fbx) by (eapply xflags_keep; eauto).
    pose proof C1 as (SP1 & SW1 & SV1 & _).
    destruct (branch_taken BC_LTU (Z_to_bv 64 yk) (Z_to_bv 64 xk)) eqn:LT1.
    + (* [comment removed for export] *)
      assert (LT1': (yk <? xk) = true). { unfold branch_taken, bv_ltu in LT1. rewrite !BG.unsigned_lit in LT1 by lia. exact LT1. }
      rewrite LT1'.
      destruct (cmP2_conc fx1 R0 R1 M1 sp xo fbx SP1 SW1 SV1 XF1 ltac:(kin K1 2%nat; exact A2) ltac:(kin K1 8%nat; exact A8)) as (fx2 & R2 & M2 & MS2 & K2 & RET2 & MM2 & G2).
      exists fx2, R2, M2. split. { eapply msteps_trans. exact MS1. eapply msteps_trans. exact MB1. exact MS2. }
      split. { intros x Hx. rewrite (K2 x). apply K1'. exact Hx. apply (L5K.incl_b cmp_pass KSP2 ltac:(vm_compute; reflexivity)). exact Hx. }
      split. { exact RET2. }
      split. { intros a. rewrite MM2. apply MM1. } eapply mem_grows_trans; eauto.
    + (* [comment removed for export] *)
      assert (LT1': (yk <? xk) = false). { unfold branch_taken, bv_ltu in LT1. rewrite !BG.unsigned_lit in LT1 by lia. exact LT1. }
      rewrite LT1'.
      assert (AT1: at_head R1 sp xo (S k)). { unfold at_head. split. kin K1 2%nat; exact A2. split. kin K1 8%nat; exact A8. split. exact B9. kin K1 18%nat; exact A18. }
      assert (Ux1 : L5.u64_at RSEGS M1 (xd + 8 * (Z.of_nat (S k) - 1)) xk) by (eapply u64_keep; eauto).
      assert (Uy1 : L5.u64_at RSEGS M1 (yd + 8 * (Z.of_nat (S k) - 1)) yk) by (eapply u64_keep; eauto).
      destruct (cmJ_conc fx1 R0 R1 M1 sp xo xd yd n (S k) xk yk C1 AT1 ltac:(lia) Hxo Ux1 Uy1 Rxk Ryk) as (fx2 & R2 & M2 & MS2 & K2 & C9 & (C19 & C10) & MM2 & G2).
      pose proof (br_220ec fx2 R2 M2) as MB2. rewrite C19, C10 in MB2.
      assert (C2: loopctx M2 sp R0 xd yd n) by (eapply loopctx_keep; eauto). assert (XF2: xflags M2 sp xo fbx) by (eapply xflags_keep; eauto).
      pose proof C2 as (SP2 & SW2 & SV2 & _).
      destruct (branch_taken BC_GEU (Z_to_bv 64 xk) (Z_to_bv 64 yk)) eqn:GE2.
      * (* [comment removed for export] *)
        assert (GE2': (xk <? yk) = false).
        { unfold branch_taken, bv_ltu in GE2. apply Bool.negb_true_iff in GE2. rewrite !BG.unsigned_lit in GE2 by lia. exact GE2. }
        rewrite GE2'.
        assert (AT2: at_head R2 sp xo k).
        { unfold at_head. split. kin K2 2%nat; kin K1 2%nat; exact A2. split. kin K2 8%nat; kin K1 8%nat; exact A8.
          split. rewrite C9. f_equal. lia. kin K2 18%nat; kin K1 18%nat; exact A18. }
        assert (Lx2: L5.limbs_at RSEGS M2 xd wx).
        { apply (L5C.limbs_at_agree RSEGS M M2). intros i Hi. rewrite MM2. apply MM1. lia. rewrite Nx. lia. exact Lx. }
        assert (Ly2: L5.limbs_at RSEGS M2 yd wy).
        { apply (L5C.limbs_at_agree RSEGS M M2). intros i Hi. rewrite MM2. apply MM1. lia. rewrite Ny. lia. exact Ly. }
        destruct (IH fx2 R0 R2 M2 sp xo xd yd fbx n wx wy C2 XF2 AT2 ltac:(lia) Hxo Lx2 Ly2 Nx Ny Wx Wy) as (fx3 & R3 & M3 & MS3 & K3 & RES & MM3 & G3).
        exists fx3, R3, M3. split. { eapply msteps_trans. exact MS1. eapply msteps_trans. exact MB1. eapply msteps_trans. exact MS2. eapply msteps_trans. exact MB2. exact MS3. }
        split. { intros x Hx. rewrite (K3 x Hx). rewrite (K2 x). apply K1'. exact Hx. apply (L5K.incl_b cmp_pass KSJ ltac:(vm_compute; reflexivity)). exact Hx. }
        split. exact RES. split. { intros a. rewrite MM3, MM2. apply MM1. } eapply mem_grows_trans. exact G1. eapply mem_grows_trans; eauto.
      * (* [comment removed for export] *)
        assert (GE2': (xk <? yk) = true).
        { unfold branch_taken, bv_ltu in GE2. apply Bool.negb_false_iff in GE2. rewrite !BG.unsigned_lit in GE2 by lia. exact GE2. }
        rewrite GE2'.
        destruct (cmN2_conc fx2 R0 R2 M2 sp xo fbx SP2 SW2 SV2 XF2 ltac:(kin K2 2%nat; kin K1 2%nat; exact A2) ltac:(kin K2 8%nat; kin K1 8%nat; exact A8)) as (fx3 & R3 & M3 & MS3 & K3 & RET3 & MM3 & G3).
        exists fx3, R3, M3. split. { eapply msteps_trans. exact MS1. eapply msteps_trans. exact MB1. eapply msteps_trans. exact MS2. eapply msteps_trans. exact MB2. exact MS3. }
        split. { intros x Hx. rewrite (K3 x). rewrite (K2 x). apply K1'. exact Hx. apply (L5K.incl_b cmp_pass KSJ ltac:(vm_compute; reflexivity)). exact Hx.
                 apply (L5K.incl_b cmp_pass KSN2 ltac:(vm_compute; reflexivity)). exact Hx. }
        split. { exact RET3. }
        split. { intros a. rewrite MM3, MM2. apply MM1. } eapply mem_grows_trans. exact G1. eapply mem_grows_trans; eauto.
Qed.

(* [comment removed for export] *)
Lemma enc_full wx wy n : length wx = n -> length wy = n -> L5W.words_ok wx -> L5W.words_ok wy ->
  enc (BigModel.compare_loop n wx wy) = cmp_val wx wy.
Proof.
  intros Nx Ny Wx Wy. apply L5W.words_ok_BF in Wx. apply L5W.words_ok_BF in Wy.
  rewrite (BigFactsOps.compare_loop_spec wx wy Wx Wy n) by lia.
  rewrite <- Nx at 1. rewrite firstn_all. rewrite <- Ny. rewrite firstn_all.
  unfold enc, cmp_val, BigFactsOps.cmp3.
  destruct (Z.compare_spec (BigFactsBase.val wx) (BigFactsBase.val wy));
    destruct (Z.ltb_spec (BigFactsBase.val wx) (BigFactsBase.val wy)); try lia;
    destruct (Z.ltb_spec (BigFactsBase.val wy) (BigFactsBase.val wx)); try lia; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma kept_regs_preserved R R' : (forall i, In i cmp_kept -> getr R' (reg i) = getr R (reg i)) -> regs_preserved R R'.
Proof.
  intros K x Hx. rewrite <- (AX2S.ridx_roundtrip x). apply K.
  unfold callee_saved_idx in Hx. unfold AX2.ridx. set (z := bv_unsigned x) in *. cbn in Hx.
  repeat (destruct Hx as [Hx|Hx]; [rewrite <- Hx; cbn; tauto|]). destruct Hx.
Qed.

(* [comment removed for export] *)
Lemma kept_of_pass R R' sp c :
  getr R (reg 2) = Z_to_bv 64 sp -> (forall i, In i cmp_pass -> getr R' (reg i) = getr R (reg i)) -> at_ret R R' sp c ->
  forall i, In i cmp_kept -> getr R' (reg i) = getr R (reg i).
Proof.
  intros H2 K (T1 & T2 & T8 & T9 & T18 & T19 & _) i Hi.
  destruct (existsb (Nat.eqb i) cmp_pass) eqn:PB. { apply K. apply L5K.in_b. exact PB. }
  cbn in Hi. repeat (destruct Hi as [<-|Hi]; [first [discriminate PB | rewrite ?H2; assumption] |]). destruct Hi.
Qed.

Theorem cmp_run (fx : FPState) R M (sp xo yo r : Z) (bx by_ : L5.bigobj) (wx wy : list Z) :
  getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 10) = Z_to_bv 64 xo -> getr R (reg 11) = Z_to_bv 64 yo -> getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r ->
  cmp_obj M xo bx -> cmp_obj M yo by_ -> cmp_stack M sp xo yo bx by_ -> L5C.obj_limbs RSEGS M bx wx -> L5C.obj_limbs RSEGS M by_ wy ->
  exists (fx' : FPState) R' M', msteps RSEGS (st fx R CMP M) (st fx' R' r M') /\ cmp_post M M' R R' sp (L5.bo_len bx) (L5.bo_len by_) wx wy.
Proof.
  intros H2 H10 H11 H1 [Hr He] OX OY OS OLX OLY.
  destruct (obj_limbs_data M xo bx wx ltac:(exact (proj1 OX)) OLX) as (Lx & Nx & Wx).
  destruct (obj_limbs_data M yo by_ wy ltac:(exact (proj1 OY)) OLY) as (Ly & Ny & Wy).
  destruct (cmA_conc fx R M sp xo yo bx by_ OX OY OS H2 H10 H11) as (fx1 & R1 & M1 & MS1 & K1 & (A2 & A8 & A9 & A11 & A13) & SV1 & VW1 & MM1 & G1).
  pose proof OX as ((Xfb & Xfbr & _ & XST) & Xs1 & Xl1 & Xl2 & X8 & Xlo & Xhi & Xdlo & Xdhi & Xd).
  pose proof OY as ((_ & _ & _ & YST) & _ & Yl1 & Yl2 & _ & _ & _ & Ydlo & Ydhi & Yd).
  destruct OS as (S16 & Ssp & SW & Sa1 & Sa2 & Sa3 & Sa4).
  assert (Ax: L5.bo_data xo bx mod 8 = 0).
  { destruct bx as [f l [v0 v1|c q]]; cbn [L5.bo_data L5.bo_st] in *. rewrite Z.add_mod, X8 by lia. reflexivity.
    destruct XST as (_ & _ & _ & _ & _ & Q8 & _). exact Q8. }
  assert (Ay: L5.bo_data yo by_ mod 8 = 0).
  { destruct by_ as [f l [v0 v1|c q]]; cbn [L5.bo_data L5.bo_st] in *. pose proof OY as (_ & _ & _ & _ & Y8 & _). rewrite Z.add_mod, Y8 by lia. reflexivity.
    destruct YST as (_ & _ & _ & _ & _ & Q8 & _). exact Q8. }
  set (xd := L5.bo_data xo bx) in *. set (yd := L5.bo_data yo by_) in *.
  set (nx := L5.bo_len bx) in *. set (ny := L5.bo_len by_) in *. set (fbx := L5.bo_fb bx) in *.
  assert (SP: spok sp) by (split; assumption).
  assert (SW1: L5.writable RSEGS M1 (sp - 80) 80) by (eapply L5.writable_grows; eauto).
  assert (XF1: xflags M1 sp xo fbx).
  { split. 2: (repeat split; unfold apart in *; try assumption; lia).
    eapply (L5K.u8_at_keep RSEGS M M1 (sp - 80) sp). exact MM1. unfold apart in Sa1; lia. lia. lia. exact Xfb. }
  assert (Hxo: 0 <= xo < 2 ^ 64) by lia.
  assert (K1' : forall x, In x cmp_pass -> getr R1 (reg x) = getr R (reg x)).
  { intros x Hx. apply K1. apply (L5K.incl_b cmp_pass KSA ltac:(vm_compute; reflexivity)). exact Hx. }
  assert (PACK: forall (fx' : FPState) R' M' c, msteps RSEGS (st fx1 R1 SZBR M1) (st fx' R' RET M') ->
      (forall x, In x cmp_pass -> getr R' (reg x) = getr R1 (reg x)) -> at_ret R R' sp c -> res_sized c nx ny -> (nx = ny -> c = cmp_val wx wy) ->
      (forall a : word, M' a = M1 a) -> mem_grows M1 M' ->
      exists (fx'' : FPState) R'' M'', msteps RSEGS (st fx R CMP M) (st fx'' R'' r M'') /\ cmp_post M M'' R R'' sp nx ny wx wy).
  { intros fx' R' M' c MS K RETc Hc VAL' MM G.
    pose proof RETc as (T1 & _ & _ & _ & _ & _ & T10).
    pose proof (ret_2212c fx' R' M' r ltac:(rewrite T1; exact H1) Hr He) as MSR.
    exists fx', R', M'. split. { eapply msteps_trans. exact MS1. eapply msteps_trans. exact MS. exact MSR. }
    assert (KK: forall i, In i cmp_kept -> getr R' (reg i) = getr R (reg i)).
    { apply (kept_of_pass R R' sp c H2). intros i Hi. rewrite (K i Hi). apply K1'. exact Hi. exact RETc. }
    split. exact KK. split. apply kept_regs_preserved; exact KK. split. { exists c. split. exact T10. split. exact Hc. exact VAL'. }
    split. { intros a Ha. rewrite MM. apply MM1. exact Ha. } eapply mem_grows_trans; eauto. }
  pose proof (br_22078 fx1 R1 M1) as MB1. rewrite A9, A13 in MB1.
  destruct (branch_taken BC_GEU (Z_to_bv 64 (Z.of_nat nx)) (Z_to_bv 64 (Z.of_nat ny))) eqn:GE1.
  - pose proof (br_22088 fx1 R1 M1) as MB2. rewrite A9, A13 in MB2.
    destruct (branch_taken BC_GEU (Z_to_bv 64 (Z.of_nat ny)) (Z_to_bv 64 (Z.of_nat nx))) eqn:GE2.
    + (* [comment removed for export] *)
      assert (EQ: nx = ny).
      { unfold branch_taken in GE1, GE2. apply Bool.negb_true_iff in GE1. apply Bool.negb_true_iff in GE2.
        unfold bv_ltu in GE1, GE2. rewrite !BG.unsigned_lit in GE1, GE2 by lia. apply Z.ltb_ge in GE1. apply Z.ltb_ge in GE2. lia. }
      destruct (cmE_conc fx1 R R1 M1 sp xo nx ltac:(lia) ltac:(lia) Hxo Xl1 Xl2 A2 A8 A9) as (fx2 & R2 & M2 & MS2 & K2 & AT2 & MM2 & G2).
      assert (C2: loopctx M2 sp R xd yd nx).
      { eapply loopctx_keep. exact MM2. exact G2.
        split. exact SP. split. exact SW1. split. exact SV1. split. exact VW1.
        split. lia. split. lia. split. lia. split. lia. split. exact Ax. split. exact Ay.
        split. eapply L5.defined_grows; eauto. split. { replace nx with ny. eapply L5.defined_grows; eauto. }
        split. exact Sa3. split. { replace nx with ny. exact Sa4. } split. exact Xl1. exact Xl2. }
      assert (XF2: xflags M2 sp xo fbx) by (eapply xflags_keep; eauto).
      assert (Lx2: L5.limbs_at RSEGS M2 xd wx).
      { apply (L5C.limbs_at_agree RSEGS M M2). 2: lia. 2: rewrite Nx; lia. 2: exact Lx.
        intros i Hi. rewrite MM2. apply MM1. rewrite BG.unsigned_lit by lia. rewrite Nx in Hi. unfold apart in Sa3. lia. }
      assert (Ly2: L5.limbs_at RSEGS M2 yd wy).
      { apply (L5C.limbs_at_agree RSEGS M M2). 2: lia. 2: rewrite Ny; lia. 2: exact Ly.
        intros i Hi. rewrite MM2. apply MM1. rewrite BG.unsigned_lit by lia. rewrite Ny in Hi. unfold apart in Sa4. lia. }
      destruct (wloop nx fx2 R R2 M2 sp xo xd yd fbx nx wx wy C2 XF2 AT2 ltac:(lia) Hxo Lx2 Ly2 Nx ltac:(lia) Wx Wy) as (fx3 & R3 & M3 & MS3 & K3 & RETc & MM3 & G3).
      apply (PACK fx3 R3 M3 (enc (BigModel.compare_loop nx wx wy))). { eapply msteps_trans. exact MB1. eapply msteps_trans. exact MB2. eapply msteps_trans. exact MS2. exact MS3. }
      { intros x Hx. rewrite (K3 x Hx). apply K2. apply (L5K.incl_b cmp_pass KSE ltac:(vm_compute; reflexivity)). exact Hx. }
      exact RETc. { split. apply enc_cases. split; intros; lia. } { intros _. apply (enc_full wx wy nx Nx ltac:(lia) Wx Wy). }
      { intros a. rewrite MM3. apply MM2. } eapply mem_grows_trans; eauto.
    + (* [comment removed for export] *)
      assert (GE': (ny < nx)%nat).
      { unfold branch_taken, bv_ltu in GE1, GE2. apply Bool.negb_true_iff in GE1. apply Bool.negb_false_iff in GE2. rewrite !BG.unsigned_lit in GE1, GE2 by lia.
        apply Z.ltb_ge in GE1. apply Z.ltb_lt in GE2. lia. }
      destruct (cmP_conc fx1 R R1 M1 sp xo SP SW1 SV1 Hxo A2 A8 A11) as (fx2 & R2 & M2 & MS2 & K2 & RET2 & MM2 & G2).
      apply (PACK fx2 R2 M2 1). { eapply msteps_trans. exact MB1. eapply msteps_trans. exact MB2. exact MS2. }
      { intros x Hx. apply K2. apply (L5K.incl_b cmp_pass KSP ltac:(vm_compute; reflexivity)). exact Hx. }
      exact RET2. { split. right; left; reflexivity. split. intros; lia. reflexivity. } { intros; exfalso; lia. } exact MM2. exact G2.
  - (* [comment removed for export] *)
    assert (LT': (nx < ny)%nat).
    { unfold branch_taken, bv_ltu in GE1. apply Bool.negb_false_iff in GE1. rewrite !BG.unsigned_lit in GE1 by lia. apply Z.ltb_lt in GE1. lia. }
    destruct (cmN_conc fx1 R R1 M1 sp xo SP SW1 SV1 Hxo A2 A8 A11) as (fx2 & R2 & M2 & MS2 & K2 & RET2 & MM2 & G2).
    apply (PACK fx2 R2 M2 MAXW). { eapply msteps_trans. exact MB1. exact MS2. }
    { intros x Hx. apply K2. apply (L5K.incl_b cmp_pass KSN ltac:(vm_compute; reflexivity)). exact Hx. }
    exact RET2. { split. right; right; reflexivity. split. reflexivity. intros; lia. } { intros; exfalso; lia. } exact MM2. exact G2.
Qed.

Lemma r1 : (1%bv : bv 5) = reg 1. Proof. apply bv_eq; reflexivity. Qed.
Lemma r2 : (2%bv : bv 5) = reg 2. Proof. apply bv_eq; reflexivity. Qed.
Lemma r10 : (10%bv : bv 5) = reg 10. Proof. apply bv_eq; reflexivity. Qed.
Lemma r11 : (11%bv : bv 5) = reg 11. Proof. apply bv_eq; reflexivity. Qed.

Theorem cmp_ok : cmp_spec.
Proof.
  intros fx R M model K sp xo yo r bx by_ wx wy Hh Hl H2 H10 H11 H1 Hra OX OY OS OLX OLY HK. unfold cfg.
  rewrite r2 in H2. rewrite r10 in H10. rewrite r11 in H11. rewrite r1 in H1.
  eapply (L5.run_cps RSEGS (fun _ R' M' => cmp_post M M' R R' sp (L5.bo_len bx) (L5.bo_len by_) wx wy)). exact Hh. exact Hl.
  - exact (cmp_run fx R M sp xo yo r bx by_ wx wy H2 H10 H11 H1 Hra OX OY OS OLX OLY).
  - intros fx' R' M' HP. apply HK. exact HP.
Qed.
End SCFG_2.


End L5CMPU.
