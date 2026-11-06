(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.openssl.punycode.images Require Import Asan.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import FpLift WpEngine LibKit StrKit WpTac WpMem.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import ACode AShadow ARt AImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition C_fuzz : code := Eval vm_compute in (mk_code ASEGS 0x1f30e0 210).
Lemma C_fuzz_eq : mk_code ASEGS 0x1f30e0 210 = C_fuzz.
Proof. vm_compute. reflexivity. Qed.
Ltac wp_fz stops := wp_go 0x1f30e0 210%nat C_fuzz_eq C_fuzz stops.

Lemma rget_lof : forall regs (k : nat), (0 < k < 32)%nat -> rget (lof regs) k = getr regs (Z_to_bv 5 (Z.of_nat k)).
Proof. intros regs k Hk. symmetry. apply rrel_getr; [apply rrel_lof | exact Hk]. Qed.

Section Store.
Variable rom : mem.
Variable Post : word -> regfile -> mem -> Prop.
Variables (M : mem) (b n : Z).
Hypothesis Hb : 0 < b.
Hypothesis Hn : 0 <= n.
Hypothesis Hbn : b + n + 1 < 2 ^ 63.
Hypothesis Hacc : acc1 M (b + n).
Hypothesis Hwr : wr_ok ASEGS M (b + n) 1.

Lemma store0_cps : forall l, length l = 32%nat -> rget l 21 = W b -> rget l 19 = W n -> rget l 24 = W SB ->
  (forall l' M', length l' = 32%nat -> same_except [10; 11; 12]%nat l l' ->
     rget l' 10 = W (b + n) -> rget l' 11 = v_addi (rget l 23) 144 -> rget l' 12 = W 16 ->
     cell ASEGS M' (b + n) 1 (W 0) -> unch M M' (fun x => inr x (b + n) 1) -> mem_grows M M' ->
     reach ASEGS rom (W 0x1f3294) l' M' Post) ->
  reach ASEGS rom (Z_to_bv 64 0x1f3274) l M Post.
Proof.
  intros l Hl H21 H19 H24 K.
  destruct Hacc as (s & Hs & Hc).
  regs_open l Hl. subst s5 s3 s8.
  wp_fz [0x1f3294].
  rewrite ?add_W. rewrite sha_addr_r by lia.
  pose proof (bv_unsigned_in_range 8 s) as Hb8. change (bv_modulus 8) with 256 in Hb8.
  exists (W (bv_unsigned s)). split.
  { exists [s]. split; [cbn [rdn]; rewrite Hs; reflexivity|]. rewrite bytes_le_1. rewrite Wu by lia. reflexivity. }
  assert (Hs7 : 0 <= bv_unsigned s <= 7) by (destruct Hc as [Hc|Hc]; lia).
  pose proof (Z.mod_pos_bound (b + n) 8 ltac:(lia)) as Hm8.
  rewrite lb_small by lia. rewrite ?andi7_W by lia. rewrite ?Ws_pos by lia. rewrite ?Wu by lia.
  assert (Kfin : store_ok ASEGS M (Z_to_bv 64 (b + n)) 1 = true
        /\ reach ASEGS rom (Z_to_bv 64 2044564)
            [x0; ra; sp; gp; tp; t0; t1; t2; s0; s1; Z_to_bv 64 (b + n); v_addi s7 144; Z_to_bv 64 16; a3; a4; a5;
             a6; a7; s2; Z_to_bv 64 n; s4; Z_to_bv 64 b; s6; s7; Z_to_bv 64 SB; s9; s10; s11; t3; t4; t5; t6]
            (wbytes M (Z_to_bv 64 (b + n)) (word_to_le_bytes 1 (Z_to_bv 64 0))) Post).
  { split; [apply Hwr; cbn; lia|].
    apply K.
    - reflexivity.
    - intros k Hk. do 32 (destruct k as [|k]; [first [reflexivity | exfalso; apply Hk; cbv; repeat (first [left; reflexivity | right]); fail]|]).
      rewrite !rget_beyond by (cbn [length]; lia). reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - apply (cell_store_same ASEGS M (b + n) 1 (W 0)); cbn; lia.
    - apply unch_store; [apply unch_refl | lia | cbn; lia | intros x Hx; exact Hx].
    - apply wbytes_grows. }
  split; [intros Hnz; split; [intros _; exact Kfin | intros Hbad; exfalso; destruct Hc as [Hc|Hc]; lia] | intros _; exact Kfin].
Qed.
End Store.

(* [comment removed for export] *)
Ltac reg_out HRR Hv :=
  match goal with |- getr ?regs' ?r = _ =>
    let k := eval cbv in (Z.to_nat (bv_unsigned r)) in
    replace r with (Z_to_bv 5 (Z.of_nat k)) by (apply bv_eq; reflexivity);
    rewrite (rrel_getr regs' _ k HRR) by lia; exact Hv end.

(* [comment removed for export] *)
Theorem store0_spec : forall regs F fc M rom b n,
  getr regs 21%bv = W b -> getr regs 19%bv = W n -> getr regs 24%bv = W SB ->
  0 < b -> 0 <= n -> b + n + 1 < 2 ^ 63 ->
  acc1 M (b + n) -> wr_ok ASEGS M (b + n) 1 ->
  exists regs' M',
    msteps ASEGS (mkstF regs F fc (W 0x1f3274) M rom) (mkstF regs' F fc (W 0x1f3294) M' rom)
    /\ (forall r : reg, ~ In (ridx r) [10; 11; 12]%nat -> getr regs' r = getr regs r)
    /\ getr regs' 10%bv = W (b + n) /\ getr regs' 11%bv = W (bv_unsigned (getr regs 23%bv) + 144) /\ getr regs' 12%bv = W 16
    /\ cell ASEGS M' (b + n) 1 (W 0) /\ (forall x, ~ inr x (b + n) 1 -> M' x = M x) /\ mem_grows M M'.
Proof.
  intros regs F fc M rom b n H21 H19 H24 Hb Hn Hbn Hacc Hwr.
  pose (Post := fun (pc' : word) (l' : regfile) (M' : mem) =>
     pc' = W 0x1f3294 /\ same_except [10; 11; 12]%nat (lof regs) l'
     /\ rget l' 10 = W (b + n) /\ rget l' 11 = v_addi (rget (lof regs) 23) 144 /\ rget l' 12 = W 16
     /\ cell ASEGS M' (b + n) 1 (W 0) /\ unch M M' (fun x => inr x (b + n) 1) /\ mem_grows M M').
  assert (HR : reach ASEGS rom (W 0x1f3274) (lof regs) M Post).
  { eapply (store0_cps rom Post M b n Hb Hn Hbn Hacc Hwr); [reflexivity | | | |].
    - rewrite rget_lof by lia. exact H21.
    - rewrite rget_lof by lia. exact H19.
    - rewrite rget_lof by lia. exact H24.
    - intros l' M' Hl' Hse R10 R11 R12 Hcell HU HG. apply reach_done. unfold Post. repeat split; assumption. }
  destruct (reach_exF ASEGS rom _ _ F fc _ _ HR) as (pc' & regs' & l' & M' & Hms & HRR & HP).
  destruct HP as (-> & Hse & R10 & R11 & R12 & Hcell & HU & HG).
  exists regs', M'. split; [exact Hms|].
  split; [intros r Hr; eapply same_except_getr; eassumption|].
  split; [reg_out HRR R10|].
  split.
  { assert (R11' : rget l' 11 = W (bv_unsigned (getr regs 23%bv) + 144)).
    { rewrite R11. rewrite rget_lof by lia. replace (Z_to_bv 5 (Z.of_nat 23)) with (23%bv : bv 5) by (apply bv_eq; reflexivity).
      unfold v_addi. reflexivity. }
    reg_out HRR R11'. }
  split; [reg_out HRR R12|].
  split; [exact Hcell|]. split; [exact HU | exact HG].
Qed.
