(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg SymExec AxSymExec3 AxSymExec3B AxSymExec3Sound
  HeapIface L5Defs L5Core PmLibDefs PmLibSpecs PmRef.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutL5A.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmParseSW Require Import UvZ.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGenW Require Import ParseStringBitsXBW.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac dlia := Z.div_mod_to_equations; lia.

Module PCVK.
Import PMR.
Abbreviation uv := CL5A.uv.
(* [comment removed for export] *)
Definition V (n : nat) : expr := EVar n.
Definition ADD (a b : expr) : expr := EAlu ALU_ADD a b.
Definition SUBE (a b : expr) : expr := EAlu ALU_SUB a b.
Definition ANDE (a b : expr) : expr := EAlu ALU_AND a b.
Definition ORE (a b : expr) : expr := EAlu ALU_OR a b.
Definition SRLE (a b : expr) : expr := EAlu ALU_SRL a b.
Definition SLTUE (a b : expr) : expr := EAlu ALU_SLTU a b.
Definition MULE (a b : expr) : expr := EMd M_MUL a b.
Definition ADDW (a b : expr) : expr := EAluw ALU_ADD a b.
Definition SLLW (a b : expr) : expr := EAluw ALU_SLL a b.
Definition SRLW (a b : expr) : expr := EAluw ALU_SRL a b.
Definition EXT4 (a : expr) : expr := EExt true 0 4 a.
Definition has (cells : list kentry) (k : kentry) : bool := CC.has_cell cells k.
Definition hasr (cells : list kentry) (e : expr) (lo hi : Z) : bool := has cells (KRange e lo hi).
Lemma has_ok : forall segs E (M : word -> option byte) cells X, know_ok segs E M cells -> has cells X = true -> kentry_ok segs E M X.
Proof. intros segs E M cells X HK H. unfold has in H. apply CC.has_cell_In in H. exact (proj1 (Forall_forall _ _) HK X H). Qed.
(* [comment removed for export] *)
Definition fe_hs (A : expr) : expr := SLTUE (SUBE (SRLW A (ELit 10)) (ELit 54)) (ELit 1).
Definition fe_lt128 (H : expr) : expr := SLTUE H (ELit 128).
Definition fe_surr (H : expr) : expr := SLTUE (SUBE (MULE (ELit 2048) (SRLE H (ELit 11))) (ELit 55296)) (ELit 1).
Definition fe_lt2k (H : expr) : expr := SLTUE (SUBE (SRLW H (ELit 11)) (ELit 0)) (ELit 1).
Definition fe_lt64k (H : expr) : expr := SLTUE (SUBE (SRLW H (ELit 16)) (ELit 0)) (ELit 1).
Definition fe_gt (H : expr) : expr := SLTUE (ELit 16) (SRLW H (ELit 16)).
Definition lit (cells : list kentry) (e : expr) : option bool := if hasr cells e 1 1 then Some true else if hasr cells e 0 0 then Some false else None.
Definition ve_and255 (H : expr) : expr := ANDE H (ELit 255).
Definition ve_cont0 (H : expr) : expr := ANDE (ADD (ANDE H (ELit 63)) (ELit (-128))) (ELit 255).
Definition ve_cont (H : expr) (k : Z) : expr := ANDE (ADD (ANDE (SRLE H (ELit k)) (ELit (-129))) (ELit 128)) (ELit 191).
Definition ve_lead (H : expr) (k m : Z) : expr := ANDE (ADD (ANDE (SRLE H (ELit k)) (ELit (- m - 1))) (ELit m)) (ELit 255).
Inductive region := R1 | R2 | R3 | R4 | RRep | RSurr.
Definition region_eqb (a b : region) : bool := match a, b with R1, R1 | R2, R2 | R3, R3 | R4, R4 | RRep, RRep | RSurr, RSurr => true | _, _ => false end.
Lemma region_eqb_eq : forall a b, region_eqb a b = true -> a = b. Proof. intros [] [] H; try discriminate H; reflexivity. Qed.
Definition klen (r : region) : nat := match r with R1 => 1 | R2 => 2 | R3 => 3 | R4 => 4 | RRep => 3 | RSurr => 0 end%nat.
Definition reg_of (cells : list kentry) (H : expr) : option region :=
  let ls := lit cells (fe_surr H) in let l1 := lit cells (fe_lt128 H) in let l2 := lit cells (fe_lt2k H) in let l3 := lit cells (fe_lt64k H) in let lg := lit cells (fe_gt H) in
  match ls with
  | Some true => Some RSurr
  | Some false =>
      match l1 with
      | Some true => Some R1
      | Some false =>
          match l2 with
          | Some true => Some R2
          | Some false =>
              match l3 with
              | Some true => Some R3
              | Some false => match lg with Some true => Some RRep | Some false => Some R4 | None => None end
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.
(* [comment removed for export] *)
Fixpoint srlw6n (n : nat) (H : expr) : expr := match n with O => H | S n' => SRLW (srlw6n n' H) (ELit 6) end.
Definition ve_leadw (H : expr) (n : nat) (m : Z) : expr := ANDE (ADD (ANDE (srlw6n n H) (ELit (- m - 1))) (ELit m)) (ELit 255).
Definition ve_contw (H : expr) (n : nat) : expr := ANDE (ADD (ANDE (srlw6n n H) (ELit 63)) (ELit (-128))) (ELit 255).
Definition vexp (H : expr) (r : region) (idx : nat) : option expr :=
  match r, idx with
  | R1, 0 => Some (ve_and255 H)
  | R2, 0 => Some (ve_leadw H 1 192) | R2, 1 => Some (ve_contw H 0)
  | R3, 0 => Some (ve_leadw H 2 224) | R3, 1 => Some (ve_contw H 1) | R3, 2 => Some (ve_contw H 0)
  | R4, 0 => Some (ve_leadw H 3 240) | R4, 1 => Some (ve_contw H 2) | R4, 2 => Some (ve_contw H 1) | R4, 3 => Some (ve_contw H 0)
  | RRep, 0 => Some (ELit 239) | RRep, 1 => Some (ELit 191) | RRep, 2 => Some (ELit 189)
  | _, _ => None
  end%nat.
Definition vshape_ok (H : expr) (r : region) (idx : nat) (a1 : expr) : bool := match vexp H r idx with Some e => expr_eqb a1 e | None => false end.
(* [comment removed for export] *)
Definition inreg (x : Z) (r : region) : Prop :=
  match r with
  | RSurr => is_surr x = true
  | R1 => is_surr x = false /\ x < 128
  | R2 => is_surr x = false /\ 128 <= x < 2048
  | R3 => is_surr x = false /\ 2048 <= x < 65536
  | R4 => is_surr x = false /\ 65536 <= x <= 1114111
  | RRep => is_surr x = false /\ 1114111 < x
  end.
Section Sound.
Variable segs : list Segment.
Lemma lit_sound : forall E (M : word -> option byte) cells e b, know_ok segs E M cells -> lit cells e = Some b -> uv E e = (if b then 1 else 0).
Proof.
  intros E M cells e b HK H. unfold lit in H.
  destruct (hasr cells e 1 1) eqn:H1; [injection H as <-; pose proof (has_ok segs E M cells _ HK H1) as T; cbn [kentry_ok] in T; fold (uv E e) in T; lia|].
  destruct (hasr cells e 0 0) eqn:H0; [injection H as <-; pose proof (has_ok segs E M cells _ HK H0) as T; cbn [kentry_ok] in T; fold (uv E e) in T; lia | discriminate H].
Qed.
Lemma is_surr_eq : forall x, is_surr x = ((55296 <=? x) && (x <? 57344))%bool.
Proof. intros x. unfold is_surr. destruct (Z.leb_spec x 57343); destruct (Z.ltb_spec x 57344); try reflexivity; lia. Qed.
Lemma reg_of_sound : forall E (M : word -> option byte) cells H x r, know_ok segs E M cells -> uv E H = UVZ.sx32 x -> 0 <= x < 2 ^ 32 -> reg_of cells H = Some r -> inreg x r.
Proof.
  intros E M cells H x r HK UH Hx HR. unfold reg_of in HR. cbv zeta in HR.
  destruct (lit cells (fe_surr H)) as [[|]|] eqn:ES; [| |discriminate HR];
    pose proof (lit_sound E M cells _ _ HK ES) as LS; unfold fe_surr, SLTUE, SUBE, MULE, SRLE in LS; rewrite (PSBT.f_surr E H x UH Hx), <- is_surr_eq in LS.
  { injection HR as <-. cbn. destruct (is_surr x); [reflexivity | discriminate LS]. }
  assert (NS : is_surr x = false) by (destruct (is_surr x); [discriminate LS | reflexivity]). clear LS ES.
  destruct (lit cells (fe_lt128 H)) as [[|]|] eqn:E1; [| |discriminate HR];
    pose proof (lit_sound E M cells _ _ HK E1) as L1; unfold fe_lt128, SLTUE in L1; rewrite (PSBT.f_lt128 E H x UH Hx) in L1.
  { injection HR as <-. cbn. split; [exact NS|]. destruct (Z.ltb_spec x 128); [lia | discriminate L1]. }
  assert (G1 : 128 <= x) by (destruct (Z.ltb_spec x 128); [discriminate L1 | lia]). clear L1 E1.
  destruct (lit cells (fe_lt2k H)) as [[|]|] eqn:E2; [| |discriminate HR];
    pose proof (lit_sound E M cells _ _ HK E2) as L2; unfold fe_lt2k, SLTUE, SUBE, SRLW in L2; rewrite (PSBT.f_srlw0 E H x UH Hx 11) in L2 by lia; change (2 ^ 11) with 2048 in L2.
  { injection HR as <-. cbn. split; [exact NS|]. destruct (Z.ltb_spec x 2048); [lia | discriminate L2]. }
  assert (G2 : 2048 <= x) by (destruct (Z.ltb_spec x 2048); [discriminate L2 | lia]). clear L2 E2.
  destruct (lit cells (fe_lt64k H)) as [[|]|] eqn:E3; [| |discriminate HR];
    pose proof (lit_sound E M cells _ _ HK E3) as L3; unfold fe_lt64k, SLTUE, SUBE, SRLW in L3; rewrite (PSBT.f_srlw0 E H x UH Hx 16) in L3 by lia; change (2 ^ 16) with 65536 in L3.
  { injection HR as <-. cbn. split; [exact NS|]. destruct (Z.ltb_spec x 65536); [lia | discriminate L3]. }
  assert (G3 : 65536 <= x) by (destruct (Z.ltb_spec x 65536); [discriminate L3 | lia]). clear L3 E3.
  destruct (lit cells (fe_gt H)) as [[|]|] eqn:EG; [| |discriminate HR];
    pose proof (lit_sound E M cells _ _ HK EG) as LG; unfold fe_gt, SLTUE, SRLW in LG; rewrite (PSBT.f_gt E H x UH Hx) in LG.
  { injection HR as <-. cbn. split; [exact NS|]. destruct (Z.ltb_spec 1114111 x); [lia | discriminate LG]. }
  injection HR as <-. cbn. split; [exact NS|]. destruct (Z.ltb_spec 1114111 x); [discriminate LG | lia].
Qed.
Lemma utf8_of_len : forall cp, (length (utf8_of cp) <= 4)%nat.
Proof. intros cp. unfold utf8_of. repeat (destruct (_ : bool); cbn [length]; try lia). Qed.
Lemma shiftr_div : forall x k, 0 <= k -> Z.shiftr x k = x / 2 ^ k.
Proof. intros. apply Z.shiftr_div_pow2. assumption. Qed.
Lemma land63 : forall x, Z.land x 63 = x mod 64.
Proof. intros. change 63 with (2 ^ 6 - 1). rewrite PSBT.land_ones' by lia. reflexivity. Qed.
Lemma klen_len : forall x r, 0 <= x -> inreg x r -> length (utf8_of x) = klen r.
Proof.
  intros x r Hx HR. unfold utf8_of. destruct r; cbn [inreg] in HR;
    [destruct HR as [NS HR] | destruct HR as [NS HR] | destruct HR as [NS HR] | destruct HR as [NS HR] | destruct HR as [NS HR] | rewrite HR; reflexivity]; rewrite NS.
  - destruct (Z.ltb_spec x 128); [reflexivity | lia].
  - destruct (Z.ltb_spec x 128); [lia|]. destruct (Z.ltb_spec x 2048); [reflexivity | lia].
  - destruct (Z.ltb_spec x 128); [lia|]. destruct (Z.ltb_spec x 2048); [lia|]. destruct (Z.ltb_spec x 65536); [reflexivity | lia].
  - destruct (Z.ltb_spec x 128); [lia|]. destruct (Z.ltb_spec x 2048); [lia|]. destruct (Z.ltb_spec x 65536); [lia|]. destruct (Z.leb_spec x 1114111); [reflexivity | lia].
  - destruct (Z.ltb_spec x 128); [lia|]. destruct (Z.ltb_spec x 2048); [lia|]. destruct (Z.ltb_spec x 65536); [lia|]. destruct (Z.leb_spec x 1114111); [lia | reflexivity].
Qed.
(* [comment removed for export] *)
Lemma uv_srlw6n : forall E H x n, uv E H = UVZ.sx32 x -> 0 <= x < 2 ^ 32 ->
  uv E (srlw6n n H) = UVZ.sx32 (x / 64 ^ Z.of_nat n) /\ 0 <= x / 64 ^ Z.of_nat n < 2 ^ 32.
Proof.
  intros E H x n UH Hx. induction n as [|n IH].
  - cbn [srlw6n Z.of_nat]. rewrite Z.pow_0_r, Z.div_1_r. split; [exact UH | exact Hx].
  - destruct IH as [IH1 IH2]. cbn [srlw6n]. unfold SRLW. rewrite (PSBT.uv_srlw_lit E) by lia. rewrite IH1, PSBT.sx32_mod, (Z.mod_small _ _ IH2).
    assert (HP : 0 < 64 ^ Z.of_nat n) by (apply Z.pow_pos_nonneg; lia).
    replace (x / 64 ^ Z.of_nat (S n)) with (x / 64 ^ Z.of_nat n / 2 ^ 6).
    + split; [reflexivity|]. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
    + rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. change (2 ^ 6) with 64. rewrite Z.div_div by lia. f_equal. lia.
Qed.
Lemma v_leadw : forall E X y m j, uv E X = UVZ.sx32 y -> 0 <= y < 2 ^ 32 -> 1 <= j <= 8 -> m = 256 - 2 ^ j ->
  uv E (ANDE (ADD (ANDE X (ELit (- m - 1))) (ELit m)) (ELit 255)) = m + y mod 2 ^ j.
Proof.
  intros E X y m j UX Hy Hj Hm. unfold ANDE, ADD.
  assert (HJ : 2 <= 2 ^ j <= 256) by (split; [change 2 with (2 ^ 1) at 1; apply Z.pow_le_mono_r; dlia | change 256 with (2 ^ 8); apply Z.pow_le_mono_r; dlia]).
  rewrite PSBT.uv_and, PSBT.uv_add, PSBT.uv_and, UX, !PSBT.uv_lit, (Z.mod_small m), (Z.mod_small 255) by dlia.
  set (z := UVZ.sx32 y). pose proof (PSBT.sx32_range y) as Hz. fold z in Hz.
  rewrite (PSBT.land_notmask z m Hz). pose proof (PSBT.lor_bound z m 64 Hz ltac:(dlia)) as Hlor.
  rewrite (Z.mod_small (z - Z.land z m + m)) by (rewrite PSBT.lor_as_sub_add; exact Hlor). change 255 with (2 ^ 8 - 1). rewrite PSBT.land_ones' by dlia. change (2 ^ 8) with 256.
  rewrite (PSBT.land_byte y Hy z m) by dlia.
  assert (ID : forall w, 0 <= w < 256 -> (w - Z.land w m + m) mod 256 = m + w mod 2 ^ j).
  { intros w Hw. subst m.
    assert (A : PSBT.allr 0 256 (fun w => forallb (fun j => ((w - Z.land w (256 - 2 ^ j) + (256 - 2 ^ j)) mod 256 =? (256 - 2 ^ j) + w mod 2 ^ j)) [1; 2; 3; 4; 5; 6; 7; 8]) = true) by (vm_compute; reflexivity).
    pose proof (PSBT.allr_sound 0 256 _ A w Hw) as B. cbv beta in B. rewrite forallb_forall in B.
    assert (Hin : In j [1; 2; 3; 4; 5; 6; 7; 8]) by (cbn; dlia). apply Z.eqb_eq. exact (B j Hin). }
  transitivity (((z mod 256) - Z.land (z mod 256) m + m) mod 256); [dlia|].
  rewrite (ID (z mod 256)) by (apply Z.mod_pos_bound; dlia). f_equal.
  (* [comment removed for export] *)
  transitivity (z mod 2 ^ j); [apply Z.mod_mod_divide; exists (2 ^ (8 - j)); rewrite <- Z.pow_add_r by dlia; replace (8 - j + j) with 8 by dlia; reflexivity|].
  unfold z. pose proof (PSBT.sx32_div_mod y Hy 0 j ltac:(lia) ltac:(lia) ltac:(lia)) as D. rewrite Z.pow_0_r, !Z.div_1_r in D. exact D.
Qed.
Lemma v_contw : forall E X y, uv E X = UVZ.sx32 y -> 0 <= y < 2 ^ 32 -> uv E (ANDE (ADD (ANDE X (ELit 63)) (ELit (-128))) (ELit 255)) = 128 + y mod 64.
Proof. intros E X y UX Hy. unfold ANDE, ADD. exact (PSBT.v_cont0 E X y UX Hy). Qed.
Lemma vexp_sound : forall E H x r (idx : nat) e, uv E H = UVZ.sx32 x -> 0 <= x < 2 ^ 32 -> inreg x r -> vexp H r idx = Some e ->
  uv E e = nth idx (utf8_of x) 0 /\ (idx < length (utf8_of x))%nat.
Proof.
  intros E H x r idx e UH Hx HR HV. rewrite (klen_len x r ltac:(lia) HR).
  pose proof (PSBT.v_and255 E H x UH Hx) as V1.
  pose proof (uv_srlw6n E H x 0 UH Hx) as [S0 R0]. pose proof (uv_srlw6n E H x 1 UH Hx) as [S1 R1']. pose proof (uv_srlw6n E H x 2 UH Hx) as [S2 R2']. pose proof (uv_srlw6n E H x 3 UH Hx) as [S3 R3'].
  change (64 ^ Z.of_nat 0) with 1 in S0, R0. change (64 ^ Z.of_nat 1) with 64 in S1, R1'. change (64 ^ Z.of_nat 2) with 4096 in S2, R2'. change (64 ^ Z.of_nat 3) with 262144 in S3, R3'.
  rewrite Z.div_1_r in S0, R0.
  unfold utf8_of. destruct r; cbn [inreg] in HR; [destruct HR as [NS HR] | destruct HR as [NS HR] | destruct HR as [NS HR] | destruct HR as [NS HR] | destruct HR as [NS HR] |]; try rewrite NS.
  - destruct (Z.ltb_spec x 128); [|lia]. destruct idx as [|idx]; cbn [vexp] in HV; [|discriminate HV]. injection HV as <-. unfold ve_and255, ANDE.
    split; [cbn [nth]; rewrite V1; apply Z.mod_small; lia | cbn; lia].
  - destruct (Z.ltb_spec x 128); [lia|]. destruct (Z.ltb_spec x 2048); [|lia].
    destruct idx as [|[|idx]]; cbn [vexp] in HV; try discriminate HV; injection HV as <-; unfold ve_leadw, ve_contw; cbn [nth length].
    + split; [|cbn; lia]. rewrite (v_leadw E _ _ 192 6 S1 R1' ltac:(lia) eq_refl). rewrite shiftr_div by lia. change (2 ^ 6) with 64. rewrite Z.mod_small; [reflexivity|]. Z.div_mod_to_equations. lia.
    + split; [|cbn; lia]. rewrite (v_contw E _ _ S0 R0), land63. reflexivity.
  - destruct (Z.ltb_spec x 128); [lia|]. destruct (Z.ltb_spec x 2048); [lia|]. destruct (Z.ltb_spec x 65536); [|lia].
    destruct idx as [|[|[|idx]]]; cbn [vexp] in HV; try discriminate HV; injection HV as <-; unfold ve_leadw, ve_contw; cbn [nth length].
    + split; [|cbn; lia]. rewrite (v_leadw E _ _ 224 5 S2 R2' ltac:(lia) eq_refl). rewrite shiftr_div by lia. change (2 ^ 12) with 4096. rewrite Z.mod_small; [reflexivity|]. Z.div_mod_to_equations. lia.
    + split; [|cbn; lia]. rewrite (v_contw E _ _ S1 R1'), shiftr_div, land63 by lia. change (2 ^ 6) with 64. reflexivity.
    + split; [|cbn; lia]. rewrite (v_contw E _ _ S0 R0), land63. reflexivity.
  - destruct (Z.ltb_spec x 128); [lia|]. destruct (Z.ltb_spec x 2048); [lia|]. destruct (Z.ltb_spec x 65536); [lia|]. destruct (Z.leb_spec x 1114111); [|lia].
    destruct idx as [|[|[|[|idx]]]]; cbn [vexp] in HV; try discriminate HV; injection HV as <-; unfold ve_leadw, ve_contw; cbn [nth length].
    + split; [|cbn; lia]. rewrite (v_leadw E _ _ 240 4 S3 R3' ltac:(lia) eq_refl). rewrite shiftr_div by lia. change (2 ^ 18) with 262144. rewrite Z.mod_small; [reflexivity|]. Z.div_mod_to_equations. lia.
    + split; [|cbn; lia]. rewrite (v_contw E _ _ S2 R2'), shiftr_div, land63 by lia. change (2 ^ 12) with 4096. reflexivity.
    + split; [|cbn; lia]. rewrite (v_contw E _ _ S1 R1'), shiftr_div, land63 by lia. change (2 ^ 6) with 64. reflexivity.
    + split; [|cbn; lia]. rewrite (v_contw E _ _ S0 R0), land63. reflexivity.
  - destruct (Z.ltb_spec x 128); [lia|]. destruct (Z.ltb_spec x 2048); [lia|]. destruct (Z.ltb_spec x 65536); [lia|]. destruct (Z.leb_spec x 1114111); [lia|].
    destruct idx as [|[|[|idx]]]; cbn [vexp] in HV; try discriminate HV; injection HV as <-; cbn [nth length]; rewrite PSBT.uv_lit; (split; [reflexivity | cbn; lia]).
  - (* [comment removed for export] *) destruct idx; cbn [vexp] in HV; discriminate HV.
Qed.
(* [comment removed for export] *)
Lemma firstn_S_nth : forall (l : list Z) m, (m < length l)%nat -> firstn (S m) l = firstn m l ++ [nth m l 0].
Proof.
  induction l as [|a r IH]; intros m Hm; [cbn in Hm; lia|]. destruct m as [|m]; [reflexivity|]. cbn [firstn nth app]. cbn in Hm. rewrite (IH m) by lia. reflexivity.
Qed.
Lemma firstn_all_len : forall (l : list Z) m, (length l <= m)%nat -> firstn m l = l.
Proof. intros l m H. apply firstn_all2. exact H. Qed.
(* [comment removed for export] *)
Section Atoms.
Variable E : env.
Lemma uv_sll4r : forall ecp cp, uv E ecp mod 2 ^ 32 = cp -> uv E (EAluw ALU_SLL ecp (ELit 4)) = UVZ.sx32 (cp * 16).
Proof. intros ecp cp Hcp. rewrite PSBT.uv_sllw_lit by dlia. rewrite Hcp. reflexivity. Qed.
Lemma atom_addw1 : forall ecp eb cp b k, uv E ecp mod 2 ^ 32 = cp -> uv E eb = b ->
  uv E (EAluw ALU_ADD (EAlu ALU_ADD eb (EAluw ALU_SLL ecp (ELit 4))) (ELit (- k))) = UVZ.sx32 (PSBT.hexv cp (b - k)).
Proof.
  intros ecp eb cp b k Hcp Hb. rewrite PSBT.uv_addw, PSBT.uv_add, (uv_sll4r ecp cp Hcp), Hb, PSBT.uv_lit, !PSBT.mod32_of_64.
  unfold PSBT.hexv. apply PSBT.sx32_eqm.
  rewrite Z.mod_mod, <- Z.add_mod by dlia. replace (b + UVZ.sx32 (cp * 16) + - k) with (UVZ.sx32 (cp * 16) + (b - k)) by dlia.
  rewrite Z.add_mod, PSBT.sx32_mod, <- Z.add_mod by dlia. reflexivity.
Qed.
Lemma atom_or1 : forall ecp eb cp b, uv E ecp mod 2 ^ 32 = cp -> uv E eb = b -> 0 <= cp -> 48 <= b <= 57 ->
  uv E (EAlu ALU_OR (EAlu ALU_ADD eb (ELit (-48))) (EAluw ALU_SLL ecp (ELit 4))) = UVZ.sx32 (PSBT.hexv cp (b - 48)).
Proof.
  intros ecp eb cp b Hcp Hb Hcp0 Hbr. rewrite PSBT.uv_or, PSBT.uv_add, Hb, PSBT.uv_lit, (uv_sll4r ecp cp Hcp).
  assert (E1 : (b + (-48) mod 2 ^ 64) mod 2 ^ 64 = b + -48) by (rewrite Z.add_mod_idemp_r by dlia; apply Z.mod_small; dlia). rewrite E1.
  assert (HM : (cp * 16) mod 2 ^ 32 = 16 * (cp mod 2 ^ 28)) by (rewrite (Z.mul_comm cp 16); change (2 ^ 32) with (16 * 2 ^ 28); apply Z.mul_mod_distr_l; dlia).
  pose proof (Z.mod_pos_bound cp (2 ^ 28) ltac:(dlia)) as HMr. set (M := cp mod 2 ^ 28) in *.
  assert (H16 : exists q, 0 <= q /\ UVZ.sx32 (cp * 16) = q * 2 ^ 4).
  { unfold UVZ.sx32. rewrite HM. destruct (Z.ltb_spec (16 * M) (2 ^ 31)).
    - exists M. split; [dlia | change (2 ^ 4) with 16; dlia].
    - exists (M + 2 ^ 60 - 2 ^ 28). split; [dlia | change (2 ^ 4) with 16; dlia]. }
  destruct H16 as (q & Hq & Hq16). rewrite Hq16, (PSBT.lor_disjoint' (b + -48) q 4 Hq ltac:(dlia) ltac:(change (2 ^ 4) with 16; dlia)), <- Hq16.
  unfold PSBT.hexv, UVZ.sx32. rewrite Z.mod_mod, Z.add_mod, HM, (Z.mod_small (b - 48)), (Z.mod_small (16 * M + (b - 48))) by dlia.
  destruct (Z.ltb_spec (16 * M) (2 ^ 31)); destruct (Z.ltb_spec (16 * M + (b - 48)) (2 ^ 31)); dlia.
Qed.
(* [comment removed for export] *)
Lemma hexval_digit : forall b, 48 <= b <= 57 -> hexval b = Some (b - 48).
Proof. intros b Hb. unfold hexval, is_digit. destruct (Z.leb_spec 48 b); destruct (Z.leb_spec b 57); cbn [andb]; try lia. reflexivity. Qed.
Lemma hexval_lower : forall b, 97 <= b <= 102 -> hexval b = Some (b - 87).
Proof. intros b Hb. unfold hexval, is_digit. destruct (Z.leb_spec 48 b); destruct (Z.leb_spec b 57); cbn [andb]; try lia. destruct (Z.leb_spec 97 b); destruct (Z.leb_spec b 102); cbn [andb]; try lia. reflexivity. Qed.
Lemma hexval_upper : forall b, 65 <= b <= 70 -> hexval b = Some (b - 55).
Proof.
  intros b Hb. unfold hexval, is_digit. destruct (Z.leb_spec 48 b); destruct (Z.leb_spec b 57); cbn [andb]; try lia.
  destruct (Z.leb_spec 97 b); destruct (Z.leb_spec b 102); cbn [andb]; try lia; destruct (Z.leb_spec 65 b); destruct (Z.leb_spec b 70); cbn [andb]; try lia; reflexivity.
Qed.
Lemma hexval_none : forall b, ~ (48 <= b <= 57 \/ 97 <= b <= 102 \/ 65 <= b <= 70) -> hexval b = None.
Proof.
  intros b Hb. unfold hexval, is_digit. destruct (Z.leb_spec 48 b); destruct (Z.leb_spec b 57); cbn [andb]; try (exfalso; lia);
  destruct (Z.leb_spec 97 b); destruct (Z.leb_spec b 102); cbn [andb]; try (exfalso; lia); destruct (Z.leb_spec 65 b); destruct (Z.leb_spec b 70); cbn [andb]; try (exfalso; lia); reflexivity.
Qed.
End Atoms.
End Sound.
End PCVK.
