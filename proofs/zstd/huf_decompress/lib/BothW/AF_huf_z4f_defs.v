(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image Frame.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require SysStep.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells ABase.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_x2t_hdefs.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Mem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import HufPure_HufX2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require MState.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".

Definition LB (p : Z) (z : Z) : Prop := exists i, 0 <= i <= p /\ Z.testbit z i = true.
Definition LBW (p : Z) (w : word) : Prop := LB p (bv_unsigned w).

Lemma lb_nz : forall p z, LB p z -> z <> 0.
Proof. intros p z (i & Hi & Hb) E. subst z. rewrite Z.bits_0 in Hb. discriminate Hb. Qed.

Lemma lb_mono : forall p q z, LB p z -> p <= q -> LB q z.
Proof. intros p q z (i & Hi & Hb) Hpq. exists i. split; [lia | exact Hb]. Qed.

Lemma lb_shl : forall p s z, LB p z -> 0 <= s -> p + s <= 63 -> LB (p + s) ((z * 2 ^ s) mod 2 ^ 64).
Proof.
  intros p s z (i & Hi & Hb) Hs Hps. exists (i + s). split; [lia|].
  rewrite Z.mod_pow2_bits_low by lia. rewrite Z.mul_pow2_bits by lia.
  replace (i + s - s) with i by lia. exact Hb.
Qed.

Lemma lb_shl_le : forall p s t z, LB p z -> 0 <= t <= s -> p + s <= 63 -> LB (p + s) ((z * 2 ^ t) mod 2 ^ 64).
Proof.
  intros p s t z H Ht Hps. apply (lb_mono (p + t)); [|lia]. apply lb_shl; [exact H | lia | lia].
Qed.

Lemma lbw_nz : forall p (x : word), LBW p x -> bv_unsigned x <> 0.
Proof. intros p x H. exact (lb_nz p _ H). Qed.

Lemma lbw_pos : forall p (x : word), LBW p x -> 1 <= bv_unsigned x < 2 ^ 64.
Proof.
  intros p x H. pose proof (lbw_nz p x H). pose proof (bv_unsigned_in_range 64 x) as R.
  unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2 ^ 64) in R. lia.
Qed.

Lemma lbw_Z : forall p z, 0 <= z < 2 ^ 64 -> LB p z -> LBW p (Z_to_bv 64 z).
Proof. intros p z Hz H. unfold LBW. rewrite KXS.u_small by lia. exact H. Qed.

Lemma lbw_unZ : forall p (x : word), LBW p x -> LB p (bv_unsigned x).
Proof. intros p x H. exact H. Qed.

Lemma lbw_mono : forall p q (x : word), LBW p x -> p <= q -> LBW q x.
Proof. intros p q x H Hpq. exact (lb_mono p q _ H Hpq). Qed.

Lemma lbw_sll : forall p s (x y : word), LBW p x -> bv_unsigned y mod 64 <= s -> p + s <= 63 -> LBW (p + s) (alu64 ALU_SLL x y).
Proof.
  intros p s x y H Hy Hps. unfold LBW. rewrite KXS.u_sll64.
  pose proof (Z.mod_pos_bound (bv_unsigned y) 64 ltac:(lia)) as R.
  apply (lb_shl_le p s (bv_unsigned y mod 64)); [exact H | lia | lia].
Qed.

Lemma lb_or1 : forall z, LB 0 (Z.lor z 1).
Proof.
  intros z. exists 0. split; [lia|]. rewrite Z.lor_spec.
  replace (Z.testbit 1 0) with true by reflexivity. apply Bool.orb_true_r.
Qed.

Lemma lbw_or1 : forall x : word, LBW 0 (alu64 ALU_OR x (Z_to_bv 64 1)).
Proof. intros x. unfold LBW. rewrite KXS.u_or64, KXS.u_small by lia. apply lb_or1. Qed.

Lemma lbw_reload : forall (x y : word), bv_unsigned y mod 64 <= 7 -> LBW 7 (alu64 ALU_SLL (alu64 ALU_OR x (Z_to_bv 64 1)) y).
Proof.
  intros x y Hy. change (LBW 7) with (LBW (0 + 7)). apply lbw_sll; [apply lbw_or1 | exact Hy | lia].
Qed.

Definition EVENW (w : word) : Prop := Z.testbit (bv_unsigned w) 0 = false.

Lemma evenw_add : forall x y : word, EVENW x -> EVENW y -> EVENW (alu64 ALU_ADD x y).
Proof.
  intros x y Hx Hy. unfold EVENW in *. rewrite KXS.u_add64. rewrite Z.mod_pow2_bits_low by lia.
  rewrite Z.add_bit0, Hx, Hy. reflexivity.
Qed.

Lemma evenw_mul_l : forall c (y : word), 0 <= c < 2 ^ 64 -> Z.testbit c 0 = false -> EVENW (mul_div M_MUL (Z_to_bv 64 c) y).
Proof.
  intros c y Hc He. unfold EVENW. rewrite KXS.u_mul64, (KXS.u_small c) by lia. rewrite Z.mod_pow2_bits_low by lia.
  rewrite Z.bit0_eqb in He. apply Z.eqb_neq in He. pose proof (Z.mod_pos_bound c 2 ltac:(lia)) as R.
  replace c with (2 * (c / 2)) by lia. rewrite <- Z.mul_assoc. apply Z.testbit_even_0.
Qed.

Lemma evenw_and_m2 : forall x : word, EVENW (alu64 ALU_AND x (Z_to_bv 64 (-2))).
Proof.
  intros x. unfold EVENW. rewrite KXS.u_and64. rewrite Z.land_spec.
  replace (Z.testbit (bv_unsigned (Z_to_bv 64 (-2))) 0) with false by (vm_compute; reflexivity). apply Bool.andb_false_r.
Qed.

Lemma lbw_add1 : forall x : word, EVENW x -> LBW 0 (alu64 ALU_ADD x (Z_to_bv 64 1)).
Proof.
  intros x Hx. unfold LBW, LB. exists 0. split; [lia|]. rewrite KXS.u_add64, (KXS.u_small 1) by lia.
  rewrite Z.mod_pow2_bits_low by lia. rewrite Z.add_bit0, Hx. reflexivity.
Qed.

Lemma lbw_reload2 : forall (x y : word), EVENW x -> bv_unsigned y mod 64 <= 7 -> LBW 7 (alu64 ALU_SLL (alu64 ALU_ADD x (Z_to_bv 64 1)) y).
Proof.
  intros x y Hx Hy. change (LBW 7) with (LBW (0 + 7)). apply lbw_sll; [apply lbw_add1; exact Hx | exact Hy | lia].
Qed.

Lemma land7_mod64 : forall c : word, bv_unsigned (alu64 ALU_AND c (Z_to_bv 64 7)) mod 64 <= 7.
Proof.
  intros c. rewrite KXS.u_and64, (KXS.u_small 7) by lia.
  pose proof (bv_unsigned_in_range 64 c) as R.
  assert (H : 0 <= Z.land (bv_unsigned c) 7 <= 7)
    by (split; [apply Z.land_nonneg; right; lia | apply KXS.land_le_r; lia]).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma land7z_mod64 : forall c : Z, 0 <= c -> Z.land c 7 mod 64 <= 7.
Proof.
  intros c Hc.
  assert (H : 0 <= Z.land c 7 <= 7) by (split; [apply Z.land_nonneg; right; lia | apply KXS.land_le_r; lia]).
  rewrite Z.mod_small by lia. lia.
Qed.

Ltac kx_erange H e :=
  lazymatch goal with
  | KXK : KXS.know_ok ?segs ?E ?m ?kn |- _ =>
      let r := eval vm_compute in (KX2.erange kn e) in
      lazymatch r with
      | Some (?lo, ?hi) =>
          pose proof (KXS.erange_sound segs E m kn e lo hi KXK ltac:(vm_cast_no_check (@eq_refl (option (Z * Z)) (Some (lo, hi))))) as H
      | None => fail "kx_erange: no interval known for" e
      end
  end.

Ltac e42_amt :=
  cbn [KX2.edenot];
  rewrite ?KXS.u_add64, ?KXS.u_mul64; rewrite ?(KXS.u_small 256) by lia;
  lazymatch goal with
  | |- context [bv_unsigned (KX2.ev ?E ?j)] => idtac
  | |- ?G => fail 1 "e42_amt: unexpected amount" G
  end;
  repeat match goal with H : 0 <= bv_unsigned (KX2.ev _ _) <= _ |- _ => clear H end;
  repeat match goal with
  | |- context [bv_unsigned (KX2.ev ?E ?j)] =>
      lazymatch goal with
      | _ : _ <= bv_unsigned (KX2.ev E j) <= _ |- _ => fail
      | _ => let H := fresh "KXVR" in kx_erange H (KX2.EVar j); cbn [KX2.edenot] in H
      end
  end;
  Z.div_mod_to_equations; lia.

Ltac e42_lb_atom KXA :=
  lazymatch goal with
  | |- LBW ?p (KX2.edenot ?E (KX2.EVar ?a)) =>
      change (LBW p (KX2.ev E a)); rewrite (KXA a) by (cbn [length]; lia); cbn [nth]; rewrite ?OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib.MState.Z_to_bv_bv_unsigned;
      first [ assumption | eapply lbw_mono; [eassumption | lia] | lazymatch goal with |- ?G => fail 1 "e42_lb_atom:" G end ]
  end.

Ltac e42_lb_chain KXA :=
  lazymatch goal with
  | |- LBW ?p (KX2.edenot ?E (KX2.EAlu ALU_SLL ?a ?b)) =>
      change (LBW p (alu64 ALU_SLL (KX2.edenot E a) (KX2.edenot E b)));
      let q := eval vm_compute in (p - 11) in
      change p with (q + 11);
      apply (lbw_sll q 11 (KX2.edenot E a) (KX2.edenot E b)); [e42_lb_chain KXA | e42_amt | lia ]
  | |- LBW ?p (KX2.edenot ?E (KX2.EVar ?a)) => e42_lb_atom KXA
  | |- ?G => fail 1 "e42_lb_chain: unexpected goal" G
  end.

Ltac e42_even :=
  lazymatch goal with
  | |- EVENW (KX2.edenot ?E (KX2.EAlu ALU_ADD ?a ?b)) =>
      change (EVENW (alu64 ALU_ADD (KX2.edenot E a) (KX2.edenot E b))); apply evenw_add; e42_even
  | |- EVENW (KX2.edenot ?E (KX2.EMd M_MUL (KX2.ELit ?c) ?b)) =>
      change (EVENW (mul_div M_MUL (Z_to_bv 64 c) (KX2.edenot E b))); apply evenw_mul_l; [lia | reflexivity]
  | |- EVENW (KX2.edenot ?E (KX2.EAlu ALU_AND ?a (KX2.ELit (-2)))) =>
      change (EVENW (alu64 ALU_AND (KX2.edenot E a) (Z_to_bv 64 (-2)))); apply evenw_and_m2
  | |- ?G => fail 1 "e42_even: unexpected term" G
  end.

Ltac e42_lb_reload :=
  lazymatch goal with
  | |- LBW ?p (KX2.edenot ?E (KX2.EAlu ALU_SLL (KX2.EAlu ALU_ADD ?x (KX2.ELit 1)) ?c)) =>
      change (LBW p (alu64 ALU_SLL (alu64 ALU_ADD (KX2.edenot E x) (Z_to_bv 64 1)) (KX2.edenot E c)));
      apply (lbw_mono 7 p); [|lia]; apply lbw_reload2;
      [ e42_even
      | lazymatch c with
        | KX2.EAlu ALU_AND ?v (KX2.ELit 7) => change (KX2.edenot E c) with (alu64 ALU_AND (KX2.edenot E v) (Z_to_bv 64 7)); apply land7_mod64
        | _ => cbn [KX2.edenot]; rewrite ?KXS.u_and64; rewrite ?(KXS.u_small 7) by lia; Z.div_mod_to_equations; lia
        end ]
  | |- LBW ?p (KX2.edenot ?E (KX2.EAlu ALU_SLL (KX2.EAlu ALU_OR ?x (KX2.ELit 1)) ?c)) =>
      change (LBW p (alu64 ALU_SLL (alu64 ALU_OR (KX2.edenot E x) (Z_to_bv 64 1)) (KX2.edenot E c)));
      apply (lbw_mono 7 p); [|lia]; apply lbw_reload;
      lazymatch c with
      | KX2.EAlu ALU_AND ?v (KX2.ELit 7) => change (KX2.edenot E c) with (alu64 ALU_AND (KX2.edenot E v) (Z_to_bv 64 7)); apply land7_mod64
      | _ => cbn [KX2.edenot]; rewrite ?KXS.u_and64; rewrite ?(KXS.u_small 7) by lia; Z.div_mod_to_equations; lia
      end
  | |- ?G => fail 1 "e42_lb_reload: unexpected term" G
  end.

Definition huf_x2_ok (dtb : list byte) (tl : Z) : Prop :=
  forall i, 0 <= i < 2^tl -> exists b, nth_error dtb (Z.to_nat (4 * i + 7)) = Some b /\ 1 <= bv_unsigned b <= 2.
Definition huf_nb_ok (x2 : bool) (dtb : list byte) (tl : Z) : Prop :=
  forall i, 0 <= i < 2^tl ->
    exists b, nth_error dtb (Z.to_nat (if x2 then 4 * i + 6 else 2 * i + 4)) = Some b /\ bv_unsigned b <= tl.

Definition x42e_ctx (SPV DST dcap SRC n DT DTB tl lo : Z) (src dtb : list byte) : Prop :=
  (4096 <= lo /\ lo <= SPV - 3136) /\ SPV < 2^47 /\ SPV mod 16 = 0 /\ 0x10007fff8000 <= lo /\
  zlen src = n /\ zlen dtb = DTB /\ 1 <= tl <= 12 /\
  (4096 <= DST /\ 0 <= dcap < 2^32 /\ DST + dcap < 2^47) /\ (4096 <= SRC /\ 0 <= n < 2^32 /\ SRC + n < 2^47) /\
  (4096 <= DT /\ DT + DTB < 2^47) /\
  (DST + dcap <= lo \/ SPV <= DST) /\ (SRC + n <= lo \/ SPV <= SRC) /\ (DT + DTB <= lo \/ SPV <= DT) /\
  (DST + dcap <= SRC \/ SRC + n <= DST) /\ (DST + dcap <= DT \/ DT + DTB <= DST) /\
  nth_error dtb 2 = Some (Z_to_bv 8 tl) /\
  (dcap <= 0 \/ (DST + dcap <= 0x7fff7000 \/ 0x10007fff8000 <= DST)) /\ DT mod 4 = 0 /\
  (0 < dcap -> ABase.AIMG_HI <= DST) /\
  4 + 4 * 2 ^ tl <= DTB.
Ltac x42e_ctx_open CTX :=
  destruct CTX as (LO & SPB & SPA & KLO & SL & DL & TL & R1 & R2 & R3 & OS1 & OS2 & OS3 & DJ1 & DJ2 & DT2 & DSTA & DTA & DHI & DTBF).

Definition x42e_actx (RNG : footprint) (m0 : amem) (SPV DST dcap SRC n DT DTB lo : Z) : Prop :=
  unpoisoned m0 SRC (SRC + n) /\ unpoisoned m0 DT (DT + DTB) /\ (0 < dcap -> unpoisoned m0 DST (DST + dcap)) /\
  rng RNG SRC n /\ rng RNG (shad SRC) (shspan SRC n) /\ rng RNG DT DTB /\ rng RNG (shad DT) (shspan DT DTB) /\
  (0 < dcap -> rng RNG DST dcap) /\ (0 < dcap -> rng RNG (shad DST) (shspan DST dcap)) /\
  rng RNG lo (SPV - lo) /\ rng_aimg RNG /\ artcells m0.
Ltac x42e_actx_open ACTX :=
  destruct ACTX as (USRC & UDT & UDST & RSRC & RSRCS & RDT & RDTS & RDST & RDSTS & RSTK & RI & ART).

Lemma z4f_nth_firstn : forall {X} (l : list X) (N k : nat), (k < N)%nat -> nth_error (firstn N l) k = nth_error l k.
Proof.
  intros X l. induction l as [|x l IH]; intros N k H; destruct N as [|N]; try lia; destruct k as [|k]; simpl; try reflexivity.
  all: apply IH; lia.
Qed.

Lemma z4f_first1 : forall {X} (l : list X) (k : nat) b, nth_error l k = Some b -> firstn 1 (skipn k l) = [b].
Proof.
  intros X l. induction l as [|x l IH]; intros k b H; destruct k as [|k]; simpl in *; try discriminate.
  - injection H as ->. reflexivity.
  - apply IH. exact H.
Qed.

Lemma z4_x2tab_fact : forall mm A cells, x2_table_ok cells 11 ->
  bytes_at bsegs mm A (firstn (Z.to_nat (4 * 2^11)) (x2_bytes' cells)) ->
  KXTac.ztab_fact bsegs mm A 8192 4 [(2, 0, 11); (3, 1, 2)].
Proof.
  intros mm A cells (_ & LEN & OK) HB z Hz lo hi HF.
  assert (P11 : 2 ^ 11 = 2048) by reflexivity.
  rewrite P11 in LEN, OK, HB. unfold FseNCount.Zlength in LEN.
  assert (KD : exists v j, z - A = 4 * v + j /\ 0 <= j < 4 /\ 0 <= v < 2048).
  { exists ((z - A) / 4), ((z - A) mod 4).
    split; [apply Z.div_mod; lia|]. split; [apply Z.mod_pos_bound; lia|].
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  destruct KD as (v & j & Ek & Hj & Hv).
  assert (HM : (z - A) mod 4 = j).
  { rewrite Ek, Z.add_comm, Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. lia. }
  rewrite HM in HF.
  assert (LC : (Z.to_nat v < length cells)%nat) by lia.
  pose proof (x2_bytes'_length cells) as BL.
  pose proof (bytes_at_rdn bsegs mm A _ (Z.to_nat (z - A)) 1 HB) as HR.
  rewrite length_firstn in HR. specialize (HR ltac:(lia)).
  replace (A + Z.of_nat (Z.to_nat (z - A))) with z in HR by lia.
  assert (NB : nth_error (firstn (Z.to_nat (4 * 2048)) (x2_bytes' cells)) (Z.to_nat (z - A))
             = nth_error (x2_cellbytes (nth (Z.to_nat v) cells x2_default)) (Z.to_nat j)).
  { rewrite z4f_nth_firstn by lia.
    replace (Z.to_nat (z - A)) with (4 * Z.to_nat v + Z.to_nat j)%nat by lia.
    apply x2_bytes'_nth; lia. }
  pose proof (OK v ltac:(lia)) as CO. unfold x2_cell_ok in CO. destruct CO as (_ & CNB & CLN).
  assert (JC : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by lia.
  destruct JC as [-> | [-> | [-> | ->]]]; cbn in HF; try discriminate HF; injection HF as E1 E2; subst lo hi.
  - assert (B2 : nth_error (x2_cellbytes (nth (Z.to_nat v) cells x2_default)) (Z.to_nat 2)
                 = Some (Z_to_bv 8 (x2_nbBits (nth (Z.to_nat v) cells x2_default)))) by reflexivity.
    rewrite B2 in NB. rewrite (z4f_first1 _ _ _ NB) in HR.
    exists (Z_to_bv 8 (x2_nbBits (nth (Z.to_nat v) cells x2_default))). split; [exact HR|].
    rewrite Z_to_bv_unsigned, bv_wrap_small; [lia|]. unfold bv_modulus. change (2 ^ Z.of_N 8) with 256. lia.
  - assert (B3 : nth_error (x2_cellbytes (nth (Z.to_nat v) cells x2_default)) (Z.to_nat 3)
                 = Some (Z_to_bv 8 (x2_len (nth (Z.to_nat v) cells x2_default)))) by reflexivity.
    rewrite B3 in NB. rewrite (z4f_first1 _ _ _ NB) in HR.
    exists (Z_to_bv 8 (x2_len (nth (Z.to_nat v) cells x2_default))). split; [exact HR|].
    rewrite Z_to_bv_unsigned, bv_wrap_small; [lia|]. unfold bv_modulus. change (2 ^ Z.of_N 8) with 256. lia.
Qed.

Import KXS.

Lemma z4f_shd_ap : forall E X B O k L,
  bv_unsigned (edenot E X) < 2^47 -> 0 <= O -> O + 2^44 <= 2^64 -> 1 <= L <= 8 ->
  0 <= bv_unsigned (edenot E B) + k -> bv_unsigned (edenot E B) + k + L <= 2^64 ->
  bv_unsigned (edenot E B) + k + L <= O \/ O + 2^44 <= bv_unsigned (edenot E B) + k ->
  flat E (SA (EAlu ALU_SRL X (ELit 3)) O) (elenZ E (ELit 1)) /\ flat E (SA B k) (elenZ E (ELit L)) /\
  (estart E (SA (EAlu ALU_SRL X (ELit 3)) O) + elenZ E (ELit 1) <= estart E (SA B k) \/
   estart E (SA B k) + elenZ E (ELit L) <= estart E (SA (EAlu ALU_SRL X (ELit 3)) O)).
Proof.
  intros E X B O k L HX HO1 HO2 HL HB1 HB2 HAP.
  pose proof (bv_unsigned_in_range _ (edenot E X)) as [RX0 _].
  unfold flat, estart, elenZ. cbn [a_base a_off edenot].
  rewrite u_srl64, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  change (3 mod 2 ^ 64) with 3. change (1 mod 2 ^ 64) with 1. change (2 ^ (3 mod 64)) with 8.
  rewrite (Z.mod_small L (2 ^ 64)) by lia.
  assert (HD : bv_unsigned (edenot E X) / 8 < 2^44)
    by (apply Z.div_lt_upper_bound; [lia | change (8 * 2^44) with (2^47); lia]).
  assert (HD0 : 0 <= bv_unsigned (edenot E X) / 8) by (apply Z.div_pos; lia).
  repeat split; lia.
Qed.

Ltac z4fez :=
  repeat lazymatch goal with
  | |- context [edenot ?E _] =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        rewrite ?(ez_ok zv E (kE_atoms zv xs));
        let na := eval vm_compute in (length zv) in
        cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]
      end
  end.

Lemma z4f_div_rng : forall x s, 0 <= x < 2 ^ 64 -> 0 <= s <= 64 -> 0 <= x / 2 ^ s < 2 ^ (64 - s).
Proof.
  intros x s Hx Hs. split.
  - apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia].
  - apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia |].
    rewrite <- Z.pow_add_r by lia. replace (s + (64 - s)) with 64 by lia. lia.
Qed.

Ltac z4fnum :=
  rewrite ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64);
  repeat match goal with |- context [?s mod 64] =>
    lazymatch s with Zpos _ => let v := eval vm_compute in (s mod 64) in change (s mod 64) with v end end;
  repeat match goal with |- context [?a mod 2 ^ 64] =>
    lazymatch a with context [_ mod 2 ^ 64] => fail | context [_ / _] => fail
    | _ => rewrite (Z.mod_small a (2 ^ 64)) by lia end end;
  repeat match goal with |- context [?x / 2 ^ ?s] =>
    lazymatch s with Zpos _ =>
      let H := fresh "DV" in pose proof (z4f_div_rng x s ltac:(lia) ltac:(lia)) as H;
      let e := eval vm_compute in (2 ^ (64 - s)) in change (2 ^ (64 - s)) with e in H;
      let v := fresh "dv" in set (v := x / 2 ^ s) in *; clearbody v end end;
  repeat match goal with |- context [?a mod 2 ^ 64] =>
    lazymatch a with context [_ mod 2 ^ 64] => fail | _ => rewrite (Z.mod_small a (2 ^ 64)) by lia end end.

Ltac z4facc R :=
  lazymatch goal with
  | |- accP _ _ _ =>
      unfold accP, adenot; cbn [a_base a_off fst snd]; unfold PropExec.v_addi; z4fez; z4fnum;
      apply (proj2 (proj2 R)); lia
  end.

Ltac z4fshd :=
  lazymatch goal with
  | |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit ?L)) /\ _ =>
      apply (z4f_shd_ap E X B O k L);
      [ z4fez; z4fnum; first [lia | Z.div_mod_to_equations; lia] | lia | lia | lia
      | z4fez; z4fnum; lia | z4fez; z4fnum; lia | z4fez; z4fnum; lia ]
  end.

Ltac z4fan E :=
  let b := eval unfold E in E in
  lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
    let na := eval vm_compute in (length zv) in
    rewrite ?adenot_wa; change E with (kE zv xs) in *;
    repeat match goal with
    | |- context [estart (kE zv xs) ?a] =>
        rewrite (estart_ez_kE zv xs a); [ | cbv [ez a_base a_off]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]; lia ]
    end;
    rewrite ?(ez_ok zv (kE zv xs) (kE_atoms zv xs));
    cbv [ez a_base a_off]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]
  end.

Ltac z4fsplit n := lazymatch n with O => idtac | S ?n' => split; [| z4fsplit n'] end.

Section CANSEC1. Context {rc : runConstT}.
Section X42E.
  Variables (RNG : footprint).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (SPV DST dcap SRC n DT DTB tl lo : Z) (src dtb : list byte).
  Hypothesis CTX : x42e_ctx SPV DST dcap SRC n DT DTB tl lo src dtb.
  Hypothesis X2OK : huf_x2_ok dtb tl.
  Hypothesis NBOK : huf_nb_ok true dtb tl.
  Hypothesis ACTX : x42e_actx RNG m0 SPV DST dcap SRC n DT DTB lo.

  Variable POST : machine_state -> Prop.
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -528)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation FRS mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 :=
    (rw_cells bsegs mm (SPV + -528) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12;
                                     C8 w13; C8 w14; C8 w15; C8 w16; C8 w17]).
  Notation ARGS mm ip0 ip1 ip2 ip3 op0 op1 op2 op3 b0 b1 b2 b3 adt ilow oend ie0 ie1 ie2 ie3 :=
    (rw_cells bsegs mm (SPV + -384) [C8 ip0; C8 ip1; C8 ip2; C8 ip3; C8 op0; C8 op1; C8 op2; C8 op3; C8 b0; C8 b1; C8 b2; C8 b3;
                                     C8 adt; C8 ilow; C8 oend; C8 ie0; C8 ie1; C8 ie2; C8 ie3]).
  Notation LOC mm e0 e1 e2 e3 p0 p1 p2 p3 i0 i1 i2 i3 c0 c1 c2 c3 :=
    (rw_cells bsegs mm (SPV + -232) [C8 e0; C8 e1; C8 e2; C8 e3; C8 p0; C8 p1; C8 p2; C8 p3; C8 i0; C8 i1; C8 i2; C8 i3;
                                     C8 c0; C8 c1; C8 c2; C8 c3]).
  Notation FRQ mm := (rw_cells bsegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation W0 := [(DST, DST + dcap); (SPV - 3136, SPV)].
  Notation WDF := [(DST, DST + dcap); (SPV - 528, SPV - 104)].
  Notation WD := [(DST, DST + dcap)].
  Notation SB := (Z_to_bv 64 0x7fff8000).
  Hypothesis TL11 : tl = 11.
  Notation WDL := [(DST, DST + dcap); (SPV - 232, SPV - 104)].
  Lemma x42f_idx11 : forall (w : word), 0 <= bv_unsigned w / 9007199254740992 < 2 ^ 11.
  Proof.
    intros w. pose proof (bv_unsigned_in_range 64 w) as HX. unfold bv_modulus in HX. change (2 ^ Z.of_N 64) with (2^64) in HX.
    split; [apply Z.div_pos; lia |]. apply Z.div_lt_upper_bound; [lia|]. change (9007199254740992 * 2 ^ 11) with (2^64). lia.
  Qed.
  Lemma x42f_tab : forall mm, bytes_at bsegs mm DT dtb -> KXTac.ztab_fact bsegs mm (DT + 4) 8192 4 [(2, 0, 11); (3, 1, 2)].
  Proof using CTX X2OK NBOK TL11.
    intros mm HB z Hz lo0 hi0 HF.
    pose proof CTX as CTX'. x42e_ctx_open CTX'.
    assert (P11 : 2 ^ 11 = 2048) by reflexivity. rewrite TL11, P11 in DTBF.
    assert (KD : exists i f, z - (DT + 4) = 4 * i + f /\ 0 <= f < 4 /\ 0 <= i < 2048).
    { exists ((z - (DT + 4)) / 4), ((z - (DT + 4)) mod 4).
      split; [apply Z.div_mod; lia|]. split; [apply Z.mod_pos_bound; lia|].
      split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    destruct KD as (i & f & Ek & Hf & Hi).
    assert (HM : (z - (DT + 4)) mod 4 = f).
    { rewrite Ek, Z.add_comm, Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. lia. }
    rewrite HM in HF.
    pose proof (bytes_at_rdn bsegs mm DT dtb (Z.to_nat (z - DT)) 1 HB) as HR. specialize (HR ltac:(lia)).
    replace (DT + Z.of_nat (Z.to_nat (z - DT))) with z in HR by lia.
    assert (JC : f = 0 \/ f = 1 \/ f = 2 \/ f = 3) by lia.
    destruct JC as [-> | [-> | [-> | ->]]]; cbn in HF; try discriminate HF; injection HF as E1 E2; subst lo0 hi0.
    - destruct (NBOK i) as (b & Hn & Hr); [rewrite TL11, P11; lia|]. cbv beta iota in Hn.
      replace (Z.to_nat (z - DT)) with (Z.to_nat (4 * i + 6)) in HR by (f_equal; lia).
      rewrite (z4f_first1 _ _ _ Hn) in HR. exists b. split; [exact HR|].
      rewrite TL11 in Hr. pose proof (bv_unsigned_in_range 8 b). lia.
    - destruct (X2OK i) as (b & Hn & Hr); [rewrite TL11, P11; lia|].
      replace (Z.to_nat (z - DT)) with (Z.to_nat (4 * i + 7)) in HR by (f_equal; lia).
      rewrite (z4f_first1 _ _ _ Hn) in HR. exists b. split; [exact HR | exact Hr].
  Qed.
  Lemma x42f_unp : forall mm, munch W0 m0 mm ->
    unpoisoned mm SRC (SRC + n) /\ unpoisoned mm DT (DT + DTB) /\ (0 < dcap -> unpoisoned mm DST (DST + dcap)).
  Proof using CTX ACTX.
    intros mm MU.
    pose proof CTX as CTX'. x42e_ctx_open CTX'. pose proof ACTX as ACTX'. x42e_actx_open ACTX'.
    assert (MUS : munch [(SPV - 3136, SPV)] m0 mm \/ 0 < dcap).
    { destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd]; [right; exact Hd | left].
      eapply munch_weaken; [|exact MU]. intros x Hx. cbn [outside] in *. destruct Hx as [Hx _].
      split; [lia | split; [exact Hx | exact I]]. }
    split; [|split].
    - destruct MUS as [MUS|Hd]; (eapply unpoisoned_munch; [exact USRC | first [exact MUS | exact MU] |]);
        cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF; repeat split; Z.div_mod_to_equations; lia.
    - destruct MUS as [MUS|Hd]; (eapply unpoisoned_munch; [exact UDT | first [exact MUS | exact MU] |]);
        cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF; repeat split; Z.div_mod_to_equations; lia.
    - intros Hd. eapply unpoisoned_munch; [exact (UDST Hd) | exact MU |].
      cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; Z.div_mod_to_equations; lia.
  Qed.

  Definition z4fI (mb mm : amem) (fr ar cs : list cell) : Prop :=
    munch [(DST, DST + dcap); (SPV - 232, SPV - 104)] mb mm /\ wmono bsegs mb mm /\
    munch [(DST, DST + dcap); (SPV - 3136, SPV)] m0 mm /\ wmono bsegs m0 mm /\ mem_inv bsegs mm /\
    stk bsegs mm DST (DST + dcap) /\ bytes_at bsegs mm DT dtb /\ bytes_at bsegs mm SRC src /\
    rw_cells bsegs mm (SPV + -528) fr /\ rw_cells bsegs mm (SPV + -384) ar /\ rw_cells bsegs mm (SPV + -232) cs /\
    Z.of_nat (cells_size fr) = 144 /\ Z.of_nat (cells_size ar) = 152.

  Lemma z4fI_wr8 : forall mb mm fr ar cs (k : nat) w0 v a,
    z4fI mb mm fr ar cs -> cell_at cs k = Some (C8 w0) -> (k + 8 <= 128)%nat -> a = SPV + -232 + Z.of_nat k ->
    z4fI mb (CatExec.wbytes mm (wa a) (word_to_le_bytes 8 v)) fr ar (cell_upd cs k (C8 v)).
  Proof using CTX.
    intros mb mm fr ar cs k w0 v a I CK KR AE.
    pose proof CTX as CTX'. x42e_ctx_open CTX'.
    destruct I as (MU & WM & MU0 & WM0 & MI & STK & DTB0 & SRC0 & FR & AR & LC & LFR & LAR).
    assert (L8 : length (word_to_le_bytes 8 v) = 8%nat) by reflexivity.
    rewrite wbytes_eq. subst a.
    assert (K8 : 0 <= Z.of_nat k <= 120) by lia.
    unfold z4fI. z4fsplit 12%nat.
    - apply munch_write; [exact MU | lia | rewrite L8; lia | rewrite L8; cbn [inside]; lia].
    - apply wmono_write; exact WM.
    - apply munch_write; [exact MU0 | lia | rewrite L8; lia | rewrite L8; cbn [inside]; lia].
    - apply wmono_write; exact WM0.
    - change (word_to_le_bytes 8 v) with (cbytes (C8 v)).
      apply mem_inv_store_cbytes; [exact MI | exact I | eapply rw_cells_store_ok; [exact LC | exact CK | reflexivity]].
    - apply stk_write; [exact STK | lia | rewrite L8; lia].
    - apply bytes_at_write_other; [exact DTB0 | lia | rewrite L8; lia | rewrite L8; lia].
    - apply bytes_at_write_other; [exact SRC0 | lia | rewrite L8; lia | rewrite L8; lia].
    - apply rw_cells_frame; [exact FR | lia | rewrite L8; lia | rewrite L8; lia].
    - apply rw_cells_frame; [exact AR | lia | rewrite L8; lia | rewrite L8; lia].
    - change (word_to_le_bytes 8 v) with (cbytes (C8 v)).
      eapply rw_cells_write; [exact LC | exact CK | reflexivity | exact I].
    - exact LFR.
    - exact LAR.
  Qed.

  Lemma z4fI_wr1 : forall mb mm fr ar cs v a,
    z4fI mb mm fr ar cs -> Z.of_nat (cells_size cs) = 128 -> DST <= a -> a + 1 <= DST + dcap ->
    z4fI mb (CatExec.wbytes mm (wa a) (word_to_le_bytes 1 v)) fr ar cs.
  Proof using CTX.
    intros mb mm fr ar cs v a I LLC A0 A1.
    pose proof CTX as CTX'. x42e_ctx_open CTX'.
    destruct I as (MU & WM & MU0 & WM0 & MI & STK & DTB0 & SRC0 & FR & AR & LC & LFR & LAR).
    assert (L1 : length (word_to_le_bytes 1 v) = 1%nat) by reflexivity.
    rewrite wbytes_eq.
    unfold z4fI. z4fsplit 12%nat.
    - apply munch_write; [exact MU | lia | rewrite L1; lia | rewrite L1; cbn [inside]; lia].
    - apply wmono_write; exact WM.
    - apply munch_write; [exact MU0 | lia | rewrite L1; lia | rewrite L1; cbn [inside]; lia].
    - apply wmono_write; exact WM0.
    - apply mem_inv_store; [exact MI | rewrite L1].
      apply store_ok_of_wview; [lia | lia |]. intros j Hj.
      destruct STK as (S0 & S1 & S2). apply (S2 (a + j)). lia.
    - apply stk_write; [exact STK | lia | rewrite L1; lia].
    - apply bytes_at_write_other; [exact DTB0 | lia | rewrite L1; lia | rewrite L1; lia].
    - apply bytes_at_write_other; [exact SRC0 | lia | rewrite L1; lia | rewrite L1; lia].
    - apply rw_cells_frame; [exact FR | lia | rewrite L1; lia | rewrite L1; lia].
    - apply rw_cells_frame; [exact AR | lia | rewrite L1; lia | rewrite L1; lia].
    - apply rw_cells_frame; [exact LC | lia | rewrite L1; lia | rewrite L1; lia].
    - exact LFR.
    - exact LAR.
  Qed.

  Lemma z4fI_wr8c : forall mb mm fr ar cs cs' (k : nat) w0 v a,
    z4fI mb mm fr ar cs -> cell_at cs k = Some (C8 w0) -> (k + 8 <= 128)%nat -> a = SPV + -232 + Z.of_nat k ->
    cs' = cell_upd cs k (C8 v) ->
    z4fI mb (CatExec.wbytes mm (wa a) (word_to_le_bytes 8 v)) fr ar cs'.
  Proof using CTX. intros until a. intros I CK KR AE ->. exact (z4fI_wr8 _ _ _ _ _ _ _ _ _ I CK KR AE). Qed.

  Notation KHI r mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 :=
    (forall mm' i0' i1' i2' i3' o0' o1' o2' o3' (c0' c1' c2' c3' : word) (y1 y5 y6 y16 y17 y18 y19 y25 : word) (w'0 w'1 w'2 : word),
        munch WDL mb mm' -> wmono bsegs mb mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb ->
        (FRS mm' w'0 w'1 w'2 (Z_to_bv 64 (SRC)) (Z_to_bv 64 (n)) (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + 3 * q)) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (66420))) ->
        (ARGS mm' av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
        (LOC mm' e0 e1 e2 e3 (Z_to_bv 64 (DST + o0')) (Z_to_bv 64 (DST + o1')) (Z_to_bv 64 (DST + o2')) (Z_to_bv 64 (DST + o3')) (Z_to_bv 64 (SRC + i0')) (Z_to_bv 64 (SRC + i1')) (Z_to_bv 64 (SRC + i2')) (Z_to_bv 64 (SRC + i3')) c0' c1' c2' c3') -> bytes_at bsegs mm' SRC src ->
        i0 - 7 <= i0' <= i0 -> i1 - 7 <= i1' <= i1 -> i2 - 7 <= i2' <= i2 -> i3 - 7 <= i3' <= i3 ->
        o0 + 5 <= o0' <= o0 + 10 -> o1 + 5 <= o1' <= o1 + 10 -> o2 + 5 <= o2' <= o2 + 10 -> o3 + 5 <= o3' <= o3 + 10 ->
        LBW 8 c0' -> LBW 8 c1' -> LBW 8 c2' -> LBW 8 c3' -> o3' < OL -> (2 <= r)%nat ->
        evtF bsegs RNG POST (ST 0x853d4 mm' y1 y5 y6 (Z_to_bv 64 (SRC + i2')) (Z_to_bv 64 (18446744073709551600)) (Z_to_bv 64 (SPV + -136)) (Z_to_bv 64 (nd)) c0' (Z_to_bv 64 (DST + o3')) (Z_to_bv 64 (DST + o0')) (Z_to_bv 64 (DST + o2')) (Z_to_bv 64 (DST + o1')) y16 y17 y18 y19 c3' (Z_to_bv 64 (SPV + -168)) c1' SB c2' y25 (Z_to_bv 64 (134483)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + OL)) (Z_to_bv 64 (SRC + i3')) (Z_to_bv 64 (SRC + i1')) (Z_to_bv 64 (SRC + i0')))).
  Notation KOI r mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 :=
    (forall mm' i0' i1' i2' i3' o0' o1' o2' o3' (c0' c1' c2' c3' : word) (y1 y7 y18 y19 y20 y22 y24 y25 y28 y29 y30 y31 : word) (w'0 w'1 w'2 : word),
        munch WDL mb mm' -> wmono bsegs mb mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb ->
        (FRS mm' w'0 w'1 w'2 (Z_to_bv 64 (SRC)) (Z_to_bv 64 (n)) (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + 3 * q)) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (66420))) ->
        (ARGS mm' av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
        (LOC mm' e0 e1 e2 e3 (Z_to_bv 64 (DST + o0')) (Z_to_bv 64 (DST + o1')) (Z_to_bv 64 (DST + o2')) (Z_to_bv 64 (DST + o3')) (Z_to_bv 64 (SRC + i0')) (Z_to_bv 64 (SRC + i1')) (Z_to_bv 64 (SRC + i2')) (Z_to_bv 64 (SRC + i3')) c0' c1' c2' c3') -> bytes_at bsegs mm' SRC src ->
        i0 - 7 <= i0' <= i0 -> i1 - 7 <= i1' <= i1 -> i2 - 7 <= i2' <= i2 -> i3 - 7 <= i3' <= i3 ->
        o0 + 5 <= o0' <= o0 + 10 -> o1 + 5 <= o1' <= o1 + 10 -> o2 + 5 <= o2' <= o2 + 10 -> o3 + 5 <= o3' <= o3 + 10 ->
        LBW 8 c0' -> LBW 8 c1' -> LBW 8 c2' -> LBW 8 c3' -> OL <= o3' ->
        evtF bsegs RNG POST (ST 0x85278 mm' y1 (Z_to_bv 64 (SRC + i2')) (Z_to_bv 64 (SRC + i3')) y7 (Z_to_bv 64 (18446744073709551600)) (Z_to_bv 64 (SPV + -136)) (Z_to_bv 64 (nd)) c0' (Z_to_bv 64 (DST + o3')) (Z_to_bv 64 (DST + o0')) (Z_to_bv 64 (DST + o2')) (Z_to_bv 64 (DST + o1')) (Z_to_bv 64 (SRC + i0')) (Z_to_bv 64 (SRC + i1')) y18 y19 y20 (Z_to_bv 64 (SPV + -168)) y22 SB y24 y25 (Z_to_bv 64 (134483)) (Z_to_bv 64 (DT + 4)) y28 y29 y30 y31)).

  Definition x42e_fi0_stmt : Prop := forall (r : nat) mb mm q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 (c0 c1 c2 c3 : word) (e0 e1 e2 e3 : word) (av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 : word)
      (x1 x5 x6 x16 x17 x18 x19 x25 : word)
      (w0 w1 w2 : word),
    munch WDL mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    (FRS mm w0 w1 w2 (Z_to_bv 64 (SRC)) (Z_to_bv 64 (n)) (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + 3 * q)) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (66420))) ->
    (ARGS mm av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
    (LOC mm e0 e1 e2 e3 (Z_to_bv 64 (DST + o0)) (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (DST + o3)) (Z_to_bv 64 (SRC + i0)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i3)) c0 c1 c2 c3) ->
    bytes_at bsegs mm SRC src -> nd = -1 * DT + -5 ->
    (1 <= r)%nat -> OL - o3 <= 5 * Z.of_nat r -> 0 <= o0 -> 0 <= o1 -> 0 <= o2 -> 0 <= o3 ->
    o0 + 10 * Z.of_nat r <= q -> o1 + 10 * Z.of_nat r <= 2 * q -> o2 + 10 * Z.of_nat r <= 3 * q -> o3 + 10 * Z.of_nat r <= dcap ->
    3 * q <= dcap -> 0 <= q -> 0 <= OL <= dcap ->
    7 * Z.of_nat r <= i0 -> 7 * Z.of_nat r <= i1 -> 7 * Z.of_nat r <= i2 -> 7 * Z.of_nat r <= i3 ->
    i0 + 8 <= n -> i1 + 8 <= n -> i2 + 8 <= n -> i3 + 8 <= n -> 8 <= l1 -> 8 <= l2 -> 8 <= l3 -> 6 + l1 + l2 + l3 + 8 <= n ->
    LBW 8 c0 ->
    LBW 8 c1 ->
    LBW 8 c2 ->
    LBW 8 c3 ->
    KHI r mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 ->
    KOI r mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 ->
    evtF bsegs RNG POST (ST 0x853d4 mm x1 x5 x6 (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (18446744073709551600)) (Z_to_bv 64 (SPV + -136)) (Z_to_bv 64 (nd)) c0 (Z_to_bv 64 (DST + o3)) (Z_to_bv 64 (DST + o0)) (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (DST + o1)) x16 x17 x18 x19 c3 (Z_to_bv 64 (SPV + -168)) c1 SB c2 x25 (Z_to_bv 64 (134483)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + OL)) (Z_to_bv 64 (SRC + i3)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i0))).

  Definition x42e_fi1_stmt : Prop := forall (r : nat) mb mm q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 u0 u1 (c0 c1 c2 c3 : word) (e0 e1 e2 e3 : word) (av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 : word)
      (x1 x6 x16 x17 x18 x19 x22 x25 : word)
      (w0 w1 w2 : word),
    munch WDL mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    (FRS mm w0 w1 w2 (Z_to_bv 64 (SRC)) (Z_to_bv 64 (n)) (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + 3 * q)) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (66420))) ->
    (ARGS mm av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
    (LOC mm e0 e1 e2 e3 (Z_to_bv 64 (DST + u0)) (Z_to_bv 64 (DST + u1)) (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (DST + o3)) (Z_to_bv 64 (SRC + i0)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i3)) c0 c1 c2 c3) ->
    bytes_at bsegs mm SRC src -> nd = -1 * DT + -5 ->
    (1 <= r)%nat -> OL - o3 <= 5 * Z.of_nat r -> 0 <= o0 -> 0 <= o1 -> 0 <= o2 -> 0 <= o3 ->
    o0 + 10 * Z.of_nat r <= q -> o1 + 10 * Z.of_nat r <= 2 * q -> o2 + 10 * Z.of_nat r <= 3 * q -> o3 + 10 * Z.of_nat r <= dcap ->
    3 * q <= dcap -> 0 <= q -> 0 <= OL <= dcap ->
    7 * Z.of_nat r <= i0 -> 7 * Z.of_nat r <= i1 -> 7 * Z.of_nat r <= i2 -> 7 * Z.of_nat r <= i3 ->
    i0 + 8 <= n -> i1 + 8 <= n -> i2 + 8 <= n -> i3 + 8 <= n -> 8 <= l1 -> 8 <= l2 -> 8 <= l3 -> 6 + l1 + l2 + l3 + 8 <= n ->
    o0 + 1 <= u0 <= o0 + 2 ->
    o1 + 1 <= u1 <= o1 + 2 ->
    LBW 19 c0 ->
    LBW 19 c1 ->
    LBW 8 c2 ->
    LBW 8 c3 ->
    KHI r mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 ->
    KOI r mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 ->
    evtF bsegs RNG POST (ST 0x85580 mm x1 c1 x6 (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (18446744073709551600)) (Z_to_bv 64 (SPV + -136)) (Z_to_bv 64 (nd)) c0 (Z_to_bv 64 (DST + o3)) (Z_to_bv 64 (DST + u0)) (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (DST + u1)) x16 x17 x18 x19 c3 (Z_to_bv 64 (SPV + -168)) x22 SB c2 x25 (Z_to_bv 64 (134483)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + OL)) (Z_to_bv 64 (SRC + i3)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i0))).

  Definition x42e_fi2_stmt : Prop := forall (r : nat) mb mm q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 u0 u1 u2 ix (c0 c1 c2 c3 : word) (e0 e1 e2 e3 : word) (av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 : word)
      (x1 x17 x18 x19 x22 x24 x25 : word)
      (w0 w1 w2 : word),
    munch WDL mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    (FRS mm w0 w1 w2 (Z_to_bv 64 (SRC)) (Z_to_bv 64 (n)) (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + 3 * q)) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (66420))) ->
    (ARGS mm av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
    (LOC mm e0 e1 e2 e3 (Z_to_bv 64 (DST + u0)) (Z_to_bv 64 (DST + u1)) (Z_to_bv 64 (DST + u2)) (Z_to_bv 64 (DST + o3)) (Z_to_bv 64 (SRC + i0)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i3)) c0 c1 c2 c3) ->
    bytes_at bsegs mm SRC src -> nd = -1 * DT + -5 ->
    (1 <= r)%nat -> OL - o3 <= 5 * Z.of_nat r -> 0 <= o0 -> 0 <= o1 -> 0 <= o2 -> 0 <= o3 ->
    o0 + 10 * Z.of_nat r <= q -> o1 + 10 * Z.of_nat r <= 2 * q -> o2 + 10 * Z.of_nat r <= 3 * q -> o3 + 10 * Z.of_nat r <= dcap ->
    3 * q <= dcap -> 0 <= q -> 0 <= OL <= dcap ->
    7 * Z.of_nat r <= i0 -> 7 * Z.of_nat r <= i1 -> 7 * Z.of_nat r <= i2 -> 7 * Z.of_nat r <= i3 ->
    i0 + 8 <= n -> i1 + 8 <= n -> i2 + 8 <= n -> i3 + 8 <= n -> 8 <= l1 -> 8 <= l2 -> 8 <= l3 -> 6 + l1 + l2 + l3 + 8 <= n ->
    o0 + 2 <= u0 <= o0 + 4 ->
    o1 + 1 <= u1 <= o1 + 2 ->
    o2 + 1 <= u2 <= o2 + 2 ->
    0 <= ix <= 2047 ->
    LBW 30 c0 ->
    LBW 19 c1 ->
    LBW 19 c2 ->
    LBW 8 c3 ->
    KHI r mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 ->
    KOI r mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 ->
    evtF bsegs RNG POST (ST 0x8572c mm x1 c1 c2 (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (18446744073709551600)) (Z_to_bv 64 (SPV + -136)) (Z_to_bv 64 (nd)) c0 (Z_to_bv 64 (DST + o3)) (Z_to_bv 64 (DST + u0)) (Z_to_bv 64 (DST + u2)) (Z_to_bv 64 (DST + u1)) (Z_to_bv 64 (4 * ix)) x17 x18 x19 c3 (Z_to_bv 64 (SPV + -168)) x22 SB x24 x25 (Z_to_bv 64 (134483)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + OL)) (Z_to_bv 64 (SRC + i3)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i0))).

  Definition x42e_fi3_stmt : Prop := forall (r : nat) mb mm q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 u0 u1 u2 ix (c0 c1 c2 c3 : word) (e0 e1 e2 e3 : word) (av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 : word)
      (x1 x17 x18 x19 x22 x24 x25 : word)
      (w0 w1 w2 : word),
    munch WDL mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    (FRS mm w0 w1 w2 (Z_to_bv 64 (SRC)) (Z_to_bv 64 (n)) (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + 3 * q)) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (66420))) ->
    (ARGS mm av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
    (LOC mm e0 e1 e2 e3 (Z_to_bv 64 (DST + u0)) (Z_to_bv 64 (DST + u1)) (Z_to_bv 64 (DST + u2)) (Z_to_bv 64 (DST + o3)) (Z_to_bv 64 (SRC + i0)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i3)) c0 c1 c2 c3) ->
    bytes_at bsegs mm SRC src -> nd = -1 * DT + -5 ->
    (1 <= r)%nat -> OL - o3 <= 5 * Z.of_nat r -> 0 <= o0 -> 0 <= o1 -> 0 <= o2 -> 0 <= o3 ->
    o0 + 10 * Z.of_nat r <= q -> o1 + 10 * Z.of_nat r <= 2 * q -> o2 + 10 * Z.of_nat r <= 3 * q -> o3 + 10 * Z.of_nat r <= dcap ->
    3 * q <= dcap -> 0 <= q -> 0 <= OL <= dcap ->
    7 * Z.of_nat r <= i0 -> 7 * Z.of_nat r <= i1 -> 7 * Z.of_nat r <= i2 -> 7 * Z.of_nat r <= i3 ->
    i0 + 8 <= n -> i1 + 8 <= n -> i2 + 8 <= n -> i3 + 8 <= n -> 8 <= l1 -> 8 <= l2 -> 8 <= l3 -> 6 + l1 + l2 + l3 + 8 <= n ->
    o0 + 2 <= u0 <= o0 + 4 ->
    o1 + 2 <= u1 <= o1 + 4 ->
    o2 + 2 <= u2 <= o2 + 4 ->
    0 <= ix <= 2047 ->
    LBW 30 c0 ->
    LBW 30 c1 ->
    LBW 30 c2 ->
    LBW 8 c3 ->
    KHI r mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 ->
    KOI r mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 ->
    evtF bsegs RNG POST (ST 0x858a4 mm x1 c1 c2 (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (18446744073709551600)) (Z_to_bv 64 (SPV + -136)) (Z_to_bv 64 (nd)) c0 (Z_to_bv 64 (DST + o3)) (Z_to_bv 64 (DST + u0)) (Z_to_bv 64 (DST + u2)) (Z_to_bv 64 (DST + u1)) (Z_to_bv 64 (4 * ix)) x17 x18 x19 c3 (Z_to_bv 64 (SPV + -168)) x22 SB x24 x25 (Z_to_bv 64 (134483)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + OL)) (Z_to_bv 64 (SRC + i3)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i0))).

  Definition x42e_fi4_stmt : Prop := forall (r : nat) mb mm q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 u0 u1 u2 ix (c0 c1 c2 c3 : word) (e0 e1 e2 e3 : word) (av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 : word)
      (x1 x17 x18 x19 x22 x24 x25 : word)
      (w0 w1 w2 : word),
    munch WDL mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    (FRS mm w0 w1 w2 (Z_to_bv 64 (SRC)) (Z_to_bv 64 (n)) (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + 3 * q)) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (66420))) ->
    (ARGS mm av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
    (LOC mm e0 e1 e2 e3 (Z_to_bv 64 (DST + u0)) (Z_to_bv 64 (DST + u1)) (Z_to_bv 64 (DST + u2)) (Z_to_bv 64 (DST + o3)) (Z_to_bv 64 (SRC + i0)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i3)) c0 c1 c2 c3) ->
    bytes_at bsegs mm SRC src -> nd = -1 * DT + -5 ->
    (1 <= r)%nat -> OL - o3 <= 5 * Z.of_nat r -> 0 <= o0 -> 0 <= o1 -> 0 <= o2 -> 0 <= o3 ->
    o0 + 10 * Z.of_nat r <= q -> o1 + 10 * Z.of_nat r <= 2 * q -> o2 + 10 * Z.of_nat r <= 3 * q -> o3 + 10 * Z.of_nat r <= dcap ->
    3 * q <= dcap -> 0 <= q -> 0 <= OL <= dcap ->
    7 * Z.of_nat r <= i0 -> 7 * Z.of_nat r <= i1 -> 7 * Z.of_nat r <= i2 -> 7 * Z.of_nat r <= i3 ->
    i0 + 8 <= n -> i1 + 8 <= n -> i2 + 8 <= n -> i3 + 8 <= n -> 8 <= l1 -> 8 <= l2 -> 8 <= l3 -> 6 + l1 + l2 + l3 + 8 <= n ->
    o0 + 3 <= u0 <= o0 + 6 ->
    o1 + 3 <= u1 <= o1 + 6 ->
    o2 + 2 <= u2 <= o2 + 4 ->
    0 <= ix <= 2047 ->
    LBW 41 c0 ->
    LBW 41 c1 ->
    LBW 30 c2 ->
    LBW 8 c3 ->
    KHI r mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 ->
    KOI r mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 ->
    evtF bsegs RNG POST (ST 0x85a0c mm x1 c1 c2 (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (18446744073709551600)) (Z_to_bv 64 (SPV + -136)) (Z_to_bv 64 (nd)) c0 (Z_to_bv 64 (DST + o3)) (Z_to_bv 64 (DST + u0)) (Z_to_bv 64 (DST + u2)) (Z_to_bv 64 (DST + u1)) (Z_to_bv 64 (4 * ix)) x17 x18 x19 c3 (Z_to_bv 64 (SPV + -168)) x22 SB x24 x25 (Z_to_bv 64 (134483)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + OL)) (Z_to_bv 64 (SRC + i3)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i0))).

  Definition x42e_fi5_stmt : Prop := forall (r : nat) mb mm q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 u0 u1 u2 ix (c0 c1 c2 c3 : word) (e0 e1 e2 e3 : word) (av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 : word)
      (x1 x17 x18 x19 x22 x24 x25 : word)
      (w0 w1 w2 : word),
    munch WDL mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    (FRS mm w0 w1 w2 (Z_to_bv 64 (SRC)) (Z_to_bv 64 (n)) (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + 3 * q)) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (66420))) ->
    (ARGS mm av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
    (LOC mm e0 e1 e2 e3 (Z_to_bv 64 (DST + u0)) (Z_to_bv 64 (DST + u1)) (Z_to_bv 64 (DST + u2)) (Z_to_bv 64 (DST + o3)) (Z_to_bv 64 (SRC + i0)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i3)) c0 c1 c2 c3) ->
    bytes_at bsegs mm SRC src -> nd = -1 * DT + -5 ->
    (1 <= r)%nat -> OL - o3 <= 5 * Z.of_nat r -> 0 <= o0 -> 0 <= o1 -> 0 <= o2 -> 0 <= o3 ->
    o0 + 10 * Z.of_nat r <= q -> o1 + 10 * Z.of_nat r <= 2 * q -> o2 + 10 * Z.of_nat r <= 3 * q -> o3 + 10 * Z.of_nat r <= dcap ->
    3 * q <= dcap -> 0 <= q -> 0 <= OL <= dcap ->
    7 * Z.of_nat r <= i0 -> 7 * Z.of_nat r <= i1 -> 7 * Z.of_nat r <= i2 -> 7 * Z.of_nat r <= i3 ->
    i0 + 8 <= n -> i1 + 8 <= n -> i2 + 8 <= n -> i3 + 8 <= n -> 8 <= l1 -> 8 <= l2 -> 8 <= l3 -> 6 + l1 + l2 + l3 + 8 <= n ->
    o0 + 4 <= u0 <= o0 + 8 ->
    o1 + 3 <= u1 <= o1 + 6 ->
    o2 + 3 <= u2 <= o2 + 6 ->
    0 <= ix <= 2047 ->
    LBW 52 c0 ->
    LBW 41 c1 ->
    LBW 41 c2 ->
    LBW 8 c3 ->
    KHI r mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 ->
    KOI r mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 ->
    evtF bsegs RNG POST (ST 0x85b74 mm x1 c1 c2 (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (18446744073709551600)) (Z_to_bv 64 (SPV + -136)) (Z_to_bv 64 (nd)) c0 (Z_to_bv 64 (DST + o3)) (Z_to_bv 64 (DST + u0)) (Z_to_bv 64 (DST + u2)) (Z_to_bv 64 (DST + u1)) (Z_to_bv 64 (4 * ix)) x17 x18 x19 c3 (Z_to_bv 64 (SPV + -168)) x22 SB x24 x25 (Z_to_bv 64 (134483)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + OL)) (Z_to_bv 64 (SRC + i3)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i0))).

  Definition x42e_fi6_stmt : Prop := forall (r : nat) mb mm q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 u0 u1 u2 ix (c0 c1 c2 c3 : word) (e0 e1 e2 e3 : word) (av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 : word)
      (x1 x6 x17 x18 x19 x24 x25 : word)
      (w0 w1 w2 : word),
    munch WDL mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    (FRS mm w0 w1 w2 (Z_to_bv 64 (SRC)) (Z_to_bv 64 (n)) (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + 3 * q)) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (66420))) ->
    (ARGS mm av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
    (LOC mm e0 e1 e2 e3 (Z_to_bv 64 (DST + u0)) (Z_to_bv 64 (DST + u1)) (Z_to_bv 64 (DST + u2)) (Z_to_bv 64 (DST + o3)) (Z_to_bv 64 (SRC + i0)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i3)) c0 c1 c2 c3) ->
    bytes_at bsegs mm SRC src -> nd = -1 * DT + -5 ->
    (1 <= r)%nat -> OL - o3 <= 5 * Z.of_nat r -> 0 <= o0 -> 0 <= o1 -> 0 <= o2 -> 0 <= o3 ->
    o0 + 10 * Z.of_nat r <= q -> o1 + 10 * Z.of_nat r <= 2 * q -> o2 + 10 * Z.of_nat r <= 3 * q -> o3 + 10 * Z.of_nat r <= dcap ->
    3 * q <= dcap -> 0 <= q -> 0 <= OL <= dcap ->
    7 * Z.of_nat r <= i0 -> 7 * Z.of_nat r <= i1 -> 7 * Z.of_nat r <= i2 -> 7 * Z.of_nat r <= i3 ->
    i0 + 8 <= n -> i1 + 8 <= n -> i2 + 8 <= n -> i3 + 8 <= n -> 8 <= l1 -> 8 <= l2 -> 8 <= l3 -> 6 + l1 + l2 + l3 + 8 <= n ->
    o0 + 4 <= u0 <= o0 + 8 ->
    o1 + 4 <= u1 <= o1 + 8 ->
    o2 + 4 <= u2 <= o2 + 8 ->
    0 <= ix <= 2047 ->
    LBW 52 c0 ->
    LBW 52 c1 ->
    LBW 52 c2 ->
    LBW 8 c3 ->
    KHI r mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 ->
    KOI r mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 ->
    evtF bsegs RNG POST (ST 0x85cdc mm x1 c1 x6 (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (18446744073709551600)) (Z_to_bv 64 (SPV + -136)) (Z_to_bv 64 (nd)) c0 (Z_to_bv 64 (DST + o3)) (Z_to_bv 64 (DST + u0)) (Z_to_bv 64 (DST + u2)) (Z_to_bv 64 (DST + u1)) (Z_to_bv 64 (4 * ix)) x17 x18 x19 c3 (Z_to_bv 64 (SPV + -168)) c2 SB x24 x25 (Z_to_bv 64 (134483)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + OL)) (Z_to_bv 64 (SRC + i3)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i0))).

  Definition x42e_fi7_stmt : Prop := forall (r : nat) mb mm q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 u0 u1 u2 ix (c0 c1 c2 c3 : word) (e0 e1 e2 e3 : word) (av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 : word)
      (x1 x5 x17 x18 x19 x24 x25 : word)
      (w0 w1 w2 : word),
    munch WDL mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    (FRS mm w0 w1 w2 (Z_to_bv 64 (SRC)) (Z_to_bv 64 (n)) (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + 3 * q)) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (66420))) ->
    (ARGS mm av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
    (LOC mm e0 e1 e2 e3 (Z_to_bv 64 (DST + u0)) (Z_to_bv 64 (DST + u1)) (Z_to_bv 64 (DST + u2)) (Z_to_bv 64 (DST + o3)) (Z_to_bv 64 (SRC + i0)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i3)) c0 c1 c2 c3) ->
    bytes_at bsegs mm SRC src -> nd = -1 * DT + -5 ->
    (1 <= r)%nat -> OL - o3 <= 5 * Z.of_nat r -> 0 <= o0 -> 0 <= o1 -> 0 <= o2 -> 0 <= o3 ->
    o0 + 10 * Z.of_nat r <= q -> o1 + 10 * Z.of_nat r <= 2 * q -> o2 + 10 * Z.of_nat r <= 3 * q -> o3 + 10 * Z.of_nat r <= dcap ->
    3 * q <= dcap -> 0 <= q -> 0 <= OL <= dcap ->
    7 * Z.of_nat r <= i0 -> 7 * Z.of_nat r <= i1 -> 7 * Z.of_nat r <= i2 -> 7 * Z.of_nat r <= i3 ->
    i0 + 8 <= n -> i1 + 8 <= n -> i2 + 8 <= n -> i3 + 8 <= n -> 8 <= l1 -> 8 <= l2 -> 8 <= l3 -> 6 + l1 + l2 + l3 + 8 <= n ->
    o0 + 5 <= u0 <= o0 + 10 ->
    o1 + 5 <= u1 <= o1 + 10 ->
    o2 + 4 <= u2 <= o2 + 8 ->
    0 <= ix <= 2047 ->
    LBW 63 c0 ->
    LBW 63 c1 ->
    LBW 52 c2 ->
    LBW 8 c3 ->
    KHI r mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 ->
    KOI r mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 ->
    evtF bsegs RNG POST (ST 0x85e44 mm x1 x5 c1 (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (18446744073709551600)) (Z_to_bv 64 (SPV + -136)) (Z_to_bv 64 (nd)) c0 (Z_to_bv 64 (DST + o3)) (Z_to_bv 64 (DST + u0)) (Z_to_bv 64 (DST + u2)) (Z_to_bv 64 (DST + u1)) (Z_to_bv 64 (4 * ix)) x17 x18 x19 c3 (Z_to_bv 64 (SPV + -168)) c2 SB x24 x25 (Z_to_bv 64 (134483)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + OL)) (Z_to_bv 64 (SRC + i3)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i0))).

  Definition x42e_fi8_stmt : Prop := forall (r : nat) mb mm q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 u0 u1 u2 u3 ix (c0 c1 c2 c3 : word) (e0 e1 e2 e3 : word) (av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 : word)
      (x1 x17 x18 x19 x20 x22 x25 : word)
      (w0 w1 w2 : word),
    munch WDL mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    (FRS mm w0 w1 w2 (Z_to_bv 64 (SRC)) (Z_to_bv 64 (n)) (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + 3 * q)) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (66420))) ->
    (ARGS mm av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
    (LOC mm e0 e1 e2 e3 (Z_to_bv 64 (DST + u0)) (Z_to_bv 64 (DST + u1)) (Z_to_bv 64 (DST + u2)) (Z_to_bv 64 (DST + u3)) (Z_to_bv 64 (SRC + i0)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i3)) c0 c1 c2 c3) ->
    bytes_at bsegs mm SRC src -> nd = -1 * DT + -5 ->
    (1 <= r)%nat -> OL - o3 <= 5 * Z.of_nat r -> 0 <= o0 -> 0 <= o1 -> 0 <= o2 -> 0 <= o3 ->
    o0 + 10 * Z.of_nat r <= q -> o1 + 10 * Z.of_nat r <= 2 * q -> o2 + 10 * Z.of_nat r <= 3 * q -> o3 + 10 * Z.of_nat r <= dcap ->
    3 * q <= dcap -> 0 <= q -> 0 <= OL <= dcap ->
    7 * Z.of_nat r <= i0 -> 7 * Z.of_nat r <= i1 -> 7 * Z.of_nat r <= i2 -> 7 * Z.of_nat r <= i3 ->
    i0 + 8 <= n -> i1 + 8 <= n -> i2 + 8 <= n -> i3 + 8 <= n -> 8 <= l1 -> 8 <= l2 -> 8 <= l3 -> 6 + l1 + l2 + l3 + 8 <= n ->
    o0 + 5 <= u0 <= o0 + 10 ->
    o1 + 5 <= u1 <= o1 + 10 ->
    o2 + 5 <= u2 <= o2 + 10 ->
    o3 + 1 <= u3 <= o3 + 2 ->
    0 <= ix <= 2047 ->
    LBW 63 c0 ->
    LBW 63 c1 ->
    LBW 63 c2 ->
    LBW 19 c3 ->
    KHI r mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 ->
    KOI r mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 ->
    evtF bsegs RNG POST (ST 0x85fcc mm x1 c3 c1 (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (18446744073709551600)) (Z_to_bv 64 (SPV + -136)) (Z_to_bv 64 (nd)) c0 (Z_to_bv 64 (DST + u3)) (Z_to_bv 64 (DST + u0)) (Z_to_bv 64 (DST + u2)) (Z_to_bv 64 (DST + u1)) (Z_to_bv 64 (4 * ix)) x17 x18 x19 x20 (Z_to_bv 64 (SPV + -168)) x22 SB c2 x25 (Z_to_bv 64 (134483)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + OL)) (Z_to_bv 64 (SRC + i3)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i0))).

  Definition x42e_fi9_stmt : Prop := forall (r : nat) mb mm q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 u0 u1 u2 u3 j0 ix (c0 c1 c2 c3 : word) (e0 e1 e2 e3 : word) (av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 : word)
      (x1 x5 x18 x19 x25 x31 : word)
      (w0 w1 w2 : word),
    munch WDL mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    (FRS mm w0 w1 w2 (Z_to_bv 64 (SRC)) (Z_to_bv 64 (n)) (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + 3 * q)) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (66420))) ->
    (ARGS mm av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
    (LOC mm e0 e1 e2 e3 (Z_to_bv 64 (DST + u0)) (Z_to_bv 64 (DST + u1)) (Z_to_bv 64 (DST + u2)) (Z_to_bv 64 (DST + u3)) (Z_to_bv 64 (SRC + j0)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i3)) c0 c1 c2 c3) ->
    bytes_at bsegs mm SRC src -> nd = -1 * DT + -5 ->
    (1 <= r)%nat -> OL - o3 <= 5 * Z.of_nat r -> 0 <= o0 -> 0 <= o1 -> 0 <= o2 -> 0 <= o3 ->
    o0 + 10 * Z.of_nat r <= q -> o1 + 10 * Z.of_nat r <= 2 * q -> o2 + 10 * Z.of_nat r <= 3 * q -> o3 + 10 * Z.of_nat r <= dcap ->
    3 * q <= dcap -> 0 <= q -> 0 <= OL <= dcap ->
    7 * Z.of_nat r <= i0 -> 7 * Z.of_nat r <= i1 -> 7 * Z.of_nat r <= i2 -> 7 * Z.of_nat r <= i3 ->
    i0 + 8 <= n -> i1 + 8 <= n -> i2 + 8 <= n -> i3 + 8 <= n -> 8 <= l1 -> 8 <= l2 -> 8 <= l3 -> 6 + l1 + l2 + l3 + 8 <= n ->
    o0 + 5 <= u0 <= o0 + 10 ->
    o1 + 5 <= u1 <= o1 + 10 ->
    o2 + 5 <= u2 <= o2 + 10 ->
    o3 + 2 <= u3 <= o3 + 4 ->
    i0 - 7 <= j0 <= i0 ->
    0 <= ix <= 2047 ->
    LBW 7 c0 ->
    LBW 63 c1 ->
    LBW 63 c2 ->
    LBW 30 c3 ->
    KHI r mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 ->
    KOI r mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 ->
    evtF bsegs RNG POST (ST 0x86168 mm x1 x5 c1 (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (18446744073709551600)) (Z_to_bv 64 (SPV + -136)) (Z_to_bv 64 (nd)) c0 (Z_to_bv 64 (DST + u3)) (Z_to_bv 64 (DST + u0)) (Z_to_bv 64 (DST + u2)) (Z_to_bv 64 (DST + u1)) (Z_to_bv 64 (SRC + j0)) (Z_to_bv 64 (4 * ix)) x18 x19 (Z_to_bv 64 (151050438420815295)) (Z_to_bv 64 (SPV + -168)) c3 SB c2 x25 (Z_to_bv 64 (134483)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + OL)) (Z_to_bv 64 (SRC + i3)) (Z_to_bv 64 (SRC + i1)) x31).

  Definition x42e_fi10_stmt : Prop := forall (r : nat) mb mm q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 u0 u1 u2 u3 j0 j1 ix (c0 c1 c2 c3 : word) (e0 e1 e2 e3 : word) (av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 : word)
      (x1 x6 x18 x19 x25 x30 : word)
      (w0 w1 w2 : word),
    munch WDL mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    (FRS mm w0 w1 w2 (Z_to_bv 64 (SRC)) (Z_to_bv 64 (n)) (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + 3 * q)) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (66420))) ->
    (ARGS mm av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
    (LOC mm e0 e1 e2 e3 (Z_to_bv 64 (DST + u0)) (Z_to_bv 64 (DST + u1)) (Z_to_bv 64 (DST + u2)) (Z_to_bv 64 (DST + u3)) (Z_to_bv 64 (SRC + j0)) (Z_to_bv 64 (SRC + j1)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i3)) c0 c1 c2 c3) ->
    bytes_at bsegs mm SRC src -> nd = -1 * DT + -5 ->
    (1 <= r)%nat -> OL - o3 <= 5 * Z.of_nat r -> 0 <= o0 -> 0 <= o1 -> 0 <= o2 -> 0 <= o3 ->
    o0 + 10 * Z.of_nat r <= q -> o1 + 10 * Z.of_nat r <= 2 * q -> o2 + 10 * Z.of_nat r <= 3 * q -> o3 + 10 * Z.of_nat r <= dcap ->
    3 * q <= dcap -> 0 <= q -> 0 <= OL <= dcap ->
    7 * Z.of_nat r <= i0 -> 7 * Z.of_nat r <= i1 -> 7 * Z.of_nat r <= i2 -> 7 * Z.of_nat r <= i3 ->
    i0 + 8 <= n -> i1 + 8 <= n -> i2 + 8 <= n -> i3 + 8 <= n -> 8 <= l1 -> 8 <= l2 -> 8 <= l3 -> 6 + l1 + l2 + l3 + 8 <= n ->
    o0 + 5 <= u0 <= o0 + 10 ->
    o1 + 5 <= u1 <= o1 + 10 ->
    o2 + 5 <= u2 <= o2 + 10 ->
    o3 + 3 <= u3 <= o3 + 6 ->
    i0 - 7 <= j0 <= i0 ->
    i1 - 7 <= j1 <= i1 ->
    0 <= ix <= 2047 ->
    LBW 7 c0 ->
    LBW 7 c1 ->
    LBW 63 c2 ->
    LBW 41 c3 ->
    KHI r mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 ->
    KOI r mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 ->
    evtF bsegs RNG POST (ST 0x86308 mm x1 (Z_to_bv 64 (4 * ix)) x6 (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (18446744073709551600)) (Z_to_bv 64 (SPV + -136)) (Z_to_bv 64 (nd)) c0 (Z_to_bv 64 (DST + u3)) (Z_to_bv 64 (DST + u0)) (Z_to_bv 64 (DST + u2)) (Z_to_bv 64 (DST + u1)) (Z_to_bv 64 (SRC + j0)) (Z_to_bv 64 (SRC + j1)) x18 x19 (Z_to_bv 64 (151050438420815295)) (Z_to_bv 64 (SPV + -168)) c1 SB c2 x25 (Z_to_bv 64 (134483)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + OL)) (Z_to_bv 64 (SRC + i3)) x30 c3).

  Definition x42e_fi11_stmt : Prop := forall (r : nat) mb mm q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 u0 u1 u2 u3 j0 j1 j2 ix (c0 c1 c2 c3 : word) (e0 e1 e2 e3 : word) (av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 : word)
      (x1 x7 x18 x19 x25 x31 : word)
      (w0 w1 w2 : word),
    munch WDL mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    (FRS mm w0 w1 w2 (Z_to_bv 64 (SRC)) (Z_to_bv 64 (n)) (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + 3 * q)) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (66420))) ->
    (ARGS mm av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
    (LOC mm e0 e1 e2 e3 (Z_to_bv 64 (DST + u0)) (Z_to_bv 64 (DST + u1)) (Z_to_bv 64 (DST + u2)) (Z_to_bv 64 (DST + u3)) (Z_to_bv 64 (SRC + j0)) (Z_to_bv 64 (SRC + j1)) (Z_to_bv 64 (SRC + j2)) (Z_to_bv 64 (SRC + i3)) c0 c1 c2 c3) ->
    bytes_at bsegs mm SRC src -> nd = -1 * DT + -5 ->
    (1 <= r)%nat -> OL - o3 <= 5 * Z.of_nat r -> 0 <= o0 -> 0 <= o1 -> 0 <= o2 -> 0 <= o3 ->
    o0 + 10 * Z.of_nat r <= q -> o1 + 10 * Z.of_nat r <= 2 * q -> o2 + 10 * Z.of_nat r <= 3 * q -> o3 + 10 * Z.of_nat r <= dcap ->
    3 * q <= dcap -> 0 <= q -> 0 <= OL <= dcap ->
    7 * Z.of_nat r <= i0 -> 7 * Z.of_nat r <= i1 -> 7 * Z.of_nat r <= i2 -> 7 * Z.of_nat r <= i3 ->
    i0 + 8 <= n -> i1 + 8 <= n -> i2 + 8 <= n -> i3 + 8 <= n -> 8 <= l1 -> 8 <= l2 -> 8 <= l3 -> 6 + l1 + l2 + l3 + 8 <= n ->
    o0 + 5 <= u0 <= o0 + 10 ->
    o1 + 5 <= u1 <= o1 + 10 ->
    o2 + 5 <= u2 <= o2 + 10 ->
    o3 + 4 <= u3 <= o3 + 8 ->
    i0 - 7 <= j0 <= i0 ->
    i1 - 7 <= j1 <= i1 ->
    i2 - 7 <= j2 <= i2 ->
    0 <= ix <= 2047 ->
    LBW 7 c0 ->
    LBW 7 c1 ->
    LBW 7 c2 ->
    LBW 52 c3 ->
    KHI r mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 ->
    KOI r mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 ->
    evtF bsegs RNG POST (ST 0x864b0 mm x1 (Z_to_bv 64 (SRC + j2)) (Z_to_bv 64 (4 * ix)) x7 (Z_to_bv 64 (18446744073709551600)) (Z_to_bv 64 (SPV + -136)) (Z_to_bv 64 (nd)) c0 (Z_to_bv 64 (DST + u3)) (Z_to_bv 64 (DST + u0)) (Z_to_bv 64 (DST + u2)) (Z_to_bv 64 (DST + u1)) (Z_to_bv 64 (SRC + j0)) (Z_to_bv 64 (SRC + j1)) x18 x19 (Z_to_bv 64 (151050438420815295)) (Z_to_bv 64 (SPV + -168)) c1 SB c2 x25 (Z_to_bv 64 (134483)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + OL)) (Z_to_bv 64 (SRC + i3)) c3 x31).

  Definition x42e_fi12_stmt : Prop := forall (r : nat) mb mm q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 u0 u1 u2 u3 j0 j1 j2 (c0 c1 c2 c3 : word) (e0 e1 e2 e3 : word) (av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 : word)
      (x1 x7 x18 x19 x25 x30 x31 : word)
      (w0 w1 w2 : word),
    munch WDL mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    (FRS mm w0 w1 w2 (Z_to_bv 64 (SRC)) (Z_to_bv 64 (n)) (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + 3 * q)) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (66420))) ->
    (ARGS mm av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
    (LOC mm e0 e1 e2 e3 (Z_to_bv 64 (DST + u0)) (Z_to_bv 64 (DST + u1)) (Z_to_bv 64 (DST + u2)) (Z_to_bv 64 (DST + u3)) (Z_to_bv 64 (SRC + j0)) (Z_to_bv 64 (SRC + j1)) (Z_to_bv 64 (SRC + j2)) (Z_to_bv 64 (SRC + i3)) c0 c1 c2 c3) ->
    bytes_at bsegs mm SRC src -> nd = -1 * DT + -5 ->
    (1 <= r)%nat -> OL - o3 <= 5 * Z.of_nat r -> 0 <= o0 -> 0 <= o1 -> 0 <= o2 -> 0 <= o3 ->
    o0 + 10 * Z.of_nat r <= q -> o1 + 10 * Z.of_nat r <= 2 * q -> o2 + 10 * Z.of_nat r <= 3 * q -> o3 + 10 * Z.of_nat r <= dcap ->
    3 * q <= dcap -> 0 <= q -> 0 <= OL <= dcap ->
    7 * Z.of_nat r <= i0 -> 7 * Z.of_nat r <= i1 -> 7 * Z.of_nat r <= i2 -> 7 * Z.of_nat r <= i3 ->
    i0 + 8 <= n -> i1 + 8 <= n -> i2 + 8 <= n -> i3 + 8 <= n -> 8 <= l1 -> 8 <= l2 -> 8 <= l3 -> 6 + l1 + l2 + l3 + 8 <= n ->
    o0 + 5 <= u0 <= o0 + 10 ->
    o1 + 5 <= u1 <= o1 + 10 ->
    o2 + 5 <= u2 <= o2 + 10 ->
    o3 + 5 <= u3 <= o3 + 10 ->
    i0 - 7 <= j0 <= i0 ->
    i1 - 7 <= j1 <= i1 ->
    i2 - 7 <= j2 <= i2 ->
    LBW 7 c0 ->
    LBW 7 c1 ->
    LBW 7 c2 ->
    LBW 63 c3 ->
    KHI r mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 ->
    KOI r mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 ->
    evtF bsegs RNG POST (ST 0x8655c mm x1 (Z_to_bv 64 (SRC + j2)) c3 x7 (Z_to_bv 64 (18446744073709551600)) (Z_to_bv 64 (SPV + -136)) (Z_to_bv 64 (nd)) c0 (Z_to_bv 64 (DST + u3)) (Z_to_bv 64 (DST + u0)) (Z_to_bv 64 (DST + u2)) (Z_to_bv 64 (DST + u1)) (Z_to_bv 64 (SRC + j0)) (Z_to_bv 64 (SRC + j1)) x18 x19 (Z_to_bv 64 (151050438420815295)) (Z_to_bv 64 (SPV + -168)) c1 SB c2 x25 (Z_to_bv 64 (134483)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + OL)) (Z_to_bv 64 (SRC + i3)) x30 x31).

End X42E.
End CANSEC1.

Ltac z4fmem M :=
  lazymatch M with
  | CatExec.wbytes _ _ _ =>
      let SP0 := lazymatch goal with H : z4fI _ ?SP0 _ _ _ _ _ _ _ _ _ _ _ |- _ => constr:(SP0) end in
      lazymatch M with
      | CatExec.wbytes ?m (wa (SP0 + ?o)) (word_to_le_bytes 8 ?v) =>
          z4fmem m;
          lazymatch goal with C : x42e_ctx _ _ _ _ _ _ _ _ _ _ _ |- _ =>
          lazymatch goal with H : z4fI _ _ _ _ _ _ _ _ _ _ _ _ ?cs |- _ =>
          let k := eval vm_compute in (Z.to_nat (o + 232)) in
          let cs' := eval cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in (cell_upd cs k (C8 v)) in
          eapply (z4fI_wr8c _ _ _ _ _ _ _ _ _ _ _ _ C _ _ _ _ cs cs' k _ v (SP0 + o)) in H;
          [ | reflexivity | apply Nat.leb_le; reflexivity | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; ring | reflexivity ]
          end end
      | CatExec.wbytes ?m (wa ?a) (word_to_le_bytes 1 ?v) =>
          z4fmem m;
          lazymatch goal with C : x42e_ctx _ _ _ _ _ _ _ _ _ _ _ |- _ =>
          lazymatch goal with H : z4fI _ _ _ _ _ _ _ _ _ _ _ _ ?cs |- _ =>
          eapply (z4fI_wr1 _ _ _ _ _ _ _ _ _ _ _ _ C _ _ _ _ cs v a) in H; [ | reflexivity | lia | lia ]
          end end
      | _ => idtac
      end
  | _ => idtac
  end.
