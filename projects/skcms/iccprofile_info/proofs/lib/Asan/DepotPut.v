(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.skcms.iccprofile_info.images Require Import Asan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import
  PropExec CatExec CatSim SeqExec StoreOk AgentLib AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlanSound AsanPlanSoundSums DepotSymSeg DepotInv DepotPutA.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2S. Import APC. Import APS. Import APSX. Import SEG.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac el_lia_core := first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                                | Zify.zify; xlia zchecker ].
Local Ltac el_goal_has_var := match goal with |- ?G => match G with context [?x] => is_var x end end.
Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].

Notation DI := (DepotInv ASEGS D SSA).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithFP1. Context {FP : PropExec.FPState}.
(* [comment removed for export] *)
Definition mkE (f : nat -> word) : env := Env f (fun _ => []).

Lemma ev_mkE : forall f i, edenot (mkE f) (EVar i) = f i.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Fixpoint tset (l : list (nat * word)) (f : nat -> word) : nat -> word :=
  match l with [] => f | (i, w) :: r => fun j => if Nat.eqb j i then w else tset r f j end.

Lemma regs_ok_intro : forall E sr R,
  (forall i, (0 < i < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat i)) = edenot E (nth i sr (ELit 0))) ->
  regs_ok E sr R.
Proof.
  intros E sr R H. apply regs_ok_pointwise. intros r Hr0. pose proof (ridx_range r) as Hrr.
  assert (Hr1 : (0 < ridx r)%nat).
  { destruct (ridx r) eqn:E0; [|lia]. exfalso. apply Hr0. rewrite (reg_of_ridx r 0%nat E0). apply bv_eq. reflexivity. }
  rewrite (reg_of_ridx r _ eq_refl) at 1. apply H. lia.
Qed.

Section WithSegsFacts.
#[local] Notation segs := ASEGS.

Lemma kword_intro : forall E M b off w v (a : Z),
  bv_unsigned (edenot E b) + off = a -> 0 <= a -> a + Z.of_nat w <= 2 ^ 64 -> (1 <= w <= 8)%nat ->
  rdn segs M (Z_to_bv 64 a) w = Some (word_to_le_bytes w (edenot E v)) ->
  kentry_ok segs E M (KWord (SA b off) w v).
Proof.
  intros E M b off w v a Ha H0 Hhi Hw Hr. cbn [kentry_ok]. split; [lia|]. split.
  - unfold flat, estart. cbn [a_base a_off]. lia.
  - rewrite adenot_SA. unfold estart. cbn [a_base a_off]. rewrite Ha. exact Hr.
Qed.

Lemma kword_elim : forall E M0 b off w v base,
  kentry_ok segs E M0 (KWord (SA b off) w v) -> bv_unsigned (edenot E b) = base ->
  rdn segs M0 (Z_to_bv 64 (base + off)) w = Some (word_to_le_bytes w (edenot E v)).
Proof.
  intros E M0 b off w v base [Hw [Hfl Hr]] Hb. rewrite <- Hr. f_equal.
  unfold adenot, v_addi. cbn [a_base a_off]. rewrite Hb. reflexivity.
Qed.

Lemma krange_intro : forall E M e lo hi,
  lo <= bv_unsigned (edenot E e) <= hi -> kentry_ok segs E M (KRange e lo hi).
Proof. intros. cbn [kentry_ok]. lia. Qed.

Lemma kalign_intro : forall E M e m,
  0 < m -> bv_unsigned (edenot E e) mod m = 0 -> kentry_ok segs E M (KAlign e m).
Proof. intros. cbn [kentry_ok]. split; assumption. Qed.

Lemma kimg_intro : forall E M lo hi,
  0 <= lo -> hi <= 2 ^ 64 -> (forall i, lo <= i < hi -> M (Z_to_bv 64 i) = None) -> kentry_ok segs E M (KImg lo hi).
Proof. intros. cbn [kentry_ok]. split; [assumption|]. split; assumption. Qed.

Lemma kwr_intro : forall E M b off n (a : Z),
  bv_unsigned (edenot E b) + off = a -> 0 <= a -> 0 < n < 2 ^ 64 -> a + n <= 2 ^ 64 ->
  (forall d m, 0 <= d -> d + Z.of_nat m <= n -> store_ok segs M (Z_to_bv 64 (a + d)) m = true) ->
  kentry_ok segs E M (KWr (SA b off) (ELit n)).
Proof.
  intros E M b off n a Ha H0 Hn Hhi Hs. cbn [kentry_ok].
  assert (En : elenZ E (ELit n) = n) by (unfold elenZ; cbn [edenot]; apply u64_lit; lia). rewrite En.
  split. { unfold flat, estart. cbn [a_base a_off]. lia. }
  intros d m Hd Hdm. unfold estart. cbn [a_base a_off]. rewrite Ha. apply Hs; assumption.
Qed.

Lemma kdisj_intro : forall E M b1 o1 n1 b2 o2 n2,
  0 <= n1 < 2 ^ 64 -> 0 <= n2 < 2 ^ 64 ->
  (bv_unsigned (edenot E b1) + o1 + n1 <= bv_unsigned (edenot E b2) + o2
   \/ bv_unsigned (edenot E b2) + o2 + n2 <= bv_unsigned (edenot E b1) + o1) ->
  kentry_ok segs E M (KDisj (SA b1 o1) (ELit n1) (SA b2 o2) (ELit n2)).
Proof.
  intros. cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite !u64_lit by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma segs_wr_of_forallb : forall sg,
  forallb (fun seg => negb (seg_writable seg) || seg_readable seg)%bool sg = true -> APSX.segs_wr_ok sg.
Proof.
  intros sg H seg Hin Hw. pose proof (proj1 (forallb_forall _ _) H seg Hin) as Hs. cbn beta in Hs.
  rewrite Hw in Hs. exact Hs.
Qed.
Lemma RSEGS_wr : segs_wr_ok segs.
Proof. apply segs_wr_of_forallb. vm_compute. reflexivity. Qed.   (* [comment removed for export] *)

Lemma readable_rdn : forall M a n, 0 <= a < 2 ^ 64 -> a + Z.of_nat n <= 2 ^ 64 -> store_ok segs M (Z_to_bv 64 a) n = true ->
  exists bs, rdn segs M (Z_to_bv 64 a) n = Some bs /\ length bs = n.
Proof. intros M a n Ha Hn H. apply (store_ok_rdn segs RSEGS_wr n M (Z_to_bv 64 a)); [rewrite u64_lit by lia; lia | exact H]. Qed.

(* [comment removed for export] *)
Lemma rdn_as_word : forall M a n bs, (n <= 8)%nat -> rdn segs M a n = Some bs -> length bs = n ->
  rdn segs M a n = Some (word_to_le_bytes n (Z_to_bv 64 (bytes_le_to_Z bs))).
Proof. intros M a n bs Hn H Hl. rewrite H, word_to_le_bytes_of_bytes_n by assumption. reflexivity. Qed.

End WithSegsFacts.

(* [comment removed for export] *)
Lemma nth_allvars : forall i, (1 <= i <= 31)%nat -> nth i allvars (ELit 0) = EVar i.
Proof.
  intros i Hi.
  assert (H : forallb (fun i => expr_eqb (nth i allvars (ELit 0)) (EVar i)) (seq 1 31) = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) H i ltac:(apply in_seq; lia)) as X. apply expr_eqb_eq in X. exact X.
Qed.

Fixpoint lassoc (i : nat) (l : list (nat * expr)) : option expr :=
  match l with [] => None | (j, e) :: r => match lassoc i r with Some e' => Some e' | None => if Nat.eqb i j then Some e else None end end.

Lemma nth_setregs : forall l sr i,
  nth i (setregs l sr) (ELit 0) = match lassoc i l with Some e => e | None => nth i sr (ELit 0) end.
Proof.
  induction l as [|[j e] r IH]; intros sr i; cbn [setregs lassoc]; [reflexivity|].
  rewrite IH. destruct (lassoc i r); [reflexivity|]. rewrite nth_sr_upd. destruct (Nat.eqb i j); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma regs_ok_setregs : forall (E : env) (l : list (nat * expr)) R,
  (forall i, (1 <= i <= 31)%nat -> lassoc i l = None -> getr R (Z_to_bv 5 (Z.of_nat i)) = ev E i) ->
  (forall i e, (1 <= i <= 31)%nat -> lassoc i l = Some e -> getr R (Z_to_bv 5 (Z.of_nat i)) = edenot E e) ->
  regs_ok E (setregs l allvars) R.
Proof.
  intros E l R Hv Hl. apply regs_ok_intro. intros i Hi. rewrite nth_setregs.
  destruct (lassoc i l) as [e|] eqn:Ha.
  - apply Hl; [lia | exact Ha].
  - rewrite nth_allvars by lia. cbn [edenot]. apply Hv; [lia | exact Ha].
Qed.

(* [comment removed for export] *)
Lemma reg_of : forall E sr R i, regs_ok E sr R -> (0 < i < 32)%nat ->
  getr R (Z_to_bv 5 (Z.of_nat i)) = edenot E (nth i sr (ELit 0)).
Proof.
  intros E sr R i HR Hi. rewrite (HR _). unfold sr_get.
  assert (Hnz : bv_eqb (Z_to_bv 5 (Z.of_nat i)) 0%bv = false).
  { unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia.
    replace (bv_unsigned (0%bv : bv 5)) with 0%Z by reflexivity. lia. }
  rewrite Hnz. rewrite ridx_lit by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition KEPTI : list nat := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
End WithFP1.

#[local] Notation gr Rx i := (getr Rx (Z_to_bv 5 (Z.of_nat i))) (only parsing).
Section WithFP2. Context {FP : PropExec.FPState}.
Lemma setregs_app : forall l1 l2 sr, setregs l2 (setregs l1 sr) = setregs (l1 ++ l2) sr.
Proof. induction l1 as [|[i e] r IH]; intros l2 sr; cbn [setregs app]; [reflexivity | apply IH]. Qed.

(* [comment removed for export] *)
Definition sr_ok_but (sr : list expr) (lits : list nat) : bool :=
  forallb (fun i => existsb (Nat.eqb i) lits || expr_eqb (nth i sr (ELit 0)) (EVar i))%bool (seq 1 31).

Lemma regs_ok_lits : forall E sr Rc (lits : list nat),
  sr_ok_but sr lits = true ->
  (forall i, (0 < i < 32)%nat -> edenot E (EVar i) = getr Rc (Z_to_bv 5 (Z.of_nat i))) ->
  Forall (fun i => getr Rc (Z_to_bv 5 (Z.of_nat i)) = edenot E (nth i sr (ELit 0))) lits ->
  regs_ok E sr Rc.
Proof.
  intros E sr Rc lits Hb Hv Hl. apply regs_ok_intro. intros i Hi.
  pose proof (proj1 (forallb_forall _ _) Hb i ltac:(apply in_seq; lia)) as X. cbn beta in X.
  apply Bool.orb_prop in X as [X | X].
  - apply existsb_exists in X as (j & Hj & E1). apply Nat.eqb_eq in E1. subst j.
    exact (proj1 (Forall_forall _ _) Hl i Hj).
  - apply expr_eqb_eq in X. rewrite X. symmetry. apply Hv. exact Hi.
Qed.

(* [comment removed for export] *)
Lemma u_lit : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros. apply u64_lit. lia. Qed.

Lemma Z2bv_mod : forall z, Z_to_bv 64 (z mod 2 ^ 64) = Z_to_bv 64 z.
Proof. intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia. Qed.

(* [comment removed for export] *)
Lemma val_lit : forall E c, edenot E (ELit c) = Z_to_bv 64 c.
Proof. reflexivity. Qed.

Lemma val_add_lit : forall E e c z, edenot E e = Z_to_bv 64 z -> edenot E (EAlu ALU_ADD e (ELit c)) = Z_to_bv 64 (z + c).
Proof.
  intros E e c z He. cbn [edenot]. rewrite He. apply bv_eq. rewrite u_add64, !u_lit64, two64_eq.
  symmetry. apply Zplus_mod.
Qed.

Lemma land_ones : forall z k, 0 <= z -> 0 <= k -> Z.land z (2 ^ k - 1) = z mod 2 ^ k.
Proof.
  intros z k Hz Hk. replace (2 ^ k - 1) with (Z.ones k). { apply Z.land_ones. exact Hk. }
  unfold Z.ones. rewrite Z.shiftl_1_l. lia.
Qed.

Lemma val_bk : forall E e19 (h : word),
  edenot E e19 = h ->
  edenot E (x18_form e19) = Z_to_bv 64 (4 * (bv_unsigned h mod 2 ^ 20) + D).
Proof.
  intros E e19 h He. unfold x18_form. cbn [edenot]. rewrite He. apply bv_eq.
  pose proof (u64_range h) as Hr. pose proof (Z.mod_pos_bound (bv_unsigned h) (2 ^ 20) ltac:(lia)) as Hm.
  rewrite u_add64, u_srl64, u_mul64, !u_lit64, two64_eq by lia.
  replace (2 ^ ((42 mod 2 ^ 64) mod 64)) with (2 ^ 42) by reflexivity.
  replace (17592186044416 mod 2 ^ 64) with (2 ^ 44) by reflexivity.
  rewrite (Z.mod_small D) by (unfold D; lia).
  set (x := bv_unsigned h) in *.
  replace ((2 ^ 44 * x) mod 2 ^ 64) with (2 ^ 44 * (x mod 2 ^ 20)).
  2:{ change (2 ^ 64) with (2 ^ 44 * 2 ^ 20). rewrite Zmult_mod_distr_l. reflexivity. }
  replace (2 ^ 44 * (x mod 2 ^ 20) / 2 ^ 42) with (4 * (x mod 2 ^ 20)).
  2:{ replace (2 ^ 44 * (x mod 2 ^ 20)) with (4 * (x mod 2 ^ 20) * 2 ^ 42) by lia. symmetry. apply Z.div_mul. lia. }
  reflexivity.
Qed.

Lemma val_and31 : forall E e (v : Z), 0 <= v < 2 ^ 31 -> edenot E e = Z_to_bv 64 v ->
  edenot E (EAlu ALU_AND e (ELit 2147483647)) = Z_to_bv 64 v.
Proof.
  intros E e v Hv H40. cbn [edenot]. rewrite H40. apply bv_eq. rewrite u_and64, !u_lit64, two64_eq.
  replace (2147483647 mod 2 ^ 64) with (2 ^ 31 - 1) by reflexivity. rewrite (Z.mod_small v) by lia.
  rewrite land_ones by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma val_node : forall E e (b17v x : Z),
  edenot E (EVar 47) = Z_to_bv 64 b17v -> edenot E e = Z_to_bv 64 x ->
  0 <= x < 65536 -> 0 <= b17v -> b17v + 2 ^ 20 < 2 ^ 64 ->
  edenot E (EAlu ALU_ADD (EMd M_MUL (ELit 16) e) (EVar 47)) = Z_to_bv 64 (b17v + 16 * x).
Proof.
  intros E e b17v x H47 He Hx Hb Hb2. cbn [edenot]. cbn [edenot] in H47. rewrite H47, He. apply bv_eq.
  rewrite u_add64, u_mul64, !u_lit64, two64_eq.
  rewrite (Z.mod_small x) by lia. replace (16 mod 2 ^ 64) with 16 by reflexivity.
  rewrite (Z.mod_small (16 * x)) by lia. rewrite (Z.mod_small b17v) by lia. f_equal. lia.
Qed.

Lemma val_slot : forall E (b18v t : Z),
  edenot E (EVar 48) = Z_to_bv 64 b18v -> edenot E (EVar 46) = Z_to_bv 64 t ->
  0 <= t < 2 ^ 20 -> 0 <= b18v -> b18v + 2 ^ 23 < 2 ^ 64 ->
  edenot E FBt = Z_to_bv 64 (b18v + 8 * t).
Proof.
  intros E b18v t H48 H46 Ht Hb Hb2. unfold FBt. cbn [edenot]. cbn [edenot] in H48, H46. rewrite H48, H46. apply bv_eq.
  rewrite u_add64, u_mul64, !u_lit64, two64_eq.
  rewrite (Z.mod_small t) by lia. replace (8 mod 2 ^ 64) with 8 by reflexivity.
  rewrite (Z.mod_small (8 * t)) by lia. rewrite (Z.mod_small b18v) by lia. f_equal. lia.
Qed.

Lemma ext4_small : forall z, 0 <= z < 2 ^ 31 -> ext_val true 0 4 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold ext_val, ext_Z. apply bv_eq. f_equal.
  rewrite u64_lit by lia. change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite Z.mod_small by lia.
  unfold bv_swrap. change (bv_half_modulus (8 * N.of_nat 4)) with (2 ^ 31).
  unfold bv_wrap. change (bv_modulus (8 * N.of_nat 4)) with (2 ^ 32). f_equal.
  rewrite (Z.mod_small (z + 2 ^ 31) (2 ^ 32)); lia.
Qed.

Lemma val_ext_add : forall E e z c, edenot E e = Z_to_bv 64 z -> 0 <= z < 2 ^ 31 ->
  edenot E (EAlu ALU_ADD (EExt true 0 4 e) (ELit c)) = Z_to_bv 64 (z + c).
Proof.
  intros E e z c Hi Hz. apply (val_add_lit E). cbn [edenot]. rewrite Hi. apply ext4_small. exact Hz.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition disjZ (a la b lb : Z) : Prop := a + la <= b \/ b + lb <= a.

(* [comment removed for export] *)
Lemma out_fpE_of : forall E (x : word) (s sp bk nb fb b17 b18 N T : Z),
  bv_unsigned (edenot E (EVar 2)) = sp - 112 -> bv_unsigned (edenot E (EVar 18)) = bk -> bv_unsigned (edenot E (ELit 0)) = 0 ->
  edenot E NBn = Z_to_bv 64 nb -> 0 <= nb < 2 ^ 64 -> nb = b17 + 16 * N ->
  edenot E FBt = Z_to_bv 64 fb -> 0 <= fb < 2 ^ 64 -> fb = b18 + 8 * T ->
  ~ (sp - 224 <= bv_unsigned x < sp - 112) -> ~ (bk <= bv_unsigned x < bk + 4) ->
  ~ (SSA <= bv_unsigned x < SSA + 8) -> ~ (SSA + 24 <= bv_unsigned x < SSA + 28) ->
  ~ (D + 0x400000 <= bv_unsigned x < D + 0x400004) ->
  ~ (b17 + 16 * (N + 1) <= bv_unsigned x < b17 + 16 * (N + 1) + 16) ->
  ~ (b18 + 8 * T <= bv_unsigned x < b18 + 8 * T + (8 + 8 * s)) -> out_fp E (fpE s) x.
Proof.
  intros E x s sp bk nb fb b17 b18 N T E2 E18 E0 ENB Hnb Enb EFB Hfb Efb X1 X2 X3 X4 X5 X6 X7. unfold out_fp, fpE.
  assert (ENB' : bv_unsigned (edenot E NBn) = nb) by (rewrite ENB; apply u_lit; exact Hnb).
  assert (EFB' : bv_unsigned (edenot E FBt) = fb) by (rewrite EFB; apply u_lit; exact Hfb).
  clear ENB EFB. subst nb fb.
  repeat apply Forall_cons; try apply Forall_nil; cbn beta iota; rewrite ?E2, ?E18, ?E0, ?ENB', ?EFB'; lia.
Qed.

Section Put.
  Variables (R : bvmap 5 word) (M : word -> option byte) (rom : word -> option byte).
  Variables (sp tr s K b17 b18 : Z).
  Hypothesis Hsp : gr R 2 = Z_to_bv 64 sp.
  Hypothesis Hsp16 : sp mod 16 = 0.
  Hypothesis Hsplo : ACEILZ <= sp - 272.
  Hypothesis Hsphi : sp <= 2 ^ 47.
  Hypothesis Htr : gr R 10 = Z_to_bv 64 tr.
  Hypothesis Htr8 : tr mod 8 = 0.
  Hypothesis Htrlo : ACEILZ <= tr.
  Hypothesis Htrhi : tr + 16 <= 2 ^ 47.
  Hypothesis Hs : gr R 11 = Z_to_bv 64 s.
  Hypothesis Hs12 : s = 1 \/ s = 2.
  Hypothesis Hframe : store_ok ASEGS M (Z_to_bv 64 (sp - 272)) 272 = true.
  Hypothesis Htrok : store_ok ASEGS M (Z_to_bv 64 tr) 16 = true.
  Hypothesis Hapart : tr + 16 <= sp - 272 \/ sp <= tr.
  Hypothesis Himg : forall i, 0x10000 <= i < 0x30000 -> M (Z_to_bv 64 i) = None.
  Hypothesis HK : 0 <= K.
  (* [comment removed for export] *)
  Hypothesis Hb17sp : disjZ b17 (2 ^ 20) (sp - 272) 272.
  Hypothesis Hb18sp : disjZ b18 (8 * TCAP) (sp - 272) 272.
  Hypothesis Hb17tr : disjZ b17 (2 ^ 20) tr 16.
  Hypothesis Hb18tr : disjZ b18 (8 * TCAP) tr 16.

  (* [comment removed for export] *)
  Definition FRAME (MA : word -> option byte) : Prop :=
    rdn ASEGS MA (Z_to_bv 64 (sp - 8)) 8 = Some (word_to_le_bytes 8 (gr R 1))
    /\ rdn ASEGS MA (Z_to_bv 64 (sp - 16)) 8 = Some (word_to_le_bytes 8 (gr R 8))
    /\ rdn ASEGS MA (Z_to_bv 64 (sp - 24)) 8 = Some (word_to_le_bytes 8 (gr R 9))
    /\ rdn ASEGS MA (Z_to_bv 64 (sp - 32)) 8 = Some (word_to_le_bytes 8 (gr R 18))
    /\ rdn ASEGS MA (Z_to_bv 64 (sp - 40)) 8 = Some (word_to_le_bytes 8 (gr R 19))
    /\ rdn ASEGS MA (Z_to_bv 64 (sp - 48)) 8 = Some (word_to_le_bytes 8 (gr R 20))
    /\ rdn ASEGS MA (Z_to_bv 64 (sp - 56)) 8 = Some (word_to_le_bytes 8 (gr R 21))
    /\ rdn ASEGS MA (Z_to_bv 64 (sp - 64)) 8 = Some (word_to_le_bytes 8 (gr R 22))
    /\ rdn ASEGS MA (Z_to_bv 64 (sp - 72)) 8 = Some (word_to_le_bytes 8 (gr R 23))
    /\ rdn ASEGS MA (Z_to_bv 64 (sp - 80)) 8 = Some (word_to_le_bytes 8 (gr R 24))
    /\ rdn ASEGS MA (Z_to_bv 64 (sp - 88)) 8 = Some (word_to_le_bytes 8 (gr R 25))
    /\ rdn ASEGS MA (Z_to_bv 64 (sp - 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 s))
    /\ rdn ASEGS MA (Z_to_bv 64 (sp - 104)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 tr)).

  Section Inv.
  Variables (N T : Z) (w0 w1 : word).

  (* [comment removed for export] *)
  Definition TABV (a40 a41 hw lk : word) (i : nat) : word :=
    match i with
    | 33 => gr R 1 | 34 => gr R 8 | 35 => gr R 9 | 36 => gr R 18 | 37 => gr R 19
    | 38 => gr R 20 | 39 => gr R 21 | 42 => gr R 22 | 43 => gr R 23 | 54 => gr R 24
    | 55 => gr R 25 | 44 => Z_to_bv 64 tr | 56 => Z_to_bv 64 s | 40 => a40 | 41 => a41
    | 45 => Z_to_bv 64 N | 46 => Z_to_bv 64 T | 47 => Z_to_bv 64 b17 | 48 => Z_to_bv 64 b18 | 52 => hw | 53 => lk
    | _ => Z_to_bv 64 0
    end%nat.
  Definition ENV (Rc : bvmap 5 word) (a40 a41 hw lk : word) : env :=
    mkE (fun i => if Nat.ltb i 32 then gr Rc i else TABV a40 a41 hw lk i).

  Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.   (* [comment removed for export] *)
  Lemma EV_lo : forall Rc a40 a41 hw lk i, (i < 32)%nat -> edenot (ENV Rc a40 a41 hw lk) (EVar i) = gr Rc i.
  Proof. intros. cbn [edenot ENV mkE ev]. destruct (Nat.ltb_spec i 32); [reflexivity | lia]. Qed.
  Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].
  Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.   (* [comment removed for export] *)
  Lemma EV_hi : forall Rc a40 a41 hw lk i, (32 <= i)%nat -> edenot (ENV Rc a40 a41 hw lk) (EVar i) = TABV a40 a41 hw lk i.
  Proof. intros. cbn [edenot ENV mkE ev]. destruct (Nat.ltb_spec i 32); [lia | reflexivity]. Qed.
  Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].

  Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.   (* [comment removed for export] *)
  Lemma regs_ok_ENV : forall Rc a40 a41 hw lk sr lits,
    sr_ok_but sr lits = true ->
    Forall (fun i => gr Rc i = edenot (ENV Rc a40 a41 hw lk) (nth i sr (ELit 0))) lits ->
    regs_ok (ENV Rc a40 a41 hw lk) sr Rc.
  Proof. intros. eapply regs_ok_lits; [eassumption | intros; apply EV_lo; lia | assumption]. Qed.
  Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].

  (* [comment removed for export] *)
  Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.   (* [comment removed for export] *)
  Lemma wr_of_store_ok : forall Mx base len, 0 <= base -> 0 <= len -> base + len < 2 ^ 64 ->
    store_ok ASEGS Mx (Z_to_bv 64 base) (Z.to_nat len) = true -> wr_ok ASEGS Mx base len.
  Proof.
    intros Mx base len Hb Hl Hbl Hst d m Hd Hdm.
    apply (StoreOk.store_ok_sub ASEGS Mx (Z_to_bv 64 base) _ (Z.to_nat len) m); rewrite ?u_lit; try lia. exact Hst.
  Qed.
  Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].

  Hypothesis Hw0 : rdn ASEGS M (Z_to_bv 64 tr) 8 = Some (word_to_le_bytes 8 w0).
  Hypothesis Hw1 : rdn ASEGS M (Z_to_bv 64 (tr + 8)) 8 = Some (word_to_le_bytes 8 w1).

  Definition bkt (h : word) : Z := 4 * (bv_unsigned h mod 2 ^ 20) + D.

  Definition ARegs (RA : bvmap 5 word) (h : word) : Prop :=
    gr RA 1 = gr R 1 /\ gr RA 2 = Z_to_bv 64 (sp - 112) /\ gr RA 3 = gr R 3 /\ gr RA 4 = gr R 4
    /\ gr RA 8 = Z_to_bv 64 0 /\ gr RA 9 = Z_to_bv 64 D /\ gr RA 13 = Z_to_bv 64 0x400000
    /\ gr RA 18 = Z_to_bv 64 (bkt h) /\ gr RA 19 = h
    /\ gr RA 22 = Z_to_bv 64 65535 /\ gr RA 23 = Z_to_bv 64 2147483647
    /\ gr RA 26 = gr R 26 /\ gr RA 27 = gr R 27.

  Lemma osrA_facts : forall s0, s0 = 1 \/ s0 = 2 ->
    nth 1 (osrA s0) (ELit 0) = EVar 1 /\ nth 2 (osrA s0) (ELit 0) = EAlu ALU_ADD (EVar 2) (ELit (-112))
    /\ nth 3 (osrA s0) (ELit 0) = EVar 3 /\ nth 4 (osrA s0) (ELit 0) = EVar 4
    /\ nth 8 (osrA s0) (ELit 0) = ELit 0 /\ nth 9 (osrA s0) (ELit 0) = ELit D /\ nth 13 (osrA s0) (ELit 0) = ELit 0x400000
    /\ nth 22 (osrA s0) (ELit 0) = ELit 65535 /\ nth 23 (osrA s0) (ELit 0) = ELit 2147483647
    /\ nth 26 (osrA s0) (ELit 0) = EVar 26 /\ nth 27 (osrA s0) (ELit 0) = EVar 27.
  Proof. intros s0 [-> | ->]; repeat split; reflexivity. Qed.

  Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.   (* [comment removed for export] *)
  Lemma wr_frame : wr_ok ASEGS M (sp - 272) 272.
  Proof. apply wr_of_store_ok; unfold ACEILZ in *; try lia. exact Hframe. Qed.
  Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].

  Lemma stepA : exists RA MA (h : word),
    msteps ASEGS (mkst R (Z_to_bv 64 PUT_PC) M rom) (mkst RA (Z_to_bv 64 PC_HASHED) MA rom)
    /\ ARegs RA h /\ FRAME MA
    /\ (forall x : word, ~ (sp - 104 <= bv_unsigned x < sp) -> MA x = M x) /\ mem_grows M MA.
  Proof.
    unfold ACEILZ in *.
    set (EA := ENV R w0 w1 (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (EA2 : bv_unsigned (edenot EA (EVar 2)) = sp).
    { subst EA. rewrite EV_lo by lia. rewrite Hsp. apply u_lit. lia. }
    assert (EA10 : bv_unsigned (edenot EA (EVar 10)) = tr).
    { subst EA. rewrite EV_lo by lia. rewrite Htr. apply u_lit. lia. }
    assert (HRA : regs_ok EA (srA s) R).
    { apply regs_ok_ENV with (lits := [11%nat]); [vm_compute; reflexivity|].
      constructor; [|constructor]. change (nth 11 (srA s) (ELit 0)) with (ELit s). rewrite val_lit. exact Hs. }
    assert (HKA : know_ok ASEGS EA M knA).
    { unfold knA, know_ok. unfold ACEILZ in *. repeat apply Forall_cons; try apply Forall_nil.
      - apply kalign_intro; [lia|]. rewrite EA2. exact Hsp16.
      - apply krange_intro. rewrite EA2. lia.
      - apply (kwr_intro EA M (EVar 2) (-272) 272 (sp - 272)); rewrite ?EA2; try lia. exact wr_frame.
      - apply kalign_intro; [lia|]. rewrite EA10. exact Htr8.
      - apply krange_intro. rewrite EA10. lia.
      - apply (kword_intro EA M (EVar 10) 0 8 (EVar 40) tr); rewrite ?EA10; try lia.
        subst EA. rewrite EV_hi by lia. cbn [TABV]. exact Hw0.
      - apply (kword_intro EA M (EVar 10) 8 8 (EVar 41) (tr + 8)); rewrite ?EA10; try lia.
        subst EA. rewrite EV_hi by lia. cbn [TABV]. exact Hw1.
      - apply kdisj_intro; rewrite ?EA2, ?EA10; lia.
      - apply kimg_intro; [lia | lia | exact Himg]. }
    destruct (GA_ok s Hs12 EA R M rom HRA HKA ltac:(constructor)) as (RA & MA & MSA & HRA' & HKA' & OUTA & GRA).
    cbn [g_pc g_opc g_osr g_okn g_fp GA] in MSA, HRA', HKA', OUTA.
    set (h := gr RA 19).
    exists RA, MA, h.
    split; [exact MSA|].
    assert (RAv : forall i e, (0 < i < 32)%nat -> nth i (osrA s) (ELit 0) = e -> gr RA i = edenot EA e).
    { intros i e Hi He. rewrite (reg_of EA _ RA i HRA' Hi), He. reflexivity. }
    destruct (osrA_facts s Hs12) as (A1 & A2 & A3 & A4 & A8 & A9 & A13 & A22 & A23 & A26 & A27).
    split.
    { unfold ARegs.
      rewrite (RAv 1%nat _ ltac:(lia) A1), (RAv 2%nat _ ltac:(lia) A2), (RAv 3%nat _ ltac:(lia) A3), (RAv 4%nat _ ltac:(lia) A4).
      rewrite (RAv 8%nat _ ltac:(lia) A8), (RAv 9%nat _ ltac:(lia) A9), (RAv 13%nat _ ltac:(lia) A13).
      rewrite (RAv 22%nat _ ltac:(lia) A22), (RAv 23%nat _ ltac:(lia) A23), (RAv 26%nat _ ltac:(lia) A26), (RAv 27%nat _ ltac:(lia) A27).
      rewrite (RAv 18%nat _ ltac:(lia) (GA_x18 s Hs12)).
      assert (E19 : edenot EA (nth 19 (osrA s) (ELit 0)) = h) by (symmetry; apply (reg_of EA _ RA 19 HRA'); lia).
      rewrite (val_bk EA _ h E19). rewrite !val_lit.
      rewrite (val_add_lit EA (EVar 2) (-112) sp) by (subst EA; rewrite EV_lo by lia; exact Hsp).
      subst EA. rewrite !EV_lo by lia. unfold bkt. repeat split; reflexivity. }
    split.
    { unfold frameA, know_ok in HKA'.
      do 13 (let F := fresh "F" in apply Forall_cons_iff in HKA' as [F HKA']; apply (kword_elim EA MA (EVar 2) _ 8 _ sp) in F; [|exact EA2]).
      unfold FRAME.
      repeat match goal with |- _ /\ _ => split end.
      all: match goal with F : rdn _ _ (Z_to_bv 64 (sp + ?o)) 8 = Some _ |- rdn _ _ (Z_to_bv 64 (sp - ?k)) 8 = _ =>
             replace (sp - k) with (sp + o) by lia; rewrite F end.
      all: subst EA; rewrite ?EV_lo by lia; rewrite ?val_lit; try reflexivity.
      rewrite Htr. reflexivity. }
    split; [|exact GRA].
    intros x Hx. apply OUTA. constructor; [|constructor]. rewrite EA2. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section AfterA.
  Variable MA : word -> option byte.
  Hypothesis HFR : FRAME MA.
  Hypothesis MAout : forall x : word, ~ (sp - 104 <= bv_unsigned x < sp) -> MA x = M x.
  Hypothesis MAgr : mem_grows M MA.
  Hypothesis HIS : DepotInvS ASEGS D SSA (K + 1) b17 b18 (DST N T) MA.

  Ltac dinv :=
    let X := fresh "HIS_" in
    pose proof HIS as X; unfold DepotInvS in X; cbn [d_N d_T] in X;
    destruct X as (HK1 & HN & HNK & HT & HTK & RN & R17 & RT & R18 & RC & A17lo & A17hi & A17al & A18lo & A18hi & A18al & Hdisj
                   & L1 & L2 & L3 & L4 & L5 & W1 & W2 & W3 & W4 & TAB & NODES);
    unfold TCAP, IMGHI, VATOP, ACEILZ, DepotPutA.KHI in *;
    assert (HDv : D = 0x188a98) by reflexivity; assert (HSv : SSA = 0x178a88) by reflexivity.

  Lemma wr_ok_mono : forall M1 M2 a len, mem_grows M1 M2 -> wr_ok ASEGS M1 a len -> wr_ok ASEGS M2 a len.
  Proof. intros M1 M2 a len Hg H d m Hd Hdm. eapply store_ok_mono; [exact Hg | apply H; assumption]. Qed.

  Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.   (* [comment removed for export] *)
  Lemma wr_frameA : wr_ok ASEGS MA (sp - 272) 272.
  Proof. eapply wr_ok_mono; [exact MAgr | exact wr_frame]. Qed.
  Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].

  Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.   (* [comment removed for export] *)
  Lemma HwA0 : rdn ASEGS MA (Z_to_bv 64 tr) 8 = Some (word_to_le_bytes 8 w0).
  Proof.
    unfold ACEILZ in *. rewrite (rdn_ext ASEGS 8 MA M); [exact Hw0 | rewrite u_lit; lia |].
    intros x Hx. rewrite u_lit in Hx by lia. apply MAout. lia.
  Qed.
  Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].
  Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.   (* [comment removed for export] *)
  Lemma HwA1 : rdn ASEGS MA (Z_to_bv 64 (tr + 8)) 8 = Some (word_to_le_bytes 8 w1).
  Proof.
    unfold ACEILZ in *. rewrite (rdn_ext ASEGS 8 MA M); [exact Hw1 | rewrite u_lit; lia |].
    intros x Hx. rewrite u_lit in Hx by lia. apply MAout. lia.
  Qed.
  Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].
  Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.   (* [comment removed for export] *)
  Lemma HimgA : forall i, 0x10000 <= i < 0x30000 -> MA (Z_to_bv 64 i) = None.
  Proof. unfold ACEILZ in *. intros i Hi. rewrite MAout; [apply Himg; exact Hi|]. rewrite u_lit; lia. Qed.
  Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].

  (* [comment removed for export] *)
  Definition LRegs (Rc : bvmap 5 word) (h : word) (v cur : Z) : Prop :=
    gr Rc 1 = gr R 1 /\ gr Rc 2 = Z_to_bv 64 (sp - 112) /\ gr Rc 3 = gr R 3 /\ gr Rc 4 = gr R 4
    /\ gr Rc 8 = Z_to_bv 64 0 /\ gr Rc 9 = Z_to_bv 64 D /\ gr Rc 11 = Z_to_bv 64 cur
    /\ gr Rc 18 = Z_to_bv 64 (bkt h) /\ gr Rc 19 = h
    /\ gr Rc 20 = Z_to_bv 64 (D + 0x400008) /\ gr Rc 22 = Z_to_bv 64 65535 /\ gr Rc 23 = Z_to_bv 64 2147483647
    /\ gr Rc 24 = Z_to_bv 64 (D + 0x400010) /\ gr Rc 25 = Z_to_bv 64 v /\ gr Rc 26 = gr R 26 /\ gr Rc 27 = gr R 27.

  Lemma osrB_facts :
    nth 1 osrB (ELit 0) = EVar 1 /\ nth 2 osrB (ELit 0) = EVar 2 /\ nth 3 osrB (ELit 0) = EVar 3 /\ nth 4 osrB (ELit 0) = EVar 4
    /\ nth 8 osrB (ELit 0) = ELit 0 /\ nth 9 osrB (ELit 0) = ELit D
    /\ nth 11 osrB (ELit 0) = EVar 40   (* [comment removed for export] *)
    /\ nth 18 osrB (ELit 0) = EVar 18 /\ nth 19 osrB (ELit 0) = EVar 19 /\ nth 20 osrB (ELit 0) = ELit (D + 0x400008)
    /\ nth 22 osrB (ELit 0) = EVar 22 /\ nth 23 osrB (ELit 0) = ELit 2147483647 /\ nth 24 osrB (ELit 0) = ELit (D + 0x400010)
    /\ nth 25 osrB (ELit 0) = EVar 40
    /\ nth 26 osrB (ELit 0) = EVar 26 /\ nth 27 osrB (ELit 0) = EVar 27.
  Proof. repeat split; reflexivity. Qed.

  Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.   (* [comment removed for export] *)
  Lemma stepB : forall RA h, ARegs RA h ->
    exists RB v, msteps ASEGS (mkst RA (Z_to_bv 64 PC_HASHED) MA rom) (mkst RB (Z_to_bv 64 PC_LOOP) MA rom)
      /\ LRegs RB h v v /\ 0 <= v <= N /\ rdw ASEGS MA (bkt h) 4 v.
  Proof.
    intros RA h HA. dinv.
    set (b := bv_unsigned h mod 2 ^ 20).
    assert (Hb : 0 <= b < 2 ^ 20) by (subst b; apply Z.mod_pos_bound; lia).
    destruct (TAB b Hb) as (v & Hv & Bv).
    assert (Hbk : bkt h = D + 4 * b) by (unfold bkt; subst b; lia).
    destruct HA as (A1 & A2 & A3 & A4 & A8 & A9 & A13 & A18 & A19 & A22 & A23 & A26 & A27).
    set (EB := ENV RA (Z_to_bv 64 v) w1 (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (EB18 : bv_unsigned (edenot EB (EVar 18)) = bkt h).
    { subst EB. rewrite EV_lo by lia. rewrite A18. apply u_lit. unfold bkt, D. lia. }
    assert (EB40 : edenot EB (EVar 40) = Z_to_bv 64 v) by (subst EB; rewrite EV_hi by lia; reflexivity).
    assert (HRB : regs_ok EB srB RA).
    { apply regs_ok_ENV with (lits := [8; 9; 13; 23]%nat); [vm_compute; reflexivity|].
      repeat apply Forall_cons; try apply Forall_nil.
      - change (nth 8 srB (ELit 0)) with (ELit 0). exact A8.
      - change (nth 9 srB (ELit 0)) with (ELit D). exact A9.
      - change (nth 13 srB (ELit 0)) with (ELit 0x400000). exact A13.
      - change (nth 23 srB (ELit 0)) with (ELit 0x7fffffff). exact A23. }
    assert (HKB : know_ok ASEGS EB MA knB).
    { unfold knB, know_ok. repeat apply Forall_cons; try apply Forall_nil.
      - apply (kword_intro EB MA (EVar 18) 0 4 (EVar 40) (bkt h)); rewrite ?EB18; try (unfold bkt, D in *; lia).
        rewrite EB40, Hbk. exact Hv.
      - apply krange_intro. rewrite EB40. rewrite u_lit by lia. lia.
      - apply krange_intro. rewrite EB18. unfold bkt, D in *. lia.
      - apply kalign_intro; [lia|]. rewrite EB18, Hbk. unfold D.
        replace (1608344 + 4 * b) with ((402086 + b) * 4) by lia. apply Z_mod_mult. }
    destruct (GB_ok EB RA MA rom HRB HKB ltac:(constructor)) as (RB & MB & MSB & HRB' & HKB' & OUTB & GRB).
    cbn [g_pc g_opc g_osr g_okn g_fp GB] in MSB, HRB', HKB', OUTB.
    assert (EMB : MB = MA) by (apply functional_extensionality; intros x; apply OUTB; constructor).
    rewrite EMB in MSB.
    exists RB, v. split; [exact MSB|].
    assert (RBv : forall i e, (0 < i < 32)%nat -> nth i osrB (ELit 0) = e -> gr RB i = edenot EB e).
    { intros i e Hi He. rewrite (reg_of EB _ RB i HRB' Hi), He. reflexivity. }
    destruct osrB_facts as (B1 & B2 & B3 & B4 & B8 & B9 & B11 & B18 & B19 & B20 & B22 & B23 & B24 & B25 & B26 & B27).
    split; [| split; [exact Bv | rewrite Hbk; exact Hv]].
    unfold LRegs.
    rewrite (RBv 1%nat _ ltac:(lia) B1), (RBv 2%nat _ ltac:(lia) B2), (RBv 3%nat _ ltac:(lia) B3), (RBv 4%nat _ ltac:(lia) B4).
    rewrite (RBv 8%nat _ ltac:(lia) B8), (RBv 9%nat _ ltac:(lia) B9), (RBv 11%nat _ ltac:(lia) B11).
    rewrite (RBv 18%nat _ ltac:(lia) B18), (RBv 19%nat _ ltac:(lia) B19), (RBv 20%nat _ ltac:(lia) B20).
    rewrite (RBv 22%nat _ ltac:(lia) B22), (RBv 23%nat _ ltac:(lia) B23), (RBv 24%nat _ ltac:(lia) B24), (RBv 25%nat _ ltac:(lia) B25).
    rewrite (RBv 26%nat _ ltac:(lia) B26), (RBv 27%nat _ ltac:(lia) B27).
    rewrite EB40. rewrite !val_lit.
    subst EB. rewrite !EV_lo by lia.
    rewrite ?A1, ?A2, ?A3, ?A4, ?A8, ?A9, ?A18, ?A19, ?A22, ?A23, ?A26, ?A27.
    repeat split; reflexivity.
  Qed.
  Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].

  (* [comment removed for export] *)
  Lemma frameL_ok : forall Rc a40 a41 hw lk sz,
    gr Rc 2 = Z_to_bv 64 (sp - 112) -> (sz = EVar 56 \/ sz = ELit s) ->
    know_ok ASEGS (ENV Rc a40 a41 hw lk) MA (frameL sz).
  Proof.
    intros Rc a40 a41 hw lk sz H2 Hsz. unfold ACEILZ in *.
    destruct HFR as (F1 & F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & Fs & Ftr).
    set (E := ENV Rc a40 a41 hw lk).
    assert (E2 : bv_unsigned (edenot E (EVar 2)) = sp - 112).
    { subst E. rewrite EV_lo by lia. rewrite H2. apply u_lit. lia. }
    assert (HV : forall i, (32 <= i)%nat -> edenot E (EVar i) = TABV a40 a41 hw lk i) by (intros; subst E; apply EV_hi; assumption).
    unfold frameL, know_ok. destruct Hsz as [-> | ->].
    all: repeat apply Forall_cons; try apply Forall_nil.
    all: try match goal with |- kentry_ok _ _ _ (KWord (SA (EVar 2) ?off) 8 ?v) =>
           apply (kword_intro E MA (EVar 2) off 8 v (sp - 112 + off)); rewrite ?E2; try lia;
           first [ rewrite HV by lia; cbn [TABV] | rewrite val_lit ];
           match goal with F : rdn _ MA (Z_to_bv 64 (sp - ?k)) 8 = Some _ |- rdn _ _ (Z_to_bv 64 ?a) 8 = _ =>
             replace a with (sp - k) by lia; exact F end end.
    all: try (apply kalign_intro; [lia|]; rewrite E2; rewrite Zminus_mod, Hsp16; reflexivity).
    all: try (apply krange_intro; rewrite E2; unfold ACEILZ; lia).
    all: apply (kwr_intro E MA (EVar 2) (-160) 272 (sp - 272)); rewrite ?E2; try lia; exact wr_frameA.
  Qed.

  (* [comment removed for export] *)
  Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.   (* [comment removed for export] *)
  Lemma node_facts : forall cur, 1 <= cur <= N ->
    exists (hw : word) (lk : Z),
      rdn ASEGS MA (Z_to_bv 64 (b17 + 16 * cur)) 8 = Some (word_to_le_bytes 8 hw)
      /\ rdw ASEGS MA (b17 + 16 * cur + 8) 4 lk /\ 0 <= lk < cur.
  Proof.
    intros cur Hcur. dinv.
    destruct (NODES cur Hcur) as (lk & Hlk & Blk).
    assert (Hst : store_ok ASEGS MA (Z_to_bv 64 (b17 + 16 * cur)) 8 = true) by (apply (W3 (16 * cur) 8%nat); lia).
    destruct (readable_rdn MA (b17 + 16 * cur) 8 ltac:(lia) ltac:(lia) Hst) as (bs & Hbs & Hl).
    exists (Z_to_bv 64 (bytes_le_to_Z bs)), lk. split; [apply rdn_as_word; [lia | exact Hbs | exact Hl] |]. split; assumption.
  Qed.
  Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].

  Lemma not_in_fp : forall x : word, ~ in_fp (depot_fp D SSA b17 b18) x ->
    ~ (SSA <= bv_unsigned x < SSA + 32) /\ ~ (D <= bv_unsigned x < D + 0x400018)
    /\ ~ (b17 <= bv_unsigned x < b17 + 2 ^ 20) /\ ~ (b18 <= bv_unsigned x < b18 + 8 * TCAP).
  Proof.
    intros x H. unfold in_fp, depot_fp in H.
    repeat split; intro C; apply H.
    - apply Exists_cons_hd. exact C.
    - apply Exists_cons_tl, Exists_cons_hd. exact C.
    - apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. exact C.
    - apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. exact C.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section AfterB.
  Variables (h : word) (v : Z).
  Hypothesis Hv : 0 <= v <= N.
  Hypothesis HBK : rdw ASEGS MA (bkt h) 4 v.

  Definition POST (R' : bvmap 5 word) (M' : word -> option byte) (id : Z) : Prop :=
    (forall i, In i KEPTI -> gr R' i = gr R i)
    /\ gr R' 10 = Z_to_bv 64 id /\ 1 <= id < 65535
    /\ DepotInv ASEGS D SSA K b17 b18 M'
    /\ (forall x : word, ~ (sp - 272 <= bv_unsigned x < sp) -> ~ in_fp (depot_fp D SSA b17 b18) x -> M' x = MA x)
    /\ mem_grows MA M'.

  Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.   (* [comment removed for export] *)
  Lemma bkt_range : D <= bkt h <= D + 4194300 /\ bkt h mod 4 = 0.
  Proof.
    unfold bkt. pose proof (Z.mod_pos_bound (bv_unsigned h) (2 ^ 20) ltac:(lia)) as Hm.
    split; [unfold D; lia|].
    replace (4 * (bv_unsigned h mod 2 ^ 20) + D) with ((bv_unsigned h mod 2 ^ 20 + 402086) * 4) by (unfold D; lia).
    apply Z_mod_mult.
  Qed.
  Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].

  (* [comment removed for export] *)
  Lemma regsL_ok : forall Rc a40 a41 hw lk cur, LRegs Rc h v cur -> regs_ok (ENV Rc a40 a41 hw lk) srL Rc.
  Proof.
    intros Rc a40 a41 hw lk cur HL.
    destruct HL as (C1 & C2 & C3 & C4 & C8 & C9 & C11 & C18 & C19 & C20 & C22 & C23 & C24 & C25 & C26 & C27).
    apply regs_ok_ENV with (lits := [8; 9; 20; 22; 23; 24]%nat); [vm_compute; reflexivity|].
    repeat apply Forall_cons; try apply Forall_nil.
    - change (nth 8 srL (ELit 0)) with (ELit 0). exact C8.
    - change (nth 9 srL (ELit 0)) with (ELit D). exact C9.
    - change (nth 20 srL (ELit 0)) with (ELit (D + 0x400008)). exact C20.
    - change (nth 22 srL (ELit 0)) with (ELit 65535). exact C22.
    - change (nth 23 srL (ELit 0)) with (ELit 2147483647). exact C23.
    - change (nth 24 srL (ELit 0)) with (ELit (D + 0x400010)). exact C24.
  Qed.

  Lemma regsE_ok : forall Rc a40 a41 hw lk, LRegs Rc h v 0 -> regs_ok (ENV Rc a40 a41 hw lk) srE Rc.
  Proof.
    intros Rc a40 a41 hw lk HL.
    destruct HL as (C1 & C2 & C3 & C4 & C8 & C9 & C11 & C18 & C19 & C20 & C22 & C23 & C24 & C25 & C26 & C27).
    apply regs_ok_ENV with (lits := [8; 9; 11; 20; 22; 23; 24]%nat); [vm_compute; reflexivity|].
    repeat apply Forall_cons; try apply Forall_nil.
    - change (nth 8 srE (ELit 0)) with (ELit 0). exact C8.
    - change (nth 9 srE (ELit 0)) with (ELit D). exact C9.
    - change (nth 11 srE (ELit 0)) with (ELit 0). exact C11.
    - change (nth 20 srE (ELit 0)) with (ELit (D + 0x400008)). exact C20.
    - change (nth 22 srE (ELit 0)) with (ELit 65535). exact C22.
    - change (nth 23 srE (ELit 0)) with (ELit 2147483647). exact C23.
    - change (nth 24 srE (ELit 0)) with (ELit (D + 0x400010)). exact C24.
  Qed.

  (* [comment removed for export] *)
  Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.   (* [comment removed for export] *)
  Lemma knL_ok : forall Rc cur hw lk,
    1 <= cur <= N -> LRegs Rc h v cur ->
    rdn ASEGS MA (Z_to_bv 64 (b17 + 16 * cur)) 8 = Some (word_to_le_bytes 8 hw) ->
    rdw ASEGS MA (b17 + 16 * cur + 8) 4 lk -> 0 <= lk < cur ->
    know_ok ASEGS (ENV Rc w0 w1 hw (Z_to_bv 64 lk)) MA knL.
  Proof.
    intros Rc cur hw lk Hcur HL Hhw Hlk Blk. dinv.
    pose proof HL as HL'.
    destruct HL' as (C1 & C2 & C3 & C4 & C8 & C9 & C11 & C18 & C19 & C20 & C22 & C23 & C24 & C25 & C26 & C27).
    set (E := ENV Rc w0 w1 hw (Z_to_bv 64 lk)).
    assert (HV : forall i, (32 <= i)%nat -> edenot E (EVar i) = TABV w0 w1 hw (Z_to_bv 64 lk) i) by (intros; subst E; apply EV_hi; assumption).
    assert (E11 : edenot E (EVar 11) = Z_to_bv 64 cur) by (subst E; rewrite EV_lo by lia; exact C11).
    assert (E47 : edenot E (EVar 47) = Z_to_bv 64 b17) by (rewrite HV by lia; reflexivity).
    assert (ENB : edenot E NB = Z_to_bv 64 (b17 + 16 * cur)) by (unfold NB; apply (val_node E (EVar 11) b17 cur E47 E11); lia).
    assert (E0 : bv_unsigned (edenot E (ELit 0)) = 0) by (rewrite val_lit; apply u_lit; lia).
    unfold knL. apply Forall_app. split; [apply frameL_ok; [exact C2 | left; reflexivity]|].
    unfold know_ok. unfold ACEILZ, DepotPutA.KHI. repeat apply Forall_cons; try apply Forall_nil.
    - apply krange_intro. rewrite E11, u_lit by lia. lia.
    - apply (kword_intro E MA (ELit 0) (D + 0x400010) 8 (EVar 47) (D + 0x400010)); rewrite ?E0; try (unfold D in *; lia).
      rewrite E47. exact R17.
    - apply krange_intro. rewrite E47, u_lit by lia. lia.
    - apply kalign_intro; [lia|]. rewrite E47, u_lit by lia. exact A17al.
    - apply (kwr_intro E MA (EVar 47) 0 1048576 b17); rewrite ?E47, ?u_lit by lia; try lia. exact W3.
    - apply (kword_intro E MA NB 0 8 (EVar 52) (b17 + 16 * cur)); rewrite ?ENB, ?u_lit by lia; try lia.
      rewrite HV by lia. cbn [TABV]. exact Hhw.
    - apply (kword_intro E MA NB 8 4 (EVar 53) (b17 + 16 * cur + 8)); rewrite ?ENB, ?u_lit by lia; try lia.
      rewrite HV by lia. cbn [TABV]. exact Hlk.
    - apply krange_intro. rewrite HV by lia. cbn [TABV]. rewrite u_lit by lia. lia.
  Qed.
  Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].

  Lemma osrLC_facts :
    nth 1 osrLC (ELit 0) = EVar 1 /\ nth 2 osrLC (ELit 0) = EVar 2 /\ nth 3 osrLC (ELit 0) = EVar 3 /\ nth 4 osrLC (ELit 0) = EVar 4
    /\ nth 8 osrLC (ELit 0) = ELit 0 /\ nth 9 osrLC (ELit 0) = ELit D /\ nth 11 osrLC (ELit 0) = EVar 53
    /\ nth 18 osrLC (ELit 0) = EVar 18 /\ nth 19 osrLC (ELit 0) = EVar 19 /\ nth 20 osrLC (ELit 0) = ELit (D + 0x400008)
    /\ nth 22 osrLC (ELit 0) = ELit 65535 /\ nth 23 osrLC (ELit 0) = ELit 2147483647 /\ nth 24 osrLC (ELit 0) = ELit (D + 0x400010)
    /\ nth 25 osrLC (ELit 0) = EVar 25 /\ nth 26 osrLC (ELit 0) = EVar 26 /\ nth 27 osrLC (ELit 0) = EVar 27.
  Proof. repeat split; reflexivity. Qed.

  (* [comment removed for export] *)
  Definition retregs (osr : list expr) (x10 : expr) : Prop :=
    nth 1 osr (ELit 0) = EVar 33 /\ nth 2 osr (ELit 0) = EAlu ALU_ADD (EVar 2) (ELit 112)
    /\ nth 3 osr (ELit 0) = EVar 3 /\ nth 4 osr (ELit 0) = EVar 4 /\ nth 8 osr (ELit 0) = EVar 34 /\ nth 9 osr (ELit 0) = EVar 35
    /\ nth 10 osr (ELit 0) = x10
    /\ nth 18 osr (ELit 0) = EVar 36 /\ nth 19 osr (ELit 0) = EVar 37 /\ nth 20 osr (ELit 0) = EVar 38 /\ nth 21 osr (ELit 0) = EVar 39
    /\ nth 22 osr (ELit 0) = EVar 42 /\ nth 23 osr (ELit 0) = EVar 43 /\ nth 24 osr (ELit 0) = EVar 54 /\ nth 25 osr (ELit 0) = EVar 55
    /\ nth 26 osr (ELit 0) = EVar 26 /\ nth 27 osr (ELit 0) = EVar 27.
  Lemma osrLF_facts : retregs osrLF (EVar 11).
  Proof. repeat split; reflexivity. Qed.
  Lemma osrE_facts : forall s0, s0 = 1 \/ s0 = 2 -> retregs (osrE s0) (EAlu ALU_ADD (EVar 45) (ELit 1)).
  Proof. intros s0 [-> | ->]; repeat split; reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma kept_of_retregs : forall Rc a40 a41 hw lk osr x10 R' cur,
    LRegs Rc h v cur -> retregs osr x10 -> regs_ok (ENV Rc a40 a41 hw lk) osr R' ->
    (forall i, In i KEPTI -> gr R' i = gr R i) /\ gr R' 10 = edenot (ENV Rc a40 a41 hw lk) x10.
  Proof.
    intros Rc a40 a41 hw lk osr x10 R' cur HL HO HR'. unfold ACEILZ in *.
    destruct HL as (C1 & C2 & C3 & C4 & C8 & C9 & C11 & C18 & C19 & C20 & C22 & C23 & C24 & C25 & C26 & C27).
    destruct HO as (O1 & O2 & O3 & O4 & O8 & O9 & O10 & O18 & O19 & O20 & O21 & O22 & O23 & O24 & O25 & O26 & O27).
    set (E := ENV Rc a40 a41 hw lk) in *.
    assert (Rv : forall i e, (0 < i < 32)%nat -> nth i osr (ELit 0) = e -> gr R' i = edenot E e).
    { intros i e Hi He. rewrite (reg_of E _ R' i HR' Hi), He. reflexivity. }
    split; [| exact (Rv 10%nat _ ltac:(lia) O10)].
    intros i Hi. unfold KEPTI in Hi. cbn [In] in Hi.
    repeat match type of Hi with _ \/ _ => destruct Hi as [<- | Hi] | False => destruct Hi end.
    all: match goal with |- getr _ (Z_to_bv 5 (Z.of_nat ?i)) = _ =>
           match goal with O : nth i _ (ELit 0) = _ |- _ => rewrite (Rv i _ ltac:(lia) O) end end.
    all: try (subst E; rewrite EV_hi by lia; reflexivity).
    all: try (subst E; rewrite EV_lo by lia; assumption).
    rewrite (val_add_lit E (EVar 2) 112 (sp - 112)) by (subst E; rewrite EV_lo by lia; exact C2).
    rewrite Hsp. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.   (* [comment removed for export] *)
  Lemma stepLF : forall Rc cur hw lk,
    1 <= cur <= N ->
    rdn ASEGS MA (Z_to_bv 64 (b17 + 16 * cur)) 8 = Some (word_to_le_bytes 8 hw) ->
    rdw ASEGS MA (b17 + 16 * cur + 8) 4 lk -> 0 <= lk < cur ->
    bv_unsigned hw = bv_unsigned h ->
    LRegs Rc h v cur ->
    exists R', msteps ASEGS (mkst Rc (Z_to_bv 64 PC_LOOP) MA rom) (mkst R' (Z_to_bv 64 PUT_RET) MA rom) /\ POST R' MA cur.
  Proof.
    intros Rc cur hw lk Hcur Hhw Hlk Blk Heq HL. dinv.
    set (E := ENV Rc w0 w1 hw (Z_to_bv 64 lk)).
    pose proof (knL_ok Rc cur hw lk Hcur HL Hhw Hlk Blk) as HKN. fold E in HKN.
    pose proof (regsL_ok Rc w0 w1 hw (Z_to_bv 64 lk) cur HL) as HR. fold E in HR.
    assert (HSC : scs_denot ASEGS MA E (g_scs GLF)).
    { cbn [g_scs GLF]. constructor; [|constructor]. cbn [sc_denot]. unfold branch_taken.
      replace (edenot E (EVar 19)) with h by (subst E; rewrite EV_lo by lia; symmetry; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HL)))))))))).
      replace (edenot E (EVar 52)) with hw by (subst E; rewrite EV_hi by lia; reflexivity).
      unfold bv_eqb. rewrite Heq, Z.eqb_refl. reflexivity. }
    destruct (GLF_ok E Rc MA rom HR HKN HSC) as (R' & M' & MS & HR' & HK' & OUT & GR).
    cbn [g_pc g_opc g_osr g_okn g_fp GLF] in MS, HR', HK', OUT.
    assert (EM : M' = MA) by (apply functional_extensionality; intros x; apply OUT; constructor).
    rewrite EM in MS. exists R'. split; [exact MS|].
    destruct (kept_of_retregs Rc w0 w1 hw (Z_to_bv 64 lk) osrLF (EVar 11) R' cur HL osrLF_facts HR') as [HKP H10].
    unfold POST. split; [exact HKP|]. split.
    { rewrite H10. subst E. rewrite EV_lo by lia. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HL))))))). }
    split; [lia|]. split.
    { apply (DepotInv_mono ASEGS D SSA (K + 1) K); [lia|]. exists (DST N T). exact HIS. }
    split; [intros; reflexivity | apply mem_grows_refl].
  Qed.
  Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].

  (* [comment removed for export] *)
  Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.   (* [comment removed for export] *)
  Lemma stepLC : forall Rc cur hw lk,
    1 <= cur <= N ->
    rdn ASEGS MA (Z_to_bv 64 (b17 + 16 * cur)) 8 = Some (word_to_le_bytes 8 hw) ->
    rdw ASEGS MA (b17 + 16 * cur + 8) 4 lk -> 0 <= lk < cur ->
    bv_unsigned hw <> bv_unsigned h ->
    LRegs Rc h v cur ->
    exists Rc', msteps ASEGS (mkst Rc (Z_to_bv 64 PC_LOOP) MA rom) (mkst Rc' (Z_to_bv 64 PC_LOOP) MA rom) /\ LRegs Rc' h v lk.
  Proof.
    intros Rc cur hw lk Hcur Hhw Hlk Blk Hne HL. dinv.
    set (E := ENV Rc w0 w1 hw (Z_to_bv 64 lk)).
    pose proof (knL_ok Rc cur hw lk Hcur HL Hhw Hlk Blk) as HKN. fold E in HKN.
    pose proof (regsL_ok Rc w0 w1 hw (Z_to_bv 64 lk) cur HL) as HR. fold E in HR.
    pose proof HL as HL'.
    destruct HL' as (C1 & C2 & C3 & C4 & C8 & C9 & C11 & C18 & C19 & C20 & C22 & C23 & C24 & C25 & C26 & C27).
    assert (HSC : scs_denot ASEGS MA E (g_scs GLC)).
    { cbn [g_scs GLC]. constructor; [|constructor]. cbn [sc_denot]. unfold branch_taken.
      replace (edenot E (EVar 19)) with h by (subst E; rewrite EV_lo by lia; symmetry; exact C19).
      replace (edenot E (EVar 52)) with hw by (subst E; rewrite EV_hi by lia; reflexivity).
      unfold bv_eqb. destruct (Z.eqb_spec (bv_unsigned h) (bv_unsigned hw)); [lia | reflexivity]. }
    destruct (GLC_ok E Rc MA rom HR HKN HSC) as (R' & M' & MS & HR' & HK' & OUT & GR).
    cbn [g_pc g_opc g_osr g_okn g_fp GLC] in MS, HR', HK', OUT.
    assert (EM : M' = MA) by (apply functional_extensionality; intros x; apply OUT; constructor).
    rewrite EM in MS. exists R'. split; [exact MS|].
    assert (Rv : forall i e, (0 < i < 32)%nat -> nth i osrLC (ELit 0) = e -> gr R' i = edenot E e).
    { intros i e Hi He. rewrite (reg_of E _ R' i HR' Hi), He. reflexivity. }
    destruct osrLC_facts as (O1 & O2 & O3 & O4 & O8 & O9 & O11 & O18 & O19 & O20 & O22 & O23 & O24 & O25 & O26 & O27).
    unfold LRegs.
    rewrite (Rv 1%nat _ ltac:(lia) O1), (Rv 2%nat _ ltac:(lia) O2), (Rv 3%nat _ ltac:(lia) O3), (Rv 4%nat _ ltac:(lia) O4).
    rewrite (Rv 8%nat _ ltac:(lia) O8), (Rv 9%nat _ ltac:(lia) O9), (Rv 11%nat _ ltac:(lia) O11).
    rewrite (Rv 18%nat _ ltac:(lia) O18), (Rv 19%nat _ ltac:(lia) O19), (Rv 20%nat _ ltac:(lia) O20).
    rewrite (Rv 22%nat _ ltac:(lia) O22), (Rv 23%nat _ ltac:(lia) O23), (Rv 24%nat _ ltac:(lia) O24), (Rv 25%nat _ ltac:(lia) O25).
    rewrite (Rv 26%nat _ ltac:(lia) O26), (Rv 27%nat _ ltac:(lia) O27).
    rewrite !val_lit. subst E. cbn [edenot ENV mkE ev Nat.ltb Nat.leb TABV].
    rewrite ?C1, ?C2, ?C3, ?C4, ?C18, ?C19, ?C25, ?C26, ?C27.
    repeat split; reflexivity.
  Qed.
  Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].

  (* [comment removed for export] *)
  Lemma stepE : forall Rc, LRegs Rc h v 0 ->
    exists R' M', msteps ASEGS (mkst Rc (Z_to_bv 64 PC_LOOP) MA rom) (mkst R' (Z_to_bv 64 PUT_RET) M' rom) /\ POST R' M' (N + 1).
  Proof.
    intros Rc HL. dinv. pose proof bkt_range as [Bk1 Bk2].
    set (bh := bv_unsigned h mod 2 ^ 20).
    assert (Hbh : bkt h = 4 * bh + D) by (unfold bkt; reflexivity).
    assert (Hbh2 : 0 <= bh < 2 ^ 20) by (subst bh; apply Z.mod_pos_bound; lia).
    pose proof HL as HL'.
    destruct HL' as (C1 & C2 & C3 & C4 & C8 & C9 & C11 & C18 & C19 & C20 & C22 & C23 & C24 & C25 & C26 & C27).
    set (E := ENV Rc w0 w1 (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HV : forall i, (32 <= i)%nat -> edenot E (EVar i) = TABV w0 w1 (Z_to_bv 64 0) (Z_to_bv 64 0) i) by (intros; subst E; apply EV_hi; assumption).
    assert (E0 : bv_unsigned (edenot E (ELit 0)) = 0) by (rewrite val_lit; apply u_lit; lia).
    assert (E2 : bv_unsigned (edenot E (EVar 2)) = sp - 112) by (subst E; rewrite EV_lo by lia; rewrite C2; apply u_lit; lia).
    assert (E18 : bv_unsigned (edenot E (EVar 18)) = bkt h) by (subst E; rewrite EV_lo by lia; rewrite C18; apply u_lit; lia).
    assert (E25 : edenot E (EVar 25) = Z_to_bv 64 v) by (subst E; rewrite EV_lo by lia; exact C25).
    assert (E44 : bv_unsigned (edenot E (EVar 44)) = tr) by (rewrite HV by lia; cbn [TABV]; apply u_lit; lia).
    assert (E45 : edenot E (EVar 45) = Z_to_bv 64 N) by (rewrite HV by lia; reflexivity).
    assert (E46 : edenot E (EVar 46) = Z_to_bv 64 T) by (rewrite HV by lia; reflexivity).
    assert (E47 : edenot E (EVar 47) = Z_to_bv 64 b17) by (rewrite HV by lia; reflexivity).
    assert (E48 : edenot E (EVar 48) = Z_to_bv 64 b18) by (rewrite HV by lia; reflexivity).
    assert (HR : regs_ok E srE Rc) by (apply regsE_ok; exact HL).
    assert (HKE : know_ok ASEGS E MA (knE s)).
    { unfold knE. apply Forall_app. split; [apply frameL_ok; [exact C2 | right; reflexivity]|].
      unfold know_ok. unfold ACEILZ, DepotPutA.KHI. repeat apply Forall_cons; try apply Forall_nil.
      - apply (kword_intro E MA (EVar 18) 0 4 (EVar 25) (bkt h)); rewrite ?E18; try lia. rewrite E25. exact HBK.
      - apply krange_intro. rewrite E25, u_lit by lia. lia.
      - apply krange_intro. rewrite E18. lia.
      - apply kalign_intro; [lia|]. rewrite E18. exact Bk2.
      - apply (kword_intro E MA (ELit 0) (D + 0x400000) 4 (EVar 45) (D + 0x400000)); rewrite ?E0; try lia. rewrite E45. exact RN.
      - apply krange_intro. rewrite E45, u_lit by lia. lia.
      - apply (kword_intro E MA (ELit 0) (D + 0x400010) 8 (EVar 47) (D + 0x400010)); rewrite ?E0; try lia. rewrite E47. exact R17.
      - apply krange_intro. rewrite E47, u_lit by lia. lia.
      - apply kalign_intro; [lia|]. rewrite E47, u_lit by lia. exact A17al.
      - apply (kwr_intro E MA (EVar 47) 0 1048576 b17); rewrite ?E47, ?u_lit by lia; try lia. exact W3.
      - apply (kword_intro E MA (ELit 0) SSA 8 (EVar 46) SSA); rewrite ?E0; try lia. rewrite E46. exact RT.
      - apply krange_intro. rewrite E46, u_lit by lia. lia.
      - apply (kword_intro E MA (ELit 0) (SSA + 24) 4 (EVar 46) (SSA + 24)); rewrite ?E0; try lia. rewrite E46. exact RC.
      - apply (kword_intro E MA (ELit 0) (SSA + 16) 8 (EVar 48) (SSA + 16)); rewrite ?E0; try lia. rewrite E48. exact R18.
      - apply krange_intro. rewrite E48, u_lit by lia. lia.
      - apply kalign_intro; [lia|]. rewrite E48, u_lit by lia. exact A18al.
      - apply (kwr_intro E MA (EVar 48) 0 4096 b18); rewrite ?E48, ?u_lit by lia; try lia. exact W4.
      - apply (kwr_intro E MA (ELit 0) D 0x400018 D); rewrite ?E0; try lia. exact W1.
      - apply (kwr_intro E MA (ELit 0) SSA 32 SSA); rewrite ?E0; try lia. exact W2.
      - apply (kword_intro E MA (EVar 44) 0 8 (EVar 40) tr); rewrite ?E44; try lia. rewrite HV by lia. cbn [TABV]. exact HwA0.
      - apply (kword_intro E MA (EVar 44) 8 8 (EVar 41) (tr + 8)); rewrite ?E44; try lia. rewrite HV by lia. cbn [TABV]. exact HwA1.
      - apply kalign_intro; [lia|]. rewrite E44. exact Htr8.
      - apply krange_intro. rewrite E44. lia.
      - apply kdisj_intro; rewrite ?E44, ?E2; lia.
      (* [comment removed for export] *)
      - apply kdisj_intro; rewrite ?E47, ?E2, ?u_lit by lia; pose proof Hb17sp as X; unfold disjZ, TCAP in *; lia.
      - apply kdisj_intro; rewrite ?E48, ?E2, ?u_lit by lia; pose proof Hb18sp as X; unfold disjZ, TCAP in *; lia.
      - apply kdisj_intro; rewrite ?E47, ?E44, ?u_lit by lia; pose proof Hb17tr as X; unfold disjZ, TCAP in *; lia.
      - apply kdisj_intro; rewrite ?E48, ?E44, ?u_lit by lia; pose proof Hb18tr as X; unfold disjZ, TCAP in *; lia.
      - apply kdisj_intro; rewrite ?E47, ?E48, ?u_lit by lia; unfold TCAP in *; lia.
      - apply kimg_intro; [lia | lia | exact HimgA]. }
    destruct (GE_ok s Hs12 E Rc MA rom HR HKE ltac:(constructor)) as (R' & M' & MS & HR' & HK' & OUT & GR).
    cbn [g_pc g_opc g_osr g_okn g_fp GE] in MS, HR', HK', OUT.
    exists R', M'. split; [exact MS|].
    (* [comment removed for export] *)
    rewrite (oknEs_shape s Hs12) in HK'. unfold know_ok in HK'.
    apply Forall_cons_iff in HK' as [Kbk HK']. apply Forall_cons_iff in HK' as [Klk HK']. apply Forall_cons_iff in HK' as [KN HK'].
    apply Forall_cons_iff in HK' as [KT HK']. apply Forall_cons_iff in HK' as [KC HK']. apply Forall_cons_iff in HK' as [K17 HK'].
    apply Forall_cons_iff in HK' as [K18 HK'].
    assert (E45' : edenot E (EAlu ALU_ADD (EVar 45) (ELit 1)) = Z_to_bv 64 (N + 1)) by (apply val_add_lit; exact E45).
    assert (ENBn : edenot E NBn = Z_to_bv 64 (b17 + 16 * N)) by (unfold NBn; apply (val_node E _ b17 N E47 E45); lia).
    assert (EFBt : edenot E FBt = Z_to_bv 64 (b18 + 8 * T)) by (apply (val_slot E b18 T E48 E46); lia).
    apply (kword_elim E M' (EVar 18) 0 4 _ (bkt h)) in Kbk; [|exact E18].
    apply (kword_elim E M' NBn 24 4 _ (b17 + 16 * N)) in Klk; [| rewrite ENBn; apply u_lit; lia].
    replace (b17 + 16 * N + 24) with (b17 + 16 * (N + 1) + 8) in Klk by lia.
    apply (kword_elim E M' (ELit 0) _ 4 _ 0) in KN; [|exact E0].
    apply (kword_elim E M' (ELit 0) _ 8 _ 0) in KT; [|exact E0].
    apply (kword_elim E M' (ELit 0) _ 4 _ 0) in KC; [|exact E0].
    apply (kword_elim E M' (ELit 0) _ 8 _ 0) in K17; [|exact E0].
    apply (kword_elim E M' (ELit 0) _ 8 _ 0) in K18; [|exact E0].
    rewrite E45' in Kbk. rewrite E25 in Klk.
    rewrite (val_add_lit E (EVar 45) 1 N E45) in KN.   (* [comment removed for export] *)
    rewrite (val_add_lit E (EVar 46) (s + 1) T E46) in KT.
    rewrite (val_add_lit E (EVar 46) (s + 1) T E46) in KC.
    rewrite E47 in K17. rewrite E48 in K18.
    replace (bkt h + 0) with (bkt h) in Kbk by lia.
    replace (0 + (D + 4194304)) with (D + 4194304) in KN by lia.
    replace (0 + SSA) with SSA in KT by lia.
    replace (0 + (SSA + 24)) with (SSA + 24) in KC by lia.
    replace (0 + (D + 4194320)) with (D + 4194320) in K17 by lia.
    replace (0 + (SSA + 16)) with (SSA + 16) in K18 by lia.
    (* [comment removed for export] *)
    assert (OUT' : forall x : word,
      ~ (sp - 224 <= bv_unsigned x < sp - 112) -> ~ (bkt h <= bv_unsigned x < bkt h + 4) ->
      ~ (SSA <= bv_unsigned x < SSA + 8) -> ~ (SSA + 24 <= bv_unsigned x < SSA + 28) ->
      ~ (D + 0x400000 <= bv_unsigned x < D + 0x400004) ->
      ~ (b17 + 16 * (N + 1) <= bv_unsigned x < b17 + 16 * (N + 1) + 16) ->
      ~ (b18 + 8 * T <= bv_unsigned x < b18 + 8 * T + (8 + 8 * s)) -> M' x = MA x).
    { assert (Bnb : 0 <= b17 + 16 * N < 2 ^ 64) by lia.
      assert (Bfb : 0 <= b18 + 8 * T < 2 ^ 64) by lia.
      intros x X1 X2 X3 X4 X5 X6 X7. apply OUT.
      exact (out_fpE_of E x s sp (bkt h) _ _ b17 b18 N T E2 E18 E0 ENBn Bnb eq_refl EFBt Bfb eq_refl X1 X2 X3 X4 X5 X6 X7). }
    destruct (kept_of_retregs Rc w0 w1 (Z_to_bv 64 0) (Z_to_bv 64 0) (osrE s) _ R' 0 HL (osrE_facts s Hs12) HR') as [HKP H10].
    unfold POST. split; [exact HKP|].
    split; [rewrite H10; exact E45'|].
    split; [lia|].
    split.
    { exists (DST (N + 1) (T + s + 1)). unfold DepotInvS. cbn [d_N d_T]. unfold TCAP, IMGHI, VATOP.
      replace (T + s + 1) with (T + (s + 1)) by lia.
      repeat match goal with |- _ /\ _ => split end; try lia; try assumption.
      - eapply wr_ok_mono; [exact GR | exact W1].
      - eapply wr_ok_mono; [exact GR | exact W2].
      - eapply wr_ok_mono; [exact GR | exact W3].
      - eapply wr_ok_mono; [exact GR | exact W4].
      - intros b' Hb'. destruct (Z.eq_dec b' bh) as [-> | Nb].
        + exists (N + 1). split; [|lia]. replace (D + 4 * bh) with (bkt h) by lia. exact Kbk.
        + destruct (TAB b' Hb') as (v' & Rv' & Bv'). exists v'. split; [|lia].
          apply (rdw_frame ASEGS MA M'); [lia | lia | | exact Rv']. intros x Hx. apply OUT'; lia.
      - intros i Hi. destruct (Z.eq_dec i (N + 1)) as [-> | Hne'].
        + exists v. split; [exact Klk | lia].
        + destruct (NODES i ltac:(lia)) as (l & Rl & Bl). exists l. split; [|lia].
          apply (rdw_frame ASEGS MA M'); [lia | lia | | exact Rl]. intros x Hx.
          pose proof Hb17sp as XD1. unfold disjZ in XD1. apply OUT'; lia. }
    split; [|exact GR].
    intros x Hx1 Hx2. apply not_in_fp in Hx2 as (X1 & X2 & X3 & X4). unfold TCAP in X4.
    assert (Hs' : 1 <= s <= 2) by (clear - Hs12; lia).
    apply OUT'; clear - Hx1 X1 X2 X3 X4 Bk1 Bk2 HN HNK HT HTK HK Hs'; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma loop : forall n cur Rc, (Z.to_nat cur < n)%nat -> 0 <= cur <= N -> LRegs Rc h v cur ->
    exists R' M' id, msteps ASEGS (mkst Rc (Z_to_bv 64 PC_LOOP) MA rom) (mkst R' (Z_to_bv 64 PUT_RET) M' rom) /\ POST R' M' id.
  Proof.
    induction n as [|n IH]; intros cur Rc Hn Hcur HL; [lia|].
    destruct (Z.eq_dec cur 0) as [Hz | Hnz].
    - rewrite Hz in HL. destruct (stepE Rc HL) as (R' & M' & MS & HP). exists R', M', (N + 1). split; assumption.
    - destruct (node_facts cur ltac:(lia)) as (hw & lk & Hhw & Hlk & Blk).
      destruct (Z.eq_dec (bv_unsigned hw) (bv_unsigned h)) as [Heq | Hne].
      + destruct (stepLF Rc cur hw lk ltac:(lia) Hhw Hlk Blk Heq HL) as (R' & MS & HP). exists R', MA, cur. split; assumption.
      + destruct (stepLC Rc cur hw lk ltac:(lia) Hhw Hlk Blk Hne HL) as (Rc' & MS & HL').
        destruct (IH lk Rc' ltac:(lia) ltac:(lia) HL') as (R' & M' & id & MS' & HP).
        exists R', M', id. split; [eapply msteps_trans; [exact MS | exact MS'] | exact HP].
  Qed.

  End AfterB.
  End AfterA.
  End Inv.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem as_depot_put_main : DepotInv ASEGS D SSA (K + 1) b17 b18 M ->
    exists R' M' id,
      msteps ASEGS (mkst R (Z_to_bv 64 PUT_PC) M rom) (mkst R' (Z_to_bv 64 PUT_RET) M' rom)
      /\ (forall i, In i KEPTI -> gr R' i = gr R i)
      /\ gr R' 10 = Z_to_bv 64 id /\ 1 <= id < 65535
      /\ DepotInv ASEGS D SSA K b17 b18 M'
      /\ (forall x : word, ~ (sp - 272 <= bv_unsigned x < sp) -> ~ in_fp (depot_fp D SSA b17 b18) x -> M' x = M x)
      /\ mem_grows M M'.
  Proof.
    intros HI. unfold ACEILZ in *.
    (* [comment removed for export] *)
    assert (Hrd0 : store_ok ASEGS M (Z_to_bv 64 tr) 8 = true).
    { apply (StoreOk.store_ok_sub ASEGS M (Z_to_bv 64 tr) _ 16 8); rewrite ?u_lit by lia; try lia. exact Htrok. }
    assert (Hrd1 : store_ok ASEGS M (Z_to_bv 64 (tr + 8)) 8 = true).
    { apply (StoreOk.store_ok_sub ASEGS M (Z_to_bv 64 tr) _ 16 8); rewrite ?u_lit by lia; try lia. exact Htrok. }
    destruct (readable_rdn M tr 8 ltac:(lia) ltac:(lia) Hrd0) as (bs0 & Hbs0 & Hl0).
    destruct (readable_rdn M (tr + 8) 8 ltac:(lia) ltac:(lia) Hrd1) as (bs1 & Hbs1 & Hl1).
    pose proof (rdn_as_word M _ 8 bs0 ltac:(lia) Hbs0 Hl0) as Hw0.
    pose proof (rdn_as_word M _ 8 bs1 ltac:(lia) Hbs1 Hl1) as Hw1.
    set (w0 := Z_to_bv 64 (bytes_le_to_Z bs0)) in Hw0. set (w1 := Z_to_bv 64 (bytes_le_to_Z bs1)) in Hw1.
    (* [comment removed for export] *)
    destruct (stepA 0 0 w0 w1 Hw0 Hw1) as (RA & MA & h & MSA & HA & HFR & MAout & MAgr).
    (* [comment removed for export] *)
    assert (HIA : DepotInv ASEGS D SSA (K + 1) b17 b18 MA).
    { pose proof HI as HI0. destruct HI0 as [[N0 T0] X]. unfold DepotInvS in X. cbn [d_N d_T] in X.
      unfold TCAP, IMGHI, VATOP in X.
      destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & A1 & A2 & _ & A4 & A5 & _ & _ & L1 & L2 & L3 & _).
      apply (DepotInv_frame ASEGS D SSA (K + 1) b17 b18 M MA); [|exact HI].
      intros x Hx. apply MAout. intros C. unfold in_fp, depot_fp, TCAP in *.
      apply Exists_exists in Hx as (it & Hin & Hit).
      pose proof Hb17sp as X1. pose proof Hb18sp as X2. unfold disjZ, TCAP in X1, X2.
      destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Hit; lia. }
    destruct HIA as [[N T] HIS].
    destruct (stepB N T w1 MA HIS RA h HA) as (RB & v & MSB & HLB & Hv & HBK).
    destruct (loop N T w0 w1 Hw0 Hw1 MA HFR MAout MAgr HIS h v Hv HBK (S (Z.to_nat v)) v RB ltac:(lia) ltac:(lia) HLB)
      as (R' & M' & id & MSL & HP).
    exists R', M', id.
    split. { eapply msteps_trans; [exact MSA|]. eapply msteps_trans; [exact MSB | exact MSL]. }
    unfold POST in HP. destruct HP as (P1 & P2 & P3 & P4 & P5 & P6).
    split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split.
    - intros x Hx1 Hx2. rewrite (P5 x Hx1 Hx2). apply MAout. lia.
    - intros x Hx. apply P6. apply MAgr. exact Hx.
  Qed.
End Put.

(* [comment removed for export] *)
Theorem as_depot_put :
  forall (R : bvmap 5 word) (M rom : word -> option byte) (sp tr s K b17 b18 : Z),
    getr R (Z_to_bv 5 2) = Z_to_bv 64 sp -> sp mod 16 = 0 -> ACEILZ <= sp - 272 -> sp <= 2 ^ 47 ->
    getr R (Z_to_bv 5 10) = Z_to_bv 64 tr -> tr mod 8 = 0 -> ACEILZ <= tr -> tr + 16 <= 2 ^ 47 ->
    getr R (Z_to_bv 5 11) = Z_to_bv 64 s -> 1 <= s <= 2 ->
    store_ok ASEGS M (Z_to_bv 64 (sp - 272)) 272 = true ->
    store_ok ASEGS M (Z_to_bv 64 tr) 16 = true ->
    (tr + 16 <= sp - 272 \/ sp <= tr) ->
    (forall i, 0x10000 <= i < 0x30000 -> M (Z_to_bv 64 i) = None) ->
    0 <= K ->
    disjZ b17 (2 ^ 20) (sp - 272) 272 -> disjZ b18 (8 * TCAP) (sp - 272) 272 ->
    disjZ b17 (2 ^ 20) tr 16 -> disjZ b18 (8 * TCAP) tr 16 ->
    DepotInv ASEGS D SSA (K + 1) b17 b18 M ->
    exists R' M' id,
      msteps ASEGS (mkst R (Z_to_bv 64 PUT_PC) M rom) (mkst R' (Z_to_bv 64 PUT_RET) M' rom)
      /\ (forall i, In i KEPTI -> getr R' (Z_to_bv 5 (Z.of_nat i)) = getr R (Z_to_bv 5 (Z.of_nat i)))
      /\ getr R' (Z_to_bv 5 10) = Z_to_bv 64 id /\ 1 <= id < 65535
      /\ DepotInv ASEGS D SSA K b17 b18 M'
      /\ (forall x : word, ~ (sp - 272 <= bv_unsigned x < sp) -> ~ in_fp (depot_fp D SSA b17 b18) x -> M' x = M x)
      /\ mem_grows M M'.
Proof.
  intros R M rom sp tr s K b17 b18 Hsp Hsp16 Hsplo Hsphi Htr Htr8 Htrlo Htrhi Hs Hs12 Hframe Htrok Hapart Himg HK H1 H2 H3 H4 HI.
  exact (as_depot_put_main R M rom sp tr s K b17 b18 Hsp Hsp16 Hsplo Hsphi Htr Htr8 Htrlo Htrhi Hs ltac:(lia) Hframe Htrok Hapart Himg HK
           H1 H2 H3 H4 HI).
Qed.
End WithFP2.

