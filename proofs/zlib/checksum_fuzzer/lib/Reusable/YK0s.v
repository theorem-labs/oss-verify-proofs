(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11 YK0h YK0i YK14.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Section f.
Context {fx : FPState}.
Definition at_ (base : word) (d : Z) : word := Z_to_bv 64 (bv_unsigned base + d).
Lemma at_0 : forall base, at_ base 0 = base.
Proof.
intros base. unfold at_. rewrite Z.add_0_r. apply bv_eq.
rewrite Z_to_bv_unsigned. apply bv_wrap_small, bv_unsigned_in_range.
Qed.
Lemma at_addi : forall base d e, v_addi (at_ base d) e = at_ base (d + e).
Proof.
intros base d e. unfold at_, v_addi. apply bv_eq.
rewrite !Z_to_bv_unsigned. unfold bv_wrap.
rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.
Lemma at_btgt : forall base d e, btgt (at_ base d) e = at_ base (d + e).
Proof. intros. unfold btgt. apply at_addi. Qed.
Lemma at_lit : forall (base : word) (d : Z) (a : word),
Z_to_bv 64 (bv_unsigned base + d) = a -> at_ base d = a.
Proof. intros. assumption. Qed.
Lemma at_at : forall base d e, at_ (at_ base d) e = at_ base (d + e).
Proof. exact at_addi. Qed.
Lemma u_succ_shift : forall (a : word) (i : Z),
Z_to_bv 64 (bv_unsigned (a + 1) + i) = Z_to_bv 64 (bv_unsigned a + (1 + i)).
Proof.
intros a i. apply bv_eq. rewrite !Z_to_bv_unsigned, bv_add_unsigned.
assert (H1 : bv_unsigned (1 : word) = 1%Z) by reflexivity. rewrite H1.
unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.
Lemma at_self : forall a : word, Z_to_bv 64 (bv_unsigned a + 0) = a.
Proof. intros a. exact (at_0 a). Qed.
Definition assn := bvmap 5 word -> (word -> option byte) -> (word -> option byte) -> Prop.
Definition regset := reg -> Prop.
Definition memset := word -> Prop.
Definition regs_agree (C : regset) (regs regs' : bvmap 5 word) : Prop :=
forall r, ~ C r -> getr regs' r = getr regs r.
Definition mem_agree (W : memset) (m m' : word -> option byte) : Prop :=
forall x, ~ W x -> m' x = m x.
Lemma regs_agree_refl : forall C regs, regs_agree C regs regs.
Proof. intros C regs r _. reflexivity. Qed.
Lemma mem_agree_refl : forall W m, mem_agree W m m.
Proof. intros W m x _. reflexivity. Qed.
Lemma regs_agree_trans : forall C regs1 regs2 regs3,
regs_agree C regs1 regs2 -> regs_agree C regs2 regs3 -> regs_agree C regs1 regs3.
Proof. intros C r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). apply H1, Hr. Qed.
Lemma mem_agree_trans : forall W m1 m2 m3,
mem_agree W m1 m2 -> mem_agree W m2 m3 -> mem_agree W m1 m3.
Proof. intros W m1 m2 m3 H1 H2 x Hx. rewrite (H2 x Hx). apply H1, Hx. Qed.
Lemma regs_agree_mono : forall (C C' : regset) regs regs',
(forall r, C r -> C' r) -> regs_agree C regs regs' -> regs_agree C' regs regs'.
Proof. intros C C' regs regs' Hsub H r Hr. apply H. intro; apply Hr, Hsub; assumption. Qed.
Lemma mem_agree_mono : forall (W W' : memset) m m',
(forall x, W x -> W' x) -> mem_agree W m m' -> mem_agree W' m m'.
Proof. intros W W' m m' Hsub H x Hx. apply H. intro; apply Hx, Hsub; assumption. Qed.
Lemma regs_agree_upd : forall (C : regset) regs regs' r v,
C r -> regs_agree C regs regs' -> regs_agree C regs (regupd regs' r v).
Proof.
intros C regs regs' r v Hin H s Hs.
rewrite getr_other by (intro Heq; subst; contradiction).
apply H, Hs.
Qed.
Lemma mem_agree_wbytes : forall (W : memset) m m' a bs,
(forall i, (0 <= i < Z.of_nat (length bs))%Z -> W (Z_to_bv 64 (bv_unsigned a + i))) ->
mem_agree W m m' -> mem_agree W m (wbytes m' a bs).
Proof.
intros W m m' a bs. revert m' a.
induction bs as [|b bs IH]; intros m' a Hin H; cbn [wbytes] in *; [exact H|].
assert (Ha : W a).
{ specialize (Hin 0%Z ltac:(cbn [length]; lia)). rewrite at_self in Hin. exact Hin. }
apply IH.
- intros i Hi. rewrite u_succ_shift. apply Hin. cbn [length] in *. lia.
- intros x Hx. cbn beta. destruct (bv_eqb x a) eqn:Heq.
+ exfalso. apply Hx. unfold bv_eqb in Heq. apply Z.eqb_eq, bv_eq in Heq.
subst x. exact Ha.
+ apply H, Hx.
Qed.
Definition triple (segs : list Segment)
(C : regset) (W : memset)
(P : assn) (a b : word) (Q : assn) : Prop :=
forall regs mem rom, P regs mem rom ->
exists regs' mem',
msteps segs (mkst regs a mem rom) (mkst regs' b mem' rom)
/\ Q regs' mem' rom
/\ regs_agree C regs regs'
/\ mem_agree W mem mem'.
Lemma triple_intro : forall segs C W P a b Q,
(forall regs mem rom, P regs mem rom ->
exists regs' mem',
msteps segs (mkst regs a mem rom) (mkst regs' b mem' rom)
/\ Q regs' mem' rom
/\ regs_agree C regs regs'
/\ mem_agree W mem mem') ->
triple segs C W P a b Q.
Proof. intros; assumption. Qed.
Lemma triple_skip : forall segs C W P a, triple segs C W P a a P.
Proof.
intros segs C W P a regs mem rom HP.
exists regs, mem. split; [apply mst_refl|].
split; [exact HP|]. split; [apply regs_agree_refl|apply mem_agree_refl].
Qed.
Lemma triple_seq : forall segs C1 W1 C2 W2 P Q R a b c,
triple segs C1 W1 P a b Q ->
triple segs C2 W2 Q b c R ->
triple segs (fun r => C1 r \/ C2 r) (fun x => W1 x \/ W2 x) P a c R.
Proof.
intros segs C1 W1 C2 W2 P Q R a b c H1 H2 regs mem rom HP.
destruct (H1 _ _ _ HP) as (regs1 & mem1 & Hst1 & HQ & Hr1 & Hm1).
destruct (H2 _ _ _ HQ) as (regs2 & mem2 & Hst2 & HR & Hr2 & Hm2).
exists regs2, mem2. split; [eapply msteps_trans; eassumption|].
split; [exact HR|]. split.
- eapply regs_agree_trans;
[ eapply regs_agree_mono; [|exact Hr1]
| eapply regs_agree_mono; [|exact Hr2] ]; auto.
- eapply mem_agree_trans;
[ eapply mem_agree_mono; [|exact Hm1]
| eapply mem_agree_mono; [|exact Hm2] ]; auto.
Qed.
Lemma triple_conseq : forall segs C C' W W' P P' Q Q' a b,
triple segs C W P a b Q ->
(forall regs mem rom, P' regs mem rom -> P regs mem rom) ->
(forall regs mem rom, Q regs mem rom -> Q' regs mem rom) ->
(forall r, C r -> C' r) ->
(forall x, W x -> W' x) ->
triple segs C' W' P' a b Q'.
Proof.
intros segs C C' W W' P P' Q Q' a b H HP HQ HC HW regs mem rom HP'.
destruct (H _ _ _ (HP _ _ _ HP')) as (regs' & mem' & Hst & HQ0 & Hr & Hm).
exists regs', mem'. split; [exact Hst|]. split; [apply HQ, HQ0|].
split; [eapply regs_agree_mono; eauto | eapply mem_agree_mono; eauto].
Qed.
Lemma triple_seq_same : forall segs C W P Q R a b c,
triple segs C W P a b Q ->
triple segs C W Q b c R ->
triple segs C W P a c R.
Proof.
intros segs C W P Q R a b c H1 H2 regs mem rom HP.
destruct (H1 _ _ _ HP) as (regs1 & mem1 & Hst1 & HQ & Hr1 & Hm1).
destruct (H2 _ _ _ HQ) as (regs2 & mem2 & Hst2 & HR & Hr2 & Hm2).
exists regs2, mem2. split; [eapply msteps_trans; eassumption|].
split; [exact HR|].
split; [eapply regs_agree_trans; eassumption | eapply mem_agree_trans; eassumption].
Qed.
Definition frameable (C : regset) (W : memset) (R : assn) : Prop :=
forall regs mem rom regs' mem',
regs_agree C regs regs' -> mem_agree W mem mem' ->
R regs mem rom -> R regs' mem' rom.
Lemma triple_frame : forall segs C W P Q R a b,
triple segs C W P a b Q ->
frameable C W R ->
triple segs C W (fun regs mem rom => P regs mem rom /\ R regs mem rom) a b
(fun regs mem rom => Q regs mem rom /\ R regs mem rom).
Proof.
intros segs C W P Q R a b H HR regs mem rom (HP & HRr).
destruct (H _ _ _ HP) as (regs' & mem' & Hst & HQ & Hr & Hm).
exists regs', mem'. split; [exact Hst|].
split; [split; [exact HQ | eapply HR; eassumption]|].
split; assumption.
Qed.
Lemma frameable_and : forall C W R1 R2,
frameable C W R1 -> frameable C W R2 ->
frameable C W (fun regs mem rom => R1 regs mem rom /\ R2 regs mem rom).
Proof. intros C W R1 R2 H1 H2 regs mem rom regs' mem' Hr Hm (A & B); split; eauto. Qed.
Lemma frameable_reg : forall (C : regset) W (r : reg) (v : word),
~ C r -> frameable C W (fun regs _ _ => getr regs r = v).
Proof.
intros C W r v Hnc regs mem rom regs' mem' Hr _ Hv.
rewrite (Hr r Hnc). exact Hv.
Qed.
Lemma frameable_rdn : forall segs (C : regset) (W : memset) (a : word) (n : nat) bs,
(forall i, (0 <= i < Z.of_nat n)%Z -> ~ W (Z_to_bv 64 (bv_unsigned a + i))) ->
frameable C W (fun _ mem _ => rdn segs mem a n = Some bs).
Proof.
intros segs C W a n bs Hdisj regs mem rom regs' mem' _ Hm Hrd.
rewrite <- Hrd. clear Hrd bs. revert a Hdisj.
induction n as [|n IH]; intros a Hdisj; [reflexivity|].
assert (Ha : ~ W a).
{ specialize (Hdisj 0%Z ltac:(lia)). rewrite at_self in Hdisj. exact Hdisj. }
cbn [rdn]. rewrite (Hm a Ha). rewrite IH; [reflexivity|].
intros i Hi. rewrite u_succ_shift. apply Hdisj. lia.
Qed.
Definition ret_ok (k : word) : Prop := v_jalr k 0 = k.
Lemma land_m2_even : forall z : Z, (z mod 2 = 0)%Z -> Z.land z (-2) = z.
Proof.
intros z Hz.
assert (Hl : Z.land z 1 = 0%Z).
{ replace 1%Z with (Z.ones 1) by reflexivity. rewrite Z.land_ones by lia. exact Hz. }
replace (-2)%Z with (Z.lnot 1) by reflexivity.
rewrite <- Z.ldiff_land.
rewrite <- (Z.lor_ldiff_and z 1) at 2.
rewrite Hl, Z.lor_0_r. reflexivity.
Qed.
Lemma ret_ok_even : forall k, (bv_unsigned k mod 2 = 0)%Z -> ret_ok k.
Proof.
intros k Hk. unfold ret_ok, v_jalr, jalr_tgtZ.
rewrite Z.add_0_r, land_m2_even by exact Hk.
apply bv_eq. rewrite Z_to_bv_unsigned.
apply bv_wrap_small, bv_unsigned_in_range.
Qed.
Definition proc (segs : list Segment) (C : regset) (W : memset)
(P : assn) (entry : word) (Q : assn) : Prop :=
forall k : word, ret_ok k ->
triple segs C W (fun regs mem rom => P regs mem rom /\ getr regs 1 = k) entry k Q.
Definition ra_indep (P : assn) : Prop :=
forall regs v mem rom, P regs mem rom -> P (regupd regs 1 v) mem rom.
Lemma triple_call : forall segs C W P Q callsite entry ret,
(forall regs mem rom,
RiscvSemantics.step segs (mkst regs callsite mem rom)
= MachineOk (mkst (regupd regs 1 ret) entry mem rom)) ->
ret_ok ret ->
ra_indep P ->
proc segs C W P entry Q ->
triple segs (fun r => C r \/ r = 1) W P callsite ret Q.
Proof.
intros segs C W P Q callsite entry ret Hjal Hret HraP Hproc regs mem rom HP.
assert (Hpre : P (regupd regs 1 ret) mem rom
/\ getr (regupd regs 1 ret) 1 = ret).
{ split; [apply HraP, HP|]. apply getr_same. reg_neq_tac. }
destruct (Hproc ret Hret (regupd regs 1 ret) mem rom Hpre)
as (regs' & mem' & Hst & HQ & Hr & Hm).
exists regs', mem'. split.
- eapply mst_step; [reflexivity | apply Hjal | exact Hst].
- split; [exact HQ|]. split; [|exact Hm].
intros r Hr0.
assert (HnC : ~ C r) by tauto.
assert (Hne : r <> 1) by tauto.
rewrite (Hr r HnC), getr_other by exact Hne. reflexivity.
Qed.
Lemma triple_loop : forall segs C W (I : nat -> assn) (hd out : word) (Q : assn),
(forall i, triple segs C W (I (S i)) hd hd (I i)) ->
triple segs C W (I O) hd out Q ->
forall n, triple segs C W (I n) hd out Q.
Proof.
intros segs C W I hd out Q Hbody Hexit n.
induction n as [|n IH]; [exact Hexit|].
eapply triple_seq_same; [apply Hbody | exact IH].
Qed.
Lemma triple_loop_measure :
forall segs C W (I : nat -> assn) (hd out : word) (Q P : assn),
(forall i, triple segs C W (I (S i)) hd hd (I i)) ->
triple segs C W (I O) hd out Q ->
(forall regs mem rom, P regs mem rom -> exists n, I n regs mem rom) ->
triple segs C W P hd out Q.
Proof.
intros segs C W I hd out Q P Hbody Hexit Hmeas regs mem rom HP.
destruct (Hmeas _ _ _ HP) as (n & HI).
exact (triple_loop segs C W I hd out Q Hbody Hexit n regs mem rom HI).
Qed.
Lemma triple_msteps : forall segs C W P a b Q regs mem rom,
triple segs C W P a b Q -> P regs mem rom ->
exists regs' mem',
msteps segs (mkst regs a mem rom) (mkst regs' b mem' rom) /\ Q regs' mem' rom.
Proof.
intros segs C W P a b Q regs mem rom H HP.
destruct (H _ _ _ HP) as (regs' & mem' & Hst & HQ & _ & _).
exists regs', mem'. split; assumption.
Qed.
Lemma triple_wexit : forall segs C W P a b Q bufs code regs mem rom,
triple segs C W P a b Q ->
P regs mem rom ->
(forall regs' mem', Q regs' mem' rom ->
to_wexit segs (mkst regs' b mem' rom) bufs code) ->
to_wexit segs (mkst regs a mem rom) bufs code.
Proof.
intros segs C W P a b Q bufs code regs mem rom H HP Hcont.
destruct (H _ _ _ HP) as (regs' & mem' & Hst & HQ & _ & _).
eapply msteps_to_wexit; [exact Hst | apply Hcont, HQ].
Qed.
End f.
