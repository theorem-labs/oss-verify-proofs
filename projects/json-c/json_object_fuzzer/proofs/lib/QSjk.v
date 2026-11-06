(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG Qnhz Qrxj.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import ListNotations.
Open Scope bv_scope.
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Definition at_ (base : word) (d : Z) : word := Z_to_bv 64 (bv_unsigned base + d).

#[using="Type"] Lemma at_0 : forall base, at_ base 0 = base.
Proof.
intros base. unfold at_. rewrite Z.add_0_r. apply bv_eq.
rewrite Z_to_bv_unsigned. apply bv_wrap_small, bv_unsigned_in_range.
Qed.

#[using="Type"] Lemma at_addi : forall base d e, v_addi (at_ base d) e = at_ base (d + e).
Proof.
intros base d e. unfold at_, v_addi. apply bv_eq.
rewrite !Z_to_bv_unsigned. unfold bv_wrap.
rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

#[using="Type"] Lemma at_btgt : forall base d e, btgt (at_ base d) e = at_ base (d + e).
Proof. intros. unfold btgt. apply at_addi. Qed.

#[using="Type"] Lemma at_lit : forall (base : word) (d : Z) (a : word),
Z_to_bv 64 (bv_unsigned base + d) = a -> at_ base d = a.
Proof. intros. assumption. Qed.

#[using="Type"] Lemma at_at : forall base d e, at_ (at_ base d) e = at_ base (d + e).
Proof. exact at_addi. Qed.

#[using="Type"] Lemma u_succ_shift : forall (a : word) (i : Z),
Z_to_bv 64 (bv_unsigned (a + 1) + i) = Z_to_bv 64 (bv_unsigned a + (1 + i)).
Proof.
intros a i. apply bv_eq. rewrite !Z_to_bv_unsigned, bv_add_unsigned.
assert (H1 : bv_unsigned (1 : word) = 1%Z) by reflexivity. rewrite H1.
unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

#[using="Type"] Lemma at_self : forall a : word, Z_to_bv 64 (bv_unsigned a + 0) = a.
Proof. intros a. exact (at_0 a). Qed.

Definition assn := bvmap 5 word -> (word -> option byte) -> (word -> option byte) -> Prop.

Definition regset := reg -> Prop.
Definition memset := word -> Prop.

Definition regs_agree (C : regset) (regs regs' : bvmap 5 word) : Prop :=
forall r, ~ C r -> getr regs' r = getr regs r.

Definition mem_agree (W : memset) (m m' : word -> option byte) : Prop :=
forall x, ~ W x -> m' x = m x.

#[using="Type"] Lemma regs_agree_refl : forall C regs, regs_agree C regs regs.
Proof. intros C regs r _. reflexivity. Qed.

#[using="Type"] Lemma mem_agree_refl : forall W m, mem_agree W m m.
Proof. intros W m x _. reflexivity. Qed.

#[using="Type"] Lemma regs_agree_trans : forall C regs1 regs2 regs3,
regs_agree C regs1 regs2 -> regs_agree C regs2 regs3 -> regs_agree C regs1 regs3.
Proof. intros C r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). apply H1, Hr. Qed.

#[using="Type"] Lemma mem_agree_trans : forall W m1 m2 m3,
mem_agree W m1 m2 -> mem_agree W m2 m3 -> mem_agree W m1 m3.
Proof. intros W m1 m2 m3 H1 H2 x Hx. rewrite (H2 x Hx). apply H1, Hx. Qed.

#[using="Type"] Lemma regs_agree_mono : forall (C C' : regset) regs regs',
(forall r, C r -> C' r) -> regs_agree C regs regs' -> regs_agree C' regs regs'.
Proof. intros C C' regs regs' Hsub H r Hr. apply H. intro; apply Hr, Hsub; assumption. Qed.

#[using="Type"] Lemma mem_agree_mono : forall (W W' : memset) m m',
(forall x, W x -> W' x) -> mem_agree W m m' -> mem_agree W' m m'.
Proof. intros W W' m m' Hsub H x Hx. apply H. intro; apply Hx, Hsub; assumption. Qed.

#[using="Type"] Lemma regs_agree_upd : forall (C : regset) regs regs' r v,
C r -> regs_agree C regs regs' -> regs_agree C regs (regupd regs' r v).
Proof.
intros C regs regs' r v Hin H s Hs.
rewrite getr_other by (intro Heq; subst; contradiction).
apply H, Hs.
Qed.

#[using="Type"] Lemma mem_agree_wbytes : forall (W : memset) m m' a bs,
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

#[using="Type"] Lemma triple_intro : forall segs C W P a b Q,
(forall regs mem rom, P regs mem rom ->
exists regs' mem',
msteps segs (mkst regs a mem rom) (mkst regs' b mem' rom)
/\ Q regs' mem' rom
/\ regs_agree C regs regs'
/\ mem_agree W mem mem') ->
triple segs C W P a b Q.
Proof. intros; assumption. Qed.

#[using="Type"] Lemma triple_skip : forall segs C W P a, triple segs C W P a a P.
Proof.
intros segs C W P a regs mem rom HP.
exists regs, mem. split; [apply mst_refl|].
split; [exact HP|]. split; [apply regs_agree_refl|apply mem_agree_refl].
Qed.

#[using="Type"] Lemma triple_seq : forall segs C1 W1 C2 W2 P Q R a b c,
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

#[using="Type"] Lemma triple_conseq : forall segs C C' W W' P P' Q Q' a b,
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

#[using="Type"] Lemma triple_seq_same : forall segs C W P Q R a b c,
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

#[using="Type"] Lemma triple_frame : forall segs C W P Q R a b,
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

#[using="Type"] Lemma frameable_and : forall C W R1 R2,
frameable C W R1 -> frameable C W R2 ->
frameable C W (fun regs mem rom => R1 regs mem rom /\ R2 regs mem rom).
Proof. intros C W R1 R2 H1 H2 regs mem rom regs' mem' Hr Hm (A & B); split; eauto. Qed.

#[using="Type"] Lemma frameable_reg : forall (C : regset) W (r : reg) (v : word),
~ C r -> frameable C W (fun regs _ _ => getr regs r = v).
Proof.
intros C W r v Hnc regs mem rom regs' mem' Hr _ Hv.
rewrite (Hr r Hnc). exact Hv.
Qed.

#[using="Type"] Lemma frameable_rdn : forall segs (C : regset) (W : memset) (a : word) (n : nat) bs,
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

#[using="Type"] Lemma land_m2_even : forall z : Z, (z mod 2 = 0)%Z -> Z.land z (-2) = z.
Proof.
intros z Hz.
assert (Hl : Z.land z 1 = 0%Z).
{ replace 1%Z with (Z.ones 1) by reflexivity. rewrite Z.land_ones by lia. exact Hz. }
replace (-2)%Z with (Z.lnot 1) by reflexivity.
rewrite <- Z.ldiff_land.
rewrite <- (Z.lor_ldiff_and z 1) at 2.
rewrite Hl, Z.lor_0_r. reflexivity.
Qed.

#[using="Type"] Lemma ret_ok_even : forall k, (bv_unsigned k mod 2 = 0)%Z -> ret_ok k.
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

#[using="Type"] Lemma triple_call : forall segs C W P Q callsite entry ret,
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

#[using="Type"] Lemma triple_loop : forall segs C W (I : nat -> assn) (hd out : word) (Q : assn),
(forall i, triple segs C W (I (S i)) hd hd (I i)) ->
triple segs C W (I O) hd out Q ->
forall n, triple segs C W (I n) hd out Q.
Proof.
intros segs C W I hd out Q Hbody Hexit n.
induction n as [|n IH]; [exact Hexit|].
eapply triple_seq_same; [apply Hbody | exact IH].
Qed.

#[using="Type"] Lemma triple_loop_measure :
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

#[using="Type"] Lemma triple_msteps : forall segs C W P a b Q regs mem rom,
triple segs C W P a b Q -> P regs mem rom ->
exists regs' mem',
msteps segs (mkst regs a mem rom) (mkst regs' b mem' rom) /\ Q regs' mem' rom.
Proof.
intros segs C W P a b Q regs mem rom H HP.
destruct (H _ _ _ HP) as (regs' & mem' & Hst & HQ & _ & _).
exists regs', mem'. split; assumption.
Qed.

#[using="Type"] Lemma triple_wexit : forall segs C W P a b Q bufs code regs mem rom,
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
End FPGEN1.

End Mq0.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Prelude.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpox QsV0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.OmniRun.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude.
Import Qpox QsV0 QsRG QsRG.Mq0 Qrxj Qnhz.Mq0.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.

Import ListNotations.
Open Scope bv_scope.
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

#[using="Type"] Lemma fd32_1 : fd32 (Z_to_bv 64 1) = Z_to_bv 64 1.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma fd32_2 : fd32 (Z_to_bv 64 2) = Z_to_bv 64 2.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma u_len_word : forall {A} (l : list A), (Z.of_nat (length l) < 2^64)%Z ->
bv_unsigned (len_word l) = Z.of_nat (length l).
Proof.
intros A l H. unfold len_word. apply Z_to_bv_small.
unfold bv_modulus. change (Z.of_N 64) with 64%Z. lia.
Qed.

#[using="Type"] Lemma len_word_firstn_nat : forall n (bs : list byte),
(n <= length bs)%nat ->
len_word (firstn n bs) = nat_to_word n.
Proof.
intros n bs Hn. unfold len_word, nat_to_word.
rewrite firstn_length_le by exact Hn. reflexivity.
Qed.

#[using="Type"] Lemma u_len_word_firstn : forall n (bs : list byte),
(n <= length bs)%nat -> (Z.of_nat (length bs) < 2^64)%Z ->
bv_unsigned (len_word (firstn n bs)) = Z.of_nat n.
Proof.
intros n bs Hn Hlen.
rewrite len_word_unsigned by (rewrite firstn_length_le by exact Hn;
unfold two_pow_64; lia).
rewrite firstn_length_le by exact Hn. reflexivity.
Qed.

#[using="Type"] Lemma v_add_len_firstn : forall (p : word) n (bs : list byte),
(n <= length bs)%nat ->
v_add p (len_word (firstn n bs)) = p + nat_to_word n.
Proof.
intros p n bs Hn. rewrite len_word_firstn_nat by exact Hn.
unfold v_add. apply bv_eq.
rewrite Z_to_bv_unsigned, bv_add_unsigned. reflexivity.
Qed.

#[using="Type"] Lemma v_add_len_firstn_Z : forall (p : word) n (bs : list byte),
(n <= length bs)%nat -> (Z.of_nat (length bs) < 2^64)%Z ->
v_add p (len_word (firstn n bs)) = Z_to_bv 64 (bv_unsigned p + Z.of_nat n).
Proof.
intros p n bs Hn Hlen. unfold v_add.
rewrite u_len_word_firstn by assumption. reflexivity.
Qed.

#[using="Type"] Lemma word_add_nat_Z : forall (p : word) (k : nat),
(Z.of_nat k < 2^64)%Z ->
p + nat_to_word k = Z_to_bv 64 (bv_unsigned p + Z.of_nat k).
Proof.
intros p k Hk. apply bv_eq.
rewrite bv_add_unsigned. unfold nat_to_word.
rewrite Z_to_bv_small
by (unfold bv_modulus; change (Z.of_N 64) with 64%Z; lia).
rewrite Z_to_bv_unsigned. reflexivity.
Qed.

#[using="Type"] Lemma v_sub_len_firstn : forall n (bs : list byte),
(n <= length bs)%nat -> (Z.of_nat (length bs) < 2^64)%Z ->
v_sub (len_word bs) (len_word (firstn n bs)) = len_word (skipn n bs).
Proof.
intros n bs Hn Hlen. apply bv_eq.
rewrite v_sub_small
by (rewrite u_len_word_firstn by assumption;
rewrite len_word_unsigned by (unfold two_pow_64; lia); lia).
rewrite u_len_word_firstn by assumption.
rewrite !len_word_unsigned
by (unfold two_pow_64; rewrite ?length_skipn; lia).
rewrite length_skipn. lia.
Qed.

Section WithSegsCh.
Variable segs : list Segment.
Variable fd ch : word.

Inductive to_wall : machine_state -> list byte -> (machine_state -> Prop) -> Prop :=
| twl_write : forall ms x8 rest k,
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 64%Z ->
ms_gpr ms 0 = fd ->
ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some rest ->
(1 <= length rest)%nat ->
(forall n, (1 <= n)%nat -> (n <= length rest)%nat ->
to_wall_tail (advance_past_svc (set_gpr0 ms (len_word (firstn n rest))))
(skipn n rest) k) ->
to_wall ms rest k
with to_wall_tail : machine_state -> list byte -> (machine_state -> Prop) -> Prop :=
| twt_done : forall ms k, k ms -> to_wall_tail ms [] k
| twt_more : forall ms rest k,
(1 <= length rest)%nat ->
to_wall ms rest k ->
to_wall_tail ms rest k
| twt_step : forall ms ms' rest k,
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
to_wall_tail ms' rest k ->
to_wall_tail ms rest k.

Scheme to_wall_min := Minimality for to_wall Sort Prop
with to_wall_tail_min := Minimality for to_wall_tail Sort Prop.
Combined Scheme to_wall_mutind from to_wall_min, to_wall_tail_min.

#[using="Type"] Lemma msteps_to_wall_tail : forall ms ms' rest k,
msteps segs ms ms' -> to_wall_tail ms' rest k -> to_wall_tail ms rest k.
Proof.
intros ms ms' rest k H; induction H; [auto|].
intro Hw. eapply twt_step; eauto.
Qed.

#[using="Type"] Lemma to_wall_tail_nil_msteps : forall ms k,
to_wall_tail ms [] k -> exists ms', msteps segs ms ms' /\ k ms'.
Proof.
intros ms k H.
remember ([] : list byte) as rest eqn:Hrest.
induction H as [ms k Hk | ms rest k Hnb Hw | ms ms' rest k Hsvc Hstep Ht IH].
- exists ms. split; [apply mst_refl | exact Hk].
- subst rest. cbn in Hnb. lia.
- destruct (IH Hrest) as (ms'' & Hm & Hk).
exists ms''. split; [eapply mst_step; eauto | exact Hk].
Qed.

Hypothesis Hfd32 : fd32 fd = fd.

#[using="Hfd32"] Lemma sstep_to_wall_inv : forall ms rest k model evs st,
m_halted model = None ->
m_vm_lazy model = [] ->
fdchan fd ch model ->
buf_modeled rest ->
to_wall ms rest k ->
sstep segs (mkCfg ms model) evs st ->
exists n, (1 <= n)%nat /\ (n <= length rest)%nat /\
evs = map (WriteEv ch) (firstn n rest) /\
st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n rest)))) model) /\
to_wall_tail (advance_past_svc (set_gpr0 ms (len_word (firstn n rest))))
(skipn n rest) k.
Proof.
intros ms rest k model evs st Hh Hlazy Hfdc Hbm Hw Hss.
revert Hbm.
destruct Hw as [ms x8 rest k Hsvc Hno Hg Hr Hnb Hcont]. intro Hbm.
destruct (sstep_write_ch_inv segs fd ch Hfd32 ms model x8 rest evs st
Hh Hlazy Hfdc Hsvc Hno Hg Hr Hbm Hnb Hss) as (n & Hn1 & Hn2 & Hevs & Hst).
exists n. repeat split; try assumption.
apply (Hcont n Hn1 Hn2).
Qed.

#[using="Hfd32"] Lemma to_wall_no_error_sstep : forall ms rest k model evs,
m_halted model = None ->
m_vm_lazy model = [] ->
fdchan fd ch model ->
buf_modeled rest ->
to_wall ms rest k ->
~ sstep segs (mkCfg ms model) evs SError.
Proof.
intros ms rest k model evs Hh Hlazy Hfdc Hbm Hw Hss.
destruct (sstep_to_wall_inv ms rest k model evs SError Hh Hlazy Hfdc Hbm Hw Hss)
as (n & _ & _ & _ & Hst & _).
discriminate Hst.
Qed.

#[using="Hfd32"] Lemma to_wall_star_admits_mut : forall model tr_k,
m_halted model = None ->
m_vm_lazy model = [] ->
fdchan fd ch model ->
(forall ms rest k, to_wall ms rest k ->
buf_modeled rest ->
(forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c)
/\ (forall ms rest k, to_wall_tail ms rest k ->
buf_modeled rest ->
(forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c).
Proof.
intros model tr_k Hh Hlazy Hfdc.
apply (to_wall_mutind
(fun ms rest k =>
buf_modeled rest ->
(forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c)
(fun ms rest k =>
buf_modeled rest ->
(forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c)).
-
intros ms x8 rest k Hsvc Hno Hg Hr Hnb Hcont IH Hbm Hk.
destruct (IH (length rest) Hnb (Nat.le_refl _)
(buf_modeled_skipn (length rest) rest Hbm) Hk) as [c Hstar].
exists c.
replace (map (WriteEv ch) rest ++ tr_k)
with (map (WriteEv ch) (firstn (length rest) rest)
++ (map (WriteEv ch) (skipn (length rest) rest) ++ tr_k))
by (rewrite firstn_all, skipn_all; reflexivity).
eapply star_step; [| exact Hstar].
rewrite <- (apply_effect_copyins_no_write ms
(len_word (firstn (length rest) rest))
[(ms_gpr ms 1, length rest)]).
apply (sstep_syscall segs ms model x8
(with_copyins [(ms_gpr ms 1, length rest)]
(mkEffect (len_word (firstn (length rest) rest)) [] [])) model model
(map (WriteEv ch) (firstn (length rest) rest)));
[exact Hh | exact Hsvc | | exact Hh |].
eapply write_ch_ok_n; try eassumption. apply Nat.le_refl.
rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity.
-
intros ms k Hk Hbm Hcont. cbn [map app]. apply (Hcont ms Hk).
-
intros ms rest k Hnb Hw IH Hbm Hk. exact (IH Hbm Hk).
-
intros ms ms' rest k Hsvc Hstep Ht IH Hbm Hk.
destruct (IH Hbm Hk) as [c Hstar].
exists c.
replace (map (WriteEv ch) rest ++ tr_k)
with (([] : list event) ++ (map (WriteEv ch) rest ++ tr_k)) by reflexivity.
eapply star_step; [| exact Hstar].
apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

#[using="Hfd32"] Lemma to_wall_star_admits : forall ms rest k,
to_wall ms rest k ->
buf_modeled rest ->
forall model tr_k,
m_halted model = None ->
m_vm_lazy model = [] ->
fdchan fd ch model ->
(forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c.
Proof.
intros ms rest k Hw Hbm model tr_k Hh Hlazy Hfdc Hk.
exact (proj1 (to_wall_star_admits_mut model tr_k Hh Hlazy Hfdc) ms rest k Hw Hbm Hk).
Qed.

#[using="Hfd32"] Lemma to_wall_tail_star_admits : forall ms rest k,
to_wall_tail ms rest k ->
buf_modeled rest ->
forall model tr_k,
m_halted model = None ->
m_vm_lazy model = [] ->
fdchan fd ch model ->
(forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c.
Proof.
intros ms rest k Hw Hbm model tr_k Hh Hlazy Hfdc Hk.
exact (proj2 (to_wall_star_admits_mut model tr_k Hh Hlazy Hfdc) ms rest k Hw Hbm Hk).
Qed.

#[using="Hfd32"] Lemma to_wall_star_only_mut : forall model T,
m_halted model = None ->
m_vm_lazy model = [] ->
fdchan fd ch model ->
(forall ms rest k, to_wall ms rest k ->
buf_modeled rest ->
(forall ms' tr c, k ms' -> star segs (mkCfg ms' model) tr c -> is_prefix tr T) ->
forall tr c, star segs (mkCfg ms model) tr c ->
is_prefix tr (map (WriteEv ch) rest ++ T))
/\ (forall ms rest k, to_wall_tail ms rest k ->
buf_modeled rest ->
(forall ms' tr c, k ms' -> star segs (mkCfg ms' model) tr c -> is_prefix tr T) ->
forall tr c, star segs (mkCfg ms model) tr c ->
is_prefix tr (map (WriteEv ch) rest ++ T)).
Proof.
intros model T Hh Hlazy Hfdc.
apply (to_wall_mutind
(fun ms rest k =>
buf_modeled rest ->
(forall ms' tr c, k ms' -> star segs (mkCfg ms' model) tr c -> is_prefix tr T) ->
forall tr c, star segs (mkCfg ms model) tr c ->
is_prefix tr (map (WriteEv ch) rest ++ T))
(fun ms rest k =>
buf_modeled rest ->
(forall ms' tr c, k ms' -> star segs (mkCfg ms' model) tr c -> is_prefix tr T) ->
forall tr c, star segs (mkCfg ms model) tr c ->
is_prefix tr (map (WriteEv ch) rest ++ T))).
-
intros ms x8 rest k Hsvc Hno Hg Hr Hnb Hcont IH Hbm HK tr c Hstar.
inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst.
{ apply is_prefix_nil. }
destruct (sstep_write_ch_inv segs fd ch Hfd32 ms model x8 rest evs (SNext c2)
Hh Hlazy Hfdc Hsvc Hno Hg Hr Hbm Hnb Hss) as (n & Hn1 & Hn2 & Hevs & Hc2).
subst evs. inversion Hc2; subst c2.
pose proof (IH n Hn1 Hn2 (buf_modeled_skipn n rest Hbm) HK tr2 c Hstar2) as Hp.
rewrite <- (firstn_skipn n rest) at 2.
rewrite map_app, <- app_assoc.
apply is_prefix_app_mono. exact Hp.
-
intros ms k Hk Hbm HK tr c Hstar. cbn [map app]. exact (HK ms tr c Hk Hstar).
-
intros ms rest k Hnb Hw IH Hbm HK tr c Hstar. exact (IH Hbm HK tr c Hstar).
-
intros ms ms' rest k Hsvc Hstep Ht IH Hbm HK tr c Hstar.
inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst.
{ apply is_prefix_nil. }
destruct (sstep_instr_inv segs ms model ms' evs (SNext c2) Hlazy Hsvc Hstep Hss)
as [Hevs Hc2].
subst evs. inversion Hc2; subst c2. cbn [app].
exact (IH Hbm HK tr2 c Hstar2).
Qed.

#[using="Hfd32"] Lemma to_wall_star_only : forall ms rest k,
to_wall ms rest k ->
buf_modeled rest ->
forall model T,
m_halted model = None ->
m_vm_lazy model = [] ->
fdchan fd ch model ->
(forall ms' tr c, k ms' -> star segs (mkCfg ms' model) tr c -> is_prefix tr T) ->
forall tr c, star segs (mkCfg ms model) tr c ->
is_prefix tr (map (WriteEv ch) rest ++ T).
Proof.
intros ms rest k Hw Hbm model T Hh Hlazy Hfdc HK tr c Hstar.
exact (proj1 (to_wall_star_only_mut model T Hh Hlazy Hfdc) ms rest k Hw Hbm HK tr c Hstar).
Qed.

#[using="Type"] Lemma twl_write_rec : forall (k : machine_state -> Prop) rest regs pc mem rom,
bv_unsigned (getr regs 17) = 64%Z ->
reg_get regs 10 = fd ->
ms_read_bytes {| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17); ms_resv := None;
ms_fcsr := fC; ms_mem := mem; ms_rom := rom |}
(reg_get regs 11) (reg_get regs 12) = Some rest ->
(1 <= length rest)%nat ->
(forall n, (1 <= n)%nat -> (n <= length rest)%nat ->
to_wall_tail (mkst (regupd regs 10 (len_word (firstn n rest)))
(v_addi pc 4) mem rom)
(skipn n rest) k) ->
to_wall {| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17); ms_resv := None;
ms_fcsr := fC; ms_mem := mem; ms_rom := rom |}
rest k.
Proof.
intros k rest regs pc mem rom H17 H10 Hr Hnb Hcont.
assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
assert (E12 : Z_to_bv 5 (10 + Z.of_nat 2) = (12 : reg)) by (apply bv_eq; reflexivity).
eapply twl_write.
- cbn [ms_svc_pending]. reflexivity.
- exact H17.
- unfold ms_gpr. cbn [ms_regs]. rewrite E10. exact H10.
- unfold ms_gpr. cbn [ms_regs]. rewrite E11, E12. exact Hr.
- exact Hnb.
- intros n Hn1 Hn2. rewrite adv_set. exact (Hcont n Hn1 Hn2).
Qed.

Fixpoint to_wallexit (bufs : list (list byte)) (code : word)
(ms : machine_state) : Prop :=
match bufs with
| [] => to_wexit segs ms [] code
| buf :: rest =>
(1 <= length buf)%nat /\
to_wall_tail ms buf (to_wallexit rest code)
end.

#[using="Type"] Lemma to_wall_k_ex_mut :
(forall ms rest k, to_wall ms rest k -> exists ms', k ms')
/\ (forall ms rest k, to_wall_tail ms rest k -> exists ms', k ms').
Proof.
apply (to_wall_mutind
(fun ms rest k => exists ms', k ms')
(fun ms rest k => exists ms', k ms')).
- intros ms x8 rest k Hsvc Hno Hg Hr Hnb Hcont IH.
exact (IH (length rest) Hnb (Nat.le_refl _)).
- intros ms k Hk. exists ms. exact Hk.
- intros ms rest k Hnb Hw IH. exact IH.
- intros ms ms' rest k Hsvc Hstep Ht IH. exact IH.
Qed.

#[using="Type"] Lemma to_wall_tail_k_ex : forall ms rest k,
to_wall_tail ms rest k -> exists ms', k ms'.
Proof. exact (proj2 to_wall_k_ex_mut). Qed.

#[using="Type"] Lemma to_wallexit_bufs_nonempty : forall bufs code ms,
to_wallexit bufs code ms ->
Forall (fun b : list byte => (1 <= length b)%nat) bufs.
Proof.
induction bufs as [|buf rest IH]; intros code ms Hw; [constructor|].
destruct Hw as [Hnb Hw]. constructor; [exact Hnb|].
destruct (to_wall_tail_k_ex _ _ _ Hw) as [ms' Hk].
exact (IH code ms' Hk).
Qed.

#[using="Type"] Lemma twe_step : forall ms ms' bufs code,
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
to_wallexit bufs code ms' -> to_wallexit bufs code ms.
Proof.
intros ms ms' bufs code Hsvc Hstep Hw.
destruct bufs as [|buf rest].
- eapply tw_step; eauto.
- destruct Hw as [Hnb Hw]. split; [exact Hnb|].
eapply twt_step; eauto.
Qed.

#[using="Type"] Lemma msteps_to_wallexit : forall ms ms' bufs code,
msteps segs ms ms' -> to_wallexit bufs code ms' -> to_wallexit bufs code ms.
Proof.
intros ms ms' bufs code Hms Hw. destruct bufs as [|buf rest].
- exact (msteps_to_wexit segs ms ms' [] code Hms Hw).
- destruct Hw as [Hnb Hw]. split; [exact Hnb|].
eapply msteps_to_wall_tail; eauto.
Qed.

#[using="Hfd32"] Lemma to_wall_exec_mut : forall model (Q : post),
m_halted model = None ->
m_vm_lazy model = [] ->
fdchan fd ch model ->
(forall ms rest k, to_wall ms rest k ->
buf_modeled rest ->
(forall ms', k ms' -> OmniRun.exec segs (mkCfg ms' model) Q) ->
OmniRun.exec segs (mkCfg ms model)
(fun tr o => exists tr', tr = map (WriteEv ch) rest ++ tr' /\ Q tr' o))
/\ (forall ms rest k, to_wall_tail ms rest k ->
buf_modeled rest ->
(forall ms', k ms' -> OmniRun.exec segs (mkCfg ms' model) Q) ->
OmniRun.exec segs (mkCfg ms model)
(fun tr o => exists tr', tr = map (WriteEv ch) rest ++ tr' /\ Q tr' o)).
Proof.
intros model Q Hh Hlazy Hfdc.
apply (to_wall_mutind
(fun ms rest k =>
buf_modeled rest ->
(forall ms', k ms' -> OmniRun.exec segs (mkCfg ms' model) Q) ->
OmniRun.exec segs (mkCfg ms model)
(fun tr o => exists tr', tr = map (WriteEv ch) rest ++ tr' /\ Q tr' o))
(fun ms rest k =>
buf_modeled rest ->
(forall ms', k ms' -> OmniRun.exec segs (mkCfg ms' model) Q) ->
OmniRun.exec segs (mkCfg ms model)
(fun tr o => exists tr', tr = map (WriteEv ch) rest ++ tr' /\ Q tr' o))).
-
intros ms x8 rest k Hsvc Hno Hg Hr Hnb Hcont IH Hbm HK.
assert (Hw : to_wall ms rest k) by (eapply twl_write; eassumption).
apply exec_step; [exact Hh | | |].
+
eexists; eexists.
apply (sstep_syscall segs ms model x8
(with_copyins [(ms_gpr ms 1, length rest)]
(mkEffect (len_word (firstn (length rest) rest)) [] [])) model model
(map (WriteEv ch) (firstn (length rest) rest)));
[exact Hh | exact Hsvc | | exact Hh |].
* eapply write_ch_ok_n; try eassumption. apply Nat.le_refl.
* rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity.
+ intros evs Hss.
destruct (sstep_to_wall_inv ms rest k model evs SError Hh Hlazy Hfdc Hbm Hw Hss)
as (n & _ & _ & _ & Habs & _).
discriminate Habs.
+ intros evs c' Hss.
destruct (sstep_to_wall_inv ms rest k model evs (SNext c') Hh Hlazy Hfdc Hbm Hw Hss)
as (n & Hn1 & Hn2 & -> & Hc' & _).
injection Hc' as ->.
eapply exec_conseq;
[exact (IH n Hn1 Hn2 (buf_modeled_skipn n rest Hbm) HK) |].
intros tr o (tr' & -> & HQ). exists tr'. split; [| exact HQ].
rewrite <- (firstn_skipn n rest) at 3. rewrite map_app, <- app_assoc. reflexivity.
-
intros ms k Hk Hbm HK.
eapply exec_conseq; [exact (HK ms Hk) |].
intros tr o HQ. exists tr. split; [reflexivity | exact HQ].
-
intros ms rest k Hnb Hw IH Hbm HK. exact (IH Hbm HK).
-
intros ms ms' rest k Hsvc Hstep Ht IH Hbm HK.
apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
+ apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
+ intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
+ eapply exec_conseq; [exact (IH Hbm HK) |]. intros tr o H. cbn [app]. exact H.
Qed.

#[using="Type"] Lemma to_wexit_nil_exec_aux : forall ms bufs code model,
m_halted model = None ->
m_vm_lazy model = [] ->
to_wexit segs ms bufs code ->
bufs = [] ->
OmniRun.exec segs (mkCfg ms model)
(fun tr o => tr = [ExitEv code (m_fs model)] /\ exits_with code tr o).
Proof.
intros ms bufs code model Hh Hlazy Hte.
induction Hte as
[ms x8 Hsvc Hx8
| ms x8 buf bufs code Hsvc Hno Hg Hr Hnb Hcont IH
| ms ms' bufs code Hsvc Hstep Hte IH]; intro Hbufs; [| discriminate Hbufs |].
- apply (exec_step_only segs _ _
[ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
(mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))).
+ replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
(m_fs (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
by (cbn; reflexivity).
apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
(with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
(bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
* exact Hh.
* exact Hsvc.
* apply (exit_dispatch_ok (sys_input segs ms x8) model).
rewrite in_sysno_sys_input. exact Hx8.
* cbn. reflexivity.
* apply m_killed_with_halted.
+ intros evs st Hss. exact (sstep_exit_inv segs ms model x8 evs st Hh Hsvc Hx8 Hss).
+ apply exec_halt.
* cbn. rewrite m_halted_with_halted. discriminate.
* cbn beta. rewrite app_nil_r. split; [reflexivity |].
cbn [exits_with cfg_model]. split;
[ rewrite m_halted_with_halted; reflexivity
| apply m_killed_with_halted ].
- apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
+ apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
+ intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
+ eapply exec_conseq; [exact (IH Hbufs) |]. intros tr o H. cbn [app]. exact H.
Qed.

#[using="Type"] Lemma to_wexit_nil_exec : forall ms code model,
m_halted model = None ->
m_vm_lazy model = [] ->
to_wexit segs ms [] code ->
OmniRun.exec segs (mkCfg ms model)
(fun tr o => tr = [ExitEv code (m_fs model)] /\ exits_with code tr o).
Proof.
intros ms code model Hh Hlazy Hte.
exact (to_wexit_nil_exec_aux ms [] code model Hh Hlazy Hte eq_refl).
Qed.

#[using="Hfd32"] Lemma to_wallexit_exec : forall bufs code ms model,
m_halted model = None ->
m_vm_lazy model = [] ->
fdchan fd ch model ->
bufs_modeled bufs ->
to_wallexit bufs code ms ->
OmniRun.exec segs (mkCfg ms model)
(fun tr o => tr = wevents_ch ch bufs ++ [ExitEv code (m_fs model)]
/\ exits_with code tr o).
Proof.
induction bufs as [|buf rest IH]; intros code ms model Hh Hlazy Hfdc Hbm Hw.
- cbn [wevents_ch app]. apply to_wexit_nil_exec; assumption.
- destruct Hw as [Hnb Hw]. apply Forall_cons_iff in Hbm as [Hb Hbs].
eapply exec_conseq;
[exact (proj2 (to_wall_exec_mut model _ Hh Hlazy Hfdc) ms buf (to_wallexit rest code)
Hw Hb (fun ms' Hk => IH code ms' model Hh Hlazy Hfdc Hbs Hk)) |].
intros tr o (tr' & -> & Heq & Hx). split; [| exact Hx].
rewrite Heq. cbn [wevents_ch]. rewrite <- app_assoc. reflexivity.
Qed.

#[using="Hfd32"] Lemma to_wallexit_star_admits : forall bufs code ms model,
m_halted model = None ->
m_vm_lazy model = [] ->
fdchan fd ch model ->
bufs_modeled bufs ->
to_wallexit bufs code ms ->
exists c, star segs (mkCfg ms model)
(wevents_ch ch bufs ++ [ExitEv code (m_fs model)]) c.
Proof.
intros bufs code ms model Hh Hlazy Hfdc Hbm Hw.
destruct (exec_realizes _ _ _ (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw))
as (tr & [c' | c'] & Hm & Heq & Hx); [| destruct Hx].
subst tr. destruct (mexec_halt_star _ _ _ _ Hm c' eq_refl) as (Hstar & _).
exists c'. exact Hstar.
Qed.

#[using="Hfd32"] Lemma to_wallexit_no_other_exit : forall bufs code ms model,
m_halted model = None ->
m_vm_lazy model = [] ->
fdchan fd ch model ->
bufs_modeled bufs ->
to_wallexit bufs code ms ->
forall code', code' <> code ->
~ OmniRun.exec segs (mkCfg ms model) (exits_with code').
Proof.
intros bufs code ms model Hh Hlazy Hfdc Hbm Hw code' Hne Hex.
destruct (exec_realizes _ _ _ (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw))
as (tr & [c' | c'] & Hm & _ & Hx); [| destruct Hx].
pose proof (exec_sound _ _ _ Hex _ _ Hm) as Hx'.
cbn [exits_with] in Hx, Hx'. destruct Hx as (Hx & _). destruct Hx' as (Hx' & _).
rewrite Hx in Hx'. injection Hx' as Hx'.
exact (Hne (eq_sym Hx')).
Qed.

#[using="Hfd32"] Lemma to_wallexit_trace_unique : forall bufs code ms model,
m_halted model = None ->
m_vm_lazy model = [] ->
fdchan fd ch model ->
bufs_modeled bufs ->
to_wallexit bufs code ms ->
forall tr', tr' <> wevents_ch ch bufs ++ [ExitEv code (m_fs model)] ->
~ OmniRun.exec segs (mkCfg ms model) (fun tr _ => tr = tr').
Proof.
intros bufs code ms model Hh Hlazy Hfdc Hbm Hw tr' Hne Hex.
destruct (exec_realizes _ _ _ (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw))
as (tr & o & Hm & Heq & _).
pose proof (exec_sound _ _ _ Hex _ _ Hm) as Heq'. cbn beta in Heq'.
apply Hne. rewrite <- Heq', Heq. reflexivity.
Qed.

#[using="Hfd32"] Lemma to_wallexit_not_silent : forall bufs code ms model,
m_halted model = None ->
m_vm_lazy model = [] ->
fdchan fd ch model ->
bufs_modeled bufs ->
to_wallexit bufs code ms ->
~ cosafe segs (mkCfg ms model) (fun tr => tr = []).
Proof.
intros bufs code ms model Hh Hlazy Hfdc Hbm Hw Hc.
destruct (to_wallexit_star_admits bufs code ms model Hh Hlazy Hfdc Hbm Hw) as (c' & Hstar).
pose proof (cosafe_star _ _ _ _ _ Hc Hstar) as Hnil.
destruct (wevents_ch ch bufs); discriminate Hnil.
Qed.

#[using="Hfd32"] Lemma to_wallexit_star_only : forall bufs code ms model,
m_halted model = None ->
m_vm_lazy model = [] ->
fdchan fd ch model ->
bufs_modeled bufs ->
to_wallexit bufs code ms ->
forall tr c, star segs (mkCfg ms model) tr c ->
is_prefix tr (wevents_ch ch bufs ++ [ExitEv code (m_fs model)]).
Proof.
intros bufs code ms model Hh Hlazy Hfdc Hbm Hw tr c Hstar.
destruct (exec_realizes _ _ _
(exec_star _ _ _ _ _ (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw) Hstar))
as (tr' & o & _ & HQ).
cbn beta in HQ. destruct HQ as (Heq & _). rewrite <- Heq. apply is_prefix_app.
Qed.

#[using="Hfd32"] Lemma to_wallexit_no_error : forall ms model bufs code,
m_halted model = None ->
m_vm_lazy model = [] ->
fdchan fd ch model ->
bufs_modeled bufs ->
to_wallexit bufs code ms ->
~ reaches_error segs (mkCfg ms model).
Proof.
intros ms model bufs code Hh Hlazy Hfdc Hbm Hw. apply exec_no_error.
eapply exec_conseq; [exact (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw) |].
intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

End WithSegsCh.

Abbreviation wexit1 segs ms bufs code :=
(to_wallexit segs (Z_to_bv 64 1) bufs code ms).

#[using="Type"] Lemma wevents_ch_fd1 : forall bufs,
wevents_ch (Z_to_bv 64 1) bufs = wevents bufs.
Proof.
induction bufs as [|b bs IH]; cbn [wevents_ch wevents];
[reflexivity | rewrite IH; reflexivity].
Qed.

#[using="Type"] Lemma wall_omni_run : forall fd ch, fd32 fd = fd ->
forall segs pc ph sp brk0 mb rnd lim inp bufs code,
fdchan fd ch (init_model (segments_reserved segs) brk0 mb sp lim inp) ->
bufs_modeled bufs ->
to_wallexit segs fd bufs code (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp
(fun tr o => tr = wevents_ch ch bufs ++ [ExitEv code (in_fs inp)]
/\ exits_with code tr o).
Proof.
intros fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw.
cbn [omni_run]. unfold init_config.
exact (to_wallexit_exec segs fd ch Hfd32 bufs code _
(init_model (segments_reserved segs) brk0 mb sp lim inp)
eq_refl eq_refl Hfdc Hbm Hw).
Qed.

#[using="Type"] Lemma wall_obs_iff : forall fd ch, fd32 fd = fd ->
forall segs pc ph sp brk0 mb rnd lim inp bufs code,
fdchan fd ch (init_model (segments_reserved segs) brk0 mb sp lim inp) ->
bufs_modeled bufs ->
to_wallexit segs fd bufs code (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
forall tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr
<-> is_prefix tr (wevents_ch ch bufs ++ [ExitEv code (in_fs inp)]).
Proof.
intros fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw tr.
apply exec_obs_iff.
eapply exec_conseq;
[exact (wall_omni_run fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw) |].
intros tr' o (Heq & Hx). split; [exact Heq | exact (exits_with_never_errors _ _ _ Hx)].
Qed.

#[using="Type"] Lemma wall_no_error_run : forall fd ch, fd32 fd = fd ->
forall segs pc ph sp brk0 mb rnd lim inp bufs code,
fdchan fd ch (init_model (segments_reserved segs) brk0 mb sp lim inp) ->
bufs_modeled bufs ->
to_wallexit segs fd bufs code (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
~ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp).
Proof.
intros fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw. apply exec_no_error.
eapply exec_conseq;
[exact (wall_omni_run fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw) |].
intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

#[using="Type"] Lemma wall_omni_strong_equiv :
forall source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bufs code inp,
to_wallexit source_segs (Z_to_bv 64 1) bufs code
(init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
to_wallexit target_segs (Z_to_bv 64 1) bufs code
(init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
bufs_modeled bufs ->
omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
(mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bufs code inp
Hsource Htarget Hbm.
assert (HfdS : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
(init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp))
by (split; reflexivity).
assert (HfdT : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
(init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp))
by (split; reflexivity).
split.
{ cbn [img_segments].
eapply coexec_conseq;
[apply exec_coexec;
exact (wall_omni_run (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1 source_segs rpc rph rsp rbrk rmb rrnd
source_alloc_limit inp bufs code HfdS Hbm Hsource) |].
intros tr o (_ & Hx).
exact (never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)). }
right. split.
- apply trace_equiv_iff_omni. intro tr. cbn.
rewrite (wall_obs_iff (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bufs code HfdS Hbm Hsource tr).
rewrite (wall_obs_iff (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code HfdT Hbm Htarget tr).
reflexivity.
- apply bh_errors_iff. cbn.
apply (wall_no_error_run (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code HfdT Hbm Htarget).
Qed.

#[using="Type"] Lemma wall_strong_equiv :
forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bufs code inp,
to_wallexit source_segs (Z_to_bv 64 1) bufs code
(init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
to_wallexit target_segs (Z_to_bv 64 1) bufs code
(init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
bufs_modeled bufs ->
Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
/\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
(run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
bufs code inp Hsource Htarget Hbm.
assert (HfdS : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
(init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp))
by (split; reflexivity).
assert (HfdT : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
(init_model (segments_reserved target_segs) abrk amb asp alim inp))
by (split; reflexivity).
split.
{ apply no_error_run_modeled.
apply (wall_no_error_run (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code
HfdS Hbm Hsource). }
right. split.
- intro tr. cbn.
rewrite (wall_obs_iff (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code
HfdS Hbm Hsource tr).
rewrite (wall_obs_iff (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
target_segs apc aph asp abrk amb arnd alim inp bufs code
HfdT Hbm Htarget tr).
reflexivity.
- cbn.
apply (wall_no_error_run (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
target_segs apc aph asp abrk amb arnd alim inp bufs code
HfdT Hbm Htarget).
Qed.
End FPGEN1.
End Mq1.

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsV0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsV0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qrxj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qrxj.
Import ListNotations.
Open Scope bv_scope.
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

#[using="Type"] Lemma v_lui_4096 : v_lui 4096 = Z_to_bv 64 4096.
Proof. reflexivity. Qed.

#[using="Type"] Lemma c_lts_0_0 : c_lts (Z_to_bv 64 0) (Z_to_bv 64 0) = false.
Proof. reflexivity. Qed.

#[using="Type"] Lemma write_to_mem_below : forall data mem (buf a : word),
(bv_unsigned buf + Z.of_nat (length data) <= 2^64)%Z ->
(bv_unsigned a < bv_unsigned buf)%Z ->
write_to_mem mem buf data a = mem a.
Proof.
intros data mem buf a Hnw Ha.
rewrite write_to_mem_wbytes. apply wbytes_below; assumption.
Qed.

#[using="Type"] Lemma write_to_mem_above : forall data mem (buf a : word),
(bv_unsigned buf + Z.of_nat (length data) <= bv_unsigned a)%Z ->
write_to_mem mem buf data a = mem a.
Proof.
intros data mem buf a Ha.
rewrite write_to_mem_wbytes. apply wbytes_above; assumption.
Qed.

#[using="Type"] Lemma rdn_wtm_out : forall segs data m (buf a : word) n,
(bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
(bv_unsigned buf + Z.of_nat (length data) <= 2^64)%Z ->
((bv_unsigned buf + Z.of_nat (length data) <= bv_unsigned a)%Z \/
(bv_unsigned a + Z.of_nat n <= bv_unsigned buf)%Z) ->
rdn segs (write_to_mem m buf data) a n = rdn segs m a n.
Proof.
intros segs data m buf a n Hna Hnb Hd. apply rdn_ext; [exact Hna|].
intros x Hx. destruct Hd as [Hd | Hd].
- apply write_to_mem_above. lia.
- apply write_to_mem_below; [exact Hnb | lia].
Qed.

#[using="Type"] Lemma rdn_write_to_mem : forall segs data mem (buf : word),
(bv_unsigned buf + Z.of_nat (length data) <= 2^64)%Z ->
rdn segs (write_to_mem mem buf data) buf (length data) = Some data.
Proof.
intros segs data mem buf Hnw.
rewrite write_to_mem_wbytes. apply rdn_wbytes_hit. exact Hnw.
Qed.

#[using="Type"] Lemma adv_apply_write : forall regs pc sv mem rom ret buf data,
advance_past_svc (apply_effect
{| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc; ms_svc_pending := sv; ms_resv := None; ms_fcsr := fC;
ms_mem := mem; ms_rom := rom |}
(mkEffect ret [(buf, data)] []))
= mkst (regupd regs 10 ret) (v_addi pc 4) (write_to_mem mem buf data) rom.
Proof.
intros regs pc sv mem rom ret buf data.
unfold advance_past_svc, apply_effect, RiscvSemantics.set_reg, ms_pc.
rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
cbv beta iota zeta.
cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies
apply_zeros apply_unmaps apply_writes].
unfold mkst, regupd.
rewrite b_npc4. reflexivity.
Qed.

#[using="Type"] Lemma adv_apply_delivered : forall regs pc sv mem rom ret buf data,
advance_past_svc (apply_effect
{| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc; ms_svc_pending := sv; ms_resv := None; ms_fcsr := fC;
ms_mem := mem; ms_rom := rom |}
(mkEffect ret (delivered_writes buf data) []))
= mkst (regupd regs 10 ret) (v_addi pc 4) (write_to_mem mem buf data) rom.
Proof.
intros regs pc sv mem rom ret buf data.
destruct data as [|b rest]; [|apply adv_apply_write].
unfold advance_past_svc, apply_effect, RiscvSemantics.set_reg, ms_pc.
rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
cbv beta iota zeta.
cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies
apply_zeros apply_unmaps apply_writes
delivered_writes write_to_mem].
unfold mkst, regupd.
rewrite b_npc4. reflexivity.
Qed.
End FPGEN1.

