(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Qc6I QJFf QDM6 QCiC Qpj5 QvDJ Q67d Q6sh QKTr QvG1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import Qc27 Qc6I QJFf QDM6.
Import QCiC Qpj5.Mq1 QvDJ.Mq2 Q67d QCiC.Mq0 Q6sh QKTr.
Import QvG1.
Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.

Section AImplT.

Variable atn : node -> machine_state -> Prop.

Local Notation implMA := (@implMG PStateA asegs atn).

Definition aimplT {R} (t : T R) (s : PStateA) (Q : R -> PStateA -> machine_state -> Prop) (ms : machine_state) : Prop :=
implMA (membedA t) s Q ms.

Lemma aimplT_ret {R} (r : R) s Q ms : evt asegs (Q r s) ms -> aimplT (tret r) s Q ms.
Proof. intros H. unfold aimplT, tret. cbn [membedA]. apply implMG_ret. exact H. Qed.

Lemma aimplT_unr {R} w s (Q : R -> PStateA -> machine_state -> Prop) ms : aimplT (tunr w) s Q ms.
Proof. unfold aimplT, tunr. cbn [membedA]. apply implMG_unr. Qed.

Lemma aimplT_spin {R} s (Q : R -> PStateA -> machine_state -> Prop) ms :
evt asegs (fun ms1 => atn NSetTid ms1) ms -> aimplT (R:=R) tspin s Q ms.
Proof.
intros H. unfold aimplT, tspin. cbn [membedA]. unfold mspin. apply implMG_sys.
eapply evt_mono; [exact H|]. intros ms1 Hat. split; [exact Hat|]. intros rsp a E. discriminate.
Qed.

Lemma aimplT_mono {R} (t : T R) s Q Q' ms :
aimplT t s Q ms -> (forall r s' ms', Q r s' ms' -> Q' r s' ms') -> aimplT t s Q' ms.
Proof. intros H HQ. unfold aimplT in *. eapply implMG_mono; eauto. Qed.

Lemma aimplT_evt {R} (t : T R) s Q P ms :
evt asegs P ms -> (forall ms', P ms' -> aimplT t s Q ms') -> aimplT t s Q ms.
Proof. intros H K. unfold aimplT in *. eapply implMG_evt; eauto. Qed.

Lemma aimplT_from_evt {R} (t : T R) s Q ms :
evt asegs (fun ms' => aimplT t s Q ms') ms -> aimplT t s Q ms.
Proof. intros H. eapply aimplT_evt; [exact H|]. intros ms' H'; exact H'. Qed.

Lemma aimpl_vis_unfold {R} n (k : resp -> itree node R) Q ms :
impl asegs atn (Vis n k) Q ms = evt asegs (fun ms1 => atn n ms1 /\ forall rsp, impl asegs atn (k rsp) Q (nret ms1 rsp)) ms.
Proof. reflexivity. Qed.

Lemma aimpl_bind_mono {A B C} (t : itree node A) (f1 : A -> itree node B) (f2 : A -> itree node C) Q1 Q2 ms :
impl asegs atn (Qc6I.bind _ t f1) Q1 ms ->
(forall r ms', impl asegs atn (f1 r) Q1 ms' -> impl asegs atn (f2 r) Q2 ms') ->
impl asegs atn (Qc6I.bind _ t f2) Q2 ms.
Proof.
revert ms. induction t as [r|n k IH]; intros ms H K; cbn [Qc6I.bind] in *.
- apply K. exact H.
- rewrite aimpl_vis_unfold in H. rewrite aimpl_vis_unfold. eapply evt_mono; [exact H|].
intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
Qed.

Lemma implMA_mspin_any {A B} s (Q : A -> PStateA -> machine_state -> Prop) (Q' : B -> PStateA -> machine_state -> Prop) ms :
implMA mspin s Q ms -> implMA mspin s Q' ms.
Proof.
unfold implMG, mspin, msys, impl. cbn. intros H. eapply evt_mono; [exact H|].
intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. cbn. apply evt_done. exact I.
Qed.

Lemma aimplT_bind {R S} (t : T R) (f : R -> T S) s Q1 Q ms :
aimplT t s Q1 ms ->
(forall r s' ms', Q1 r s' ms' -> aimplT (f r) s' Q ms') ->
aimplT (tbind t f) s Q ms.
Proof.
unfold aimplT, tbind. revert s ms. induction t as [[r| |w]|e k IH]; intros s ms H K.
- cbn [sbind membedA]. cbn [membedA] in H. unfold implMG, mret in H. cbn in H.
eapply implMG_evt; [exact H|]. intros ms' H1. exact (K r s ms' H1).
- cbn [sbind membedA]. cbn [membedA] in H. eapply implMA_mspin_any. exact H.
- cbn [sbind membedA]. apply implMG_unr.
- cbn [sbind membedA]. cbn [membedA] in H. unfold implMG, mbind, ebind in H |- *.
eapply aimpl_bind_mono; [exact H|]. intros [|[z s']] ms' H1; cbn in *.
+ exact H1.
+ eapply IH; [exact H1| exact K].
Qed.

Lemma aimplT_vis {R} e (k : ansA -> T R) s Q1 Q ms :
implMA (ev_stepA e) s Q1 ms ->
(forall a s' ms', Q1 a s' ms' -> aimplT (k a) s' Q ms') ->
aimplT (tvis e k) s Q ms.
Proof.
intros H K. unfold aimplT, tvis. cbn [membedA]. eapply implMG_bind; [exact H|]. intros a s' ms' H1. apply (K a s' ms' H1).
Qed.

Lemma implMA_msys_enode {A} n (dec : resp -> option A) s (P : A -> machine_state -> Prop) ms :
impl asegs atn (enode n dec) (epost P) ms ->
implMA (msys n dec) s (fun a s' ms' => s' = s /\ P a ms') ms.
Proof.
intros H. unfold implMG, msys. cbn. unfold enode in H. cbn in H.
eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. specialize (Hk rsp).
destruct (dec rsp) as [a|]; cbn in *.
- eapply evt_mono; [exact Hk|]. intros ms' HP. cbn. auto.
- exact Hk.
Qed.

Lemma aimplT_map_fixed {R} addr len (k : ansA -> T R) s (P : ansA -> machine_state -> Prop) Q ms :
impl asegs atn (enode (NMmap addr len PROT_RW FL_FIXED) (dec_fixedA addr len)) (epost P) ms ->
(forall a ms', P a ms' -> aimplT (k a) s Q ms') ->
aimplT (tvis (EvMapFixed addr len) k) s Q ms.
Proof.
intros H K. eapply aimplT_vis; [apply implMA_msys_enode; exact H|]. intros a s' ms' [-> HP]. apply K. exact HP.
Qed.

Lemma aimplT_map_anon {R} len avoid (k : ansA -> T R) s (P : ansA -> machine_state -> Prop) Q ms :
impl asegs atn (enode (NMmap 0 len PROT_RW FL_ANON) (dec_anonA len avoid)) (epost P) ms ->
(forall a ms', P a ms' -> aimplT (k a) s Q ms') ->
aimplT (tvis (EvMapAnon len avoid) k) s Q ms.
Proof.
intros H K. eapply aimplT_vis; [apply implMA_msys_enode; exact H|]. intros a s' ms' [-> HP]. apply K. exact HP.
Qed.

Lemma ev_stepA_state e s Q ms :
implMA (ev_stepA e) s Q ms -> implMA (ev_stepA e) s (fun a s' ms' => s' = s /\ Q a s' ms') ms.
Proof.
assert (GEN : forall A n (dec : resp -> option A) (Q : A -> PStateA -> machine_state -> Prop),
implMA (msys n dec) s Q ms -> implMA (msys n dec) s (fun a s' ms' => s' = s /\ Q a s' ms') ms).
{ intros A n dec Q0 H. unfold implMG, msys, enode in *. cbv beta in H. cbv beta. rewrite aimpl_vis_unfold in H. rewrite aimpl_vis_unfold.
eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. specialize (Hk rsp).
destruct (dec rsp) as [a|]; cbn in *; [|exact Hk]. eapply evt_mono; [exact Hk|]. intros ms' HQ; cbn; auto. }
destruct e; cbn [ev_stepA]; apply GEN.
Qed.

Lemma aimplT_state {R} (t : T R) s Q ms :
aimplT t s Q ms -> aimplT t s (fun r s' ms' => s' = s /\ Q r s' ms') ms.
Proof.
unfold aimplT. revert s ms. induction t as [[r| |w]|e k IH]; intros s ms H.
- cbn [membedA] in *. unfold implMG, mret in *. cbn in *. eapply evt_mono; [exact H|]. intros ms' HQ; cbn; auto.
- cbn [membedA] in *. eapply implMA_mspin_any. exact H.
- cbn [membedA]. apply implMG_unr.
- cbn [membedA] in *. eapply implMG_bind.
+ eapply ev_stepA_state. unfold implMG, mbind, ebind in H.

instantiate (1 := fun a s' ms' => impl asegs atn (membedA (k a) s') (epost (fun p => Q (fst p) (snd p))) ms').
unfold implMG. revert H. generalize (ev_stepA e s). intros t H.
revert ms H. induction t as [x|n kk IHt]; intros ms H; cbn [Qc6I.bind] in *.
* unfold epost in H |- *. destruct x as [|[a s']]; cbn in *; apply evt_done; [exact I| exact H].
* rewrite aimpl_vis_unfold in H. rewrite aimpl_vis_unfold. eapply evt_mono; [exact H|].
intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. apply IHt. apply Hk.
+ intros a s' ms' [-> H1]. cbn in H1. apply IH. exact H1.
Qed.

Lemma raw_malloc_A_intro L n s Q ms :
aimplT (asan_malloc L (ps_a s) n) s (fun ra s1 ms' => Q (fst ra) (set_a (snd ra) s1) ms') ms ->
implMA (raw_malloc_A L n) s Q ms.
Proof.
intros H. unfold raw_malloc_A.
eapply implMG_bind with (Q1 := fun x s' ms' => x = s /\ s' = s /\ ms' = ms).
{ apply implMG_get. apply evt_done. repeat split; reflexivity. }
intros x s' ms' (-> & -> & ->).
eapply implMG_bind. { apply aimplT_state in H. exact H. }
intros [r a'] s1 ms1 [-> HQ]. cbn in HQ.
eapply implMG_bind with (Q1 := fun _ s2 ms2 => s2 = set_a a' s /\ ms2 = ms1).
{ apply implMG_upd. apply evt_done. split; reflexivity. }
intros [] s2 ms2 [-> ->]. apply implMG_ret. apply evt_done. exact HQ.
Qed.

End AImplT.
End Mq0.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u Qtfh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u.
Import QvDJ.Mq3.
Import Qtfh.
Import QvG1.
Import ListNotations.
Open Scope bv_scope.

Definition memset_entry := 0xdb750%Z.

Ltac with_arr tac :=
lazymatch goal with
| ARR : u8arr ?segs ?m ?A ?bs, FIL : filled ?cb ?bs _, LEN : length ?bs = _ |- _ => tac segs ARR FIL LEN A cb
end.

Ltac brute256 c Rc :=
first [ apply word_eq_of_eqb | apply Z.eqb_eq | idtac ];
repeat match goal with H : context [c] |- _ => tryif constr_eq H Rc then fail else clear H end;
revert c Rc; apply brute256_ok; vm_compute; reflexivity.

Ltac reg_val r :=
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end)
end.

Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.

Lemma land4_of_aligned : forall x, (0 <= x)%Z -> (x mod 4 = 0)%Z -> Z.land x 4 = (x mod 8)%Z.
Proof.
intros x Hx H4.
transitivity (Z.land (x mod 8) 4).
{ change 8%Z with (2^3)%Z. rewrite <- Z.land_ones by lia. change (Z.ones 3) with 7%Z.
rewrite <- Z.land_assoc. reflexivity. }
assert (R : (x mod 8 = 0 \/ x mod 8 = 4)%Z) by (Z.div_mod_to_equations; lia).
destruct R as [R|R]; rewrite R; reflexivity.
Qed.

Definition memset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 a2 : word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' (bv_unsigned a0)
[CB (Z.to_nat (bv_unsigned a2)) (repeat (Z_to_bv 8 (bv_unsigned a1 mod 256)) (Z.to_nat (bv_unsigned a2)))].

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Hypothesis MI0 : mem_inv asegs m.
Hypothesis AB : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 <= 2^64 /\ 0 <= bv_unsigned a2 < 2^64)%Z.

Notation A := (bv_unsigned a0).
Notation n := (bv_unsigned a2).
Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
Notation POST := (memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m).

Notation ST pc mm x11 x12 x13 x14 x15 x16 :=
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

Ltac fin_with cover :=
zstep;
with_arr ltac:(fun segs ARR FIL LEN A cb =>
let E := fresh "E" in
pose proof (filled_all _ _ _ FIL ltac:(cover)) as E;
rewrite LEN in E; rewrite E in ARR;
apply rw_cells_of_u8arr in ARR; rewrite repeat_length in ARR);
finish; subst; assumption.
Ltac fin := fin_with ltac:(intros j Hj; cbv beta; lia).
Ltac disj_lia := first [ lia | right; lia | left; disj_lia ].

Lemma memset_loop : forall (K : nat) (c p r e : Z) (m1 : word -> option byte) (bs : list byte) (Q : Z -> Prop)
(x15 x16 : word),
Z.to_nat r = K ->
c = (bv_unsigned a1 mod 256)%Z ->
u8arr asegs m1 A bs -> filled (Z_to_bv 8 c) bs Q -> length bs = Z.to_nat n ->
mem_inv asegs m1 -> munch W m m1 -> wmono asegs m m1 ->
(forall j, (0 <= j < p \/ e <= j < n) -> Q j)%Z ->
(0 <= p)%Z -> (32 <= r)%Z -> (exists q, r = 4 * q)%Z -> (p + r <= n)%Z -> (e + 28 <= p + r)%Z ->
evt asegs POST (ST 0xdb828 m1 (Z_to_bv 64 (A + p)) (Z_to_bv 64 (c * BC8)) (Z_to_bv 64 31) (Z_to_bv 64 r) x15 x16).
Proof using AB.
induction K as [K IH] using lt_wf_ind; intros c p r e m1 bs Q x15 x16 HK Hc ARR FIL LEN MI MU WM HQ Hp Hr [q4 Hq4] Hpr He;
assert (Rc : (0 <= c < 256)%Z) by (subst c; apply Z.mod_pos_bound; lia).
mst p 8%nat ltac:(symmetry; apply le8_bcast; lia).
mst (p + 8)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
mst (p + 16)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
mst (p + 24)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
zstep. zstep. zstep.
if_cases KK; zify_cond KK.
-
replace (A + p + 32)%Z with (A + (p + 32))%Z by lia.
replace (r + -32)%Z with (r - 32)%Z by lia.
eapply (IH (Z.to_nat (r - 32)) ltac:(lia) c (p + 32)%Z (r - 32)%Z e _ _ _ x15 x16 eq_refl Hc ARR); try eassumption; try lia.
2:{ exists (q4 - 8)%Z. lia. }
intros j Hj.
destruct (Z_lt_le_dec j p) as [Hlt|Hge]. { left; left; left; left. apply HQ. lia. }
destruct (Z_lt_le_dec j (p + 32)) as [Hlt2|Hge2]. 2:{ left; left; left; left. apply HQ. lia. }
assert (D : ((p <= j < p + 8 \/ p + 8 <= j < p + 16) \/ (p + 16 <= j < p + 24 \/ p + 24 <= j < p + 32))%Z) by lia.
destruct D as [[?|?]|[?|?]]; [left; left; left; right| left; left; right| left; right| right]; lia.
- fin_with ltac:(intros j Hj; destruct (Z_lt_le_dec j p); [repeat left; apply HQ; lia|];
destruct (Z_lt_le_dec j (p + 32)); [|repeat left; apply HQ; lia]; disj_lia).
Qed.

Lemma memset_body : forall junk,
rw_cells asegs m A [CB (Z.to_nat n) junk] ->
evt asegs POST (ST 0xdb750 m a1 a2 a3 a4 a5 a6).
Proof using AB MI0.
intros junk DST. pose proof MI0 as MI.
pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (zr_word a1) as R1. unfold inr64 in R1.
remember (bv_unsigned a1 mod 256)%Z as c eqn:Hc.
assert (Rc : (0 <= c < 256)%Z) by (subst c; apply Z.mod_pos_bound; lia).
pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as ARR.
pose proof (rw_cells_CB_length _ _ _ _ _ DST) as LEN.
pose proof (filled_init (Z_to_bv 8 c) junk) as FIL.

zstep. if_cases K0; zify_cond K0. { fin. }
assert (MF : ms_facts A n 0 1) by (unfold ms_facts; lia).
pose proof (ms_store_ok asegs _ A n _ 0 1 a0 ARR LEN MF (eq_sym (Z_to_bv_plus0 a0))) as SOK.
zstep. ms_arr_store MF ltac:(rewrite Hc, le1_byte; reflexivity).
zstep. zstep. mst (n - 1)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
zstep. if_cases K3; zify_cond K3. { fin. }
mst 1%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
mst 2%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
zstep.
mst (n - 3)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
mst (n - 2)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
zstep. if_cases K7; zify_cond K7. { fin. }
mst 3%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
zstep.
mst (n - 4)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
zstep. if_cases K9; zify_cond K9. { fin. }

zstep. zstep.
setreg 16%Z (Z_to_bv 64 (c * 2^56)) ltac:(apply Z_to_bv_eqm; rewrite Z.shiftl_mul_pow2 by lia; subst c; Z.div_mod_to_equations; lia).
zstep. zstep.
remember (Z.land (bv_swrap 32 (0 - A) mod 18446744073709551616) 3) as k eqn:Hk.
assert (Rk : (0 <= k < 4 /\ (A + k) mod 4 = 0)%Z).
{ subst k. change 3%Z with (2^2 - 1)%Z. rewrite zb_land_mask by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ (Z.of_N 32 - 1))%Z with (2^31)%Z. change (2 ^ Z.of_N 32)%Z with (2^32)%Z.
Z.div_mod_to_equations. lia. }
clear Hk.
zstep. zstep. zstep. zstep. zstep.
change 18446744073709551612%Z with (2^64 - 2^2)%Z. rewrite land_align_down by lia.
remember (n - k - (n - k) mod 2^2)%Z as n4 eqn:Hn4.
assert (Rn4 : (exists q, n4 = 4 * q)%Z /\ (n - k - 3 <= n4 <= n - k)%Z).
{ split. { exists ((n - k) / 4)%Z. subst n4. Z.div_mod_to_equations. lia. } subst n4. Z.div_mod_to_equations. lia. }
clear Hn4. destruct Rn4 as [[q4 Hq4] Rn4].
zstep. setreg 12%Z (Z_to_bv 64 (c * BC4)) ltac:(unfold BC4; brute256 c Rc).

mst k 4%nat ltac:(symmetry; apply le4_bcast; lia).
zstep. mst (k + n4 - 4)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
zstep. if_cases K9'; zify_cond K9'. { fin. }
mst (k + 4)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + 8)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
zstep.
mst (k + n4 - 12)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + n4 - 8)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
zstep. if_cases K25; zify_cond K25. { fin. }
mst (k + 12)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + 16)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + 20)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + 24)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).

zstep.
remember (Z.land (A + k) 4) as k4 eqn:Hk4.
assert (Rk4 : ((k4 = 0 \/ k4 = 4) /\ (A + k + k4 + 24) mod 8 = 0)%Z).
{ subst k4. rewrite land4_of_aligned by lia. Z.div_mod_to_equations. lia. }
clear Hk4.
zstep. zstep. zstep.
mst (k + n4 - 28)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + n4 - 24)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + n4 - 20)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + n4 - 16)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
zstep. if_cases K32; zify_cond K32. { fin. }

zstep. zstep. zstep. zstep. setreg 12%Z (Z_to_bv 64 (c * BC8)) ltac:(unfold BC4, BC8; brute256 c Rc).
zstep.
replace (A + k + (k4 + 24))%Z with (A + (k + k4 + 24))%Z by lia.
eapply (memset_loop _ c (k + k4 + 24) _ (k + n4 - 28) _ _ _ _ _ eq_refl Hc ARR); try eassumption; try lia.
exists (q4 - Z.div k4 4 - 6)%Z. lia.
Qed.
End Proofs.

Lemma memset_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (junk : list byte),
rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
mem_inv asegs m ->
evt asegs (memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdb750) fc None m (seg_rom asegs)).
Proof.
intros until junk. intros DST MI.
eapply memset_body; [exact MI | | exact DST].
pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R. cbn. lia.
Qed.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 QwAs.
Import QvDJ.Mq3.
Import QvG1.
Import ListNotations.
Open Scope bv_scope.

Definition memchr_entry := 0xdb250%Z.

Section ZFacts.
Open Scope Z_scope.
Lemma lxor_lt_256 : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lxor a b < 256.
Proof.
intros a b Ha Hb. pose proof (Z.lxor_nonneg a b) as Hnn. split; [lia|].
destruct (Z.eq_dec (Z.lxor a b) 0) as [->|Hnz]; [lia|].
apply (proj2 (Z.log2_lt_pow2 (Z.lxor a b) 8 ltac:(lia))).
pose proof (Z.log2_lxor a b ltac:(lia) ltac:(lia)) as Hl.
assert (Z.log2 a < 8). { destruct (Z.eq_dec a 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
assert (Z.log2 b < 8). { destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
lia.
Qed.

Lemma lxor_split : forall x y x' y', 0 <= x < 256 -> 0 <= x' < 256 -> 0 <= y -> 0 <= y' ->
Z.lxor (x + 256 * y) (x' + 256 * y') = Z.lxor x x' + 256 * Z.lxor y y'.
Proof.
intros x y x' y' Hx Hx' Hy Hy'.
pose proof (lxor_lt_256 x x' Hx Hx') as Hl.
apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, !testbit_split by lia.
destruct (i <? 8); rewrite Z.lxor_spec; reflexivity.
Qed.

Lemma le_val_nonneg : forall bs, bytes_ok bs -> 0 <= le_val bs.
Proof. intros bs H. pose proof (le_val_range bs H). lia. Qed.

Lemma le_val_xor_bcast : forall bs c, bytes_ok bs -> 0 <= c < 256 ->
Z.lxor (le_val bs) (c * ones (length bs)) = le_val (map (fun b => Z.lxor b c) bs).
Proof.
induction bs as [|b bs IH]; intros c Hok Hc.
- cbn. rewrite Z.mul_0_r. reflexivity.
- inversion Hok as [|b0 bs0 Hb Hbs]; subst. cbn [le_val ones length map].
replace (c * (1 + 256 * ones (length bs))) with (c + 256 * (c * ones (length bs))) by lia.
rewrite lxor_split; try lia.
+ rewrite IH by assumption. reflexivity.
+ apply le_val_nonneg. exact Hbs.
+ pose proof (le_val_range (repeat 1 (length bs))) as Hr. assert (0 <= ones (length bs)); [|nia].
clear. induction (length bs); cbn; lia.
Qed.

Lemma bytes_ok_xor : forall bs c, bytes_ok bs -> 0 <= c < 256 -> bytes_ok (map (fun b => Z.lxor b c) bs).
Proof.
intros bs c H Hc. unfold bytes_ok in *. rewrite Forall_map. eapply Forall_impl; [|exact H].
intros b Hb. apply lxor_lt_256; assumption.
Qed.

Lemma In0_xor : forall bs c, In 0 (map (fun b => Z.lxor b c) bs) <-> In c bs.
Proof.
intros bs c. rewrite in_map_iff. split.
- intros (b & Hb & Hin). apply Z.lxor_eq in Hb. subst. exact Hin.
- intros Hin. exists c. split; [apply Z.lxor_nilpotent| exact Hin].
Qed.
End ZFacts.

Definition memchr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 a2 : word) (buf : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
(Z_to_bv 64 (memchr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf))
a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ bytes_at asegs m' (bv_unsigned a0) buf.

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf : list byte).
Hypothesis MI : mem_inv asegs m.
Hypothesis BUF : bytes_at asegs m (bv_unsigned a0) buf.
Hypothesis OK : memchr_ok (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf.
Let MU : munch [] m m := munch_refl [] m.
Let WM : wmono asegs m m := wmono_refl asegs m.

Notation A := (bv_unsigned a0).
Notation n := (bv_unsigned a2).
Notation c := ((bv_unsigned a1) mod 256)%Z.
Notation len := (Z.of_nat (length buf)).
Notation POST := (memchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 buf m).

Notation ST pc x5 x10 x12 x13 x14 x15 x16 x17 :=
(MS (mkR ra sp gp tp x5 t1 t2 s0 s1 x10 (Z_to_bv 64 c) x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom asegs)).
Notation CMAGIC := 72340172838076672%Z.
Notation HIGHS := 9259542123273814144%Z.
Notation ONES := 72340172838076673%Z.

Definition NOB (i : Z) : Prop :=
forall j b, (j < Z.to_nat i)%nat -> nth_error buf j = Some b -> bv_unsigned b <> c.

Lemma A_bound : (0 <= A /\ A + len <= 2^64 /\ 0 <= n < 2^64 /\ 0 <= c < 256)%Z.
Proof.
pose proof (bytes_at_bound _ _ _ _ BUF).
pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R.
pose proof (Z.mod_pos_bound (bv_unsigned a1) 256). cbn. lia.
Qed.

Lemma NOB_0 : NOB 0.
Proof. intros j b Hj. cbn in Hj. lia. Qed.

Lemma NOB_S : forall i b, (0 <= i)%Z -> NOB i -> nth_error buf (Z.to_nat i) = Some b -> bv_unsigned b <> c -> NOB (i + 1).
Proof.
intros i b Hi H Hn Hb j b' Hj Hn'.
destruct (Nat.eq_dec j (Z.to_nat i)) as [->|NE]. { rewrite Hn in Hn'. injection Hn' as <-. exact Hb. }
eapply H; [|exact Hn']. lia.
Qed.

Lemma ok_cases :
(exists j b, Z.of_nat j < n /\ nth_error buf j = Some b /\ bv_unsigned b = c /\
(forall j' b', (j' < j)%nat -> nth_error buf j' = Some b' -> bv_unsigned b' <> c) /\
(n <= len \/ Z.of_nat j + 1 + (- (A + Z.of_nat j + 1)) mod 8 <= len))%Z
\/ ((forall j b, (Z.of_nat j < n)%Z -> nth_error buf j = Some b -> bv_unsigned b <> c) /\ (n <= len)%Z).
Proof.
pose proof OK as H. unfold memchr_ok in H.
destruct (find_byte c (firstn (Z.to_nat n) buf)) as [j|] eqn:FB.
- left. destruct (find_byte_Some _ _ _ FB) as (Hl & (b & Hn & Hb) & Hmin).
rewrite firstn_length in Hl.
rewrite nth_error_firstn in Hn. replace (Nat.ltb j (Z.to_nat n)) with true in Hn by (symmetry; apply Nat.ltb_lt; lia).
exists j, b. repeat split; try assumption; try lia.
intros j' b' Hj' Hn'. eapply Hmin; [exact Hj'|]. rewrite nth_error_firstn.
replace (Nat.ltb j' (Z.to_nat n)) with true by (symmetry; apply Nat.ltb_lt; lia). exact Hn'.
- right. split; [|exact H]. intros j b Hj Hn. eapply (find_byte_None _ _ FB j). rewrite nth_error_firstn.
replace (Nat.ltb j (Z.to_nat n)) with true by (symmetry; apply Nat.ltb_lt; lia). exact Hn.
Qed.

Lemma readable : forall i, (0 <= i < n)%Z -> NOB i -> exists b, nth_error buf (Z.to_nat i) = Some b.
Proof.
intros i Hi HN. destruct (nth_error buf (Z.to_nat i)) as [b|] eqn:E; [exists b; reflexivity|].
exfalso. apply nth_error_None in E.
destruct ok_cases as [(j & b & Hj & Hn & Hb & Hmin & _)|(Hall & Hlen)]; [|lia].
pose proof (nth_error_lt _ _ _ Hn).
destruct (Nat.lt_ge_cases j (Z.to_nat i)) as [Hlt|Hge]; [|lia].
exact (HN _ _ Hlt Hn Hb).
Qed.

Lemma readable8 : forall i, (0 <= i)%Z -> (i + 8 <= n)%Z -> ((A + i) mod 8 = 0)%Z -> NOB i ->
(Z.to_nat i + 8 <= length buf)%nat.
Proof.
intros i Hi Hi8 Hal HN.
destruct ok_cases as [(j & b & Hj & Hn & Hb & Hmin & Hsl)|(Hall & Hlen)]; [|lia].
pose proof (nth_error_lt _ _ _ Hn).
destruct (Nat.lt_ge_cases j (Z.to_nat i)) as [Hlt|Hge]. { exfalso. exact (HN _ _ Hlt Hn Hb). }
destruct Hsl as [Hsl|Hsl]; [lia|].
destruct (Nat.lt_ge_cases j (Z.to_nat i + 8)) as [Hlt8|]; [|lia].
Z.div_mod_to_equations. lia.
Qed.

Lemma res_found : forall i b, (0 <= i < n)%Z -> NOB i -> nth_error buf (Z.to_nat i) = Some b -> bv_unsigned b = c ->
memchr_res A c n buf = (A + i)%Z.
Proof.
intros i b Hi HN Hn Hb. unfold memchr_res.
rewrite (find_byte_charact c _ (Z.to_nat i) b); [lia| | exact Hb|].
- rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia). exact Hn.
- intros j b' Hj Hn'. rewrite nth_error_firstn in Hn'. destruct (Nat.ltb j (Z.to_nat n)); [|discriminate].
exact (HN _ _ Hj Hn').
Qed.

Lemma res_none : NOB n -> memchr_res A c n buf = 0%Z.
Proof.
intros HN. unfold memchr_res. rewrite find_byte_None_intro; [reflexivity|].
intros j b Hn. rewrite nth_error_firstn in Hn. destruct (Nat.ltb_spec0 j (Z.to_nat n)); [|discriminate].
exact (HN j b ltac:(lia) Hn).
Qed.

Lemma memchr_tail : forall (k : nat) (i : Z) (x5 x12 x14 x15 x16 x17 : word),
Z.to_nat (n - i) = k -> (0 <= i < n)%Z -> NOB i ->
evt asegs POST (ST 0xdb2f0 x5 (Z_to_bv 64 (A + i)) x12 (Z_to_bv 64 (n - i)) x14 x15 x16 x17).
Proof.
induction k as [|k IH]; intros i x5 x12 x14 x15 x16 x17 Hk Hi HN; pose proof A_bound as AB; [lia|].
destruct (readable i Hi HN) as [b Hn]. pose proof (nth_error_lt _ _ _ Hn).
pose proof (u8ro_read asegs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD.
zstep. zstep. if_cases K; zify_cond K.
-  zstep. rewrite <- (res_found i b Hi HN Hn K). finish.
- zstep. zstep. zstep. if_cases K0; zify_cond K0.
+ replace (n - i + -1)%Z with (n - (i + 1))%Z by lia. replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
apply (IH (i + 1)%Z); try lia. eapply NOB_S; eauto; lia.
+  zstep. zstep. rewrite <- res_none at 1. { finish. }
replace n with (i + 1)%Z by lia. eapply NOB_S; eauto; lia.
Qed.

Lemma memchr_tail_entry : forall (i : Z) (x5 x13 x14 x15 x16 x17 : word),
(0 <= i <= n)%Z -> NOB i ->
evt asegs POST (ST 0xdb2e8 x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) x13 x14 x15 x16 x17).
Proof.
intros i x5 x13 x14 x15 x16 x17 Hi HN; pose proof A_bound as AB.
zstep. zstep. if_cases K; zify_cond K.
- zstep. zstep. rewrite <- res_none at 1. { finish. } replace n with i by lia. exact HN.
- apply (memchr_tail (Z.to_nat (n - i)) i); lia || assumption.
Qed.

Lemma memchr_words : forall (k : nat) (i : Z) (x5 x17 : word),
Z.to_nat (n - i) = k -> (0 <= i)%Z -> (i + 8 <= n)%Z -> ((A + i) mod 8 = 0)%Z -> NOB i ->
evt asegs POST (ST 0xdb2c4 x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) (Z_to_bv 64 CMAGIC) (Z_to_bv 64 HIGHS)
(Z_to_bv 64 (c * ONES)) (Z_to_bv 64 7) x17).
Proof.
induction k as [k IH] using lt_wf_ind; intros i x5 x17 Hk Hi Hi8 Hal HN; pose proof A_bound as AB.
pose proof (readable8 i Hi Hi8 Hal HN) as HW.
pose proof (bytes_at_read asegs m A buf i 8 BUF ltac:(lia) HW) as RD.
set (chunk := firstn 8 (skipn (Z.to_nat i) buf)) in RD.
assert (CL : length chunk = 8%nat). { subst chunk. rewrite firstn_length, skipn_length. lia. }
pose proof (le_val_range _ (bytes_ok_map chunk)) as WR. rewrite length_map, CL in WR.
change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR.
pose proof (le_val_range _ (bytes_ok_xor _ c (bytes_ok_map chunk) ltac:(lia))) as XR. rewrite !length_map, CL in XR.
change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in XR.
do 6 zstep.
rewrite (load8_le_val chunk CL).
replace (Z.lxor (le_val (map bv_unsigned chunk)) (c * ONES)) with (le_val (map (fun b => Z.lxor b c) (map bv_unsigned chunk))).
2:{ change ONES with ONES64b. rewrite <- ones_8, <- CL, <- (length_map bv_unsigned). symmetry. apply le_val_xor_bcast; [apply bytes_ok_map| lia]. }
if_cases K; zify_cond K.
-
clear K. destruct (readable i ltac:(lia) HN) as [b Hn].
pose proof (u8ro_read asegs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD1.
zstep. zstep. zstep. if_cases Kb; zify_cond Kb.
+ zstep. zstep. zstep. if_cases Kz; zify_cond Kz; [|exfalso; lia].
replace (n - i + -1)%Z with (n - (i + 1))%Z by lia. replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
apply (memchr_tail (Z.to_nat (n - (i + 1))) (i + 1)); try lia. eapply NOB_S; eauto; lia.
+ zstep. zstep. rewrite <- (res_found i b ltac:(lia) HN Hn Kb). finish.
- apply (haszero64_clang _ (bytes_ok_xor _ c (bytes_ok_map chunk) ltac:(lia)) ltac:(rewrite !length_map; exact CL)) in K.
rewrite In0_xor in K.

assert (HN8 : NOB (i + 8)).
{ intros j b Hj Hn. destruct (Nat.lt_ge_cases j (Z.to_nat i)) as [Hlt|Hge]. { exact (HN _ _ Hlt Hn). }
intros Hb. apply K. rewrite <- Hb. apply in_map. subst chunk.
apply nth_error_In with (n := (j - Z.to_nat i)%nat).
rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia).
rewrite nth_error_skipn, <- Hn. f_equal. lia. }
zstep. zstep. zstep. if_cases K8; zify_cond K8.
+ replace (A + i + 8)%Z with (A + (i + 8))%Z by lia. replace (n - i + -8)%Z with (n - (i + 8))%Z by lia.
apply (IH (Z.to_nat (n - (i + 8)))); try lia; try exact HN8. all: Z.div_mod_to_equations; lia.
+ replace (A + i + 8)%Z with (A + (i + 8))%Z by lia. replace (n - i + -8)%Z with (n - (i + 8))%Z by lia.
apply (memchr_tail_entry (i + 8)); try lia; exact HN8.
Qed.

Lemma memchr_mid : forall (i : Z) (x5 x13 x14 x15 x16 x17 : word),
(0 <= i <= n)%Z -> NOB i -> ((bv_unsigned x14 = 0)%Z <-> i = n) -> (i = n \/ (A + i) mod 8 = 0)%Z ->
evt asegs POST (ST 0xdb294 x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) x13 x14 x15 x16 x17).
Proof.
intros i x5 x13 x14 x15 x16 x17 Hi HN H14 Hal; pose proof A_bound as AB.
zstep. if_cases K; zify_cond K.
-  apply H14 in K. subst i. zstep. zstep. rewrite <- res_none at 1; [finish| exact HN].
- assert (Hin : (i < n)%Z). { destruct (Z.eq_dec i n) as [E|]; [|lia]. exfalso. apply K. apply H14. exact E. }
destruct Hal as [|Hal]; [lia|].
destruct (readable i ltac:(lia) HN) as [b Hn].
pose proof (u8ro_read asegs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD.
zstep. zstep. if_cases Kb; zify_cond Kb.
+ apply memchr_tail_entry; [lia| exact HN].
+ zstep. zstep. if_cases K8; zify_cond K8.
* apply memchr_tail_entry; [lia| exact HN].
* do 7 zstep.
apply (memchr_words (Z.to_nat (n - i)) i); try lia. exact HN.
Qed.

Lemma b2z_word_zero_iff : forall t, bv_unsigned (Z_to_bv 64 (Z.b2z t)) = 0%Z <-> t = false.
Proof. intros t. rewrite unsigned_lit by (destruct t; cbn; lia). destruct t; cbn; split; intros; first [congruence | lia]. Qed.

Lemma memchr_head : forall (k : nat) (i : Z) (x5 x13 x14 x17 : word),
Z.to_nat (n - i) = k -> (0 <= i < n)%Z -> NOB i -> ((A + i) mod 8 <> 0)%Z ->
evt asegs POST (ST 0xdb26c x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) x13 x14 (Z_to_bv 64 (A + i + 1)) (Z_to_bv 64 1) x17).
Proof.
induction k as [|k IH]; intros i x5 x13 x14 x17 Hk Hi HN Hal; pose proof A_bound as AB; [lia|].
destruct (readable i Hi HN) as [b Hn]. pose proof (nth_error_lt _ _ _ Hn).
pose proof (u8ro_read asegs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD.
zstep. zstep. zstep. if_cases Kb; zify_cond Kb.
-  apply (memchr_tail (Z.to_nat (n - i)) i); try lia. exact HN.
- pose proof (NOB_S i b ltac:(lia) HN Hn Kb) as HN1.
zstep. zstep. zstep. zstep. zstep. if_cases Kal; zify_cond Kal.
+ replace (A + i + 1)%Z with (A + (i + 1))%Z by lia. replace (n - i + -1)%Z with (n - (i + 1))%Z by lia.
apply (memchr_mid (i + 1)); try lia; try exact HN1.
* rewrite b2z_word_zero_iff, Z.ltb_ge. lia.
* right. revert Kal. zb_masks. intros Kal. Z.div_mod_to_equations; lia.
+ zstep. zstep. if_cases K1; zify_cond K1.
* replace (A + i + 2)%Z with (A + (i + 1) + 1)%Z by lia.
replace (A + i + 1)%Z with (A + (i + 1))%Z by lia. replace (n - i + -1)%Z with (n - (i + 1))%Z by lia.
apply (IH (i + 1)%Z); try lia; try exact HN1. revert Kal. zb_masks. intros Kal. Z.div_mod_to_equations; lia.
* replace (A + i + 1)%Z with (A + (i + 1))%Z by lia. replace (n - i + -1)%Z with (n - (i + 1))%Z by lia.
apply (memchr_mid (i + 1)); try lia; try exact HN1. rewrite b2z_word_zero_iff, Z.ltb_ge. lia.
Qed.

Lemma memchr_body :
evt asegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdb250) fc None m (seg_rom asegs)).
Proof.
pose proof A_bound as AB. pose proof (zr_word a1) as R1. unfold inr64 in R1.
zstep. replace (Z.land (bv_unsigned a1) 255) with c.
2:{ change 255%Z with (2^8 - 1)%Z. rewrite zb_land_mask by lia. reflexivity. }
zstep. zstep. zstep. if_cases Kal; zify_cond Kal.
-
eapply evt_eq.
2:{ apply (memchr_mid 0 t0 (Z_to_bv 64 (Z.land A 7)) (Z_to_bv 64 (Z.b2z (0 <? n)%Z)) a5 a6 a7); try lia.
- apply NOB_0. - rewrite b2z_word_zero_iff, Z.ltb_ge. lia.
- right. revert Kal. zb_masks. intros Kal. rewrite Z.add_0_r. exact Kal. }
unfold mkR. rewrite Z_to_bv_plus0, Z.sub_0_r, Z_to_bv_bv_unsigned. reflexivity.
- zstep. if_cases K0; zify_cond K0.
+
eapply evt_eq.
2:{ apply (memchr_mid 0 t0 (Z_to_bv 64 (Z.land A 7)) (Z_to_bv 64 (Z.b2z (0 <? n)%Z)) a5 a6 a7); try lia.
- apply NOB_0. - rewrite b2z_word_zero_iff, Z.ltb_ge. lia. }
unfold mkR. rewrite Z_to_bv_plus0, Z.sub_0_r, Z_to_bv_bv_unsigned. reflexivity.
+ zstep. zstep.
eapply evt_eq.
2:{ apply (memchr_head (Z.to_nat n) 0 t0 (Z_to_bv 64 (Z.land A 7)) (Z_to_bv 64 (Z.b2z (0 <? n)%Z)) a7); try lia.
- apply NOB_0. - revert Kal. zb_masks. intros Kal. rewrite Z.add_0_r. exact Kal. }
unfold mkR. rewrite Z_to_bv_plus0, Z.sub_0_r, Z_to_bv_bv_unsigned, Z.add_0_r. reflexivity.
Qed.
End Proofs.

Lemma memchr_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (buf : list byte),
bytes_at asegs m (bv_unsigned a0) buf ->
memchr_ok (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf ->
mem_inv asegs m ->
evt asegs (memchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 buf m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdb250) fc None m (seg_rom asegs)).
Proof. intros until buf. intros BUF OK MI. apply memchr_body; assumption. Qed.
End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u.
Import QvDJ.Mq3.
Import Qtfh.
Import QvG1.
Import ListNotations.
Open Scope bv_scope.

Definition memset_entry := 0xdb750%Z.

Ltac with_arr tac :=
lazymatch goal with
| ARR : u8arr ?segs ?m ?A ?bs, FIL : filled ?cb ?bs _, LEN : length ?bs = _ |- _ => tac segs ARR FIL LEN A cb
end.

Ltac brute256 c Rc :=
first [ apply word_eq_of_eqb | apply Z.eqb_eq | idtac ];
repeat match goal with H : context [c] |- _ => tryif constr_eq H Rc then fail else clear H end;
revert c Rc; apply brute256_ok; vm_compute; reflexivity.

Ltac reg_val r :=
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end)
end.

Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.

Lemma land4_of_aligned : forall x, (0 <= x)%Z -> (x mod 4 = 0)%Z -> Z.land x 4 = (x mod 8)%Z.
Proof.
intros x Hx H4.
transitivity (Z.land (x mod 8) 4).
{ change 8%Z with (2^3)%Z. rewrite <- Z.land_ones by lia. change (Z.ones 3) with 7%Z.
rewrite <- Z.land_assoc. reflexivity. }
assert (R : (x mod 8 = 0 \/ x mod 8 = 4)%Z) by (Z.div_mod_to_equations; lia).
destruct R as [R|R]; rewrite R; reflexivity.
Qed.

Definition memset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 a2 : word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' (bv_unsigned a0)
[CB (Z.to_nat (bv_unsigned a2)) (repeat (Z_to_bv 8 (bv_unsigned a1 mod 256)) (Z.to_nat (bv_unsigned a2)))].

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Hypothesis MI0 : mem_inv asegs m.
Hypothesis AB : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 <= 2^64 /\ 0 <= bv_unsigned a2 < 2^64)%Z.

Notation A := (bv_unsigned a0).
Notation n := (bv_unsigned a2).
Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
Notation POST := (memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m).

Notation ST pc mm x11 x12 x13 x14 x15 x16 :=
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

Ltac fin_with cover :=
zstep;
with_arr ltac:(fun segs ARR FIL LEN A cb =>
let E := fresh "E" in
pose proof (filled_all _ _ _ FIL ltac:(cover)) as E;
rewrite LEN in E; rewrite E in ARR;
apply rw_cells_of_u8arr in ARR; rewrite repeat_length in ARR);
finish; subst; assumption.
Ltac fin := fin_with ltac:(intros j Hj; cbv beta; lia).
Ltac disj_lia := first [ lia | right; lia | left; disj_lia ].

Lemma memset_loop : forall (K : nat) (c p r e : Z) (m1 : word -> option byte) (bs : list byte) (Q : Z -> Prop)
(x15 x16 : word),
Z.to_nat r = K ->
c = (bv_unsigned a1 mod 256)%Z ->
u8arr asegs m1 A bs -> filled (Z_to_bv 8 c) bs Q -> length bs = Z.to_nat n ->
mem_inv asegs m1 -> munch W m m1 -> wmono asegs m m1 ->
(forall j, (0 <= j < p \/ e <= j < n) -> Q j)%Z ->
(0 <= p)%Z -> (32 <= r)%Z -> (exists q, r = 4 * q)%Z -> (p + r <= n)%Z -> (e + 28 <= p + r)%Z ->
evt asegs POST (ST 0xdb828 m1 (Z_to_bv 64 (A + p)) (Z_to_bv 64 (c * BC8)) (Z_to_bv 64 31) (Z_to_bv 64 r) x15 x16).
Proof using AB.
induction K as [K IH] using lt_wf_ind; intros c p r e m1 bs Q x15 x16 HK Hc ARR FIL LEN MI MU WM HQ Hp Hr [q4 Hq4] Hpr He;
assert (Rc : (0 <= c < 256)%Z) by (subst c; apply Z.mod_pos_bound; lia).
mst p 8%nat ltac:(symmetry; apply le8_bcast; lia).
mst (p + 8)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
mst (p + 16)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
mst (p + 24)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
zstep. zstep. zstep.
if_cases KK; zify_cond KK.
-
replace (A + p + 32)%Z with (A + (p + 32))%Z by lia.
replace (r + -32)%Z with (r - 32)%Z by lia.
eapply (IH (Z.to_nat (r - 32)) ltac:(lia) c (p + 32)%Z (r - 32)%Z e _ _ _ x15 x16 eq_refl Hc ARR); try eassumption; try lia.
2:{ exists (q4 - 8)%Z. lia. }
intros j Hj.
destruct (Z_lt_le_dec j p) as [Hlt|Hge]. { left; left; left; left. apply HQ. lia. }
destruct (Z_lt_le_dec j (p + 32)) as [Hlt2|Hge2]. 2:{ left; left; left; left. apply HQ. lia. }
assert (D : ((p <= j < p + 8 \/ p + 8 <= j < p + 16) \/ (p + 16 <= j < p + 24 \/ p + 24 <= j < p + 32))%Z) by lia.
destruct D as [[?|?]|[?|?]]; [left; left; left; right| left; left; right| left; right| right]; lia.
- fin_with ltac:(intros j Hj; destruct (Z_lt_le_dec j p); [repeat left; apply HQ; lia|];
destruct (Z_lt_le_dec j (p + 32)); [|repeat left; apply HQ; lia]; disj_lia).
Qed.

Lemma memset_body : forall junk,
rw_cells asegs m A [CB (Z.to_nat n) junk] ->
evt asegs POST (ST 0xdb750 m a1 a2 a3 a4 a5 a6).
Proof using AB MI0.
intros junk DST. pose proof MI0 as MI.
pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (zr_word a1) as R1. unfold inr64 in R1.
remember (bv_unsigned a1 mod 256)%Z as c eqn:Hc.
assert (Rc : (0 <= c < 256)%Z) by (subst c; apply Z.mod_pos_bound; lia).
pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as ARR.
pose proof (rw_cells_CB_length _ _ _ _ _ DST) as LEN.
pose proof (filled_init (Z_to_bv 8 c) junk) as FIL.

zstep. if_cases K0; zify_cond K0. { fin. }
assert (MF : ms_facts A n 0 1) by (unfold ms_facts; lia).
pose proof (ms_store_ok asegs _ A n _ 0 1 a0 ARR LEN MF (eq_sym (Z_to_bv_plus0 a0))) as SOK.
zstep. ms_arr_store MF ltac:(rewrite Hc, le1_byte; reflexivity).
zstep. zstep. mst (n - 1)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
zstep. if_cases K3; zify_cond K3. { fin. }
mst 1%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
mst 2%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
zstep.
mst (n - 3)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
mst (n - 2)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
zstep. if_cases K7; zify_cond K7. { fin. }
mst 3%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
zstep.
mst (n - 4)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
zstep. if_cases K9; zify_cond K9. { fin. }

zstep. zstep.
setreg 16%Z (Z_to_bv 64 (c * 2^56)) ltac:(apply Z_to_bv_eqm; rewrite Z.shiftl_mul_pow2 by lia; subst c; Z.div_mod_to_equations; lia).
zstep. zstep.
remember (Z.land (bv_swrap 32 (0 - A) mod 18446744073709551616) 3) as k eqn:Hk.
assert (Rk : (0 <= k < 4 /\ (A + k) mod 4 = 0)%Z).
{ subst k. change 3%Z with (2^2 - 1)%Z. rewrite zb_land_mask by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ (Z.of_N 32 - 1))%Z with (2^31)%Z. change (2 ^ Z.of_N 32)%Z with (2^32)%Z.
Z.div_mod_to_equations. lia. }
clear Hk.
zstep. zstep. zstep. zstep. zstep.
change 18446744073709551612%Z with (2^64 - 2^2)%Z. rewrite land_align_down by lia.
remember (n - k - (n - k) mod 2^2)%Z as n4 eqn:Hn4.
assert (Rn4 : (exists q, n4 = 4 * q)%Z /\ (n - k - 3 <= n4 <= n - k)%Z).
{ split. { exists ((n - k) / 4)%Z. subst n4. Z.div_mod_to_equations. lia. } subst n4. Z.div_mod_to_equations. lia. }
clear Hn4. destruct Rn4 as [[q4 Hq4] Rn4].
zstep. setreg 12%Z (Z_to_bv 64 (c * BC4)) ltac:(unfold BC4; brute256 c Rc).

mst k 4%nat ltac:(symmetry; apply le4_bcast; lia).
zstep. mst (k + n4 - 4)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
zstep. if_cases K9'; zify_cond K9'. { fin. }
mst (k + 4)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + 8)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
zstep.
mst (k + n4 - 12)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + n4 - 8)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
zstep. if_cases K25; zify_cond K25. { fin. }
mst (k + 12)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + 16)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + 20)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + 24)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).

zstep.
remember (Z.land (A + k) 4) as k4 eqn:Hk4.
assert (Rk4 : ((k4 = 0 \/ k4 = 4) /\ (A + k + k4 + 24) mod 8 = 0)%Z).
{ subst k4. rewrite land4_of_aligned by lia. Z.div_mod_to_equations. lia. }
clear Hk4.
zstep. zstep. zstep.
mst (k + n4 - 28)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + n4 - 24)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + n4 - 20)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + n4 - 16)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
zstep. if_cases K32; zify_cond K32. { fin. }

zstep. zstep. zstep. zstep. setreg 12%Z (Z_to_bv 64 (c * BC8)) ltac:(unfold BC4, BC8; brute256 c Rc).
zstep.
replace (A + k + (k4 + 24))%Z with (A + (k + k4 + 24))%Z by lia.
eapply (memset_loop _ c (k + k4 + 24) _ (k + n4 - 28) _ _ _ _ _ eq_refl Hc ARR); try eassumption; try lia.
exists (q4 - Z.div k4 4 - 6)%Z. lia.
Qed.
End Proofs.

Lemma memset_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (junk : list byte),
rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
mem_inv asegs m ->
evt asegs (memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdb750) fc None m (seg_rom asegs)).
Proof.
intros until junk. intros DST MI.
eapply memset_body; [exact MI | | exact DST].
pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R. cbn. lia.
Qed.
End Mq3.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Uaccess.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Qc6I QJFf QDM6.
Import QvG1.
Import ListNotations.
Open Scope bv_scope.

Definition sysret_entry := 0xcca08%Z.
Definition read_entry := 0xe1270%Z.
Definition close_entry := 0xe1190%Z.
Definition open_entry := 0xcc924%Z.

Definition sysret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r errv : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (sysret_val r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' (errno_addr tp) [C4 (sysret_errno r errv)].

Lemma sysret_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(errv : word) (lo : Z),
stk asegs m lo (bv_unsigned sp) ->
rw_cells asegs m (errno_addr tp) [C4 errv] ->
mem_inv asegs m ->
(lo <= bv_unsigned sp - 16)%Z ->
(errno_addr tp + 4 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= errno_addr tp)%Z ->
(164 <= bv_unsigned tp)%Z ->
evt asegs (sysret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 errv F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcca08) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros ST ERR MI LO SEP TP.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
pose proof (wmono_refl asegs m) as WM.
do 3 step. if_cases Hc; zify_cond Hc.
-
step. unfold sysret_post, sysret_val, sysret_errno. rewrite (errno_of_small a0) by lia. finish.
- carve_frame 16%nat ST.
do 14 step.
pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
rewrite negw_errno in ERR by lia.
unfold sysret_post, sysret_val, sysret_errno. rewrite (errno_of_big a0) by lia.
release_frame FR ST (bv_unsigned sp).
finish.
Qed.

Definition read_ret (a : read_ans) : word :=
match a with RdErr _ => Z_to_bv 64 (-1) | RdData bs => Z_to_bv 64 (Z.of_nat (length bs)) end.

Definition read_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(B : Z) (n : nat) (junk : list byte) (errv : word) (lo : Z) (m : word -> option byte)
(a : read_ans) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (read_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (B, B + Z.of_nat n); (errno_addr tp, errno_addr tp + 4)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ match a with
| RdErr e => rw_cells asegs m' B [CB n junk]
/\ rw_cells asegs m' (errno_addr tp) [C4 (Z_to_bv 64 e)] /\ (1 <= e <= 4095)%Z
| RdData bs => rw_cells asegs m' B [CB (length bs) bs; CB (n - length bs) (skipn (length bs) junk)]
/\ rw_cells asegs m' (errno_addr tp) [C4 errv] /\ (length bs <= n)%nat
end.

Definition close_ret (a : sret) : word :=
match a with
| SVal _ => Z_to_bv 64 0
| SErr e => if (e =? EINTR)%Z then Z_to_bv 64 0 else Z_to_bv 64 (-1)
end.
Definition close_errno (a : sret) (errv : word) : word :=
match a with
| SVal _ => errv
| SErr e => if (e =? EINTR)%Z then errv else Z_to_bv 64 e
end.

Definition close_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(errv : word) (lo : Z) (m : word -> option byte) (a : sret) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (close_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' (errno_addr tp) [C4 (close_errno a errv)].

Definition got_ssp := 0xe6b80%Z.
Definition ssp_guard := 0x642ea0%Z.

Definition open_ret (a : sret) : word :=
match a with SVal fd => Z_to_bv 64 fd | SErr _ => Z_to_bv 64 (-1) end.
Definition open_errno (a : sret) (errv : word) : word :=
match a with SVal _ => errv | SErr e => Z_to_bv 64 e end.

Definition open_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(P : Z) (path : list byte) (errv canary : word) (lo : Z) (m : word -> option byte) (a : sret) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (open_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' (errno_addr tp) [C4 (open_errno a errv)]
/\ bytes_at asegs m' P (path ++ [Z_to_bv 8 0])
/\ rw_cells asegs m' got_ssp [C8 (Z_to_bv 64 ssp_guard)]
/\ rw_cells asegs m' ssp_guard [C8 canary]
/\ match a with SVal fd => (3 <= fd <= 4096)%Z | SErr e => (1 <= e <= 4095)%Z end.

End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCNF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Export QDM6.Mq0.
Export QCNF.Mq1.
Import ListNotations.
Open Scope bv_scope.

Lemma b2z_Zb2z : b2z = Z.b2z. Proof. reflexivity. Qed.

Ltac zb_masks_in H :=
repeat match type of H with
| context [Z.land ?x ?m] =>
is_Zlit_zb m;
let k := eval vm_compute in (Z.log2 (m + 1)) in
let m' := eval vm_compute in (2 ^ k - 1)%Z in
constr_eq m m';
let p := eval vm_compute in (2 ^ k)%Z in
replace (Z.land x m) with (x mod p)%Z in H
by (symmetry; change m with (2^k - 1)%Z; change p with (2^k)%Z; apply zb_land_mask; lia)
end.

Ltac zs_wrap e ::= zs_wrap_land e. Ltac mkr__zs_wrap_0 e := zs_wrap_land e.
Ltac zs_wrap_in e H ::= zs_wrap_land_in e H. Ltac mkr__zs_wrap_in_1 e H := zs_wrap_land_in e H.
Ltac zs_idioms ::= zs_idioms_land. Ltac mkr__zs_idioms_2 := zs_idioms_land.
Ltac zs_idioms_in H ::= zs_idioms_land_in H. Ltac mkr__zs_idioms_in_3 H := zs_idioms_land_in H.

Ltac unfold_sf_in H :=
cbv beta delta [add64 sub64 mul64 shl64 not64 ltu64 eqz64 nez64 zext32 sext32 srliw mulhu
is_neg64 sra63 lt_s64 lo64 hi64 wrap64 b2z
ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI] in H. Ltac mkr__unfold_sf_in_4 H := cbv beta delta [add64 sub64 mul64 shl64 not64 ltu64 eqz64 nez64 zext32 sext32 srliw mulhu
is_neg64 sra63 lt_s64 lo64 hi64 wrap64 b2z
ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI] in H.
Ltac unfold_sf :=
cbv beta delta [add64 sub64 mul64 shl64 not64 ltu64 eqz64 nez64 zext32 sext32 srliw mulhu
is_neg64 sra63 lt_s64 lo64 hi64 wrap64 b2z
ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI].

Ltac norm_model H := unfold_sf_in H; zb_fold_lits_in H.

Ltac get_head t := lazymatch t with ?g _ => get_head g | _ => t end.

Tactic Notation "model_hyp" ident(HR) constr(t) :=
assert (HR : t = t) by reflexivity;
let h := get_head t in unfold h in HR at 2;
norm_model HR.

Notation W64 := 18446744073709551615%Z.

Ltac model_eval :=
lazy -[Z.shiftr Z.shiftl Z.land Z.lor Z.lxor Z.lnot Z.mul Z.add Z.sub Z.opp Z.modulo Z.div
Z.ltb Z.eqb Z.leb Z.pow bv_unsigned].

Tactic Notation "model_end" constr(X) constr(t) :=
replace (Z_to_bv 64 X) with (Z_to_bv 64 t) by (f_equal; model_eval; reflexivity).

Lemma lo64_mk128' : forall hi lo, (0 <= lo < 2^64)%Z -> (0 <= hi)%Z -> lo64 (mk128 hi lo) = lo.
Proof.
intros hi lo Hlo Hhi. unfold lo64, mk128. rewrite wrap64_mod.
rewrite <- Z.land_ones by lia. apply Z.bits_inj'. intros i Hi.
rewrite Z.land_spec, Z.lor_spec, Z.shiftl_spec by lia.
destruct (Z.lt_ge_cases i 64).
- rewrite Z.ones_spec_low, (Z.testbit_neg_r _ (i - 64)) by lia. cbn. apply andb_true_r.
- rewrite Z.ones_spec_high by lia. rewrite andb_false_r.
symmetry. destruct (Z.eq_dec lo 0) as [->|]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64%Z; [apply Z.log2_lt_pow2; lia|lia].
Qed.

Lemma lo64_mk128 : forall hi lo, (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z -> lo64 (mk128 hi lo) = lo.
Proof. intros. apply lo64_mk128'; lia. Qed.

Lemma hi64_mk128 : forall hi lo, (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z -> hi64 (mk128 hi lo) = hi.
Proof.
intros hi lo Hlo Hhi. unfold hi64, mk128. rewrite wrap64_mod.
rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
rewrite (Z.shiftr_div_pow2 lo), Z.div_small, Z.lor_0_r by lia. apply Z.mod_small. lia.
Qed.

Lemma lor_disjoint_add : forall a b, Z.land a b = 0%Z -> Z.lor a b = (a + b)%Z.
Proof. intros a b H. rewrite <- Z.lxor_lor by exact H. symmetry. apply Z.add_nocarry_lxor. exact H. Qed.

Lemma land_even_mask : forall y, Z.land y 18446744073709551614 = (Z.land y 18446744073709551615 - Z.land y 1)%Z.
Proof.
intros y. change 18446744073709551615%Z with (Z.lor 18446744073709551614 1).
rewrite Z.land_lor_distr_r, lor_disjoint_add; [lia|].
rewrite (Z.land_comm (Z.land y _) (Z.land y 1)), Z.land_assoc, (Z.land_comm (Z.land y 1) y), Z.land_assoc, Z.land_diag.
rewrite <- Z.land_assoc. change (Z.land 1 18446744073709551614) with 0%Z. apply Z.land_0_r.
Qed.

Lemma land_1 : forall y, Z.land y 1 = (y mod 2)%Z.
Proof. intros. change 1%Z with (Z.ones 1) at 1. rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_W64 : forall y, Z.land y 18446744073709551615 = (y mod 2^64)%Z.
Proof. intros. change 18446744073709551615%Z with (Z.ones 64). apply Z.land_ones. lia. Qed.

Lemma round_even_idiom : forall x, (0 <= x)%Z ->
Z_to_bv 64 (Z.land (x + 1) 18446744073709551614) = Z_to_bv 64 (x + Z.land x 1).
Proof.
intros x Hx. apply Z_to_bv_eqm. rewrite land_even_mask, land_W64, !land_1.
Z.div_mod_to_equations. lia.
Qed.

Ltac bool_atom_cases :=
repeat match goal with
| |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b)
| |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
| |- context [Z.leb ?a ?b] => destruct (Z.leb_spec0 a b)
end.

Ltac weq :=
first [ reflexivity
| f_equal; zeq
| rewrite round_even_idiom by zrange_nonneg; weq_arith
| weq_arith ]
with weq_arith :=
apply Z_to_bv_eqm; rewrite ?land_even_mask, ?land_1; zb_masks; cbv delta [Z.b2z]; cbn [negb];
bool_atom_cases; cbn [negb]; pose_word_ranges; Z.div_mod_to_equations; lia.

Ltac ms_eq :=
first [ reflexivity
| lazymatch goal with
| |- Z_to_bv 64 _ = Z_to_bv 64 _ => weq
| |- _ = Z_to_bv 64 (bv_unsigned _) => symmetry; apply Z_to_bv_bv_unsigned
| |- Z_to_bv 64 (bv_unsigned _) = _ => apply Z_to_bv_bv_unsigned
| |- context [mkR] => unfold mkR; ms_eq
| |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ => f_equal; ms_eq
| |- TNode _ _ _ = TNode _ _ _ => f_equal; ms_eq
| |- Some _ = Some _ => f_equal; ms_eq
end ].

Ltac sf_finish :=
apply evt_done;
lazymatch goal with |- ?P ?ms => try unfold P end; hnf;
rewrite ?lo64_mk128, ?hi64_mk128 by zrange;
repeat (lazymatch goal with |- ex _ => eexists end);
split; [ ms_eq | repeat match goal with |- _ /\ _ => split end; try assumption ].

Lemma signed_of_Z : forall z, (-2^63 <= z < 2^63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof.
intros z Hz. rewrite Z_to_bv_signed. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 64 / 2)%Z with (2^63)%Z. lia.
Qed.
Ltac signed_lits_in H :=
repeat match type of H with
| context [bv_signed (Z_to_bv 64 ?z)] => rewrite (signed_of_Z z) in H by lia
end.

Lemma mod64_land63 : forall y, (y mod 64 = Z.land y 63)%Z.
Proof. intros. change 63%Z with (Z.ones 6). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land63_idem : forall y, Z.land (Z.land y 63) 63 = Z.land y 63.
Proof. intros. rewrite <- Z.land_assoc. reflexivity. Qed.

Ltac zs_idioms_sf :=
match goal with
| |- context [Z.shiftr (Z.land (Z.shiftl ?x ?k) 18446744073709551615) ?k] =>
rewrite (zb_shl_shr_land x k) by (first [lia | zrange_nonneg])
| |- context [(?y mod 64)%Z] => rewrite (mod64_land63 y), ?land63_idem
end.
Ltac zs_idioms_sf_in H :=
match type of H with
| context [Z.shiftr (Z.land (Z.shiftl ?x ?k) 18446744073709551615) ?k] =>
rewrite (zb_shl_shr_land x k) in H by (first [lia | zrange_nonneg])
| context [(?y mod 64)%Z] => rewrite (mod64_land63 y), ?land63_idem in H
end.
Ltac zs_idioms ::= zs_idioms_sf. Ltac mkr__zs_idioms_5 := zs_idioms_sf.
Ltac zs_idioms_in H ::= zs_idioms_sf_in H. Ltac mkr__zs_idioms_in_6 H := zs_idioms_sf_in H.
End Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbcP_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QwAs.
Import QvDJ.Mq3.
Import QbcP_c1.Mq0.
Import ListNotations. Local Ltac QoSL.cell_of_bytes bs ::= QoSL.mkr__cell_of_bytes_10 bs. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.

Ltac reg_val r :=
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end)
end.
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.

Ltac name_list xs L :=
lazymatch type of L with
| length _ = O => destruct xs; [clear L | cbn in L; discriminate]
| length _ = S _ => let x := fresh "x" in let xs' := fresh "xs" in
destruct xs as [|x xs']; [cbn in L; discriminate | cbn in L; apply Nat.succ_inj in L; name_list xs' L]
end.

Ltac window base k HW :=
lazymatch goal with SRC : bytes_at ?segs ?m ?S ?src |- _ =>
let xs := fresh "xs" in let L := fresh "L" in
destruct (window_ex src base k ltac:(lia)) as [xs [HW L]]; name_list xs L
end.

Ltac woff base c :=
let cz := eval vm_compute in (Z.of_nat c) in
lazymatch cz with 0%Z => base | _ => constr:((base + cz)%Z) end.

Ltac anorm REG imm :=
lazymatch REG with
| Z_to_bv 64 ?E =>
let E' :=
lazymatch imm with
| 0%Z => E
| _ => lazymatch E with
| Z.add ?x ?a =>
let isl := lazymatch a with Z0 => true | Zpos _ => true | Zneg _ => true | _ => false end in
lazymatch isl with
| true => let s := eval vm_compute in (a + imm)%Z in
lazymatch s with 0%Z => x | _ => constr:(Z.add x s) end
| false => constr:(Z.add E imm)
end
| _ => constr:(Z.add E imm)
end
end in
constr:(Z_to_bv 64 E')
| _ => lazymatch imm with 0%Z => REG | _ => constr:(Z_to_bv 64 (bv_unsigned REG + imm)%Z) end
end.

Ltac cur_mem_addr :=
lazymatch goal with |- evt ?segs _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) =>
let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
lazymatch fw with Some ?w =>
let d := eval vm_compute in (decode_any w) in
lazymatch d with
| Some (Load _ _ _ ?rs ?imm, _) =>
let rz := eval vm_compute in (bv_unsigned rs) in
let immz := eval vm_compute in (bv_signed imm) in
let REG := reg_val rz in anorm REG immz
| Some (Store _ ?rs _ ?imm, _) =>
let rz := eval vm_compute in (bv_unsigned rs) in
let immz := eval vm_compute in (bv_signed imm) in
let REG := reg_val rz in anorm REG immz
end end end. Ltac mkr__cur_mem_addr_0 := lazymatch goal with |- evt ?segs _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) =>
let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
lazymatch fw with Some ?w =>
let d := eval vm_compute in (decode_any w) in
lazymatch d with
| Some (Load _ _ _ ?rs ?imm, _) =>
let rz := eval vm_compute in (bv_unsigned rs) in
let immz := eval vm_compute in (bv_signed imm) in
let REG := reg_val rz in anorm REG immz
| Some (Store _ ?rs _ ?imm, _) =>
let rz := eval vm_compute in (bv_unsigned rs) in
let immz := eval vm_compute in (bv_signed imm) in
let REG := reg_val rz in anorm REG immz
end end end.

Ltac addr_tac :=
unfold wa;
first [ reflexivity
| f_equal; lia
| lazymatch goal with |- ?v = Z_to_bv 64 ?e =>
replace e with (bv_unsigned v) by lia; symmetry; apply Z_to_bv_bv_unsigned end ].

Definition ld_facts (base : Z) (c j kw : nat) (i : Z) : Prop :=
(0 <= base)%Z /\ (c + j <= kw)%nat /\ (i = base + Z.of_nat c)%Z.

Lemma mc_read1 : forall segs m S src kw base xsw c i a b,
bytes_at segs m S src -> firstn kw (skipn (Z.to_nat base) src) = xsw ->
ld_facts base c 1 kw i -> nth_error xsw c = Some b -> a = wa (S + i) ->
ov_read_bytes segs m a 1 = Some [b].
Proof.
intros segs m S src kw base xsw c i a b SRC HW (Hb & Hc & Hi) Hn Ha.
eapply (u8ro_read segs m S src i b a SRC); [ | lia | exact Ha ].
rewrite <- Hn. eapply window_nth; eauto; lia.
Qed.

Lemma mc_read4 : forall segs m S src kw base xsw c i a,
bytes_at segs m S src -> firstn kw (skipn (Z.to_nat base) src) = xsw -> length xsw = kw ->
ld_facts base c 4 kw i -> a = wa (S + i) ->
exists w, ov_read_bytes segs m a 4 = Some w /\ w = firstn 4 (skipn c xsw) /\ length w = 4%nat.
Proof.
intros segs m S src kw base xsw c i a SRC HW HL (Hb & Hc & Hi) ->.
assert (L : (Z.to_nat base + kw <= length src)%nat).
{ apply (f_equal (@length byte)) in HW. rewrite length_firstn, length_skipn, HL in HW. lia. }
exists (firstn 4 (skipn (Z.to_nat i) src)). split; [|split].
- apply (bytes_at_read segs m S src i 4 SRC); lia.
- eapply window_sub; eauto; lia.
- rewrite length_firstn, length_skipn. lia.
Qed.

Definition st_facts (S D n base : Z) (c k kw : nat) (P : Z) : Prop :=
((0 <= base)%Z /\ (c + k <= kw)%nat /\ P = base + Z.of_nat c /\ 0 <= P /\ P + Z.of_nat k <= n /\
(S + n <= D \/ D + n <= S) /\ 0 <= D /\ D + n <= 2^64)%Z.

Lemma mc_store_ok : forall segs m1 S D n src kw base xsw c k P bs a,
u8arr segs m1 D bs -> copied src bs (Z.to_nat P) -> length src = Z.to_nat n ->
firstn kw (skipn (Z.to_nat base) src) = xsw ->
st_facts S D n base c k kw P -> a = wa (D + P) -> store_ok segs m1 a k = true.
Proof.
intros segs m1 S D n src kw base xsw c k P bs a DST [L _] LEN _ (_ & _ & _ & HP & Hk & _) Ha.
eapply (u8arr_store_ok_n segs m1 D bs P k a DST); [lia | | exact Ha]. rewrite L, LEN. lia.
Qed.

Lemma mc_store : forall segs m0 m1 S D n src kw base xsw c k P bs xs a,
bytes_at segs m1 S src -> u8arr segs m1 D bs -> copied src bs (Z.to_nat P) ->
mem_inv segs m1 -> munch [(D, D + n)]%Z m0 m1 -> wmono segs m0 m1 ->
length src = Z.to_nat n -> firstn kw (skipn (Z.to_nat base) src) = xsw ->
st_facts S D n base c k kw P ->
xs = firstn k (skipn c xsw) -> length xs = k -> a = wa (D + P) ->
bytes_at segs (write_to_mem m1 a xs) S src /\
u8arr segs (write_to_mem m1 a xs) D (upd_bytes bs (Z.to_nat P) xs) /\
copied src (upd_bytes bs (Z.to_nat P) xs) (Z.to_nat (P + Z.of_nat k)) /\
mem_inv segs (write_to_mem m1 a xs) /\ munch [(D, D + n)]%Z m0 (write_to_mem m1 a xs) /\
wmono segs m0 (write_to_mem m1 a xs).
Proof.
intros segs m0 m1 S D n src kw base xsw c k P bs xs a SRC DST CP MI MU WM LEN HW
(Hb & Hc & HPb & HP & Hk & SEP & D0 & Dn) Hxs Hl Ha.
pose proof (proj1 CP) as Lbs.
assert (SOK : store_ok segs m1 a (length xs) = true).
{ rewrite Hl. eapply mc_store_ok; eauto. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]; eauto; lia. }
subst a. split; [|split; [|split; [|split; [|split]]]].
- apply bytes_at_write_other; [exact SRC | lia | lia | rewrite LEN; lia].
- apply (u8arr_write_bytes segs m1 D bs P xs DST); [lia|]. rewrite Lbs, LEN. lia.
- apply (f_equal (@length byte)) in CP || idtac.
rewrite <- Hl. apply copied_updZ; [exact CP | lia | | rewrite LEN; lia].
rewrite Hl, Hxs. eapply window_sub; eauto; lia.
- apply mem_inv_store; assumption.
- apply munch_write; [exact MU | lia | lia |]. cbn [inside]. left. lia.
- apply wmono_write. exact WM.
Qed.

Ltac ld1 HW c :=
lazymatch type of HW with firstn ?k (skipn (Z.to_nat ?base) ?src) = ?xs =>
lazymatch goal with SRC : bytes_at ?segs ?m ?S src |- _ =>
let i := woff base c in
let a := cur_mem_addr in
let RD := fresh "RD" in
pose proof (mc_read1 segs m S src k base xs c i a _ SRC HW
ltac:(unfold ld_facts; lia) ltac:(reflexivity) ltac:(addr_tac)) as RD;
zstep; try clear RD;
lazymatch goal with |- evt _ _ ?ms => let ms' := eval cbv beta in ms in change ms with ms' end
end end.

Ltac ld4 HW c w :=
lazymatch type of HW with firstn ?k (skipn (Z.to_nat ?base) ?src) = ?xs =>
lazymatch goal with SRC : bytes_at ?segs ?m ?S src |- _ =>
let i := woff base c in
let a := cur_mem_addr in
let RD := fresh "RD" in let Ew := fresh "E" w in let Lw := fresh "L" w in
destruct (mc_read4 segs m S src k base xs c i a SRC HW ltac:(reflexivity) ltac:(unfold ld_facts; lia) ltac:(addr_tac))
as [w [RD [Ew Lw]]];
cbn [firstn skipn] in Ew;
zstep; try clear RD
end end.

Ltac zify_bytes :=
repeat match goal with
| |- context [bv_unsigned ?b] =>
lazymatch type of b with
| byte => pose proof (byte_range b); generalize dependent (bv_unsigned b); intros
end
end.
Ltac solve_le K :=
repeat match goal with H : ?w = _ :: _ |- _ => is_var w; subst w end;
first [ apply le4_of_mod32; [reflexivity|] | apply le1_of_mod8 ];
cbn [map le_val]; rewrite ?unsigned_lit_wrap; rewrite ?lw_unsigned4;
zify_bytes;
rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2, ?bv_swrap32_eq, ?bv_wrap32_eq by lia;
lazymatch K with
| 0%Z => idtac
| _ => first [ rewrite (lor_add _ _ K); [ | lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia ]
| rewrite (lor_add' _ _ K); [ | lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia ] ]
end;
Z.div_mod_to_equations; lia.

Ltac by_byte := symmetry; apply le1_zxb.
Ltac by_lw := symmetry; lazymatch goal with |- le4 (sext 64 (bv_extract 0 32 (le_bytes_to_word ?w))) = _ =>
lazymatch goal with L : length w = 4%nat, E : w = _ |- _ => rewrite (le4_lw w L); exact E end end.

Ltac by_le K :=
symmetry;
repeat match goal with H : ?w = _ :: _ |- _ => is_var w; subst w end;
first
[ lazymatch goal with
| |- le4 (Z_to_bv 64 (Z.lor (Z.modulo (bv_swrap 32 (Z.shiftr _ ?k)) _) _)) = _ =>
lazymatch k with 24%Z => apply merge_a24 | 16%Z => apply merge_a16 | 8%Z => apply merge_a8 end
| |- le4 (Z_to_bv 64 (Z.lor _ (Z.modulo (bv_swrap 32 (Z.shiftr _ ?k)) _))) = _ =>
lazymatch k with 24%Z => apply merge_r24 | 16%Z => apply merge_r16 | 8%Z => apply merge_r8 end
| |- le1 (Z_to_bv 64 (Z.shiftr _ ?k)) = _ =>
lazymatch k with 8%Z => apply lwb1 | 16%Z => apply lwb2 end
| |- le1 (sext _ _) = _ => apply lwb0
end
| solve_le K ].

Ltac cst_core HW c k bytes_tac SF :=
lazymatch type of HW with firstn ?kw (skipn (Z.to_nat ?base) ?src) = ?xsw =>
let xs := eval cbv beta iota delta [firstn skipn] in (firstn k (skipn c xsw)) in
let kz := eval vm_compute in (Z.of_nat k) in
lazymatch goal with
| SRC : bytes_at ?segs ?m ?S src, DST : u8arr ?segs ?m ?D ?bs, CP : copied src ?bs (Z.to_nat ?P),
MI : mem_inv ?segs ?m, MU : munch _ ?m0 ?m, WM : wmono ?segs ?m0 ?m, LEN : length src = Z.to_nat _
|- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs0) _) =>
replace bs0 with xs by bytes_tac;
let SRC' := fresh "SRC" in let DST' := fresh "DST" in let CP' := fresh "CP" in
let MI' := fresh "MI" in let MU' := fresh "MU" in let WM' := fresh "WM" in
destruct (mc_store segs m0 m S D _ src kw base xsw c k P bs xs a SRC DST CP MI MU WM LEN HW SF
ltac:(reflexivity) ltac:(reflexivity) ltac:(addr_tac))
as (SRC' & DST' & CP' & MI' & MU' & WM');
change (Z.of_nat k) with kz in CP';
clear SRC DST CP MI MU WM SF;
repeat match goal with
| H : store_ok segs m _ _ = true |- _ => clear H
| H : ov_read_bytes segs m _ _ = Some _ |- _ => clear H
end;
let m' := fresh "m" in remember (write_to_mem m a xs) as m' eqn:Heqm; clear Heqm; try clear m;
let bs' := fresh "bs" in remember (upd_bytes bs (Z.to_nat P) xs) as bs' eqn:Heqbs; clear Heqbs; try clear bs;
rename SRC' into SRC; rename DST' into DST; rename CP' into CP;
rename MI' into MI; rename MU' into MU; rename WM' into WM
end end.

Ltac cst HW c k bytes_tac :=
lazymatch goal with SF : st_facts _ _ _ _ c k _ _ |- _ => cst_core HW c k bytes_tac SF end.

Ltac st HW c k bytes_tac :=
lazymatch type of HW with firstn ?kw (skipn (Z.to_nat ?base) ?src) = ?xsw =>
lazymatch goal with
| SRC : bytes_at ?segs ?m ?S src, DST : u8arr ?segs ?m ?D ?bs, CP : copied src ?bs (Z.to_nat ?P),
MU : munch [(_, _ + ?n)%Z] _ ?m, LEN : length src = Z.to_nat _ |- _ =>
let a := cur_mem_addr in
let SF := fresh "SF" in let SOK := fresh "SOK" in
assert (SF : st_facts S D n base c k kw P) by (unfold st_facts; lia);
pose proof (mc_store_ok segs m S D n src kw base xsw c k P bs a DST CP LEN HW SF ltac:(addr_tac)) as SOK;
zstep; [ cst_core HW c k bytes_tac SF | .. ]
end end.
Ltac st1 HW c := st HW c 1%nat by_byte.
Ltac st4 HW c := st HW c 4%nat by_lw.

Ltac by_win HW c :=
lazymatch type of HW with firstn ?k (skipn (Z.to_nat ?base) ?src) = ?xs =>
first [ rewrite (window_sub src xs base k c 4 _ HW) by lia
| symmetry; rewrite (window_sub src xs base k c 4 _ HW) by lia ];
cbn [firstn skipn]; first [ assumption | symmetry; assumption | reflexivity ]
end.

Ltac cp_norm P' :=
lazymatch goal with CP : copied ?src ?bs (Z.to_nat ?P) |- _ => replace (Z.to_nat P) with (Z.to_nat P') in CP by lia end.

Definition mc_inv (segs : list MemImageType.Segment) (S D : Z) (src : list byte) (W : list ivl)
(m0 m1 : word -> option byte) (bs : list byte) (P : Z) : Prop :=
bytes_at segs m1 S src /\ u8arr segs m1 D bs /\ copied src bs (Z.to_nat P) /\
mem_inv segs m1 /\ munch W m0 m1 /\ wmono segs m0 m1.

Ltac open_inv H := destruct H as (SRC & DST & CP & MI & MU & WM).

Ltac inv_tac :=
lazymatch goal with
| |- mc_inv _ _ _ _ _ _ _ _ _ =>
split; [eassumption | split; [eassumption | split; [ | repeat split; eassumption ]]];
lazymatch goal with CP : copied _ _ (Z.to_nat ?P) |- copied _ _ (Z.to_nat ?P') =>
first [ exact CP | replace (Z.to_nat P') with (Z.to_nat P) by lia; exact CP ] end
end.

Ltac use_side :=
first [ inv_tac | idtac ]; try assumption; try (f_equal; lia); try lia;
try (rewrite ?unsigned_lit by lia; Z.div_mod_to_equations; lia);
try (rewrite ?Z.add_0_r, ?Z.sub_0_r; symmetry; apply Z_to_bv_bv_unsigned).
Tactic Notation "use" uconstr(L) := eapply L; use_side.

Ltac finish2 :=
apply evt_done;
lazymatch goal with |- ?P ?ms => try unfold P | _ => idtac end;
hnf;
repeat (lazymatch goal with |- ex _ => eexists end);
lazymatch goal with
| |- _ = _ /\ _ => split; [ cbv delta [mkR]; reflexivity | ]
| |- _ = _ => cbv delta [mkR]; reflexivity
end;
repeat match goal with |- _ /\ _ => split end; try assumption.

Ltac mc_fin :=
lazymatch goal with
| DST : u8arr _ ?m1 _ ?bs, CP : copied ?src ?bs (Z.to_nat ?P), L : length ?src = _ |- _ =>
let E := fresh "E" in
pose proof (copied_all _ _ _ CP ltac:(lia)) as E; rewrite E in DST; clear E CP;
apply rw_cells_of_u8arr in DST; rewrite L in DST
end;
finish2.

Ltac fix_lit_store :=
try (lazymatch goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
end).
Ltac lstep := zstep; fix_lit_store.
End Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import Qc27 Qc6I QJFf QDM6.
Import QCiC Qpj5.Mq1 QvDJ.Mq2 Q67d QCiC.Mq0 Q6sh QKTr.
Import QZzg.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.cell_of_bytes bs ::= QoSL.mkr__cell_of_bytes_10 bs. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Section AImplT.

Variable atn : node -> machine_state -> Prop.

Local Notation implMA := (@implMG PStateA asegs atn).

Definition aimplT {R} (t : T R) (s : PStateA) (Q : R -> PStateA -> machine_state -> Prop) (ms : machine_state) : Prop :=
implMA (membedA t) s Q ms.

Lemma aimplT_ret {R} (r : R) s Q ms : evt asegs (Q r s) ms -> aimplT (tret r) s Q ms.
Proof. intros H. unfold aimplT, tret. cbn [membedA]. apply implMG_ret. exact H. Qed.

Lemma aimplT_unr {R} w s (Q : R -> PStateA -> machine_state -> Prop) ms : aimplT (tunr w) s Q ms.
Proof. unfold aimplT, tunr. cbn [membedA]. apply implMG_unr. Qed.

Lemma aimplT_spin {R} s (Q : R -> PStateA -> machine_state -> Prop) ms :
evt asegs (fun ms1 => atn NSetTid ms1) ms -> aimplT (R:=R) tspin s Q ms.
Proof.
intros H. unfold aimplT, tspin. cbn [membedA]. unfold mspin. apply implMG_sys.
eapply evt_mono; [exact H|]. intros ms1 Hat. split; [exact Hat|]. intros rsp a E. discriminate.
Qed.

Lemma aimplT_mono {R} (t : T R) s Q Q' ms :
aimplT t s Q ms -> (forall r s' ms', Q r s' ms' -> Q' r s' ms') -> aimplT t s Q' ms.
Proof. intros H HQ. unfold aimplT in *. eapply implMG_mono; eauto. Qed.

Lemma aimplT_evt {R} (t : T R) s Q P ms :
evt asegs P ms -> (forall ms', P ms' -> aimplT t s Q ms') -> aimplT t s Q ms.
Proof. intros H K. unfold aimplT in *. eapply implMG_evt; eauto. Qed.

Lemma aimplT_from_evt {R} (t : T R) s Q ms :
evt asegs (fun ms' => aimplT t s Q ms') ms -> aimplT t s Q ms.
Proof. intros H. eapply aimplT_evt; [exact H|]. intros ms' H'; exact H'. Qed.

Lemma aimpl_vis_unfold {R} n (k : resp -> itree node R) Q ms :
impl asegs atn (Vis n k) Q ms = evt asegs (fun ms1 => atn n ms1 /\ forall rsp, impl asegs atn (k rsp) Q (nret ms1 rsp)) ms.
Proof. reflexivity. Qed.

Lemma aimpl_bind_mono {A B C} (t : itree node A) (f1 : A -> itree node B) (f2 : A -> itree node C) Q1 Q2 ms :
impl asegs atn (Qc6I.bind _ t f1) Q1 ms ->
(forall r ms', impl asegs atn (f1 r) Q1 ms' -> impl asegs atn (f2 r) Q2 ms') ->
impl asegs atn (Qc6I.bind _ t f2) Q2 ms.
Proof.
revert ms. induction t as [r|n k IH]; intros ms H K; cbn [Qc6I.bind] in *.
- apply K. exact H.
- rewrite aimpl_vis_unfold in H. rewrite aimpl_vis_unfold. eapply evt_mono; [exact H|].
intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
Qed.

Lemma implMA_mspin_any {A B} s (Q : A -> PStateA -> machine_state -> Prop) (Q' : B -> PStateA -> machine_state -> Prop) ms :
implMA mspin s Q ms -> implMA mspin s Q' ms.
Proof.
unfold implMG, mspin, msys, impl. cbn. intros H. eapply evt_mono; [exact H|].
intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. cbn. apply evt_done. exact I.
Qed.

Lemma aimplT_bind {R S} (t : T R) (f : R -> T S) s Q1 Q ms :
aimplT t s Q1 ms ->
(forall r s' ms', Q1 r s' ms' -> aimplT (f r) s' Q ms') ->
aimplT (tbind t f) s Q ms.
Proof.
unfold aimplT, tbind. revert s ms. induction t as [[r| |w]|e k IH]; intros s ms H K.
- cbn [sbind membedA]. cbn [membedA] in H. unfold implMG, mret in H. cbn in H.
eapply implMG_evt; [exact H|]. intros ms' H1. exact (K r s ms' H1).
- cbn [sbind membedA]. cbn [membedA] in H. eapply implMA_mspin_any. exact H.
- cbn [sbind membedA]. apply implMG_unr.
- cbn [sbind membedA]. cbn [membedA] in H. unfold implMG, mbind, ebind in H |- *.
eapply aimpl_bind_mono; [exact H|]. intros [|[z s']] ms' H1; cbn in *.
+ exact H1.
+ eapply IH; [exact H1| exact K].
Qed.

Lemma aimplT_vis {R} e (k : ansA -> T R) s Q1 Q ms :
implMA (ev_stepA e) s Q1 ms ->
(forall a s' ms', Q1 a s' ms' -> aimplT (k a) s' Q ms') ->
aimplT (tvis e k) s Q ms.
Proof.
intros H K. unfold aimplT, tvis. cbn [membedA]. eapply implMG_bind; [exact H|]. intros a s' ms' H1. apply (K a s' ms' H1).
Qed.

Lemma implMA_msys_enode {A} n (dec : resp -> option A) s (P : A -> machine_state -> Prop) ms :
impl asegs atn (enode n dec) (epost P) ms ->
implMA (msys n dec) s (fun a s' ms' => s' = s /\ P a ms') ms.
Proof.
intros H. unfold implMG, msys. cbn. unfold enode in H. cbn in H.
eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. specialize (Hk rsp).
destruct (dec rsp) as [a|]; cbn in *.
- eapply evt_mono; [exact Hk|]. intros ms' HP. cbn. auto.
- exact Hk.
Qed.

Lemma aimplT_map_fixed {R} addr len (k : ansA -> T R) s (P : ansA -> machine_state -> Prop) Q ms :
impl asegs atn (enode (NMmap addr len PROT_RW FL_FIXED) (dec_fixedA addr len)) (epost P) ms ->
(forall a ms', P a ms' -> aimplT (k a) s Q ms') ->
aimplT (tvis (EvMapFixed addr len) k) s Q ms.
Proof.
intros H K. eapply aimplT_vis; [apply implMA_msys_enode; exact H|]. intros a s' ms' [-> HP]. apply K. exact HP.
Qed.

Lemma aimplT_map_anon {R} len avoid (k : ansA -> T R) s (P : ansA -> machine_state -> Prop) Q ms :
impl asegs atn (enode (NMmap 0 len PROT_RW FL_ANON) (dec_anonA len avoid)) (epost P) ms ->
(forall a ms', P a ms' -> aimplT (k a) s Q ms') ->
aimplT (tvis (EvMapAnon len avoid) k) s Q ms.
Proof.
intros H K. eapply aimplT_vis; [apply implMA_msys_enode; exact H|]. intros a s' ms' [-> HP]. apply K. exact HP.
Qed.

Lemma ev_stepA_state e s Q ms :
implMA (ev_stepA e) s Q ms -> implMA (ev_stepA e) s (fun a s' ms' => s' = s /\ Q a s' ms') ms.
Proof.
assert (GEN : forall A n (dec : resp -> option A) (Q : A -> PStateA -> machine_state -> Prop),
implMA (msys n dec) s Q ms -> implMA (msys n dec) s (fun a s' ms' => s' = s /\ Q a s' ms') ms).
{ intros A n dec Q0 H. unfold implMG, msys, enode in *. cbv beta in H. cbv beta. rewrite aimpl_vis_unfold in H. rewrite aimpl_vis_unfold.
eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. specialize (Hk rsp).
destruct (dec rsp) as [a|]; cbn in *; [|exact Hk]. eapply evt_mono; [exact Hk|]. intros ms' HQ; cbn; auto. }
destruct e; cbn [ev_stepA]; apply GEN.
Qed.

Lemma aimplT_state {R} (t : T R) s Q ms :
aimplT t s Q ms -> aimplT t s (fun r s' ms' => s' = s /\ Q r s' ms') ms.
Proof.
unfold aimplT. revert s ms. induction t as [[r| |w]|e k IH]; intros s ms H.
- cbn [membedA] in *. unfold implMG, mret in *. cbn in *. eapply evt_mono; [exact H|]. intros ms' HQ; cbn; auto.
- cbn [membedA] in *. eapply implMA_mspin_any. exact H.
- cbn [membedA]. apply implMG_unr.
- cbn [membedA] in *. eapply implMG_bind.
+ eapply ev_stepA_state. unfold implMG, mbind, ebind in H.

instantiate (1 := fun a s' ms' => impl asegs atn (membedA (k a) s') (epost (fun p => Q (fst p) (snd p))) ms').
unfold implMG. revert H. generalize (ev_stepA e s). intros t H.
revert ms H. induction t as [x|n kk IHt]; intros ms H; cbn [Qc6I.bind] in *.
* unfold epost in H |- *. destruct x as [|[a s']]; cbn in *; apply evt_done; [exact I| exact H].
* rewrite aimpl_vis_unfold in H. rewrite aimpl_vis_unfold. eapply evt_mono; [exact H|].
intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. apply IHt. apply Hk.
+ intros a s' ms' [-> H1]. cbn in H1. apply IH. exact H1.
Qed.

Lemma raw_malloc_A_intro L n s Q ms :
aimplT (asan_malloc L (ps_a s) n) s (fun ra s1 ms' => Q (fst ra) (set_a (snd ra) s1) ms') ms ->
implMA (raw_malloc_A L n) s Q ms.
Proof.
intros H. unfold raw_malloc_A.
eapply implMG_bind with (Q1 := fun x s' ms' => x = s /\ s' = s /\ ms' = ms).
{ apply implMG_get. apply evt_done. repeat split; reflexivity. }
intros x s' ms' (-> & -> & ->).
eapply implMG_bind. { apply aimplT_state in H. exact H. }
intros [r a'] s1 ms1 [-> HQ]. cbn in HQ.
eapply implMG_bind with (Q1 := fun _ s2 ms2 => s2 = set_a a' s /\ ms2 = ms1).
{ apply implMG_upd. apply evt_done. split; reflexivity. }
intros [] s2 ms2 [-> ->]. apply implMG_ret. apply evt_done. exact HQ.
Qed.

End AImplT.
End Mq7.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u.
Import QvDJ.Mq3.
Import Qtfh.
Import QZzg.
Import ListNotations. Local Ltac QoSL.cell_of_bytes bs ::= QoSL.mkr__cell_of_bytes_10 bs. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.

Definition memset_entry := 0xdde14%Z.

Ltac with_arr tac :=
lazymatch goal with
| ARR : u8arr ?segs ?m ?A ?bs, FIL : filled ?cb ?bs _, LEN : length ?bs = _ |- _ => tac segs ARR FIL LEN A cb
end.

Ltac brute256 c Rc :=
first [ apply word_eq_of_eqb | apply Z.eqb_eq | idtac ];
repeat match goal with H : context [c] |- _ => tryif constr_eq H Rc then fail else clear H end;
revert c Rc; apply brute256_ok; vm_compute; reflexivity.

Ltac reg_val r :=
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end)
end.

Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.

Lemma land4_of_aligned : forall x, (0 <= x)%Z -> (x mod 4 = 0)%Z -> Z.land x 4 = (x mod 8)%Z.
Proof.
intros x Hx H4.
transitivity (Z.land (x mod 8) 4).
{ change 8%Z with (2^3)%Z. rewrite <- Z.land_ones by lia. change (Z.ones 3) with 7%Z.
rewrite <- Z.land_assoc. reflexivity. }
assert (R : (x mod 8 = 0 \/ x mod 8 = 4)%Z) by (Z.div_mod_to_equations; lia).
destruct R as [R|R]; rewrite R; reflexivity.
Qed.

Definition memset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 a2 : word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' (bv_unsigned a0)
[CB (Z.to_nat (bv_unsigned a2)) (repeat (Z_to_bv 8 (bv_unsigned a1 mod 256)) (Z.to_nat (bv_unsigned a2)))].

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Hypothesis MI0 : mem_inv asegs m.
Hypothesis AB : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 <= 2^64 /\ 0 <= bv_unsigned a2 < 2^64)%Z.

Notation A := (bv_unsigned a0).
Notation n := (bv_unsigned a2).
Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
Notation POST := (memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m).

Notation ST pc mm x11 x12 x13 x14 x15 x16 :=
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

Ltac fin_with cover :=
zstep;
with_arr ltac:(fun segs ARR FIL LEN A cb =>
let E := fresh "E" in
pose proof (filled_all _ _ _ FIL ltac:(cover)) as E;
rewrite LEN in E; rewrite E in ARR;
apply rw_cells_of_u8arr in ARR; rewrite repeat_length in ARR);
finish; subst; assumption.
Ltac fin := fin_with ltac:(intros j Hj; cbv beta; lia).
Ltac disj_lia := first [ lia | right; lia | left; disj_lia ].

Lemma memset_loop : forall (K : nat) (c p r e : Z) (m1 : word -> option byte) (bs : list byte) (Q : Z -> Prop)
(x15 x16 : word),
Z.to_nat r = K ->
c = (bv_unsigned a1 mod 256)%Z ->
u8arr asegs m1 A bs -> filled (Z_to_bv 8 c) bs Q -> length bs = Z.to_nat n ->
mem_inv asegs m1 -> munch W m m1 -> wmono asegs m m1 ->
(forall j, (0 <= j < p \/ e <= j < n) -> Q j)%Z ->
(0 <= p)%Z -> (32 <= r)%Z -> (exists q, r = 4 * q)%Z -> (p + r <= n)%Z -> (e + 28 <= p + r)%Z ->
evt asegs POST (ST 0xddeec m1 (Z_to_bv 64 (A + p)) (Z_to_bv 64 (c * BC8)) (Z_to_bv 64 31) (Z_to_bv 64 r) x15 x16).
Proof using AB.
induction K as [K IH] using lt_wf_ind; intros c p r e m1 bs Q x15 x16 HK Hc ARR FIL LEN MI MU WM HQ Hp Hr [q4 Hq4] Hpr He;
assert (Rc : (0 <= c < 256)%Z) by (subst c; apply Z.mod_pos_bound; lia).
mst p 8%nat ltac:(symmetry; apply le8_bcast; lia).
mst (p + 8)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
mst (p + 16)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
mst (p + 24)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
zstep. zstep. zstep.
if_cases KK; zify_cond KK.
-
replace (A + p + 32)%Z with (A + (p + 32))%Z by lia.
replace (r + -32)%Z with (r - 32)%Z by lia.
eapply (IH (Z.to_nat (r - 32)) ltac:(lia) c (p + 32)%Z (r - 32)%Z e _ _ _ x15 x16 eq_refl Hc ARR); try eassumption; try lia.
2:{ exists (q4 - 8)%Z. lia. }
intros j Hj.
destruct (Z_lt_le_dec j p) as [Hlt|Hge]. { left; left; left; left. apply HQ. lia. }
destruct (Z_lt_le_dec j (p + 32)) as [Hlt2|Hge2]. 2:{ left; left; left; left. apply HQ. lia. }
assert (D : ((p <= j < p + 8 \/ p + 8 <= j < p + 16) \/ (p + 16 <= j < p + 24 \/ p + 24 <= j < p + 32))%Z) by lia.
destruct D as [[?|?]|[?|?]]; [left; left; left; right| left; left; right| left; right| right]; lia.
- fin_with ltac:(intros j Hj; destruct (Z_lt_le_dec j p); [repeat left; apply HQ; lia|];
destruct (Z_lt_le_dec j (p + 32)); [|repeat left; apply HQ; lia]; disj_lia).
Qed.

Lemma memset_body : forall junk,
rw_cells asegs m A [CB (Z.to_nat n) junk] ->
evt asegs POST (ST 0xdde14 m a1 a2 a3 a4 a5 a6).
Proof using AB MI0.
intros junk DST. pose proof MI0 as MI.
pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (zr_word a1) as R1. unfold inr64 in R1.
remember (bv_unsigned a1 mod 256)%Z as c eqn:Hc.
assert (Rc : (0 <= c < 256)%Z) by (subst c; apply Z.mod_pos_bound; lia).
pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as ARR.
pose proof (rw_cells_CB_length _ _ _ _ _ DST) as LEN.
pose proof (filled_init (Z_to_bv 8 c) junk) as FIL.

zstep. if_cases K0; zify_cond K0. { fin. }
assert (MF : ms_facts A n 0 1) by (unfold ms_facts; lia).
pose proof (ms_store_ok asegs _ A n _ 0 1 a0 ARR LEN MF (eq_sym (Z_to_bv_plus0 a0))) as SOK.
zstep. ms_arr_store MF ltac:(rewrite Hc, le1_byte; reflexivity).
zstep. zstep. mst (n - 1)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
zstep. if_cases K3; zify_cond K3. { fin. }
mst 1%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
mst 2%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
zstep.
mst (n - 3)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
mst (n - 2)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
zstep. if_cases K7; zify_cond K7. { fin. }
mst 3%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
zstep.
mst (n - 4)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
zstep. if_cases K9; zify_cond K9. { fin. }

zstep. zstep.
setreg 16%Z (Z_to_bv 64 (c * 2^56)) ltac:(apply Z_to_bv_eqm; rewrite Z.shiftl_mul_pow2 by lia; subst c; Z.div_mod_to_equations; lia).
zstep. zstep.
remember (Z.land (bv_swrap 32 (0 - A) mod 18446744073709551616) 3) as k eqn:Hk.
assert (Rk : (0 <= k < 4 /\ (A + k) mod 4 = 0)%Z).
{ subst k. change 3%Z with (2^2 - 1)%Z. rewrite zb_land_mask by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ (Z.of_N 32 - 1))%Z with (2^31)%Z. change (2 ^ Z.of_N 32)%Z with (2^32)%Z.
Z.div_mod_to_equations. lia. }
clear Hk.
zstep. zstep. zstep. zstep. zstep.
change 18446744073709551612%Z with (2^64 - 2^2)%Z. rewrite land_align_down by lia.
remember (n - k - (n - k) mod 2^2)%Z as n4 eqn:Hn4.
assert (Rn4 : (exists q, n4 = 4 * q)%Z /\ (n - k - 3 <= n4 <= n - k)%Z).
{ split. { exists ((n - k) / 4)%Z. subst n4. Z.div_mod_to_equations. lia. } subst n4. Z.div_mod_to_equations. lia. }
clear Hn4. destruct Rn4 as [[q4 Hq4] Rn4].
zstep. setreg 12%Z (Z_to_bv 64 (c * BC4)) ltac:(unfold BC4; brute256 c Rc).

mst k 4%nat ltac:(symmetry; apply le4_bcast; lia).
zstep. mst (k + n4 - 4)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
zstep. if_cases K9'; zify_cond K9'. { fin. }
mst (k + 4)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + 8)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
zstep.
mst (k + n4 - 12)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + n4 - 8)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
zstep. if_cases K25; zify_cond K25. { fin. }
mst (k + 12)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + 16)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + 20)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + 24)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).

zstep.
remember (Z.land (A + k) 4) as k4 eqn:Hk4.
assert (Rk4 : ((k4 = 0 \/ k4 = 4) /\ (A + k + k4 + 24) mod 8 = 0)%Z).
{ subst k4. rewrite land4_of_aligned by lia. Z.div_mod_to_equations. lia. }
clear Hk4.
zstep. zstep. zstep.
mst (k + n4 - 28)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + n4 - 24)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + n4 - 20)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + n4 - 16)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
zstep. if_cases K32; zify_cond K32. { fin. }

zstep. zstep. zstep. zstep. setreg 12%Z (Z_to_bv 64 (c * BC8)) ltac:(unfold BC4, BC8; brute256 c Rc).
zstep.
replace (A + k + (k4 + 24))%Z with (A + (k + k4 + 24))%Z by lia.
eapply (memset_loop _ c (k + k4 + 24) _ (k + n4 - 28) _ _ _ _ _ eq_refl Hc ARR); try eassumption; try lia.
exists (q4 - Z.div k4 4 - 6)%Z. lia.
Qed.
End Proofs.

Lemma memset_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (junk : list byte),
rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
mem_inv asegs m ->
evt asegs (memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdde14) fc None m (seg_rom asegs)).
Proof.
intros until junk. intros DST MI.
eapply memset_body; [exact MI | | exact DST].
pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R. cbn. lia.
Qed.
End Mq8.

Module Mq9.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 QwAs.
Import QvDJ.Mq3.
Import QZzg.
Import ListNotations. Local Ltac QoSL.cell_of_bytes bs ::= QoSL.mkr__cell_of_bytes_10 bs. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.

Definition memchr_entry := 0xdd914%Z.

Section ZFacts.
Open Scope Z_scope.
Lemma lxor_lt_256 : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lxor a b < 256.
Proof.
intros a b Ha Hb. pose proof (Z.lxor_nonneg a b) as Hnn. split; [lia|].
destruct (Z.eq_dec (Z.lxor a b) 0) as [->|Hnz]; [lia|].
apply (proj2 (Z.log2_lt_pow2 (Z.lxor a b) 8 ltac:(lia))).
pose proof (Z.log2_lxor a b ltac:(lia) ltac:(lia)) as Hl.
assert (Z.log2 a < 8). { destruct (Z.eq_dec a 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
assert (Z.log2 b < 8). { destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
lia.
Qed.

Lemma lxor_split : forall x y x' y', 0 <= x < 256 -> 0 <= x' < 256 -> 0 <= y -> 0 <= y' ->
Z.lxor (x + 256 * y) (x' + 256 * y') = Z.lxor x x' + 256 * Z.lxor y y'.
Proof.
intros x y x' y' Hx Hx' Hy Hy'.
pose proof (lxor_lt_256 x x' Hx Hx') as Hl.
apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, !testbit_split by lia.
destruct (i <? 8); rewrite Z.lxor_spec; reflexivity.
Qed.

Lemma le_val_nonneg : forall bs, bytes_ok bs -> 0 <= le_val bs.
Proof. intros bs H. pose proof (le_val_range bs H). lia. Qed.

Lemma le_val_xor_bcast : forall bs c, bytes_ok bs -> 0 <= c < 256 ->
Z.lxor (le_val bs) (c * ones (length bs)) = le_val (map (fun b => Z.lxor b c) bs).
Proof.
induction bs as [|b bs IH]; intros c Hok Hc.
- cbn. rewrite Z.mul_0_r. reflexivity.
- inversion Hok as [|b0 bs0 Hb Hbs]; subst. cbn [le_val ones length map].
replace (c * (1 + 256 * ones (length bs))) with (c + 256 * (c * ones (length bs))) by lia.
rewrite lxor_split; try lia.
+ rewrite IH by assumption. reflexivity.
+ apply le_val_nonneg. exact Hbs.
+ pose proof (le_val_range (repeat 1 (length bs))) as Hr. assert (0 <= ones (length bs)); [|nia].
clear. induction (length bs); cbn; lia.
Qed.

Lemma bytes_ok_xor : forall bs c, bytes_ok bs -> 0 <= c < 256 -> bytes_ok (map (fun b => Z.lxor b c) bs).
Proof.
intros bs c H Hc. unfold bytes_ok in *. rewrite Forall_map. eapply Forall_impl; [|exact H].
intros b Hb. apply lxor_lt_256; assumption.
Qed.

Lemma In0_xor : forall bs c, In 0 (map (fun b => Z.lxor b c) bs) <-> In c bs.
Proof.
intros bs c. rewrite in_map_iff. split.
- intros (b & Hb & Hin). apply Z.lxor_eq in Hb. subst. exact Hin.
- intros Hin. exists c. split; [apply Z.lxor_nilpotent| exact Hin].
Qed.
End ZFacts.

Definition memchr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 a2 : word) (buf : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
(Z_to_bv 64 (memchr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf))
a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ bytes_at asegs m' (bv_unsigned a0) buf.

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf : list byte).
Hypothesis MI : mem_inv asegs m.
Hypothesis BUF : bytes_at asegs m (bv_unsigned a0) buf.
Hypothesis OK : memchr_ok (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf.
Let MU : munch [] m m := munch_refl [] m.
Let WM : wmono asegs m m := wmono_refl asegs m.

Notation A := (bv_unsigned a0).
Notation n := (bv_unsigned a2).
Notation c := ((bv_unsigned a1) mod 256)%Z.
Notation len := (Z.of_nat (length buf)).
Notation POST := (memchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 buf m).

Notation ST pc x5 x10 x12 x13 x14 x15 x16 x17 :=
(MS (mkR ra sp gp tp x5 t1 t2 s0 s1 x10 (Z_to_bv 64 c) x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom asegs)).
Notation CMAGIC := 72340172838076672%Z.
Notation HIGHS := 9259542123273814144%Z.
Notation ONES := 72340172838076673%Z.

Definition NOB (i : Z) : Prop :=
forall j b, (j < Z.to_nat i)%nat -> nth_error buf j = Some b -> bv_unsigned b <> c.

Lemma A_bound : (0 <= A /\ A + len <= 2^64 /\ 0 <= n < 2^64 /\ 0 <= c < 256)%Z.
Proof.
pose proof (bytes_at_bound _ _ _ _ BUF).
pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R.
pose proof (Z.mod_pos_bound (bv_unsigned a1) 256). cbn. lia.
Qed.

Lemma NOB_0 : NOB 0.
Proof. intros j b Hj. cbn in Hj. lia. Qed.

Lemma NOB_S : forall i b, (0 <= i)%Z -> NOB i -> nth_error buf (Z.to_nat i) = Some b -> bv_unsigned b <> c -> NOB (i + 1).
Proof.
intros i b Hi H Hn Hb j b' Hj Hn'.
destruct (Nat.eq_dec j (Z.to_nat i)) as [->|NE]. { rewrite Hn in Hn'. injection Hn' as <-. exact Hb. }
eapply H; [|exact Hn']. lia.
Qed.

Lemma ok_cases :
(exists j b, Z.of_nat j < n /\ nth_error buf j = Some b /\ bv_unsigned b = c /\
(forall j' b', (j' < j)%nat -> nth_error buf j' = Some b' -> bv_unsigned b' <> c) /\
(n <= len \/ Z.of_nat j + 1 + (- (A + Z.of_nat j + 1)) mod 8 <= len))%Z
\/ ((forall j b, (Z.of_nat j < n)%Z -> nth_error buf j = Some b -> bv_unsigned b <> c) /\ (n <= len)%Z).
Proof.
pose proof OK as H. unfold memchr_ok in H.
destruct (find_byte c (firstn (Z.to_nat n) buf)) as [j|] eqn:FB.
- left. destruct (find_byte_Some _ _ _ FB) as (Hl & (b & Hn & Hb) & Hmin).
rewrite firstn_length in Hl.
rewrite nth_error_firstn in Hn. replace (Nat.ltb j (Z.to_nat n)) with true in Hn by (symmetry; apply Nat.ltb_lt; lia).
exists j, b. repeat split; try assumption; try lia.
intros j' b' Hj' Hn'. eapply Hmin; [exact Hj'|]. rewrite nth_error_firstn.
replace (Nat.ltb j' (Z.to_nat n)) with true by (symmetry; apply Nat.ltb_lt; lia). exact Hn'.
- right. split; [|exact H]. intros j b Hj Hn. eapply (find_byte_None _ _ FB j). rewrite nth_error_firstn.
replace (Nat.ltb j (Z.to_nat n)) with true by (symmetry; apply Nat.ltb_lt; lia). exact Hn.
Qed.

Lemma readable : forall i, (0 <= i < n)%Z -> NOB i -> exists b, nth_error buf (Z.to_nat i) = Some b.
Proof.
intros i Hi HN. destruct (nth_error buf (Z.to_nat i)) as [b|] eqn:E; [exists b; reflexivity|].
exfalso. apply nth_error_None in E.
destruct ok_cases as [(j & b & Hj & Hn & Hb & Hmin & _)|(Hall & Hlen)]; [|lia].
pose proof (nth_error_lt _ _ _ Hn).
destruct (Nat.lt_ge_cases j (Z.to_nat i)) as [Hlt|Hge]; [|lia].
exact (HN _ _ Hlt Hn Hb).
Qed.

Lemma readable8 : forall i, (0 <= i)%Z -> (i + 8 <= n)%Z -> ((A + i) mod 8 = 0)%Z -> NOB i ->
(Z.to_nat i + 8 <= length buf)%nat.
Proof.
intros i Hi Hi8 Hal HN.
destruct ok_cases as [(j & b & Hj & Hn & Hb & Hmin & Hsl)|(Hall & Hlen)]; [|lia].
pose proof (nth_error_lt _ _ _ Hn).
destruct (Nat.lt_ge_cases j (Z.to_nat i)) as [Hlt|Hge]. { exfalso. exact (HN _ _ Hlt Hn Hb). }
destruct Hsl as [Hsl|Hsl]; [lia|].
destruct (Nat.lt_ge_cases j (Z.to_nat i + 8)) as [Hlt8|]; [|lia].
Z.div_mod_to_equations. lia.
Qed.

Lemma res_found : forall i b, (0 <= i < n)%Z -> NOB i -> nth_error buf (Z.to_nat i) = Some b -> bv_unsigned b = c ->
memchr_res A c n buf = (A + i)%Z.
Proof.
intros i b Hi HN Hn Hb. unfold memchr_res.
rewrite (find_byte_charact c _ (Z.to_nat i) b); [lia| | exact Hb|].
- rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia). exact Hn.
- intros j b' Hj Hn'. rewrite nth_error_firstn in Hn'. destruct (Nat.ltb j (Z.to_nat n)); [|discriminate].
exact (HN _ _ Hj Hn').
Qed.

Lemma res_none : NOB n -> memchr_res A c n buf = 0%Z.
Proof.
intros HN. unfold memchr_res. rewrite find_byte_None_intro; [reflexivity|].
intros j b Hn. rewrite nth_error_firstn in Hn. destruct (Nat.ltb_spec0 j (Z.to_nat n)); [|discriminate].
exact (HN j b ltac:(lia) Hn).
Qed.

Lemma memchr_tail : forall (k : nat) (i : Z) (x5 x12 x14 x15 x16 x17 : word),
Z.to_nat (n - i) = k -> (0 <= i < n)%Z -> NOB i ->
evt asegs POST (ST 0xdd9b4 x5 (Z_to_bv 64 (A + i)) x12 (Z_to_bv 64 (n - i)) x14 x15 x16 x17).
Proof.
induction k as [|k IH]; intros i x5 x12 x14 x15 x16 x17 Hk Hi HN; pose proof A_bound as AB; [lia|].
destruct (readable i Hi HN) as [b Hn]. pose proof (nth_error_lt _ _ _ Hn).
pose proof (u8ro_read asegs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD.
zstep. zstep. if_cases K; zify_cond K.
-  zstep. rewrite <- (res_found i b Hi HN Hn K). finish.
- zstep. zstep. zstep. if_cases K0; zify_cond K0.
+ replace (n - i + -1)%Z with (n - (i + 1))%Z by lia. replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
apply (IH (i + 1)%Z); try lia. eapply NOB_S; eauto; lia.
+  zstep. zstep. rewrite <- res_none at 1. { finish. }
replace n with (i + 1)%Z by lia. eapply NOB_S; eauto; lia.
Qed.

Lemma memchr_tail_entry : forall (i : Z) (x5 x13 x14 x15 x16 x17 : word),
(0 <= i <= n)%Z -> NOB i ->
evt asegs POST (ST 0xdd9ac x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) x13 x14 x15 x16 x17).
Proof.
intros i x5 x13 x14 x15 x16 x17 Hi HN; pose proof A_bound as AB.
zstep. zstep. if_cases K; zify_cond K.
- zstep. zstep. rewrite <- res_none at 1. { finish. } replace n with i by lia. exact HN.
- apply (memchr_tail (Z.to_nat (n - i)) i); lia || assumption.
Qed.

Lemma memchr_words : forall (k : nat) (i : Z) (x5 x17 : word),
Z.to_nat (n - i) = k -> (0 <= i)%Z -> (i + 8 <= n)%Z -> ((A + i) mod 8 = 0)%Z -> NOB i ->
evt asegs POST (ST 0xdd988 x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) (Z_to_bv 64 CMAGIC) (Z_to_bv 64 HIGHS)
(Z_to_bv 64 (c * ONES)) (Z_to_bv 64 7) x17).
Proof.
induction k as [k IH] using lt_wf_ind; intros i x5 x17 Hk Hi Hi8 Hal HN; pose proof A_bound as AB.
pose proof (readable8 i Hi Hi8 Hal HN) as HW.
pose proof (bytes_at_read asegs m A buf i 8 BUF ltac:(lia) HW) as RD.
set (chunk := firstn 8 (skipn (Z.to_nat i) buf)) in RD.
assert (CL : length chunk = 8%nat). { subst chunk. rewrite firstn_length, skipn_length. lia. }
pose proof (le_val_range _ (bytes_ok_map chunk)) as WR. rewrite length_map, CL in WR.
change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR.
pose proof (le_val_range _ (bytes_ok_xor _ c (bytes_ok_map chunk) ltac:(lia))) as XR. rewrite !length_map, CL in XR.
change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in XR.
do 6 zstep.
rewrite (load8_le_val chunk CL).
replace (Z.lxor (le_val (map bv_unsigned chunk)) (c * ONES)) with (le_val (map (fun b => Z.lxor b c) (map bv_unsigned chunk))).
2:{ change ONES with ONES64b. rewrite <- ones_8, <- CL, <- (length_map bv_unsigned). symmetry. apply le_val_xor_bcast; [apply bytes_ok_map| lia]. }
if_cases K; zify_cond K.
-
clear K. destruct (readable i ltac:(lia) HN) as [b Hn].
pose proof (u8ro_read asegs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD1.
zstep. zstep. zstep. if_cases Kb; zify_cond Kb.
+ zstep. zstep. zstep. if_cases Kz; zify_cond Kz; [|exfalso; lia].
replace (n - i + -1)%Z with (n - (i + 1))%Z by lia. replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
apply (memchr_tail (Z.to_nat (n - (i + 1))) (i + 1)); try lia. eapply NOB_S; eauto; lia.
+ zstep. zstep. rewrite <- (res_found i b ltac:(lia) HN Hn Kb). finish.
- apply (haszero64_clang _ (bytes_ok_xor _ c (bytes_ok_map chunk) ltac:(lia)) ltac:(rewrite !length_map; exact CL)) in K.
rewrite In0_xor in K.

assert (HN8 : NOB (i + 8)).
{ intros j b Hj Hn. destruct (Nat.lt_ge_cases j (Z.to_nat i)) as [Hlt|Hge]. { exact (HN _ _ Hlt Hn). }
intros Hb. apply K. rewrite <- Hb. apply in_map. subst chunk.
apply nth_error_In with (n := (j - Z.to_nat i)%nat).
rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia).
rewrite nth_error_skipn, <- Hn. f_equal. lia. }
zstep. zstep. zstep. if_cases K8; zify_cond K8.
+ replace (A + i + 8)%Z with (A + (i + 8))%Z by lia. replace (n - i + -8)%Z with (n - (i + 8))%Z by lia.
apply (IH (Z.to_nat (n - (i + 8)))); try lia; try exact HN8. all: Z.div_mod_to_equations; lia.
+ replace (A + i + 8)%Z with (A + (i + 8))%Z by lia. replace (n - i + -8)%Z with (n - (i + 8))%Z by lia.
apply (memchr_tail_entry (i + 8)); try lia; exact HN8.
Qed.

Lemma memchr_mid : forall (i : Z) (x5 x13 x14 x15 x16 x17 : word),
(0 <= i <= n)%Z -> NOB i -> ((bv_unsigned x14 = 0)%Z <-> i = n) -> (i = n \/ (A + i) mod 8 = 0)%Z ->
evt asegs POST (ST 0xdd958 x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) x13 x14 x15 x16 x17).
Proof.
intros i x5 x13 x14 x15 x16 x17 Hi HN H14 Hal; pose proof A_bound as AB.
zstep. if_cases K; zify_cond K.
-  apply H14 in K. subst i. zstep. zstep. rewrite <- res_none at 1; [finish| exact HN].
- assert (Hin : (i < n)%Z). { destruct (Z.eq_dec i n) as [E|]; [|lia]. exfalso. apply K. apply H14. exact E. }
destruct Hal as [|Hal]; [lia|].
destruct (readable i ltac:(lia) HN) as [b Hn].
pose proof (u8ro_read asegs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD.
zstep. zstep. if_cases Kb; zify_cond Kb.
+ apply memchr_tail_entry; [lia| exact HN].
+ zstep. zstep. if_cases K8; zify_cond K8.
* apply memchr_tail_entry; [lia| exact HN].
* do 7 zstep.
apply (memchr_words (Z.to_nat (n - i)) i); try lia. exact HN.
Qed.

Lemma b2z_word_zero_iff : forall t, bv_unsigned (Z_to_bv 64 (Z.b2z t)) = 0%Z <-> t = false.
Proof. intros t. rewrite unsigned_lit by (destruct t; cbn; lia). destruct t; cbn; split; intros; first [congruence | lia]. Qed.

Lemma memchr_head : forall (k : nat) (i : Z) (x5 x13 x14 x17 : word),
Z.to_nat (n - i) = k -> (0 <= i < n)%Z -> NOB i -> ((A + i) mod 8 <> 0)%Z ->
evt asegs POST (ST 0xdd930 x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) x13 x14 (Z_to_bv 64 (A + i + 1)) (Z_to_bv 64 1) x17).
Proof.
induction k as [|k IH]; intros i x5 x13 x14 x17 Hk Hi HN Hal; pose proof A_bound as AB; [lia|].
destruct (readable i Hi HN) as [b Hn]. pose proof (nth_error_lt _ _ _ Hn).
pose proof (u8ro_read asegs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD.
zstep. zstep. zstep. if_cases Kb; zify_cond Kb.
-  apply (memchr_tail (Z.to_nat (n - i)) i); try lia. exact HN.
- pose proof (NOB_S i b ltac:(lia) HN Hn Kb) as HN1.
zstep. zstep. zstep. zstep. zstep. if_cases Kal; zify_cond Kal.
+ replace (A + i + 1)%Z with (A + (i + 1))%Z by lia. replace (n - i + -1)%Z with (n - (i + 1))%Z by lia.
apply (memchr_mid (i + 1)); try lia; try exact HN1.
* rewrite b2z_word_zero_iff, Z.ltb_ge. lia.
* right. revert Kal. zb_masks. intros Kal. Z.div_mod_to_equations; lia.
+ zstep. zstep. if_cases K1; zify_cond K1.
* replace (A + i + 2)%Z with (A + (i + 1) + 1)%Z by lia.
replace (A + i + 1)%Z with (A + (i + 1))%Z by lia. replace (n - i + -1)%Z with (n - (i + 1))%Z by lia.
apply (IH (i + 1)%Z); try lia; try exact HN1. revert Kal. zb_masks. intros Kal. Z.div_mod_to_equations; lia.
* replace (A + i + 1)%Z with (A + (i + 1))%Z by lia. replace (n - i + -1)%Z with (n - (i + 1))%Z by lia.
apply (memchr_mid (i + 1)); try lia; try exact HN1. rewrite b2z_word_zero_iff, Z.ltb_ge. lia.
Qed.

Lemma memchr_body :
evt asegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdd914) fc None m (seg_rom asegs)).
Proof.
pose proof A_bound as AB. pose proof (zr_word a1) as R1. unfold inr64 in R1.
zstep. replace (Z.land (bv_unsigned a1) 255) with c.
2:{ change 255%Z with (2^8 - 1)%Z. rewrite zb_land_mask by lia. reflexivity. }
zstep. zstep. zstep. if_cases Kal; zify_cond Kal.
-
eapply evt_eq.
2:{ apply (memchr_mid 0 t0 (Z_to_bv 64 (Z.land A 7)) (Z_to_bv 64 (Z.b2z (0 <? n)%Z)) a5 a6 a7); try lia.
- apply NOB_0. - rewrite b2z_word_zero_iff, Z.ltb_ge. lia.
- right. revert Kal. zb_masks. intros Kal. rewrite Z.add_0_r. exact Kal. }
unfold mkR. rewrite Z_to_bv_plus0, Z.sub_0_r, Z_to_bv_bv_unsigned. reflexivity.
- zstep. if_cases K0; zify_cond K0.
+
eapply evt_eq.
2:{ apply (memchr_mid 0 t0 (Z_to_bv 64 (Z.land A 7)) (Z_to_bv 64 (Z.b2z (0 <? n)%Z)) a5 a6 a7); try lia.
- apply NOB_0. - rewrite b2z_word_zero_iff, Z.ltb_ge. lia. }
unfold mkR. rewrite Z_to_bv_plus0, Z.sub_0_r, Z_to_bv_bv_unsigned. reflexivity.
+ zstep. zstep.
eapply evt_eq.
2:{ apply (memchr_head (Z.to_nat n) 0 t0 (Z_to_bv 64 (Z.land A 7)) (Z_to_bv 64 (Z.b2z (0 <? n)%Z)) a7); try lia.
- apply NOB_0. - revert Kal. zb_masks. intros Kal. rewrite Z.add_0_r. exact Kal. }
unfold mkR. rewrite Z_to_bv_plus0, Z.sub_0_r, Z_to_bv_bv_unsigned, Z.add_0_r. reflexivity.
Qed.
End Proofs.

Lemma memchr_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (buf : list byte),
bytes_at asegs m (bv_unsigned a0) buf ->
memchr_ok (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf ->
mem_inv asegs m ->
evt asegs (memchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 buf m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdd914) fc None m (seg_rom asegs)).
Proof. intros until buf. intros BUF OK MI. apply memchr_body; assumption. Qed.
End Mq9.

Module Mqa.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u.
Import QvDJ.Mq3.
Import Qtfh.
Import QZzg.
Import ListNotations. Local Ltac QoSL.cell_of_bytes bs ::= QoSL.mkr__cell_of_bytes_10 bs. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.

Definition memset_entry := 0xdde14%Z.

Ltac with_arr tac :=
lazymatch goal with
| ARR : u8arr ?segs ?m ?A ?bs, FIL : filled ?cb ?bs _, LEN : length ?bs = _ |- _ => tac segs ARR FIL LEN A cb
end.

Ltac brute256 c Rc :=
first [ apply word_eq_of_eqb | apply Z.eqb_eq | idtac ];
repeat match goal with H : context [c] |- _ => tryif constr_eq H Rc then fail else clear H end;
revert c Rc; apply brute256_ok; vm_compute; reflexivity.

Ltac reg_val r :=
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end)
end.

Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.

Lemma land4_of_aligned : forall x, (0 <= x)%Z -> (x mod 4 = 0)%Z -> Z.land x 4 = (x mod 8)%Z.
Proof.
intros x Hx H4.
transitivity (Z.land (x mod 8) 4).
{ change 8%Z with (2^3)%Z. rewrite <- Z.land_ones by lia. change (Z.ones 3) with 7%Z.
rewrite <- Z.land_assoc. reflexivity. }
assert (R : (x mod 8 = 0 \/ x mod 8 = 4)%Z) by (Z.div_mod_to_equations; lia).
destruct R as [R|R]; rewrite R; reflexivity.
Qed.

Definition memset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 a2 : word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' (bv_unsigned a0)
[CB (Z.to_nat (bv_unsigned a2)) (repeat (Z_to_bv 8 (bv_unsigned a1 mod 256)) (Z.to_nat (bv_unsigned a2)))].

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Hypothesis MI0 : mem_inv asegs m.
Hypothesis AB : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 <= 2^64 /\ 0 <= bv_unsigned a2 < 2^64)%Z.

Notation A := (bv_unsigned a0).
Notation n := (bv_unsigned a2).
Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
Notation POST := (memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m).

Notation ST pc mm x11 x12 x13 x14 x15 x16 :=
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

Ltac fin_with cover :=
zstep;
with_arr ltac:(fun segs ARR FIL LEN A cb =>
let E := fresh "E" in
pose proof (filled_all _ _ _ FIL ltac:(cover)) as E;
rewrite LEN in E; rewrite E in ARR;
apply rw_cells_of_u8arr in ARR; rewrite repeat_length in ARR);
finish; subst; assumption.
Ltac fin := fin_with ltac:(intros j Hj; cbv beta; lia).
Ltac disj_lia := first [ lia | right; lia | left; disj_lia ].

Lemma memset_loop : forall (K : nat) (c p r e : Z) (m1 : word -> option byte) (bs : list byte) (Q : Z -> Prop)
(x15 x16 : word),
Z.to_nat r = K ->
c = (bv_unsigned a1 mod 256)%Z ->
u8arr asegs m1 A bs -> filled (Z_to_bv 8 c) bs Q -> length bs = Z.to_nat n ->
mem_inv asegs m1 -> munch W m m1 -> wmono asegs m m1 ->
(forall j, (0 <= j < p \/ e <= j < n) -> Q j)%Z ->
(0 <= p)%Z -> (32 <= r)%Z -> (exists q, r = 4 * q)%Z -> (p + r <= n)%Z -> (e + 28 <= p + r)%Z ->
evt asegs POST (ST 0xddeec m1 (Z_to_bv 64 (A + p)) (Z_to_bv 64 (c * BC8)) (Z_to_bv 64 31) (Z_to_bv 64 r) x15 x16).
Proof using AB.
induction K as [K IH] using lt_wf_ind; intros c p r e m1 bs Q x15 x16 HK Hc ARR FIL LEN MI MU WM HQ Hp Hr [q4 Hq4] Hpr He;
assert (Rc : (0 <= c < 256)%Z) by (subst c; apply Z.mod_pos_bound; lia).
mst p 8%nat ltac:(symmetry; apply le8_bcast; lia).
mst (p + 8)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
mst (p + 16)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
mst (p + 24)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
zstep. zstep. zstep.
if_cases KK; zify_cond KK.
-
replace (A + p + 32)%Z with (A + (p + 32))%Z by lia.
replace (r + -32)%Z with (r - 32)%Z by lia.
eapply (IH (Z.to_nat (r - 32)) ltac:(lia) c (p + 32)%Z (r - 32)%Z e _ _ _ x15 x16 eq_refl Hc ARR); try eassumption; try lia.
2:{ exists (q4 - 8)%Z. lia. }
intros j Hj.
destruct (Z_lt_le_dec j p) as [Hlt|Hge]. { left; left; left; left. apply HQ. lia. }
destruct (Z_lt_le_dec j (p + 32)) as [Hlt2|Hge2]. 2:{ left; left; left; left. apply HQ. lia. }
assert (D : ((p <= j < p + 8 \/ p + 8 <= j < p + 16) \/ (p + 16 <= j < p + 24 \/ p + 24 <= j < p + 32))%Z) by lia.
destruct D as [[?|?]|[?|?]]; [left; left; left; right| left; left; right| left; right| right]; lia.
- fin_with ltac:(intros j Hj; destruct (Z_lt_le_dec j p); [repeat left; apply HQ; lia|];
destruct (Z_lt_le_dec j (p + 32)); [|repeat left; apply HQ; lia]; disj_lia).
Qed.

Lemma memset_body : forall junk,
rw_cells asegs m A [CB (Z.to_nat n) junk] ->
evt asegs POST (ST 0xdde14 m a1 a2 a3 a4 a5 a6).
Proof using AB MI0.
intros junk DST. pose proof MI0 as MI.
pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (zr_word a1) as R1. unfold inr64 in R1.
remember (bv_unsigned a1 mod 256)%Z as c eqn:Hc.
assert (Rc : (0 <= c < 256)%Z) by (subst c; apply Z.mod_pos_bound; lia).
pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as ARR.
pose proof (rw_cells_CB_length _ _ _ _ _ DST) as LEN.
pose proof (filled_init (Z_to_bv 8 c) junk) as FIL.

zstep. if_cases K0; zify_cond K0. { fin. }
assert (MF : ms_facts A n 0 1) by (unfold ms_facts; lia).
pose proof (ms_store_ok asegs _ A n _ 0 1 a0 ARR LEN MF (eq_sym (Z_to_bv_plus0 a0))) as SOK.
zstep. ms_arr_store MF ltac:(rewrite Hc, le1_byte; reflexivity).
zstep. zstep. mst (n - 1)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
zstep. if_cases K3; zify_cond K3. { fin. }
mst 1%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
mst 2%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
zstep.
mst (n - 3)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
mst (n - 2)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
zstep. if_cases K7; zify_cond K7. { fin. }
mst 3%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
zstep.
mst (n - 4)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
zstep. if_cases K9; zify_cond K9. { fin. }

zstep. zstep.
setreg 16%Z (Z_to_bv 64 (c * 2^56)) ltac:(apply Z_to_bv_eqm; rewrite Z.shiftl_mul_pow2 by lia; subst c; Z.div_mod_to_equations; lia).
zstep. zstep.
remember (Z.land (bv_swrap 32 (0 - A) mod 18446744073709551616) 3) as k eqn:Hk.
assert (Rk : (0 <= k < 4 /\ (A + k) mod 4 = 0)%Z).
{ subst k. change 3%Z with (2^2 - 1)%Z. rewrite zb_land_mask by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ (Z.of_N 32 - 1))%Z with (2^31)%Z. change (2 ^ Z.of_N 32)%Z with (2^32)%Z.
Z.div_mod_to_equations. lia. }
clear Hk.
zstep. zstep. zstep. zstep. zstep.
change 18446744073709551612%Z with (2^64 - 2^2)%Z. rewrite land_align_down by lia.
remember (n - k - (n - k) mod 2^2)%Z as n4 eqn:Hn4.
assert (Rn4 : (exists q, n4 = 4 * q)%Z /\ (n - k - 3 <= n4 <= n - k)%Z).
{ split. { exists ((n - k) / 4)%Z. subst n4. Z.div_mod_to_equations. lia. } subst n4. Z.div_mod_to_equations. lia. }
clear Hn4. destruct Rn4 as [[q4 Hq4] Rn4].
zstep. setreg 12%Z (Z_to_bv 64 (c * BC4)) ltac:(unfold BC4; brute256 c Rc).

mst k 4%nat ltac:(symmetry; apply le4_bcast; lia).
zstep. mst (k + n4 - 4)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
zstep. if_cases K9'; zify_cond K9'. { fin. }
mst (k + 4)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + 8)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
zstep.
mst (k + n4 - 12)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + n4 - 8)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
zstep. if_cases K25; zify_cond K25. { fin. }
mst (k + 12)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + 16)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + 20)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + 24)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).

zstep.
remember (Z.land (A + k) 4) as k4 eqn:Hk4.
assert (Rk4 : ((k4 = 0 \/ k4 = 4) /\ (A + k + k4 + 24) mod 8 = 0)%Z).
{ subst k4. rewrite land4_of_aligned by lia. Z.div_mod_to_equations. lia. }
clear Hk4.
zstep. zstep. zstep.
mst (k + n4 - 28)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + n4 - 24)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + n4 - 20)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + n4 - 16)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
zstep. if_cases K32; zify_cond K32. { fin. }

zstep. zstep. zstep. zstep. setreg 12%Z (Z_to_bv 64 (c * BC8)) ltac:(unfold BC4, BC8; brute256 c Rc).
zstep.
replace (A + k + (k4 + 24))%Z with (A + (k + k4 + 24))%Z by lia.
eapply (memset_loop _ c (k + k4 + 24) _ (k + n4 - 28) _ _ _ _ _ eq_refl Hc ARR); try eassumption; try lia.
exists (q4 - Z.div k4 4 - 6)%Z. lia.
Qed.
End Proofs.

Lemma memset_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (junk : list byte),
rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
mem_inv asegs m ->
evt asegs (memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdde14) fc None m (seg_rom asegs)).
Proof.
intros until junk. intros DST MI.
eapply memset_body; [exact MI | | exact DST].
pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R. cbn. lia.
Qed.
End Mqa.

Module Mqb.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Qc6I QJFf QDM6.
Import QZzg.
Import ListNotations. Local Ltac QoSL.cell_of_bytes bs ::= QoSL.mkr__cell_of_bytes_10 bs. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.

Definition sysret_entry := 0xcf0cc%Z.
Definition read_entry := 0xe3934%Z.
Definition close_entry := 0xe3854%Z.
Definition open_entry := 0xcefe8%Z.

Definition sysret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r errv : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (sysret_val r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' (errno_addr tp) [C4 (sysret_errno r errv)].

Lemma sysret_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(errv : word) (lo : Z),
stk asegs m lo (bv_unsigned sp) ->
rw_cells asegs m (errno_addr tp) [C4 errv] ->
mem_inv asegs m ->
(lo <= bv_unsigned sp - 16)%Z ->
(errno_addr tp + 4 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= errno_addr tp)%Z ->
(164 <= bv_unsigned tp)%Z ->
evt asegs (sysret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 errv F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcf0cc) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros ST ERR MI LO SEP TP.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
pose proof (wmono_refl asegs m) as WM.
do 3 step. if_cases Hc; zify_cond Hc.
-
step. unfold sysret_post, sysret_val, sysret_errno. rewrite (errno_of_small a0) by lia. finish.
- carve_frame 16%nat ST.
do 14 step.
pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
rewrite negw_errno in ERR by lia.
unfold sysret_post, sysret_val, sysret_errno. rewrite (errno_of_big a0) by lia.
release_frame FR ST (bv_unsigned sp).
finish.
Qed.

Definition read_ret (a : read_ans) : word :=
match a with RdErr _ => Z_to_bv 64 (-1) | RdData bs => Z_to_bv 64 (Z.of_nat (length bs)) end.

Definition read_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(B : Z) (n : nat) (junk : list byte) (errv : word) (lo : Z) (m : word -> option byte)
(a : read_ans) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (read_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (B, B + Z.of_nat n); (errno_addr tp, errno_addr tp + 4)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ match a with
| RdErr e => rw_cells asegs m' B [CB n junk]
/\ rw_cells asegs m' (errno_addr tp) [C4 (Z_to_bv 64 e)] /\ (1 <= e <= 4095)%Z
| RdData bs => rw_cells asegs m' B [CB (length bs) bs; CB (n - length bs) (skipn (length bs) junk)]
/\ rw_cells asegs m' (errno_addr tp) [C4 errv] /\ (length bs <= n)%nat
end.

Definition close_ret (a : sret) : word :=
match a with
| SVal _ => Z_to_bv 64 0
| SErr e => if (e =? EINTR)%Z then Z_to_bv 64 0 else Z_to_bv 64 (-1)
end.
Definition close_errno (a : sret) (errv : word) : word :=
match a with
| SVal _ => errv
| SErr e => if (e =? EINTR)%Z then errv else Z_to_bv 64 e
end.

Definition close_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(errv : word) (lo : Z) (m : word -> option byte) (a : sret) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (close_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' (errno_addr tp) [C4 (close_errno a errv)].

Definition got_ssp := 0xe8f90%Z.
Definition ssp_guard := 0x645560%Z.

Definition open_ret (a : sret) : word :=
match a with SVal fd => Z_to_bv 64 fd | SErr _ => Z_to_bv 64 (-1) end.
Definition open_errno (a : sret) (errv : word) : word :=
match a with SVal _ => errv | SErr e => Z_to_bv 64 e end.

Definition open_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(P : Z) (path : list byte) (errv canary : word) (lo : Z) (m : word -> option byte) (a : sret) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (open_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' (errno_addr tp) [C4 (open_errno a errv)]
/\ bytes_at asegs m' P (path ++ [Z_to_bv 8 0])
/\ rw_cells asegs m' got_ssp [C8 (Z_to_bv 64 ssp_guard)]
/\ rw_cells asegs m' ssp_guard [C8 canary]
/\ match a with SVal fd => (3 <= fd <= 4096)%Z | SErr e => (1 <= e <= 4095)%Z end.

End Mqb.

Module Mqc.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Export QDM6.Mq0.
Export QCNF.
Import ListNotations. Local Ltac QoSL.cell_of_bytes bs ::= QoSL.mkr__cell_of_bytes_10 bs. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.

Lemma b2z_Zb2z : b2z = Z.b2z. Proof. reflexivity. Qed.

Ltac zb_masks_in H :=
repeat match type of H with
| context [Z.land ?x ?m] =>
is_Zlit_zb m;
let k := eval vm_compute in (Z.log2 (m + 1)) in
let m' := eval vm_compute in (2 ^ k - 1)%Z in
constr_eq m m';
let p := eval vm_compute in (2 ^ k)%Z in
replace (Z.land x m) with (x mod p)%Z in H
by (symmetry; change m with (2^k - 1)%Z; change p with (2^k)%Z; apply zb_land_mask; lia)
end.

Ltac zs_wrap e ::= zs_wrap_land e. Ltac mkr__zs_wrap_0 e := zs_wrap_land e.
Ltac zs_wrap_in e H ::= zs_wrap_land_in e H. Ltac mkr__zs_wrap_in_1 e H := zs_wrap_land_in e H.
Ltac zs_idioms ::= zs_idioms_land. Ltac mkr__zs_idioms_2 := zs_idioms_land.
Ltac zs_idioms_in H ::= zs_idioms_land_in H. Ltac mkr__zs_idioms_in_3 H := zs_idioms_land_in H.

Ltac unfold_sf_in H :=
cbv beta delta [add64 sub64 mul64 shl64 not64 ltu64 eqz64 nez64 zext32 sext32 srliw mulhu
is_neg64 sra63 lt_s64 lo64 hi64 wrap64 b2z
ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI] in H. Ltac mkr__unfold_sf_in_4 H := cbv beta delta [add64 sub64 mul64 shl64 not64 ltu64 eqz64 nez64 zext32 sext32 srliw mulhu
is_neg64 sra63 lt_s64 lo64 hi64 wrap64 b2z
ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI] in H.
Ltac unfold_sf :=
cbv beta delta [add64 sub64 mul64 shl64 not64 ltu64 eqz64 nez64 zext32 sext32 srliw mulhu
is_neg64 sra63 lt_s64 lo64 hi64 wrap64 b2z
ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI].

Ltac norm_model H := unfold_sf_in H; zb_fold_lits_in H.

Ltac get_head t := lazymatch t with ?g _ => get_head g | _ => t end.

Tactic Notation "model_hyp" ident(HR) constr(t) :=
assert (HR : t = t) by reflexivity;
let h := get_head t in unfold h in HR at 2;
norm_model HR.

Notation W64 := 18446744073709551615%Z.

Ltac model_eval :=
lazy -[Z.shiftr Z.shiftl Z.land Z.lor Z.lxor Z.lnot Z.mul Z.add Z.sub Z.opp Z.modulo Z.div
Z.ltb Z.eqb Z.leb Z.pow bv_unsigned].

Tactic Notation "model_end" constr(X) constr(t) :=
replace (Z_to_bv 64 X) with (Z_to_bv 64 t) by (f_equal; model_eval; reflexivity).

Lemma lo64_mk128' : forall hi lo, (0 <= lo < 2^64)%Z -> (0 <= hi)%Z -> lo64 (mk128 hi lo) = lo.
Proof.
intros hi lo Hlo Hhi. unfold lo64, mk128. rewrite wrap64_mod.
rewrite <- Z.land_ones by lia. apply Z.bits_inj'. intros i Hi.
rewrite Z.land_spec, Z.lor_spec, Z.shiftl_spec by lia.
destruct (Z.lt_ge_cases i 64).
- rewrite Z.ones_spec_low, (Z.testbit_neg_r _ (i - 64)) by lia. cbn. apply andb_true_r.
- rewrite Z.ones_spec_high by lia. rewrite andb_false_r.
symmetry. destruct (Z.eq_dec lo 0) as [->|]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64%Z; [apply Z.log2_lt_pow2; lia|lia].
Qed.

Lemma lo64_mk128 : forall hi lo, (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z -> lo64 (mk128 hi lo) = lo.
Proof. intros. apply lo64_mk128'; lia. Qed.

Lemma hi64_mk128 : forall hi lo, (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z -> hi64 (mk128 hi lo) = hi.
Proof.
intros hi lo Hlo Hhi. unfold hi64, mk128. rewrite wrap64_mod.
rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
rewrite (Z.shiftr_div_pow2 lo), Z.div_small, Z.lor_0_r by lia. apply Z.mod_small. lia.
Qed.

Lemma lor_disjoint_add : forall a b, Z.land a b = 0%Z -> Z.lor a b = (a + b)%Z.
Proof. intros a b H. rewrite <- Z.lxor_lor by exact H. symmetry. apply Z.add_nocarry_lxor. exact H. Qed.

Lemma land_even_mask : forall y, Z.land y 18446744073709551614 = (Z.land y 18446744073709551615 - Z.land y 1)%Z.
Proof.
intros y. change 18446744073709551615%Z with (Z.lor 18446744073709551614 1).
rewrite Z.land_lor_distr_r, lor_disjoint_add; [lia|].
rewrite (Z.land_comm (Z.land y _) (Z.land y 1)), Z.land_assoc, (Z.land_comm (Z.land y 1) y), Z.land_assoc, Z.land_diag.
rewrite <- Z.land_assoc. change (Z.land 1 18446744073709551614) with 0%Z. apply Z.land_0_r.
Qed.

Lemma land_1 : forall y, Z.land y 1 = (y mod 2)%Z.
Proof. intros. change 1%Z with (Z.ones 1) at 1. rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_W64 : forall y, Z.land y 18446744073709551615 = (y mod 2^64)%Z.
Proof. intros. change 18446744073709551615%Z with (Z.ones 64). apply Z.land_ones. lia. Qed.

Lemma round_even_idiom : forall x, (0 <= x)%Z ->
Z_to_bv 64 (Z.land (x + 1) 18446744073709551614) = Z_to_bv 64 (x + Z.land x 1).
Proof.
intros x Hx. apply Z_to_bv_eqm. rewrite land_even_mask, land_W64, !land_1.
Z.div_mod_to_equations. lia.
Qed.

Ltac bool_atom_cases :=
repeat match goal with
| |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b)
| |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
| |- context [Z.leb ?a ?b] => destruct (Z.leb_spec0 a b)
end.

Ltac weq :=
first [ reflexivity
| f_equal; zeq
| rewrite round_even_idiom by zrange_nonneg; weq_arith
| weq_arith ]
with weq_arith :=
apply Z_to_bv_eqm; rewrite ?land_even_mask, ?land_1; zb_masks; cbv delta [Z.b2z]; cbn [negb];
bool_atom_cases; cbn [negb]; pose_word_ranges; Z.div_mod_to_equations; lia.

Ltac ms_eq :=
first [ reflexivity
| lazymatch goal with
| |- Z_to_bv 64 _ = Z_to_bv 64 _ => weq
| |- _ = Z_to_bv 64 (bv_unsigned _) => symmetry; apply Z_to_bv_bv_unsigned
| |- Z_to_bv 64 (bv_unsigned _) = _ => apply Z_to_bv_bv_unsigned
| |- context [mkR] => unfold mkR; ms_eq
| |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ => f_equal; ms_eq
| |- TNode _ _ _ = TNode _ _ _ => f_equal; ms_eq
| |- Some _ = Some _ => f_equal; ms_eq
end ].

Ltac sf_finish :=
apply evt_done;
lazymatch goal with |- ?P ?ms => try unfold P end; hnf;
rewrite ?lo64_mk128, ?hi64_mk128 by zrange;
repeat (lazymatch goal with |- ex _ => eexists end);
split; [ ms_eq | repeat match goal with |- _ /\ _ => split end; try assumption ].

Lemma signed_of_Z : forall z, (-2^63 <= z < 2^63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof.
intros z Hz. rewrite Z_to_bv_signed. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 64 / 2)%Z with (2^63)%Z. lia.
Qed.
Ltac signed_lits_in H :=
repeat match type of H with
| context [bv_signed (Z_to_bv 64 ?z)] => rewrite (signed_of_Z z) in H by lia
end.

Lemma mod64_land63 : forall y, (y mod 64 = Z.land y 63)%Z.
Proof. intros. change 63%Z with (Z.ones 6). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land63_idem : forall y, Z.land (Z.land y 63) 63 = Z.land y 63.
Proof. intros. rewrite <- Z.land_assoc. reflexivity. Qed.

Ltac zs_idioms_sf :=
match goal with
| |- context [Z.shiftr (Z.land (Z.shiftl ?x ?k) 18446744073709551615) ?k] =>
rewrite (zb_shl_shr_land x k) by (first [lia | zrange_nonneg])
| |- context [(?y mod 64)%Z] => rewrite (mod64_land63 y), ?land63_idem
end.
Ltac zs_idioms_sf_in H :=
match type of H with
| context [Z.shiftr (Z.land (Z.shiftl ?x ?k) 18446744073709551615) ?k] =>
rewrite (zb_shl_shr_land x k) in H by (first [lia | zrange_nonneg])
| context [(?y mod 64)%Z] => rewrite (mod64_land63 y), ?land63_idem in H
end.
Ltac zs_idioms ::= zs_idioms_sf. Ltac mkr__zs_idioms_5 := zs_idioms_sf.
Ltac zs_idioms_in H ::= zs_idioms_sf_in H. Ltac mkr__zs_idioms_in_6 H := zs_idioms_sf_in H.
End Mqc.

Module Mqd.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QwAs.
Import QvDJ.Mq3.
Import QbcP_c1.Mq1.
Import ListNotations. Local Ltac QoSL.cell_of_bytes bs ::= QoSL.mkr__cell_of_bytes_10 bs. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.

Ltac reg_val r :=
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end)
end.
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.

Ltac name_list xs L :=
lazymatch type of L with
| length _ = O => destruct xs; [clear L | cbn in L; discriminate]
| length _ = S _ => let x := fresh "x" in let xs' := fresh "xs" in
destruct xs as [|x xs']; [cbn in L; discriminate | cbn in L; apply Nat.succ_inj in L; name_list xs' L]
end.

Ltac window base k HW :=
lazymatch goal with SRC : bytes_at ?segs ?m ?S ?src |- _ =>
let xs := fresh "xs" in let L := fresh "L" in
destruct (window_ex src base k ltac:(lia)) as [xs [HW L]]; name_list xs L
end.

Ltac woff base c :=
let cz := eval vm_compute in (Z.of_nat c) in
lazymatch cz with 0%Z => base | _ => constr:((base + cz)%Z) end.

Ltac anorm REG imm :=
lazymatch REG with
| Z_to_bv 64 ?E =>
let E' :=
lazymatch imm with
| 0%Z => E
| _ => lazymatch E with
| Z.add ?x ?a =>
let isl := lazymatch a with Z0 => true | Zpos _ => true | Zneg _ => true | _ => false end in
lazymatch isl with
| true => let s := eval vm_compute in (a + imm)%Z in
lazymatch s with 0%Z => x | _ => constr:(Z.add x s) end
| false => constr:(Z.add E imm)
end
| _ => constr:(Z.add E imm)
end
end in
constr:(Z_to_bv 64 E')
| _ => lazymatch imm with 0%Z => REG | _ => constr:(Z_to_bv 64 (bv_unsigned REG + imm)%Z) end
end.

Ltac cur_mem_addr :=
lazymatch goal with |- evt ?segs _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) =>
let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
lazymatch fw with Some ?w =>
let d := eval vm_compute in (decode_any w) in
lazymatch d with
| Some (Load _ _ _ ?rs ?imm, _) =>
let rz := eval vm_compute in (bv_unsigned rs) in
let immz := eval vm_compute in (bv_signed imm) in
let REG := reg_val rz in anorm REG immz
| Some (Store _ ?rs _ ?imm, _) =>
let rz := eval vm_compute in (bv_unsigned rs) in
let immz := eval vm_compute in (bv_signed imm) in
let REG := reg_val rz in anorm REG immz
end end end. Ltac mkr__cur_mem_addr_0 := lazymatch goal with |- evt ?segs _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) =>
let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
lazymatch fw with Some ?w =>
let d := eval vm_compute in (decode_any w) in
lazymatch d with
| Some (Load _ _ _ ?rs ?imm, _) =>
let rz := eval vm_compute in (bv_unsigned rs) in
let immz := eval vm_compute in (bv_signed imm) in
let REG := reg_val rz in anorm REG immz
| Some (Store _ ?rs _ ?imm, _) =>
let rz := eval vm_compute in (bv_unsigned rs) in
let immz := eval vm_compute in (bv_signed imm) in
let REG := reg_val rz in anorm REG immz
end end end.

Ltac addr_tac :=
unfold wa;
first [ reflexivity
| f_equal; lia
| lazymatch goal with |- ?v = Z_to_bv 64 ?e =>
replace e with (bv_unsigned v) by lia; symmetry; apply Z_to_bv_bv_unsigned end ].

Definition ld_facts (base : Z) (c j kw : nat) (i : Z) : Prop :=
(0 <= base)%Z /\ (c + j <= kw)%nat /\ (i = base + Z.of_nat c)%Z.

Lemma mc_read1 : forall segs m S src kw base xsw c i a b,
bytes_at segs m S src -> firstn kw (skipn (Z.to_nat base) src) = xsw ->
ld_facts base c 1 kw i -> nth_error xsw c = Some b -> a = wa (S + i) ->
ov_read_bytes segs m a 1 = Some [b].
Proof.
intros segs m S src kw base xsw c i a b SRC HW (Hb & Hc & Hi) Hn Ha.
eapply (u8ro_read segs m S src i b a SRC); [ | lia | exact Ha ].
rewrite <- Hn. eapply window_nth; eauto; lia.
Qed.

Lemma mc_read4 : forall segs m S src kw base xsw c i a,
bytes_at segs m S src -> firstn kw (skipn (Z.to_nat base) src) = xsw -> length xsw = kw ->
ld_facts base c 4 kw i -> a = wa (S + i) ->
exists w, ov_read_bytes segs m a 4 = Some w /\ w = firstn 4 (skipn c xsw) /\ length w = 4%nat.
Proof.
intros segs m S src kw base xsw c i a SRC HW HL (Hb & Hc & Hi) ->.
assert (L : (Z.to_nat base + kw <= length src)%nat).
{ apply (f_equal (@length byte)) in HW. rewrite length_firstn, length_skipn, HL in HW. lia. }
exists (firstn 4 (skipn (Z.to_nat i) src)). split; [|split].
- apply (bytes_at_read segs m S src i 4 SRC); lia.
- eapply window_sub; eauto; lia.
- rewrite length_firstn, length_skipn. lia.
Qed.

Definition st_facts (S D n base : Z) (c k kw : nat) (P : Z) : Prop :=
((0 <= base)%Z /\ (c + k <= kw)%nat /\ P = base + Z.of_nat c /\ 0 <= P /\ P + Z.of_nat k <= n /\
(S + n <= D \/ D + n <= S) /\ 0 <= D /\ D + n <= 2^64)%Z.

Lemma mc_store_ok : forall segs m1 S D n src kw base xsw c k P bs a,
u8arr segs m1 D bs -> copied src bs (Z.to_nat P) -> length src = Z.to_nat n ->
firstn kw (skipn (Z.to_nat base) src) = xsw ->
st_facts S D n base c k kw P -> a = wa (D + P) -> store_ok segs m1 a k = true.
Proof.
intros segs m1 S D n src kw base xsw c k P bs a DST [L _] LEN _ (_ & _ & _ & HP & Hk & _) Ha.
eapply (u8arr_store_ok_n segs m1 D bs P k a DST); [lia | | exact Ha]. rewrite L, LEN. lia.
Qed.

Lemma mc_store : forall segs m0 m1 S D n src kw base xsw c k P bs xs a,
bytes_at segs m1 S src -> u8arr segs m1 D bs -> copied src bs (Z.to_nat P) ->
mem_inv segs m1 -> munch [(D, D + n)]%Z m0 m1 -> wmono segs m0 m1 ->
length src = Z.to_nat n -> firstn kw (skipn (Z.to_nat base) src) = xsw ->
st_facts S D n base c k kw P ->
xs = firstn k (skipn c xsw) -> length xs = k -> a = wa (D + P) ->
bytes_at segs (write_to_mem m1 a xs) S src /\
u8arr segs (write_to_mem m1 a xs) D (upd_bytes bs (Z.to_nat P) xs) /\
copied src (upd_bytes bs (Z.to_nat P) xs) (Z.to_nat (P + Z.of_nat k)) /\
mem_inv segs (write_to_mem m1 a xs) /\ munch [(D, D + n)]%Z m0 (write_to_mem m1 a xs) /\
wmono segs m0 (write_to_mem m1 a xs).
Proof.
intros segs m0 m1 S D n src kw base xsw c k P bs xs a SRC DST CP MI MU WM LEN HW
(Hb & Hc & HPb & HP & Hk & SEP & D0 & Dn) Hxs Hl Ha.
pose proof (proj1 CP) as Lbs.
assert (SOK : store_ok segs m1 a (length xs) = true).
{ rewrite Hl. eapply mc_store_ok; eauto. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]; eauto; lia. }
subst a. split; [|split; [|split; [|split; [|split]]]].
- apply bytes_at_write_other; [exact SRC | lia | lia | rewrite LEN; lia].
- apply (u8arr_write_bytes segs m1 D bs P xs DST); [lia|]. rewrite Lbs, LEN. lia.
- apply (f_equal (@length byte)) in CP || idtac.
rewrite <- Hl. apply copied_updZ; [exact CP | lia | | rewrite LEN; lia].
rewrite Hl, Hxs. eapply window_sub; eauto; lia.
- apply mem_inv_store; assumption.
- apply munch_write; [exact MU | lia | lia |]. cbn [inside]. left. lia.
- apply wmono_write. exact WM.
Qed.

Ltac ld1 HW c :=
lazymatch type of HW with firstn ?k (skipn (Z.to_nat ?base) ?src) = ?xs =>
lazymatch goal with SRC : bytes_at ?segs ?m ?S src |- _ =>
let i := woff base c in
let a := cur_mem_addr in
let RD := fresh "RD" in
pose proof (mc_read1 segs m S src k base xs c i a _ SRC HW
ltac:(unfold ld_facts; lia) ltac:(reflexivity) ltac:(addr_tac)) as RD;
zstep; try clear RD;
lazymatch goal with |- evt _ _ ?ms => let ms' := eval cbv beta in ms in change ms with ms' end
end end.

Ltac ld4 HW c w :=
lazymatch type of HW with firstn ?k (skipn (Z.to_nat ?base) ?src) = ?xs =>
lazymatch goal with SRC : bytes_at ?segs ?m ?S src |- _ =>
let i := woff base c in
let a := cur_mem_addr in
let RD := fresh "RD" in let Ew := fresh "E" w in let Lw := fresh "L" w in
destruct (mc_read4 segs m S src k base xs c i a SRC HW ltac:(reflexivity) ltac:(unfold ld_facts; lia) ltac:(addr_tac))
as [w [RD [Ew Lw]]];
cbn [firstn skipn] in Ew;
zstep; try clear RD
end end.

Ltac zify_bytes :=
repeat match goal with
| |- context [bv_unsigned ?b] =>
lazymatch type of b with
| byte => pose proof (byte_range b); generalize dependent (bv_unsigned b); intros
end
end.
Ltac solve_le K :=
repeat match goal with H : ?w = _ :: _ |- _ => is_var w; subst w end;
first [ apply le4_of_mod32; [reflexivity|] | apply le1_of_mod8 ];
cbn [map le_val]; rewrite ?unsigned_lit_wrap; rewrite ?lw_unsigned4;
zify_bytes;
rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2, ?bv_swrap32_eq, ?bv_wrap32_eq by lia;
lazymatch K with
| 0%Z => idtac
| _ => first [ rewrite (lor_add _ _ K); [ | lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia ]
| rewrite (lor_add' _ _ K); [ | lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia ] ]
end;
Z.div_mod_to_equations; lia.

Ltac by_byte := symmetry; apply le1_zxb.
Ltac by_lw := symmetry; lazymatch goal with |- le4 (sext 64 (bv_extract 0 32 (le_bytes_to_word ?w))) = _ =>
lazymatch goal with L : length w = 4%nat, E : w = _ |- _ => rewrite (le4_lw w L); exact E end end.

Ltac by_le K :=
symmetry;
repeat match goal with H : ?w = _ :: _ |- _ => is_var w; subst w end;
first
[ lazymatch goal with
| |- le4 (Z_to_bv 64 (Z.lor (Z.modulo (bv_swrap 32 (Z.shiftr _ ?k)) _) _)) = _ =>
lazymatch k with 24%Z => apply merge_a24 | 16%Z => apply merge_a16 | 8%Z => apply merge_a8 end
| |- le4 (Z_to_bv 64 (Z.lor _ (Z.modulo (bv_swrap 32 (Z.shiftr _ ?k)) _))) = _ =>
lazymatch k with 24%Z => apply merge_r24 | 16%Z => apply merge_r16 | 8%Z => apply merge_r8 end
| |- le1 (Z_to_bv 64 (Z.shiftr _ ?k)) = _ =>
lazymatch k with 8%Z => apply lwb1 | 16%Z => apply lwb2 end
| |- le1 (sext _ _) = _ => apply lwb0
end
| solve_le K ].

Ltac cst_core HW c k bytes_tac SF :=
lazymatch type of HW with firstn ?kw (skipn (Z.to_nat ?base) ?src) = ?xsw =>
let xs := eval cbv beta iota delta [firstn skipn] in (firstn k (skipn c xsw)) in
let kz := eval vm_compute in (Z.of_nat k) in
lazymatch goal with
| SRC : bytes_at ?segs ?m ?S src, DST : u8arr ?segs ?m ?D ?bs, CP : copied src ?bs (Z.to_nat ?P),
MI : mem_inv ?segs ?m, MU : munch _ ?m0 ?m, WM : wmono ?segs ?m0 ?m, LEN : length src = Z.to_nat _
|- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs0) _) =>
replace bs0 with xs by bytes_tac;
let SRC' := fresh "SRC" in let DST' := fresh "DST" in let CP' := fresh "CP" in
let MI' := fresh "MI" in let MU' := fresh "MU" in let WM' := fresh "WM" in
destruct (mc_store segs m0 m S D _ src kw base xsw c k P bs xs a SRC DST CP MI MU WM LEN HW SF
ltac:(reflexivity) ltac:(reflexivity) ltac:(addr_tac))
as (SRC' & DST' & CP' & MI' & MU' & WM');
change (Z.of_nat k) with kz in CP';
clear SRC DST CP MI MU WM SF;
repeat match goal with
| H : store_ok segs m _ _ = true |- _ => clear H
| H : ov_read_bytes segs m _ _ = Some _ |- _ => clear H
end;
let m' := fresh "m" in remember (write_to_mem m a xs) as m' eqn:Heqm; clear Heqm; try clear m;
let bs' := fresh "bs" in remember (upd_bytes bs (Z.to_nat P) xs) as bs' eqn:Heqbs; clear Heqbs; try clear bs;
rename SRC' into SRC; rename DST' into DST; rename CP' into CP;
rename MI' into MI; rename MU' into MU; rename WM' into WM
end end.

Ltac cst HW c k bytes_tac :=
lazymatch goal with SF : st_facts _ _ _ _ c k _ _ |- _ => cst_core HW c k bytes_tac SF end.

Ltac st HW c k bytes_tac :=
lazymatch type of HW with firstn ?kw (skipn (Z.to_nat ?base) ?src) = ?xsw =>
lazymatch goal with
| SRC : bytes_at ?segs ?m ?S src, DST : u8arr ?segs ?m ?D ?bs, CP : copied src ?bs (Z.to_nat ?P),
MU : munch [(_, _ + ?n)%Z] _ ?m, LEN : length src = Z.to_nat _ |- _ =>
let a := cur_mem_addr in
let SF := fresh "SF" in let SOK := fresh "SOK" in
assert (SF : st_facts S D n base c k kw P) by (unfold st_facts; lia);
pose proof (mc_store_ok segs m S D n src kw base xsw c k P bs a DST CP LEN HW SF ltac:(addr_tac)) as SOK;
zstep; [ cst_core HW c k bytes_tac SF | .. ]
end end.
Ltac st1 HW c := st HW c 1%nat by_byte.
Ltac st4 HW c := st HW c 4%nat by_lw.

Ltac by_win HW c :=
lazymatch type of HW with firstn ?k (skipn (Z.to_nat ?base) ?src) = ?xs =>
first [ rewrite (window_sub src xs base k c 4 _ HW) by lia
| symmetry; rewrite (window_sub src xs base k c 4 _ HW) by lia ];
cbn [firstn skipn]; first [ assumption | symmetry; assumption | reflexivity ]
end.

Ltac cp_norm P' :=
lazymatch goal with CP : copied ?src ?bs (Z.to_nat ?P) |- _ => replace (Z.to_nat P) with (Z.to_nat P') in CP by lia end.

Definition mc_inv (segs : list MemImageType.Segment) (S D : Z) (src : list byte) (W : list ivl)
(m0 m1 : word -> option byte) (bs : list byte) (P : Z) : Prop :=
bytes_at segs m1 S src /\ u8arr segs m1 D bs /\ copied src bs (Z.to_nat P) /\
mem_inv segs m1 /\ munch W m0 m1 /\ wmono segs m0 m1.

Ltac open_inv H := destruct H as (SRC & DST & CP & MI & MU & WM).

Ltac inv_tac :=
lazymatch goal with
| |- mc_inv _ _ _ _ _ _ _ _ _ =>
split; [eassumption | split; [eassumption | split; [ | repeat split; eassumption ]]];
lazymatch goal with CP : copied _ _ (Z.to_nat ?P) |- copied _ _ (Z.to_nat ?P') =>
first [ exact CP | replace (Z.to_nat P') with (Z.to_nat P) by lia; exact CP ] end
end.

Ltac use_side :=
first [ inv_tac | idtac ]; try assumption; try (f_equal; lia); try lia;
try (rewrite ?unsigned_lit by lia; Z.div_mod_to_equations; lia);
try (rewrite ?Z.add_0_r, ?Z.sub_0_r; symmetry; apply Z_to_bv_bv_unsigned).
Tactic Notation "use" uconstr(L) := eapply L; use_side.

Ltac finish2 :=
apply evt_done;
lazymatch goal with |- ?P ?ms => try unfold P | _ => idtac end;
hnf;
repeat (lazymatch goal with |- ex _ => eexists end);
lazymatch goal with
| |- _ = _ /\ _ => split; [ cbv delta [mkR]; reflexivity | ]
| |- _ = _ => cbv delta [mkR]; reflexivity
end;
repeat match goal with |- _ /\ _ => split end; try assumption.

Ltac mc_fin :=
lazymatch goal with
| DST : u8arr _ ?m1 _ ?bs, CP : copied ?src ?bs (Z.to_nat ?P), L : length ?src = _ |- _ =>
let E := fresh "E" in
pose proof (copied_all _ _ _ CP ltac:(lia)) as E; rewrite E in DST; clear E CP;
apply rw_cells_of_u8arr in DST; rewrite L in DST
end;
finish2.

Ltac fix_lit_store :=
try (lazymatch goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
end).
Ltac lstep := zstep; fix_lit_store.
End Mqd.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export QZzg.
Import ListNotations. Local Ltac QoSL.cell_of_bytes bs ::= QoSL.mkr__cell_of_bytes_10 bs. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Lemma a_find_segment_none : forall z n, 1 <= n -> (z + n <= 0x10000 \/ 0x647000 <= z) ->
find_segment asegs z n = None.
Proof.
intros z n Hn Hz. unfold asegs, AsanUbsan.M.loaded_segments, AsanUbsan.AsanUbsan_loaded_segments. cbn [find_segment].
replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_000)) with 0x10000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_000)) with 0x2e000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_001)) with 0x3e000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_001)) with 0xa6000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_002)) with 0x0e4000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_002)) with 0x6000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_003)) with 0x0ea000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_003)) with 0x55d000%Z by (vm_compute; reflexivity).
destruct (Z.leb_spec0 0x10000 z); destruct (Z.leb_spec0 (z + n) (0x10000 + 0x2e000)); cbn [andb]; try lia.
all: destruct (Z.leb_spec0 0x3e000 z); destruct (Z.leb_spec0 (z + n) (0x3e000 + 0xa6000)); cbn [andb]; try lia.
all: destruct (Z.leb_spec0 0x0e4000 z); destruct (Z.leb_spec0 (z + n) (0x0e4000 + 0x6000)); cbn [andb]; try lia.
all: destruct (Z.leb_spec0 0x0ea000 z); destruct (Z.leb_spec0 (z + n) (0x0ea000 + 0x55d000)); cbn [andb]; try lia.
all: reflexivity.
Qed.

Lemma a_ro_addr_false : forall x : word,
(bv_unsigned x + 1 <= 0x10000 \/ 0x647000 <= bv_unsigned x)%Z -> ro_addr asegs x = false.
Proof. intros x Hx. unfold ro_addr. rewrite a_find_segment_none by lia. reflexivity. Qed.

Lemma a_memory_read_none : forall (x : word) n,
(1 <= Z.of_N n)%Z -> (bv_unsigned x + Z.of_N n <= 0x10000 \/ 0x647000 <= bv_unsigned x)%Z -> memory_read asegs x n = None.
Proof. intros x n Hn Hx. unfold memory_read. rewrite a_find_segment_none by lia. reflexivity. Qed.

Lemma a_wview_overlay : forall m (x : word),
(bv_unsigned x + 1 <= 0x10000 \/ 0x647000 <= bv_unsigned x)%Z -> wview asegs m x = m x.
Proof.
intros m x Hx. unfold wview. destruct (m x); [reflexivity|]. rewrite a_find_segment_none by lia. reflexivity.
Qed.

Lemma a_seg_rom_none : forall (x : word),
(bv_unsigned x + 1 <= 0x10000 \/ 0x647000 <= bv_unsigned x)%Z -> seg_rom asegs x = None.
Proof. intros x Hx. unfold seg_rom. rewrite a_memory_read_none by (cbn; lia). reflexivity. Qed.

Lemma a_mrd_overlay : forall m (x : word),
(bv_unsigned x + 1 <= 0x10000 \/ 0x647000 <= bv_unsigned x)%Z -> mrd asegs m x = m x.
Proof. intros m x Hx. unfold mrd. destruct (m x); [reflexivity|]. apply a_seg_rom_none. exact Hx. Qed.

